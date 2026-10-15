{-# OPTIONS --guardedness #-}

-- Core.hs:2061-2355, network 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d.
-- Enabled assertions, total diagnostic tracing. Over-limit promotion is a
-- coverage frontier BEFORE any transactional write, never a successful shortcut.
module ConnectionManagement.Rules.RemoteState where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; _≤?_)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Rules.IGRegistration as IG

data Operation : Set where
  promote demote : Operation
-- Retain the old concrete snapshot; source returns its abstract-state projection.
data Outcome : Set where
  success terminatedConnection : ConnectionState → Outcome
  unsupported : Maybe ConnectionState → Outcome

data PC : Set where
  transaction assertion counters returning assertionRaised requiresPruning : PC
record Frame : Set where
  constructor frame
  field operation : Operation
        key : ConnectionKey
        time : ℕ
        rest : List IGEvent
        captured : IG.Published
        pc : PC
        outcome : Outcome
        deferredAssertion : Bool
open Frame public
record Decision : Set where
  constructor decision
  field replacement : Maybe ConnectionState
        result : Outcome
        assertLater needsCapacity : Bool
open Decision public

-- Pure source cases; capacity is read only in the two outbound promotion cases.
promoteCase : ConnectionKey → ConnectionState → Decision
promoteCase k st@(outboundDup _ w h _) = decision (just (duplexActive k w h)) (success st) false true
promoteCase k st@(outboundIdle _ w h duplex) = decision (just (inboundActive k w h duplex)) (success st) false true
promoteCase k st@(outboundIdle _ _ _ unidirectional) = decision nothing (unsupported (just st)) false false
promoteCase k st@(inboundIdle _ w h flow) = decision (just (inboundActive k w h flow)) (success st) false false
promoteCase k st@(inboundActive _ _ _ _) = decision nothing (success st) true false
promoteCase k st@(duplexActive _ _ _) = decision nothing (success st) false false
promoteCase k st@(terminating _ _ _) = decision nothing (unsupported (just st)) false false
promoteCase k st@(terminated _) = decision nothing (unsupported (just st)) false false
promoteCase k st = decision nothing (unsupported (just st)) true false

demoteCase : ConnectionKey → ConnectionState → Decision
demoteCase k st@(outboundDup _ _ _ _) = decision nothing (success st) false false
demoteCase k st@(outboundIdle _ _ _ _) = decision nothing (success st) false false
demoteCase k st@(inboundIdle _ _ _ _) = decision nothing (success st) false false
demoteCase k st@(inboundActive _ w h flow) = decision (just (inboundIdle k w h flow)) (success st) false false
demoteCase k st@(duplexActive _ w h) = decision (just (outboundDup k w h ticking)) (success st) false false
demoteCase k st@(terminating _ _ _) = decision nothing (terminatedConnection st) false false
demoteCase k st@(terminated _) = decision nothing (terminatedConnection st) false false
demoteCase k st = decision nothing (unsupported (just st)) true false

choose : Frame → ConnectionState → Decision
choose f with operation f
... | promote = promoteCase (key f)
... | demote = demoteCase (key f)

record Proposal : Set where
  constructor proposal
  field edit : Maybe (EntryId × ConnectionState)
        pending : Maybe Frame
        governor : IG.Runtime
open Proposal public

data Action : Set where
  enter transact checkAssertion readCounters returnToIG : Action

continue : PC → Frame → IG.Runtime → Proposal
continue p f ig = proposal nothing (just (record f { pc = p })) ig

-- Selection and edit are applied by Machine in one event, as for inbound release.
commitDecision : EntryId → Decision → Frame → IG.Runtime → Proposal
commitDecision e d f ig with replacement d
... | nothing = proposal nothing (just updated) ig
  where updated = record f { pc = assertion ; outcome = result d ; deferredAssertion = assertLater d }
... | just st = proposal (just (e , st)) (just updated) ig
  where updated = record f { pc = assertion ; outcome = result d ; deferredAssertion = assertLater d }

capacityDecision : ℕ → ConnMap → EntryId → Decision → Frame → IG.Runtime → State → Maybe Proposal
capacityDecision limit m e d f ig s with needsCapacity d
... | false = just (commitDecision e d f ig)
... | true with countIncoming (entries (cm s)) m
...   | nothing = nothing
...   | just n with suc n ≤? limit
...     | yes _ = just (commitDecision e d f ig)
...     | no _ = just (continue requiresPruning f ig)

select : ℕ → Frame → IG.Runtime → State → Maybe Proposal
select limit f ig s with mapCell (cm s)
... | taken _ = nothing
... | full m with lookupConnection (key f) m
...   | nothing = just (continue assertion f ig)
...   | just e with lookup e (entries (cm s))
...     | nothing = nothing
...     | just st = capacityDecision limit m e (choose f st) f ig s

-- Demotion counts every result; promotion counts only success. Both assert first.
afterAssertion : Frame → PC
afterAssertion f with operation f | outcome f
... | demote | _ = counters
... | promote | success _ = counters
... | promote | _ = returning

resume : Frame → IG.PC
resume f with operation f | outcome f
... | promote | _ = IG.publishDecision (time f) (rest f) (IG.setRemote (key f) IG.remoteWarm (captured f))
... | demote | success _ = IG.awaitRemoteIdle (time f) (key f) (rest f) (captured f)
... | demote | _ = IG.readNext (time f) (rest f)

stepWorker : ℕ → Action → Frame → IG.Runtime → State → Maybe Proposal
stepWorker limit transact f ig s with pc f
... | transaction = select limit f ig s
... | _ = nothing
stepWorker limit checkAssertion f ig s with pc f | deferredAssertion f
... | assertion | true = just (continue assertionRaised f ig)
... | assertion | false = just (continue (afterAssertion f) f ig)
... | _ | _ = nothing
stepWorker limit readCounters f ig s with pc f | mapCell (cm s)
... | counters | full m with countIncoming (entries (cm s)) m
...   | nothing = nothing
...   | just _ = just (continue returning f ig)
stepWorker limit readCounters f ig s | _ | _ = nothing
stepWorker limit returnToIG f ig s with pc f
... | returning = just (proposal nothing nothing (IG.setPC (resume f) ig))
... | _ = nothing
stepWorker _ _ _ _ _ = nothing

begin : Operation → ℕ → ConnectionKey → List IGEvent → IG.Published → IG.Runtime → Proposal
begin op t k rest captured ig = proposal nothing
  (just (frame op k t rest captured transaction (unsupported nothing) false)) (IG.setPC IG.inCM ig)

step : ℕ → Action → Maybe Frame → IG.Runtime → State → Maybe Proposal
step limit enter nothing ig s with IG.continuation ig
... | IG.needsCM t rest (awakeRemote k) captured = just (begin promote t k rest captured ig)
... | IG.needsCM t rest (waitIdleRemote k) captured = just (begin demote t k rest captured ig)
... | _ = nothing
step limit a (just f) ig s with IG.continuation ig
... | IG.inCM = stepWorker limit a f ig s
... | _ = nothing
step _ _ _ _ _ = nothing

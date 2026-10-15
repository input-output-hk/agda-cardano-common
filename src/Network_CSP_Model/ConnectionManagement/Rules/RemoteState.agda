{-# OPTIONS --guardedness #-}

-- Core.hs:2061-2355, network 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d.
-- Enabled assertions and total diagnostic tracing. Pruning commits all victim
-- writes atomically, then delivers captured cancellations in connection order.
module ConnectionManagement.Rules.RemoteState where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; _≤?_; _∸_)
import Data.Nat as Nat
open import Data.Integer using (ℤ)
open import Class.DecEq using (_≟_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.Pruning as Prune

data Operation : Set where
  promote demote : Operation
-- Retain the old concrete snapshot; source returns its abstract-state projection.
data Outcome : Set where
  success terminatedConnection : ConnectionState → Outcome
  unsupported : Maybe ConnectionState → Outcome

data PC : Set where
  transaction assertion counters returning assertionRaised : PC
  cancellationNext : List Prune.Candidate → PC
  awaitDelivery : Prune.Candidate → List Prune.Candidate → PC
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
        pruneVictims : List Prune.Candidate
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
  field edits : List (EntryId × ConnectionState)
        pending : Maybe Frame
        governor : IG.Runtime
        consumedRandom : Bool
open Proposal public

data Action : Set where
  enter transact checkAssertion readCounters returnToIG requestPruneCancellation : Action
  transactPruning : ℕ → List ℤ → Action
  pruneCancellationDelivered : WorkerId → Action

continue : PC → Frame → IG.Runtime → Proposal
continue p f ig = proposal [] (just (record f { pc = p })) ig false

-- Selection and edit are applied by Machine in one event, as for inbound release.
commitDecision : EntryId → Decision → Frame → IG.Runtime → Proposal
commitDecision e d f ig with replacement d
... | nothing = proposal [] (just updated) ig false
  where updated = record f { pc = assertion ; outcome = result d ; deferredAssertion = assertLater d }
... | just st = proposal ((e , st) ∷ []) (just updated) ig false
  where updated = record f { pc = assertion ; outcome = result d ; deferredAssertion = assertLater d }

-- Entropy is accepted only by an over-limit transaction. No split/draw is
-- consumed when the same promotion no longer requires pruning.
plainDecision : Maybe (List ℤ) → EntryId → Decision → Frame → IG.Runtime → Maybe Proposal
plainDecision nothing e d f ig = just (commitDecision e d f ig)
plainDecision (just _) _ _ _ _ = nothing

pruneDecision : ℕ → ConnMap → EntryId → Decision → Frame → IG.Runtime → State → List ℤ → Maybe Proposal
pruneDecision n m e d f ig s scores with replacement d | Prune.candidates m (entries (cm s))
... | just st | just cs with Prune.candidateFor (key f) e st
...   | nothing = nothing
...   | just self with Prune.makePlan n self st cs scores
...     | nothing = nothing
...     | just selectedPlan = just (proposal (Prune.edits selectedPlan)
       (just (record f { pc = assertion ; outcome = result d
                      ; deferredAssertion = false ; pruneVictims = Prune.victims selectedPlan })) ig true)
pruneDecision _ _ _ _ _ _ _ _ | _ | _ = nothing

capacityDecision : ℕ → Maybe (List ℤ) → ConnMap → EntryId → Decision → Frame → IG.Runtime → State → Maybe Proposal
capacityDecision limit scores m e d f ig s with needsCapacity d
... | false = plainDecision scores e d f ig
... | true with countIncoming (entries (cm s)) m
...   | nothing = nothing
...   | just n with suc n ≤? limit
...     | yes _ = plainDecision scores e d f ig
...     | no _ with scores
...       | nothing = nothing -- requires the scored transaction action
...       | just draws = pruneDecision (suc n ∸ limit) m e d f ig s draws

select : ℕ → Maybe (List ℤ) → Frame → IG.Runtime → State → Maybe Proposal
select limit scores f ig s with mapCell (cm s)
... | taken _ = nothing
... | full m with lookupConnection (key f) m
...   | nothing with scores
...     | nothing = just (continue assertion f ig)
...     | just _ = nothing
select limit scores f ig s | full m | just e with lookup e (entries (cm s))
...     | nothing = nothing
...     | just st = capacityDecision limit scores m e (choose f st) f ig s

beforeCounters : List Prune.Candidate → PC
beforeCounters [] = counters
beforeCounters victims = cancellationNext victims

-- Demotion counts every result; promotion counts only success. Both assert first.
afterAssertion : Frame → PC
afterAssertion f with operation f | outcome f
... | demote | _ = counters
... | promote | success _ = beforeCounters (pruneVictims f)
... | promote | _ = returning

resume : Frame → IG.PC
resume f with operation f | outcome f
... | promote | _ = IG.publishDecision (time f) (rest f) (IG.setRemote (key f) IG.remoteWarm (captured f))
... | demote | success _ = IG.awaitRemoteIdle (time f) (key f) (rest f) (captured f)
... | demote | _ = IG.readNext (time f) (rest f)

stepWorker : ℕ → ℕ → Action → Frame → IG.Runtime → State → Maybe Proposal
stepWorker limit generation transact f ig s with pc f
... | transaction = select limit nothing f ig s
... | _ = nothing
stepWorker limit generation (transactPruning ticket scores) f ig s with pc f | ticket Nat.≟ generation
... | transaction | yes _ = select limit (just scores) f ig s
... | _ | _ = nothing
stepWorker limit generation requestPruneCancellation f ig s with pc f
... | cancellationNext [] = just (continue counters f ig)
... | cancellationNext (victim ∷ rest) = just (continue (awaitDelivery victim rest) f ig)
... | _ = nothing
stepWorker limit generation (pruneCancellationDelivered w) f ig s with pc f
... | awaitDelivery victim rest with w ≟ Prune.thread victim
...   | yes _ = just (continue (cancellationNext rest) f ig)
...   | no _ = nothing
stepWorker limit generation (pruneCancellationDelivered w) f ig s | _ = nothing
stepWorker limit generation checkAssertion f ig s with pc f | deferredAssertion f
... | assertion | true = just (continue assertionRaised f ig)
... | assertion | false = just (continue (afterAssertion f) f ig)
... | _ | _ = nothing
stepWorker limit generation readCounters f ig s with pc f | mapCell (cm s)
... | counters | full m with countIncoming (entries (cm s)) m
...   | nothing = nothing
...   | just _ = just (continue returning f ig)
stepWorker limit generation readCounters f ig s | _ | _ = nothing
stepWorker limit generation returnToIG f ig s with pc f
... | returning = just (proposal [] nothing (IG.setPC (resume f) ig) false)
... | _ = nothing
stepWorker _ _ _ _ _ _ = nothing

begin : Operation → ℕ → ConnectionKey → List IGEvent → IG.Published → IG.Runtime → Proposal
begin op t k rest captured ig = proposal []
  (just (frame op k t rest captured transaction (unsupported nothing) false [])) (IG.setPC IG.inCM ig) false

step : ℕ → ℕ → Action → Maybe Frame → IG.Runtime → State → Maybe Proposal
step limit generation enter nothing ig s with IG.continuation ig
... | IG.needsCM t rest (awakeRemote k) captured = just (begin promote t k rest captured ig)
... | IG.needsCM t rest (waitIdleRemote k) captured = just (begin demote t k rest captured ig)
... | _ = nothing
step limit generation a (just f) ig s with IG.continuation ig
... | IG.inCM = stepWorker limit generation a f ig s
... | _ = nothing
step _ _ _ _ _ _ = nothing

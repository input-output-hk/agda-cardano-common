{-# OPTIONS --guardedness #-}

-- Core.hs:1107-1260 at 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d.
-- Assertions enabled; diagnostic tracers total. Cancellation delivery is an
-- explicit environment boundary, not a proof that handler cleanup has finished.
module ConnectionManagement.Rules.InboundRelease where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup; put)
import ConnectionManagement.Rules.IGRegistration as IG

data Outcome : Set where
  commit keep : Outcome
  unsupported : ConnectionState → Outcome

data PC : Set where
  transaction counters cancellation assertion returning assertionRaised : PC
  delivering : WorkerId → PC

record Frame : Set where
  constructor frame
  field key : ConnectionKey
        time : ℕ
        rest : List IGEvent
        captured : IG.Published
        pc : PC
        outcome : Outcome
        target : Maybe WorkerId
        deferredAssertion : Bool
open Frame public

-- A proposal is applied in the SAME machine event as the transaction. There is
-- no intermediate state between choosing and writing the current entry TVar.
record Proposal : Set where
  constructor proposal
  field edit : Maybe (EntryId × ConnectionState)
        pending : Maybe Frame
        governor : IG.Runtime
open Proposal public

data Action : Set where
  enter transact readCounters requestCancellation checkAssertion returnToIG : Action
  cancellationDelivered : WorkerId → Action

continue : PC → Frame → IG.Runtime → Proposal
continue pc f ig = proposal nothing (just (record f { pc = pc })) ig

-- Requested key replaces the key stored in the TVar, exactly as in Core.hs.
branch : ConnectionState → Frame → Maybe ConnectionState × Frame
branch (outboundDup _ w h ticking) f = just (outboundDup (key f) w h expired) ,
  record f { pc = counters ; outcome = keep }
branch (outboundDup _ _ _ expired) f = nothing , record f { pc = assertionRaised }
branch (outboundIdle _ _ _ _) f = nothing ,
  record f { pc = counters ; outcome = commit ; deferredAssertion = true }
branch (inboundIdle _ w _ _) f = just (terminating (key f) w nothing) ,
  record f { pc = counters ; outcome = commit ; target = just w }
branch st@(inboundActive _ w _ _) f = just (terminating (key f) w nothing) ,
  record f { pc = counters ; outcome = unsupported st ; target = just w ; deferredAssertion = true }
branch st@(duplexActive _ w h) f = just (outboundDup (key f) w h ticking) ,
  record f { pc = counters ; outcome = unsupported st ; deferredAssertion = true }
branch (terminating _ _ _) f = nothing , record f { pc = counters ; outcome = commit }
branch st f = nothing , record f { pc = counters ; outcome = unsupported st }

select : Frame → IG.Runtime → State → Maybe Proposal
select f ig s with mapCell (cm s)
... | taken _ = nothing
... | full m with lookupConnection (key f) m
...   | nothing = just (continue counters f ig)
...   | just e with lookup e (entries (cm s))
...     | nothing = nothing -- malformed dangling reference, not a source retry
...     | just st with branch st f
...       | nothing , f′ = just (proposal nothing (just f′) ig)
...       | just st′ , f′ = just (proposal (just (e , st′)) (just f′) ig)

resume : Frame → IG.PC
resume f with outcome f
... | commit = IG.publishDecision (time f) (rest f) (IG.unregister (key f) (captured f))
... | keep = IG.publishDecision (time f) (rest f) (IG.setRemote (key f) IG.remoteCold (captured f))
... | unsupported _ = IG.readNext (time f) (rest f)

-- No counter read may bypass an owned map. This read is later than the write.
stepWorker : Action → Frame → IG.Runtime → State → Maybe Proposal
stepWorker transact f ig s with pc f
... | transaction = select f ig s
... | _ = nothing
stepWorker readCounters f ig s with pc f | mapCell (cm s)
... | counters | full m with countIncoming (entries (cm s)) m
...   | nothing = nothing
...   | just _ = just (continue cancellation f ig)
stepWorker readCounters f ig s | _ | _ = nothing
stepWorker requestCancellation f ig s with pc f | target f
... | cancellation | nothing = just (continue assertion f ig)
... | cancellation | just w = just (continue (delivering w) f ig)
... | _ | _ = nothing
stepWorker (cancellationDelivered w) f ig s with pc f
... | delivering v = delivered w v
  where
  open import Class.DecEq using (_≟_)
  open import Relation.Nullary using (yes; no)
  delivered : WorkerId → WorkerId → Maybe Proposal
  delivered w v with w ≟ v
  ... | yes _ = just (continue assertion f ig)
  ... | no _ = nothing
... | _ = nothing
stepWorker checkAssertion f ig s with pc f | deferredAssertion f
... | assertion | true = just (continue assertionRaised f ig)
... | assertion | false = just (continue returning f ig)
... | _ | _ = nothing
stepWorker returnToIG f ig s with pc f
... | returning = just (proposal nothing nothing (IG.setPC (resume f) ig))
... | _ = nothing
stepWorker _ _ _ _ = nothing

step : Action → Maybe Frame → IG.Runtime → State → Maybe Proposal
step enter nothing ig s with IG.continuation ig
... | IG.needsCM t rest (commitRemote k) captured =
  just (proposal nothing (just (frame k t rest captured transaction commit nothing false)) (IG.setPC IG.inCM ig))
... | _ = nothing
step a (just f) ig s with IG.continuation ig
... | IG.inCM = stepWorker a f ig s
... | _ = nothing -- IG deactivation prevents return into its former batch
step _ _ _ _ = nothing

applyEdit : Maybe (EntryId × ConnectionState) → State → Maybe State
applyEdit nothing s = just s
applyEdit (just (e , st)) s with lookup e (entries (cm s))
... | nothing = nothing
... | just _ = just (record s { cm = record (cm s) { entries = put e st (entries (cm s)) } })

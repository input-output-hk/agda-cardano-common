{-# OPTIONS --guardedness #-}

-- Core.hs:1834-2060: outbound release, ordered timer race, and pruning.
module ConnectionManagement.Rules.OutboundRelease where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc; _≤?_; _∸_)
open import Data.Integer using (ℤ)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Rules.Pruning as Prune

data Result : Set where
  success unsupported : Maybe ConnectionState → Result
  assertionFailure : Result

data PC : Set where
  transaction : PC
  check : Bool → PC → PC
  count : PC → PC
  armTimer waitIdle timeoutWrite : EntryId → WorkerId → PC
  cancel : WorkerId → PC → PC
  delivering : WorkerId → PC → PC
  prune : List Prune.Candidate → Result → PC
  complete : Result → PC

record Frame : Set where
  constructor frame
  field key : ConnectionKey
        pc : PC
        timerReady : Bool
open Frame public
Runtime = Store WorkerId Frame

-- Changes to the captured entry win over a simultaneously ready timer.
isIdle : ConnectionState → Bool
isIdle (outboundIdle _ _ _ _) = true
isIdle _ = false
isTerminated : ConnectionState → Bool
isTerminated (terminating _ _ _) = true
isTerminated (terminated _) = true
isTerminated _ = false

record Decision : Set where
  constructor decision
  field replacement : Maybe ConnectionState
        continuation : PC
        needsCapacity : Bool
open Decision public

branch : ConnectionKey → EntryId → ConnectionState → Decision
branch k e st@reservedOutbound = decision nothing (complete (unsupported (just st))) false
branch k e st@(unnegotiated _ _ _) = decision nothing (complete (unsupported (just st))) false
branch k e (outboundUni _ w h) = decision (just (outboundIdle k w h unidirectional)) (count (armTimer e w)) false
branch k e (outboundDup _ w h expired) = decision (just (outboundIdle k w h duplex)) (count (armTimer e w)) false
branch k e st@(outboundDup _ w h ticking) = decision (just (inboundIdle k w h duplex)) (count (complete (success (just st)))) true
branch k e st@(outboundIdle _ _ _ _) = decision nothing (count (complete (success (just st)))) false
branch k e st@(inboundIdle _ _ _ _) = decision nothing (count (complete (success (just st)))) false
branch k e st@(inboundActive _ _ _ duplex) = decision nothing (complete (unsupported (just st))) false
branch k e st@(inboundActive _ _ _ unidirectional) = decision nothing (check true (complete (unsupported (just st)))) false
branch k e st@(duplexActive _ w h) = decision (just (inboundActive k w h duplex)) (count (complete (success (just st)))) false
branch k e st@(terminating _ _ _) = decision nothing (count (complete (success (just st)))) false
branch k e st@(terminated _) = decision nothing (count (complete (success (just st)))) false

setPC : Frame → PC → State → Frame × State
setPC f pc s = record f { pc = pc } , s
write : EntryId → ConnectionState → State → State
write e st s = record s { cm = record (cm s) { entries = put e st (entries (cm s)) } }
apply : EntryId → Decision → Frame → State → Frame × State
apply e d f s with replacement d
... | nothing = setPC f (continuation d) s
... | just st = setPC f (continuation d) (write e st s)

-- Entropy is supplied only for an over-limit transaction, and every scored
-- victim write commits atomically before ordered cancellation begins.
capacity : ℕ → Maybe (List ℤ) → ConnMap → EntryId → ConnectionState → Decision → Frame → State → Maybe (Frame × State)
capacity limit scores m e old d f s with needsCapacity d
... | false with scores
...   | nothing = just (apply e d f s)
...   | just _ = nothing
capacity limit scores m e old d f s | true with countIncoming (entries (cm s)) m
... | nothing = nothing
... | just n with suc n ≤? limit
...   | yes _ with scores
...     | nothing = just (apply e d f s)
...     | just _ = nothing
capacity limit scores m e old d f s | true | just n | no _ with scores | replacement d | Prune.candidates m (entries (cm s))
... | just draws | just st | just candidates with Prune.candidateFor (key f) e st
...   | nothing = nothing
...   | just self with Prune.makePlan (suc n ∸ limit) self st candidates draws
...     | nothing = nothing
...     | just selectedPlan with Prune.applyEdits (Prune.edits selectedPlan) s
...       | nothing = nothing
...       | just s′ = just (setPC f (prune (Prune.victims selectedPlan) (success (just old))) s′)
capacity limit scores m e old d f s | true | just n | no _ | _ | _ | _ = nothing

transact : ℕ → Maybe (List ℤ) → Frame → State → Maybe (Frame × State)
transact limit scores f s with mapCell (cm s)
... | taken _ = nothing
... | full m with lookupConnection (key f) m
...   | nothing with scores
...     | nothing = just (setPC f (count (complete (success nothing))) s)
...     | just _ = nothing
transact limit scores f s | full m | just e with lookup e (entries (cm s))
... | nothing = nothing
... | just st = capacity limit scores m e st (branch (key f) e st) f s

data Action : Set where
  transactionStep checkAssertion readCounters registerTimer expireTimer selectWakeup commitTimeout requestCancellation returnResult : Action
  transactionPruning : List ℤ → Action
  cancellationDelivered : WorkerId → Action

step : ℕ → Action → Frame → State → Maybe (Frame × State)
step limit transactionStep f s with pc f
... | transaction = transact limit nothing f s
... | _ = nothing
step limit (transactionPruning scores) f s with pc f
... | transaction = transact limit (just scores) f s
... | _ = nothing
step limit checkAssertion f s with pc f
... | check true next = just (setPC f (complete assertionFailure) s)
... | check false next = just (setPC f next s)
... | _ = nothing
step limit readCounters f s with pc f | mapCell (cm s)
... | count next | full m with countIncoming (entries (cm s)) m
...   | nothing = nothing
...   | just _ = just (setPC f next s)
step limit readCounters f s | _ | _ = nothing
step limit registerTimer f s with pc f
... | armTimer e w = just (record f { pc = waitIdle e w; timerReady = false } , s)
... | _ = nothing
step limit expireTimer f s with pc f | timerReady f
... | waitIdle e w | false = just (record f { timerReady = true } , s)
... | _ | _ = nothing
step limit selectWakeup f s with pc f
... | waitIdle e w with lookup e (entries (cm s))
...   | nothing = nothing
...   | just st with isIdle st | isTerminated st | timerReady f
...     | false | true | _ = just (setPC f (complete (success (just st))) s)
...     | false | false | _ = just (setPC f (complete (unsupported (just st))) s)
...     | true | _ | true = just (setPC f (timeoutWrite e w) s)
...     | true | _ | false = nothing
step limit selectWakeup f s | _ = nothing
step limit commitTimeout f s with pc f
... | timeoutWrite e w with lookup e (entries (cm s))
...   | nothing = nothing
...   | just _ = just (setPC f (count (cancel w (complete (success (just (terminating (key f) w nothing))))))
  (write e (terminating (key f) w nothing) s))
step limit commitTimeout f s | _ = nothing
step limit requestCancellation f s with pc f
... | cancel w next = just (setPC f (delivering w next) s)
... | prune [] result = just (setPC f (count (complete result)) s)
... | prune (victim ∷ rest) result = just (setPC f (delivering (Prune.thread victim) (prune rest result)) s)
... | _ = nothing
step limit (cancellationDelivered w) f s with pc f
... | delivering v next with w ≟ v
...   | yes _ = just (setPC f next s)
...   | no _ = nothing
step limit (cancellationDelivered w) f s | _ = nothing
step limit returnResult f s = nothing -- subsystem consumes complete frames

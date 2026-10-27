{-# OPTIONS --guardedness #-}

-- Physical diffusion Async scopes at the fixed network pin: Diffusion.hs
-- 767-826 and PeerSelectionActions.hs:84-102. These metadata transitions do
-- not implement a thread's local cleanup or certify whole diffusion shutdown.
module ConnectionManagement.Rules.AsyncScope where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

data Actor : Set where
  churn governor localRoot ledger : Actor

data ThreadPhase : Set where
  running cancelRequested cancelDelivered bodyUnwinding bodyExited resultAvailable joined : ThreadPhase

data ClosePC : Set where
  openScope : ClosePC
  closing : Actor → ClosePC
  readyToFinish finishedScope : ClosePC

-- Four concrete phase fields avoid retaining chains of callback closures.
record State : Set where
  constructor scopeState
  field
    churnPhase governorPhase localRootPhase ledgerPhase : ThreadPhase
    cursor : ClosePC
    requestIssued : Bool
open State public

threads : State → Actor → ThreadPhase
threads s churn = churnPhase s
threads s governor = governorPhase s
threads s localRoot = localRootPhase s
threads s ledger = ledgerPhase s

-- Compatibility builder evaluates the supplied table at its four finite keys.
scopes : (Actor → ThreadPhase) → ClosePC → Bool → State
scopes table pc issued = scopeState (table churn) (table governor)
  (table localRoot) (table ledger) pc issued

initial : State
initial = scopes (λ _ → running) openScope false

same : Actor → Actor → Bool
same churn churn = true
same governor governor = true
same localRoot localRoot = true
same ledger ledger = true
same _ _ = false

-- Each update retains the other physical Async handles' observations.
setPhase : Actor → ThreadPhase → (Actor → ThreadPhase) → Actor → ThreadPhase
setPhase actor phase old other with same actor other
... | true = phase
... | false = old other

-- Updates materialize four values immediately; no callback is stored in State.
withPhase : Actor → ThreadPhase → State → State
withPhase actor phase s = scopeState
  (setPhase actor phase (threads s) churn)
  (setPhase actor phase (threads s) governor)
  (setPhase actor phase (threads s) localRoot)
  (setPhase actor phase (threads s) ledger)
  (cursor s) (requestIssued s)

-- These finite observations establish compatibility without function equality.
threads-scopes : ∀ table pc issued actor → threads (scopes table pc issued) actor ≡ table actor
threads-scopes table pc issued churn = refl
threads-scopes table pc issued governor = refl
threads-scopes table pc issued localRoot = refl
threads-scopes table pc issued ledger = refl
threads-withPhase : ∀ actor phase s other →
  threads (withPhase actor phase s) other ≡ setPhase actor phase (threads s) other
threads-withPhase actor phase s churn = refl
threads-withPhase actor phase s governor = refl
threads-withPhase actor phase s localRoot = refl
threads-withPhase actor phase s ledger = refl

isJoined : ThreadPhase → Bool
isJoined joined = true
isJoined _ = false
allJoined : State → Bool
allJoined s = isJoined (threads s churn) ∧ isJoined (threads s governor) ∧
  isJoined (threads s localRoot) ∧ isJoined (threads s ledger)

nextCursor : Actor → ClosePC
nextCursor churn = closing governor
nextCursor governor = closing localRoot
nextCursor localRoot = closing ledger
nextCursor ledger = readyToFinish

-- The Bool passed to step is the adapter's governor-own-pool-closed check.
-- It is consulted only for governor local-body exit, never as whole shutdown.
exitAllowed : Actor → Bool → Bool
exitAllowed governor governorPoolClosed = governorPoolClosed
exitAllowed _ governorPoolClosed = true

canExit : ThreadPhase → Bool
canExit running = true
canExit cancelRequested = true
canExit cancelDelivered = true
canExit bodyUnwinding = true
canExit _ = false

-- Even an already exited/result-available child receives the owner's cancel
-- request before join. A normal exit may outrun cancellation delivery.
requestedPhase : ThreadPhase → ThreadPhase
requestedPhase running = cancelRequested
requestedPhase old = old

data Action : Set where
  beginUnwind requestCancel deliverCancel join finishClose : Action
  beginFailure bodyExit publishResult : Actor → Action

advance : Bool → Action → State → Maybe State
advance governorPoolClosed beginUnwind s with cursor s
... | openScope = just (record s { cursor = closing churn; requestIssued = false })
... | _ = nothing
advance governorPoolClosed requestCancel s with cursor s | requestIssued s
... | closing actor | false with threads s actor
...   | joined = nothing
...   | old = just (record (withPhase actor (requestedPhase old) s) { requestIssued = true })
advance governorPoolClosed requestCancel s | _ | _ = nothing
advance governorPoolClosed deliverCancel s with cursor s | requestIssued s
... | closing actor | true with threads s actor
...   | cancelRequested = just (withPhase actor cancelDelivered s)
...   | _ = nothing
advance governorPoolClosed deliverCancel s | _ | _ = nothing
-- An observed independent exception enters the child's local finally scopes;
-- it is distinct from delivery of the supervising owner's cancellation.
advance governorPoolClosed (beginFailure actor) s with threads s actor
... | running = just (withPhase actor bodyUnwinding s)
... | cancelRequested = just (withPhase actor bodyUnwinding s)
... | _ = nothing
advance governorPoolClosed (bodyExit actor) s with exitAllowed actor governorPoolClosed ∧ canExit (threads s actor)
... | true = just (withPhase actor bodyExited s)
... | false = nothing
advance governorPoolClosed (publishResult actor) s with threads s actor
... | bodyExited = just (withPhase actor resultAvailable s)
... | _ = nothing
advance governorPoolClosed join s with cursor s | requestIssued s
... | closing actor | true with threads s actor
...   | resultAvailable = just (record (withPhase actor joined s) { cursor = nextCursor actor; requestIssued = false })
...   | _ = nothing
advance governorPoolClosed join s | _ | _ = nothing
advance governorPoolClosed finishClose s with cursor s | allJoined s
... | readyToFinish | true = just (record s { cursor = finishedScope })
... | _ | _ = nothing

-- Once all four scope joins have completed, this coordinator is terminal.
closed : State → Bool
closed s with cursor s
... | finishedScope = true
... | _ = false
step : Bool → Action → State → Maybe State
step gate action s with cursor s
... | finishedScope = nothing
... | _ = advance gate action s

-- Finite scope executions establish operational evidence, with no fairness or
-- guarantee that cancellation delivery/local cleanup/result publication occurs.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as gate} → step gate a s ≡ just s₁ →
    Executes s₁ as s₂ → Executes s (a ∷ as) s₂

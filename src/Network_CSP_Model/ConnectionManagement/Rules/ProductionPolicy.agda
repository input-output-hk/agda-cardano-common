{-# OPTIONS --guardedness #-}

-- An explicit peer-job production-policy profile over the open subsystem.
-- The classifier projects the captured source SomeException's dynamic type;
-- it is not a claim that every ioFailure is an IOException or IOManagerError.
-- Handler policy extensions and completed-supervision internals remain outside
-- this profile. The shutdown boundary asserts completion; it does not prove it.
module ConnectionManagement.Rules.ProductionPolicy where

open import Data.Bool using (Bool; true; false; not)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.PeerJobs as Jobs
import ConnectionManagement.Subsystem as Open

-- The base PeerStateActions rethrow policy treats all known CM faults as
-- ShutdownPeer. Only the abstract captured exception may have IOManagerError type.
fatal : (ErrorId → Bool) → Cases.Fault → Bool
fatal isIOManagerError (Cases.ioFailure err) = isIOManagerError err
fatal isIOManagerError Cases.connectionExists = false
fatal isIOManagerError Cases.forbiddenOperation = false
fatal isIOManagerError Cases.forbiddenConnection = false
fatal isIOManagerError Cases.inboundNotFound = false
fatal isIOManagerError Cases.impossibleState = false

-- Preserve the actor and captured fault of the first successful fatal delivery.
data Delivery : Set where
  jobDelivery : JobId → Cases.Fault → Delivery
  monitorDelivery : PeerConnectionId → Cases.Fault → Delivery

data Stage : Set where
  live : Stage
  delivered stopped : Delivery → Stage

record State : Set where
  constructor observed
  field machine : Open.Configuration
        stage : Stage
open State public

data Action : Set where
  dispatch : Open.Action → Action
  completeShutdown : Action

-- A completed shutdown is a stutter on the underlying configuration. It has
-- no fabricated open-system action and carries no cleanup or join theorem.
erase : Action → List Open.Action
erase (dispatch a) = a ∷ []
erase completeShutdown = []
eraseActions : List Action → List Open.Action
eraseActions [] = []
eraseActions (a ∷ as) = erase a ++ eraseActions as

-- Identify acknowledged delivery from the PRE-action fault-bearing frame.
-- Node deliveries by handler lifecycle actions are deliberately not classified.
deliveryOf : Open.Action → Open.Configuration → Maybe Delivery
deliveryOf (Open.jobStep j Jobs.deliverNodeException) c with lookup j (Open.jobs c)
... | nothing = nothing
... | just jf with Jobs.pc (Open.execution jf)
...   | Jobs.nodeDelivery err = just (jobDelivery j err)
...   | _ = nothing
deliveryOf (Open.monitorStep ref Jobs.deliverNodeException) c with lookup ref (Open.monitors c)
... | nothing = nothing
... | just mf with Jobs.pc mf
...   | Jobs.nodeDelivery err = just (monitorDelivery ref err)
...   | _ = nothing
deliveryOf _ c = nothing

-- Delivery permits continued subsystem interleavings. Later fatal deliveries do
-- not erase the first observed actor/fault while supervision remains pending.
noteDelivery : Open.Action → Open.Configuration → Stage → Stage
noteDelivery a c live with deliveryOf a c
... | nothing = live
... | just d = delivered d
noteDelivery a c (delivered d) = delivered d
noteDelivery a c (stopped d) = stopped d

-- A single immutable classifier is used throughout each profile execution.
module Profile (isIOManagerError : ErrorId → Bool) where

  -- No pre-seeded fatal delivery or shutdown stage is assumed by the initializer.
  initial : Open.Configuration → State
  initial c = observed c live

  -- Policy selection and direct delivery both consult the captured fault.
  -- Ordinary job actions keep their underlying guards and effects unchanged.
  actionAllowed : Jobs.Action → Jobs.PC → Bool
  actionAllowed Jobs.choosePeerPolicy (Jobs.acquirePolicy err) = not (fatal isIOManagerError err)
  actionAllowed Jobs.choosePeerPolicy _ = false
  actionAllowed Jobs.chooseNodePolicy (Jobs.acquirePolicy err) = fatal isIOManagerError err
  actionAllowed Jobs.chooseNodePolicy _ = false
  actionAllowed Jobs.deliverNodeException (Jobs.nodeDelivery err) = fatal isIOManagerError err
  actionAllowed Jobs.deliverNodeException _ = false
  -- The same captured fatal fault is rethrown locally after throwTo returns.
  actionAllowed Jobs.rethrowNodeException (Jobs.nodeRethrow err) = fatal isIOManagerError err
  actionAllowed Jobs.rethrowNodeException _ = false
  actionAllowed _ _ = true

  -- Background-monitor jobs obey the same base policy as governor-owned jobs.
  allowed : Open.Action → Open.Configuration → Bool
  allowed (Open.jobStep j a) c with lookup j (Open.jobs c)
  ... | nothing = false
  ... | just jf = actionAllowed a (Jobs.pc (Open.execution jf))
  allowed (Open.monitorStep ref a) c with lookup ref (Open.monitors c)
  ... | nothing = false
  ... | just mf = actionAllowed a (Jobs.pc mf)
  allowed _ c = true

  -- A profile dispatch still requires a real successful open subsystem step.
  dispatchStep : Open.Action → Open.Configuration → Stage → Maybe State
  dispatchStep a c ph with allowed a c
  ... | false = nothing
  ... | true with Open.advance a c
  ...   | nothing = nothing
  ...   | just c′ = just (observed c′ (noteDelivery a c ph))

  -- Acknowledgment alone never terminates the profile. Completion is an explicit
  -- external boundary that is available only after a recorded fatal delivery.
  step : Action → State → Maybe State
  step (dispatch a) (observed c live) = dispatchStep a c live
  step (dispatch a) (observed c (delivered d)) = dispatchStep a c (delivered d)
  step (dispatch a) (observed c (stopped d)) = nothing
  step completeShutdown (observed c live) = nothing
  step completeShutdown (observed c (delivered d)) = just (observed c (stopped d))
  step completeShutdown (observed c (stopped d)) = nothing

  data Executes : State → List Action → State → Set where
    done : ∀ {s} → Executes s [] s
    next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂

  -- Every action is unavailable after the explicit completed-shutdown boundary.
  stopped-step : ∀ a c d → step a (observed c (stopped d)) ≡ nothing
  stopped-step (dispatch a) c d = refl
  stopped-step completeShutdown c d = refl

  -- The profile cannot complete shutdown before it has observed fatal delivery.
  no-early-shutdown : ∀ c → step completeShutdown (initial c) ≡ nothing
  no-early-shutdown c = refl

  -- Filtering does not manufacture an underlying dispatcher transition.
  dispatch-projects : ∀ a c ph {s′} → dispatchStep a c ph ≡ just s′ →
    Open.Executes c (a ∷ []) (machine s′)
  dispatch-projects a c ph eq with allowed a c
  ... | false = case eq of λ ()
  ... | true with Open.advance a c in advanced
  ...   | nothing = case eq of λ ()
  ...   | just c′ with just-injective eq
  ...     | refl = Open.next advanced Open.done

  -- Erasure keeps each ordinary step and removes only completed-shutdown stutter.
  step-projects : ∀ a s {s′} → step a s ≡ just s′ →
    Open.Executes (machine s) (erase a) (machine s′)
  step-projects (dispatch a) (observed c live) eq = dispatch-projects a c live eq
  step-projects (dispatch a) (observed c (delivered d)) eq = dispatch-projects a c (delivered d) eq
  step-projects (dispatch a) (observed c (stopped d)) ()
  step-projects completeShutdown (observed c live) ()
  step-projects completeShutdown (observed c (delivered d)) eq with just-injective eq
  ... | refl = Open.done
  step-projects completeShutdown (observed c (stopped d)) ()

  -- Compose projected fragments without introducing a new operational semantics.
  append-exec : ∀ {c as c₁ bs c₂} → Open.Executes c as c₁ → Open.Executes c₁ bs c₂ →
    Open.Executes c (as ++ bs) c₂
  append-exec Open.done tail = tail
  append-exec (Open.next eq path) tail = Open.next eq (append-exec path tail)

  exec-projects : ∀ {s as s′} → Executes s as s′ →
    Open.Executes (machine s) (eraseActions as) (machine s′)
  exec-projects done = Open.done
  exec-projects (next {s = s} {a = a} eq path) = append-exec (step-projects a s eq) (exec-projects path)

  -- Reuse any existing open-subsystem safety invariant, including the stuttering
  -- shutdown boundary. This proves preservation only, not source refinement.
  module Lift
    (Predicate : Open.Configuration → Set)
    (preserve : ∀ a c {c′} → Open.advance a c ≡ just c′ → Predicate c → Predicate c′) where

    Valid : State → Set
    Valid s = Predicate (machine s)

    projected-preserves : ∀ {c as c′} → Open.Executes c as c′ → Predicate c → Predicate c′
    projected-preserves Open.done valid = valid
    projected-preserves (Open.next {c = c} {a = a} eq path) valid =
      projected-preserves path (preserve a c eq valid)

    step-preserves : ∀ a s {s′} → step a s ≡ just s′ → Valid s → Valid s′
    step-preserves a s eq = projected-preserves (step-projects a s eq)

    exec-preserves : ∀ {s as s′} → Executes s as s′ → Valid s → Valid s′
    exec-preserves path = projected-preserves (exec-projects path)

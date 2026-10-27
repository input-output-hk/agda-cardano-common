{-# OPTIONS --guardedness #-}

-- A bounded pre-handshake physical-handler profile over real dispatcher writes.
-- Children enter the registry only at an observed inbound Server.fork. No
-- existing handler heap is adopted as physical Async history; negotiated mux
-- bodies and their pools are outside this profile.
module ConnectionManagement.HandlerSupervision where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.CMShutdown as Close

-- mkMuxBearer setup precedes the catch around restored runHandshake. A setup
-- cancellation at an observed interruptible operation has no promise write.
data Phase : Set where
  maskedSetup handshaking : Phase
  caughtCancellation cancellationPublished bodyExited finalizing : ErrorId → Phase
  cleanupComplete resultAvailable : ErrorId → S.CleanupOutcome → Phase
record Thread : Set where
  constructor handlerThread
  field captured : S.HandlerStart
        phase : Phase
open Thread public
record State : Set where
  constructor supervised
  field source : M.Configuration
        threads : Store WorkerId Thread
        shutdown : Close.State
open State public

-- This initializer admits no unrecorded pre-existing physical handlers.
initial : M.Configuration → Maybe State
initial c with S.handlers (M.world c) | S.cleanups (M.world c) |
  M.handlerLifecycles c | M.publicationFaults c
... | [] | [] | [] | [] = just (supervised c [] Close.initialState)
... | _ | _ | _ | _ = nothing

-- The source finally's exception overrides the body cancellation on failure.
-- Preserve both details in the phase and expose the effective Async exception.
effectiveError : ErrorId → S.CleanupOutcome → ErrorId
effectiveError original S.cleanupNormal = original
effectiveError original (S.cleanupError err) = err
resultReady : WorkerId → State → Bool
resultReady w s with lookup w (threads s)
... | just t with phase t
...   | resultAvailable _ _ = true
...   | _ = false
resultReady w s | nothing = false

-- Transparent helpers separate actual Machine writes from registry metadata.
setSource : M.Configuration → State → State
setSource c s = record s { source = c }
setPhase : WorkerId → Thread → Phase → State → State
setPhase w t p s = record s { threads = put w (record t { phase = p }) (threads s) }
dispatch : M.Action → State → Maybe State
dispatch action s with M.advance action (source s)
... | nothing = nothing
... | just c = just (setSource c s)
dispatchPhase : M.Action → WorkerId → Thread → Phase → State → Maybe State
dispatchPhase action w t p s with dispatch action s
... | nothing = nothing
... | just next = just (setPhase w t p next)

-- Capture the actual new child and its original HandlerStart atomically with
-- the actual admission fork; later CM key reuse never redirects this history.
forkAdmission : WorkerId → State → Maybe State
forkAdmission w s with lookup w (S.admissions (M.world (source s)))
... | nothing = nothing
... | just a with lookup (S.child (S.request a)) (threads s)
...   | just old = nothing
...   | nothing with M.advance (M.admissionStep w Server.fork) (source s)
...     | nothing = nothing
...     | just c with lookup (S.child (S.request a)) (S.handlers (M.world c))
...       | nothing = nothing
...       | just h = just (record (setSource c s)
  { threads = put (S.child (S.request a)) (handlerThread h maskedSetup) (threads s) })

-- Physical thread transitions cannot be bypassed through the open dispatcher.
-- Ordinary unrelated admission/consumer/IG operations retain their own guards.
rawAllowed : M.Action → Bool
rawAllowed (M.handlerPublication _ _ _) = false
rawAllowed (M.handlerExit _) = false
rawAllowed (M.handlerStep _ _) = false
rawAllowed (M.cleanupStep _ _) = false
rawAllowed (M.releaseStep (Release.cancellationDelivered _)) = false
rawAllowed (M.remoteStep (Remote.pruneCancellationDelivered _)) = false
rawAllowed _ = true

-- A delivery is a local unwind entry, not handler exit or an Async result.
deliverHandshake : WorkerId → ErrorId → State → Maybe State
deliverHandshake w err s with lookup w (threads s)
... | just t with phase t
...   | handshaking = just (setPhase w t (caughtCancellation err) s)
...   | _ = nothing
deliverHandshake w err s | nothing = nothing
deliverBlockedSetup : WorkerId → ErrorId → State → Maybe State
deliverBlockedSetup w err s with lookup w (threads s)
... | just t with phase t
...   | maskedSetup = just (setPhase w t (bodyExited err) s)
...   | _ = nothing
deliverBlockedSetup w err s | nothing = nothing

-- The coordinator receives only this registry's physical-result observation.
-- Delivery acknowledgment is private to the coupled delivery actions below.
acknowledge : State → Maybe State
acknowledge s with Close.step (S.cm (M.world (source s))) (λ w → resultReady w s)
  Close.acknowledgeDelivery (shutdown s)
... | nothing = nothing
... | just next = just (record s { shutdown = next })
deliverShutdown : Bool → ErrorId → State → Maybe State
deliverShutdown blocked err s with Close.phase (shutdown s)
... | Close.awaitDelivery e w with blocked
...   | false with deliverHandshake w err s
...     | nothing = nothing
...     | just next = acknowledge next
deliverShutdown blocked err s | Close.awaitDelivery e w | true with deliverBlockedSetup w err s
...     | nothing = nothing
...     | just next = acknowledge next
deliverShutdown blocked err s | _ = nothing

-- TIME_WAIT is an interruptible part of the already-entered finalizer. Its
-- actual finally continuation still terminates/purges the captured entry.
deliverTimeWait : ErrorId → State → Maybe State
deliverTimeWait err s with Close.phase (shutdown s)
... | Close.awaitDelivery e w with lookup w (threads s) | lookup w (S.cleanups (M.world (source s)))
...   | just t | just (S.cleanupWaiting captured) with phase t
...     | finalizing original with dispatch (M.cleanupStep w (Cleanup.interruptTimeWait err)) s
...       | nothing = nothing
...       | just next = acknowledge next
deliverTimeWait err s | Close.awaitDelivery e w | just t | just (S.cleanupWaiting captured) | _ = nothing
deliverTimeWait err s | Close.awaitDelivery e w | _ | _ = nothing
deliverTimeWait err s | _ = nothing

data Action : Set where
  run : M.Action → Action
  enterHandshake : WorkerId → Action
  deliverHandshakeCancellation deliverBlockedSetupCancellation : WorkerId → ErrorId → Action
  publishCaught rethrowCaught enterFinalizer finishCleanup publishAsyncResult : WorkerId → Action
  cleanup : WorkerId → Cleanup.CleanupAction → Action
  shutdownStep : Close.Action → Action
  deliverShutdownHandshake deliverShutdownBlockedSetup deliverShutdownTimeWait : ErrorId → Action
  acknowledgeFinished : Action

step : Action → State → Maybe State
step (run (M.admissionStep w Server.fork)) s = forkAdmission w s
step (run action) s with rawAllowed action
... | false = nothing
... | true = dispatch action s
step (enterHandshake w) s with lookup w (threads s)
... | just t with phase t
...   | maskedSetup = just (setPhase w t handshaking s)
...   | _ = nothing
step (enterHandshake w) s | nothing = nothing
step (deliverHandshakeCancellation w err) s = deliverHandshake w err s
step (deliverBlockedSetupCancellation w err) s = deliverBlockedSetup w err s
-- ConnectionHandler.hs:337-346,414-425 catches the handshake exception, writes
-- Left(HandlerError err), then rethrows it. classifyHandlerError:199 projects
-- that generic HandlerError to protocolViolation, not negotiationFailure.
step (publishCaught w) s with lookup w (threads s)
... | just t with phase t
...   | caughtCancellation err = dispatchPhase
  (M.handlerPublication w (S.handlerError S.protocolViolation err) M.resultWritten)
  w t (cancellationPublished err) s
...   | _ = nothing
step (publishCaught w) s | nothing = nothing
step (rethrowCaught w) s with lookup w (threads s)
... | just t with phase t
...   | cancellationPublished err = just (setPhase w t (bodyExited err) s)
...   | _ = nothing
step (rethrowCaught w) s | nothing = nothing
step (enterFinalizer w) s with lookup w (threads s)
... | just t with phase t
...   | bodyExited err = dispatchPhase (M.handlerExit w) w t (finalizing err) s
...   | _ = nothing
step (enterFinalizer w) s | nothing = nothing
step (cleanup w action) s with lookup w (threads s)
... | just t with phase t
...   | finalizing err = dispatch (M.cleanupStep w action) s
...   | _ = nothing
step (cleanup w action) s | nothing = nothing
step (finishCleanup w) s with lookup w (threads s) | lookup w (S.cleanups (M.world (source s)))
... | just t | just (S.cleanupDone outcome) with phase t
...   | finalizing err = just (setPhase w t (cleanupComplete err outcome) s)
...   | _ = nothing
step (finishCleanup w) s | _ | _ = nothing
step (publishAsyncResult w) s with lookup w (threads s) | lookup w (S.cleanups (M.world (source s)))
... | just t | just (S.cleanupDone outcome) with phase t
...   | cleanupComplete err observed = just (setPhase w t (resultAvailable err outcome) s)
...   | _ = nothing
step (publishAsyncResult w) s | _ | _ = nothing
step (shutdownStep Close.acknowledgeDelivery) s = nothing
step (shutdownStep action) s with Close.step (S.cm (M.world (source s)))
  (λ w → resultReady w s) action (shutdown s)
... | nothing = nothing
... | just next = just (record s { shutdown = next })
step (deliverShutdownHandshake err) s = deliverShutdown false err s
step (deliverShutdownBlockedSetup err) s = deliverShutdown true err s
step (deliverShutdownTimeWait err) s = deliverTimeWait err s
step acknowledgeFinished s with Close.phase (shutdown s)
... | Close.awaitDelivery e w with resultReady w s
...   | true = acknowledge s
...   | false = nothing
step acknowledgeFinished s | _ = nothing

-- Closing the fixed CM snapshot leaves independent admissions and their later
-- children enabled. No fairness, successful-close, or whole-node exit is asserted.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂

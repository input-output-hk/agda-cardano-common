{-# OPTIONS --guardedness #-}

-- Exact allowed edits of the tracked runtime, witnessed from the actual rules.
-- This proof layer does not constrain execution or change Machine.advance.
module ConnectionManagement.Properties.HandlerEvolution where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Data.Maybe.Properties using (just-injective)
open import Class.DecEq using (DecEq; _≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State hiding (capturedMux)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote

-- Fresh attachment excludes both duplicate worker keys and shared mux owners.
-- Later edits only update a frame phase using the frame actually found.
data Evolution : L.Runtime → L.Runtime → Set where
  unchanged : ∀ {rt} → Evolution rt rt
  attached : ∀ w f rt → lookup w rt ≡ nothing →
    L.hasMux (L.capturedMux f) rt ≡ false → Evolution rt (put w f rt)
  phaseChanged : ∀ w f p rt → lookup w rt ≡ just f →
    Evolution rt (L.setPhase w f p rt)

-- Match only attachment's actual success case; it inserts an absent worker.
attach-evolves : ∀ w err rt ig s {rt′ ig′} →
  L.attachMux w err rt ig s ≡ just (rt′ , ig′) → Evolution rt rt′
attach-evolves w err rt ig s eq with lookup w rt in absent | lookup w (handlers s) | lookup w (cleanups s)
... | nothing | just h | nothing with lookup (handlerPromise h) (handshakeResults s)
...   | just (negotiated hid _) with lookup hid (IG.handles (IG.execution ig))
...     | just hd with lookup (M.muxRef hd) (IG.muxes (IG.execution ig)) | L.hasMux (M.muxRef hd) rt in unused
...       | just m | false with M.status m | M.callback m
...         | M.ready | M.returned = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (attached w (L.frame (M.muxRef hd) err L.monitoring) rt absent unused)
...         | M.stopping | _ = case eq of λ ()
...         | M.stopped | _ = case eq of λ ()
...         | M.failed _ | _ = case eq of λ ()
...         | M.ready | M.readActive _ = case eq of λ ()
...         | M.ready | M.commitTrace _ _ = case eq of λ ()
...         | M.ready | M.afterStart _ = case eq of λ ()
...         | M.ready | M.forkPending _ = case eq of λ ()
...         | M.ready | M.afterFailure = case eq of λ ()
...         | M.ready | M.tracerFailed _ = case eq of λ ()
attach-evolves w err rt ig s eq | nothing | just h | nothing | just (negotiated hid _) | just hd | nothing | _ = case eq of λ ()
attach-evolves w err rt ig s eq | nothing | just h | nothing | just (negotiated hid _) | just hd | just _ | true = case eq of λ ()
attach-evolves w err rt ig s eq | nothing | just h | nothing | just (negotiated hid _) | nothing = case eq of λ ()
attach-evolves w err rt ig s eq | nothing | just h | nothing | nothing = case eq of λ ()
attach-evolves w err rt ig s eq | nothing | just h | nothing | just query = case eq of λ ()
attach-evolves w err rt ig s eq | nothing | just h | nothing | just (handlerError _ _) = case eq of λ ()
attach-evolves _ _ _ _ _ eq | just _ | _ | _ = case eq of λ ()
attach-evolves _ _ _ _ _ eq | nothing | nothing | _ = case eq of λ ()
attach-evolves _ _ _ _ _ eq | nothing | just _ | just _ = case eq of λ ()

-- All lifecycle actions preserve every existing capture, not only their own.
step-evolves : ∀ w a rt ig s {rt′ ig′} →
  L.step w a rt ig s ≡ just (rt′ , ig′) → Evolution rt rt′
step-evolves w (L.attach err) rt ig s eq = attach-evolves w err rt ig s eq
step-evolves w L.jobPoolClosed rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.poolClosing | just m = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.poolClosed) rt owned)
...   | L.normalClosing | just m = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.normalClosed) rt owned)
...   | L.syncClosing err | just m = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.syncClosed err) rt owned)
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.monitoring | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.poolClosing | nothing = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.poolClosed | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.deadTracing | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.normalClosing | nothing = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.syncClosing err | nothing = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-evolves w L.jobPoolClosed rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.poolClosed | just m = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.deadTracing) rt owned)
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.monitoring | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.poolClosing | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.poolClosed | nothing = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.deadTracing | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.normalClosing | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.syncClosing err | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-evolves w L.publishAsyncFailure rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.deadTracing | just m with M.callback m
...     | M.readActive _ = case eq of λ ()
...     | M.commitTrace _ _ = case eq of λ ()
...     | M.afterStart _ = case eq of λ ()
...     | M.forkPending _ = case eq of λ ()
...     | M.afterFailure = case eq of λ ()
...     | M.tracerFailed _ = case eq of λ ()
...     | M.returned = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.bodyExited) rt owned)
step-evolves w L.finishRethrow rt ig s eq | just f | L.monitoring | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.poolClosing | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.poolClosed | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.deadTracing | nothing = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.normalClosing | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.syncClosing err | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-evolves w L.finishRethrow rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.monitoring | just m with M.status m | M.callback m
...     | M.stopped | M.returned = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.normalClosing) rt owned)
...     | M.ready | _ = case eq of λ ()
...     | M.stopping | _ = case eq of λ ()
...     | M.failed _ | _ = case eq of λ ()
...     | M.stopped | M.readActive _ = case eq of λ ()
...     | M.stopped | M.commitTrace _ _ = case eq of λ ()
...     | M.stopped | M.afterStart _ = case eq of λ ()
...     | M.stopped | M.forkPending _ = case eq of λ ()
...     | M.stopped | M.afterFailure = case eq of λ ()
...     | M.stopped | M.tracerFailed _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.monitoring | nothing = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.poolClosing | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.poolClosed | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.deadTracing | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.normalClosing | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.syncClosing err | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-evolves w L.monitorReturned rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.monitoring | just m with M.status m | M.callback m
...     | M.failed fault | M.returned = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.syncClosing fault) rt owned)
...     | M.ready | _ = case eq of λ ()
...     | M.stopping | _ = case eq of λ ()
...     | M.stopped | _ = case eq of λ ()
...     | M.failed _ | M.readActive _ = case eq of λ ()
...     | M.failed _ | M.commitTrace _ _ = case eq of λ ()
...     | M.failed _ | M.afterStart _ = case eq of λ ()
...     | M.failed _ | M.forkPending _ = case eq of λ ()
...     | M.failed _ | M.afterFailure = case eq of λ ()
...     | M.failed _ | M.tracerFailed _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.monitoring | nothing = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.poolClosing | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.poolClosed | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.deadTracing | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.normalClosing | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.syncClosing err | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-evolves w L.monitorThrew rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.monitoring | just m with M.callback m
...     | M.readActive _ = case eq of λ ()
...     | M.commitTrace _ _ = case eq of λ ()
...     | M.afterStart _ = case eq of λ ()
...     | M.forkPending _ = case eq of λ ()
...     | M.afterFailure = case eq of λ ()
...     | M.tracerFailed _ = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.syncClosing fault) rt owned)
...     | M.returned = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.monitoring | nothing = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.poolClosing | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.poolClosed | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.deadTracing | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.normalClosing | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.syncClosing err | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-evolves w (L.tracerThrew fault) rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f
...   | L.normalClosed = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.normalBodyExited) rt owned)
...   | L.syncClosed err = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.classifying err) rt owned)
step-evolves w L.finishBuffer rt ig s eq | just f | L.monitoring = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.poolClosing = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.poolClosed = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.deadTracing = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.bodyExited = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.finalizing = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.normalClosing = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.normalBodyExited = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.syncClosing err = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.classifying err = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.peerRethrow err = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.nodeDelivery err = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.nodeRethrow err = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.peerBodyExited err = case eq of λ ()
step-evolves w L.finishBuffer rt ig s eq | just f | L.nodeBodyExited err = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f
...   | L.classifying err with policy
...     | L.shutdownPeer = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.peerRethrow err) rt owned)
...     | L.shutdownNode = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.nodeDelivery err) rt owned)
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.monitoring = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.poolClosing = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.poolClosed = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.deadTracing = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.bodyExited = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.finalizing = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.normalClosing = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.normalClosed = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.normalBodyExited = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.syncClosing err = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.syncClosed err = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.peerRethrow err = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.nodeDelivery err = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.nodeRethrow err = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.peerBodyExited err = case eq of λ ()
step-evolves w (L.choosePolicy policy) rt ig s eq | just f | L.nodeBodyExited err = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f
...   | L.nodeDelivery err = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.nodeRethrow err) rt owned)
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.monitoring = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.poolClosing = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.poolClosed = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.deadTracing = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.bodyExited = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.finalizing = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.normalClosing = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.normalClosed = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.normalBodyExited = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.syncClosing err = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.syncClosed err = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.classifying err = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.peerRethrow err = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.nodeRethrow err = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.peerBodyExited err = case eq of λ ()
step-evolves w L.nodeExceptionDelivered rt ig s eq | just f | L.nodeBodyExited err = case eq of λ ()
step-evolves w L.rethrow rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f
...   | L.peerRethrow err = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.peerBodyExited err) rt owned)
...   | L.nodeRethrow err = subst (λ pair → Evolution rt (proj₁ pair)) (just-injective eq)
  (phaseChanged w f (L.nodeBodyExited err) rt owned)
step-evolves w L.rethrow rt ig s eq | just f | L.monitoring = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.poolClosing = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.poolClosed = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.deadTracing = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.bodyExited = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.finalizing = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.normalClosing = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.normalClosed = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.normalBodyExited = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.syncClosing err = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.syncClosed err = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.classifying err = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.nodeDelivery err = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.peerBodyExited err = case eq of λ ()
step-evolves w L.rethrow rt ig s eq | just f | L.nodeBodyExited err = case eq of λ ()

-- Delivery and finalizer entry change phases without recapturing the mux.
delivery-evolves : ∀ w rt → Evolution rt (L.noteDelivery w rt)
delivery-evolves w rt with lookup w rt in owned
... | nothing = unchanged
... | just f with L.phase f
...   | L.monitoring = phaseChanged w f L.poolClosing rt owned
...   | L.poolClosing = unchanged
...   | L.poolClosed = unchanged
...   | L.deadTracing = unchanged
...   | L.bodyExited = unchanged
...   | L.finalizing = unchanged
...   | L.normalClosing = unchanged
...   | L.normalClosed = unchanged
...   | L.normalBodyExited = unchanged
...   | L.syncClosing err = unchanged
...   | L.syncClosed err = unchanged
...   | L.classifying err = unchanged
...   | L.peerRethrow err = unchanged
...   | L.nodeDelivery err = unchanged
...   | L.nodeRethrow err = unchanged
...   | L.peerBodyExited err = unchanged
...   | L.nodeBodyExited err = unchanged
exit-evolves : ∀ w rt → Evolution rt (L.noteExit w rt)
exit-evolves w rt with lookup w rt in owned
... | nothing = unchanged
... | just f = phaseChanged w f L.finalizing rt owned
release-evolves : ∀ a rt → Evolution rt (L.noteRelease a rt)
release-evolves (Release.cancellationDelivered w) rt = delivery-evolves w rt
release-evolves Release.enter rt = unchanged
release-evolves Release.transact rt = unchanged
release-evolves Release.readCounters rt = unchanged
release-evolves Release.requestCancellation rt = unchanged
release-evolves Release.checkAssertion rt = unchanged
release-evolves Release.returnToIG rt = unchanged
remote-evolves : ∀ a rt → Evolution rt (L.noteRemote a rt)
remote-evolves (Remote.pruneCancellationDelivered w) rt = delivery-evolves w rt
remote-evolves Remote.enter rt = unchanged
remote-evolves Remote.transact rt = unchanged
remote-evolves Remote.checkAssertion rt = unchanged
remote-evolves Remote.readCounters rt = unchanged
remote-evolves Remote.returnToIG rt = unchanged
remote-evolves Remote.requestPruneCancellation rt = unchanged
remote-evolves (Remote.transactPruning _ _) rt = unchanged

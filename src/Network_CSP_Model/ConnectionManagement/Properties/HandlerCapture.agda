{-# OPTIONS --guardedness #-}

-- Immutable captured mux identity. This theorem says nothing about whether the
-- captured mux exists or whether two workers share it; validity is separate.
module ConnectionManagement.Properties.HandlerCapture where

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
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote

-- Each prior lookup still resolves to a frame with the same captured mux.
Retains : L.Runtime → L.Runtime → Set
Retains before after = ∀ w f → lookup w before ≡ just f →
  Σ L.Frame (λ g → lookup w after ≡ just g × L.capturedMux g ≡ L.capturedMux f)
retains-refl : ∀ rt → Retains rt rt
retains-refl rt w f found = f , found , refl
retains-trans : ∀ {r₀ r₁ r₂} → Retains r₀ r₁ → Retains r₁ r₂ → Retains r₀ r₂
retains-trans left right w f found with left w f found
... | g , fg , same with right w g fg
...   | h , gh , same′ = h , gh , trans same′ same

-- A store write at a different key preserves the complete lookup value.
lookup-put-other : ∀ {K V} ⦃ _ : DecEq K ⦄ (w q : K) (v : V) xs →
  q ≢ w → lookup q (put w v xs) ≡ lookup q xs
lookup-put-other w q v [] neq with q ≟ w
... | yes eq = ⊥-elim (neq eq)
... | no _ = refl
lookup-put-other w q v ((r , old) ∷ xs) neq with w ≟ r
... | yes refl with q ≟ r
...   | yes eq = ⊥-elim (neq eq)
...   | no _ = refl
lookup-put-other w q v ((r , old) ∷ xs) neq | no _ with q ≟ r
... | yes _ = refl
... | no _ = lookup-put-other w q v xs neq

phase-retains : ∀ w f p rt → lookup w rt ≡ just f → Retains rt (L.setPhase w f p rt)
phase-retains w f p rt owned q old found with q ≟ w
... | yes refl = record f { phase = p } , lookup-put w (record f { phase = p }) rt ,
  cong L.capturedMux (just-injective (trans (sym owned) found))
... | no neq = old , trans (lookup-put-other w q (record f { phase = p }) rt neq) found , refl
fresh-retains : ∀ w f rt → lookup w rt ≡ nothing → Retains rt (put w f rt)
fresh-retains w f rt absent q old found with q ≟ w
... | yes refl = case trans (sym absent) found of λ ()
... | no neq = old , trans (lookup-put-other w q f rt neq) found , refl

-- Match only attachment's actual success case; it inserts an absent worker.
attach-retains : ∀ w err rt ig s {rt′ ig′} →
  L.attachMux w err rt ig s ≡ just (rt′ , ig′) → Retains rt rt′
attach-retains w err rt ig s eq with lookup w rt in absent | lookup w (handlers s) | lookup w (cleanups s)
... | nothing | just h | nothing with lookup (handlerPromise h) (handshakeResults s)
...   | just (negotiated hid _) with lookup hid (IG.handles (IG.execution ig))
...     | just hd with lookup (M.muxRef hd) (IG.muxes (IG.execution ig)) | L.hasMux (M.muxRef hd) rt
...       | just m | false with M.status m | M.callback m
...         | M.ready | M.returned = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (fresh-retains w (L.frame (M.muxRef hd) err L.monitoring) rt absent)
...         | M.stopping | _ = case eq of λ ()
...         | M.stopped | _ = case eq of λ ()
...         | M.failed _ | _ = case eq of λ ()
...         | M.ready | M.readActive _ = case eq of λ ()
...         | M.ready | M.commitTrace _ _ = case eq of λ ()
...         | M.ready | M.afterStart _ = case eq of λ ()
...         | M.ready | M.forkPending _ = case eq of λ ()
...         | M.ready | M.afterFailure = case eq of λ ()
...         | M.ready | M.tracerFailed _ = case eq of λ ()
attach-retains w err rt ig s eq | nothing | just h | nothing | just (negotiated hid _) | just hd | nothing | _ = case eq of λ ()
attach-retains w err rt ig s eq | nothing | just h | nothing | just (negotiated hid _) | just hd | just _ | true = case eq of λ ()
attach-retains w err rt ig s eq | nothing | just h | nothing | just (negotiated hid _) | nothing = case eq of λ ()
attach-retains w err rt ig s eq | nothing | just h | nothing | nothing = case eq of λ ()
attach-retains w err rt ig s eq | nothing | just h | nothing | just query = case eq of λ ()
attach-retains w err rt ig s eq | nothing | just h | nothing | just (handlerError _ _) = case eq of λ ()
attach-retains _ _ _ _ _ eq | just _ | _ | _ = case eq of λ ()
attach-retains _ _ _ _ _ eq | nothing | nothing | _ = case eq of λ ()
attach-retains _ _ _ _ _ eq | nothing | just _ | just _ = case eq of λ ()

-- All lifecycle actions preserve every existing capture, not only their own.
step-retains : ∀ w a rt ig s {rt′ ig′} →
  L.step w a rt ig s ≡ just (rt′ , ig′) → Retains rt rt′
step-retains w (L.attach err) rt ig s eq = attach-retains w err rt ig s eq
step-retains w L.jobPoolClosed rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.poolClosing | just m = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.poolClosed) rt owned)
...   | L.normalClosing | just m = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.normalClosed) rt owned)
...   | L.syncClosing err | just m = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.syncClosed err) rt owned)
step-retains w L.jobPoolClosed rt ig s eq | just f | L.monitoring | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.poolClosing | nothing = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.poolClosed | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.deadTracing | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.normalClosing | nothing = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.syncClosing err | nothing = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-retains w L.jobPoolClosed rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.poolClosed | just m = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.deadTracing) rt owned)
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.monitoring | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.poolClosing | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.poolClosed | nothing = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.deadTracing | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.normalClosing | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.syncClosing err | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-retains w L.publishAsyncFailure rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.deadTracing | just m with M.callback m
...     | M.readActive _ = case eq of λ ()
...     | M.commitTrace _ _ = case eq of λ ()
...     | M.afterStart _ = case eq of λ ()
...     | M.forkPending _ = case eq of λ ()
...     | M.afterFailure = case eq of λ ()
...     | M.tracerFailed _ = case eq of λ ()
...     | M.returned = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.bodyExited) rt owned)
step-retains w L.finishRethrow rt ig s eq | just f | L.monitoring | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.poolClosing | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.poolClosed | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.deadTracing | nothing = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.normalClosing | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.syncClosing err | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-retains w L.finishRethrow rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.monitoring | just m with M.status m | M.callback m
...     | M.stopped | M.returned = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.normalClosing) rt owned)
...     | M.ready | _ = case eq of λ ()
...     | M.stopping | _ = case eq of λ ()
...     | M.failed _ | _ = case eq of λ ()
...     | M.stopped | M.readActive _ = case eq of λ ()
...     | M.stopped | M.commitTrace _ _ = case eq of λ ()
...     | M.stopped | M.afterStart _ = case eq of λ ()
...     | M.stopped | M.forkPending _ = case eq of λ ()
...     | M.stopped | M.afterFailure = case eq of λ ()
...     | M.stopped | M.tracerFailed _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.monitoring | nothing = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.poolClosing | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.poolClosed | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.deadTracing | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.normalClosing | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.syncClosing err | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-retains w L.monitorReturned rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.monitoring | just m with M.status m | M.callback m
...     | M.failed fault | M.returned = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.syncClosing fault) rt owned)
...     | M.ready | _ = case eq of λ ()
...     | M.stopping | _ = case eq of λ ()
...     | M.stopped | _ = case eq of λ ()
...     | M.failed _ | M.readActive _ = case eq of λ ()
...     | M.failed _ | M.commitTrace _ _ = case eq of λ ()
...     | M.failed _ | M.afterStart _ = case eq of λ ()
...     | M.failed _ | M.forkPending _ = case eq of λ ()
...     | M.failed _ | M.afterFailure = case eq of λ ()
...     | M.failed _ | M.tracerFailed _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.monitoring | nothing = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.poolClosing | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.poolClosed | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.deadTracing | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.normalClosing | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.syncClosing err | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-retains w L.monitorThrew rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f | lookup (L.capturedMux f) (IG.muxes (IG.execution ig))
...   | L.monitoring | just m with M.callback m
...     | M.readActive _ = case eq of λ ()
...     | M.commitTrace _ _ = case eq of λ ()
...     | M.afterStart _ = case eq of λ ()
...     | M.forkPending _ = case eq of λ ()
...     | M.afterFailure = case eq of λ ()
...     | M.tracerFailed _ = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.syncClosing fault) rt owned)
...     | M.returned = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.monitoring | nothing = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.poolClosing | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.poolClosed | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.deadTracing | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.bodyExited | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.finalizing | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.normalClosing | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.normalClosed | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.normalBodyExited | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.syncClosing err | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.syncClosed err | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.classifying err | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.peerRethrow err | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.nodeDelivery err | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.nodeRethrow err | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.peerBodyExited err | _ = case eq of λ ()
step-retains w (L.tracerThrew fault) rt ig s eq | just f | L.nodeBodyExited err | _ = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f
...   | L.normalClosed = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.normalBodyExited) rt owned)
...   | L.syncClosed err = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.classifying err) rt owned)
step-retains w L.finishBuffer rt ig s eq | just f | L.monitoring = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.poolClosing = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.poolClosed = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.deadTracing = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.bodyExited = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.finalizing = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.normalClosing = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.normalBodyExited = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.syncClosing err = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.classifying err = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.peerRethrow err = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.nodeDelivery err = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.nodeRethrow err = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.peerBodyExited err = case eq of λ ()
step-retains w L.finishBuffer rt ig s eq | just f | L.nodeBodyExited err = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f
...   | L.classifying err with policy
...     | L.shutdownPeer = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.peerRethrow err) rt owned)
...     | L.shutdownNode = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.nodeDelivery err) rt owned)
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.monitoring = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.poolClosing = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.poolClosed = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.deadTracing = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.bodyExited = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.finalizing = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.normalClosing = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.normalClosed = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.normalBodyExited = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.syncClosing err = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.syncClosed err = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.peerRethrow err = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.nodeDelivery err = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.nodeRethrow err = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.peerBodyExited err = case eq of λ ()
step-retains w (L.choosePolicy policy) rt ig s eq | just f | L.nodeBodyExited err = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f
...   | L.nodeDelivery err = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.nodeRethrow err) rt owned)
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.monitoring = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.poolClosing = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.poolClosed = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.deadTracing = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.bodyExited = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.finalizing = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.normalClosing = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.normalClosed = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.normalBodyExited = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.syncClosing err = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.syncClosed err = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.classifying err = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.peerRethrow err = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.nodeRethrow err = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.peerBodyExited err = case eq of λ ()
step-retains w L.nodeExceptionDelivered rt ig s eq | just f | L.nodeBodyExited err = case eq of λ ()
step-retains w L.rethrow rt ig s eq with lookup w rt in owned
... | nothing = case eq of λ ()
... | just f with L.phase f
...   | L.peerRethrow err = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.peerBodyExited err) rt owned)
...   | L.nodeRethrow err = subst (λ pair → Retains rt (proj₁ pair)) (just-injective eq)
  (phase-retains w f (L.nodeBodyExited err) rt owned)
step-retains w L.rethrow rt ig s eq | just f | L.monitoring = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.poolClosing = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.poolClosed = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.deadTracing = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.bodyExited = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.finalizing = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.normalClosing = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.normalClosed = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.normalBodyExited = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.syncClosing err = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.syncClosed err = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.classifying err = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.nodeDelivery err = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.peerBodyExited err = case eq of λ ()
step-retains w L.rethrow rt ig s eq | just f | L.nodeBodyExited err = case eq of λ ()

-- Delivery and finalizer entry change phases without recapturing the mux.
delivery-retains : ∀ w rt → Retains rt (L.noteDelivery w rt)
delivery-retains w rt with lookup w rt in owned
... | nothing = retains-refl rt
... | just f with L.phase f
...   | L.monitoring = phase-retains w f L.poolClosing rt owned
...   | L.poolClosing = retains-refl rt
...   | L.poolClosed = retains-refl rt
...   | L.deadTracing = retains-refl rt
...   | L.bodyExited = retains-refl rt
...   | L.finalizing = retains-refl rt
...   | L.normalClosing = retains-refl rt
...   | L.normalClosed = retains-refl rt
...   | L.normalBodyExited = retains-refl rt
...   | L.syncClosing err = retains-refl rt
...   | L.syncClosed err = retains-refl rt
...   | L.classifying err = retains-refl rt
...   | L.peerRethrow err = retains-refl rt
...   | L.nodeDelivery err = retains-refl rt
...   | L.nodeRethrow err = retains-refl rt
...   | L.peerBodyExited err = retains-refl rt
...   | L.nodeBodyExited err = retains-refl rt
exit-retains : ∀ w rt → Retains rt (L.noteExit w rt)
exit-retains w rt with lookup w rt in owned
... | nothing = retains-refl rt
... | just f = phase-retains w f L.finalizing rt owned
release-retains : ∀ a rt → Retains rt (L.noteRelease a rt)
release-retains (Release.cancellationDelivered w) rt = delivery-retains w rt
release-retains Release.enter rt = retains-refl rt
release-retains Release.transact rt = retains-refl rt
release-retains Release.readCounters rt = retains-refl rt
release-retains Release.requestCancellation rt = retains-refl rt
release-retains Release.checkAssertion rt = retains-refl rt
release-retains Release.returnToIG rt = retains-refl rt
remote-retains : ∀ a rt → Retains rt (L.noteRemote a rt)
remote-retains (Remote.pruneCancellationDelivered w) rt = delivery-retains w rt
remote-retains Remote.enter rt = retains-refl rt
remote-retains Remote.transact rt = retains-refl rt
remote-retains Remote.checkAssertion rt = retains-refl rt
remote-retains Remote.readCounters rt = retains-refl rt
remote-retains Remote.returnToIG rt = retains-refl rt
remote-retains Remote.requestPruneCancellation rt = retains-refl rt
remote-retains (Remote.transactPruning _ _) rt = retains-refl rt

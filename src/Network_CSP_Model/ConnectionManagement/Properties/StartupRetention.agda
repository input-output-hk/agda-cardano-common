{-# OPTIONS --guardedness #-}

-- Startup, restart and failed-start stop requests retain original references.
module ConnectionManagement.Properties.StartupRetention where

open import Data.Bool using (true; false)
open import Data.List using (_++_; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerAnchors using (Anchors; setMux-preserves)
open import ConnectionManagement.Properties.MuxStartReferences using (one-key; bundle-key)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as L

-- Moving the IG continuation leaves the retained engine evidence intact.
control-anchors : ∀ old n pc {ig ig′} → Anchors ig ig′ →
  Anchors ig (IG.runtimeState old n pc (IG.execution ig′))
control-anchors old n pc anchors = record
  { handlesSame = Anchors.handlesSame anchors
  ; muxesRetained = Anchors.muxesRetained anchors }

data CoveredStartup : IG.IGAction → Set where
  start : CoveredStartup IG.runResponders
  restart : CoveredStartup IG.restart
  failedStop : CoveredStartup IG.requestFailedStop

worker-anchors : ∀ a → CoveredStartup a → ∀ ig queue {ig′ queue′} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Anchors ig ig′
worker-anchors .IG.runResponders start ig queue eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = case eq of λ ()
... | IG.armInactivity t = case eq of λ ()
... | IG.awaitBatch t tid = case eq of λ ()
... | IG.readNext t rest = case eq of λ ()
... | IG.prepareNew t info rest old = case eq of λ ()
... | IG.publishDecision t rest old = case eq of λ ()
... | IG.stopAfterFailure t rest mid n err = case eq of λ ()
... | IG.waitStopped t rest k mid old = case eq of λ ()
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.startResponders t info rest old tid with lookup (negotiatedHandle info) (IG.handles (IG.execution ig))
...   | nothing = case eq of λ ()
...   | just hd with lookup (M.muxRef hd) (IG.muxes (IG.execution ig)) in found
...     | nothing = case eq of λ ()
...     | just m with M.startBundle (M.bundle hd) m | bundle-key (M.bundle hd) m
...       | M.startedAll updated | same with just-injective eq
...         | refl = control-anchors _ _ _ (setMux-preserves (M.muxRef hd) m updated ig found same)
worker-anchors .IG.runResponders start ig queue eq | IG.startResponders t info rest old tid | just hd | just m | M.startFailed n err updated | same with just-injective eq
... | refl = control-anchors _ _ _ (setMux-preserves (M.muxRef hd) m updated ig found same)
worker-anchors .IG.restart restart ig queue eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = case eq of λ ()
... | IG.armInactivity t = case eq of λ ()
... | IG.awaitBatch t tid = case eq of λ ()
... | IG.readNext t rest = case eq of λ ()
... | IG.prepareNew t info rest old = case eq of λ ()
... | IG.startResponders t info rest old tid = case eq of λ ()
... | IG.publishDecision t rest old = case eq of λ ()
... | IG.stopAfterFailure t rest mid n err = case eq of λ ()
... | IG.waitStopped t rest k mid old = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.restartResponder t rest term with lookup (capturedMux term) (IG.muxes (IG.execution ig)) in found
...   | nothing = case eq of λ ()
...   | just m with M.startOne (descriptor term) m | one-key (descriptor term) m
...     | M.startedAll updated | same with just-injective eq
...       | refl = control-anchors _ _ _ (setMux-preserves (capturedMux term) m updated ig found same)
worker-anchors .IG.restart restart ig queue eq | IG.restartResponder t rest term | just m | M.startFailed n err updated | same with just-injective eq
... | refl = control-anchors _ _ _ (setMux-preserves (capturedMux term) m updated ig found same)
worker-anchors .IG.requestFailedStop failedStop ig queue eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = case eq of λ ()
... | IG.armInactivity t = case eq of λ ()
... | IG.awaitBatch t tid = case eq of λ ()
... | IG.readNext t rest = case eq of λ ()
... | IG.prepareNew t info rest old = case eq of λ ()
... | IG.startResponders t info rest old tid = case eq of λ ()
... | IG.publishDecision t rest old = case eq of λ ()
... | IG.waitStopped t rest k mid old = case eq of λ ()
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.stopAfterFailure t rest mid n err with lookup mid (IG.muxes (IG.execution ig)) in found
...   | nothing = case eq of λ ()
...   | just m with just-injective eq
...     | refl = control-anchors _ _ _
  (setMux-preserves mid m (record m { commands = M.commands m ++ (M.shutdown ∷ []) }) ig found refl)

mode-anchors : ∀ mode a → CoveredStartup a → ∀ ig queue {ig′ queue′} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Anchors ig ig′
mode-anchors noResponderMode .IG.runResponders start ig queue ()
mode-anchors noResponderMode .IG.restart restart ig queue ()
mode-anchors noResponderMode .IG.requestFailedStop failedStop ig queue ()
mode-anchors responderMode a covered ig queue eq = worker-anchors a covered ig queue eq

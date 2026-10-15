{-# OPTIONS --guardedness #-}

-- Startup, restart and failed-start stop requests retain original references.
module ConnectionManagement.Properties.HandlerIGStartup where

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
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerAnchors using (setMux-preserves)
open import ConnectionManagement.Properties.HandlerIGBoundary using (control-chain; queue-chain)
open import ConnectionManagement.Properties.MuxStartReferences using (one-key; bundle-key)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as L

data CoveredStartup : IG.IGAction → Set where
  start : CoveredStartup IG.runResponders
  restart : CoveredStartup IG.restart
  failedStop : CoveredStartup IG.requestFailedStop

worker-chain : ∀ a → CoveredStartup a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
worker-chain .IG.runResponders start ig queue s eq chain with IG.continuation ig
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
...         | refl = control-chain _ _ _ (anchors-preserve-chain (setMux-preserves (M.muxRef hd) m updated ig found same) chain)
worker-chain .IG.runResponders start ig queue s eq chain | IG.startResponders t info rest old tid | just hd | just m | M.startFailed n err updated | same with just-injective eq
... | refl = control-chain _ _ _ (anchors-preserve-chain (setMux-preserves (M.muxRef hd) m updated ig found same) chain)
worker-chain .IG.restart restart ig queue s eq chain with IG.continuation ig
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
...       | refl = control-chain _ _ _ (anchors-preserve-chain (setMux-preserves (capturedMux term) m updated ig found same) chain)
worker-chain .IG.restart restart ig queue s eq chain | IG.restartResponder t rest term | just m | M.startFailed n err updated | same with just-injective eq
... | refl = control-chain _ _ _ (anchors-preserve-chain (setMux-preserves (capturedMux term) m updated ig found same) chain)
worker-chain .IG.requestFailedStop failedStop ig queue s eq chain with IG.continuation ig
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
...     | refl = control-chain _ _ _ (anchors-preserve-chain
  (setMux-preserves mid m (record m { commands = M.commands m ++ (M.shutdown ∷ []) }) ig found refl) chain)

mode-chain : ∀ mode a → CoveredStartup a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
mode-chain noResponderMode a covered ig queue s () chain
mode-chain responderMode a covered ig queue s eq chain = worker-chain a covered ig queue s eq chain

step-preserves : ∀ a → CoveredStartup a → ∀ c {c′} → advance (igStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves a covered c eq q (f , found , chain) with L.allowIG a (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c)) in stepped
...   | nothing = case eq of λ ()
...   | just (ig′ , queue′) with just-injective eq
...     | refl = f , found , queue-chain queue′
  (mode-chain (responder c) a covered (inboundGovernor c) (inboundInfo (world c)) (world c) stepped chain)

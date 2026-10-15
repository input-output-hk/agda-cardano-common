{-# OPTIONS --guardedness #-}

-- IG control-loop actions may alter membership, timers and queue, but retain
-- installed handles and muxes. This is reference safety, not progress.
module ConnectionManagement.Properties.LoopRetention where

open import Data.Bool using (true; false)
open import Data.Nat using (_≤?_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerAnchors using (Anchors; setMux-preserves)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.IGBatch as Batch
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as L

-- Engine equality is sufficient; membership and control are unconstrained.
stable-anchors : ∀ {ig ig′} →
  IG.handles (IG.execution ig′) ≡ IG.handles (IG.execution ig) →
  IG.muxes (IG.execution ig′) ≡ IG.muxes (IG.execution ig) → Anchors ig ig′
stable-anchors handlesSame muxesSame =
  record { handlesSame = handlesSame
         ; muxesRetained = λ mid m found → m , trans (cong (lookup mid) muxesSame) found , refl }

-- readOne only selects a continuation, even for captured-mux restart/wait events.
read-engine : ∀ time event rest ig → IG.execution (IG.readOne time event rest ig) ≡ IG.execution ig
read-engine time (newConnection info) rest ig with lookup (connectionKey info) (IG.connections (IG.publishedState ig))
... | nothing = refl
... | just _ = refl
read-engine time (maturedDuplexPeers ms fs) rest ig = refl
read-engine time inactivityTimeout rest ig = refl
read-engine time (remotePromotedToHot k) rest ig = refl
read-engine time (remoteDemotedToWarm k) rest ig = refl
read-engine time (muxFinished k) rest ig with lookup k (IG.connections (IG.publishedState ig))
... | nothing = refl
... | just reg with lookup (negotiatedHandle (IG.notification reg)) (IG.handles (IG.execution ig))
...   | nothing = refl
...   | just _ = refl
read-engine time (miniProtocolTerminated term) rest ig with result term
... | errored _ = refl
... | clean with lookup (peer term) (IG.connections (IG.publishedState ig))
...   | nothing = refl
...   | just _ = refl
read-engine time (waitIdleRemote k) rest ig = refl
read-engine time (commitRemote k) rest ig = refl
read-engine time (awakeRemote k) rest ig = refl

data CoveredLoop : IG.IGAction → Set where
  deactivate : CoveredLoop IG.deactivateIG
  flush : CoveredLoop IG.flushOnExit
  capture : ∀ {time} → CoveredLoop (IG.captureTime time)
  inactivity : CoveredLoop IG.registerInactivity
  select : CoveredLoop IG.selectBatch
  read : CoveredLoop IG.readEvent
  idleTimer : CoveredLoop IG.registerIdleTimer
  finish : CoveredLoop IG.finishBatch
  poll : CoveredLoop IG.pollStopped
  expire : ∀ {tid} → CoveredLoop (IG.expireTimer tid)

worker-anchors : ∀ a → CoveredLoop a → ∀ ig queue {ig′ queue′} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Anchors ig ig′
worker-anchors .IG.deactivateIG deactivate ig queue eq with IG.active (IG.execution ig)
... | false = case eq of λ ()
... | true with just-injective eq
...   | refl = stable-anchors refl refl
worker-anchors .(IG.expireTimer tid) (expire {tid}) ig queue eq with lookup tid (IG.timers (IG.execution ig))
... | nothing = case eq of λ ()
... | just expired = case eq of λ ()
... | just ticking with just-injective eq
...   | refl = stable-anchors refl refl
worker-anchors .IG.flushOnExit flush ig queue eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
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
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.exitFlush with just-injective eq
...   | refl = stable-anchors refl refl
worker-anchors .(IG.captureTime time) (capture {time}) ig queue eq with IG.continuation ig
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
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.sampleTime with IG.lastTime (IG.execution ig) ≤? time
...   | no _ = case eq of λ ()
...   | yes _ with just-injective eq
...     | refl = stable-anchors refl refl
worker-anchors .IG.registerInactivity inactivity ig queue eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = case eq of λ ()
... | IG.awaitBatch t tid = case eq of λ ()
... | IG.readNext t rest = case eq of λ ()
... | IG.prepareNew t info rest old = case eq of λ ()
... | IG.startResponders t info rest old tid = case eq of λ ()
... | IG.publishDecision t rest old = case eq of λ ()
... | IG.stopAfterFailure t rest mid n err = case eq of λ ()
... | IG.waitStopped t rest k mid old = case eq of λ ()
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.armInactivity t with just-injective eq
...   | refl = stable-anchors refl refl
worker-anchors .IG.selectBatch select ig queue eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = case eq of λ ()
... | IG.armInactivity t = case eq of λ ()
... | IG.readNext t rest = case eq of λ ()
... | IG.prepareNew t info rest old = case eq of λ ()
... | IG.startResponders t info rest old tid = case eq of λ ()
... | IG.publishDecision t rest old = case eq of λ ()
... | IG.stopAfterFailure t rest mid n err = case eq of λ ()
... | IG.waitStopped t rest k mid old = case eq of λ ()
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.awaitBatch t tid with Batch.selectBatch (IG.maturity t (IG.publishedState ig))
  (IG.commitCandidate (IG.execution ig) (IG.publishedState ig)) (IG.expiredTimer tid (IG.execution ig)) inactivityTimeout queue
...   | nothing = case eq of λ ()
...   | just chosen with just-injective eq
...     | refl = stable-anchors refl refl
worker-anchors .IG.readEvent read ig queue eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = case eq of λ ()
... | IG.armInactivity t = case eq of λ ()
... | IG.awaitBatch t tid = case eq of λ ()
... | IG.prepareNew t info rest old = case eq of λ ()
... | IG.startResponders t info rest old tid = case eq of λ ()
... | IG.publishDecision t rest old = case eq of λ ()
... | IG.stopAfterFailure t rest mid n err = case eq of λ ()
... | IG.waitStopped t rest k mid old = case eq of λ ()
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.readNext t [] = case eq of λ ()
... | IG.readNext t (event ∷ rest) with just-injective eq
...   | refl = stable-anchors (cong IG.handles (read-engine t event rest ig))
  (cong IG.muxes (read-engine t event rest ig))
worker-anchors .IG.registerIdleTimer idleTimer ig queue eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = case eq of λ ()
... | IG.armInactivity t = case eq of λ ()
... | IG.awaitBatch t tid = case eq of λ ()
... | IG.readNext t rest = case eq of λ ()
... | IG.startResponders t info rest old tid = case eq of λ ()
... | IG.publishDecision t rest old = case eq of λ ()
... | IG.stopAfterFailure t rest mid n err = case eq of λ ()
... | IG.waitStopped t rest k mid old = case eq of λ ()
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.prepareNew t info rest old with just-injective eq
...   | refl = stable-anchors refl refl
worker-anchors .IG.registerIdleTimer idleTimer ig queue eq | IG.awaitRemoteIdle t k rest old with just-injective eq
...   | refl = stable-anchors refl refl
worker-anchors .IG.finishBatch finish ig queue eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = case eq of λ ()
... | IG.armInactivity t = case eq of λ ()
... | IG.awaitBatch t tid = case eq of λ ()
... | IG.prepareNew t info rest old = case eq of λ ()
... | IG.startResponders t info rest old tid = case eq of λ ()
... | IG.publishDecision t rest old = case eq of λ ()
... | IG.stopAfterFailure t rest mid n err = case eq of λ ()
... | IG.waitStopped t rest k mid old = case eq of λ ()
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.readNext t (_ ∷ _) = case eq of λ ()
... | IG.readNext t [] with just-injective eq
...   | refl = stable-anchors refl refl
worker-anchors .IG.pollStopped poll ig queue eq with IG.continuation ig
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
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old = case eq of λ ()
... | IG.waitStopped t rest k mid old with lookup mid (IG.muxes (IG.execution ig))
...   | nothing = case eq of λ ()
...   | just m with M.status m
...     | M.ready = case eq of λ ()
...     | M.stopping = case eq of λ ()
...     | M.stopped with just-injective eq
...       | refl = stable-anchors refl refl
worker-anchors .IG.pollStopped poll ig queue eq | IG.waitStopped t rest k mid old | just m | M.failed err with just-injective eq
... | refl = stable-anchors refl refl

mode-anchors : ∀ mode a → CoveredLoop a → ∀ ig queue {ig′ queue′} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Anchors ig ig′
mode-anchors noResponderMode a covered ig queue ()
mode-anchors responderMode a covered ig queue eq = worker-anchors a covered ig queue eq

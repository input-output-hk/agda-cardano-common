{-# OPTIONS --guardedness #-}

-- IG control-loop actions may alter membership, timers and queue, but retain
-- installed handles and muxes. This is reference safety, not progress.
module ConnectionManagement.Properties.HandlerIGLoop where

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
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerIGBoundary using (queue-chain)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.IGBatch as Batch
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as L

stable-chain : ∀ {ig ig′ q mid s} →
  IG.handles (IG.execution ig′) ≡ IG.handles (IG.execution ig) →
  IG.muxes (IG.execution ig′) ≡ IG.muxes (IG.execution ig) →
  Chain q mid s ig → Chain q mid s ig′
stable-chain handlesSame muxesSame = anchors-preserve-chain
  (record { handlesSame = handlesSame
          ; muxesRetained = λ mid m found → m , trans (cong (lookup mid) muxesSame) found , refl })

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

worker-chain : ∀ a → CoveredLoop a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
worker-chain .IG.deactivateIG deactivate ig queue s eq chain with IG.active (IG.execution ig)
... | false = case eq of λ ()
... | true with just-injective eq
...   | refl = stable-chain refl refl chain
worker-chain .(IG.expireTimer tid) (expire {tid}) ig queue s eq chain with lookup tid (IG.timers (IG.execution ig))
... | nothing = case eq of λ ()
... | just expired = case eq of λ ()
... | just ticking with just-injective eq
...   | refl = stable-chain refl refl chain
worker-chain .IG.flushOnExit flush ig queue s eq chain with IG.continuation ig
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
...   | refl = stable-chain refl refl chain
worker-chain .(IG.captureTime time) (capture {time}) ig queue s eq chain with IG.continuation ig
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
...     | refl = stable-chain refl refl chain
worker-chain .IG.registerInactivity inactivity ig queue s eq chain with IG.continuation ig
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
...   | refl = stable-chain refl refl chain
worker-chain .IG.selectBatch select ig queue s eq chain with IG.continuation ig
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
...     | refl = stable-chain refl refl chain
worker-chain .IG.readEvent read ig queue s eq chain with IG.continuation ig
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
...   | refl = stable-chain (cong IG.handles (read-engine t event rest ig))
  (cong IG.muxes (read-engine t event rest ig)) chain
worker-chain .IG.registerIdleTimer idleTimer ig queue s eq chain with IG.continuation ig
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
...   | refl = stable-chain refl refl chain
worker-chain .IG.registerIdleTimer idleTimer ig queue s eq chain | IG.awaitRemoteIdle t k rest old with just-injective eq
...   | refl = stable-chain refl refl chain
worker-chain .IG.finishBatch finish ig queue s eq chain with IG.continuation ig
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
...   | refl = stable-chain refl refl chain
worker-chain .IG.pollStopped poll ig queue s eq chain with IG.continuation ig
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
...       | refl = stable-chain refl refl chain
worker-chain .IG.pollStopped poll ig queue s eq chain | IG.waitStopped t rest k mid old | just m | M.failed err with just-injective eq
... | refl = stable-chain refl refl chain

mode-chain : ∀ mode a → CoveredLoop a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
mode-chain noResponderMode a covered ig queue s () chain
mode-chain responderMode a covered ig queue s eq chain = worker-chain a covered ig queue s eq chain

step-preserves : ∀ a → CoveredLoop a → ∀ c {c′} → advance (igStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves a covered c eq q (f , found , chain) with L.allowIG a (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c)) in stepped
...   | nothing = case eq of λ ()
...   | just (ig′ , queue′) with just-injective eq
...     | refl = f , found , queue-chain queue′
  (mode-chain (responder c) a covered (inboundGovernor c) (inboundInfo (world c)) (world c) stepped chain)

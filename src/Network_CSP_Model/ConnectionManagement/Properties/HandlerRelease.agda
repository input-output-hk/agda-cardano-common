{-# OPTIONS --guardedness #-}

-- Entry edits retain resource identities; release changes only IG control state.
module ConnectionManagement.Properties.HandlerRelease where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (put-preserves-present)
open import ConnectionManagement.Properties.HandlerCleanup using (reframe)
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerAnchors using (Anchors)
open import ConnectionManagement.Properties.HandlerCapture using (release-retains)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.InboundRelease as R
import ConnectionManagement.Rules.Pruning as P
import ConnectionManagement.Rules.IGRegistration as IG

-- Successful arbitrary edits preserve every existing chain, not just the victim.
edit-chain : ∀ edit s {s′ q mid ig} → R.applyEdit edit s ≡ just s′ → Chain q mid s ig → Chain q mid s′ ig
edit-chain nothing s refl chain = chain
edit-chain (just (e , st)) s eq chain with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just _ with just-injective eq
...   | refl = reframe _ _ _ (λ q → put-preserves-present e q st (entries (cm s))) (λ _ p → p) chain

-- Atomic pruning batches can contain many writes, including repeated targets.
-- Only successful application has an endpoint; failure exposes no partial state.
edits-chain : ∀ edits s {s′ q mid ig} → P.applyEdits edits s ≡ just s′ → Chain q mid s ig → Chain q mid s′ ig
edits-chain [] s refl chain = chain
edits-chain (edit ∷ edits) s eq chain with R.applyEdit (just edit) s in applied
... | nothing = case eq of λ ()
... | just s₁ = edits-chain edits s₁ eq (edit-chain (just edit) s applied chain)

-- Equal engines suffice even when the governor continuation changes.
engine-anchors : ∀ {ig ig′} → IG.execution ig′ ≡ IG.execution ig → Anchors ig ig′
engine-anchors refl = record { handlesSame = refl; muxesRetained = λ mid m found → m , found , refl }

select-execution : ∀ f ig s {p} → R.select f ig s ≡ just p → IG.execution (R.governor p) ≡ IG.execution ig
select-execution f ig s eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with lookupConnection (R.key f) m
...   | nothing with just-injective eq
...     | refl = refl
select-execution f ig s eq | full m | just e with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st with R.branch st f
...   | nothing , f′ with just-injective eq
...     | refl = refl
select-execution f ig s eq | full m | just e | just st | just st′ , f′ with just-injective eq
... | refl = refl

worker-execution : ∀ a f ig s {p} → R.stepWorker a f ig s ≡ just p → IG.execution (R.governor p) ≡ IG.execution ig
worker-execution R.transact f ig s eq with R.pc f
... | R.counters = case eq of λ ()
... | R.cancellation = case eq of λ ()
... | R.assertion = case eq of λ ()
... | R.returning = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.delivering v = case eq of λ ()
... | R.transaction = select-execution f ig s eq
worker-execution R.readCounters f ig s eq with R.pc f
... | R.transaction = case eq of λ ()
... | R.cancellation = case eq of λ ()
... | R.assertion = case eq of λ ()
... | R.returning = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.delivering v = case eq of λ ()
... | R.counters with mapCell (cm s)
...   | taken _ = case eq of λ ()
...   | full m with countIncoming (entries (cm s)) m
...     | nothing = case eq of λ ()
...     | just _ with just-injective eq
...       | refl = refl
worker-execution R.requestCancellation f ig s eq with R.pc f
... | R.transaction = case eq of λ ()
... | R.counters = case eq of λ ()
... | R.assertion = case eq of λ ()
... | R.returning = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.delivering v = case eq of λ ()
... | R.cancellation with R.target f
...   | nothing with just-injective eq
...     | refl = refl
worker-execution R.requestCancellation f ig s eq | R.cancellation | just w with just-injective eq
... | refl = refl
worker-execution (R.cancellationDelivered w) f ig s eq with R.pc f
... | R.transaction = case eq of λ ()
... | R.counters = case eq of λ ()
... | R.cancellation = case eq of λ ()
... | R.assertion = case eq of λ ()
... | R.returning = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.delivering v with w ≟ v
...   | no _ = case eq of λ ()
...   | yes _ with just-injective eq
...     | refl = refl
worker-execution R.checkAssertion f ig s eq with R.pc f
... | R.transaction = case eq of λ ()
... | R.counters = case eq of λ ()
... | R.cancellation = case eq of λ ()
... | R.returning = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.delivering v = case eq of λ ()
... | R.assertion with R.deferredAssertion f
...   | true with just-injective eq
...     | refl = refl
worker-execution R.checkAssertion f ig s eq | R.assertion | false with just-injective eq
... | refl = refl
worker-execution R.returnToIG f ig s eq with R.pc f
... | R.transaction = case eq of λ ()
... | R.counters = case eq of λ ()
... | R.cancellation = case eq of λ ()
... | R.assertion = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.delivering v = case eq of λ ()
... | R.returning with just-injective eq
...   | refl = refl
worker-execution R.enter f ig s eq = case eq of λ ()

release-execution : ∀ a pending ig s {p} → R.step a pending ig s ≡ just p → IG.execution (R.governor p) ≡ IG.execution ig
release-execution R.enter nothing ig s eq with IG.continuation ig
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
... | IG.restartResponder t rest term = case eq of λ ()
... | IG.awaitRemoteIdle t k rest old = case eq of λ ()
... | IG.needsCM t rest event old with event
...   | commitRemote k with just-injective eq
...     | refl = refl
release-execution R.enter nothing ig s eq | IG.needsCM t rest event old | (newConnection info) = case eq of λ ()
release-execution R.enter nothing ig s eq | IG.needsCM t rest event old | (miniProtocolTerminated term) = case eq of λ ()
release-execution R.enter nothing ig s eq | IG.needsCM t rest event old | (muxFinished k) = case eq of λ ()
release-execution R.enter nothing ig s eq | IG.needsCM t rest event old | (awakeRemote k) = case eq of λ ()
release-execution R.enter nothing ig s eq | IG.needsCM t rest event old | (waitIdleRemote k) = case eq of λ ()
release-execution R.enter nothing ig s eq | IG.needsCM t rest event old | (remotePromotedToHot k) = case eq of λ ()
release-execution R.enter nothing ig s eq | IG.needsCM t rest event old | (remoteDemotedToWarm k) = case eq of λ ()
release-execution R.enter nothing ig s eq | IG.needsCM t rest event old | (maturedDuplexPeers peers fresh) = case eq of λ ()
release-execution R.enter nothing ig s eq | IG.needsCM t rest event old | inactivityTimeout = case eq of λ ()
release-execution R.transact nothing ig s eq = case eq of λ ()
release-execution R.readCounters nothing ig s eq = case eq of λ ()
release-execution R.requestCancellation nothing ig s eq = case eq of λ ()
release-execution (R.cancellationDelivered w) nothing ig s eq = case eq of λ ()
release-execution R.checkAssertion nothing ig s eq = case eq of λ ()
release-execution R.returnToIG nothing ig s eq = case eq of λ ()
release-execution R.enter (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution R.enter f ig s eq
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

release-execution R.transact (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution R.transact f ig s eq
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

release-execution R.readCounters (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution R.readCounters f ig s eq
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

release-execution R.requestCancellation (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution R.requestCancellation f ig s eq
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

release-execution (R.cancellationDelivered w) (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution (R.cancellationDelivered w) f ig s eq
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

release-execution R.checkAssertion (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution R.checkAssertion f ig s eq
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

release-execution R.returnToIG (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution R.returnToIG f ig s eq
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

-- The real dispatcher applies the edit atomically and may note cancellation.
step-preserves : ∀ a c {c′} → advance (releaseStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves a c eq q (f , found , chain) with L.allowRelease a (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with R.step a (inboundRelease c) (inboundGovernor c) (world c) in stepped
...   | nothing = case eq of λ ()
...   | just p with R.applyEdit (R.edit p) (world c) in applied
...     | nothing = case eq of λ ()
...     | just s with just-injective eq
...       | refl with release-retains a (handlerLifecycles c) q f found
...         | g , retained , same = g , retained , subst (λ mid → Chain q mid s (R.governor p)) (sym same)
  (anchors-preserve-chain (engine-anchors (release-execution a (inboundRelease c) (inboundGovernor c) (world c) stepped))
    (edit-chain (R.edit p) (world c) applied chain))

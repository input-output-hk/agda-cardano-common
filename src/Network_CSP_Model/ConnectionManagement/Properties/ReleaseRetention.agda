{-# OPTIONS --guardedness #-}

-- Entry edits retain resource identities; release changes only IG control state.
module ConnectionManagement.Properties.ReleaseRetention where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; trans)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (put-preserves-present)
open import ConnectionManagement.Properties.CleanupRetention using (Retains; retains; reframe)
import ConnectionManagement.Properties.CleanupRetention as Cleanup
open import ConnectionManagement.Properties.HandlerAnchors using (Anchors)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.InboundRelease as R
import ConnectionManagement.Rules.Pruning as P
import ConnectionManagement.Rules.IGRegistration as IG

-- Compose effects for an atomic batch; no successful partial endpoint escapes.
compose-retains : ∀ {s t u} → Retains s t → Retains t u → Retains s u
compose-retains a b = retains
  (trans (Cleanup.handlersSame b) (Cleanup.handlersSame a))
  (trans (Cleanup.resultsSame b) (Cleanup.resultsSame a))
  (λ e p → Cleanup.entriesRetained b e (Cleanup.entriesRetained a e p))
  (λ sock p → Cleanup.socketsRetained b sock (Cleanup.socketsRetained a sock p))

edit-retains : ∀ edit s {s′} → R.applyEdit edit s ≡ just s′ → Retains s s′
edit-retains nothing s refl = retains refl refl (λ _ p → p) (λ _ p → p)
edit-retains (just (e , st)) s eq with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just _ with just-injective eq
...   | refl = reframe _ _ _ (λ q → put-preserves-present e q st (entries (cm s))) (λ _ p → p)

edits-retains : ∀ edits s {s′} → P.applyEdits edits s ≡ just s′ → Retains s s′
edits-retains [] s refl = retains refl refl (λ _ p → p) (λ _ p → p)
edits-retains (edit ∷ edits) s eq with R.applyEdit (just edit) s in applied
... | nothing = case eq of λ ()
... | just s₁ = compose-retains (edit-retains (just edit) s applied) (edits-retains edits s₁ eq)

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

-- Include lifecycle guards and the actual atomic world edit from advance.
step-effects : ∀ a c {c′} → advance (releaseStep a) c ≡ just c′ →
  Retains (world c) (world c′) × Anchors (inboundGovernor c) (inboundGovernor c′)
step-effects a c eq with L.allowRelease a (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with R.step a (inboundRelease c) (inboundGovernor c) (world c) in stepped
...   | nothing = case eq of λ ()
...   | just p with R.applyEdit (R.edit p) (world c) in applied
...     | nothing = case eq of λ ()
...     | just s with just-injective eq
...       | refl = edit-retains (R.edit p) (world c) applied ,
  engine-anchors (release-execution a (inboundRelease c) (inboundGovernor c) (world c) stepped)

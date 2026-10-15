{-# OPTIONS --guardedness #-}

-- Remote promotion/demotion, including scored pruning, retain original chains.
module ConnectionManagement.Properties.RemoteRetention where

open import Data.Bool using (true; false)
open import Data.Nat using (suc; _≤?_)
import Data.Nat as Nat
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.CleanupRetention using (Retains)
open import ConnectionManagement.Properties.HandlerAnchors using (Anchors)
open import ConnectionManagement.Properties.ReleaseRetention using (edits-retains; engine-anchors)
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.RemoteState as R
import ConnectionManagement.Rules.Pruning as P
import ConnectionManagement.Rules.IGRegistration as IG

commit-execution : ∀ e d f ig → IG.execution (R.governor (R.commitDecision e d f ig)) ≡ IG.execution ig
commit-execution e d f ig with R.replacement d
... | nothing = refl
... | just _ = refl
plain-execution : ∀ scores e d f ig {p} → R.plainDecision scores e d f ig ≡ just p → IG.execution (R.governor p) ≡ IG.execution ig
plain-execution nothing e d f ig refl = commit-execution e d f ig
plain-execution (just _) e d f ig ()
prune-execution : ∀ n m e d f ig s scores {p} → R.pruneDecision n m e d f ig s scores ≡ just p → IG.execution (R.governor p) ≡ IG.execution ig
prune-execution n m e d f ig s scores eq with R.replacement d | P.candidates m (entries (cm s))
... | nothing | _ = case eq of λ ()
... | just _ | nothing = case eq of λ ()
... | just st | just cs with P.candidateFor (R.key f) e st
...   | nothing = case eq of λ ()
...   | just self with P.makePlan n self st cs scores
...     | nothing = case eq of λ ()
...     | just selectedPlan with just-injective eq
...       | refl = refl
capacity-execution : ∀ limit scores m e d f ig s {p} → R.capacityDecision limit scores m e d f ig s ≡ just p → IG.execution (R.governor p) ≡ IG.execution ig
capacity-execution limit scores m e d f ig s eq with R.needsCapacity d
... | false = plain-execution scores e d f ig eq
... | true with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just n with suc n ≤? limit
...     | yes _ = plain-execution scores e d f ig eq
...     | no _ with scores
...       | nothing = case eq of λ ()
...       | just draws = prune-execution _ m e d f ig s draws eq
select-execution : ∀ limit scores f ig s {p} → R.select limit scores f ig s ≡ just p → IG.execution (R.governor p) ≡ IG.execution ig
select-execution limit scores f ig s eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with lookupConnection (R.key f) m
...   | nothing with scores
...     | just _ = case eq of λ ()
...     | nothing with just-injective eq
...       | refl = refl
select-execution limit scores f ig s eq | full m | just e with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st = capacity-execution limit scores m e (R.choose f st) f ig s eq

worker-execution : ∀ limit generation a f ig s {p} → R.stepWorker limit generation a f ig s ≡ just p → IG.execution (R.governor p) ≡ IG.execution ig
worker-execution limit generation R.transact f ig s eq with R.pc f
... | R.assertion = case eq of λ ()
... | R.counters = case eq of λ ()
... | R.returning = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.cancellationNext victims = case eq of λ ()
... | R.awaitDelivery victim rest = case eq of λ ()
... | R.transaction = select-execution limit nothing f ig s eq
worker-execution limit generation (R.transactPruning ticket scores) f ig s eq with R.pc f
... | R.assertion = case eq of λ ()
... | R.counters = case eq of λ ()
... | R.returning = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.cancellationNext victims = case eq of λ ()
... | R.awaitDelivery victim rest = case eq of λ ()
... | R.transaction with ticket Nat.≟ generation
...   | no _ = case eq of λ ()
...   | yes _ = select-execution limit (just scores) f ig s eq
worker-execution limit generation R.requestPruneCancellation f ig s eq with R.pc f
... | R.transaction = case eq of λ ()
... | R.assertion = case eq of λ ()
... | R.counters = case eq of λ ()
... | R.returning = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.awaitDelivery victim rest = case eq of λ ()
... | R.cancellationNext victims with victims
...   | [] with just-injective eq
...     | refl = refl
worker-execution limit generation R.requestPruneCancellation f ig s eq | R.cancellationNext victims | victim ∷ rest with just-injective eq
... | refl = refl
worker-execution limit generation (R.pruneCancellationDelivered w) f ig s eq with R.pc f
... | R.transaction = case eq of λ ()
... | R.assertion = case eq of λ ()
... | R.counters = case eq of λ ()
... | R.returning = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.cancellationNext victims = case eq of λ ()
... | R.awaitDelivery victim rest with w ≟ P.thread victim
...   | no _ = case eq of λ ()
...   | yes _ with just-injective eq
...     | refl = refl
worker-execution limit generation R.checkAssertion f ig s eq with R.pc f
... | R.transaction = case eq of λ ()
... | R.counters = case eq of λ ()
... | R.returning = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.cancellationNext victims = case eq of λ ()
... | R.awaitDelivery victim rest = case eq of λ ()
... | R.assertion with R.deferredAssertion f
...   | true with just-injective eq
...     | refl = refl
worker-execution limit generation R.checkAssertion f ig s eq | R.assertion | false with just-injective eq
... | refl = refl
worker-execution limit generation R.readCounters f ig s eq with R.pc f
... | R.transaction = case eq of λ ()
... | R.assertion = case eq of λ ()
... | R.returning = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.cancellationNext victims = case eq of λ ()
... | R.awaitDelivery victim rest = case eq of λ ()
... | R.counters with mapCell (cm s)
...   | taken _ = case eq of λ ()
...   | full m with countIncoming (entries (cm s)) m
...     | nothing = case eq of λ ()
...     | just _ with just-injective eq
...       | refl = refl
worker-execution limit generation R.returnToIG f ig s eq with R.pc f
... | R.transaction = case eq of λ ()
... | R.assertion = case eq of λ ()
... | R.counters = case eq of λ ()
... | R.assertionRaised = case eq of λ ()
... | R.cancellationNext victims = case eq of λ ()
... | R.awaitDelivery victim rest = case eq of λ ()
... | R.returning with just-injective eq
...   | refl = refl
worker-execution limit generation R.enter f ig s eq = case eq of λ ()

remote-execution : ∀ limit generation a pending ig s {p} → R.step limit generation a pending ig s ≡ just p → IG.execution (R.governor p) ≡ IG.execution ig
remote-execution limit generation R.enter nothing ig s eq with IG.continuation ig
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
remote-execution limit generation R.enter nothing ig s eq | IG.needsCM t rest event old | newConnection info = case eq of λ ()
remote-execution limit generation R.enter nothing ig s eq | IG.needsCM t rest event old | muxFinished k = case eq of λ ()
remote-execution limit generation R.enter nothing ig s eq | IG.needsCM t rest event old | miniProtocolTerminated term = case eq of λ ()
remote-execution limit generation R.enter nothing ig s eq | IG.needsCM t rest event old | waitIdleRemote k with just-injective eq
... | refl = refl
remote-execution limit generation R.enter nothing ig s eq | IG.needsCM t rest event old | remotePromotedToHot k = case eq of λ ()
remote-execution limit generation R.enter nothing ig s eq | IG.needsCM t rest event old | remoteDemotedToWarm k = case eq of λ ()
remote-execution limit generation R.enter nothing ig s eq | IG.needsCM t rest event old | commitRemote k = case eq of λ ()
remote-execution limit generation R.enter nothing ig s eq | IG.needsCM t rest event old | awakeRemote k with just-injective eq
... | refl = refl
remote-execution limit generation R.enter nothing ig s eq | IG.needsCM t rest event old | maturedDuplexPeers peers fresh = case eq of λ ()
remote-execution limit generation R.enter nothing ig s eq | IG.needsCM t rest event old | inactivityTimeout = case eq of λ ()
remote-execution limit generation R.transact nothing ig s eq = case eq of λ ()
remote-execution limit generation (R.transactPruning ticket scores) nothing ig s eq = case eq of λ ()
remote-execution limit generation R.requestPruneCancellation nothing ig s eq = case eq of λ ()
remote-execution limit generation (R.pruneCancellationDelivered w) nothing ig s eq = case eq of λ ()
remote-execution limit generation R.checkAssertion nothing ig s eq = case eq of λ ()
remote-execution limit generation R.readCounters nothing ig s eq = case eq of λ ()
remote-execution limit generation R.returnToIG nothing ig s eq = case eq of λ ()
remote-execution limit generation R.enter (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution limit generation R.enter f ig s eq
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

remote-execution limit generation R.transact (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution limit generation R.transact f ig s eq
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

remote-execution limit generation (R.transactPruning ticket scores) (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution limit generation (R.transactPruning ticket scores) f ig s eq
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

remote-execution limit generation R.requestPruneCancellation (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution limit generation R.requestPruneCancellation f ig s eq
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

remote-execution limit generation (R.pruneCancellationDelivered w) (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution limit generation (R.pruneCancellationDelivered w) f ig s eq
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

remote-execution limit generation R.checkAssertion (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution limit generation R.checkAssertion f ig s eq
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

remote-execution limit generation R.readCounters (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution limit generation R.readCounters f ig s eq
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

remote-execution limit generation R.returnToIG (just f) ig s eq with IG.continuation ig
... | IG.sampleTime = case eq of λ ()
... | IG.exitFlush = case eq of λ ()
... | IG.exited = case eq of λ ()
... | IG.inCM = worker-execution limit generation R.returnToIG f ig s eq
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

-- Scored pruning commits all edits atomically before exposing an endpoint.
step-effects : ∀ a c {c′} → advance (remoteStep a) c ≡ just c′ →
  Retains (world c) (world c′) × Anchors (inboundGovernor c) (inboundGovernor c′)
step-effects a c eq with L.allowRemote a (handlerLifecycles c) (world c)
... | false = case eq of λ ()
... | true with R.step (promotionHardLimit c) (pruningGeneration c) a (remoteCall c) (inboundGovernor c) (world c) in stepped
...   | nothing = case eq of λ ()
...   | just p with P.applyEdits (R.edits p) (world c) in applied
...     | nothing = case eq of λ ()
...     | just s with just-injective eq
...       | refl = edits-retains (R.edits p) (world c) applied ,
  engine-anchors (remote-execution (promotionHardLimit c) (pruningGeneration c) a (remoteCall c) (inboundGovernor c) (world c) stepped)

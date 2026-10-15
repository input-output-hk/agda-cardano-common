{-# OPTIONS --guardedness #-}

-- Mux monitor, job and tracer actions retain every existing handler chain.
module ConnectionManagement.Properties.HandlerIGMux where

open import Class.DecEq.Instances using (DecEq-ℕ)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Data.Maybe.Properties using (just-injective)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences
open import ConnectionManagement.Properties.HandlerAnchors using (setMux-preserves)
open import ConnectionManagement.Properties.HandlerIGBoundary using (queue-chain)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as L

-- All runtime updates preserve the key, even when they change the queue.
finish : ∀ ig mid old new s {ig′ q captured} →
  lookup mid (IG.muxes (IG.execution ig)) ≡ just old → M.key new ≡ M.key old →
  IG.setMux mid new ig ≡ ig′ → Chain q captured s ig → Chain q captured s ig′
finish ig mid old new s found same refl chain =
  anchors-preserve-chain (setMux-preserves mid old new ig found same) chain

data CoveredMux : IG.IGAction → Set where
  sample : ∀ {mid} → CoveredMux (IG.sampleTracer mid)
  trace : ∀ {mid} → CoveredMux (IG.commitTracer mid)
  started : ∀ {mid} → CoveredMux (IG.finishStart mid)
  fork : ∀ {mid} → CoveredMux (IG.forkResponder mid)
  command : ∀ {mid} → CoveredMux (IG.monitorCommand mid)
  completion : ∀ {mid} → CoveredMux (IG.monitorCompletion mid)
  demand : ∀ {mid n} → CoveredMux (IG.startOnDemand mid n)
  jobFinished : ∀ {mid n outcome} → CoveredMux (IG.finishProtocol mid n outcome)
  jobResult : ∀ {mid n} → CoveredMux (IG.publishJobResult mid n)
  stopped : ∀ {mid} → CoveredMux (IG.finishStop mid)

worker-chain : ∀ a → CoveredMux a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
worker-chain .(IG.sampleTracer mid) (sample {mid}) ig queue s eq chain with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.callback m
...   | M.returned = case eq of λ ()
...   | M.readActive tr = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...   | M.commitTrace active tr = case eq of λ ()
...   | M.afterStart j = case eq of λ ()
...   | M.forkPending j = case eq of λ ()
...   | M.afterFailure = case eq of λ ()
...   | M.tracerFailed j = case eq of λ ()
worker-chain .(IG.commitTracer mid) (trace {mid}) ig queue s eq chain with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.callback m
...   | M.returned = case eq of λ ()
...   | M.readActive tr = case eq of λ ()
...   | M.afterStart j = case eq of λ ()
...   | M.forkPending j = case eq of λ ()
...   | M.afterFailure = case eq of λ ()
...   | M.tracerFailed j = case eq of λ ()
...   | M.commitTrace false tr = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...   | M.commitTrace true tr with IG.missingDescriptor tr (IG.tracerView (M.key m) ig) (M.traceCounters m)
...     | just n = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...     | nothing with M.traceSTM (M.key m) tr (IG.tracerView (M.key m) ig) (M.traceCounters m) queue
...       | nothing = case eq of λ ()
...       | just (rc , output) = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
worker-chain .(IG.finishStart mid) (started {mid}) ig queue s eq chain with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.callback m
...   | M.returned = case eq of λ ()
...   | M.readActive tr = case eq of λ ()
...   | M.commitTrace active tr = case eq of λ ()
...   | M.afterStart j = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...   | M.forkPending j = case eq of λ ()
...   | M.afterFailure = case eq of λ ()
...   | M.tracerFailed j = case eq of λ ()
worker-chain .(IG.forkResponder mid) (fork {mid}) ig queue s eq chain with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.callback m
...   | M.returned = case eq of λ ()
...   | M.readActive tr = case eq of λ ()
...   | M.commitTrace active tr = case eq of λ ()
...   | M.afterStart j = case eq of λ ()
...   | M.forkPending j = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...   | M.afterFailure = case eq of λ ()
...   | M.tracerFailed j = case eq of λ ()
worker-chain .(IG.monitorCommand mid) (command {mid}) ig queue s eq chain with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.callback m | M.status m | M.completions m | M.commands m
...   | M.readActive tr | _ | _ | _ = case eq of λ ()
...   | M.commitTrace active tr | _ | _ | _ = case eq of λ ()
...   | M.afterStart j | _ | _ | _ = case eq of λ ()
...   | M.forkPending j | _ | _ | _ = case eq of λ ()
...   | M.tracerFailed j | _ | _ | _ = case eq of λ ()
...   | M.afterFailure | _ | _ | _ = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...   | M.returned | M.stopping | _ | _ = case eq of λ ()
...   | M.returned | M.stopped | _ | _ = case eq of λ ()
...   | M.returned | M.failed err | _ | _ = case eq of λ ()
...   | M.returned | M.ready | _ ∷ _ | _ = case eq of λ ()
...   | M.returned | M.ready | [] | [] = case eq of λ ()
...   | M.returned | M.ready | [] | M.shutdown ∷ rest = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...   | M.returned | M.ready | [] | M.startCommand p ∷ rest with startMode p
...     | eagerly = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...     | onDemand = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...     | onDemandAny = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
worker-chain .(IG.monitorCompletion mid) (completion {mid}) ig queue s eq chain with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.callback m | M.status m | M.completions m
...   | M.readActive tr | _ | _ = case eq of λ ()
...   | M.commitTrace active tr | _ | _ = case eq of λ ()
...   | M.afterStart j | _ | _ = case eq of λ ()
...   | M.forkPending j | _ | _ = case eq of λ ()
...   | M.afterFailure | _ | _ = case eq of λ ()
...   | M.tracerFailed j | _ | _ = case eq of λ ()
...   | M.returned | M.stopping | _ = case eq of λ ()
...   | M.returned | M.stopped | _ = case eq of λ ()
...   | M.returned | M.failed err | _ = case eq of λ ()
...   | M.returned | M.ready | [] = case eq of λ ()
...   | M.returned | M.ready | (n , outcome) ∷ rest with outcome
...     | clean = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...     | errored err = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
worker-chain .(IG.startOnDemand mid n) (demand {mid} {n}) ig queue s eq chain with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.callback m | M.status m | M.commands m | M.completions m | lookup n (M.waiting m)
...   | M.readActive tr | _ | _ | _ | _ = case eq of λ ()
...   | M.commitTrace active tr | _ | _ | _ | _ = case eq of λ ()
...   | M.afterStart j | _ | _ | _ | _ = case eq of λ ()
...   | M.forkPending j | _ | _ | _ | _ = case eq of λ ()
...   | M.afterFailure | _ | _ | _ | _ = case eq of λ ()
...   | M.tracerFailed j | _ | _ | _ | _ = case eq of λ ()
...   | M.returned | M.stopping | _ | _ | _ = case eq of λ ()
...   | M.returned | M.stopped | _ | _ | _ = case eq of λ ()
...   | M.returned | M.failed err | _ | _ | _ = case eq of λ ()
...   | M.returned | M.ready | _ ∷ _ | _ | _ = case eq of λ ()
...   | M.returned | M.ready | [] | _ ∷ _ | _ = case eq of λ ()
...   | M.returned | M.ready | [] | [] | nothing = case eq of λ ()
...   | M.returned | M.ready | [] | [] | just eagerly = case eq of λ ()
...   | M.returned | M.ready | [] | [] | just onDemandAny = case eq of λ ()
...   | M.returned | M.ready | [] | [] | just onDemand = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
worker-chain .(IG.finishProtocol mid n outcome) (jobFinished {mid} {n} {outcome}) ig queue s eq chain with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with lookup n (M.protocols m) | IG.hasJob n (M.runningJobs m)
...   | nothing | _ = case eq of λ ()
...   | just M.idle | _ = case eq of λ ()
...   | just M.demand | _ = case eq of λ ()
...   | just M.demandAny | _ = case eq of λ ()
...   | just M.running | false = case eq of λ ()
...   | just M.running | true with outcome
...     | clean = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...     | errored err = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
worker-chain .(IG.publishJobResult mid n) (jobResult {mid} {n}) ig queue s eq chain with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with lookup n (M.finishedJobs m)
...   | nothing = case eq of λ ()
...   | just outcome = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
worker-chain .(IG.finishStop mid) (stopped {mid}) ig queue s eq chain with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.status m | M.callback m
...   | M.ready | _ = case eq of λ ()
...   | M.stopped | _ = case eq of λ ()
...   | M.failed err | _ = case eq of λ ()
...   | M.stopping | M.returned = finish ig mid m _ s found refl (cong proj₁ (just-injective eq)) chain
...   | M.stopping | M.readActive tr = case eq of λ ()
...   | M.stopping | M.commitTrace active tr = case eq of λ ()
...   | M.stopping | M.afterStart j = case eq of λ ()
...   | M.stopping | M.forkPending j = case eq of λ ()
...   | M.stopping | M.afterFailure = case eq of λ ()
...   | M.stopping | M.tracerFailed j = case eq of λ ()

mode-chain : ∀ mode a → CoveredMux a → ∀ ig queue s {ig′ queue′ q mid} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Chain q mid s ig → Chain q mid s ig′
mode-chain noResponderMode a covered ig queue s () chain
mode-chain responderMode a covered ig queue s eq chain = worker-chain a covered ig queue s eq chain

step-preserves : ∀ a → CoveredMux a → ∀ c {c′} → advance (igStep a) c ≡ just c′ →
  ∀ q → TrackedChain q c → TrackedChain q c′
step-preserves a covered c eq q (f , found , chain) with L.allowIG a (handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (responder c) a (inboundGovernor c) (inboundInfo (world c)) in stepped
...   | nothing = case eq of λ ()
...   | just (ig′ , queue′) with just-injective eq
...     | refl = f , found , queue-chain queue′
  (mode-chain (responder c) a covered (inboundGovernor c) (inboundInfo (world c)) (world c) stepped chain)

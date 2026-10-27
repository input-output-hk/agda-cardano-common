{-# OPTIONS --guardedness #-}

-- Mux monitor, job and tracer effects retain handle lookups and mux keys.
module ConnectionManagement.Properties.MuxRetention where

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
open import ConnectionManagement.Properties.HandlerAnchors using (Anchors; setMux-preserves)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.TracerReadiness as Readiness
import ConnectionManagement.Rules.HandlerLifecycle as L

-- Extract effects independently of any handler, promise or lifecycle frame.
finish : ∀ ig mid old new {ig′} →
  lookup mid (IG.muxes (IG.execution ig)) ≡ just old → M.key new ≡ M.key old →
  IG.setMux mid new ig ≡ ig′ → Anchors ig ig′
finish ig mid old new found same refl = setMux-preserves mid old new ig found same

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

worker-anchors : ∀ a → CoveredMux a → ∀ ig queue {ig′ queue′} →
  IG.stepWorker a ig queue ≡ just (ig′ , queue′) → Anchors ig ig′
worker-anchors .(IG.sampleTracer mid) (sample {mid}) ig queue eq with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.tracerAttachment m | M.callback m
...   | M.noIGTracer | M.readActive tr = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...   | M.igTracer | M.readActive tr = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...   | M.noIGTracer | M.returned = case eq of λ ()
...   | M.igTracer | M.returned = case eq of λ ()
...   | M.noIGTracer | M.commitTrace active tr = case eq of λ ()
...   | M.igTracer | M.commitTrace active tr = case eq of λ ()
...   | M.noIGTracer | M.afterStart j = case eq of λ ()
...   | M.igTracer | M.afterStart j = case eq of λ ()
...   | M.noIGTracer | M.forkPending j = case eq of λ ()
...   | M.igTracer | M.forkPending j = case eq of λ ()
...   | M.noIGTracer | M.afterFailure = case eq of λ ()
...   | M.igTracer | M.afterFailure = case eq of λ ()
...   | M.noIGTracer | M.tracerFailed j = case eq of λ ()
...   | M.igTracer | M.tracerFailed j = case eq of λ ()
worker-anchors .(IG.commitTracer mid) (trace {mid}) ig queue eq with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.tracerAttachment m | M.callback m
...   | M.noIGTracer | M.returned = case eq of λ ()
...   | M.igTracer | M.returned = case eq of λ ()
...   | M.noIGTracer | M.readActive tr = case eq of λ ()
...   | M.igTracer | M.readActive tr = case eq of λ ()
...   | M.noIGTracer | M.afterStart j = case eq of λ ()
...   | M.igTracer | M.afterStart j = case eq of λ ()
...   | M.noIGTracer | M.forkPending j = case eq of λ ()
...   | M.igTracer | M.forkPending j = case eq of λ ()
...   | M.noIGTracer | M.afterFailure = case eq of λ ()
...   | M.igTracer | M.afterFailure = case eq of λ ()
...   | M.noIGTracer | M.tracerFailed j = case eq of λ ()
...   | M.igTracer | M.tracerFailed j = case eq of λ ()
...   | M.noIGTracer | M.commitTrace active tr = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...   | M.igTracer | M.commitTrace false tr = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...   | M.igTracer | M.commitTrace true tr with Readiness.prefixReady (M.key m) tr (IG.tracerView (M.key m) ig) (M.traceCounters m) queue
...     | false = case eq of λ ()
...     | true with IG.missingDescriptor tr (IG.tracerView (M.key m) ig) (M.traceCounters m)
...       | just n = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...       | nothing with M.traceSTM (M.key m) tr (IG.tracerView (M.key m) ig) (M.traceCounters m) queue
...         | nothing = case eq of λ ()
...         | just (rc , output) = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
worker-anchors .(IG.finishStart mid) (started {mid}) ig queue eq with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.callback m
...   | M.returned = case eq of λ ()
...   | M.readActive tr = case eq of λ ()
...   | M.commitTrace active tr = case eq of λ ()
...   | M.afterStart j = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...   | M.forkPending j = case eq of λ ()
...   | M.afterFailure = case eq of λ ()
...   | M.tracerFailed j = case eq of λ ()
worker-anchors .(IG.forkResponder mid) (fork {mid}) ig queue eq with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.callback m
...   | M.returned = case eq of λ ()
...   | M.readActive tr = case eq of λ ()
...   | M.commitTrace active tr = case eq of λ ()
...   | M.afterStart j = case eq of λ ()
...   | M.forkPending j = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...   | M.afterFailure = case eq of λ ()
...   | M.tracerFailed j = case eq of λ ()
worker-anchors .(IG.monitorCommand mid) (command {mid}) ig queue eq with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.callback m | M.status m | M.completions m | M.commands m
...   | M.readActive tr | _ | _ | _ = case eq of λ ()
...   | M.commitTrace active tr | _ | _ | _ = case eq of λ ()
...   | M.afterStart j | _ | _ | _ = case eq of λ ()
...   | M.forkPending j | _ | _ | _ = case eq of λ ()
...   | M.tracerFailed j | _ | _ | _ = case eq of λ ()
...   | M.afterFailure | _ | _ | _ = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...   | M.returned | M.stopping | _ | _ = case eq of λ ()
...   | M.returned | M.stopped | _ | _ = case eq of λ ()
...   | M.returned | M.failed err | _ | _ = case eq of λ ()
...   | M.returned | M.ready | _ ∷ _ | _ = case eq of λ ()
...   | M.returned | M.ready | [] | [] = case eq of λ ()
...   | M.returned | M.ready | [] | M.shutdown ∷ rest = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...   | M.returned | M.ready | [] | M.startCommand p ∷ rest with startMode p
...     | eagerly = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...     | onDemand = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...     | onDemandAny = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
worker-anchors .(IG.monitorCompletion mid) (completion {mid}) ig queue eq with lookup mid (IG.muxes (IG.execution ig)) in found
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
...   | M.returned | M.ready | M.jobResult M.responderJob n outcome ∷ rest with outcome
...     | clean = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...     | errored err = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
worker-anchors .(IG.monitorCompletion mid) (completion {mid}) ig queue eq | just m | M.returned | M.ready | M.jobResult M.initiatorJob n outcome ∷ rest with outcome
... | clean = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
... | errored err = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
worker-anchors .(IG.startOnDemand mid n) (demand {mid} {n}) ig queue eq with lookup mid (IG.muxes (IG.execution ig)) in found
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
...   | M.returned | M.ready | [] | [] | just onDemand = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
worker-anchors .(IG.finishProtocol mid n outcome) (jobFinished {mid} {n} {outcome}) ig queue eq with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with lookup n (M.protocols m) | IG.hasJob n (M.runningJobs m)
...   | nothing | _ = case eq of λ ()
...   | just M.idle | _ = case eq of λ ()
...   | just M.demand | _ = case eq of λ ()
...   | just M.demandAny | _ = case eq of λ ()
...   | just M.running | false = case eq of λ ()
...   | just M.running | true with outcome
...     | clean = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...     | errored err = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
worker-anchors .(IG.publishJobResult mid n) (jobResult {mid} {n}) ig queue eq with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with lookup n (M.finishedJobs m)
...   | nothing = case eq of λ ()
...   | just outcome = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
worker-anchors .(IG.finishStop mid) (stopped {mid}) ig queue eq with lookup mid (IG.muxes (IG.execution ig)) in found
... | nothing = case eq of λ ()
... | just m with M.status m | M.callback m
...   | M.ready | _ = case eq of λ ()
...   | M.stopped | _ = case eq of λ ()
...   | M.failed err | _ = case eq of λ ()
...   | M.stopping | M.returned = finish ig mid m _ found refl (cong proj₁ (just-injective eq))
...   | M.stopping | M.readActive tr = case eq of λ ()
...   | M.stopping | M.commitTrace active tr = case eq of λ ()
...   | M.stopping | M.afterStart j = case eq of λ ()
...   | M.stopping | M.forkPending j = case eq of λ ()
...   | M.stopping | M.afterFailure = case eq of λ ()
...   | M.stopping | M.tracerFailed j = case eq of λ ()

mode-anchors : ∀ mode a → CoveredMux a → ∀ ig queue {ig′ queue′} →
  IG.step mode a ig queue ≡ just (ig′ , queue′) → Anchors ig ig′
mode-anchors noResponderMode .(IG.monitorCommand mid) (command {mid}) ig queue eq with IG.runtimeAllowed (IG.monitorCommand mid) ig
... | false = case eq of λ ()
... | true = worker-anchors (IG.monitorCommand mid) command ig queue eq
mode-anchors noResponderMode .(IG.monitorCompletion mid) (completion {mid}) ig queue eq with IG.runtimeAllowed (IG.monitorCompletion mid) ig
... | false = case eq of λ ()
... | true = worker-anchors (IG.monitorCompletion mid) completion ig queue eq
mode-anchors noResponderMode .(IG.sampleTracer mid) (sample {mid}) ig queue eq = worker-anchors (IG.sampleTracer mid) sample ig queue eq
mode-anchors noResponderMode .(IG.commitTracer mid) (trace {mid}) ig queue eq = worker-anchors (IG.commitTracer mid) trace ig queue eq
mode-anchors noResponderMode .(IG.finishStop mid) (stopped {mid}) ig queue eq = worker-anchors (IG.finishStop mid) stopped ig queue eq
mode-anchors noResponderMode .(IG.finishStart mid) (started {mid}) ig queue ()
mode-anchors noResponderMode .(IG.forkResponder mid) (fork {mid}) ig queue ()
mode-anchors noResponderMode .(IG.startOnDemand mid n) (demand {mid} {n}) ig queue ()
mode-anchors noResponderMode .(IG.finishProtocol mid n result) (jobFinished {mid} {n} {result}) ig queue ()
mode-anchors noResponderMode .(IG.publishJobResult mid n) (jobResult {mid} {n}) ig queue ()
mode-anchors responderMode a covered ig queue eq = worker-anchors a covered ig queue eq

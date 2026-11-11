{-# OPTIONS --guardedness #-}

-- Completion/registry flags retain execution and use stable physical pool writes.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesFlagSteps
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (JobId)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.OutboundKeys using (Unique)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesJobFlags as Flags
import ConnectionManagement.Properties.OwnedFramesJobNames as Names
import ConnectionManagement.Properties.OwnedFramesPoolTransport as PoolFacts
import ConnectionManagement.Properties.OwnedFramesObservation as Observation
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesLifts as Lifts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module F = Flags isBearerClosed isIOManagerError
  module N = Names isBearerClosed isIOManagerError
  module P = PoolFacts isBearerClosed isIOManagerError
  module V = Observation isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError
  module L = Lifts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- Exactly the two normal job-flag families are selected here.
flag-action : Sub.Action → Bool
flag-action (Sub.enqueueCompletion _ _) = true
flag-action (Sub.deregisterJob _) = true
flag-action _ = false

-- The actual source transition changes just one job's bookkeeping flags.
record Effect (c d : Sub.Configuration) : Set where
  field
    key : JobId
    old next : Sub.JobFrame
    saved : lookup key (Sub.jobs c) ≡ just old
    execution : Sub.execution next ≡ Sub.execution old
    rows : Sub.jobs d ≡ put key next (Sub.jobs c)
    source : J.cm (Sub.world d) ≡ J.cm (Sub.world c)
    follows : Sub.monitors d ≡ Sub.monitors c

-- Mirror the completion and registry writers, including all actual guards.
flag-effect : ∀ a c {d} → flag-action a ≡ true → Sub.advance a c ≡ just d → Effect c d
flag-effect (Sub.enqueueCompletion j delay) c permit eq with lookup j (Sub.jobs c) in saved
... | nothing = case eq of λ ()
... | just old with Sub.queued old | J.pc (Sub.execution old)
...   | false | J.complete result with Sub.validCompletionDelay (J.work (Sub.execution old)) result delay
...     | false = case eq of λ ()
...     | true = case just-injective eq of λ { refl → record
  { key = j; old = old; next = record old { queued = true }; saved = saved
  ; execution = refl; rows = refl; source = refl; follows = refl } }
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | true | pc = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | J.begin = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | J.awaitAcquire = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | (J.startBundle t ns) = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | (J.publishBundle t) = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | J.markWarm = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | J.forkMonitor = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | J.finishActivation = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | J.awaitHot = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | J.awaitAll = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | J.callRelease = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | J.awaitRelease = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | J.delayFailure = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | (J.awaitCold result) = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | (J.acquirePolicy fault) = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | (J.nodeDelivery fault) = case eq of λ ()
flag-effect (Sub.enqueueCompletion j delay) c permit eq | just old | false | (J.nodeRethrow fault) = case eq of λ ()
flag-effect (Sub.deregisterJob j) c permit eq with lookup j (Sub.jobs c) in saved
... | nothing = case eq of λ ()
... | just old with Sub.queued old | Sub.deregistered old | any (λ x → does (x ≟ j)) (Sub.pool c)
...   | true | false | true = case just-injective eq of λ { refl → record
  { key = j; old = old; next = record old { deregistered = true }; saved = saved
  ; execution = refl; rows = refl; source = refl; follows = refl } }
...   | true | true | true = case eq of λ ()
...   | true | true | false = case eq of λ ()
...   | true | false | false = case eq of λ ()
...   | false | true | true = case eq of λ ()
...   | false | true | false = case eq of λ ()
...   | false | false | true = case eq of λ ()
...   | false | false | false = case eq of λ ()
flag-effect (Sub.core action) c () eq
flag-effect Sub.publishPublicState c () eq
flag-effect (Sub.sampleTime t) c () eq
flag-effect (Sub.applyAt t) c () eq
flag-effect (Sub.setTargets t) c () eq
flag-effect (Sub.selectMonitor delay) c () eq
flag-effect Sub.selectCompletion c () eq
flag-effect Sub.selectTargets c () eq
flag-effect Sub.selectWakeup c () eq
flag-effect Sub.registerWakeup c () eq
flag-effect Sub.expireWakeup c () eq
flag-effect Sub.cancelWakeup c () eq
flag-effect Sub.publishCounters c () eq
flag-effect Sub.traceSelection c () eq
flag-effect (Sub.selectPolicy picked) c () eq
flag-effect (Sub.forkJob caller child sock) c () eq
flag-effect Sub.registerJob c () eq
flag-effect Sub.finishLaunch c () eq
flag-effect (Sub.jobStep j action) c () eq
flag-effect (Sub.protocolResult ref n result) c () eq
flag-effect (Sub.publishInitiatorResult ref i) c () eq
flag-effect (Sub.pollPeer ref caller) c () eq
flag-effect (Sub.monitorStep ref action) c () eq
flag-effect (Sub.monitorFinished ref) c () eq
flag-effect (Sub.observeInitiatorFailure ref) c () eq

-- Normal publication/removal use the exact non-running kernel transitions.
normal-stable : ∀ a s {p} → flag-action a ≡ true → GP.normalPool a s ≡ just p → P.G.Stable (GP.pool s) p
normal-stable (Sub.enqueueCompletion j delay) s permit eq with lookup j (GP.Pool.handles (GP.pool s))
... | just (GP.Pool.bodyReturned captured) with GP.returnedBody j (GP.machine s) captured
...   | true = P.G.step-stable (GP.Pool.publishCompletion j) (GP.pool s) refl eq
...   | false = case eq of λ ()
normal-stable (Sub.enqueueCompletion j delay) s permit eq | nothing = case eq of λ ()
normal-stable (Sub.enqueueCompletion j delay) s permit eq | just GP.Pool.bodyRunning = case eq of λ ()
normal-stable (Sub.enqueueCompletion j delay) s permit eq | just GP.Pool.bodyUnwinding = case eq of λ ()
normal-stable (Sub.enqueueCompletion j delay) s permit eq | just (GP.Pool.deregisterPending exit) = case eq of λ ()
normal-stable (Sub.enqueueCompletion j delay) s permit eq | just (GP.Pool.deregistered exit) = case eq of λ ()
normal-stable (Sub.enqueueCompletion j delay) s permit eq | just (GP.Pool.resultAvailable exit) = case eq of λ ()
normal-stable (Sub.deregisterJob j) s permit eq = P.G.step-stable (GP.Pool.deregister j) (GP.pool s) refl eq
normal-stable (Sub.core action) s () eq
normal-stable Sub.publishPublicState s () eq
normal-stable (Sub.sampleTime t) s () eq
normal-stable (Sub.applyAt t) s () eq
normal-stable (Sub.setTargets t) s () eq
normal-stable (Sub.selectMonitor delay) s () eq
normal-stable Sub.selectCompletion s () eq
normal-stable Sub.selectTargets s () eq
normal-stable Sub.selectWakeup s () eq
normal-stable Sub.registerWakeup s () eq
normal-stable Sub.expireWakeup s () eq
normal-stable Sub.cancelWakeup s () eq
normal-stable Sub.publishCounters s () eq
normal-stable Sub.traceSelection s () eq
normal-stable (Sub.selectPolicy picked) s () eq
normal-stable (Sub.forkJob caller child sock) s () eq
normal-stable Sub.registerJob s () eq
normal-stable Sub.finishLaunch s () eq
normal-stable (Sub.jobStep j action) s () eq
normal-stable (Sub.protocolResult ref n result) s () eq
normal-stable (Sub.publishInitiatorResult ref i) s () eq
normal-stable (Sub.pollPeer ref caller) s () eq
normal-stable (Sub.monitorStep ref action) s () eq
normal-stable (Sub.monitorFinished ref) s () eq
normal-stable (Sub.observeInitiatorFailure ref) s () eq

-- These actions never produce another job body return through noteReturn.
note-result : ∀ a c p {p′} → flag-action a ≡ true → GP.noteReturn a c p ≡ just p′ → p′ ≡ p
note-result (Sub.enqueueCompletion j delay) c p permit eq = sym (just-injective eq)
note-result (Sub.deregisterJob j) c p permit eq = sym (just-injective eq)
note-result (Sub.core action) c p () eq
note-result Sub.publishPublicState c p () eq
note-result (Sub.sampleTime t) c p () eq
note-result (Sub.applyAt t) c p () eq
note-result (Sub.setTargets t) c p () eq
note-result (Sub.selectMonitor delay) c p () eq
note-result Sub.selectCompletion c p () eq
note-result Sub.selectTargets c p () eq
note-result Sub.selectWakeup c p () eq
note-result Sub.registerWakeup c p () eq
note-result Sub.expireWakeup c p () eq
note-result Sub.cancelWakeup c p () eq
note-result Sub.publishCounters c p () eq
note-result Sub.traceSelection c p () eq
note-result (Sub.selectPolicy picked) c p () eq
note-result (Sub.forkJob caller child sock) c p () eq
note-result Sub.registerJob c p () eq
note-result Sub.finishLaunch c p () eq
note-result (Sub.jobStep j action) c p () eq
note-result (Sub.protocolResult ref n result) c p () eq
note-result (Sub.publishInitiatorResult ref i) c p () eq
note-result (Sub.pollPeer ref caller) c p () eq
note-result (Sub.monitorStep ref action) c p () eq
note-result (Sub.monitorFinished ref) c p () eq
note-result (Sub.observeInitiatorFailure ref) c p () eq

-- Source projection, execution equality and stable pool transport compose.
governor-flags : ∀ a s {g′} → flag-action a ≡ true → GP.step (GP.run a) (PS.governor s) ≡ just g′ → D.Held s → D.Held (record s { governor = g′ })
governor-flags a s permit eq (inv , unique , aux) with GP.normalPool a (PS.governor s) in pooled |
  GP.Production.step (Policy.dispatch a) (GP.source (PS.governor s)) in dispatched
... | just p′ | just source′ with GP.noteReturn a (Policy.machine source′) p′ in noted
...   | nothing = case eq of λ ()
...   | just p″ with GP.Production.step-projects (Policy.dispatch a) (GP.source (PS.governor s)) dispatched
...     | Sub.next advanced Sub.done = case just-injective eq of λ { refl →
  subst (λ cm → Inv cm (C.capture target)) (sym (Effect.source effect)) (proj₁ carried) ,
  subst Unique (sym (Effect.source effect)) unique , proj₂ carried }
  where
  effect = flag-effect a (PS.machine s) permit advanced
  j = Effect.key effect
  old = Effect.old effect
  next = Effect.next effect
  job-context = N.job-context (C.capture s) (put j next (Sub.jobs (PS.machine s)))
  after-context = P.gov-context job-context p″
  stable = subst (P.G.Stable (GP.pool (PS.governor s))) (sym (note-result a (Policy.machine source′) p′ permit noted)) (normal-stable a (PS.governor s) permit pooled)
  job-inv = F.flags-inv (PS.cm s) (C.capture s) j old next (Effect.saved effect) (Effect.execution effect) inv
  job-aux = F.caller-aux (C.capture s) j old next (Effect.saved effect) (cong J.caller (Effect.execution effect)) aux
  target = record s { governor = GP.supervised source′ p″ (GP.noteRegions a (J.cm (Sub.world (Policy.machine source′))) (GP.regions (PS.governor s))) (GP.unwinding (PS.governor s)) }
  same = V.observed-equal after-context (C.capture target) (Effect.rows effect) (Effect.follows effect) refl refl refl refl
  carried = V.observed-preserves (PS.cm s) after-context (C.capture target) same
    (P.gov-inv (PS.cm s) job-context p″ stable job-inv) (P.gov-aux job-context p″ stable job-aux)
governor-flags a s permit eq held | nothing | source = case eq of λ ()
governor-flags a s permit eq held | just pool | nothing = case eq of λ ()

-- PSA preserves the exact selected normal writer and all original guards.
ps-flags : ∀ a s {t} → flag-action a ≡ true → PS.step (PS.run (GP.run a)) s ≡ just t → D.Held s → D.Held t
ps-flags (Sub.enqueueCompletion j delay) s permit = L.governor-lift (GP.run (Sub.enqueueCompletion j delay)) s (governor-flags (Sub.enqueueCompletion j delay) s refl) (λ after → refl)
ps-flags (Sub.deregisterJob j) s permit = L.governor-lift (GP.run (Sub.deregisterJob j)) s (governor-flags (Sub.deregisterJob j) s refl) (λ after → refl)
ps-flags (Sub.core action) s () eq held
ps-flags Sub.publishPublicState s () eq held
ps-flags (Sub.sampleTime t) s () eq held
ps-flags (Sub.applyAt t) s () eq held
ps-flags (Sub.setTargets t) s () eq held
ps-flags (Sub.selectMonitor delay) s () eq held
ps-flags Sub.selectCompletion s () eq held
ps-flags Sub.selectTargets s () eq held
ps-flags Sub.selectWakeup s () eq held
ps-flags Sub.registerWakeup s () eq held
ps-flags Sub.expireWakeup s () eq held
ps-flags Sub.cancelWakeup s () eq held
ps-flags Sub.publishCounters s () eq held
ps-flags Sub.traceSelection s () eq held
ps-flags (Sub.selectPolicy picked) s () eq held
ps-flags (Sub.forkJob caller child sock) s () eq held
ps-flags Sub.registerJob s () eq held
ps-flags Sub.finishLaunch s () eq held
ps-flags (Sub.jobStep j action) s () eq held
ps-flags (Sub.protocolResult ref n result) s () eq held
ps-flags (Sub.publishInitiatorResult ref i) s () eq held
ps-flags (Sub.pollPeer ref caller) s () eq held
ps-flags (Sub.monitorStep ref action) s () eq held
ps-flags (Sub.monitorFinished ref) s () eq held
ps-flags (Sub.observeInitiatorFailure ref) s () eq held

-- These are the actual K completion/registry labels.
k-flags : ∀ a s {t} → flag-action a ≡ true → K.step (K.peerStep (PS.run (GP.run a))) s ≡ just t → R.Reach s → R.Reach t
k-flags a s permit = L.peer-lift (PS.run (GP.run a)) (λ p → ps-flags a p permit) s

-- Cancelled deregistration writes the same execution-preserving job flag.
governor-cancelled : ∀ j s {g′} → GP.step (GP.deregisterCancelled j) (PS.governor s) ≡ just g′ → D.Held s → D.Held (record s { governor = g′ })
governor-cancelled j s eq (inv , unique , aux) with lookup j (Sub.jobs (PS.machine s)) in saved |
  GP.Pool.step (GP.Pool.deregister j) (GP.pool (PS.governor s)) in deregistered
... | just old | just p′ with P.G.step-stable (GP.Pool.deregister j) (GP.pool (PS.governor s)) refl deregistered | lookup j (GP.Pool.handles (GP.pool (PS.governor s)))
...   | stable | just (GP.Pool.deregisterPending GP.Pool.cancelledExit) = case just-injective eq of λ { refl → proj₁ carried , unique , proj₂ carried }
  where
  next = record old { deregistered = true }
  job-context = N.job-context (C.capture s) (put j next (Sub.jobs (PS.machine s)))
  after-context = P.gov-context job-context p′
  target = record s { governor = record (PS.governor s) { pool = p′; source = record (GP.source (PS.governor s))
    { machine = record (PS.machine s) { jobs = put j next (Sub.jobs (PS.machine s)); pool = GP.Pool.remove j (Sub.pool (PS.machine s)) } } } }
  same = V.observed-equal after-context (C.capture target) refl refl refl refl refl refl
  carried = V.observed-preserves (PS.cm s) after-context (C.capture target) same
    (P.gov-inv (PS.cm s) job-context p′ stable (F.flags-inv (PS.cm s) (C.capture s) j old next saved refl inv))
    (P.gov-aux job-context p′ stable (F.caller-aux (C.capture s) j old next saved refl aux))
governor-cancelled j s eq held | just old | just p′ | stable | nothing = case eq of λ ()
governor-cancelled j s eq held | just old | just p′ | stable | just GP.Pool.bodyRunning = case eq of λ ()
governor-cancelled j s eq held | just old | just p′ | stable | just GP.Pool.bodyUnwinding = case eq of λ ()
governor-cancelled j s eq held | just old | just p′ | stable | just (GP.Pool.bodyReturned captured) = case eq of λ ()
governor-cancelled j s eq held | just old | just p′ | stable | just (GP.Pool.deregisterPending GP.Pool.normalExit) = case eq of λ ()
governor-cancelled j s eq held | just old | just p′ | stable | just (GP.Pool.deregistered exit) = case eq of λ ()
governor-cancelled j s eq held | just old | just p′ | stable | just (GP.Pool.resultAvailable exit) = case eq of λ ()
governor-cancelled j s eq held | nothing | pool = case eq of λ ()
governor-cancelled j s eq held | just old | nothing = case eq of λ ()

-- The cancelled path retains the same real PSA/shared dispatch checks.
k-cancelled : ∀ j s {t} → K.step (K.peerStep (PS.run (GP.deregisterCancelled j))) s ≡ just t → R.Reach s → R.Reach t
k-cancelled j = L.peer-lift (PS.run (GP.deregisterCancelled j)) (λ s → L.governor-lift (GP.deregisterCancelled j) s (governor-cancelled j s) (λ after → refl))

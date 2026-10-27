{-# OPTIONS --guardedness #-}

-- Actual queued-pool startup histories, without treating ready/registered as
-- termination. Publication/buffer/bearer boundaries remain explicit inputs.
module ConnectionManagement.Properties.MuxStartup (Result : Set) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (Present; lookup-put; put-preserves-present)
import ConnectionManagement.Rules.MuxStartup as Startup
module S = Startup Result
module Pool = S.Pool

-- Historical handles remain meaningful after child deregistration. A startup
-- certificate therefore makes no claim that both actors remain registered.
Pair : JobId → JobId → Pool.State → Set
Pair muxer demuxer p = Present muxer (Pool.handles p) × Present demuxer (Pool.handles p) × muxer ≢ demuxer
PhaseValid : S.PC → Pool.State → Set
PhaseValid (S.muxerForked muxer) p = Present muxer (Pool.handles p)
PhaseValid (S.muxerRegistered muxer) p = Present muxer (Pool.handles p)
PhaseValid (S.demuxerForked muxer demuxer) p = Pair muxer demuxer p
PhaseValid (S.demuxerRegistered muxer demuxer) p = Pair muxer demuxer p
PhaseValid (S.matureTraced muxer demuxer) p = Pair muxer demuxer p
PhaseValid (S.monitoring muxer demuxer) p = Pair muxer demuxer p
PhaseValid _ p = ⊤
Valid : S.State → Set
Valid s = PhaseValid (S.phase s) (S.pool s)
Retains : Pool.State → Pool.State → Set
Retains p q = ∀ j → Present j (Pool.handles p) → Present j (Pool.handles q)

phase-retained : ∀ phase p q → Retains p q → PhaseValid phase p → PhaseValid phase q
phase-retained (S.muxerForked m) p q keeps valid = keeps m valid
phase-retained (S.muxerRegistered m) p q keeps valid = keeps m valid
phase-retained (S.demuxerForked m d) p q keeps (mp , dp , apart) = keeps m mp , keeps d dp , apart
phase-retained (S.demuxerRegistered m d) p q keeps (mp , dp , apart) = keeps m mp , keeps d dp , apart
phase-retained (S.matureTraced m d) p q keeps (mp , dp , apart) = keeps m mp , keeps d dp , apart
phase-retained (S.monitoring m d) p q keeps (mp , dp , apart) = keeps m mp , keeps d dp , apart
phase-retained S.awaitPublication p q keeps valid = tt
phase-retained S.published p q keeps valid = tt
phase-retained S.bufferReady p q keeps valid = tt
phase-retained S.bearerReady p q keeps valid = tt
phase-retained S.runEntered p q keeps valid = tt
phase-retained S.startingTraced p q keeps valid = tt
phase-retained S.egressReady p q keeps valid = tt
phase-retained S.poolReady p q keeps valid = tt

record ForkEvidence (j : JobId) (p q : Pool.State) : Set where
  constructor forkEvidence
  field fresh : lookup j (Pool.handles p) ≡ nothing
        present : Present j (Pool.handles q)
        retained : Retains p q
open ForkEvidence public

fork-evidence : ∀ j p {q} → Pool.step (Pool.fork j) p ≡ just q → ForkEvidence j p q
fork-evidence j p eq with Pool.phase p | Pool.parentFork p | lookup j (Pool.handles p) in found
... | Pool.openPool | nothing | nothing = case just-injective eq of λ { refl →
  forkEvidence found (Pool.bodyRunning , lookup-put j Pool.bodyRunning (Pool.handles p))
    (λ k → put-preserves-present j k Pool.bodyRunning (Pool.handles p)) }
fork-evidence j p eq | Pool.closing | parent | existing = case eq of λ ()
fork-evidence j p eq | Pool.closedPool | parent | existing = case eq of λ ()
fork-evidence j p eq | (Pool.cancelPending k) | parent | existing = case eq of λ ()
fork-evidence j p eq | (Pool.joinPending k) | parent | existing = case eq of λ ()
fork-evidence j p eq | Pool.openPool | just parent | existing = case eq of λ ()
fork-evidence j p eq | Pool.openPool | nothing | just existing = case eq of λ ()

register-retains : ∀ p {q} → Pool.step Pool.register p ≡ just q → Retains p q
register-retains p eq with Pool.phase p | Pool.parentFork p
... | Pool.openPool | just j with Pool.member j (Pool.registered p)
...   | false = case just-injective eq of λ { refl → λ k present → present }
...   | true = case eq of λ ()
register-retains p eq | Pool.closing | parent = case eq of λ ()
register-retains p eq | Pool.closedPool | parent = case eq of λ ()
register-retains p eq | (Pool.cancelPending k) | parent = case eq of λ ()
register-retains p eq | (Pool.joinPending k) | parent = case eq of λ ()
register-retains p eq | Pool.openPool | nothing = case eq of λ ()

-- Fresh physical identifiers are distinct even when the first child has
-- returned, queued a result, deregistered, or exposed its Async result already.
fresh-distinct : ∀ muxer demuxer p → Present muxer (Pool.handles p) →
  lookup demuxer (Pool.handles p) ≡ nothing → muxer ≢ demuxer
fresh-distinct muxer demuxer p (old , present) fresh refl with trans (sym fresh) present
... | ()

child-retains : ∀ action p {q} → Pool.step (S.poolAction action) p ≡ just q → Retains p q
child-retains (S.bodyReturned j result) p eq with lookup j (Pool.handles p)
... | nothing = case eq of λ ()
child-retains (S.bodyReturned j result) p eq | just Pool.bodyRunning = case just-injective eq of λ { refl → λ k → put-preserves-present j k (Pool.bodyReturned result) (Pool.handles p) }
child-retains (S.bodyReturned j result) p eq | just (Pool.bodyReturned oldResult) = case eq of λ ()
child-retains (S.bodyReturned j result) p eq | just Pool.bodyUnwinding = case eq of λ ()
child-retains (S.bodyReturned j result) p eq | just (Pool.deregisterPending exit) = case eq of λ ()
child-retains (S.bodyReturned j result) p eq | just (Pool.deregistered exit) = case eq of λ ()
child-retains (S.bodyReturned j result) p eq | just (Pool.resultAvailable exit) = case eq of λ ()
child-retains (S.publishCompletion j) p eq with lookup j (Pool.handles p)
... | nothing = case eq of λ ()
child-retains (S.publishCompletion j) p eq | just Pool.bodyRunning = case eq of λ ()
child-retains (S.publishCompletion j) p eq | just (Pool.bodyReturned oldResult) = case just-injective eq of λ { refl → λ k → put-preserves-present j k (Pool.deregisterPending Pool.normalExit) (Pool.handles p) }
child-retains (S.publishCompletion j) p eq | just Pool.bodyUnwinding = case eq of λ ()
child-retains (S.publishCompletion j) p eq | just (Pool.deregisterPending exit) = case eq of λ ()
child-retains (S.publishCompletion j) p eq | just (Pool.deregistered exit) = case eq of λ ()
child-retains (S.publishCompletion j) p eq | just (Pool.resultAvailable exit) = case eq of λ ()
child-retains (S.publishAsyncResult j) p eq with lookup j (Pool.handles p)
... | nothing = case eq of λ ()
child-retains (S.publishAsyncResult j) p eq | just Pool.bodyRunning = case eq of λ ()
child-retains (S.publishAsyncResult j) p eq | just (Pool.bodyReturned oldResult) = case eq of λ ()
child-retains (S.publishAsyncResult j) p eq | just Pool.bodyUnwinding = case eq of λ ()
child-retains (S.publishAsyncResult j) p eq | just (Pool.deregisterPending exit) = case eq of λ ()
child-retains (S.publishAsyncResult j) p eq | just (Pool.deregistered exit) = case just-injective eq of λ { refl → λ k → put-preserves-present j k (Pool.resultAvailable exit) (Pool.handles p) }
child-retains (S.publishAsyncResult j) p eq | just (Pool.resultAvailable exit) = case eq of λ ()
child-retains (S.deregister j) p eq with lookup j (Pool.handles p) | Pool.member j (Pool.registered p)
... | just (Pool.deregisterPending exit) | true = case just-injective eq of λ { refl →
  λ k → put-preserves-present j k (Pool.deregistered exit) (Pool.handles p) }
child-retains (S.deregister j) p eq | just Pool.bodyRunning | member = case eq of λ ()
child-retains (S.deregister j) p eq | just (Pool.bodyReturned oldResult) | member = case eq of λ ()
child-retains (S.deregister j) p eq | just Pool.bodyUnwinding | member = case eq of λ ()
child-retains (S.deregister j) p eq | just (Pool.deregistered exit) | member = case eq of λ ()
child-retains (S.deregister j) p eq | just (Pool.resultAvailable exit) | member = case eq of λ ()
child-retains (S.deregister j) p eq | nothing | member = case eq of λ ()
child-retains (S.deregister j) p eq | just (Pool.deregisterPending exit) | false = case eq of λ ()

PoolTrace : Pool.State → Pool.State → Set
PoolTrace p q = Σ (List Pool.Action) (λ as → Pool.Executes p as q)
record Evidence (before after : S.State) : Set where
  constructor evidence
  field projection : PoolTrace (S.pool before) (S.pool after)
        preservation : Valid before → Valid after
open Evidence public

via-evidence : ∀ phase action s {s′} →
  (∀ q → Pool.step action (S.pool s) ≡ just q → Valid s → PhaseValid phase q) →
  S.via phase action s ≡ just s′ → Evidence s s′
via-evidence phase action s preserves eq with Pool.step action (S.pool s) in advanced
... | nothing = case eq of λ ()
... | just q = case just-injective eq of λ { refl →
  evidence (action ∷ [] , Pool.next advanced Pool.done) (preserves q refl) }

step-evidence : ∀ action s {s′} → S.step action s ≡ just s′ → Evidence s s′
step-evidence S.observePublication (S.startupState S.awaitPublication p) eq = case just-injective eq of λ { refl → evidence ([] , Pool.done) (λ valid → tt) }
step-evidence S.observePublication (S.startupState S.published p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence S.observePublication (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState S.published p) eq = case just-injective eq of λ { refl → evidence ([] , Pool.done) (λ valid → tt) }
step-evidence S.allocateBuffer (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence S.allocateBuffer (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState S.published p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState S.bufferReady p) eq = case just-injective eq of λ { refl → evidence ([] , Pool.done) (λ valid → tt) }
step-evidence S.createBearer (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence S.createBearer (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState S.published p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState S.bearerReady p) eq = case just-injective eq of λ { refl → evidence ([] , Pool.done) (λ valid → tt) }
step-evidence S.enterRun (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence S.enterRun (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState S.published p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState S.runEntered p) eq = case just-injective eq of λ { refl → evidence ([] , Pool.done) (λ valid → tt) }
step-evidence S.traceStarting (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence S.traceStarting (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState S.published p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState S.startingTraced p) eq = case just-injective eq of λ { refl → evidence ([] , Pool.done) (λ valid → tt) }
step-evidence S.allocateEgress (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence S.allocateEgress (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState S.published p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState S.egressReady p) eq = case just-injective eq of λ { refl → evidence ([] , Pool.done) (λ valid → tt) }
step-evidence S.openPool (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence S.openPool (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState S.published p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState (S.demuxerRegistered m d) p) eq = case just-injective eq of λ { refl → evidence ([] , Pool.done) (λ valid → valid) }
step-evidence S.traceMature (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence S.traceMature (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState S.published p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence S.enterMonitor (S.startupState (S.matureTraced m d) p) eq = case just-injective eq of λ { refl → evidence ([] , Pool.done) (λ valid → valid) }
step-evidence S.enterMonitor (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState S.published p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState S.poolReady p) eq = via-evidence (S.muxerForked j) (Pool.fork j) (S.startupState S.poolReady p) (λ q advanced valid → present (fork-evidence j p advanced)) eq
step-evidence (S.forkMuxer j) (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence (S.forkMuxer j) (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState S.published p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState (S.muxerForked m) p) eq = via-evidence (S.muxerRegistered m) (Pool.register) (S.startupState (S.muxerForked m) p) (λ q advanced valid → register-retains p advanced m valid) eq
step-evidence S.registerMuxer (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence S.registerMuxer (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState S.published p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState (S.muxerRegistered m) p) eq = via-evidence (S.demuxerForked m j) (Pool.fork j) (S.startupState (S.muxerRegistered m) p) (λ q advanced valid → retained (fork-evidence j p advanced) m valid , present (fork-evidence j p advanced) , fresh-distinct m j p valid (fresh (fork-evidence j p advanced))) eq
step-evidence (S.forkDemuxer j) (S.startupState (S.demuxerForked m d) p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence (S.forkDemuxer j) (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState S.awaitPublication p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState S.published p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState S.bufferReady p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState S.bearerReady p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState S.runEntered p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState S.startingTraced p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState S.egressReady p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState S.poolReady p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState (S.muxerForked m) p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState (S.muxerRegistered m) p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState (S.demuxerForked m d) p) eq = via-evidence (S.demuxerRegistered m d) (Pool.register) (S.startupState (S.demuxerForked m d) p) (λ q advanced valid → phase-retained (S.demuxerRegistered m d) p q (register-retains p advanced) valid) eq
step-evidence S.registerDemuxer (S.startupState (S.demuxerRegistered m d) p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState (S.matureTraced m d) p) eq = case eq of λ ()
step-evidence S.registerDemuxer (S.startupState (S.monitoring m d) p) eq = case eq of λ ()
step-evidence (S.child action) (S.startupState pc p) eq = via-evidence pc (S.poolAction action) (S.startupState pc p)
  (λ q advanced valid → phase-retained pc p q (child-retains action p advanced) valid) eq

step-projects : ∀ action s {s′} → S.step action s ≡ just s′ → PoolTrace (S.pool s) (S.pool s′)
step-projects action s eq = projection (step-evidence action s eq)
step-preserves : ∀ action s {s′} → S.step action s ≡ just s′ → Valid s → Valid s′
step-preserves action s eq = preservation (step-evidence action s eq)

append : ∀ {p as q bs r} → Pool.Executes p as q → Pool.Executes q bs r → Pool.Executes p (as ++ bs) r
append Pool.done tail = tail
append (Pool.next eq path) tail = Pool.next eq (append path tail)
exec-projects : ∀ {s actions s′} → S.Executes s actions s′ → PoolTrace (S.pool s) (S.pool s′)
exec-projects S.done = [] , Pool.done
exec-projects (S.next {s = s} {a = a} eq path) with step-projects a s eq | exec-projects path
... | as , first | bs , tail = as ++ bs , append first tail
exec-preserves : ∀ {s actions s′} → S.Executes s actions s′ → Valid s → Valid s′
exec-preserves S.done valid = valid
exec-preserves (S.next {s = s} {a = a} eq path) valid = exec-preserves path (step-preserves a s eq valid)
initial-valid : Valid S.initial
initial-valid = tt
from-initial : ∀ {actions s} → S.Executes S.initial actions s → Valid s
from-initial path = exec-preserves path initial-valid

-- Both physical handles were allocated in the very same queued pool, remain
-- captured historically, and have distinct identities. Their bodies may have
-- completed already; current registration and result/join facts are separate.
monitoring-from-initial : ∀ {actions s} muxer demuxer → S.Executes S.initial actions s →
  S.phase s ≡ S.monitoring muxer demuxer → Pair muxer demuxer (S.pool s) × PoolTrace Pool.initial (S.pool s)
monitoring-from-initial {s = s} muxer demuxer path phase =
  subst (λ pc → PhaseValid pc (S.pool s)) phase (from-initial path) , exec-projects path

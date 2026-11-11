{-# OPTIONS --guardedness #-}

-- Quiet subsystem actions may change the shared core, peers and governor state,
-- while retaining exact caller tables, job/followup rows and live handles.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesQuietSteps
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.OutboundKeys using (uniqueSame)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.ProductionPolicy as Policy
import ConnectionManagement.Properties.OwnedFramesQuietSource as Source
import ConnectionManagement.Properties.OwnedFramesObservation as Observation
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module V = Observation isBearerClosed isIOManagerError
  module D = Cancellation isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- WithQueue registration changes registry/mask metadata but no handle phase.
pool-register-handles : ∀ p {p′} → GP.Pool.step GP.Pool.register p ≡ just p′ → GP.Pool.handles p′ ≡ GP.Pool.handles p
pool-register-handles p eq with GP.Pool.phase p | GP.Pool.parentFork p
... | GP.Pool.openPool | just j with GP.Pool.member j (GP.Pool.registered p)
...   | false = case just-injective eq of λ { refl → refl }
...   | true = case eq of λ ()
pool-register-handles p eq | GP.Pool.openPool | nothing = case eq of λ ()
pool-register-handles p eq | GP.Pool.closing | parent = case eq of λ ()
pool-register-handles p eq | GP.Pool.closedPool | parent = case eq of λ ()
pool-register-handles p eq | GP.Pool.cancelPending j | parent = case eq of λ ()
pool-register-handles p eq | GP.Pool.joinPending j | parent = case eq of λ ()

-- Every permitted quiet normalPool effect keeps all body-handle observations.
normal-pool : ∀ a s {p} → Source.quiet a ≡ true → GP.normalPool a s ≡ just p → GP.Pool.handles p ≡ GP.Pool.handles (GP.pool s)
normal-pool (Sub.core action) s () eq
normal-pool Sub.publishPublicState s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool (Sub.sampleTime t) s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool (Sub.applyAt t) s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool (Sub.setTargets t) s permit eq = case just-injective eq of λ { refl → refl }
normal-pool (Sub.selectMonitor delay) s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool Sub.selectCompletion s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool Sub.selectTargets s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool Sub.selectWakeup s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool Sub.registerWakeup s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool Sub.expireWakeup s permit eq = case just-injective eq of λ { refl → refl }
normal-pool Sub.cancelWakeup s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool Sub.publishCounters s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool Sub.traceSelection s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool (Sub.selectPolicy picked) s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool (Sub.forkJob caller child sock) s () eq
normal-pool Sub.registerJob s permit eq with Sub.pc (GP.machine s) | GP.Pool.parentFork (GP.pool s)
... | Sub.register j rest | just k with j ≟ k
...   | yes same = pool-register-handles (GP.pool s) eq
...   | no apart = case eq of λ ()
normal-pool Sub.registerJob s permit eq | Sub.register j rest | nothing = case eq of λ ()
normal-pool Sub.registerJob s permit eq | Sub.publishPublic | parent = case eq of λ ()
normal-pool Sub.registerJob s permit eq | Sub.sampleInputs | parent = case eq of λ ()
normal-pool Sub.registerJob s permit eq | Sub.prepareWait | parent = case eq of λ ()
normal-pool Sub.registerJob s permit eq | Sub.selecting | parent = case eq of λ ()
normal-pool Sub.registerJob s permit eq | (Sub.cancelTimer selected) | parent = case eq of λ ()
normal-pool Sub.registerJob s permit eq | (Sub.apply selected) | parent = case eq of λ ()
normal-pool Sub.registerJob s permit eq | (Sub.publishView work) | parent = case eq of λ ()
normal-pool Sub.registerJob s permit eq | (Sub.traceDecision work) | parent = case eq of λ ()
normal-pool Sub.registerJob s permit eq | (Sub.launch work) | parent = case eq of λ ()
normal-pool Sub.registerJob s permit eq | (Sub.completionAssertionFailed result) | parent = case eq of λ ()
normal-pool Sub.finishLaunch s permit eq with GP.ownerOpen (GP.pool s)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl }
normal-pool (Sub.jobStep j action) s () eq
normal-pool (Sub.enqueueCompletion j delay) s () eq
normal-pool (Sub.deregisterJob j) s () eq
normal-pool (Sub.protocolResult ref n result) s permit eq = case just-injective eq of λ { refl → refl }
normal-pool (Sub.publishInitiatorResult ref i) s permit eq = case just-injective eq of λ { refl → refl }
normal-pool (Sub.pollPeer ref caller) s () eq
normal-pool (Sub.monitorStep ref action) s () eq
normal-pool (Sub.monitorFinished ref) s () eq
normal-pool (Sub.observeInitiatorFailure ref) s permit eq = case just-injective eq of λ { refl → refl }

-- Only jobStep can produce a physical body return; it is outside quiet.
note-return : ∀ a c p {p′} → Source.quiet a ≡ true → GP.noteReturn a c p ≡ just p′ → p′ ≡ p
note-return (Sub.core action) c p () eq
note-return Sub.publishPublicState c p permit eq = sym (just-injective eq)
note-return (Sub.sampleTime t) c p permit eq = sym (just-injective eq)
note-return (Sub.applyAt t) c p permit eq = sym (just-injective eq)
note-return (Sub.setTargets t) c p permit eq = sym (just-injective eq)
note-return (Sub.selectMonitor delay) c p permit eq = sym (just-injective eq)
note-return Sub.selectCompletion c p permit eq = sym (just-injective eq)
note-return Sub.selectTargets c p permit eq = sym (just-injective eq)
note-return Sub.selectWakeup c p permit eq = sym (just-injective eq)
note-return Sub.registerWakeup c p permit eq = sym (just-injective eq)
note-return Sub.expireWakeup c p permit eq = sym (just-injective eq)
note-return Sub.cancelWakeup c p permit eq = sym (just-injective eq)
note-return Sub.publishCounters c p permit eq = sym (just-injective eq)
note-return Sub.traceSelection c p permit eq = sym (just-injective eq)
note-return (Sub.selectPolicy picked) c p permit eq = sym (just-injective eq)
note-return (Sub.forkJob caller child sock) c p () eq
note-return Sub.registerJob c p permit eq = sym (just-injective eq)
note-return Sub.finishLaunch c p permit eq = sym (just-injective eq)
note-return (Sub.jobStep j action) c p () eq
note-return (Sub.enqueueCompletion j delay) c p () eq
note-return (Sub.deregisterJob j) c p () eq
note-return (Sub.protocolResult ref n result) c p permit eq = sym (just-injective eq)
note-return (Sub.publishInitiatorResult ref i) c p permit eq = sym (just-injective eq)
note-return (Sub.pollPeer ref caller) c p () eq
note-return (Sub.monitorStep ref action) c p () eq
note-return (Sub.monitorFinished ref) c p () eq
note-return (Sub.observeInitiatorFailure ref) c p permit eq = sym (just-injective eq)

-- Poll is the only noteGovernor constructor that changes monitor rows.
note-governor : ∀ a s target → Source.quiet a ≡ true → PS.noteGovernor (GP.run a) s target ≡ target
note-governor (Sub.core action) s target ()
note-governor Sub.publishPublicState s target permit = refl
note-governor (Sub.sampleTime t) s target permit = refl
note-governor (Sub.applyAt t) s target permit = refl
note-governor (Sub.setTargets t) s target permit = refl
note-governor (Sub.selectMonitor delay) s target permit = refl
note-governor Sub.selectCompletion s target permit = refl
note-governor Sub.selectTargets s target permit = refl
note-governor Sub.selectWakeup s target permit = refl
note-governor Sub.registerWakeup s target permit = refl
note-governor Sub.expireWakeup s target permit = refl
note-governor Sub.cancelWakeup s target permit = refl
note-governor Sub.publishCounters s target permit = refl
note-governor Sub.traceSelection s target permit = refl
note-governor (Sub.selectPolicy picked) s target permit = refl
note-governor (Sub.forkJob caller child sock) s target ()
note-governor Sub.registerJob s target permit = refl
note-governor Sub.finishLaunch s target permit = refl
note-governor (Sub.jobStep j action) s target ()
note-governor (Sub.enqueueCompletion j delay) s target ()
note-governor (Sub.deregisterJob j) s target ()
note-governor (Sub.protocolResult ref n result) s target permit = refl
note-governor (Sub.publishInitiatorResult ref i) s target permit = refl
note-governor (Sub.pollPeer ref caller) s target ()
note-governor (Sub.monitorStep ref action) s target ()
note-governor (Sub.monitorFinished ref) s target ()
note-governor (Sub.observeInitiatorFailure ref) s target permit = refl

-- The source projection exposes the actual quiet subsystem transition.
governor-quiet : ∀ a s {g′} → Source.quiet a ≡ true → GP.step (GP.run a) (PS.governor s) ≡ just g′ →
  D.Held s → D.Held (record s { governor = g′ })
governor-quiet a s permit eq (inv , unique , aux) with GP.normalPool a (PS.governor s) in pooled |
  GP.Production.step (Policy.dispatch a) (GP.source (PS.governor s)) in dispatched
... | just p′ | just source′ with GP.noteReturn a (Policy.machine source′) p′ in noted
...   | nothing = case eq of λ ()
...   | just p″ with GP.Production.step-projects (Policy.dispatch a) (GP.source (PS.governor s)) dispatched
...     | Sub.next advanced Sub.done = case just-injective eq of λ { refl → proj₁ carried , uniqueSame (proj₁ effect) unique , proj₂ carried }
  where
  effect = Source.quiet-effect a (PS.machine s) permit advanced
  handles = trans (cong GP.Pool.handles (note-return a (Policy.machine source′) p′ permit noted))
    (normal-pool a (PS.governor s) permit pooled)
  target = record s { governor = GP.supervised source′ p″
    (GP.noteRegions a (J.cm (Sub.world (Policy.machine source′))) (GP.regions (PS.governor s))) (GP.unwinding (PS.governor s)) }
  observed = V.observed-equal (C.capture s) (C.capture target) (proj₁ (proj₂ effect)) (proj₂ (proj₂ effect)) handles refl refl refl
  carried = V.observed-preserves (PS.cm target) (C.capture s) (C.capture target) observed (same-source (proj₁ effect) inv) aux
governor-quiet a s permit eq held | nothing | source = case eq of λ ()
governor-quiet a s permit eq held | just p | nothing = case eq of λ ()

-- Real PSA guards remain in force and the noteGovernor write is transported exactly.
quiet-step : ∀ a s {t} → Source.quiet a ≡ true → PS.step (PS.run (GP.run a)) s ≡ just t → D.Held s → D.Held t
quiet-step a s permit stepped held with PS.governorAllowed (GP.run a) s
... | false = case stepped of λ ()
... | true with GP.step (GP.run a) (PS.governor s) in advanced
...   | nothing = case stepped of λ ()
...   | just g′ = case just-injective stepped of λ { refl → subst D.Held
  (sym (note-governor a s (record s { governor = g′ }) permit)) (governor-quiet a s permit advanced held) }

-- Every quiet raw constructor therefore preserves full Reach at the shared K level.
k-quiet-step : ∀ a s {t} → Source.quiet a ≡ true → K.step (K.peerStep (PS.run (GP.run a))) s ≡ just t → R.Reach s → R.Reach t
k-quiet-step a s permit stepped held with K.peerOpen s ∧ K.peerAllowed (PS.run (GP.run a)) s
... | false = case stepped of λ ()
... | true with PS.step (PS.run (GP.run a)) (K.peers s) in advanced
...   | nothing = case stepped of λ ()
...   | just p = case just-injective stepped of λ { refl → quiet-step a (K.peers s) permit advanced held }

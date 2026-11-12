{-# OPTIONS --guardedness #-}

-- Logical peer steps reuse the existing exact source effects and caller laws.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedCallersSubsystem
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import ConnectionManagement.Domain using (ident)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.OutboundKeys using (KeySame; same-refl; fields-same)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Properties.OwnedCallersBase as Base
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesJobSource as Source
import ConnectionManagement.Properties.OwnedFramesIdentity as Identity
import ConnectionManagement.Properties.OwnedFramesJobNames as NamesFacts
import ConnectionManagement.Properties.OwnedFramesQuietSource as Quiet
import ConnectionManagement.Properties.OwnedFramesPollSource as Poll
import ConnectionManagement.Properties.OwnedFramesForkJob as ForkFacts
import ConnectionManagement.Properties.OwnedFramesFlagSteps as FlagsFacts
open Base isBearerClosed isIOManagerError using
  (module PS; module GP; module C; Foreign; PeerNF; keep-empty; primitive-empty; no-present; not-present; job-update; job-birth; copy-peer)
open Frames isBearerClosed isIOManagerError using (Inv)
private
  module X = Auxiliary isBearerClosed isIOManagerError
  module Names = NamesFacts isBearerClosed isIOManagerError
  module Fork = ForkFacts isBearerClosed isIOManagerError
  module Flags = FlagsFacts isBearerClosed isIOManagerError

-- Raw core aliases are unavailable through K's peer path.
allowed : Sub.Action → Bool
allowed (Sub.core _) = false
allowed _ = true

-- The physical pool's actual fork guard supplies the fresh job handle.
ForkFresh : Sub.Action → PS.State → Set
ForkFresh (Sub.forkJob _ _ _) s = lookup (ident (Sub.nextJob (PS.machine s))) (GP.Pool.handles (GP.pool (PS.governor s))) ≡ nothing
ForkFresh _ s = ⊤

-- Job source effects can create a frame only at that job's own caller.
job-empty : ∀ a f env {next world′} → J.step a f env ≡ just (next , world′) →
  ∀ w → w ≢ J.caller f → lookup w (O.acquiring (J.cm env)) ≡ nothing → lookup w (O.releasing (J.cm env)) ≡ nothing →
  lookup w (O.acquiring (J.cm world′)) ≡ nothing × lookup w (O.releasing (J.cm world′)) ≡ nothing
job-empty a f env stepped w apart acq rel with Source.step-effect a f env stepped
... | Source.same keys = keep-empty keys w acq rel
... | Source.acquired req raw pc = primitive-empty (O.beginAcquire (J.caller f) req) (J.cm env) w
  (λ { _ _ refl → apart }) (λ { _ _ () }) raw acq rel
... | Source.released key raw pc = primitive-empty (O.beginRelease (J.caller f) key) (J.cm env) w
  (λ { _ _ () }) (λ { _ _ refl → apart }) raw acq rel

-- A job continuation keeps its historical caller and begins only on that caller.
job-safe : ∀ j a s {d} → Sub.advance (Sub.jobStep j a) (PS.machine s) ≡ just d → PeerNF s → PeerNF (PS.setMachine d s)
job-safe j a s eq held with lookup j (Sub.jobs (PS.machine s)) in found
... | nothing = case eq of λ ()
... | just jf with Sub.queued jf | J.step a (Sub.execution jf) (Sub.world (PS.machine s)) in stepped
...   | true | _ = case eq of λ ()
...   | false | nothing = case eq of λ ()
...   | false | just (next , world′) = case just-injective eq of λ { refl → proof }
  where
  -- Consume the existing active owner at this writer boundary.
  proof : PeerNF (PS.setMachine (record (PS.machine s) { world = world′; jobs = put j (record jf { execution = next }) (Sub.jobs (PS.machine s)) }) s)
  proof w present foreign = no-present (J.cm world′) w (proj₁ empty′) (proj₂ empty′) present
    where
    oldForeign : Foreign w (C.capture s)
    oldForeign = trans (sym (Names.unowned-put w j jf (record jf { execution = next }) (Sub.jobs (PS.machine s)) found
      (Identity.step-caller a (Sub.execution jf) (Sub.world (PS.machine s)) stepped))) (proj₁ foreign) , proj₂ foreign
    empty = not-present (PS.cm s) w (λ p → held w p oldForeign)
    empty′ = job-empty a (Sub.execution jf) (Sub.world (PS.machine s)) stepped w
      (λ same → X.unowned-found w (Sub.jobs (PS.machine s)) j jf (proj₁ oldForeign) found (sym same)) (proj₁ empty) (proj₂ empty)

-- An attached followup's caller is the captured physical monitor worker.
follow-safe : ∀ ref a s {d} → Sub.advance (Sub.monitorStep ref a) (PS.machine s) ≡ just d →
  X.Aux (C.capture s) → PeerNF s → PeerNF (PS.setMachine d s)
follow-safe ref a s eq aux held with lookup ref (Sub.monitors (PS.machine s)) in found
... | nothing = case eq of λ ()
... | just f with J.step a f (Sub.world (PS.machine s)) in stepped
...   | nothing = case eq of λ ()
...   | just (next , world′) = case just-injective eq of λ { refl → proof }
  where
  backing = X.Aux.followThreads aux ref f found
  -- Consume the existing active owner at this writer boundary.
  proof : PeerNF (PS.setMachine (record (PS.machine s) { world = world′; monitors = put ref next (Sub.monitors (PS.machine s)) }) s)
  proof w present foreign = no-present (J.cm world′) w (proj₁ empty′) (proj₂ empty′) present
    where
    empty = not-present (PS.cm s) w (λ p → held w p foreign)
    apart : w ≢ J.caller f
    apart same = X.peer-worker-absent w ref (PS.monitors s) (X.FollowThread.tid backing) (X.FollowThread.thread backing)
      (proj₂ foreign) (X.FollowThread.found backing) (trans (sym (X.FollowThread.caller backing)) (sym same))
    empty′ = job-empty a f (Sub.world (PS.machine s)) stepped w apart (proj₁ empty) (proj₂ empty)

-- Flag changes keep all caller identities; the existing shape theorem gives
-- the named row, old lookup, unchanged execution, source and followups.
flag-safe : ∀ a s {d} → Flags.flag-action a ≡ true → Sub.advance a (PS.machine s) ≡ just d → PeerNF s → PeerNF (PS.setMachine d s)
flag-safe a s selected eq held with Flags.flag-effect a (PS.machine s) selected eq
... | effect rewrite Flags.Effect.source effect | Flags.Effect.rows effect =
  job-update (PS.cm s) (C.capture s) (Flags.Effect.key effect) (Flags.Effect.old effect) (Flags.Effect.next effect)
    (Flags.Effect.saved effect) (cong J.caller (Flags.Effect.execution effect)) held

-- Pool freshness prevents a new job from overwriting any active frame's owner.
fork-safe : ∀ w child sock s {d} → Sub.advance (Sub.forkJob w child sock) (PS.machine s) ≡ just d →
  ForkFresh (Sub.forkJob w child sock) s → Inv (PS.cm s) (C.capture s) → PeerNF s → PeerNF (PS.setMachine d s)
fork-safe w child sock s eq fresh inv held with Fork.fork-shape w child sock (PS.machine s) eq
... | born rewrite Fork.Born.source born | Fork.Born.rows born = job-birth (PS.cm s) (C.capture s) (ident (Sub.nextJob (PS.machine s))) (Fork.Born.frame born) fresh inv held

-- Quiet effects retain jobs and source key sets, including all scheduling steps.
quiet-safe : ∀ a s {d} → Quiet.quiet a ≡ true → Sub.advance a (PS.machine s) ≡ just d → PeerNF s → PeerNF (PS.setMachine d s)
quiet-safe a s {d} selected eq held with Quiet.quiet-effect a (PS.machine s) selected eq
... | keys , rows , follows = copy-peer s (PS.setMachine d s) keys rows refl held

-- Polling cannot initialize a CM call or change the historical job table.
poll-safe : ∀ ref w s {d} → Sub.advance (Sub.pollPeer ref w) (PS.machine s) ≡ just d → PeerNF s → PeerNF (PS.setMachine d s)
poll-safe ref w s {d} eq held with Poll.poll-effect ref w (PS.machine s) eq
... | effect = copy-peer s (PS.setMachine d s) (fields-same (PS.cm s) (J.cm (Sub.world d))
  (cong O.acquiring (Poll.Effect.source effect)) (cong O.releasing (Poll.Effect.source effect))
  (cong O.acquired (Poll.Effect.source effect)) (cong O.released (Poll.Effect.source effect))) (Poll.Effect.jobs effect) refl held

-- Removing a completed logical followup leaves historical ownership unchanged.
finished-safe : ∀ ref s {d} → Sub.advance (Sub.monitorFinished ref) (PS.machine s) ≡ just d → PeerNF s → PeerNF (PS.setMachine d s)
finished-safe ref s eq held with lookup ref (Sub.monitors (PS.machine s))
... | nothing = case eq of λ ()
... | just f with J.pc f
...   | J.complete _ = case just-injective eq of λ { refl → held }
finished-safe ref s eq held | just f | J.begin = case eq of λ ()
finished-safe ref s eq held | just f | J.awaitAcquire = case eq of λ ()
finished-safe ref s eq held | just f | (J.startBundle t ns) = case eq of λ ()
finished-safe ref s eq held | just f | (J.publishBundle t) = case eq of λ ()
finished-safe ref s eq held | just f | J.markWarm = case eq of λ ()
finished-safe ref s eq held | just f | J.forkMonitor = case eq of λ ()
finished-safe ref s eq held | just f | J.finishActivation = case eq of λ ()
finished-safe ref s eq held | just f | J.awaitHot = case eq of λ ()
finished-safe ref s eq held | just f | J.awaitAll = case eq of λ ()
finished-safe ref s eq held | just f | J.callRelease = case eq of λ ()
finished-safe ref s eq held | just f | J.awaitRelease = case eq of λ ()
finished-safe ref s eq held | just f | J.delayFailure = case eq of λ ()
finished-safe ref s eq held | just f | (J.awaitCold result) = case eq of λ ()
finished-safe ref s eq held | just f | (J.acquirePolicy fault) = case eq of λ ()
finished-safe ref s eq held | just f | (J.nodeDelivery fault) = case eq of λ ()
finished-safe ref s eq held | just f | (J.nodeRethrow fault) = case eq of λ ()

-- The complete logical step proof uses existing source classifiers for quiet
-- cases and the small separate call/identity lemmas for changing families.
sub-safe : ∀ a s {d} → allowed a ≡ true → Sub.advance a (PS.machine s) ≡ just d →
  ForkFresh a s → Inv (PS.cm s) (C.capture s) → X.Aux (C.capture s) → PeerNF s → PeerNF (PS.setMachine d s)
sub-safe (Sub.core a) s () eq fresh inv aux held
sub-safe (Sub.forkJob w child sock) s ok eq fresh inv aux held = fork-safe w child sock s eq fresh inv held
sub-safe (Sub.jobStep j a) s ok eq fresh inv aux held = job-safe j a s eq held
sub-safe (Sub.monitorStep ref a) s ok eq fresh inv aux held = follow-safe ref a s eq aux held
sub-safe (Sub.enqueueCompletion j delay) s ok eq fresh inv aux held = flag-safe (Sub.enqueueCompletion j delay) s refl eq held
sub-safe (Sub.deregisterJob j) s ok eq fresh inv aux held = flag-safe (Sub.deregisterJob j) s refl eq held
sub-safe (Sub.pollPeer ref w) s ok eq fresh inv aux held = poll-safe ref w s eq held
sub-safe (Sub.monitorFinished ref) s ok eq fresh inv aux held = finished-safe ref s eq held
sub-safe Sub.publishPublicState s ok eq fresh inv aux held = quiet-safe Sub.publishPublicState s refl eq held
sub-safe (Sub.sampleTime t) s ok eq fresh inv aux held = quiet-safe (Sub.sampleTime t) s refl eq held
sub-safe (Sub.applyAt t) s ok eq fresh inv aux held = quiet-safe (Sub.applyAt t) s refl eq held
sub-safe (Sub.setTargets desired) s ok eq fresh inv aux held = quiet-safe (Sub.setTargets desired) s refl eq held
sub-safe (Sub.selectMonitor delays) s ok eq fresh inv aux held = quiet-safe (Sub.selectMonitor delays) s refl eq held
sub-safe Sub.selectCompletion s ok eq fresh inv aux held = quiet-safe Sub.selectCompletion s refl eq held
sub-safe Sub.selectTargets s ok eq fresh inv aux held = quiet-safe Sub.selectTargets s refl eq held
sub-safe Sub.selectWakeup s ok eq fresh inv aux held = quiet-safe Sub.selectWakeup s refl eq held
sub-safe Sub.registerWakeup s ok eq fresh inv aux held = quiet-safe Sub.registerWakeup s refl eq held
sub-safe Sub.expireWakeup s ok eq fresh inv aux held = quiet-safe Sub.expireWakeup s refl eq held
sub-safe Sub.cancelWakeup s ok eq fresh inv aux held = quiet-safe Sub.cancelWakeup s refl eq held
sub-safe Sub.publishCounters s ok eq fresh inv aux held = quiet-safe Sub.publishCounters s refl eq held
sub-safe Sub.traceSelection s ok eq fresh inv aux held = quiet-safe Sub.traceSelection s refl eq held
sub-safe (Sub.selectPolicy picked) s ok eq fresh inv aux held = quiet-safe (Sub.selectPolicy picked) s refl eq held
sub-safe Sub.registerJob s ok eq fresh inv aux held = quiet-safe Sub.registerJob s refl eq held
sub-safe Sub.finishLaunch s ok eq fresh inv aux held = quiet-safe Sub.finishLaunch s refl eq held
sub-safe (Sub.protocolResult ref n result) s ok eq fresh inv aux held = quiet-safe (Sub.protocolResult ref n result) s refl eq held
sub-safe (Sub.publishInitiatorResult ref n) s ok eq fresh inv aux held = quiet-safe (Sub.publishInitiatorResult ref n) s refl eq held
sub-safe (Sub.observeInitiatorFailure ref) s ok eq fresh inv aux held = quiet-safe (Sub.observeInitiatorFailure ref) s refl eq held

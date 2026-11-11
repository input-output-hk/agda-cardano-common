{-# OPTIONS --guardedness #-}

-- Actual cleanup, handoff and completed-unwind governor writers.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesUnwindSteps
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.OutboundKeys using (KeySame; same-refl; uniqueSame)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
import ConnectionManagement.Properties.OwnedFramesCancel as CancelFacts
import ConnectionManagement.Properties.OwnedFramesUnwindContext as UnwindFacts
import ConnectionManagement.Properties.OwnedFramesPoolTransport as PoolFacts
import ConnectionManagement.Properties.OwnedFramesContext as ContextFacts
import ConnectionManagement.Properties.OwnedFramesObservation as Observation
import ConnectionManagement.Properties.OwnedFramesLifts as Lifts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
open Frames isBearerClosed isIOManagerError
private
  module D = Cancellation isBearerClosed isIOManagerError
  module U = UnwindFacts isBearerClosed isIOManagerError
  module P = PoolFacts isBearerClosed isIOManagerError
  module V = ContextFacts isBearerClosed isIOManagerError
  module Obs = Observation isBearerClosed isIOManagerError
  module L = Lifts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- Caller cleanup uses the actual acquisition world writer and retains keys.
governor-cleanup : ∀ j a s {g′} → GP.step (GP.cleanup j a) (PS.governor s) ≡ just g′ → D.Held s → D.Held (record s { governor = g′ })
governor-cleanup j a s eq (inv , unique , aux) with lookup j (GP.unwinding (PS.governor s)) in saved
... | nothing = case eq of λ ()
... | just old with Cancel.step a old (PS.cm s) in cleaned
...   | nothing = case eq of λ ()
...   | just (next , c′) = case just-injective eq of λ { refl →
  U.unwind-inv c′ (C.capture s) j next (same-source keys inv) , uniqueSame keys unique ,
  U.unwind-aux (C.capture s) j old next saved (CancelFacts.cleanup-caller a old (PS.cm s) cleaned) aux }
  where keys = CancelFacts.cleanup-keys a old (PS.cm s) cleaned

-- Region bookkeeping is outside the six ownership observations.
region-held : ∀ s regions → D.Held s → D.Held (record s { governor = record (PS.governor s) { regions = regions } })
region-held s regions (inv , unique , aux) =
  V.copy-inv (PS.cm s) (C.capture s) (C.capture target) inv , unique , V.copy-aux (C.capture s) (C.capture target) aux
  where target = record s { governor = record (PS.governor s) { regions = regions } }

-- Handoff keeps its real fork-gap and connected-commit guards.
governor-handoff : ∀ w s {g′} → GP.step (GP.handoff w) (PS.governor s) ≡ just g′ → D.Held s → D.Held (record s { governor = g′ })
governor-handoff w s eq held with GP.region w (PS.governor s) | lookup w (O.acquiring (PS.cm s))
... | Cancel.forkedBeforeHandoff | just f with A.pc f
...   | A.connectedCommit e promise key = case just-injective eq of λ { refl → region-held s (put w Cancel.ordinary (GP.regions (PS.governor s))) held }
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | A.selecting = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.count next) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.allocatePromise e) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.openSocket e pid) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.configureSocket e pid) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.bindSocket e pid) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.connectSocket e pid) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.localAddress e pid) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.updateAddress e pid key) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.forkHandler e pid key) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.awaitResult e pid key) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.commitResult e key result) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.waitingInbound e key) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.closeError e err) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.removeError e err) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | just f | (A.complete result) = case eq of λ ()
governor-handoff w s eq held | Cancel.forkedBeforeHandoff | nothing = case eq of λ ()
governor-handoff w s eq held | Cancel.ordinary | _ = case eq of λ ()
governor-handoff w s eq held | Cancel.protectedCleanup | _ = case eq of λ ()
governor-handoff w s eq held | Cancel.interruptibleOpen | _ = case eq of λ ()

-- Cold restoration changes peer status, leaving all ownership observations.
restore-effect : ∀ f c → KeySame (J.cm (Sub.world c)) (J.cm (Sub.world (GP.restoreCold f c))) ×
  Sub.jobs (GP.restoreCold f c) ≡ Sub.jobs c × Sub.monitors (GP.restoreCold f c) ≡ Sub.monitors c
restore-effect f c with G.kind (J.work f) | J.pc f
... | G.establish | J.begin = same-refl (J.cm (Sub.world c)) , refl , refl
... | G.establish | J.complete result = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | J.awaitAcquire with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | (J.startBundle t ns) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | (J.publishBundle t) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | J.markWarm with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | J.forkMonitor with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | J.finishActivation with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | J.awaitHot with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | J.awaitAll with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | J.callRelease with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | J.awaitRelease with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | J.delayFailure with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | (J.awaitCold result) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | (J.acquirePolicy fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | (J.nodeDelivery fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.establish | (J.nodeRethrow fault) with lookup (J.connectionRef f) (J.peers (Sub.world c))
... | nothing = same-refl (J.cm (Sub.world c)) , refl , refl
... | just peer = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.forget | _ = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.activate | _ = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.close | _ = same-refl (J.cm (Sub.world c)) , refl , refl
restore-effect f c | G.deactivate | _ = same-refl (J.cm (Sub.world c)) , refl , refl


-- Transfer the three exact source/subsystem facts into the complete PS view.
restore-held : ∀ f s → D.Held s → D.Held (record s { governor = record (PS.governor s)
  { source = record (GP.source (PS.governor s)) { machine = GP.restoreCold f (PS.machine s) } } })
restore-held f s (inv , unique , aux) = proj₁ carried , uniqueSame (proj₁ effect) unique , proj₂ carried
  where
  effect = restore-effect f (PS.machine s)
  target = record s { governor = record (PS.governor s) { source = record (GP.source (PS.governor s)) { machine = GP.restoreCold f (PS.machine s) } } }
  observed = Obs.observed-equal (C.capture s) (C.capture target) (proj₁ (proj₂ effect)) (proj₂ (proj₂ effect)) refl refl refl refl
  carried = Obs.observed-preserves (PS.cm target) (C.capture s) (C.capture target) observed (same-source (proj₁ effect) inv) aux

-- Physical unwind completion preserves stopped handles before restoring Cold.
governor-body-unwound : ∀ j s {g′} → GP.step (GP.bodyUnwound j) (PS.governor s) ≡ just g′ → D.Held s → D.Held (record s { governor = g′ })
governor-body-unwound j s eq held with lookup j (GP.unwinding (PS.governor s)) | lookup j (Sub.jobs (PS.machine s))
... | just f | just jf with Cancel.pc f
...   | Cancel.finished Cancel.abandoned with GP.Pool.step (GP.Pool.bodyUnwound j) (GP.pool (PS.governor s)) in unwound
...     | just p′ = case just-injective eq of λ { refl → restore-held (Sub.execution jf)
  (record s { governor = record (PS.governor s) { pool = p′ } })
  (P.gov-held s p′ (P.G.step-stable (GP.Pool.bodyUnwound j) (GP.pool (PS.governor s)) refl unwound) held) }
...     | nothing = case eq of λ ()
governor-body-unwound j s eq held | just f | just jf | Cancel.finished Cancel.cleanupComplete with GP.Pool.step (GP.Pool.bodyUnwound j) (GP.pool (PS.governor s)) in unwound
... | just p′ = case just-injective eq of λ { refl → restore-held (Sub.execution jf)
  (record s { governor = record (PS.governor s) { pool = p′ } })
  (P.gov-held s p′ (P.G.step-stable (GP.Pool.bodyUnwound j) (GP.pool (PS.governor s)) refl unwound) held) }
... | nothing = case eq of λ ()
governor-body-unwound j s eq held | just f | just jf | Cancel.cleaning active = case eq of λ ()
governor-body-unwound j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) = case eq of λ ()
governor-body-unwound j s eq held | nothing | _ = case eq of λ ()
governor-body-unwound j s eq held | just f | nothing = case eq of λ ()

-- Generic lifts retain the actual PS and K permission checks for these writers.
k-cleanup : ∀ j a s {t} → K.step (K.peerStep (PS.run (GP.cleanup j a))) s ≡ just t → R.Reach s → R.Reach t
k-cleanup j a = L.peer-lift (PS.run (GP.cleanup j a)) (λ s → L.governor-lift (GP.cleanup j a) s (governor-cleanup j a s) (λ after → refl))
k-handoff : ∀ w s {t} → K.step (K.peerStep (PS.run (GP.handoff w))) s ≡ just t → R.Reach s → R.Reach t
k-handoff w = L.peer-lift (PS.run (GP.handoff w)) (λ s → L.governor-lift (GP.handoff w) s (governor-handoff w s) (λ after → refl))
k-body-unwound : ∀ j s {t} → K.step (K.peerStep (PS.run (GP.bodyUnwound j))) s ≡ just t → R.Reach s → R.Reach t
k-body-unwound j = L.peer-lift (PS.run (GP.bodyUnwound j)) (λ s → L.governor-lift (GP.bodyUnwound j) s (governor-body-unwound j s) (λ after → refl))

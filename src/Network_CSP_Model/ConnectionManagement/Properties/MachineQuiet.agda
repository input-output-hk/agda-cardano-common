{-# OPTIONS --guardedness #-}

-- An exited, deactivated inbound governor with no pending CM call stays so
-- under every machine step. From that state a release or remote call cannot
-- begin (both need a needsCM continuation), handler lifecycle steps only
-- rewrite mux rows, and all other steps write only the shared world,
-- lifecycles or publication faults.
module ConnectionManagement.Properties.MachineQuiet where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (any)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Machine
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.IGTypes as IGTypes
open import ConnectionManagement.Properties.IGQuiet using (Quiet; quiet-step)

-- Handler lifecycle steps keep the governor's control state.
attach-quiet : ∀ w err rt ig s {rt′ ig′} → Quiet ig → Life.attachMux w err rt ig s ≡ just (rt′ , ig′) → Quiet ig′
attach-quiet w err rt ig s q eq with lookup w rt | lookup w (S.handlers s) | lookup w (S.cleanups s)
... | nothing | nothing | _ = case eq of λ ()
... | nothing | just _ | just _ = case eq of λ ()
... | just _ | _ | _ = case eq of λ ()
... | nothing | just h | nothing with lookup (S.handlerPromise h) (S.handshakeResults s)
...   | nothing = case eq of λ ()
...   | just S.query = case eq of λ ()
...   | just (S.handlerError _ _) = case eq of λ ()
...   | just (S.negotiated hid _) with lookup hid (IG.handles (IG.execution ig))
...     | nothing = case eq of λ ()
...     | just hd with lookup (M.muxRef hd) (IG.muxes (IG.execution ig)) | Life.hasMux (M.muxRef hd) rt
...       | nothing | _ = case eq of λ ()
...       | just _ | true = case eq of λ ()
...       | just m | false with M.status m | M.callback m
...         | M.ready | M.returned = case just-injective eq of λ { refl → q }
...         | M.ready | M.readActive _ = case eq of λ ()
...         | M.ready | M.commitTrace _ _ = case eq of λ ()
...         | M.ready | M.afterStart _ = case eq of λ ()
...         | M.ready | M.forkPending _ = case eq of λ ()
...         | M.ready | M.afterFailure = case eq of λ ()
...         | M.ready | M.tracerFailed _ = case eq of λ ()
...         | M.stopping | _ = case eq of λ ()
...         | M.stopped | _ = case eq of λ ()
...         | M.failed _ | _ = case eq of λ ()
life-quiet : ∀ w a rt ig s {rt′ ig′} → Quiet ig → Life.step w a rt ig s ≡ just (rt′ , ig′) → Quiet ig′
life-quiet w (Life.attach err) rt ig s q eq = attach-quiet w err rt ig s q eq
life-quiet w Life.jobPoolClosed rt ig s q eq with lookup w rt
... | nothing = case eq of λ ()
... | just f with Life.phase f | lookup (Life.capturedMux f) (IG.muxes (IG.execution ig))
...   | Life.poolClosing | just m = case just-injective eq of λ { refl → q }
...   | Life.normalClosing | just m = case just-injective eq of λ { refl → q }
...   | Life.syncClosing err | just m = case just-injective eq of λ { refl → q }
...   | Life.monitoring | _ = case eq of λ ()
...   | Life.poolClosing | nothing = case eq of λ ()
...   | Life.poolClosed | _ = case eq of λ ()
...   | Life.deadTracing | _ = case eq of λ ()
...   | Life.bodyExited | _ = case eq of λ ()
...   | Life.finalizing | _ = case eq of λ ()
...   | Life.normalClosing | nothing = case eq of λ ()
...   | Life.normalClosed | _ = case eq of λ ()
...   | Life.normalBodyExited | _ = case eq of λ ()
...   | Life.syncClosing _ | nothing = case eq of λ ()
...   | Life.syncClosed _ | _ = case eq of λ ()
...   | Life.classifying _ | _ = case eq of λ ()
...   | Life.peerRethrow _ | _ = case eq of λ ()
...   | Life.nodeDelivery _ | _ = case eq of λ ()
...   | Life.nodeRethrow _ | _ = case eq of λ ()
...   | Life.peerBodyExited _ | _ = case eq of λ ()
...   | Life.nodeBodyExited _ | _ = case eq of λ ()
life-quiet w Life.publishAsyncFailure rt ig s q eq with lookup w rt
... | nothing = case eq of λ ()
... | just f with Life.phase f | lookup (Life.capturedMux f) (IG.muxes (IG.execution ig))
...   | Life.poolClosed | just m = case just-injective eq of λ { refl → q }
...   | Life.monitoring | _ = case eq of λ ()
...   | Life.poolClosing | _ = case eq of λ ()
...   | Life.poolClosed | nothing = case eq of λ ()
...   | Life.deadTracing | _ = case eq of λ ()
...   | Life.bodyExited | _ = case eq of λ ()
...   | Life.finalizing | _ = case eq of λ ()
...   | Life.normalClosing | _ = case eq of λ ()
...   | Life.normalClosed | _ = case eq of λ ()
...   | Life.normalBodyExited | _ = case eq of λ ()
...   | Life.syncClosing _ | _ = case eq of λ ()
...   | Life.syncClosed _ | _ = case eq of λ ()
...   | Life.classifying _ | _ = case eq of λ ()
...   | Life.peerRethrow _ | _ = case eq of λ ()
...   | Life.nodeDelivery _ | _ = case eq of λ ()
...   | Life.nodeRethrow _ | _ = case eq of λ ()
...   | Life.peerBodyExited _ | _ = case eq of λ ()
...   | Life.nodeBodyExited _ | _ = case eq of λ ()
life-quiet w Life.finishRethrow rt ig s q eq with lookup w rt
... | nothing = case eq of λ ()
... | just f with Life.phase f | lookup (Life.capturedMux f) (IG.muxes (IG.execution ig))
...   | Life.monitoring | _ = case eq of λ ()
...   | Life.poolClosing | _ = case eq of λ ()
...   | Life.poolClosed | _ = case eq of λ ()
...   | Life.deadTracing | nothing = case eq of λ ()
...   | Life.bodyExited | _ = case eq of λ ()
...   | Life.finalizing | _ = case eq of λ ()
...   | Life.normalClosing | _ = case eq of λ ()
...   | Life.normalClosed | _ = case eq of λ ()
...   | Life.normalBodyExited | _ = case eq of λ ()
...   | Life.syncClosing _ | _ = case eq of λ ()
...   | Life.syncClosed _ | _ = case eq of λ ()
...   | Life.classifying _ | _ = case eq of λ ()
...   | Life.peerRethrow _ | _ = case eq of λ ()
...   | Life.nodeDelivery _ | _ = case eq of λ ()
...   | Life.nodeRethrow _ | _ = case eq of λ ()
...   | Life.peerBodyExited _ | _ = case eq of λ ()
...   | Life.nodeBodyExited _ | _ = case eq of λ ()
...   | Life.deadTracing | just m with M.callback m
...     | M.returned = case just-injective eq of λ { refl → q }
...     | M.readActive _ = case eq of λ ()
...     | M.commitTrace _ _ = case eq of λ ()
...     | M.afterStart _ = case eq of λ ()
...     | M.forkPending _ = case eq of λ ()
...     | M.afterFailure = case eq of λ ()
...     | M.tracerFailed _ = case eq of λ ()
life-quiet w Life.monitorReturned rt ig s q eq with lookup w rt
... | nothing = case eq of λ ()
... | just f with Life.phase f | lookup (Life.capturedMux f) (IG.muxes (IG.execution ig))
...   | Life.monitoring | nothing = case eq of λ ()
...   | Life.poolClosing | _ = case eq of λ ()
...   | Life.poolClosed | _ = case eq of λ ()
...   | Life.deadTracing | _ = case eq of λ ()
...   | Life.bodyExited | _ = case eq of λ ()
...   | Life.finalizing | _ = case eq of λ ()
...   | Life.normalClosing | _ = case eq of λ ()
...   | Life.normalClosed | _ = case eq of λ ()
...   | Life.normalBodyExited | _ = case eq of λ ()
...   | Life.syncClosing _ | _ = case eq of λ ()
...   | Life.syncClosed _ | _ = case eq of λ ()
...   | Life.classifying _ | _ = case eq of λ ()
...   | Life.peerRethrow _ | _ = case eq of λ ()
...   | Life.nodeDelivery _ | _ = case eq of λ ()
...   | Life.nodeRethrow _ | _ = case eq of λ ()
...   | Life.peerBodyExited _ | _ = case eq of λ ()
...   | Life.nodeBodyExited _ | _ = case eq of λ ()
...   | Life.monitoring | just m with M.status m | M.callback m
...     | M.stopped | M.returned = case just-injective eq of λ { refl → q }
...     | M.ready | _ = case eq of λ ()
...     | M.stopping | _ = case eq of λ ()
...     | M.stopped | M.readActive _ = case eq of λ ()
...     | M.stopped | M.commitTrace _ _ = case eq of λ ()
...     | M.stopped | M.afterStart _ = case eq of λ ()
...     | M.stopped | M.forkPending _ = case eq of λ ()
...     | M.stopped | M.afterFailure = case eq of λ ()
...     | M.stopped | M.tracerFailed _ = case eq of λ ()
...     | M.failed _ | _ = case eq of λ ()
life-quiet w Life.monitorThrew rt ig s q eq with lookup w rt
... | nothing = case eq of λ ()
... | just f with Life.phase f | lookup (Life.capturedMux f) (IG.muxes (IG.execution ig))
...   | Life.monitoring | nothing = case eq of λ ()
...   | Life.poolClosing | _ = case eq of λ ()
...   | Life.poolClosed | _ = case eq of λ ()
...   | Life.deadTracing | _ = case eq of λ ()
...   | Life.bodyExited | _ = case eq of λ ()
...   | Life.finalizing | _ = case eq of λ ()
...   | Life.normalClosing | _ = case eq of λ ()
...   | Life.normalClosed | _ = case eq of λ ()
...   | Life.normalBodyExited | _ = case eq of λ ()
...   | Life.syncClosing _ | _ = case eq of λ ()
...   | Life.syncClosed _ | _ = case eq of λ ()
...   | Life.classifying _ | _ = case eq of λ ()
...   | Life.peerRethrow _ | _ = case eq of λ ()
...   | Life.nodeDelivery _ | _ = case eq of λ ()
...   | Life.nodeRethrow _ | _ = case eq of λ ()
...   | Life.peerBodyExited _ | _ = case eq of λ ()
...   | Life.nodeBodyExited _ | _ = case eq of λ ()
...   | Life.monitoring | just m with M.status m | M.callback m
...     | M.failed err | M.returned = case just-injective eq of λ { refl → q }
...     | M.ready | _ = case eq of λ ()
...     | M.stopping | _ = case eq of λ ()
...     | M.stopped | _ = case eq of λ ()
...     | M.failed _ | M.readActive _ = case eq of λ ()
...     | M.failed _ | M.commitTrace _ _ = case eq of λ ()
...     | M.failed _ | M.afterStart _ = case eq of λ ()
...     | M.failed _ | M.forkPending _ = case eq of λ ()
...     | M.failed _ | M.afterFailure = case eq of λ ()
...     | M.failed _ | M.tracerFailed _ = case eq of λ ()
life-quiet w (Life.tracerThrew err) rt ig s q eq with lookup w rt
... | nothing = case eq of λ ()
... | just f with Life.phase f | lookup (Life.capturedMux f) (IG.muxes (IG.execution ig))
...   | Life.monitoring | nothing = case eq of λ ()
...   | Life.poolClosing | _ = case eq of λ ()
...   | Life.poolClosed | _ = case eq of λ ()
...   | Life.deadTracing | _ = case eq of λ ()
...   | Life.bodyExited | _ = case eq of λ ()
...   | Life.finalizing | _ = case eq of λ ()
...   | Life.normalClosing | _ = case eq of λ ()
...   | Life.normalClosed | _ = case eq of λ ()
...   | Life.normalBodyExited | _ = case eq of λ ()
...   | Life.syncClosing _ | _ = case eq of λ ()
...   | Life.syncClosed _ | _ = case eq of λ ()
...   | Life.classifying _ | _ = case eq of λ ()
...   | Life.peerRethrow _ | _ = case eq of λ ()
...   | Life.nodeDelivery _ | _ = case eq of λ ()
...   | Life.nodeRethrow _ | _ = case eq of λ ()
...   | Life.peerBodyExited _ | _ = case eq of λ ()
...   | Life.nodeBodyExited _ | _ = case eq of λ ()
...   | Life.monitoring | just m with M.callback m
...     | M.tracerFailed _ = case just-injective eq of λ { refl → q }
...     | M.readActive _ = case eq of λ ()
...     | M.commitTrace _ _ = case eq of λ ()
...     | M.afterStart _ = case eq of λ ()
...     | M.forkPending _ = case eq of λ ()
...     | M.afterFailure = case eq of λ ()
...     | M.returned = case eq of λ ()
life-quiet w Life.finishBuffer rt ig s q eq with lookup w rt
... | nothing = case eq of λ ()
... | just f with Life.phase f
...   | Life.normalClosed = case just-injective eq of λ { refl → q }
...   | Life.syncClosed err = case just-injective eq of λ { refl → q }
...   | Life.monitoring = case eq of λ ()
...   | Life.poolClosing = case eq of λ ()
...   | Life.poolClosed = case eq of λ ()
...   | Life.deadTracing = case eq of λ ()
...   | Life.bodyExited = case eq of λ ()
...   | Life.finalizing = case eq of λ ()
...   | Life.normalClosing = case eq of λ ()
...   | Life.normalBodyExited = case eq of λ ()
...   | Life.syncClosing _ = case eq of λ ()
...   | Life.classifying _ = case eq of λ ()
...   | Life.peerRethrow _ = case eq of λ ()
...   | Life.nodeDelivery _ = case eq of λ ()
...   | Life.nodeRethrow _ = case eq of λ ()
...   | Life.peerBodyExited _ = case eq of λ ()
...   | Life.nodeBodyExited _ = case eq of λ ()
life-quiet w (Life.choosePolicy policy) rt ig s q eq with lookup w rt
... | nothing = case eq of λ ()
... | just f with Life.phase f | policy
...   | Life.classifying err | Life.shutdownPeer = case just-injective eq of λ { refl → q }
...   | Life.classifying err | Life.shutdownNode = case just-injective eq of λ { refl → q }
...   | Life.monitoring | _ = case eq of λ ()
...   | Life.poolClosing | _ = case eq of λ ()
...   | Life.poolClosed | _ = case eq of λ ()
...   | Life.deadTracing | _ = case eq of λ ()
...   | Life.bodyExited | _ = case eq of λ ()
...   | Life.finalizing | _ = case eq of λ ()
...   | Life.normalClosing | _ = case eq of λ ()
...   | Life.normalClosed | _ = case eq of λ ()
...   | Life.normalBodyExited | _ = case eq of λ ()
...   | Life.syncClosing _ | _ = case eq of λ ()
...   | Life.syncClosed _ | _ = case eq of λ ()
...   | Life.peerRethrow _ | _ = case eq of λ ()
...   | Life.nodeDelivery _ | _ = case eq of λ ()
...   | Life.nodeRethrow _ | _ = case eq of λ ()
...   | Life.peerBodyExited _ | _ = case eq of λ ()
...   | Life.nodeBodyExited _ | _ = case eq of λ ()
life-quiet w Life.nodeExceptionDelivered rt ig s q eq with lookup w rt
... | nothing = case eq of λ ()
... | just f with Life.phase f
...   | Life.nodeDelivery err = case just-injective eq of λ { refl → q }
...   | Life.monitoring = case eq of λ ()
...   | Life.poolClosing = case eq of λ ()
...   | Life.poolClosed = case eq of λ ()
...   | Life.deadTracing = case eq of λ ()
...   | Life.bodyExited = case eq of λ ()
...   | Life.finalizing = case eq of λ ()
...   | Life.normalClosing = case eq of λ ()
...   | Life.normalClosed = case eq of λ ()
...   | Life.normalBodyExited = case eq of λ ()
...   | Life.syncClosing _ = case eq of λ ()
...   | Life.syncClosed _ = case eq of λ ()
...   | Life.classifying _ = case eq of λ ()
...   | Life.peerRethrow _ = case eq of λ ()
...   | Life.nodeRethrow _ = case eq of λ ()
...   | Life.peerBodyExited _ = case eq of λ ()
...   | Life.nodeBodyExited _ = case eq of λ ()
life-quiet w Life.rethrow rt ig s q eq with lookup w rt
... | nothing = case eq of λ ()
... | just f with Life.phase f
...   | Life.peerRethrow err = case just-injective eq of λ { refl → q }
...   | Life.nodeRethrow err = case just-injective eq of λ { refl → q }
...   | Life.monitoring = case eq of λ ()
...   | Life.poolClosing = case eq of λ ()
...   | Life.poolClosed = case eq of λ ()
...   | Life.deadTracing = case eq of λ ()
...   | Life.bodyExited = case eq of λ ()
...   | Life.finalizing = case eq of λ ()
...   | Life.normalClosing = case eq of λ ()
...   | Life.normalClosed = case eq of λ ()
...   | Life.normalBodyExited = case eq of λ ()
...   | Life.syncClosing _ = case eq of λ ()
...   | Life.syncClosed _ = case eq of λ ()
...   | Life.classifying _ = case eq of λ ()
...   | Life.nodeDelivery _ = case eq of λ ()
...   | Life.peerBodyExited _ = case eq of λ ()
...   | Life.nodeBodyExited _ = case eq of λ ()

-- No release or remote call begins from an exited governor with none pending.
release-none : ∀ a ig s → IG.continuation ig ≡ IG.exited → Release.step a nothing ig s ≡ nothing
release-none Release.enter (IG.runtimeState p n c e) s refl = refl
release-none Release.transact ig s cont = refl
release-none Release.readCounters ig s cont = refl
release-none Release.requestCancellation ig s cont = refl
release-none Release.checkAssertion ig s cont = refl
release-none Release.returnToIG ig s cont = refl
release-none (Release.cancellationDelivered _) ig s cont = refl
remote-none : ∀ L G a ig s → IG.continuation ig ≡ IG.exited → Remote.step L G a nothing ig s ≡ nothing
remote-none L G Remote.enter (IG.runtimeState p n c e) s refl = refl
remote-none L G Remote.transact ig s cont = refl
remote-none L G Remote.checkAssertion ig s cont = refl
remote-none L G Remote.readCounters ig s cont = refl
remote-none L G Remote.returnToIG ig s cont = refl
remote-none L G Remote.requestPruneCancellation ig s cont = refl
remote-none L G (Remote.transactPruning _ _) ig s cont = refl
remote-none L G (Remote.pruneCancellationDelivered _) ig s cont = refl

-- The governor's control state plus both pending CM calls.
QuietCore : Machine.Configuration → Set
QuietCore c = Quiet (Machine.inboundGovernor c) × Machine.inboundRelease c ≡ nothing × Machine.remoteCall c ≡ nothing

absurd-just : ∀ {A : Set} {x : A} {B : Set} → nothing ≡ just x → B
absurd-just ()

machine-quiet : ∀ a c {c′} → Machine.advance a c ≡ just c′ → QuietCore c → QuietCore c′
machine-quiet (Machine.handlerStep w a) c eq (q , rel , rem)
  with Life.step w a (Machine.handlerLifecycles c) (Machine.inboundGovernor c) (Machine.world c) in stepped
... | nothing = case eq of λ ()
... | just (rt , ig) = case just-injective eq of λ { refl → life-quiet w a (Machine.handlerLifecycles c) (Machine.inboundGovernor c) (Machine.world c) q stepped , rel , rem }
machine-quiet (Machine.remoteStep a) c eq (q , rel , rem) with Life.allowRemote a (Machine.handlerLifecycles c) (Machine.world c)
... | false = case eq of λ ()
... | true with Remote.step (Machine.promotionHardLimit c) (Machine.pruningGeneration c) a (Machine.remoteCall c) (Machine.inboundGovernor c) (Machine.world c) in stepped
...   | nothing = case eq of λ ()
...   | just p = absurd-just (trans (sym (remote-none (Machine.promotionHardLimit c) (Machine.pruningGeneration c) a (Machine.inboundGovernor c) (Machine.world c) (proj₁ q)))
    (trans (cong (λ x → Remote.step (Machine.promotionHardLimit c) (Machine.pruningGeneration c) a x (Machine.inboundGovernor c) (Machine.world c)) (sym rem)) stepped))
machine-quiet (Machine.releaseStep a) c eq (q , rel , rem) with Life.allowRelease a (Machine.handlerLifecycles c) (Machine.world c)
... | false = case eq of λ ()
... | true with Release.step a (Machine.inboundRelease c) (Machine.inboundGovernor c) (Machine.world c) in stepped
...   | nothing = case eq of λ ()
...   | just p = absurd-just (trans (sym (release-none a (Machine.inboundGovernor c) (Machine.world c) (proj₁ q)))
    (trans (cong (λ x → Release.step a x (Machine.inboundGovernor c) (Machine.world c)) (sym rel)) stepped))
machine-quiet (Machine.igStep a) c eq (q , rel , rem) with Life.allowIG a (Machine.handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (Machine.responder c) a (Machine.inboundGovernor c) (S.inboundInfo (Machine.world c)) in stepped
...   | nothing = case eq of λ ()
...   | just (ig , queue) = case just-injective eq of λ { refl → quiet-step (Machine.responder c) a (Machine.inboundGovernor c) (S.inboundInfo (Machine.world c)) (proj₁ q) (proj₂ q) stepped , rel , rem }
machine-quiet (Machine.admissionStep w a) c eq (q , rel , rem) with Admission.stepPrefix w a (Machine.world c)
... | nothing = case eq of λ ()
... | just s = case just-injective eq of λ { refl → q , rel , rem }
machine-quiet (Machine.handshakeStep w a) c eq (q , rel , rem) with Handshake.stepHandshake (Machine.responder c) w a (Machine.world c)
... | nothing = case eq of λ ()
... | just s = case just-injective eq of λ { refl → q , rel , rem }
machine-quiet (Machine.cleanupStep w a) c eq (q , rel , rem) with Cleanup.stepCleanup w a (Machine.world c)
... | nothing = case eq of λ ()
... | just s = case just-injective eq of λ { refl → q , rel , rem }
machine-quiet (Machine.handlerExit w) c eq (q , rel , rem) with Life.mayExit w (Machine.handlerLifecycles c)
... | false = case eq of λ ()
... | true with Cleanup.beginCleanupBoundary w (Machine.world c)
...   | nothing = case eq of λ ()
...   | just s = case just-injective eq of λ { refl → q , rel , rem }
machine-quiet (Machine.handlerPublication w result outcome) c eq (q , rel , rem)
  with any (λ v → does (v ≟ w)) (Machine.publicationFaults c)
... | true = case eq of λ ()
... | false with Handshake.publishBoundary w result (Machine.world c) | outcome
...   | nothing | _ = case eq of λ ()
...   | just (Handshake.published s) | Machine.resultWritten = case just-injective eq of λ { refl → q , rel , rem }
...   | just Handshake.writerBlocked | Machine.duplicateWrite = case just-injective eq of λ { refl → q , rel , rem }
...   | just (Handshake.published s) | Machine.duplicateWrite = case eq of λ ()
...   | just Handshake.writerBlocked | Machine.resultWritten = case eq of λ ()

-- Outbound caller steps change only the shared world and lifecycles.
outbound-quiet : ∀ a c {c′} → O.advance a c ≡ just c′ → QuietCore (O.core c) → QuietCore (O.core c′)
outbound-quiet (O.inbound a) c eq q with Machine.advance a (O.core c) in stepped
... | nothing = case eq of λ ()
... | just c₁ = case just-injective eq of λ { refl → machine-quiet a (O.core c) stepped q }
outbound-quiet (O.beginAcquire w req) c eq q with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | nothing | nothing = case just-injective eq of λ { refl → q }
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
outbound-quiet (O.beginRelease w key) c eq q with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | nothing | nothing = case just-injective eq of λ { refl → q }
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
outbound-quiet (O.acquire w A.returnResult) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.pc f
...   | A.complete result = case just-injective eq of λ { refl → q }
...   | A.selecting = case eq of λ ()
...   | (A.count _) = case eq of λ ()
...   | (A.allocatePromise _) = case eq of λ ()
...   | (A.openSocket _ _) = case eq of λ ()
...   | (A.configureSocket _ _) = case eq of λ ()
...   | (A.bindSocket _ _) = case eq of λ ()
...   | (A.connectSocket _ _) = case eq of λ ()
...   | (A.localAddress _ _) = case eq of λ ()
...   | (A.updateAddress _ _ _) = case eq of λ ()
...   | (A.forkHandler _ _ _) = case eq of λ ()
...   | (A.connectedCommit _ _ _) = case eq of λ ()
...   | (A.awaitResult _ _ _) = case eq of λ ()
...   | (A.commitResult _ _ _) = case eq of λ ()
...   | (A.waitingInbound _ _) = case eq of λ ()
...   | (A.closeError _ _) = case eq of λ ()
...   | (A.removeError _ _) = case eq of λ ()
outbound-quiet (O.acquire w (A.select x)) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) (A.select x) f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.readCounters) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.readCounters f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.newPromise) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.newPromise f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.openOK) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.openOK f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.configureOK) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.configureOK f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.bindOK) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.bindOK f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.connectOK) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.connectOK f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w (A.gotLocal x)) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) (A.gotLocal x) f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.updateLocalAddress) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.updateLocalAddress f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.forkOK) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.forkOK f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.commitConnected) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.commitConnected f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.readResult) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.readResult f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.commitHandshake) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.commitHandshake f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w (A.failIO x)) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) (A.failIO x) f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w (A.closeFailed x)) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) (A.closeFailed x) f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.closeOK) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.closeOK f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.removeReservation) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.removeReservation f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.acquire w A.waitNegotiated) c eq q with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (Machine.responder (O.core c)) A.waitNegotiated f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.release w R.returnResult) c eq q with lookup w (O.releasing c)
... | nothing = case eq of λ ()
... | just f with R.pc f
...   | R.complete result = case just-injective eq of λ { refl → q }
...   | R.transaction = case eq of λ ()
...   | (R.check _ _) = case eq of λ ()
...   | (R.count _) = case eq of λ ()
...   | (R.armTimer _ _) = case eq of λ ()
...   | (R.waitIdle _ _) = case eq of λ ()
...   | (R.timeoutWrite _ _) = case eq of λ ()
...   | (R.cancel _ _) = case eq of λ ()
...   | (R.delivering _ _) = case eq of λ ()
...   | (R.prune _ _) = case eq of λ ()
outbound-quiet (O.release w R.transactionStep) c eq q with lookup w (O.releasing c) | O.canDeliver R.transactionStep c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (Machine.promotionHardLimit (O.core c)) R.transactionStep f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.release w R.checkAssertion) c eq q with lookup w (O.releasing c) | O.canDeliver R.checkAssertion c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (Machine.promotionHardLimit (O.core c)) R.checkAssertion f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.release w R.readCounters) c eq q with lookup w (O.releasing c) | O.canDeliver R.readCounters c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (Machine.promotionHardLimit (O.core c)) R.readCounters f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.release w R.registerTimer) c eq q with lookup w (O.releasing c) | O.canDeliver R.registerTimer c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (Machine.promotionHardLimit (O.core c)) R.registerTimer f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.release w R.expireTimer) c eq q with lookup w (O.releasing c) | O.canDeliver R.expireTimer c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (Machine.promotionHardLimit (O.core c)) R.expireTimer f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.release w R.selectWakeup) c eq q with lookup w (O.releasing c) | O.canDeliver R.selectWakeup c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (Machine.promotionHardLimit (O.core c)) R.selectWakeup f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.release w R.commitTimeout) c eq q with lookup w (O.releasing c) | O.canDeliver R.commitTimeout c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (Machine.promotionHardLimit (O.core c)) R.commitTimeout f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.release w R.requestCancellation) c eq q with lookup w (O.releasing c) | O.canDeliver R.requestCancellation c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (Machine.promotionHardLimit (O.core c)) R.requestCancellation f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.release w (R.transactionPruning x)) c eq q with lookup w (O.releasing c) | O.canDeliver (R.transactionPruning x) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (Machine.promotionHardLimit (O.core c)) (R.transactionPruning x) f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-quiet (O.release w (R.cancellationDelivered x)) c eq q with lookup w (O.releasing c) | O.canDeliver (R.cancellationDelivered x) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (Machine.promotionHardLimit (O.core c)) (R.cancellationDelivered x) f (Machine.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → q }
outbound-exec-quiet : ∀ {c as c′} → O.Executes c as c′ → QuietCore (O.core c) → QuietCore (O.core c′)
outbound-exec-quiet O.done q = q
outbound-exec-quiet (O.next {c = c} {a = a} eq rest) q = outbound-exec-quiet rest (outbound-quiet a c eq q)

-- A governor write that keeps the control state (continuation and activity).
SameControl : IG.Runtime → IG.Runtime → Set
SameControl ig ig′ = IG.continuation ig′ ≡ IG.continuation ig × IG.active (IG.execution ig′) ≡ IG.active (IG.execution ig)
same-control-quiet : ∀ {ig ig′} → SameControl ig ig′ → Quiet ig → Quiet ig′
same-control-quiet (cont , act) (exitedNow , inactive) = trans cont exitedNow , trans act inactive

-- Peer actions return the governor unchanged or with one mux row replaced.
peer-control : ∀ a p ig s {p′ ig′} → Peer.step a p ig s ≡ just (p′ , ig′) → SameControl ig ig′
peer-control Peer.activate p ig s eq with Peer.status p
... | Peer.peerWarm = case just-injective eq of λ { refl → refl , refl }
... | Peer.peerCold = case eq of λ ()
... | Peer.peerCooling = case eq of λ ()
... | Peer.peerHot = case eq of λ ()
peer-control Peer.deactivate p ig s eq with Peer.status p
... | Peer.peerHot = case just-injective eq of λ { refl → refl , refl }
... | Peer.peerWarm = case just-injective eq of λ { refl → refl , refl }
... | Peer.peerCold = case eq of λ ()
... | Peer.peerCooling = case eq of λ ()
peer-control Peer.close p ig s eq = case just-injective eq of λ { refl → refl , refl }
peer-control (Peer.startProtocol t n) p ig s eq with lookup (Peer.muxRef p) (IG.muxes (IG.execution ig))
... | nothing = case eq of λ ()
... | just m with M.status m
...   | M.ready with Peer.startRun t n (Peer.runs p)
...     | nothing = case eq of λ ()
...     | just rs = case just-injective eq of λ { refl → refl , refl }
peer-control (Peer.startProtocol t n) p ig s eq | just m | M.stopping = case eq of λ ()
peer-control (Peer.startProtocol t n) p ig s eq | just m | M.stopped = case eq of λ ()
peer-control (Peer.startProtocol t n) p ig s eq | just m | M.failed _ = case eq of λ ()
peer-control (Peer.publishProtocols t) p ig s eq with Peer.started t (Peer.runs p)
... | false = case eq of λ ()
... | true = case just-injective eq of λ { refl → refl , refl }
peer-control (Peer.protocolResult n result) p ig s eq with Peer.finishRun n result (Peer.runs p)
... | nothing = case eq of λ ()
... | just rs = case just-injective eq of λ { refl → refl , refl }
peer-control Peer.markWarm p ig s eq = case just-injective eq of λ { refl → refl , refl }
peer-control Peer.forkMonitor p ig s eq with Peer.monitorStarted p
... | true = case eq of λ ()
... | false = case just-injective eq of λ { refl → refl , refl }
peer-control (Peer.markPromoted time) p ig s eq = case just-injective eq of λ { refl → refl , refl }
peer-control Peer.finishDeactivate p ig s eq with Peer.all IGTypes.hot (Peer.runs p)
... | nothing = case eq of λ ()
... | just (IGTypes.errored _) = case just-injective eq of λ { refl → refl , refl }
... | just IGTypes.clean with Peer.status p
...   | Peer.peerHot = case just-injective eq of λ { refl → refl , refl }
...   | Peer.peerCold = case just-injective eq of λ { refl → refl , refl }
...   | Peer.peerCooling = case just-injective eq of λ { refl → refl , refl }
...   | Peer.peerWarm = case just-injective eq of λ { refl → refl , refl }
peer-control Peer.timeoutDeactivate p ig s eq with lookup (Peer.muxRef p) (IG.muxes (IG.execution ig))
... | nothing = case eq of λ ()
... | just m = case just-injective eq of λ { refl → refl , refl }
peer-control Peer.timeoutClose p ig s eq with lookup (Peer.muxRef p) (IG.muxes (IG.execution ig))
... | nothing = case eq of λ ()
... | just m = case just-injective eq of λ { refl → refl , refl }
peer-control Peer.monitorCooling p ig s eq with Peer.status p | Peer.demoted (Peer.key p) s
... | Peer.peerCooling | true = case just-injective eq of λ { refl → refl , refl }
... | Peer.peerCold | _ = case just-injective eq of λ { refl → refl , refl }
... | Peer.peerCooling | false = case eq of λ ()
... | Peer.peerWarm | _ = case eq of λ ()
... | Peer.peerHot | _ = case eq of λ ()
peer-control Peer.monitorError p ig s eq = case just-injective eq of λ { refl → refl , refl }

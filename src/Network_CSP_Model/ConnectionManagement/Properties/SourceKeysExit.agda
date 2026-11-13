{-# OPTIONS --guardedness #-}

-- Caller bookkeeping through handler exit: only an inherited group action can
-- have a root; own plans run inbound steps or a release receipt, which keeps
-- the release frame key.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.SourceKeysExit (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Rules.HandshakeContinuation as HS
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.OutboundRelease as Release
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.MuxHandlerExit as Exit
open import ConnectionManagement.Properties.OutboundKeys
import ConnectionManagement.Properties.SourceKeysGroup as GroupKeys
private
  module W = Exit isBearerClosed
  module G = W.G
  module U = W.U
  module P = W.P
  module Pool = W.Pool
  module Lower = GroupKeys isBearerClosed

rootW : W.Action → Maybe O.Action
rootW (W.run a) = Lower.rootG a
rootW _ = nothing
planRoot : W.Plan → Maybe O.Action
planRoot (W.inherited a) = Lower.rootG a
planRoot (W.machine x fs) = keyRoot x
planRoot _ = nothing
Same : W.State → W.State → Set
Same s s′ = KeySame (W.source s) (W.source s′)

control-keys : ∀ a s {s′} → W.control a s ≡ just s′ → Same s s′
control-keys a s eq with Close.step (Shared.cm (W.shared s)) (λ w → W.resultReady w s) a (W.shutdown s)
... | nothing = case eq of λ ()
... | just next = case just-injective eq of λ { refl → same-refl _ }
enact-keys : ∀ plan s {s′} → W.enact plan s ≡ just s′ → Effect (planRoot plan) (W.source s) (W.source s′)
enact-keys (W.local fs) s eq = case just-injective eq of λ { refl → same-refl _ }
enact-keys (W.machine x fs) s eq with O.advance x (W.source s) in advanced
... | nothing = case eq of λ ()
... | just c = case just-injective eq of λ { refl → advance-effect x (W.source s) advanced }
enact-keys (W.inherited a) s eq with G.step a (W.base s) in stepped
... | nothing = case eq of λ ()
... | just g = case just-injective eq of λ { refl → Lower.step-keysG a (W.base s) stepped }
enact-keys (W.coordinator a) s eq = control-keys a s eq
enact-keys (W.handshakeDelivery w window err) s eq with G.step (W.handshakeAction w window err) (W.base s) in stepped
... | nothing = case eq of λ ()
... | just g = same-trans (Lower.step-keysG (W.handshakeAction w window err) (W.base s) stepped)
  (control-keys Close.acknowledgeDelivery (record s { base = g }) eq)
enact-keys (W.muxDelivery w err) s eq with G.step (G.abortOwner w err) (W.base s) in stepped
... | nothing = case eq of λ ()
... | just g = same-trans (Lower.step-keysG (G.abortOwner w err) (W.base s) stepped)
  (control-keys Close.acknowledgeDelivery (record s { base = g }) eq)
enact-keys (W.timeWaitDelivery w err) s eq with O.advance (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s) in advanced
... | nothing = case eq of λ ()
... | just c = same-trans (nonkey (O.inbound (Machine.cleanupStep w (Cleanup.interruptTimeWait err))) (W.source s) refl advanced)
  (control-keys Close.acknowledgeDelivery (record (W.setSource c s) { exits = W.noteCleanup w (Cleanup.interruptTimeWait err) s }) eq)
enact-keys (W.releaseDelivery caller target err) s eq with G.step (G.abortOwner target err) (W.base s) in stepped
... | nothing = case eq of λ ()
... | just g with O.advance (O.release caller (Release.cancellationDelivered target)) (G.source g) in advanced
...   | nothing = case eq of λ ()
...   | just c = case just-injective eq of λ { refl → same-trans (Lower.step-keysG (G.abortOwner target err) (W.base s) stepped)
  (nonkey (O.release caller (Release.cancellationDelivered target)) (G.source g) refl advanced) }
enact-keys (W.releaseTimeWaitDelivery caller target err) s eq with O.advance (O.inbound (Machine.cleanupStep target (Cleanup.interruptTimeWait err))) (W.source s) in first
... | nothing = case eq of λ ()
... | just c with O.advance (O.release caller (Release.cancellationDelivered target)) c in second
...   | nothing = case eq of λ ()
...   | just c′ = case just-injective eq of λ { refl → same-trans
  (nonkey (O.inbound (Machine.cleanupStep target (Cleanup.interruptTimeWait err))) (W.source s) refl first)
  (nonkey (O.release caller (Release.cancellationDelivered target)) c refl second) }

-- Only an inherited group action is chosen with a root.
choose-root : ∀ a s {plan} → W.choose a s ≡ just plan → planRoot plan ≡ rootW a
choose-root (W.run a) s eq with W.delegateAllowed a
... | true = case just-injective eq of λ { refl → refl }
... | false = case eq of λ ()
choose-root (W.finishHandshake w) s eq with lookup w (W.exits s) in absent | lookup w (U.frames (P.base (G.protocolState (W.base s)))) in found
... | nothing | just f with U.progress f
...   | U.handshakePending (HS.exited result HS.normal) = case just-injective eq of λ { refl → refl }
...   | U.handshakePending (HS.exited result (HS.sync err)) = case just-injective eq of λ { refl → refl }
...   | U.handshakePending (HS.exited result (HS.async err)) = case just-injective eq of λ { refl → refl }
choose-root (W.finishHandshake w) s eq | nothing | just f | U.handshakePending (HS.returned result) = case eq of λ ()
choose-root (W.finishHandshake w) s eq | nothing | just f | U.handshakePending (HS.published result) = case eq of λ ()
choose-root (W.finishHandshake w) s eq | nothing | just f | U.handshakePending HS.sleeping = case eq of λ ()
choose-root (W.finishHandshake w) s eq | nothing | just f | U.returnedSuccess = case eq of λ ()
choose-root (W.finishHandshake w) s eq | nothing | just f | U.handleAllocated hid mid = case eq of λ ()
choose-root (W.finishHandshake w) s eq | nothing | just f | U.promisePublished hid mid = case eq of λ ()
choose-root (W.finishHandshake w) s eq | nothing | nothing = case eq of λ ()
choose-root (W.finishHandshake w) s eq | just old | _ = case eq of λ ()
choose-root (W.beginExit w) s eq with lookup w (W.exits s) | lookup w (U.frames (P.base (G.protocolState (W.base s)))) |
  G.phase (G.frameAt w (W.base s)) | Pool.phase (W.poolAt w s)
... | nothing | just f | G.scopeDone outcome | Pool.closedPool with lookup w (Shared.handlers (W.shared s))
...   | just h with W.sameStart (U.captured f) h ∧ W.countersClear f s
...     | true = case just-injective eq of λ { refl → refl }
...     | false = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just f | G.scopeDone outcome | Pool.closedPool | nothing = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | nothing | _ | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.idle | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.shutdownSelected | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.stoppingTraced | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.stoppingWritten | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.groupClosing | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.draining | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.drainReady | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.stoppedTrace | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.stoppedTracing | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.monitorReturnedNormal | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.ownerAborting _ | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.wholeClosing _ | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.wholeClosed _ | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.scopeDone _ | Pool.openPool = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.scopeDone _ | Pool.closing = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.scopeDone _ | Pool.cancelPending _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.scopeDone _ | Pool.joinPending _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.asyncFailureWritten _ | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | nothing | just _ | G.asyncDeadTracing _ | _ = case eq of λ ()
choose-root (W.beginExit w) s eq | just _ | _ | _ | _ = case eq of λ ()
choose-root (W.observeBufferReturn w) s eq with lookup w (W.exits s)
... | just f with W.phase f
...   | W.bufferScope o = case just-injective eq of λ { refl → refl }
choose-root (W.observeBufferReturn w) s eq | just f | W.classifying _ = case eq of λ ()
choose-root (W.observeBufferReturn w) s eq | just f | W.errorTracing _ _ = case eq of λ ()
choose-root (W.observeBufferReturn w) s eq | just f | W.peerRethrow _ = case eq of λ ()
choose-root (W.observeBufferReturn w) s eq | just f | W.nodeDelivery _ = case eq of λ ()
choose-root (W.observeBufferReturn w) s eq | just f | W.nodeRethrow _ = case eq of λ ()
choose-root (W.observeBufferReturn w) s eq | just f | W.bodyExited _ = case eq of λ ()
choose-root (W.observeBufferReturn w) s eq | just f | W.finalizing _ = case eq of λ ()
choose-root (W.observeBufferReturn w) s eq | just f | W.cleanupComplete _ _ = case eq of λ ()
choose-root (W.observeBufferReturn w) s eq | just f | W.resultAvailable _ _ = case eq of λ ()
choose-root (W.observeBufferReturn w) s eq | nothing = case eq of λ ()
choose-root (W.observeBufferException w G.normalExit) s ()
choose-root (W.observeBufferException w (G.failedExit err)) s eq with lookup w (W.exits s)
... | just f with W.phase f
...   | W.bufferScope o = case just-injective eq of λ { refl → refl }
choose-root (W.observeBufferException w (G.failedExit err)) s eq | just f | W.classifying _ = case eq of λ ()
choose-root (W.observeBufferException w (G.failedExit err)) s eq | just f | W.errorTracing _ _ = case eq of λ ()
choose-root (W.observeBufferException w (G.failedExit err)) s eq | just f | W.peerRethrow _ = case eq of λ ()
choose-root (W.observeBufferException w (G.failedExit err)) s eq | just f | W.nodeDelivery _ = case eq of λ ()
choose-root (W.observeBufferException w (G.failedExit err)) s eq | just f | W.nodeRethrow _ = case eq of λ ()
choose-root (W.observeBufferException w (G.failedExit err)) s eq | just f | W.bodyExited _ = case eq of λ ()
choose-root (W.observeBufferException w (G.failedExit err)) s eq | just f | W.finalizing _ = case eq of λ ()
choose-root (W.observeBufferException w (G.failedExit err)) s eq | just f | W.cleanupComplete _ _ = case eq of λ ()
choose-root (W.observeBufferException w (G.failedExit err)) s eq | just f | W.resultAvailable _ _ = case eq of λ ()
choose-root (W.observeBufferException w (G.failedExit err)) s eq | nothing = case eq of λ ()
choose-root (W.observeBufferException w (G.asyncExit err)) s eq with lookup w (W.exits s)
... | just f with W.phase f
...   | W.bufferScope o = case just-injective eq of λ { refl → refl }
choose-root (W.observeBufferException w (G.asyncExit err)) s eq | just f | W.classifying _ = case eq of λ ()
choose-root (W.observeBufferException w (G.asyncExit err)) s eq | just f | W.errorTracing _ _ = case eq of λ ()
choose-root (W.observeBufferException w (G.asyncExit err)) s eq | just f | W.peerRethrow _ = case eq of λ ()
choose-root (W.observeBufferException w (G.asyncExit err)) s eq | just f | W.nodeDelivery _ = case eq of λ ()
choose-root (W.observeBufferException w (G.asyncExit err)) s eq | just f | W.nodeRethrow _ = case eq of λ ()
choose-root (W.observeBufferException w (G.asyncExit err)) s eq | just f | W.bodyExited _ = case eq of λ ()
choose-root (W.observeBufferException w (G.asyncExit err)) s eq | just f | W.finalizing _ = case eq of λ ()
choose-root (W.observeBufferException w (G.asyncExit err)) s eq | just f | W.cleanupComplete _ _ = case eq of λ ()
choose-root (W.observeBufferException w (G.asyncExit err)) s eq | just f | W.resultAvailable _ _ = case eq of λ ()
choose-root (W.observeBufferException w (G.asyncExit err)) s eq | nothing = case eq of λ ()
choose-root (W.choosePolicy w policy) s eq with lookup w (W.exits s)
... | just f with W.phase f
...   | W.classifying e = case just-injective eq of λ { refl → refl }
choose-root (W.choosePolicy w policy) s eq | just f | W.bufferScope _ = case eq of λ ()
choose-root (W.choosePolicy w policy) s eq | just f | W.errorTracing _ _ = case eq of λ ()
choose-root (W.choosePolicy w policy) s eq | just f | W.peerRethrow _ = case eq of λ ()
choose-root (W.choosePolicy w policy) s eq | just f | W.nodeDelivery _ = case eq of λ ()
choose-root (W.choosePolicy w policy) s eq | just f | W.nodeRethrow _ = case eq of λ ()
choose-root (W.choosePolicy w policy) s eq | just f | W.bodyExited _ = case eq of λ ()
choose-root (W.choosePolicy w policy) s eq | just f | W.finalizing _ = case eq of λ ()
choose-root (W.choosePolicy w policy) s eq | just f | W.cleanupComplete _ _ = case eq of λ ()
choose-root (W.choosePolicy w policy) s eq | just f | W.resultAvailable _ _ = case eq of λ ()
choose-root (W.choosePolicy w policy) s eq | nothing = case eq of λ ()
choose-root (W.observeErrorTrace w) s eq with lookup w (W.exits s)
... | just f with W.phase f
...   | W.errorTracing e Life.shutdownPeer = case just-injective eq of λ { refl → refl }
...   | W.errorTracing e Life.shutdownNode = case just-injective eq of λ { refl → refl }
choose-root (W.observeErrorTrace w) s eq | just f | W.bufferScope _ = case eq of λ ()
choose-root (W.observeErrorTrace w) s eq | just f | W.classifying _ = case eq of λ ()
choose-root (W.observeErrorTrace w) s eq | just f | W.peerRethrow _ = case eq of λ ()
choose-root (W.observeErrorTrace w) s eq | just f | W.nodeDelivery _ = case eq of λ ()
choose-root (W.observeErrorTrace w) s eq | just f | W.nodeRethrow _ = case eq of λ ()
choose-root (W.observeErrorTrace w) s eq | just f | W.bodyExited _ = case eq of λ ()
choose-root (W.observeErrorTrace w) s eq | just f | W.finalizing _ = case eq of λ ()
choose-root (W.observeErrorTrace w) s eq | just f | W.cleanupComplete _ _ = case eq of λ ()
choose-root (W.observeErrorTrace w) s eq | just f | W.resultAvailable _ _ = case eq of λ ()
choose-root (W.observeErrorTrace w) s eq | nothing = case eq of λ ()
choose-root (W.observeNodeDelivery w) s eq with lookup w (W.exits s)
... | just f with W.phase f
...   | W.nodeDelivery e = case just-injective eq of λ { refl → refl }
choose-root (W.observeNodeDelivery w) s eq | just f | W.bufferScope _ = case eq of λ ()
choose-root (W.observeNodeDelivery w) s eq | just f | W.classifying _ = case eq of λ ()
choose-root (W.observeNodeDelivery w) s eq | just f | W.errorTracing _ _ = case eq of λ ()
choose-root (W.observeNodeDelivery w) s eq | just f | W.peerRethrow _ = case eq of λ ()
choose-root (W.observeNodeDelivery w) s eq | just f | W.nodeRethrow _ = case eq of λ ()
choose-root (W.observeNodeDelivery w) s eq | just f | W.bodyExited _ = case eq of λ ()
choose-root (W.observeNodeDelivery w) s eq | just f | W.finalizing _ = case eq of λ ()
choose-root (W.observeNodeDelivery w) s eq | just f | W.cleanupComplete _ _ = case eq of λ ()
choose-root (W.observeNodeDelivery w) s eq | just f | W.resultAvailable _ _ = case eq of λ ()
choose-root (W.observeNodeDelivery w) s eq | nothing = case eq of λ ()
choose-root (W.rethrow w) s eq with lookup w (W.exits s)
... | just f with W.phase f
...   | W.peerRethrow e = case just-injective eq of λ { refl → refl }
...   | W.nodeRethrow e = case just-injective eq of λ { refl → refl }
choose-root (W.rethrow w) s eq | just f | W.bufferScope _ = case eq of λ ()
choose-root (W.rethrow w) s eq | just f | W.classifying _ = case eq of λ ()
choose-root (W.rethrow w) s eq | just f | W.errorTracing _ _ = case eq of λ ()
choose-root (W.rethrow w) s eq | just f | W.nodeDelivery _ = case eq of λ ()
choose-root (W.rethrow w) s eq | just f | W.bodyExited _ = case eq of λ ()
choose-root (W.rethrow w) s eq | just f | W.finalizing _ = case eq of λ ()
choose-root (W.rethrow w) s eq | just f | W.cleanupComplete _ _ = case eq of λ ()
choose-root (W.rethrow w) s eq | just f | W.resultAvailable _ _ = case eq of λ ()
choose-root (W.rethrow w) s eq | nothing = case eq of λ ()
choose-root (W.enterFinalizer w) s eq with lookup w (W.exits s)
... | just f with W.phase f | W.currentCapture w f s
...   | W.bodyExited r | true = case just-injective eq of λ { refl → refl }
choose-root (W.enterFinalizer w) s eq | just f | W.bufferScope _ | _ = case eq of λ ()
choose-root (W.enterFinalizer w) s eq | just f | W.classifying _ | _ = case eq of λ ()
choose-root (W.enterFinalizer w) s eq | just f | W.errorTracing _ _ | _ = case eq of λ ()
choose-root (W.enterFinalizer w) s eq | just f | W.peerRethrow _ | _ = case eq of λ ()
choose-root (W.enterFinalizer w) s eq | just f | W.nodeDelivery _ | _ = case eq of λ ()
choose-root (W.enterFinalizer w) s eq | just f | W.nodeRethrow _ | _ = case eq of λ ()
choose-root (W.enterFinalizer w) s eq | just f | W.bodyExited _ | false = case eq of λ ()
choose-root (W.enterFinalizer w) s eq | just f | W.finalizing _ | _ = case eq of λ ()
choose-root (W.enterFinalizer w) s eq | just f | W.cleanupComplete _ _ | _ = case eq of λ ()
choose-root (W.enterFinalizer w) s eq | just f | W.resultAvailable _ _ | _ = case eq of λ ()
choose-root (W.enterFinalizer w) s eq | nothing = case eq of λ ()
choose-root (W.cleanup w action) s eq with lookup w (W.exits s)
... | just f with W.phase f | W.currentCapture w f s
...   | W.finalizing r | true = case just-injective eq of λ { refl → refl }
choose-root (W.cleanup w action) s eq | just f | W.bufferScope _ | _ = case eq of λ ()
choose-root (W.cleanup w action) s eq | just f | W.classifying _ | _ = case eq of λ ()
choose-root (W.cleanup w action) s eq | just f | W.errorTracing _ _ | _ = case eq of λ ()
choose-root (W.cleanup w action) s eq | just f | W.peerRethrow _ | _ = case eq of λ ()
choose-root (W.cleanup w action) s eq | just f | W.nodeDelivery _ | _ = case eq of λ ()
choose-root (W.cleanup w action) s eq | just f | W.nodeRethrow _ | _ = case eq of λ ()
choose-root (W.cleanup w action) s eq | just f | W.bodyExited _ | _ = case eq of λ ()
choose-root (W.cleanup w action) s eq | just f | W.finalizing _ | false = case eq of λ ()
choose-root (W.cleanup w action) s eq | just f | W.cleanupComplete _ _ | _ = case eq of λ ()
choose-root (W.cleanup w action) s eq | just f | W.resultAvailable _ _ | _ = case eq of λ ()
choose-root (W.cleanup w action) s eq | nothing = case eq of λ ()
choose-root (W.finishCleanup w) s eq with lookup w (W.exits s) | lookup w (Shared.cleanups (W.shared s))
... | just f | just (Shared.cleanupDone outcome) with W.phase f
...   | W.finalizing result with W.effectiveResult result outcome (W.cleanupException f)
...     | just _ = case just-injective eq of λ { refl → refl }
...     | nothing = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just f | just (Shared.cleanupDone outcome) | W.bufferScope _ = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just f | just (Shared.cleanupDone outcome) | W.classifying _ = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just f | just (Shared.cleanupDone outcome) | W.errorTracing _ _ = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just f | just (Shared.cleanupDone outcome) | W.peerRethrow _ = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just f | just (Shared.cleanupDone outcome) | W.nodeDelivery _ = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just f | just (Shared.cleanupDone outcome) | W.nodeRethrow _ = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just f | just (Shared.cleanupDone outcome) | W.bodyExited _ = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just f | just (Shared.cleanupDone outcome) | W.cleanupComplete _ _ = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just f | just (Shared.cleanupDone outcome) | W.resultAvailable _ _ = case eq of λ ()
choose-root (W.finishCleanup w) s eq | nothing | _ = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just _ | nothing = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just _ | just Shared.cleanupAcquire = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just _ | just (Shared.cleanupSelect _) = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just _ | just (Shared.cleanupClose _ _ _) = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just _ | just (Shared.cleanupPublish _ _ _) = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just _ | just (Shared.cleanupRestore _ _) = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just _ | just (Shared.cleanupWaiting _) = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just _ | just (Shared.cleanupFinalize _ _) = case eq of λ ()
choose-root (W.finishCleanup w) s eq | just _ | just (Shared.cleanupCount _) = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq with lookup w (W.exits s) | lookup w (Shared.cleanups (W.shared s))
... | just f | just (Shared.cleanupDone outcome) with W.phase f
...   | W.cleanupComplete result observed with W.sameCleanup observed outcome
...     | true = case just-injective eq of λ { refl → refl }
...     | false = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just f | just (Shared.cleanupDone outcome) | W.bufferScope _ = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just f | just (Shared.cleanupDone outcome) | W.classifying _ = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just f | just (Shared.cleanupDone outcome) | W.errorTracing _ _ = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just f | just (Shared.cleanupDone outcome) | W.peerRethrow _ = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just f | just (Shared.cleanupDone outcome) | W.nodeDelivery _ = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just f | just (Shared.cleanupDone outcome) | W.nodeRethrow _ = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just f | just (Shared.cleanupDone outcome) | W.bodyExited _ = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just f | just (Shared.cleanupDone outcome) | W.finalizing _ = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just f | just (Shared.cleanupDone outcome) | W.resultAvailable _ _ = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | nothing | _ = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just _ | nothing = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just _ | just Shared.cleanupAcquire = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just _ | just (Shared.cleanupSelect _) = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just _ | just (Shared.cleanupClose _ _ _) = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just _ | just (Shared.cleanupPublish _ _ _) = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just _ | just (Shared.cleanupRestore _ _) = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just _ | just (Shared.cleanupWaiting _) = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just _ | just (Shared.cleanupFinalize _ _) = case eq of λ ()
choose-root (W.publishAsyncResult w) s eq | just _ | just (Shared.cleanupCount _) = case eq of λ ()
choose-root (W.shutdownStep Close.acknowledgeDelivery) s ()
choose-root (W.shutdownStep Close.captureSnapshot) s eq = case just-injective eq of λ { refl → refl }
choose-root (W.shutdownStep Close.readEntry) s eq = case just-injective eq of λ { refl → refl }
choose-root (W.shutdownStep Close.requestCancellation) s eq = case just-injective eq of λ { refl → refl }
choose-root (W.shutdownStep Close.finishTraversal) s eq = case just-injective eq of λ { refl → refl }
choose-root (W.shutdownStep Close.finishClose) s eq = case just-injective eq of λ { refl → refl }
choose-root (W.deliverShutdownHandshake window err) s eq with Close.phase (W.shutdown s)
... | Close.awaitDelivery e w = case just-injective eq of λ { refl → refl }
choose-root (W.deliverShutdownHandshake window err) s eq | Close.initial = case eq of λ ()
choose-root (W.deliverShutdownHandshake window err) s eq | Close.reading = case eq of λ ()
choose-root (W.deliverShutdownHandshake window err) s eq | Close.awaitResults = case eq of λ ()
choose-root (W.deliverShutdownHandshake window err) s eq | Close.closed = case eq of λ ()
choose-root (W.deliverShutdownHandshake window err) s eq | Close.sendReady _ _ = case eq of λ ()
choose-root (W.deliverShutdownMux err) s eq with Close.phase (W.shutdown s)
... | Close.awaitDelivery e w = case just-injective eq of λ { refl → refl }
choose-root (W.deliverShutdownMux err) s eq | Close.initial = case eq of λ ()
choose-root (W.deliverShutdownMux err) s eq | Close.reading = case eq of λ ()
choose-root (W.deliverShutdownMux err) s eq | Close.awaitResults = case eq of λ ()
choose-root (W.deliverShutdownMux err) s eq | Close.closed = case eq of λ ()
choose-root (W.deliverShutdownMux err) s eq | Close.sendReady _ _ = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq with Close.phase (W.shutdown s)
... | Close.awaitDelivery e w with lookup w (W.exits s) | lookup w (Shared.cleanups (W.shared s))
...   | just f | just (Shared.cleanupWaiting _) with W.phase f | W.currentCapture w f s
...     | W.finalizing _ | true = case just-injective eq of λ { refl → refl }
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just f | just (Shared.cleanupWaiting x) | W.bufferScope _ | _ = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just f | just (Shared.cleanupWaiting x) | W.classifying _ | _ = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just f | just (Shared.cleanupWaiting x) | W.errorTracing _ _ | _ = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just f | just (Shared.cleanupWaiting x) | W.peerRethrow _ | _ = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just f | just (Shared.cleanupWaiting x) | W.nodeDelivery _ | _ = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just f | just (Shared.cleanupWaiting x) | W.nodeRethrow _ | _ = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just f | just (Shared.cleanupWaiting x) | W.bodyExited _ | _ = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just f | just (Shared.cleanupWaiting x) | W.finalizing _ | false = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just f | just (Shared.cleanupWaiting x) | W.cleanupComplete _ _ | _ = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just f | just (Shared.cleanupWaiting x) | W.resultAvailable _ _ | _ = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | nothing | _ = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just _ | nothing = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just _ | just Shared.cleanupAcquire = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just _ | just (Shared.cleanupSelect _) = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just _ | just (Shared.cleanupClose _ _ _) = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just _ | just (Shared.cleanupPublish _ _ _) = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just _ | just (Shared.cleanupRestore _ _) = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just _ | just (Shared.cleanupFinalize _ _) = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just _ | just (Shared.cleanupCount _) = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitDelivery e w | just _ | just (Shared.cleanupDone _) = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.initial = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.reading = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.awaitResults = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.closed = case eq of λ ()
choose-root (W.deliverShutdownTimeWait err) s eq | Close.sendReady _ _ = case eq of λ ()
choose-root W.acknowledgeFinished s eq with Close.phase (W.shutdown s)
... | Close.awaitDelivery e w with W.resultReady w s
...   | true = case just-injective eq of λ { refl → refl }
...   | false = case eq of λ ()
choose-root W.acknowledgeFinished s eq | Close.initial = case eq of λ ()
choose-root W.acknowledgeFinished s eq | Close.reading = case eq of λ ()
choose-root W.acknowledgeFinished s eq | Close.awaitResults = case eq of λ ()
choose-root W.acknowledgeFinished s eq | Close.closed = case eq of λ ()
choose-root W.acknowledgeFinished s eq | Close.sendReady _ _ = case eq of λ ()
choose-root (W.deliverReleaseMux caller err) s eq with W.releaseTarget caller s
... | nothing = case eq of λ ()
... | just target = case just-injective eq of λ { refl → refl }
choose-root (W.deliverReleaseTimeWait caller err) s eq with W.timeWaitTarget caller s
... | nothing = case eq of λ ()
... | just target = case just-injective eq of λ { refl → refl }
choose-root (W.acknowledgeReleaseFinished caller) s eq with W.releaseTarget caller s
... | nothing = case eq of λ ()
... | just target with W.resultReady target s
...   | false = case eq of λ ()
...   | true = case just-injective eq of λ { refl → refl }

step-keysW : ∀ a s {s′} → W.step a s ≡ just s′ → Effect (rootW a) (W.source s) (W.source s′)
step-keysW a s {s′} eq with W.choose a s in chosen
... | nothing = case eq of λ ()
... | just plan = subst (λ r → Effect r (W.source s) (W.source s′)) (choose-root a s chosen) (enact-keys plan s eq)

{-# OPTIONS --guardedness #-}

-- The legacy lifecycle store (Machine.handlerLifecycles) read by
-- HandlerValidity and TrackedChain stays empty in the supervised stack. Only a
-- raw Machine.handlerStep attaches a frame; every other source operation keeps
-- an empty store empty. HandlerSupervision starts empty and refuses raw
-- handlerStep, and the outbound physical layer refuses raw inbound operations,
-- so every initialized run of either layer keeps the store empty. Layers above
-- reach the source only through these two layers or through the explicit
-- direct operations covered by outbound-preserves.
module ConnectionManagement.Properties.LegacyLifecycleEmpty where

open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Function using (case_of_)
open import Relation.Nullary using (does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (DecEq-Id)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Handshake as Hs
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.InboundRelease as InRelease
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.Pruning as Prune
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R

Empty : M.Configuration → Set
Empty c = M.handlerLifecycles c ≡ []

-- Every source operation except a raw lifecycle attachment.
Quiet : M.Action → Set
Quiet (M.handlerStep _ _) = ⊥
Quiet _ = ⊤

remote-empty : ∀ a → Life.noteRemote a [] ≡ []
remote-empty Remote.enter = refl
remote-empty Remote.transact = refl
remote-empty Remote.checkAssertion = refl
remote-empty Remote.readCounters = refl
remote-empty Remote.returnToIG = refl
remote-empty Remote.requestPruneCancellation = refl
remote-empty (Remote.transactPruning n zs) = refl
remote-empty (Remote.pruneCancellationDelivered w) = refl
release-empty : ∀ a → Life.noteRelease a [] ≡ []
release-empty InRelease.enter = refl
release-empty InRelease.transact = refl
release-empty InRelease.readCounters = refl
release-empty InRelease.requestCancellation = refl
release-empty InRelease.checkAssertion = refl
release-empty InRelease.returnToIG = refl
release-empty (InRelease.cancellationDelivered w) = refl

machine-preserves : ∀ a c {d} → M.advance a c ≡ just d → Quiet a → Empty c → Empty d
machine-preserves (M.handlerStep w a) c eq () e
machine-preserves (M.admissionStep w a) c eq q e with Server.stepPrefix w a (M.world c)
... | nothing = case eq of λ ()
... | just s = case just-injective eq of λ { refl → e }
machine-preserves (M.handshakeStep w a) c eq q e with Hs.stepHandshake (M.responder c) w a (M.world c)
... | nothing = case eq of λ ()
... | just s = case just-injective eq of λ { refl → e }
machine-preserves (M.cleanupStep w a) c eq q e with Cleanup.stepCleanup w a (M.world c)
... | nothing = case eq of λ ()
... | just s = case just-injective eq of λ { refl → e }
machine-preserves (M.remoteStep a) c eq q e with Life.allowRemote a (M.handlerLifecycles c) (M.world c)
... | false = case eq of λ ()
... | true with Remote.step (M.promotionHardLimit c) (M.pruningGeneration c) a (M.remoteCall c) (M.inboundGovernor c) (M.world c)
...   | nothing = case eq of λ ()
...   | just plan with Prune.applyEdits (Remote.edits plan) (M.world c)
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → trans (cong (Life.noteRemote a) e) (remote-empty a) }
machine-preserves (M.releaseStep a) c eq q e with Life.allowRelease a (M.handlerLifecycles c) (M.world c)
... | false = case eq of λ ()
... | true with InRelease.step a (M.inboundRelease c) (M.inboundGovernor c) (M.world c)
...   | nothing = case eq of λ ()
...   | just plan with InRelease.applyEdit (InRelease.edit plan) (M.world c)
...     | nothing = case eq of λ ()
...     | just next = case just-injective eq of λ { refl → trans (cong (Life.noteRelease a) e) (release-empty a) }
machine-preserves (M.igStep a) c eq q e with Life.allowIG a (M.handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (M.responder c) a (M.inboundGovernor c) (S.inboundInfo (M.world c))
...   | nothing = case eq of λ ()
...   | just (governor , queue) = case just-injective eq of λ { refl → e }
machine-preserves (M.handlerExit w) c eq q e with Life.mayExit w (M.handlerLifecycles c)
... | false = case eq of λ ()
... | true with Cleanup.beginCleanupBoundary w (M.world c)
...   | nothing = case eq of λ ()
...   | just next = case just-injective eq of λ { refl → cong (Life.noteExit w) e }
machine-preserves (M.handlerPublication w result outcome) c eq q e with any (λ other → does (other ≟ w)) (M.publicationFaults c)
... | true = case eq of λ ()
... | false with Hs.publishBoundary w result (M.world c) | outcome
...   | nothing | _ = case eq of λ ()
...   | just (Hs.published next) | M.resultWritten = case just-injective eq of λ { refl → e }
...   | just (Hs.published next) | M.duplicateWrite = case eq of λ ()
...   | just Hs.writerBlocked | M.resultWritten = case eq of λ ()
...   | just Hs.writerBlocked | M.duplicateWrite = case just-injective eq of λ { refl → e }

-- Outbound-machine operations, including direct inbound calls by upper layers.
QuietO : O.Action → Set
QuietO (O.inbound a) = Quiet a
QuietO _ = ⊤

outbound-preserves : ∀ a c {d} → O.advance a c ≡ just d → QuietO a → Empty (O.core c) → Empty (O.core d)
outbound-preserves (O.inbound a) c eq q e with M.advance a (O.core c) in actual
... | nothing = case eq of λ ()
... | just c′ = case just-injective eq of λ { refl → machine-preserves a (O.core c) actual q e }
outbound-preserves (O.beginAcquire w req) c eq q e with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | nothing | nothing = case just-injective eq of λ { refl → e }
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
outbound-preserves (O.beginRelease w key) c eq q e with lookup w (O.acquiring c) | lookup w (O.releasing c)
... | nothing | nothing = case just-injective eq of λ { refl → e }
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
outbound-preserves (O.acquire w A.returnResult) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.pc f
...   | A.complete result = case just-injective eq of λ { refl → e }
...   | A.selecting = case eq of λ ()
...   | (A.count p) = case eq of λ ()
...   | (A.allocatePromise e) = case eq of λ ()
...   | (A.openSocket e p) = case eq of λ ()
...   | (A.configureSocket e p) = case eq of λ ()
...   | (A.bindSocket e p) = case eq of λ ()
...   | (A.connectSocket e p) = case eq of λ ()
...   | (A.localAddress e p) = case eq of λ ()
...   | (A.updateAddress e p k) = case eq of λ ()
...   | (A.forkHandler e p k) = case eq of λ ()
...   | (A.connectedCommit e p k) = case eq of λ ()
...   | (A.awaitResult e p k) = case eq of λ ()
...   | (A.commitResult e k r) = case eq of λ ()
...   | (A.waitingInbound e k) = case eq of λ ()
...   | (A.closeError e x) = case eq of λ ()
...   | (A.removeError e x) = case eq of λ ()
outbound-preserves (O.release w R.returnResult) c eq q e with lookup w (O.releasing c)
... | nothing = case eq of λ ()
... | just f with R.pc f
...   | R.complete result = case just-injective eq of λ { refl → e }
...   | R.transaction = case eq of λ ()
...   | (R.check b p) = case eq of λ ()
...   | (R.count p) = case eq of λ ()
...   | (R.armTimer e w′) = case eq of λ ()
...   | (R.waitIdle e w′) = case eq of λ ()
...   | (R.timeoutWrite e w′) = case eq of λ ()
...   | (R.cancel w′ p) = case eq of λ ()
...   | (R.delivering w′ p) = case eq of λ ()
...   | (R.prune cs r) = case eq of λ ()
outbound-preserves (O.acquire w A.readCounters) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.readCounters f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.newPromise) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.newPromise f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.openOK) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.openOK f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.configureOK) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.configureOK f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.bindOK) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.bindOK f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.connectOK) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.connectOK f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.updateLocalAddress) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.updateLocalAddress f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.forkOK) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.forkOK f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.commitConnected) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.commitConnected f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.readResult) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.readResult f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.commitHandshake) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.commitHandshake f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.closeOK) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.closeOK f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.removeReservation) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.removeReservation f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w A.waitNegotiated) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) A.waitNegotiated f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w (A.select x)) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) (A.select x) f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w (A.gotLocal x)) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) (A.gotLocal x) f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w (A.failIO x)) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) (A.failIO x) f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.acquire w (A.closeFailed x)) c eq q e with lookup w (O.acquiring c)
... | nothing = case eq of λ ()
... | just f with A.step w (M.responder (O.core c)) (A.closeFailed x) f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → e }
outbound-preserves (O.release w R.transactionStep) c eq q e with lookup w (O.releasing c) | O.canDeliver R.transactionStep c
... | just f | true with R.step (M.promotionHardLimit (O.core c)) R.transactionStep f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → cong (O.noteDelivery R.transactionStep) e }
outbound-preserves (O.release w R.transactionStep) c eq q e | just f | false = case eq of λ ()
outbound-preserves (O.release w R.transactionStep) c eq q e | nothing | _ = case eq of λ ()
outbound-preserves (O.release w R.checkAssertion) c eq q e with lookup w (O.releasing c) | O.canDeliver R.checkAssertion c
... | just f | true with R.step (M.promotionHardLimit (O.core c)) R.checkAssertion f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → cong (O.noteDelivery R.checkAssertion) e }
outbound-preserves (O.release w R.checkAssertion) c eq q e | just f | false = case eq of λ ()
outbound-preserves (O.release w R.checkAssertion) c eq q e | nothing | _ = case eq of λ ()
outbound-preserves (O.release w R.readCounters) c eq q e with lookup w (O.releasing c) | O.canDeliver R.readCounters c
... | just f | true with R.step (M.promotionHardLimit (O.core c)) R.readCounters f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → cong (O.noteDelivery R.readCounters) e }
outbound-preserves (O.release w R.readCounters) c eq q e | just f | false = case eq of λ ()
outbound-preserves (O.release w R.readCounters) c eq q e | nothing | _ = case eq of λ ()
outbound-preserves (O.release w R.registerTimer) c eq q e with lookup w (O.releasing c) | O.canDeliver R.registerTimer c
... | just f | true with R.step (M.promotionHardLimit (O.core c)) R.registerTimer f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → cong (O.noteDelivery R.registerTimer) e }
outbound-preserves (O.release w R.registerTimer) c eq q e | just f | false = case eq of λ ()
outbound-preserves (O.release w R.registerTimer) c eq q e | nothing | _ = case eq of λ ()
outbound-preserves (O.release w R.expireTimer) c eq q e with lookup w (O.releasing c) | O.canDeliver R.expireTimer c
... | just f | true with R.step (M.promotionHardLimit (O.core c)) R.expireTimer f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → cong (O.noteDelivery R.expireTimer) e }
outbound-preserves (O.release w R.expireTimer) c eq q e | just f | false = case eq of λ ()
outbound-preserves (O.release w R.expireTimer) c eq q e | nothing | _ = case eq of λ ()
outbound-preserves (O.release w R.selectWakeup) c eq q e with lookup w (O.releasing c) | O.canDeliver R.selectWakeup c
... | just f | true with R.step (M.promotionHardLimit (O.core c)) R.selectWakeup f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → cong (O.noteDelivery R.selectWakeup) e }
outbound-preserves (O.release w R.selectWakeup) c eq q e | just f | false = case eq of λ ()
outbound-preserves (O.release w R.selectWakeup) c eq q e | nothing | _ = case eq of λ ()
outbound-preserves (O.release w R.commitTimeout) c eq q e with lookup w (O.releasing c) | O.canDeliver R.commitTimeout c
... | just f | true with R.step (M.promotionHardLimit (O.core c)) R.commitTimeout f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → cong (O.noteDelivery R.commitTimeout) e }
outbound-preserves (O.release w R.commitTimeout) c eq q e | just f | false = case eq of λ ()
outbound-preserves (O.release w R.commitTimeout) c eq q e | nothing | _ = case eq of λ ()
outbound-preserves (O.release w R.requestCancellation) c eq q e with lookup w (O.releasing c) | O.canDeliver R.requestCancellation c
... | just f | true with R.step (M.promotionHardLimit (O.core c)) R.requestCancellation f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → cong (O.noteDelivery R.requestCancellation) e }
outbound-preserves (O.release w R.requestCancellation) c eq q e | just f | false = case eq of λ ()
outbound-preserves (O.release w R.requestCancellation) c eq q e | nothing | _ = case eq of λ ()
outbound-preserves (O.release w (R.transactionPruning x)) c eq q e with lookup w (O.releasing c) | O.canDeliver (R.transactionPruning x) c
... | just f | true with R.step (M.promotionHardLimit (O.core c)) (R.transactionPruning x) f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → cong (O.noteDelivery (R.transactionPruning x)) e }
outbound-preserves (O.release w (R.transactionPruning x)) c eq q e | just f | false = case eq of λ ()
outbound-preserves (O.release w (R.transactionPruning x)) c eq q e | nothing | _ = case eq of λ ()
outbound-preserves (O.release w (R.cancellationDelivered x)) c eq q e with lookup w (O.releasing c) | O.canDeliver (R.cancellationDelivered x) c
... | just f | true with R.step (M.promotionHardLimit (O.core c)) (R.cancellationDelivered x) f (M.world (O.core c))
...   | nothing = case eq of λ ()
...   | just (f′ , world′) = case just-injective eq of λ { refl → cong (O.noteDelivery (R.cancellationDelivered x)) e }
outbound-preserves (O.release w (R.cancellationDelivered x)) c eq q e | just f | false = case eq of λ ()
outbound-preserves (O.release w (R.cancellationDelivered x)) c eq q e | nothing | _ = case eq of λ ()

-- HandlerSupervision: the only layer that forwards arbitrary raw source operations.
module Raw where
 Valid : H.State → Set
 Valid s = Empty (H.source s)
 dispatch-preserves : ∀ a s {t} → H.dispatch a s ≡ just t → Quiet a → Valid s → Valid t
 dispatch-preserves a s eq q e with M.advance a (H.source s) in actual
 ... | nothing = case eq of λ ()
 ... | just c = case just-injective eq of λ { refl → machine-preserves a (H.source s) actual q e }
 dispatch-phase-preserves : ∀ a w thread pc s {t} → H.dispatchPhase a w thread pc s ≡ just t → Quiet a → Valid s → Valid t
 dispatch-phase-preserves a w thread pc s eq q e with H.dispatch a s in actual
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → dispatch-preserves a s actual q e }
 acknowledge-preserves : ∀ s {t} → H.acknowledge s ≡ just t → Valid s → Valid t
 acknowledge-preserves s eq e with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.acknowledgeDelivery (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → e }
 fork-preserves : ∀ w s {t} → H.forkAdmission w s ≡ just t → Valid s → Valid t
 fork-preserves w s eq e with lookup w (S.admissions (M.world (H.source s)))
 ... | nothing = case eq of λ ()
 ... | just a with lookup (S.child (S.request a)) (H.threads s)
 ...   | just old = case eq of λ ()
 ...   | nothing with M.advance (M.admissionStep w Server.fork) (H.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just c with lookup (S.child (S.request a)) (S.handlers (M.world c))
 ...       | nothing = case eq of λ ()
 ...       | just handler = case just-injective eq of λ { refl → machine-preserves (M.admissionStep w Server.fork) (H.source s) actual tt e }
 handshake-preserves : ∀ w err s {t} → H.deliverHandshake w err s ≡ just t → Valid s → Valid t
 handshake-preserves w err s eq e with lookup w (H.threads s)
 ... | nothing = case eq of λ ()
 ... | just thread with H.phase thread
 handshake-preserves w err s eq e | just thread | H.maskedSetup = case eq of λ ()
 handshake-preserves w err s eq e | just thread | H.handshaking = case just-injective eq of λ { refl → e }
 handshake-preserves w err s eq e | just thread | (H.caughtCancellation old) = case eq of λ ()
 handshake-preserves w err s eq e | just thread | (H.cancellationPublished old) = case eq of λ ()
 handshake-preserves w err s eq e | just thread | (H.bodyExited old) = case eq of λ ()
 handshake-preserves w err s eq e | just thread | (H.finalizing old) = case eq of λ ()
 handshake-preserves w err s eq e | just thread | (H.cleanupComplete old outcome) = case eq of λ ()
 handshake-preserves w err s eq e | just thread | (H.resultAvailable old outcome) = case eq of λ ()
 setup-preserves : ∀ w err s {t} → H.deliverBlockedSetup w err s ≡ just t → Valid s → Valid t
 setup-preserves w err s eq e with lookup w (H.threads s)
 ... | nothing = case eq of λ ()
 ... | just thread with H.phase thread
 setup-preserves w err s eq e | just thread | H.maskedSetup = case just-injective eq of λ { refl → e }
 setup-preserves w err s eq e | just thread | H.handshaking = case eq of λ ()
 setup-preserves w err s eq e | just thread | (H.caughtCancellation old) = case eq of λ ()
 setup-preserves w err s eq e | just thread | (H.cancellationPublished old) = case eq of λ ()
 setup-preserves w err s eq e | just thread | (H.bodyExited old) = case eq of λ ()
 setup-preserves w err s eq e | just thread | (H.finalizing old) = case eq of λ ()
 setup-preserves w err s eq e | just thread | (H.cleanupComplete old outcome) = case eq of λ ()
 setup-preserves w err s eq e | just thread | (H.resultAvailable old outcome) = case eq of λ ()
 shutdown-preserves : ∀ blocked err s {t} → H.deliverShutdown blocked err s ≡ just t → Valid s → Valid t
 shutdown-preserves blocked err s eq e with Close.phase (H.shutdown s)
 ... | Close.awaitDelivery e′ w with blocked
 ...   | false with H.deliverHandshake w err s in delivered
 ...     | nothing = case eq of λ ()
 ...     | just next = acknowledge-preserves next eq (handshake-preserves w err s delivered e)
 shutdown-preserves blocked err s eq e | Close.awaitDelivery e′ w | true with H.deliverBlockedSetup w err s in delivered
 ...     | nothing = case eq of λ ()
 ...     | just next = acknowledge-preserves next eq (setup-preserves w err s delivered e)
 shutdown-preserves blocked err s eq e | Close.initial = case eq of λ ()
 shutdown-preserves blocked err s eq e | Close.reading = case eq of λ ()
 shutdown-preserves blocked err s eq e | (Close.sendReady e′ w′) = case eq of λ ()
 shutdown-preserves blocked err s eq e | Close.awaitResults = case eq of λ ()
 shutdown-preserves blocked err s eq e | Close.closed = case eq of λ ()
 timewait-preserves : ∀ err s {t} → H.deliverTimeWait err s ≡ just t → Valid s → Valid t
 timewait-preserves err s eq e with Close.phase (H.shutdown s)
 ... | Close.awaitDelivery e′ w with lookup w (H.threads s) | lookup w (S.cleanups (M.world (H.source s)))
 ...   | just t | just (S.cleanupWaiting captured) with H.phase t
 ...     | H.finalizing original with H.dispatch (M.cleanupStep w (Cleanup.interruptTimeWait err)) s in advanced
 ...       | nothing = case eq of λ ()
 ...       | just next = acknowledge-preserves next eq (dispatch-preserves (M.cleanupStep w (Cleanup.interruptTimeWait err)) s advanced tt e)
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupWaiting captured) | H.maskedSetup = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupWaiting captured) | H.handshaking = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupWaiting captured) | (H.caughtCancellation old) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupWaiting captured) | (H.cancellationPublished old) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupWaiting captured) | (H.bodyExited old) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupWaiting captured) | (H.cleanupComplete old outcome) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupWaiting captured) | (H.resultAvailable old outcome) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just S.cleanupAcquire = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupSelect l) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupClose l m tl) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupPublish l m tl) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupRestore l x) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupFinalize h o) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupCount o) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | just (S.cleanupDone o) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | nothing | cleanup = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitDelivery e′ w | just t | nothing = case eq of λ ()
 timewait-preserves err s eq e | Close.initial = case eq of λ ()
 timewait-preserves err s eq e | Close.reading = case eq of λ ()
 timewait-preserves err s eq e | (Close.sendReady e′ w′) = case eq of λ ()
 timewait-preserves err s eq e | Close.awaitResults = case eq of λ ()
 timewait-preserves err s eq e | Close.closed = case eq of λ ()
 step-preserves : ∀ action s {t} → H.step action s ≡ just t → Valid s → Valid t
 step-preserves (H.run (M.admissionStep w Server.fork)) s eq e = fork-preserves w s eq e
 step-preserves (H.run (M.admissionStep w Server.take)) s eq e = dispatch-preserves (M.admissionStep w Server.take) s eq tt e
 step-preserves (H.run (M.admissionStep w Server.countLimit)) s eq e = dispatch-preserves (M.admissionStep w Server.countLimit) s eq tt e
 step-preserves (H.run (M.admissionStep w Server.allocatePromise)) s eq e = dispatch-preserves (M.admissionStep w Server.allocatePromise) s eq tt e
 step-preserves (H.run (M.admissionStep w Server.chooseEntry)) s eq e = dispatch-preserves (M.admissionStep w Server.chooseEntry) s eq tt e
 step-preserves (H.run (M.admissionStep w Server.putMapBack)) s eq e = dispatch-preserves (M.admissionStep w Server.putMapBack) s eq tt e
 step-preserves (H.run (M.admissionStep w Server.readCounters)) s eq e = dispatch-preserves (M.admissionStep w Server.readCounters) s eq tt e
 step-preserves (H.run (M.admissionStep w Server.restoreBody)) s eq e = dispatch-preserves (M.admissionStep w Server.restoreBody) s eq tt e
 step-preserves (H.run (M.admissionStep w Server.restore)) s eq e = dispatch-preserves (M.admissionStep w Server.restore) s eq tt e
 step-preserves (H.run (M.admissionStep w Server.close)) s eq e = dispatch-preserves (M.admissionStep w Server.close) s eq tt e
 step-preserves (H.run (M.admissionStep w Server.failFork)) s eq e = dispatch-preserves (M.admissionStep w Server.failFork) s eq tt e
 step-preserves (H.run (M.handshakeStep w a)) s eq e = dispatch-preserves (M.handshakeStep w a) s eq tt e
 step-preserves (H.run (M.handlerPublication w result outcome)) s eq e = case eq of λ ()
 step-preserves (H.run (M.handlerExit w)) s eq e = case eq of λ ()
 step-preserves (H.run (M.handlerStep w a)) s eq e = case eq of λ ()
 step-preserves (H.run (M.cleanupStep w a)) s eq e = case eq of λ ()
 step-preserves (H.run (M.igStep a)) s eq e = dispatch-preserves (M.igStep a) s eq tt e
 step-preserves (H.run (M.remoteStep a)) s eq e with H.rawAllowed (M.remoteStep a)
 ... | false = case eq of λ ()
 ... | true = dispatch-preserves (M.remoteStep a) s eq tt e
 step-preserves (H.run (M.releaseStep a)) s eq e with H.rawAllowed (M.releaseStep a)
 ... | false = case eq of λ ()
 ... | true = dispatch-preserves (M.releaseStep a) s eq tt e
 step-preserves (H.enterHandshake w) s eq e with lookup w (H.threads s)
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 step-preserves (H.enterHandshake w) s eq e | just t | H.maskedSetup = case just-injective eq of λ { refl → e }
 step-preserves (H.enterHandshake w) s eq e | just t | H.handshaking = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq e | just t | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq e | just t | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq e | just t | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq e | just t | (H.finalizing err) = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq e | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 step-preserves (H.enterHandshake w) s eq e | just t | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.deliverHandshakeCancellation w err) s eq e = handshake-preserves w err s eq e
 step-preserves (H.deliverBlockedSetupCancellation w err) s eq e = setup-preserves w err s eq e
 step-preserves (H.publishCaught w) s eq e with lookup w (H.threads s)
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 step-preserves (H.publishCaught w) s eq e | just t | H.maskedSetup = case eq of λ ()
 step-preserves (H.publishCaught w) s eq e | just t | H.handshaking = case eq of λ ()
 step-preserves (H.publishCaught w) s eq e | just t | (H.caughtCancellation err) = dispatch-phase-preserves (M.handlerPublication w (S.handlerError S.protocolViolation err) M.resultWritten) w t (H.cancellationPublished err) s eq tt e
 step-preserves (H.publishCaught w) s eq e | just t | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.publishCaught w) s eq e | just t | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.publishCaught w) s eq e | just t | (H.finalizing err) = case eq of λ ()
 step-preserves (H.publishCaught w) s eq e | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 step-preserves (H.publishCaught w) s eq e | just t | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq e with lookup w (H.threads s)
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 step-preserves (H.rethrowCaught w) s eq e | just t | H.maskedSetup = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq e | just t | H.handshaking = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq e | just t | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq e | just t | (H.cancellationPublished err) = case just-injective eq of λ { refl → e }
 step-preserves (H.rethrowCaught w) s eq e | just t | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq e | just t | (H.finalizing err) = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq e | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 step-preserves (H.rethrowCaught w) s eq e | just t | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq e with lookup w (H.threads s)
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 step-preserves (H.enterFinalizer w) s eq e | just t | H.maskedSetup = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq e | just t | H.handshaking = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq e | just t | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq e | just t | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq e | just t | (H.bodyExited err) = dispatch-phase-preserves (M.handlerExit w) w t (H.finalizing err) s eq tt e
 step-preserves (H.enterFinalizer w) s eq e | just t | (H.finalizing err) = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq e | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 step-preserves (H.enterFinalizer w) s eq e | just t | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.cleanup w action) s eq e with lookup w (H.threads s)
 ... | nothing = case eq of λ ()
 ... | just t with H.phase t
 step-preserves (H.cleanup w action) s eq e | just t | H.maskedSetup = case eq of λ ()
 step-preserves (H.cleanup w action) s eq e | just t | H.handshaking = case eq of λ ()
 step-preserves (H.cleanup w action) s eq e | just t | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.cleanup w action) s eq e | just t | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.cleanup w action) s eq e | just t | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.cleanup w action) s eq e | just t | (H.finalizing err) = dispatch-preserves (M.cleanupStep w action) s eq tt e
 step-preserves (H.cleanup w action) s eq e | just t | (H.cleanupComplete err outcome) = case eq of λ ()
 step-preserves (H.cleanup w action) s eq e | just t | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e with lookup w (H.threads s) | lookup w (S.cleanups (M.world (H.source s)))
 ... | just t | just (S.cleanupDone done) with H.phase t
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupDone done) | H.maskedSetup = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupDone done) | H.handshaking = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupDone done) | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupDone done) | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupDone done) | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupDone done) | (H.finalizing err) = case just-injective eq of λ { refl → e }
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupDone done) | (H.cleanupComplete err outcome) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupDone done) | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | nothing | cleanup = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | nothing = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just S.cleanupAcquire = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupSelect l) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupClose l m tl) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupPublish l m tl) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupRestore l x) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupWaiting h) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupFinalize h o) = case eq of λ ()
 step-preserves (H.finishCleanup w) s eq e | just t | just (S.cleanupCount o) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e with lookup w (H.threads s) | lookup w (S.cleanups (M.world (H.source s)))
 ... | just t | just (S.cleanupDone done) with H.phase t
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupDone done) | H.maskedSetup = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupDone done) | H.handshaking = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupDone done) | (H.caughtCancellation err) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupDone done) | (H.cancellationPublished err) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupDone done) | (H.bodyExited err) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupDone done) | (H.finalizing err) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupDone done) | (H.cleanupComplete err outcome) = case just-injective eq of λ { refl → e }
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupDone done) | (H.resultAvailable err outcome) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | nothing | cleanup = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | nothing = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just S.cleanupAcquire = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupSelect l) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupClose l m tl) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupPublish l m tl) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupRestore l x) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupWaiting h) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupFinalize h o) = case eq of λ ()
 step-preserves (H.publishAsyncResult w) s eq e | just t | just (S.cleanupCount o) = case eq of λ ()
 step-preserves (H.shutdownStep Close.captureSnapshot) s eq e with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.captureSnapshot (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → e }
 step-preserves (H.shutdownStep Close.readEntry) s eq e with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.readEntry (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → e }
 step-preserves (H.shutdownStep Close.requestCancellation) s eq e with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.requestCancellation (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → e }
 step-preserves (H.shutdownStep Close.finishTraversal) s eq e with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.finishTraversal (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → e }
 step-preserves (H.shutdownStep Close.finishClose) s eq e with Close.step (S.cm (M.world (H.source s))) (λ w → H.resultReady w s) Close.finishClose (H.shutdown s)
 ... | nothing = case eq of λ ()
 ... | just next = case just-injective eq of λ { refl → e }
 step-preserves (H.shutdownStep Close.acknowledgeDelivery) s () e
 step-preserves (H.deliverShutdownHandshake err) s eq e = shutdown-preserves false err s eq e
 step-preserves (H.deliverShutdownBlockedSetup err) s eq e = shutdown-preserves true err s eq e
 step-preserves (H.deliverShutdownTimeWait err) s eq e = timewait-preserves err s eq e
 step-preserves H.acknowledgeFinished s eq e with Close.phase (H.shutdown s)
 ... | Close.awaitDelivery e′ w with H.resultReady w s
 ...   | true = acknowledge-preserves s eq e
 ...   | false = case eq of λ ()
 step-preserves H.acknowledgeFinished s eq e | Close.initial = case eq of λ ()
 step-preserves H.acknowledgeFinished s eq e | Close.reading = case eq of λ ()
 step-preserves H.acknowledgeFinished s eq e | (Close.sendReady e′ w′) = case eq of λ ()
 step-preserves H.acknowledgeFinished s eq e | Close.awaitResults = case eq of λ ()
 step-preserves H.acknowledgeFinished s eq e | Close.closed = case eq of λ ()
 exec-preserves : ∀ {s as t} → H.Executes s as t → Valid s → Valid t
 exec-preserves H.done e = e
 exec-preserves {s} (H.next {a = a} eq rest) e = exec-preserves rest (step-preserves a s eq e)
 initialized-valid : ∀ c {s} → H.initial c ≡ just s → Valid s
 initialized-valid c eq with S.handlers (M.world c) | S.cleanups (M.world c) | M.handlerLifecycles c in empty | M.publicationFaults c
 ... | [] | [] | [] | [] = case just-injective eq of λ { refl → empty }
 ... | _ ∷ _ | _ | _ | _ = case eq of λ ()
 ... | [] | _ ∷ _ | _ | _ = case eq of λ ()
 ... | [] | [] | _ ∷ _ | _ = case eq of λ ()
 ... | [] | [] | [] | _ ∷ _ = case eq of λ ()
 -- Every initialized handler-supervision run keeps the legacy store empty.
 from-initial : ∀ c {start as s} → H.initial c ≡ just start → H.Executes start as s → M.handlerLifecycles (H.source s) ≡ []
 from-initial c actual path = exec-preserves path (initialized-valid c actual)

-- The outbound physical layer forwards handler actions to Raw and refuses raw
-- inbound source operations on its outbound side.
module Physical where
 Valid : B.State → Set
 Valid s = Empty (O.core (B.source s))
 allowed-quiet : ∀ a s → B.outboundAllowed a s ≡ true → QuietO a
 allowed-quiet (O.inbound a) s ()
 allowed-quiet (O.beginAcquire w req) s allowed = tt
 allowed-quiet (O.acquire w a) s allowed = tt
 allowed-quiet (O.beginRelease w key) s allowed = tt
 allowed-quiet (O.release w a) s allowed = tt
 fork-preserves : ∀ w s {t} → B.forkOutbound w s ≡ just t → Valid s → Valid t
 fork-preserves w s eq e with lookup w (O.acquiring (B.source s))
 ... | nothing = case eq of λ ()
 ... | just f with B.freshChild (A.child (A.req f)) s
 ...   | false = case eq of λ ()
 ...   | true with O.advance (O.acquire w A.forkOK) (B.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just c with lookup (A.child (A.req f)) (S.handlers (M.world (O.core c)))
 ...       | nothing = case eq of λ ()
 ...       | just captured = case just-injective eq of λ { refl → outbound-preserves (O.acquire w A.forkOK) (B.source s) actual tt e }
 step-preserves : ∀ a s {t} → B.step a s ≡ just t → Valid s → Valid t
 step-preserves (B.handler a) s eq e with B.handlerAllowed a s
 ... | false = case eq of λ ()
 ... | true with H.step a (B.view s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just h = case just-injective eq of λ { refl → Raw.step-preserves a (B.view s) actual e }
 step-preserves (B.outbound a) s eq e with B.forkCaller a
 ... | just w = fork-preserves w s eq e
 ... | nothing with B.outboundAllowed a s in allowed
 ...   | false = case eq of λ ()
 ...   | true with O.advance a (B.source s) in actual
 ...     | nothing = case eq of λ ()
 ...     | just c = case just-injective eq of λ { refl → outbound-preserves a (B.source s) actual (allowed-quiet a s allowed) e }
 exec-preserves : ∀ {s as t} → B.Executes s as t → Valid s → Valid t
 exec-preserves B.done e = e
 exec-preserves {s} (B.next {a = a} eq rest) e = exec-preserves rest (step-preserves a s eq e)
 initialized-valid : ∀ c {s} → B.initial c ≡ just s → Valid s
 initialized-valid c eq with H.initial (O.core c) in actual
 ... | nothing = case eq of λ ()
 ... | just h = case just-injective eq of λ { refl → Raw.initialized-valid (O.core c) actual }
 -- Every initialized outbound-physical run keeps the legacy store empty.
 from-initial : ∀ c {start as s} → B.initial c ≡ just start → B.Executes start as s → M.handlerLifecycles (O.core (B.source s)) ≡ []
 from-initial c actual path = exec-preserves path (initialized-valid c actual)

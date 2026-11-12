{-# OPTIONS --guardedness #-}

-- Saved publication-failure content through Server, IG, peer and frontend
-- writers. Saved frames keep their own immutable profiles and physical captures.
module ConnectionManagement.Properties.LiveTrackerFailureFrontend where

open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; ErrorId; HandleId)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
open import ConnectionManagement.IGTypes using (clean; errored; number)
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.MuxDeltaQ as DeltaQModel
import ConnectionManagement.MuxCatchUnwind as CatchModel
import ConnectionManagement.MuxPublicationUnwind as PublicationModel
import ConnectionManagement.ServerAdmission as AdmissionModel
import ConnectionManagement.ServerIGExit as IGExitModel
import ConnectionManagement.ServerPeers as SharedModel
import ConnectionManagement.PeerSupervision as PeerModel
import ConnectionManagement.PeerContext as PeerContext
import ConnectionManagement.Properties.MuxStartupUnwind as UnwindFacts
import ConnectionManagement.Properties.MuxDeltaQ as DeltaFacts
import ConnectionManagement.Properties.MuxCatchUnwind as CatchFacts
import ConnectionManagement.Properties.CleanupPeers as CleanupPeers
import ConnectionManagement.Properties.InboundOriginRuntime as OriginRuntime
import ConnectionManagement.Properties.InboundOriginPeers as OriginPeers
import ConnectionManagement.Properties.LiveTrackerContentFrontend as Frame
import ConnectionManagement.Properties.LiveTrackerCaptureFrontend as Capture
import ConnectionManagement.Properties.LiveTrackerFailureContent as Failure
import ConnectionManagement.Properties.LiveTrackerFrameContent as Content
import ConnectionManagement.Properties.LiveTrackerCapture as Captured
import ConnectionManagement.Properties.HandlerBirthEffects as Birth
open import ConnectionManagement.Properties.LiveTrackerFrameContent using (Content; at)
import ConnectionManagement.Properties.LiveTrackerContentPeers as PeersContent
open import Data.List.Relation.Unary.All using ([]; _∷_)


-- Source bookkeeping preserves the saved frame's own contents and descriptor.
module Lower (b : ErrorId → Bool) where
 private module N = PublicationModel b using (module C; module R; State; base; captured; failures; initial; publicationState; raw; source; step)
 private module F = Failure b using (Covers; Valid; captures; descriptor; frames; negotiated; snapshot; snapshots; failure-valid; view)
 private module U = ProtocolModel.U
 source-snapshots : ∀ c s →
   Machine.inboundGovernor (O.core c) ≡ Machine.inboundGovernor (O.core (N.source s)) →
   Shared.handlers (Machine.world (O.core c)) ≡ Shared.handlers (Machine.world (O.core (N.source s))) →
   Shared.handshakeResults (Machine.world (O.core c)) ≡ Shared.handshakeResults (Machine.world (O.core (N.source s))) →
   ∀ rows → F.Covers rows (F.view s) (N.source s) → F.Covers rows (F.view s) c
 source-snapshots c s tables handlers results [] [] = []
 source-snapshots c s tables handlers results ((w , row) ∷ rows) (good ∷ rest) =
   F.snapshot (F.descriptor good) (Content.same-stores w (N.captured row) (N.source s) c tables handlers results (F.negotiated good)) ∷
   source-snapshots c s tables handlers results rows rest
 source-quiet : ∀ c s →
   Machine.inboundGovernor (O.core c) ≡ Machine.inboundGovernor (O.core (N.source s)) →
   Shared.handlers (Machine.world (O.core c)) ≡ Shared.handlers (Machine.world (O.core (N.source s))) →
   Shared.handshakeResults (Machine.world (O.core c)) ≡ Shared.handshakeResults (Machine.world (O.core (N.source s))) →
   F.Valid s → F.Valid (N.publicationState
     (record (N.base s) { base = record (N.C.base (N.base s)) { base = N.R.setSource c (N.raw s) } }) (N.failures s))
 source-quiet c s tables handlers results valid = F.failure-valid
   (Content.reframe _ (N.source s) c tables handlers results (F.frames valid))
   (Capture.Publication.source-valid b c s (F.captures valid))
   (source-snapshots c s tables handlers results (N.failures s) (F.snapshots valid))

module Peer (b io : ErrorId → Bool) where
 private module N = PublicationModel b using (module C; module R; State; base; captured; failures; initial; publicationState; raw; source; step)
 private module F = Failure b using (Covers; Valid; captures; descriptor; frames; negotiated; snapshot; snapshots; failure-valid; view)
 private module PS = PeerModel io using (cm; step)
 snapshots : ∀ a p {q} → PS.step a p ≡ just q → ∀ registry rows →
   F.Covers rows registry (PS.cm p) → F.Covers rows registry (PS.cm q)
 snapshots a p actual registry [] [] = []
 snapshots a p actual registry ((w , row) ∷ rows) (good ∷ rest) =
   F.snapshot (F.descriptor good) (PeersContent.For.preserves b io w (N.captured row) a p actual (F.negotiated good)) ∷
   snapshots a p actual registry rows rest
 preserve : ∀ a p {q} → PS.step a p ≡ just q → ∀ s → N.source s ≡ PS.cm p →
   F.Valid s → F.Valid (N.publicationState
     (record (N.base s) { base = record (N.C.base (N.base s)) { base = N.R.setSource (PS.cm q) (N.raw s) } }) (N.failures s))
 preserve a p {q} actual s same valid = F.failure-valid
   (Frame.peer-content b io a p actual _ (subst (Content.Covers _) same (F.frames valid)))
   (Capture.Publication.source-valid b (PS.cm q) s (F.captures valid))
   (snapshots a p actual (F.view s) (N.failures s) (subst (F.Covers (N.failures s) (F.view s)) same (F.snapshots valid)))

-- Server bookkeeping retains backing; real physical calls use the lower proof.
module Server (isBearerClosed : ErrorId → Bool) where
 private module SA = AdmissionModel isBearerClosed using (Action; State; initial; setSource; source; request; socketOutcome; acceptedFork; accepting; allowed; base; bodyExited; calling; chooseScope; closeDisconnected; closeException; closePrefix; closePrefixWorker; closeWorker; enactClose; enactPrefixClose; enactScope; forkAccepted; fresh; inherit; listenerOpen; nextException; nextNormal; observeException; observeReturn; pc; physicalAction; prefixCloseFailed; prefixException; prefixMatches; prefixReturned; publishWorkerResult; resultAvailable; run; runMachine; sameLimit; scope; scopeAdvance; shared; stage; step; workerClose; workerException; workerPrefixException; workerPrefixReturned; workerResult; workerReturned; workers)
 private module N = PublicationModel isBearerClosed using (initial; raw; step)
 private module W = ExitModel isBearerClosed using (run)
 private module G = GroupModel isBearerClosed using (Action; run)
 private module Monitor = MonitorModel isBearerClosed using (run)
 private module P = ProtocolModel using (run)
 private module U = MuxModel Types.TypedResult using (run)
 private module PublishFacts = Failure isBearerClosed using (Valid; initialized-valid; step-preserves)
 Valid : SA.State → Set
 Valid s = PublishFacts.Valid (SA.base s)
 -- Successful birth writes an admission and socket; physical metadata is separate.
 fork-preserves : ∀ w req s {t} → SA.forkAccepted w req s ≡ just t → Valid s → Valid t
 fork-preserves w req s eq valid with SA.accepting (SA.stage s) | SA.listenerOpen s |
   SA.sameLimit req (SA.workers s) | SA.fresh w s | SA.fresh (Shared.child req) s |
   w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (SA.shared s))
 ... | true | true | true | true | true | no _ | nothing =
   case just-injective eq of λ { refl → Lower.source-quiet isBearerClosed
     (record (SA.source s) { core = Machine.replaceWorld (O.core (SA.source s)) (record (SA.shared s)
       { admissions = put w (Shared.admissionWorker req Shared.acquireMap) (Shared.admissions (SA.shared s))
       ; sockets = put (Shared.socketRef req) (Shared.admitting w) (Shared.sockets (SA.shared s)) }) })
     (SA.base s) refl refl refl valid }
 ... | false | _ | _ | _ | _ | _ | _ = case eq of λ ()
 ... | true | false | _ | _ | _ | _ | _ = case eq of λ ()
 ... | true | true | false | _ | _ | _ | _ = case eq of λ ()
 ... | true | true | true | false | _ | _ | _ = case eq of λ ()
 ... | true | true | true | true | false | _ | _ = case eq of λ ()
 ... | true | true | true | true | true | yes _ | _ = case eq of λ ()
 ... | true | true | true | true | true | no _ | just _ = case eq of λ ()

 -- Return, exception and result observations change only raw-worker metadata.
 return-preserves : ∀ w s {t} → SA.observeReturn w s ≡ just t → Valid s → Valid t
 return-preserves w s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.completedHandshake (Shared.connected _) = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.completedHandshake (Shared.disconnected _) = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.acquireMap = case eq of λ ()
 ...   | SA.calling | Shared.count _ = case eq of λ ()
 ...   | SA.calling | Shared.prepare _ = case eq of λ ()
 ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
 ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket _ = case eq of λ ()
 ...   | SA.calling | Shared.finished _ = case eq of λ ()
 ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
 ...   | SA.calling | Shared.awaitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
 ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
 ...   | SA.closeDisconnected | _ = case eq of λ ()
 ...   | SA.closeException _ | _ = case eq of λ ()
 ...   | SA.closePrefix _ _ | _ = case eq of λ ()
 ...   | SA.bodyExited _ | _ = case eq of λ ()
 ...   | SA.resultAvailable _ | _ = case eq of λ ()
 return-preserves w s eq valid | nothing | _ = case eq of λ ()
 return-preserves w s eq valid | just _ | nothing = case eq of λ ()
 prefix-return-preserves : ∀ w s {t} → SA.prefixReturned w s ≡ just t → Valid s → Valid t
 prefix-return-preserves w s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.closeSocket Shared.hardLimitReached = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.acquireMap = case eq of λ ()
 ...   | SA.calling | Shared.count _ = case eq of λ ()
 ...   | SA.calling | Shared.prepare _ = case eq of λ ()
 ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
 ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
 ...   | SA.calling | Shared.finished _ = case eq of λ ()
 ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
 ...   | SA.calling | Shared.awaitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
 ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.completedHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket Shared.forbidden = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket Shared.forkFailed = case eq of λ ()
 ...   | SA.closeDisconnected | _ = case eq of λ ()
 ...   | SA.closeException _ | _ = case eq of λ ()
 ...   | SA.closePrefix _ _ | _ = case eq of λ ()
 ...   | SA.bodyExited _ | _ = case eq of λ ()
 ...   | SA.resultAvailable _ | _ = case eq of λ ()
 prefix-return-preserves w s eq valid | nothing | _ = case eq of λ ()
 prefix-return-preserves w s eq valid | just _ | nothing = case eq of λ ()
 prefix-exception-preserves : ∀ w err s {t} → SA.prefixException w err s ≡ just t → Valid s → Valid t
 prefix-exception-preserves w err s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.closeSocket Shared.forbidden = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.closeSocket Shared.forkFailed = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.acquireMap = case eq of λ ()
 ...   | SA.calling | Shared.count _ = case eq of λ ()
 ...   | SA.calling | Shared.prepare _ = case eq of λ ()
 ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
 ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
 ...   | SA.calling | Shared.finished _ = case eq of λ ()
 ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
 ...   | SA.calling | Shared.awaitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
 ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.completedHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket Shared.hardLimitReached = case eq of λ ()
 ...   | SA.closeDisconnected | _ = case eq of λ ()
 ...   | SA.closeException _ | _ = case eq of λ ()
 ...   | SA.closePrefix _ _ | _ = case eq of λ ()
 ...   | SA.bodyExited _ | _ = case eq of λ ()
 ...   | SA.resultAvailable _ | _ = case eq of λ ()
 prefix-exception-preserves w err s eq valid | nothing | _ = case eq of λ ()
 prefix-exception-preserves w err s eq valid | just _ | nothing = case eq of λ ()
 exception-preserves : ∀ w err s {t} → SA.observeException w err s ≡ just t → Valid s → Valid t
 exception-preserves w err s eq valid with lookup w (SA.workers s) | lookup w (Shared.admissions (SA.shared s))
 ... | just worker | just a with SA.pc worker | Shared.pc a
 ...   | SA.calling | Shared.awaitHandshake _ _ = case just-injective eq of λ { refl → valid }
 ...   | SA.calling | Shared.acquireMap = case eq of λ ()
 ...   | SA.calling | Shared.count _ = case eq of λ ()
 ...   | SA.calling | Shared.prepare _ = case eq of λ ()
 ...   | SA.calling | Shared.selectEntry _ _ = case eq of λ ()
 ...   | SA.calling | Shared.forkHandler _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.publish _ _ _ = case eq of λ ()
 ...   | SA.calling | Shared.reject _ _ = case eq of λ ()
 ...   | SA.calling | Shared.closeSocket _ = case eq of λ ()
 ...   | SA.calling | Shared.finished _ = case eq of λ ()
 ...   | SA.calling | Shared.countPublished _ _ = case eq of λ ()
 ...   | SA.calling | Shared.commitHandshake _ _ = case eq of λ ()
 ...   | SA.calling | Shared.countHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.notifyInbound _ = case eq of λ ()
 ...   | SA.calling | Shared.returnHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.completedHandshake _ = case eq of λ ()
 ...   | SA.calling | Shared.impossibleHandshake = case eq of λ ()
 ...   | SA.closeDisconnected | _ = case eq of λ ()
 ...   | SA.closeException _ | _ = case eq of λ ()
 ...   | SA.closePrefix _ _ | _ = case eq of λ ()
 ...   | SA.bodyExited _ | _ = case eq of λ ()
 ...   | SA.resultAvailable _ | _ = case eq of λ ()
 exception-preserves w err s eq valid | nothing | _ = case eq of λ ()
 exception-preserves w err s eq valid | just _ | nothing = case eq of λ ()
 result-preserves : ∀ w s {t} → SA.publishWorkerResult w s ≡ just t → Valid s → Valid t
 result-preserves w s eq valid with lookup w (SA.workers s)
 ... | nothing = case eq of λ ()
 ... | just worker with SA.pc worker
 ...   | SA.bodyExited r = case just-injective eq of λ { refl → valid }
 ...   | SA.calling = case eq of λ ()
 ...   | SA.closeDisconnected = case eq of λ ()
 ...   | SA.closeException _ = case eq of λ ()
 ...   | SA.closePrefix _ _ = case eq of λ ()
 ...   | SA.resultAvailable _ = case eq of λ ()

 -- Both successful/uncertain socket observations preserve the capture map.
 enact-close-preserves : ∀ w worker outcome next s → Valid s →
   Valid (SA.enactClose w worker outcome next s)
 enact-close-preserves w worker outcome next s valid = Lower.source-quiet isBearerClosed
   (record (SA.source s) { core = Machine.replaceWorld (O.core (SA.source s)) (record (SA.shared s)
     { sockets = put (Shared.socketRef (SA.request worker)) (SA.socketOutcome outcome) (Shared.sockets (SA.shared s)) }) })
   (SA.base s) refl refl refl valid
 enact-prefix-preserves : ∀ w worker result outcome s {t} → SA.enactPrefixClose w worker result outcome s ≡ just t →
   Valid s → Valid t
 enact-prefix-preserves w worker result nothing s eq valid with N.step
   (SA.runMachine (Machine.admissionStep w Admission.close)) (SA.base s) in advanced
 ... | nothing = case eq of λ ()
 ... | just n = case just-injective eq of λ { refl → PublishFacts.step-preserves (SA.runMachine (Machine.admissionStep w Admission.close)) (SA.base s) advanced valid }
 enact-prefix-preserves w worker result (just err) s eq valid = case just-injective eq of λ
   { refl → enact-close-preserves w worker (just err) (SA.prefixCloseFailed result err) s valid }
 close-prefix-preserves : ∀ w worker failure result outcome s {t} →
   SA.closePrefixWorker w worker failure result outcome s ≡ just t → Valid s → Valid t
 close-prefix-preserves w worker failure result outcome s eq valid with SA.prefixMatches w failure s
 ... | false = case eq of λ ()
 ... | true = enact-prefix-preserves w worker result outcome s eq valid
 close-preserves : ∀ w outcome s {t} → SA.closeWorker w outcome s ≡ just t → Valid s → Valid t
 close-preserves w outcome s eq valid with lookup w (SA.workers s)
 ... | nothing = case eq of λ ()
 ... | just worker with SA.pc worker
 ...   | SA.closeDisconnected = case just-injective eq of λ
   { refl → enact-close-preserves w worker outcome (SA.nextNormal outcome) s valid }
 ...   | SA.closeException err = case just-injective eq of λ
   { refl → enact-close-preserves w worker outcome (SA.nextException err outcome) s valid }
 ...   | SA.closePrefix f r = close-prefix-preserves w worker f r outcome s eq valid
 ...   | SA.calling = case eq of λ ()
 ...   | SA.bodyExited _ = case eq of λ ()
 ...   | SA.resultAvailable _ = case eq of λ ()
 inherit-preserves : ∀ a s {t} → SA.inherit a s ≡ just t → Valid s → Valid t
 inherit-preserves a s eq valid with SA.allowed a s
 ... | false = case eq of λ ()
 ... | true with N.step a (SA.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just n = case just-injective eq of λ { refl → PublishFacts.step-preserves a (SA.base s) actual valid }
 scope-enact-preserves : ∀ p s {t} → SA.enactScope p s ≡ just t → Valid s → Valid t
 scope-enact-preserves p s eq valid with SA.physicalAction p
 ... | nothing = case just-injective eq of λ { refl → valid }
 ... | just command with N.step command (SA.base s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just n = case just-injective eq of λ { refl → PublishFacts.step-preserves command (SA.base s) actual valid }
 scope-preserves : ∀ a s {t} → SA.scopeAdvance a s ≡ just t → Valid s → Valid t
 scope-preserves a s eq valid with SA.chooseScope a s
 ... | nothing = case eq of λ ()
 ... | just p = scope-enact-preserves p s eq valid
 step-preserves : ∀ a s {t} → SA.step a s ≡ just t → Valid s → Valid t
 step-preserves (SA.acceptedFork w req) = fork-preserves w req
 step-preserves (SA.run a) = inherit-preserves a
 step-preserves (SA.workerReturned w) = return-preserves w
 step-preserves (SA.workerPrefixReturned w) = prefix-return-preserves w
 step-preserves (SA.workerPrefixException w err) = prefix-exception-preserves w err
 step-preserves (SA.workerException w err) = exception-preserves w err
 step-preserves (SA.workerClose w outcome) = close-preserves w outcome
 step-preserves (SA.workerResult w) = result-preserves w
 step-preserves (SA.scope a) = scope-preserves a
 initialized-valid : ∀ c {s} → SA.initial c ≡ just s → Valid s
 initialized-valid c eq with Shared.admissions (Machine.world (O.core c)) | Shared.sockets (Machine.world (O.core c)) | N.initial c in lower
 ... | [] | [] | just n = case just-injective eq of λ { refl → PublishFacts.initialized-valid c lower }
 ... | _ ∷ _ | _ | _ = case eq of λ ()
 ... | [] | _ ∷ _ | _ = case eq of λ ()
 ... | [] | [] | nothing = case eq of λ ()

-- IG exit plans delegate physical changes or update only their own metadata.
module IGExit (b : ErrorId → Bool) where
 private module E = IGExitModel b using (clearPending; source; State; abandon; ownFailure; base; choose; delegate; enact; finish; initial; local; step)
 private module SA = AdmissionModel b using (initial; setSource; step; base)
 private module N = PublicationModel b using (raw)
 private module ServerFacts = Server b using (Valid; initialized-valid; step-preserves)
 Valid : E.State → Set
 Valid s = ServerFacts.Valid (E.base s)
 enact-preserves : ∀ p s {t} → E.enact p s ≡ just t → Valid s → Valid t
 enact-preserves (E.delegate a e) s eq valid with SA.step a (E.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just server = case just-injective eq of λ { refl → ServerFacts.step-preserves a (E.base s) actual valid }
 enact-preserves (E.local e) s eq valid = case just-injective eq of λ { refl → valid }
 enact-preserves (E.abandon r) s eq valid = case just-injective eq of λ { refl →
   Lower.source-quiet b (E.clearPending (E.source s)) (SA.base (E.base s)) refl refl refl valid }
 enact-preserves (E.ownFailure r f) s eq valid = case just-injective eq of λ { refl →
   Lower.source-quiet b (E.clearPending (E.source s)) (SA.base (E.base s)) refl refl refl valid }
 enact-preserves (E.finish e) s eq valid = case just-injective eq of λ { refl → valid }
 step-preserves : ∀ a s {t} → E.step a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid with E.choose a s
 ... | nothing = case eq of λ ()
 ... | just p = enact-preserves p s eq valid
 initialized-valid : ∀ c {s} → E.initial c ≡ just s → Valid s
 initialized-valid c eq with Machine.inboundRelease (O.core c) | Machine.remoteCall (O.core c) | SA.initial c in lower
 ... | nothing | nothing | just a = case just-injective eq of λ { refl → ServerFacts.initialized-valid c lower }
 ... | just _ | _ | _ = case eq of λ ()
 ... | nothing | just _ | _ = case eq of λ ()
 ... | nothing | nothing | nothing = case eq of λ ()

-- The shared composition routes every CM write through the actual Server step.
module SharedLayer (b io : ErrorId → Bool) where
 private module K = SharedModel b io using (State; coreAction; coreAllowed; coreStep; initial; peerAllowed; peerOpen; peerStep; peers; server; serverAllowed; serverStep; setSource; step)
 private module E = IGExitModel b using (initial; step)
 private module PS = PeerModel io using (cm; step)
 private module ExitFacts = IGExit b using (Valid; initialized-valid; step-preserves)
 private module PeerFacts = CleanupPeers io using (cleanups-same)
 private module Permission = OriginRuntime.Frontend b io (λ _ _ → false) using (peer-permission)
 private module SA = AdmissionModel b using (base)
 private module EX = IGExitModel b using (base)
 private module N = PublicationModel b using (raw)
 unwind : K.State → UnwindModel.State b
 unwind s = N.raw (SA.base (EX.base (K.server s)))
 Valid : K.State → Set
 Valid s = ExitFacts.Valid (K.server s)
 step-preserves : ∀ a s {t} → K.step a s ≡ just t → Valid s → Valid t
 step-preserves (K.serverStep a) s eq valid with K.serverAllowed a s
 ... | false = case eq of λ ()
 ... | true with E.step a (K.server s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just e = case just-injective eq of λ { refl → ExitFacts.step-preserves a (K.server s) actual valid }
 step-preserves (K.coreStep a) s eq valid with K.coreAllowed a s
 ... | false = case eq of λ ()
 ... | true with E.step (K.coreAction a) (K.server s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just e = case just-injective eq of λ { refl → ExitFacts.step-preserves (K.coreAction a) (K.server s) actual valid }
 step-preserves (K.peerStep a) s eq valid with K.peerOpen s | K.peerAllowed a s in allowed
 ... | false | _ = case eq of λ ()
 ... | true | false = case eq of λ ()
 ... | true | true with PS.step a (K.peers s) in actual
 ...   | nothing = case eq of λ ()
 ...   | just p = case just-injective eq of λ { refl → Peer.preserve b io a (K.peers s) actual (SA.base (EX.base (K.server s))) refl valid }
 initialized-valid : ∀ c g {s} → K.initial c g ≡ just s → Valid s
 initialized-valid c g eq with E.initial c in lower
 ... | nothing = case eq of λ ()
 ... | just e = case just-injective eq of λ { refl → ExitFacts.initialized-valid c lower }



import ConnectionManagement.Rules.PeerActions
open import Data.Nat using (ℕ)
module Frontend (b io : ErrorId → Bool) (capability : HandleId → ℕ → Bool) where
 private module T = SharedModel.Protocols b io capability using (Runs; Runtime; advance; base; birth; cacheResult; caller; calls; choose; complete; deliverTraceFault; descriptor; enact; front; handleRef; inherit; initialize; latest; local; more; mux; owner; peerRef; publication; reading; sourceOf; stop; traceFault)
 private module K = SharedModel b io using (State; context; coreAction; coreAllowed; coreStep; initial; peerAllowed; peerOpen; peerStep; peers; server; serverAllowed; serverStep; source; step)
 private module N = PublicationModel b using (module C; module R; State; base; captured; failures; initial; publicationState; raw; source; step)
 private module F = Failure b using (Covers; Valid; captures; descriptor; frames; negotiated; snapshot; snapshots; failure-valid; view)
 private module PS = PeerModel io using (cm; step)
 private module Combined = SharedLayer b io using (initialized-valid; step-preserves)
 publication : T.Runtime → N.State
 publication s = T.publication (T.base s)
 Valid : T.Runtime → Set
 Valid s = F.Valid (publication s)
 snapshots : T.Runtime → Set
 snapshots s = F.Covers (N.failures (publication s)) (F.view (publication s)) (T.sourceOf s)
 cache-snapshots : ∀ rid r result front s → F.Valid (T.publication s) →
   F.Covers (N.failures (T.publication (T.cacheResult rid r result front s)))
     (F.view (T.publication (T.cacheResult rid r result front s))) (K.source (T.cacheResult rid r result front s))
 cache-snapshots rid r result front s valid with T.latest (T.owner r) (number (T.descriptor r)) (T.calls front)
 ... | nothing = F.snapshots valid
 ... | just (current , _) with current ≟ rid
 ...   | no _ = F.snapshots valid
 ...   | yes _ with lookup (T.peerRef r) (PeerContext.SubContext.peers (PeerContext.subsystem (K.context s)))
 ...     | nothing = F.snapshots valid
 ...     | just peer with ConnectionManagement.Rules.PeerActions.handleRef peer ≟ T.handleRef r |
   ConnectionManagement.Rules.PeerActions.muxRef peer ≟ T.mux r
 ...       | yes _ | yes _ with ConnectionManagement.Rules.PeerActions.finishRun (number (T.descriptor r)) result (ConnectionManagement.Rules.PeerActions.runs peer)
 ...         | nothing = F.snapshots valid
 ...         | just rs = F.snapshots valid
 cache-snapshots rid r result front s valid | just (current , _) | yes _ | just peer | no _ | _ = F.snapshots valid
 cache-snapshots rid r result front s valid | just (current , _) | yes _ | just peer | yes _ | no _ = F.snapshots valid
 enact-snapshots : ∀ p s {t} → T.enact p s ≡ just t → Valid s → snapshots t
 enact-snapshots (T.inherit a front) s eq valid with K.step a (T.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just k = case just-injective eq of λ { refl → F.snapshots (Combined.step-preserves a (T.base s) actual valid) }
 enact-snapshots (T.caller a front) s eq valid with PS.step a (K.peers (T.base s)) in actual
 ... | nothing = case eq of λ ()
 ... | just peer = case just-injective eq of λ { refl → Peer.snapshots b io a (K.peers (T.base s)) actual _ _ (F.snapshots valid) }
 enact-snapshots (T.local front) s eq valid = case just-injective eq of λ { refl → F.snapshots valid }
 enact-snapshots (T.reading results) s eq valid = case just-injective eq of λ { refl → F.snapshots valid }
 enact-snapshots (T.traceFault w rid result fs) s eq valid = case just-injective eq of λ { refl → F.snapshots valid }
 enact-snapshots (T.deliverTraceFault w rid result fs coordinator) s eq valid = case just-injective eq of λ { refl → F.snapshots valid }
 enact-snapshots (T.birth w ownerFrame pool j rid r front) s eq valid = case just-injective eq of λ { refl → F.snapshots valid }
 enact-snapshots (T.complete a rid r result) s eq valid with K.step a (T.base s) in actual
 ... | nothing = case eq of λ ()
 ... | just k = case just-injective eq of λ { refl → cache-snapshots rid r result (T.front s) k (Combined.step-preserves a (T.base s) actual valid) }
 step-snapshots : ∀ a s {t} → T.advance a s ≡ just t → Valid s → snapshots t
 step-snapshots a s eq valid with T.choose a s
 ... | nothing = case eq of λ ()
 ... | just p = enact-snapshots p s eq valid
 step-preserves : ∀ a s {t} → T.advance a s ≡ just t → Valid s → Valid t
 step-preserves a s eq valid = F.failure-valid
   (Frame.Frontend.step-preserves b io capability a s eq (F.frames valid))
   (Capture.Frontend.step-preserves b io capability a s eq (F.captures valid)) (step-snapshots a s eq valid)
 initialized-valid : ∀ c g {s} → T.initialize c g ≡ just s → Valid s
 initialized-valid c g eq with K.initial c g in lower
 ... | nothing = case eq of λ ()
 ... | just k = case just-injective eq of λ { refl → Combined.initialized-valid c g lower }
 run-preserves : ∀ {s events t} → T.Runs s events t → Valid s → Valid t
 run-preserves T.stop valid = valid
 run-preserves (T.more {s = s} {a = a} actual rest) valid = run-preserves rest (step-preserves a s actual valid)
 from-initial : ∀ c g {start events s} → T.initialize c g ≡ just start → T.Runs start events s → Valid s
 from-initial c g initialized path = run-preserves path (initialized-valid c g initialized)

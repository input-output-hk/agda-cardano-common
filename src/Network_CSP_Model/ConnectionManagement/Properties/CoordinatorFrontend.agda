{-# OPTIONS --guardedness #-}

-- SI5b, upper half: the coordinator frame lifted through the Server, the IG
-- exit wrapper, the shared Server/peer composition and the runtime frontend.
-- The runtime's own trace-fault delivery acknowledges through the exit
-- wrapper; its chosen plan carries that real acknowledgment.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.CoordinatorFrontend (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
import Data.Nat as Nat
open import Data.Product using (Σ; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (worker; local; mux; job; entry)
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.IGTypes using (clean; errored; number)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.PeerActions as Peer
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.MuxHandlerSupervision as MuxModel
import ConnectionManagement.MuxProtocolJobs as ProtocolModel
import ConnectionManagement.MuxResultMonitor as MonitorModel
import ConnectionManagement.MuxGroupShutdown as GroupModel
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.MuxStartupUnwind as UnwindModel
import ConnectionManagement.MuxPublicationUnwind as PublicationModel
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Properties.CoordinatorFrames as Frames
import ConnectionManagement.Properties.ServerShutdownComplete as Complete
private
  module Low = Frames isBearerClosed
  module S = Server isBearerClosed
  module E = Exit isBearerClosed
  module K = Combined isBearerClosed isIOManagerError
  module PS = Supervision isIOManagerError
  module C = Context isIOManagerError
  module N = PublicationModel isBearerClosed
  module W = ExitModel isBearerClosed
  module R = UnwindModel isBearerClosed
  module G = GroupModel isBearerClosed
  module Monitor = MonitorModel isBearerClosed
  module U = MuxModel Types.TypedResult
  module P = ProtocolModel
  module Pool = ProtocolModel.Pool
  module SI5a = Complete isBearerClosed isIOManagerError
open Low using (Frame; stay; same; compose; control-frame; publication-frame) public

-- Server: worker metadata keeps the coordinator; inherited and IG-cleanup
-- steps are publication steps.
coordS : S.State → Close.State
coordS s = Low.coordN (S.base s)

fork-frame : ∀ w req s {t} → S.forkAccepted w req s ≡ just t → Frame (coordS s) (coordS t)
fork-frame w req s eq with S.accepting (S.stage s) | S.listenerOpen s |
  S.sameLimit req (S.workers s) | S.fresh w s | S.fresh (Shared.child req) s |
  w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (S.shared s))
... | true | true | true | true | true | no _ | nothing =
  case just-injective eq of λ { refl → stay _ }
... | false | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | true | false | _ | _ | _ | _ | _ = case eq of λ ()
... | true | true | false | _ | _ | _ | _ = case eq of λ ()
... | true | true | true | false | _ | _ | _ = case eq of λ ()
... | true | true | true | true | false | _ | _ = case eq of λ ()
... | true | true | true | true | true | yes _ | _ = case eq of λ ()
... | true | true | true | true | true | no _ | just _ = case eq of λ ()

inherit-frame : ∀ a s {t} → S.inherit a s ≡ just t → Frame (coordS s) (coordS t)
inherit-frame a s eq with S.allowed a s
... | false = case eq of λ ()
... | true with N.step a (S.base s) in advanced
...   | nothing = case eq of λ ()
...   | just n = case just-injective eq of λ { refl → publication-frame a (S.base s) advanced }

-- Return, exception and result observations change only raw-worker metadata.
body-restore-frame : ∀ w s {t} → S.restoreWorker w s ≡ just t → Frame (coordS s) (coordS t)
body-restore-frame w s eq with lookup w (S.workers s)
... | nothing = case eq of λ ()
... | just worker with S.pc worker
...   | S.closePrefix Shared.bodyFailed (S.raised fault) with N.step (S.runMachine (Machine.admissionStep w Admission.restoreBody)) (S.base s) in actual
...     | nothing = case eq of λ ()
...     | just n = case just-injective eq of λ { refl → publication-frame (S.runMachine (Machine.admissionStep w Admission.restoreBody)) (S.base s) actual }
body-restore-frame w s eq | just worker | S.calling = case eq of λ ()
body-restore-frame w s eq | just worker | S.closeDisconnected = case eq of λ ()
body-restore-frame w s eq | just worker | S.closeException fault = case eq of λ ()
body-restore-frame w s eq | just worker | S.closePrefix Shared.hardLimitReached result = case eq of λ ()
body-restore-frame w s eq | just worker | S.closePrefix Shared.forbidden result = case eq of λ ()
body-restore-frame w s eq | just worker | S.closePrefix Shared.forkFailed result = case eq of λ ()
body-restore-frame w s eq | just worker | S.closePrefix Shared.bodyFailed S.returned = case eq of λ ()
body-restore-frame w s eq | just worker | S.bodyExited result = case eq of λ ()
body-restore-frame w s eq | just worker | S.resultAvailable result = case eq of λ ()

return-frame : ∀ w s {t} → S.observeReturn w s ≡ just t → Frame (coordS s) (coordS t)
return-frame w s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.completedHandshake (Shared.connected _) = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.completedHandshake (Shared.disconnected _) = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.acquireMap = case eq of λ ()
...   | S.calling | Shared.count _ = case eq of λ ()
...   | S.calling | Shared.prepare _ = case eq of λ ()
...   | S.calling | Shared.selectEntry _ _ = case eq of λ ()
...   | S.calling | Shared.forkHandler _ _ _ = case eq of λ ()
...   | S.calling | Shared.publish _ _ _ = case eq of λ ()
...   | S.calling | Shared.reject _ _ = case eq of λ ()
...   | S.calling | Shared.closeSocket _ = case eq of λ ()
...   | S.calling | Shared.finished _ = case eq of λ ()
...   | S.calling | Shared.countPublished _ _ = case eq of λ ()
...   | S.calling | Shared.awaitHandshake _ _ = case eq of λ ()
...   | S.calling | Shared.commitHandshake _ _ = case eq of λ ()
...   | S.calling | Shared.countHandshake _ = case eq of λ ()
...   | S.calling | Shared.notifyInbound _ = case eq of λ ()
...   | S.calling | Shared.returnHandshake _ = case eq of λ ()
...   | S.calling | Shared.impossibleHandshake = case eq of λ ()
...   | S.closeDisconnected | _ = case eq of λ ()
...   | S.closeException _ | _ = case eq of λ ()
...   | S.closePrefix _ _ | _ = case eq of λ ()
...   | S.bodyExited _ | _ = case eq of λ ()
...   | S.resultAvailable _ | _ = case eq of λ ()
return-frame w s eq | nothing | _ = case eq of λ ()
return-frame w s eq | just _ | nothing = case eq of λ ()
prefix-return-frame : ∀ w s {t} → S.prefixReturned w s ≡ just t → Frame (coordS s) (coordS t)
prefix-return-frame w s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.closeSocket Shared.hardLimitReached = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.acquireMap = case eq of λ ()
...   | S.calling | Shared.count _ = case eq of λ ()
...   | S.calling | Shared.prepare _ = case eq of λ ()
...   | S.calling | Shared.selectEntry _ _ = case eq of λ ()
...   | S.calling | Shared.forkHandler _ _ _ = case eq of λ ()
...   | S.calling | Shared.publish _ _ _ = case eq of λ ()
...   | S.calling | Shared.reject _ _ = case eq of λ ()
...   | S.calling | Shared.finished _ = case eq of λ ()
...   | S.calling | Shared.countPublished _ _ = case eq of λ ()
...   | S.calling | Shared.awaitHandshake _ _ = case eq of λ ()
...   | S.calling | Shared.commitHandshake _ _ = case eq of λ ()
...   | S.calling | Shared.countHandshake _ = case eq of λ ()
...   | S.calling | Shared.notifyInbound _ = case eq of λ ()
...   | S.calling | Shared.returnHandshake _ = case eq of λ ()
...   | S.calling | Shared.completedHandshake _ = case eq of λ ()
...   | S.calling | Shared.impossibleHandshake = case eq of λ ()
...   | S.calling | Shared.closeSocket Shared.bodyFailed = case eq of λ ()
...   | S.calling | Shared.closeSocket Shared.forbidden = case eq of λ ()
...   | S.calling | Shared.closeSocket Shared.forkFailed = case eq of λ ()
...   | S.closeDisconnected | _ = case eq of λ ()
...   | S.closeException _ | _ = case eq of λ ()
...   | S.closePrefix _ _ | _ = case eq of λ ()
...   | S.bodyExited _ | _ = case eq of λ ()
...   | S.resultAvailable _ | _ = case eq of λ ()
prefix-return-frame w s eq | nothing | _ = case eq of λ ()
prefix-return-frame w s eq | just _ | nothing = case eq of λ ()
prefix-exception-frame : ∀ w err s {t} → S.prefixException w err s ≡ just t → Frame (coordS s) (coordS t)
prefix-exception-frame w err s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.closeSocket Shared.bodyFailed = case eq of λ ()
...   | S.calling | Shared.closeSocket Shared.forbidden = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.closeSocket Shared.forkFailed = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.acquireMap = case eq of λ ()
...   | S.calling | Shared.count _ = case eq of λ ()
...   | S.calling | Shared.prepare _ = case eq of λ ()
...   | S.calling | Shared.selectEntry _ _ = case eq of λ ()
...   | S.calling | Shared.forkHandler _ _ _ = case eq of λ ()
...   | S.calling | Shared.publish _ _ _ = case eq of λ ()
...   | S.calling | Shared.reject _ _ = case eq of λ ()
...   | S.calling | Shared.finished _ = case eq of λ ()
...   | S.calling | Shared.countPublished _ _ = case eq of λ ()
...   | S.calling | Shared.awaitHandshake _ _ = case eq of λ ()
...   | S.calling | Shared.commitHandshake _ _ = case eq of λ ()
...   | S.calling | Shared.countHandshake _ = case eq of λ ()
...   | S.calling | Shared.notifyInbound _ = case eq of λ ()
...   | S.calling | Shared.returnHandshake _ = case eq of λ ()
...   | S.calling | Shared.completedHandshake _ = case eq of λ ()
...   | S.calling | Shared.impossibleHandshake = case eq of λ ()
...   | S.calling | Shared.closeSocket Shared.hardLimitReached = case eq of λ ()
...   | S.closeDisconnected | _ = case eq of λ ()
...   | S.closeException _ | _ = case eq of λ ()
...   | S.closePrefix _ _ | _ = case eq of λ ()
...   | S.bodyExited _ | _ = case eq of λ ()
...   | S.resultAvailable _ | _ = case eq of λ ()
prefix-exception-frame w err s eq | nothing | _ = case eq of λ ()
prefix-exception-frame w err s eq | just _ | nothing = case eq of λ ()
exception-frame : ∀ w err s {t} → S.observeException w err s ≡ just t → Frame (coordS s) (coordS t)
exception-frame w err s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.awaitHandshake _ _ = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.acquireMap = case eq of λ ()
...   | S.calling | Shared.count _ = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.prepare _ = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.selectEntry _ _ = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.forkHandler _ _ _ = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.publish _ _ _ = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.reject _ _ = case eq of λ ()
...   | S.calling | Shared.closeSocket _ = case eq of λ ()
...   | S.calling | Shared.finished _ = case eq of λ ()
...   | S.calling | Shared.countPublished _ _ = case just-injective eq of λ { refl → stay _ }
...   | S.calling | Shared.commitHandshake _ _ = case eq of λ ()
...   | S.calling | Shared.countHandshake _ = case eq of λ ()
...   | S.calling | Shared.notifyInbound _ = case eq of λ ()
...   | S.calling | Shared.returnHandshake _ = case eq of λ ()
...   | S.calling | Shared.completedHandshake _ = case eq of λ ()
...   | S.calling | Shared.impossibleHandshake = case eq of λ ()
...   | S.closeDisconnected | _ = case eq of λ ()
...   | S.closeException _ | _ = case eq of λ ()
...   | S.closePrefix _ _ | _ = case eq of λ ()
...   | S.bodyExited _ | _ = case eq of λ ()
...   | S.resultAvailable _ | _ = case eq of λ ()
exception-frame w err s eq | nothing | _ = case eq of λ ()
exception-frame w err s eq | just _ | nothing = case eq of λ ()
result-frame : ∀ w s {t} → S.publishWorkerResult w s ≡ just t → Frame (coordS s) (coordS t)
result-frame w s eq with lookup w (S.workers s)
... | nothing = case eq of λ ()
... | just worker with S.pc worker
...   | S.bodyExited r = case just-injective eq of λ { refl → stay _ }
...   | S.calling = case eq of λ ()
...   | S.closeDisconnected = case eq of λ ()
...   | S.closeException _ = case eq of λ ()
...   | S.closePrefix _ _ = case eq of λ ()
...   | S.resultAvailable _ = case eq of λ ()

enact-prefix-frame : ∀ w worker result outcome s {t} → S.enactPrefixClose w worker result outcome s ≡ just t →
  Frame (coordS s) (coordS t)
enact-prefix-frame w worker result nothing s eq with N.step
  (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) in advanced
... | nothing = case eq of λ ()
... | just n = case just-injective eq of λ { refl →
  publication-frame (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) advanced }
enact-prefix-frame w worker result (just err) s eq = case just-injective eq of λ { refl → stay _ }
close-prefix-frame : ∀ w worker failure result outcome s {t} →
  S.closePrefixWorker w worker failure result outcome s ≡ just t → Frame (coordS s) (coordS t)
close-prefix-frame w worker failure result outcome s eq with S.prefixMatches w failure s
... | false = case eq of λ ()
... | true = enact-prefix-frame w worker result outcome s eq
close-frame : ∀ w outcome s {t} → S.closeWorker w outcome s ≡ just t → Frame (coordS s) (coordS t)
close-frame w outcome s eq with lookup w (S.workers s)
... | nothing = case eq of λ ()
... | just worker with S.pc worker
...   | S.closeDisconnected = case just-injective eq of λ { refl → stay _ }
...   | S.closeException err = case just-injective eq of λ { refl → stay _ }
...   | S.closePrefix f r = close-prefix-frame w worker f r outcome s eq
...   | S.calling = case eq of λ ()
...   | S.bodyExited _ = case eq of λ ()
...   | S.resultAvailable _ = case eq of λ ()


-- Socket-only scopes retain this observer; physical scopes use the old lift.
enact-scope-frame : ∀ p s {t} → S.enactScope p s ≡ just t → Frame (coordS s) (coordS t)
enact-scope-frame (S.scopePlan st keep ig nothing) s eq = case just-injective eq of λ { refl → stay _ }
enact-scope-frame (S.scopePlan st keep ig (just a)) s eq with N.step a (S.base s) in advanced
... | nothing = case eq of λ ()
... | just n = case just-injective eq of λ { refl → publication-frame a (S.base s) advanced }
enact-scope-frame (S.socketScopePlan st keep ig sock owner) s eq = case just-injective eq of λ { refl → stay _ }
scope-frame : ∀ x s {t} → S.scopeAdvance x s ≡ just t → Frame (coordS s) (coordS t)
scope-frame x s eq with S.chooseScope x s
... | nothing = case eq of λ ()
... | just p = enact-scope-frame p s eq
-- Pre-birth close preserves this observation.
fork-close-frame : ∀ outcome s {t} → S.closeFailedFork outcome s ≡ just t → Frame (coordS s) (coordS t)
fork-close-frame outcome s eq with S.failedForkSocket s
... | nothing = case eq of λ ()
... | just sock with S.isAcceptedSocket sock s
...   | false = case eq of λ ()
...   | true = case just-injective eq of λ { refl → stay _ }

server-frame : ∀ a s {t} → S.step a s ≡ just t → Frame (coordS s) (coordS t)
server-frame (S.closeForkFailure outcome) s eq = fork-close-frame outcome s eq
server-frame (S.acceptedFork w req) s eq = fork-frame w req s eq
server-frame (S.workerRestore w) s eq = body-restore-frame w s eq
server-frame (S.run a) s eq = inherit-frame a s eq
server-frame (S.workerReturned w) s eq = return-frame w s eq
server-frame (S.workerPrefixReturned w) s eq = prefix-return-frame w s eq
server-frame (S.workerPrefixException w err) s eq = prefix-exception-frame w err s eq
server-frame (S.workerException w err) s eq = exception-frame w err s eq
server-frame (S.workerClose w outcome) s eq = close-frame w outcome s eq
server-frame (S.workerResult w) s eq = result-frame w s eq
server-frame (S.scope x) s eq = scope-frame x s eq

-- IG exit wrapper.
coordE : E.State → Close.State
coordE s = coordS (E.base s)
ig-frame : ∀ a s {t} → E.step a s ≡ just t → Frame (coordE s) (coordE t)
ig-frame a s eq with E.choose a s
... | nothing = case eq of λ ()
... | just (E.delegate b e) with S.step b (E.base s) in actual
...   | nothing = case eq of λ ()
...   | just server = case just-injective eq of λ { refl → server-frame b (E.base s) actual }
ig-frame a s eq | just (E.local e) = case just-injective eq of λ { refl → stay _ }
ig-frame a s eq | just (E.abandon r) = case just-injective eq of λ { refl → stay _ }
ig-frame a s eq | just (E.ownFailure r f) = case just-injective eq of λ { refl → stay _ }
ig-frame a s eq | just (E.finish e) = case just-injective eq of λ { refl → stay _ }

-- Shared composition: peer steps write only the CM source.
coordK : K.State → Close.State
coordK s = coordE (K.server s)
shared-frame : ∀ a s {t} → K.step a s ≡ just t → Frame (coordK s) (coordK t)
shared-frame (K.serverStep a) s eq with K.serverAllowed a s
... | false = case eq of λ ()
... | true with E.step a (K.server s) in actual
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → ig-frame a (K.server s) actual }
shared-frame (K.coreStep a) s eq with K.coreAllowed a s
... | false = case eq of λ ()
... | true with E.step (K.coreAction a) (K.server s) in actual
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → ig-frame (K.coreAction a) (K.server s) actual }
shared-frame (K.peerStep a) s eq with K.peerOpen s ∧ K.peerAllowed a s
... | false = case eq of λ ()
... | true with PS.step a (K.peers s)
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → stay _ }

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  private
    module T = K.Protocols canInitiate
  coordT : T.Runtime → Close.State
  coordT s = coordK (T.base s)

  -- Only trace-fault delivery replaces the coordinator directly; its chosen
  -- plan carries the exit wrapper's actual acknowledgment.
  SafePlan : T.Plan → T.Runtime → Set
  SafePlan (T.deliverTraceFault w rid result fs coordinator) s = Σ W.State (λ target →
    W.control Close.acknowledgeDelivery (R.base (N.raw (T.publication (T.base s)))) ≡ just target ×
    coordinator ≡ W.shutdown target)
  SafePlan _ s = ⊤
  enact-frame : ∀ p s {t} → T.enact p s ≡ just t → SafePlan p s → Frame (coordT s) (coordT t)
  enact-frame (T.inherit a f) s eq safe with K.step a (T.base s) in actual
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → shared-frame a (T.base s) actual }
  enact-frame (T.caller a f) s eq safe with PS.step a (K.peers (T.base s))
  ... | nothing = case eq of λ ()
  ... | just p = case just-injective eq of λ { refl → stay _ }
  enact-frame (T.local f) s eq safe = case just-injective eq of λ { refl → stay _ }
  enact-frame (T.reading r) s eq safe = case just-injective eq of λ { refl → stay _ }
  enact-frame (T.traceFault w rid result fs) s eq safe = case just-injective eq of λ { refl → stay _ }
  enact-frame (T.deliverTraceFault w rid result fs coordinator) s eq (target , received , refl) =
    case just-injective eq of λ { refl → control-frame Close.acknowledgeDelivery (R.base (N.raw (T.publication (T.base s)))) received }
  enact-frame (T.birth w capturedFrame pool j rid r f) s eq safe = case just-injective eq of λ { refl → stay _ }
  enact-frame (T.complete a rid r result) s eq safe with K.step a (T.base s) in actual
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → compose (shared-frame a (T.base s) actual)
    (same (cong coordE (SI5a.Protocols.cache-server canInitiate rid r result (T.front s) b))) }

  fork-safe : ∀ w j s p → T.forkPlan w j s ≡ just p → SafePlan p s
  fork-safe w j s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s) |
    lookup w (U.frames (P.base (T.physical (T.base s)))) in ownerFrame-found
  ... | T.forkReadyC rid | true | just f with lookup rid (T.calls (T.front s)) in found |
    P.fresh j rid (T.physical (T.base s)) | P.noParent (P.poolAt w (T.physical (T.base s)))
  ...   | just r | true | true with T.owner r ≟ w | T.thread r | T.value r in empty | Pool.step (Pool.fork j) (P.poolAt w (T.physical (T.base s)))
  ...     | yes _ | nothing | nothing | just pool = case just-injective eq of λ { refl → tt }
  ...     | no _ | _ | _ | _ = case eq of λ ()
  ...     | yes _ | just thread | _ | _ = case eq of λ ()
  ...     | yes _ | nothing | just result | _ = case eq of λ ()
  ...     | yes _ | nothing | nothing | nothing = case eq of λ ()
  fork-safe w j s p eq | T.forkReadyC rid | true | just f | nothing | _ | _ = case eq of λ ()
  fork-safe w j s p eq | T.forkReadyC rid | true | just f | just r | false | _ = case eq of λ ()
  fork-safe w j s p eq | T.forkReadyC rid | true | just f | just r | true | false = case eq of λ ()
  fork-safe w j s p eq | T.idleC | _ | _ = case eq of λ ()
  fork-safe w j s p eq | T.selectedC rid | _ | _ = case eq of λ ()
  fork-safe w j s p eq | T.tracingC rid | _ | _ = case eq of λ ()
  fork-safe w j s p eq | T.registeringC rid target | _ | _ = case eq of λ ()
  fork-safe w j s p eq | T.failedC rid result | _ | _ = case eq of λ ()
  fork-safe w j s p eq | T.forkReadyC rid | false | _ = case eq of λ ()
  fork-safe w j s p eq | T.forkReadyC rid | true | nothing = case eq of λ ()


  select-safe : ∀ w s p → T.selectPlan w s ≡ just p → SafePlan p s
  select-safe w s p eq with T.idle w (T.front s) | T.pending w (T.front s) | T.controllerFree w (T.base s) |
    Monitor.ownerContext w (G.base (T.group (T.base s)))
  ... | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) with
    P.muxAt mid (T.physical (T.base s)) | P.noParent (P.poolAt w (T.physical (T.base s))) |
    P.noResults (P.poolAt w (T.physical (T.base s))) | Pool.phase (P.poolAt w (T.physical (T.base s)))
  ...   | just m | true | true | Pool.openPool with Mux.status m | Mux.callback m
  ...     | Mux.ready | Mux.returned = case just-injective eq of λ { refl → tt }
  ...     | Mux.stopping | _ = case eq of λ ()
  ...     | Mux.stopped | _ = case eq of λ ()
  ...     | Mux.failed err | _ = case eq of λ ()
  ...     | Mux.ready | Mux.readActive tr = case eq of λ ()
  ...     | Mux.ready | Mux.commitTrace active tr = case eq of λ ()
  ...     | Mux.ready | Mux.afterStart n = case eq of λ ()
  ...     | Mux.ready | Mux.forkPending n = case eq of λ ()
  ...     | Mux.ready | Mux.afterFailure = case eq of λ ()
  ...     | Mux.ready | Mux.tracerFailed n = case eq of λ ()
  select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | nothing | _ | _ | _ = case eq of λ ()
  select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | false | _ | _ = case eq of λ ()
  select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | false | _ = case eq of λ ()
  select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closing = case eq of λ ()
  select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.closedPool = case eq of λ ()
  select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.cancelPending j = case eq of λ ()
  select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | just (f , mid) | just m | true | true | Pool.joinPending j = case eq of λ ()
  select-safe w s p eq | false | _ | _ | _ = case eq of λ ()
  select-safe w s p eq | true | [] | _ | _ = case eq of λ ()
  select-safe w s p eq | true | T.command rid (Nat.suc n) ∷ rest | _ | _ = case eq of λ ()
  select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | false | _ = case eq of λ ()
  select-safe w s p eq | true | T.command rid Nat.zero ∷ rest | true | nothing = case eq of λ ()

  register-safe : ∀ j s p → T.registerPlan j s ≡ just p → SafePlan p s
  register-safe j s p eq with T.byThread j (T.calls (T.front s))
  ... | nothing = case eq of λ ()
  ... | just (rid , r) with T.cursor (T.owner r) (T.front s)
  ...   | T.registeringC actual target with rid ≟ actual | j ≟ target
  ...     | yes _ | yes _ = case just-injective eq of λ { refl → tt }
  ...     | no _ | _ = case eq of λ ()
  ...     | yes _ | no _ = case eq of λ ()
  register-safe j s p eq | just (rid , r) | T.idleC = case eq of λ ()
  register-safe j s p eq | just (rid , r) | T.selectedC gen = case eq of λ ()
  register-safe j s p eq | just (rid , r) | T.tracingC gen = case eq of λ ()
  register-safe j s p eq | just (rid , r) | T.forkReadyC gen = case eq of λ ()
  register-safe j s p eq | just (rid , r) | T.failedC gen result = case eq of λ ()

  completion-safe : ∀ j result s p → T.completionPlan j result s ≡ just p → SafePlan p s
  completion-safe j clean s p eq with T.byThread j (T.calls (T.front s)) in found |
    lookup j (P.jobs (T.physical (T.base s)))
  ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
    Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl → tt }
  ...   | just old | _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
  completion-safe j clean s p eq | nothing | _ = case eq of λ ()
  completion-safe j clean s p eq | just pair | nothing = case eq of λ ()

  completion-safe j (errored commitErr) s p eq with T.byThread j (T.calls (T.front s)) in found |
    lookup j (P.jobs (T.physical (T.base s)))
  ... | just (rid , r) | just job with T.value r in empty | Types.owner job ≟ T.owner r | Types.generation job ≟ rid |
    Types.protocolNumber job Nat.≟ number (T.descriptor r) | Types.direction job
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = case just-injective eq of λ { refl → tt }
  ...   | just old | _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | no _ | _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | no _ | _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | no _ | _ = case eq of λ ()
  ...   | nothing | yes _ | yes _ | yes _ | Mux.responderJob = case eq of λ ()
  completion-safe j (errored commitErr) s p eq | nothing | _ = case eq of λ ()
  completion-safe j (errored commitErr) s p eq | just pair | nothing = case eq of λ ()

  poll-safe : ∀ ref w s p → T.pollResultsPlan ref w s ≡ just p → SafePlan p s
  poll-safe ref w s p eq with T.readAllowed (Sub.pollPeer ref w) (T.base s) |
    lookup ref (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
    lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
  ... | true | just peer | nothing with Peer.status peer
  ...   | Peer.peerCold = case just-injective eq of λ { refl → tt }
  ...   | Peer.peerCooling = case just-injective eq of λ { refl → tt }
  ...   | Peer.peerWarm with T.firstPeer ref peer s
  ...     | nothing = case eq of λ ()
  ...     | just (kind , result) with T.cleanObservation result
  ...       | true = case just-injective eq of λ { refl → tt }
  ...       | false = case just-injective eq of λ { refl → tt }
  poll-safe ref w s p eq | true | just peer | nothing | Peer.peerHot with T.firstPeer ref peer s
  ...     | nothing = case eq of λ ()
  ...     | just (kind , result) with T.cleanObservation result
  ...       | true = case just-injective eq of λ { refl → tt }
  ...       | false = case just-injective eq of λ { refl → tt }
  poll-safe ref w s p eq | true | just peer | just f = case just-injective eq of λ { refl → tt }
  poll-safe ref w s p eq | false | _ | _ = case eq of λ ()
  poll-safe ref w s p eq | true | nothing | _ = case eq of λ ()

  job-wait-safe : ∀ j s p → T.waitJobPlan j s ≡ just p → SafePlan p s
  job-wait-safe j s p eq with lookup j (C.SubContext.jobs (C.subsystem (K.context (T.base s))))
  ... | nothing = case eq of λ ()
  ... | just jf with Sub.queued jf |
    lookup (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
    T.readAllowed (Sub.jobStep j (T.waitAction (Sub.execution jf))) (T.base s)
  ...   | false | just peer | true with T.waitResults (Sub.execution jf) peer s
  ...     | nothing = case eq of λ ()
  ...     | just results with T.allClean results
  ...       | true = case just-injective eq of λ { refl → tt }
  ...       | false = case just-injective eq of λ { refl → tt }
  job-wait-safe j s p eq | just jf | true | _ | _ = case eq of λ ()
  job-wait-safe j s p eq | just jf | false | nothing | _ = case eq of λ ()
  job-wait-safe j s p eq | just jf | false | just peer | false = case eq of λ ()

  monitor-wait-safe : ∀ ref s p → T.waitMonitorPlan ref s ≡ just p → SafePlan p s
  monitor-wait-safe ref s p eq with lookup ref (C.SubContext.monitors (C.subsystem (K.context (T.base s))))
  ... | nothing = case eq of λ ()
  ... | just f with lookup (J.connectionRef f) (C.SubContext.peers (C.subsystem (K.context (T.base s)))) in peerFound |
    T.readAllowed (Sub.monitorStep ref (T.waitAction f)) (T.base s)
  ...   | just peer | true with T.waitResults f peer s
  ...     | nothing = case eq of λ ()
  ...     | just results with T.allClean results
  ...       | true = case just-injective eq of λ { refl → tt }
  ...       | false = case just-injective eq of λ { refl → tt }
  monitor-wait-safe ref s p eq | just f | nothing | _ = case eq of λ ()
  monitor-wait-safe ref s p eq | just f | just peer | false = case eq of λ ()

  choose-safe : ∀ a s p → T.choose a s ≡ just p → SafePlan p s
  choose-safe (T.dispatch a) s p eq with T.inheritAllowed a s
  ... | false = case eq of λ ()
  ... | true = case just-injective eq of λ { refl → tt }
  choose-safe (T.startNext j rid) s p eq with K.peerOpen (T.base s) | T.nextRequest j (T.base s) |
    lookup rid (T.calls (T.front s)) in absent | P.generationFresh rid (P.jobs (T.physical (T.base s)))
  ... | true | just req | nothing | true with canInitiate (Peer.handleRef (T.peer req)) (number (T.protocol req)) |
    P.muxAt (Peer.muxRef (T.peer req)) (T.physical (T.base s))
  ...   | false | _ = case eq of λ ()
  ...   | true | nothing = case eq of λ ()
  ...   | true | just m with Mux.status m
  ...     | Mux.stopping = case eq of λ ()
  ...     | Mux.stopped = case eq of λ ()
  ...     | Mux.failed err = case eq of λ ()
  ...     | Mux.ready with T.slotIdle (T.worker req) (number (T.protocol req)) (T.front s)
  ...       | false = case eq of λ ()
  ...       | true = case just-injective eq of λ { refl → tt }
  choose-safe (T.startNext j rid) s p eq | false | _ | _ | _ = case eq of λ ()
  choose-safe (T.startNext j rid) s p eq | true | nothing | _ | _ = case eq of λ ()
  choose-safe (T.startNext j rid) s p eq | true | just req | just old | _ = case eq of λ ()
  choose-safe (T.startNext j rid) s p eq | true | just req | nothing | false = case eq of λ ()
  choose-safe (T.selectStart w) s p eq = select-safe w s p eq
  choose-safe (T.invokeStartTrace w) s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
  ... | T.selectedC rid | true = case just-injective eq of λ { refl → tt }
  choose-safe (T.invokeStartTrace w) s p eq | T.idleC | _ = case eq of λ ()
  choose-safe (T.invokeStartTrace w) s p eq | T.tracingC rid | _ = case eq of λ ()
  choose-safe (T.invokeStartTrace w) s p eq | T.forkReadyC rid | _ = case eq of λ ()
  choose-safe (T.invokeStartTrace w) s p eq | T.registeringC rid j | _ = case eq of λ ()
  choose-safe (T.invokeStartTrace w) s p eq | T.failedC rid result | _ = case eq of λ ()
  choose-safe (T.invokeStartTrace w) s p eq | T.selectedC rid | false = case eq of λ ()
  choose-safe (T.returnStartTrace w) s p eq with T.cursor w (T.front s) | T.controllerFree w (T.base s)
  ... | T.tracingC rid | true = case just-injective eq of λ { refl → tt }
  choose-safe (T.returnStartTrace w) s p eq | T.idleC | _ = case eq of λ ()
  choose-safe (T.returnStartTrace w) s p eq | T.selectedC rid | _ = case eq of λ ()
  choose-safe (T.returnStartTrace w) s p eq | T.forkReadyC rid | _ = case eq of λ ()
  choose-safe (T.returnStartTrace w) s p eq | T.registeringC rid j | _ = case eq of λ ()
  choose-safe (T.returnStartTrace w) s p eq | T.failedC rid result | _ = case eq of λ ()
  choose-safe (T.returnStartTrace w) s p eq | T.tracingC rid | false = case eq of λ ()
  choose-safe (T.forkStart w j) s p eq = fork-safe w j s p eq
  choose-safe (T.registerStart j) s p eq = register-safe j s p eq
  choose-safe (T.commitClean j) s p eq = completion-safe j clean s p eq
  choose-safe (T.commitError j err) s p eq = completion-safe j (errored err) s p eq
  choose-safe (T.pollResults ref w) s p eq = poll-safe ref w s p eq
  choose-safe (T.waitJobResults j) s p eq = job-wait-safe j s p eq
  choose-safe (T.waitMonitorResults ref) s p eq = monitor-wait-safe ref s p eq
  choose-safe (T.observeStartTraceException w result) s p eq with T.startTraceSelection w result s in selected
  ... | just (rid , fs) = case just-injective eq of λ { refl → tt }
  ... | nothing = case eq of λ ()
  choose-safe (T.deliverStartTraceShutdown err) s p eq with S.inCMClose (S.stage (E.base (K.server (T.base s)))) |
    Close.phase (W.shutdown (R.base (N.raw (T.publication (T.base s))))) in awaiting
  ... | true | Close.awaitDelivery entry w with T.startTraceSelection w (R.async err) s in selected
  ...   | just (rid , fs) with W.control Close.acknowledgeDelivery (R.base (N.raw (T.publication (T.base s)))) in received
  ...     | just target = case just-injective eq of λ { refl → target , received , refl }
  ...     | nothing = case eq of λ ()
  choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.awaitDelivery entry w | nothing = case eq of λ ()
  choose-safe (T.deliverStartTraceShutdown err) s p eq | false | _ = case eq of λ ()
  choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.initial = case eq of λ ()
  choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.reading = case eq of λ ()
  choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.awaitResults = case eq of λ ()
  choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.closed = case eq of λ ()
  choose-safe (T.deliverStartTraceShutdown err) s p eq | true | Close.sendReady entry w = case eq of λ ()

  advance-frame : ∀ a s {t} → T.advance a s ≡ just t → Frame (coordT s) (coordT t)
  advance-frame a s eq with T.choose a s in chosen
  ... | nothing = case eq of λ ()
  ... | just p = enact-frame p s eq (choose-safe a s p chosen)
  runs-frame : ∀ {s events t} → T.Runs s events t → Frame (coordT s) (coordT t)
  runs-frame (T.stop {s = s}) = stay (coordT s)
  runs-frame (T.more {s = s} {a = a} eq rest) = compose (advance-frame a s eq) (runs-frame rest)

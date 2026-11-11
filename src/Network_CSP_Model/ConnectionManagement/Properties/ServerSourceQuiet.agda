{-# OPTIONS --guardedness #-}

-- The quiet-governor predicate of MachineQuiet, lifted through the
-- publication-unwind layer and every Server admission step.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerSourceQuiet (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Nat using (ℕ)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (worker; local; mux; job; entry)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.PoolRelays as RR
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.ServerPeers as Combined
import ConnectionManagement.ServerPeersRelays as Relays
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Properties.MuxPublicationUnwind as PublicationFacts
import ConnectionManagement.Properties.MuxHandlerExit as ExitFacts
import ConnectionManagement.Properties.CallerCancellation as Writer
import ConnectionManagement.Properties.MachineQuiet as MQ
import ConnectionManagement.Properties.GovernorPoolCM as GovernorCM
import ConnectionManagement.Properties.PeerSupervisionCM as SupervisionCM
import ConnectionManagement.Properties.ServerIGDone as IGDone
import ConnectionManagement.Properties.ServerStageEntry as Entry
import ConnectionManagement.Properties.ServerShutdownComplete as SI5aModel
import ConnectionManagement.Properties.PoolRelays as RelaysFacts
private
  module S = Server isBearerClosed
  module N = Publication isBearerClosed
  module PubF = PublicationFacts isBearerClosed
  module ExitF = ExitFacts isBearerClosed

QC : O.Configuration → Set
QC c = MQ.QuietCore (O.core c)

-- Publication-unwind steps change the source only by outbound-machine steps.
publication-quiet : ∀ a n {n′} → N.step a n ≡ just n′ → QC (N.source n) → QC (N.source n′)
publication-quiet a n eq q = MQ.outbound-exec-quiet (proj₂ (ExitF.machine (PubF.step-projects a n eq))) q

-- Server steps: worker metadata, world writes, or publication steps.
QS : S.State → Set
QS s = QC (S.source s)
fork-quiet : ∀ w req s {t} → S.forkAccepted w req s ≡ just t → QS s → QS t
fork-quiet w req s eq with S.accepting (S.stage s) | S.listenerOpen s |
  S.sameLimit req (S.workers s) | S.fresh w s | S.fresh (Shared.child req) s |
  w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (S.shared s))
... | true | true | true | true | true | no _ | nothing =
  case just-injective eq of λ { refl → λ q → q }
... | false | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | true | false | _ | _ | _ | _ | _ = case eq of λ ()
... | true | true | false | _ | _ | _ | _ = case eq of λ ()
... | true | true | true | false | _ | _ | _ = case eq of λ ()
... | true | true | true | true | false | _ | _ = case eq of λ ()
... | true | true | true | true | true | yes _ | _ = case eq of λ ()
... | true | true | true | true | true | no _ | just _ = case eq of λ ()

inherit-quiet : ∀ a s {t} → S.inherit a s ≡ just t → QS s → QS t
inherit-quiet a s eq with S.allowed a s
... | false = case eq of λ ()
... | true with N.step a (S.base s) in advanced
...   | nothing = case eq of λ ()
...   | just n = case just-injective eq of λ { refl → publication-quiet a (S.base s) advanced }

-- Return, exception and result observations change only raw-worker metadata.
return-quiet : ∀ w s {t} → S.observeReturn w s ≡ just t → QS s → QS t
return-quiet w s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.completedHandshake (Shared.connected _) = case just-injective eq of λ { refl → λ q → q }
...   | S.calling | Shared.completedHandshake (Shared.disconnected _) = case just-injective eq of λ { refl → λ q → q }
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
return-quiet w s eq | nothing | _ = case eq of λ ()
return-quiet w s eq | just _ | nothing = case eq of λ ()
prefix-return-quiet : ∀ w s {t} → S.prefixReturned w s ≡ just t → QS s → QS t
prefix-return-quiet w s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.closeSocket Shared.hardLimitReached = case just-injective eq of λ { refl → λ q → q }
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
...   | S.calling | Shared.closeSocket Shared.forbidden = case eq of λ ()
...   | S.calling | Shared.closeSocket Shared.forkFailed = case eq of λ ()
...   | S.closeDisconnected | _ = case eq of λ ()
...   | S.closeException _ | _ = case eq of λ ()
...   | S.closePrefix _ _ | _ = case eq of λ ()
...   | S.bodyExited _ | _ = case eq of λ ()
...   | S.resultAvailable _ | _ = case eq of λ ()
prefix-return-quiet w s eq | nothing | _ = case eq of λ ()
prefix-return-quiet w s eq | just _ | nothing = case eq of λ ()
prefix-exception-quiet : ∀ w err s {t} → S.prefixException w err s ≡ just t → QS s → QS t
prefix-exception-quiet w err s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.closeSocket Shared.forbidden = case just-injective eq of λ { refl → λ q → q }
...   | S.calling | Shared.closeSocket Shared.forkFailed = case just-injective eq of λ { refl → λ q → q }
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
prefix-exception-quiet w err s eq | nothing | _ = case eq of λ ()
prefix-exception-quiet w err s eq | just _ | nothing = case eq of λ ()
exception-quiet : ∀ w err s {t} → S.observeException w err s ≡ just t → QS s → QS t
exception-quiet w err s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.awaitHandshake _ _ = case just-injective eq of λ { refl → λ q → q }
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
exception-quiet w err s eq | nothing | _ = case eq of λ ()
exception-quiet w err s eq | just _ | nothing = case eq of λ ()
result-quiet : ∀ w s {t} → S.publishWorkerResult w s ≡ just t → QS s → QS t
result-quiet w s eq with lookup w (S.workers s)
... | nothing = case eq of λ ()
... | just worker with S.pc worker
...   | S.bodyExited r = case just-injective eq of λ { refl → λ q → q }
...   | S.calling = case eq of λ ()
...   | S.closeDisconnected = case eq of λ ()
...   | S.closeException _ = case eq of λ ()
...   | S.closePrefix _ _ = case eq of λ ()
...   | S.resultAvailable _ = case eq of λ ()

enact-prefix-quiet : ∀ w worker result outcome s {t} → S.enactPrefixClose w worker result outcome s ≡ just t →
  QS s → QS t
enact-prefix-quiet w worker result nothing s eq with N.step
  (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) in advanced
... | nothing = case eq of λ ()
... | just n = case just-injective eq of λ { refl →
  publication-quiet (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) advanced }
enact-prefix-quiet w worker result (just err) s eq = case just-injective eq of λ { refl → λ q → q }
close-prefix-quiet : ∀ w worker failure result outcome s {t} →
  S.closePrefixWorker w worker failure result outcome s ≡ just t → QS s → QS t
close-prefix-quiet w worker failure result outcome s eq with S.prefixMatches w failure s
... | false = case eq of λ ()
... | true = enact-prefix-quiet w worker result outcome s eq
close-quiet : ∀ w outcome s {t} → S.closeWorker w outcome s ≡ just t → QS s → QS t
close-quiet w outcome s eq with lookup w (S.workers s)
... | nothing = case eq of λ ()
... | just worker with S.pc worker
...   | S.closeDisconnected = case just-injective eq of λ { refl → λ q → q }
...   | S.closeException err = case just-injective eq of λ { refl → λ q → q }
...   | S.closePrefix f r = close-prefix-quiet w worker f r outcome s eq
...   | S.calling = case eq of λ ()
...   | S.bodyExited _ = case eq of λ ()
...   | S.resultAvailable _ = case eq of λ ()




scope-parts : ∀ x s {t} → S.scopeAdvance x s ≡ just t →
  Σ S.ScopePlan (λ p → S.chooseScope x s ≡ just p × S.enactScope p s ≡ just t)
scope-parts x s eq with S.chooseScope x s
... | nothing = case eq of λ ()
... | just p = p , refl , eq
scope-quiet : ∀ x s {t} → S.scopeAdvance x s ≡ just t → QS s → QS t
scope-quiet x s eq with S.chooseScope x s
... | nothing = case eq of λ ()
... | just p with S.physicalAction p
...   | nothing = case just-injective eq of λ { refl → λ q → q }
...   | just a with N.step a (S.base s) in advanced
...     | nothing = case eq of λ ()
...     | just n = case just-injective eq of λ { refl → publication-quiet a (S.base s) advanced }
server-quiet : ∀ a s {t} → S.step a s ≡ just t → QS s → QS t
server-quiet (S.acceptedFork w req) s eq = fork-quiet w req s eq
server-quiet (S.run a) s eq = inherit-quiet a s eq
server-quiet (S.workerReturned w) s eq = return-quiet w s eq
server-quiet (S.workerPrefixReturned w) s eq = prefix-return-quiet w s eq
server-quiet (S.workerPrefixException w err) s eq = prefix-exception-quiet w err s eq
server-quiet (S.workerException w err) s eq = exception-quiet w err s eq
server-quiet (S.workerClose w outcome) s eq = close-quiet w outcome s eq
server-quiet (S.workerResult w) s eq = result-quiet w s eq
server-quiet (S.scope x) s eq = scope-quiet x s eq


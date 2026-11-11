{-# OPTIONS --guardedness #-}

-- Caller bookkeeping through every Server admission step: only a lifted
-- publication action can have a root; worker metadata, scope plans and the
-- prefix close keep the outbound caller keys.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.SourceKeysServer (isBearerClosed : ErrorId → Bool) where

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
import ConnectionManagement.Properties.GovernorPoolCM as GovernorCM
import ConnectionManagement.Properties.PeerSupervisionCM as SupervisionCM
import ConnectionManagement.Properties.ServerIGDone as IGDone
import ConnectionManagement.Properties.ServerStageEntry as Entry
import ConnectionManagement.Properties.ServerShutdownComplete as SI5aModel
import ConnectionManagement.Properties.PoolRelays as RelaysFacts
open import ConnectionManagement.Properties.OutboundKeys
import ConnectionManagement.Properties.SourceKeysPublication as PublicationKeys
private
  module S = Server isBearerClosed
  module PK = PublicationKeys isBearerClosed
  module N = Publication isBearerClosed
  module W = N.W
  module R = N.R
  module PubF = PublicationFacts isBearerClosed
  module ExitF = ExitFacts isBearerClosed

-- Server steps: worker metadata, world writes, or publication steps.
Same : S.State → S.State → Set
Same s t = KeySame (S.source s) (S.source t)
rootS : S.Action → Maybe O.Action
rootS (S.run a) = PK.rootN a
rootS _ = nothing
nil : ∀ r {c c′} → r ≡ nothing → Effect r c c′ → KeySame c c′
nil .nothing refl e = e
PhysRoot : Maybe N.Action → Set
PhysRoot nothing = ⊤
PhysRoot (just a) = PK.rootN a ≡ nothing
fork-keys : ∀ w req s {t} → S.forkAccepted w req s ≡ just t → Same s t
fork-keys w req s eq with S.accepting (S.stage s) | S.listenerOpen s |
  S.sameLimit req (S.workers s) | S.fresh w s | S.fresh (Shared.child req) s |
  w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (S.shared s))
... | true | true | true | true | true | no _ | nothing =
  case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
... | false | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | true | false | _ | _ | _ | _ | _ = case eq of λ ()
... | true | true | false | _ | _ | _ | _ = case eq of λ ()
... | true | true | true | false | _ | _ | _ = case eq of λ ()
... | true | true | true | true | false | _ | _ = case eq of λ ()
... | true | true | true | true | true | yes _ | _ = case eq of λ ()
... | true | true | true | true | true | no _ | just _ = case eq of λ ()

inherit-keys : ∀ a s {t} → S.inherit a s ≡ just t → Effect (PK.rootN a) (S.source s) (S.source t)
inherit-keys a s eq with S.allowed a s
... | false = case eq of λ ()
... | true with N.step a (S.base s) in advanced
...   | nothing = case eq of λ ()
...   | just n = case just-injective eq of λ { refl → PK.step-keysN a (S.base s) advanced }

-- Return, exception and result observations change only raw-worker metadata.
return-keys : ∀ w s {t} → S.observeReturn w s ≡ just t → Same s t
return-keys w s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.completedHandshake (Shared.connected _) = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
...   | S.calling | Shared.completedHandshake (Shared.disconnected _) = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
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
return-keys w s eq | nothing | _ = case eq of λ ()
return-keys w s eq | just _ | nothing = case eq of λ ()
prefix-return-keys : ∀ w s {t} → S.prefixReturned w s ≡ just t → Same s t
prefix-return-keys w s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.closeSocket Shared.hardLimitReached = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
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
prefix-return-keys w s eq | nothing | _ = case eq of λ ()
prefix-return-keys w s eq | just _ | nothing = case eq of λ ()
prefix-exception-keys : ∀ w err s {t} → S.prefixException w err s ≡ just t → Same s t
prefix-exception-keys w err s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.closeSocket Shared.forbidden = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
...   | S.calling | Shared.closeSocket Shared.forkFailed = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
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
prefix-exception-keys w err s eq | nothing | _ = case eq of λ ()
prefix-exception-keys w err s eq | just _ | nothing = case eq of λ ()
exception-keys : ∀ w err s {t} → S.observeException w err s ≡ just t → Same s t
exception-keys w err s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.awaitHandshake _ _ = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
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
exception-keys w err s eq | nothing | _ = case eq of λ ()
exception-keys w err s eq | just _ | nothing = case eq of λ ()
result-keys : ∀ w s {t} → S.publishWorkerResult w s ≡ just t → Same s t
result-keys w s eq with lookup w (S.workers s)
... | nothing = case eq of λ ()
... | just worker with S.pc worker
...   | S.bodyExited r = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
...   | S.calling = case eq of λ ()
...   | S.closeDisconnected = case eq of λ ()
...   | S.closeException _ = case eq of λ ()
...   | S.closePrefix _ _ = case eq of λ ()
...   | S.resultAvailable _ = case eq of λ ()

enact-prefix-keys : ∀ w worker result outcome s {t} → S.enactPrefixClose w worker result outcome s ≡ just t →
  Same s t
enact-prefix-keys w worker result nothing s eq with N.step
  (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) in advanced
... | nothing = case eq of λ ()
... | just n = case just-injective eq of λ { refl →
  PK.step-keysN (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s) advanced }
enact-prefix-keys w worker result (just err) s eq = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
close-prefix-keys : ∀ w worker failure result outcome s {t} →
  S.closePrefixWorker w worker failure result outcome s ≡ just t → Same s t
close-prefix-keys w worker failure result outcome s eq with S.prefixMatches w failure s
... | false = case eq of λ ()
... | true = enact-prefix-keys w worker result outcome s eq
close-keys : ∀ w outcome s {t} → S.closeWorker w outcome s ≡ just t → Same s t
close-keys w outcome s eq with lookup w (S.workers s)
... | nothing = case eq of λ ()
... | just worker with S.pc worker
...   | S.closeDisconnected = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
...   | S.closeException err = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
...   | S.closePrefix f r = close-prefix-keys w worker f r outcome s eq
...   | S.calling = case eq of λ ()
...   | S.bodyExited _ = case eq of λ ()
...   | S.resultAvailable _ = case eq of λ ()




scope-parts : ∀ x s {t} → S.scopeAdvance x s ≡ just t →
  Σ S.ScopePlan (λ p → S.chooseScope x s ≡ just p × S.enactScope p s ≡ just t)
scope-parts x s eq with S.chooseScope x s
... | nothing = case eq of λ ()
... | just p = p , refl , eq
phys-root : ∀ x s {p} → S.chooseScope x s ≡ just p → PhysRoot (S.physicalAction p)
phys-root S.returnAction s chosen with S.stage s in st
... | S.serving = case just-injective chosen of λ { refl → tt }
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.publishActionResult s chosen with S.stage s in st
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case just-injective chosen of λ { refl → tt }
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.interruptServer s chosen with S.stage s in st
... | S.serving = case just-injective chosen of λ { refl → tt }
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.selectActionWinner s chosen with S.stage s in st
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case just-injective chosen of λ { refl → tt }
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.requestAcceptCancel s chosen with S.stage s in st
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case just-injective chosen of λ { refl → tt }
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.deliverAcceptAtWait s chosen with S.stage s in st
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case just-injective chosen of λ { refl → tt }
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.closeListener s chosen with S.stage s in st
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case just-injective chosen of λ { refl → tt }
... | S.acceptFailed = case just-injective chosen of λ { refl → tt }
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.publishAcceptResult s chosen with S.stage s in st
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case just-injective chosen of λ { refl → tt }
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.joinAccept s chosen with S.stage s in st
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case just-injective chosen of λ { refl → tt }
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.traceStopped s chosen with S.stage s in st
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case just-injective chosen of λ { refl → tt }
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.cancelJoinReturnedAction s chosen with S.stage s in st
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case just-injective chosen of λ { refl → tt }
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.requestIGCancel s chosen with S.stage s in st
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case just-injective chosen of λ { refl → tt }
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.acceptFails s chosen with S.stage s in st
... | S.serving = case just-injective chosen of λ { refl → tt }
... | S.actionBodyExited = case just-injective chosen of λ { refl → tt }
... | S.actionResultAvailable = case just-injective chosen of λ { refl → tt }
... | S.closingAccept = case just-injective chosen of λ { refl → tt }
... | S.acceptCancelRequested = case just-injective chosen of λ { refl → tt }
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case chosen of λ ()
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.beginCM s chosen with S.stage s in st
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = case chosen of λ ()
... | S.igCancelRequested = case chosen of λ ()
... | S.igJoined = case just-injective chosen of λ { refl → tt }
... | S.closingCM = case chosen of λ ()
... | S.serverReturned = case chosen of λ ()
phys-root S.deliverIGBody s chosen with S.stage s in st | S.ig s in igq | Machine.inboundRelease (O.core (S.source s)) | Machine.remoteCall (O.core (S.source s))
... | S.serving | _ | _ | _ = case chosen of λ ()
... | S.actionBodyExited | _ | _ | _ = case chosen of λ ()
... | S.actionResultAvailable | _ | _ | _ = case chosen of λ ()
... | S.closingAccept | _ | _ | _ = case chosen of λ ()
... | S.acceptCancelRequested | _ | _ | _ = case chosen of λ ()
... | S.acceptCancelDelivered | _ | _ | _ = case chosen of λ ()
... | S.acceptFailed | _ | _ | _ = case chosen of λ ()
... | S.acceptBodyExited | _ | _ | _ = case chosen of λ ()
... | S.acceptResultAvailable | _ | _ | _ = case chosen of λ ()
... | S.acceptJoined | _ | _ | _ = case chosen of λ ()
... | S.serverStopped | _ | _ | _ = case chosen of λ ()
... | S.actionJoined | _ | _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igLive | nothing | nothing = case just-injective chosen of λ { refl → tt }
... | S.igCancelRequested | S.igLive | nothing | just _ = case chosen of λ ()
... | S.igCancelRequested | S.igLive | just _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igCaught | _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igInactive | _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igFlushed | _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igBodyExited | _ | _ = case chosen of λ ()
... | S.igCancelRequested | S.igResultAvailable | _ | _ = case chosen of λ ()
... | S.igJoined | _ | _ | _ = case chosen of λ ()
... | S.closingCM | _ | _ | _ = case chosen of λ ()
... | S.serverReturned | _ | _ | _ = case chosen of λ ()
phys-root S.joinIG s chosen with S.stage s in st | S.ig s in igq
... | S.serving | _ = case chosen of λ ()
... | S.actionBodyExited | _ = case chosen of λ ()
... | S.actionResultAvailable | _ = case chosen of λ ()
... | S.closingAccept | _ = case chosen of λ ()
... | S.acceptCancelRequested | _ = case chosen of λ ()
... | S.acceptCancelDelivered | _ = case chosen of λ ()
... | S.acceptFailed | _ = case chosen of λ ()
... | S.acceptBodyExited | _ = case chosen of λ ()
... | S.acceptResultAvailable | _ = case chosen of λ ()
... | S.acceptJoined | _ = case chosen of λ ()
... | S.serverStopped | _ = case chosen of λ ()
... | S.actionJoined | _ = case chosen of λ ()
... | S.igCancelRequested | S.igLive = case chosen of λ ()
... | S.igCancelRequested | S.igCaught = case chosen of λ ()
... | S.igCancelRequested | S.igInactive = case chosen of λ ()
... | S.igCancelRequested | S.igFlushed = case chosen of λ ()
... | S.igCancelRequested | S.igBodyExited = case chosen of λ ()
... | S.igCancelRequested | S.igResultAvailable = case just-injective chosen of λ { refl → tt }
... | S.igJoined | _ = case chosen of λ ()
... | S.closingCM | _ = case chosen of λ ()
... | S.serverReturned | _ = case chosen of λ ()
phys-root S.igWins s chosen with S.stage s in st | S.ig s in igq
... | S.serving | S.igLive = case chosen of λ ()
... | S.serving | S.igCaught = case chosen of λ ()
... | S.serving | S.igInactive = case chosen of λ ()
... | S.serving | S.igFlushed = case chosen of λ ()
... | S.serving | S.igBodyExited = case chosen of λ ()
... | S.serving | S.igResultAvailable = case just-injective chosen of λ { refl → tt }
... | S.actionBodyExited | S.igLive = case chosen of λ ()
... | S.actionBodyExited | S.igCaught = case chosen of λ ()
... | S.actionBodyExited | S.igInactive = case chosen of λ ()
... | S.actionBodyExited | S.igFlushed = case chosen of λ ()
... | S.actionBodyExited | S.igBodyExited = case chosen of λ ()
... | S.actionBodyExited | S.igResultAvailable = case just-injective chosen of λ { refl → tt }
... | S.actionResultAvailable | S.igLive = case chosen of λ ()
... | S.actionResultAvailable | S.igCaught = case chosen of λ ()
... | S.actionResultAvailable | S.igInactive = case chosen of λ ()
... | S.actionResultAvailable | S.igFlushed = case chosen of λ ()
... | S.actionResultAvailable | S.igBodyExited = case chosen of λ ()
... | S.actionResultAvailable | S.igResultAvailable = case just-injective chosen of λ { refl → tt }
... | S.closingAccept | _ = case chosen of λ ()
... | S.acceptCancelRequested | _ = case chosen of λ ()
... | S.acceptCancelDelivered | _ = case chosen of λ ()
... | S.acceptFailed | _ = case chosen of λ ()
... | S.acceptBodyExited | _ = case chosen of λ ()
... | S.acceptResultAvailable | _ = case chosen of λ ()
... | S.acceptJoined | _ = case chosen of λ ()
... | S.serverStopped | _ = case chosen of λ ()
... | S.actionJoined | _ = case chosen of λ ()
... | S.igCancelRequested | _ = case chosen of λ ()
... | S.igJoined | _ = case chosen of λ ()
... | S.closingCM | _ = case chosen of λ ()
... | S.serverReturned | _ = case chosen of λ ()
phys-root S.finishServer s chosen with S.stage s in st | Close.phase (W.shutdown (R.base (N.raw (S.base s))))
... | S.serving | _ = case chosen of λ ()
... | S.actionBodyExited | _ = case chosen of λ ()
... | S.actionResultAvailable | _ = case chosen of λ ()
... | S.closingAccept | _ = case chosen of λ ()
... | S.acceptCancelRequested | _ = case chosen of λ ()
... | S.acceptCancelDelivered | _ = case chosen of λ ()
... | S.acceptFailed | _ = case chosen of λ ()
... | S.acceptBodyExited | _ = case chosen of λ ()
... | S.acceptResultAvailable | _ = case chosen of λ ()
... | S.acceptJoined | _ = case chosen of λ ()
... | S.serverStopped | _ = case chosen of λ ()
... | S.actionJoined | _ = case chosen of λ ()
... | S.igCancelRequested | _ = case chosen of λ ()
... | S.igJoined | _ = case chosen of λ ()
... | S.closingCM | Close.initial = case chosen of λ ()
... | S.closingCM | Close.reading = case chosen of λ ()
... | S.closingCM | Close.awaitResults = case chosen of λ ()
... | S.closingCM | Close.closed = case just-injective chosen of λ { refl → tt }
... | S.closingCM | (Close.sendReady _ _) = case chosen of λ ()
... | S.closingCM | (Close.awaitDelivery _ _) = case chosen of λ ()
... | S.serverReturned | _ = case chosen of λ ()
phys-root S.deactivateIG s chosen with S.ig s in igq
... | S.igLive = case chosen of λ ()
... | S.igCaught = case just-injective chosen of λ { refl → refl }
... | S.igInactive = case chosen of λ ()
... | S.igFlushed = case chosen of λ ()
... | S.igBodyExited = case chosen of λ ()
... | S.igResultAvailable = case chosen of λ ()
phys-root S.flushIG s chosen with S.ig s in igq
... | S.igLive = case chosen of λ ()
... | S.igCaught = case chosen of λ ()
... | S.igInactive = case just-injective chosen of λ { refl → refl }
... | S.igFlushed = case chosen of λ ()
... | S.igBodyExited = case chosen of λ ()
... | S.igResultAvailable = case chosen of λ ()
phys-root S.publishIGResult s chosen with S.ig s in igq
... | S.igLive = case chosen of λ ()
... | S.igCaught = case chosen of λ ()
... | S.igInactive = case chosen of λ ()
... | S.igFlushed = case chosen of λ ()
... | S.igBodyExited = case just-injective chosen of λ { refl → tt }
... | S.igResultAvailable = case chosen of λ ()
phys-root S.failIGBody s chosen with S.ig s in igq | Machine.inboundRelease (O.core (S.source s)) | Machine.remoteCall (O.core (S.source s))
... | S.igLive | nothing | nothing = case just-injective chosen of λ { refl → tt }
... | S.igLive | nothing | just _ = case chosen of λ ()
... | S.igLive | just _ | _ = case chosen of λ ()
... | S.igCaught | _ | _ = case chosen of λ ()
... | S.igInactive | _ | _ = case chosen of λ ()
... | S.igFlushed | _ | _ = case chosen of λ ()
... | S.igBodyExited | _ | _ = case chosen of λ ()
... | S.igResultAvailable | _ | _ = case chosen of λ ()
phys-root S.finishIGBody s chosen with S.ig s in igq | IG.connections (IG.publishedState (Machine.inboundGovernor (O.core (S.source s)))) |
  IG.continuation (Machine.inboundGovernor (O.core (S.source s))) | IG.active (IG.execution (Machine.inboundGovernor (O.core (S.source s))))
... | S.igFlushed | [] | IG.exited | false = case just-injective chosen of λ { refl → tt }
... | S.igFlushed | [] | IG.exited | true = case chosen of λ ()
... | S.igFlushed | [] | IG.sampleTime | _ = case chosen of λ ()
... | S.igFlushed | [] | IG.exitFlush | _ = case chosen of λ ()
... | S.igFlushed | [] | IG.inCM | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.armInactivity _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.awaitBatch _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.readNext _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.prepareNew _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.startResponders _ _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.publishDecision _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.stopAfterFailure _ _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.waitStopped _ _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.restartResponder _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.awaitRemoteIdle _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | [] | (IG.needsCM _ _ _ _) | _ = case chosen of λ ()
... | S.igFlushed | _ ∷ _ | _ | _ = case chosen of λ ()
... | S.igLive | _ | _ | _ = case chosen of λ ()
... | S.igCaught | _ | _ | _ = case chosen of λ ()
... | S.igInactive | _ | _ | _ = case chosen of λ ()
... | S.igBodyExited | _ | _ | _ = case chosen of λ ()
... | S.igResultAvailable | _ | _ | _ = case chosen of λ ()
scope-keys : ∀ x s {t} → S.scopeAdvance x s ≡ just t → Same s t
scope-keys x s eq with S.chooseScope x s in chosen
... | nothing = case eq of λ ()
... | just p with S.physicalAction p in physical
...   | nothing = case just-injective eq of λ { refl → fields-same _ _ refl refl refl refl }
...   | just a with N.step a (S.base s) in advanced
...     | nothing = case eq of λ ()
...     | just n = case just-injective eq of λ { refl → nil _ (subst PhysRoot physical (phys-root x s chosen))
  (PK.step-keysN a (S.base s) advanced) }
step-keysS : ∀ a s {t} → S.step a s ≡ just t → Effect (rootS a) (S.source s) (S.source t)
step-keysS (S.acceptedFork w req) s eq = fork-keys w req s eq
step-keysS (S.run a) s eq = inherit-keys a s eq
step-keysS (S.workerReturned w) s eq = return-keys w s eq
step-keysS (S.workerPrefixReturned w) s eq = prefix-return-keys w s eq
step-keysS (S.workerPrefixException w err) s eq = prefix-exception-keys w err s eq
step-keysS (S.workerException w err) s eq = exception-keys w err s eq
step-keysS (S.workerClose w outcome) s eq = close-keys w outcome s eq
step-keysS (S.workerResult w) s eq = result-keys w s eq
step-keysS (S.scope x) s eq = scope-keys x s eq


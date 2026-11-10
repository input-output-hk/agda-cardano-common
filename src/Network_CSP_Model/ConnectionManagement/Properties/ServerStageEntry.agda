{-# OPTIONS --guardedness #-}

-- Server stage entry. Only Server scope actions change the Server stage, and
-- the only scope action that enters the post-join stages (actionJoined and
-- later) from an earlier stage is cancelJoinReturnedAction. The same holds for
-- the IG exit layer, whose own plans keep the stage.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerStageEntry (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication
private
  module S = Server isBearerClosed
  module E = Exit isBearerClosed
  module N = Publication isBearerClosed

-- The stages after the action thread has been cancelled and joined.
post : S.Stage → Bool
post S.actionJoined = true
post S.igCancelRequested = true
post S.igJoined = true
post S.closingCM = true
post S.serverReturned = true
post _ = false

-- Worker, admission and inherited steps keep the stage.
fork-stage : ∀ w req s {t} → S.forkAccepted w req s ≡ just t → S.stage t ≡ S.stage s
fork-stage w req s eq with S.accepting (S.stage s) | S.listenerOpen s |
  S.sameLimit req (S.workers s) | S.fresh w s | S.fresh (Shared.child req) s |
  w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (S.shared s))
... | true | true | true | true | true | no _ | nothing =
  case just-injective eq of λ { refl → refl }
... | false | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | true | false | _ | _ | _ | _ | _ = case eq of λ ()
... | true | true | false | _ | _ | _ | _ = case eq of λ ()
... | true | true | true | false | _ | _ | _ = case eq of λ ()
... | true | true | true | true | false | _ | _ = case eq of λ ()
... | true | true | true | true | true | yes _ | _ = case eq of λ ()
... | true | true | true | true | true | no _ | just _ = case eq of λ ()

inherit-stage : ∀ a s {t} → S.inherit a s ≡ just t → S.stage t ≡ S.stage s
inherit-stage a s eq with S.allowed a s
... | false = case eq of λ ()
... | true with N.step a (S.base s)
...   | nothing = case eq of λ ()
...   | just n = case just-injective eq of λ { refl → refl }

-- Return, exception and result observations change only raw-worker metadata.
return-stage : ∀ w s {t} → S.observeReturn w s ≡ just t → S.stage t ≡ S.stage s
return-stage w s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.completedHandshake (Shared.connected _) = case just-injective eq of λ { refl → refl }
...   | S.calling | Shared.completedHandshake (Shared.disconnected _) = case just-injective eq of λ { refl → refl }
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
return-stage w s eq | nothing | _ = case eq of λ ()
return-stage w s eq | just _ | nothing = case eq of λ ()
prefix-return-stage : ∀ w s {t} → S.prefixReturned w s ≡ just t → S.stage t ≡ S.stage s
prefix-return-stage w s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.closeSocket Shared.hardLimitReached = case just-injective eq of λ { refl → refl }
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
prefix-return-stage w s eq | nothing | _ = case eq of λ ()
prefix-return-stage w s eq | just _ | nothing = case eq of λ ()
prefix-exception-stage : ∀ w err s {t} → S.prefixException w err s ≡ just t → S.stage t ≡ S.stage s
prefix-exception-stage w err s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.closeSocket Shared.forbidden = case just-injective eq of λ { refl → refl }
...   | S.calling | Shared.closeSocket Shared.forkFailed = case just-injective eq of λ { refl → refl }
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
prefix-exception-stage w err s eq | nothing | _ = case eq of λ ()
prefix-exception-stage w err s eq | just _ | nothing = case eq of λ ()
exception-stage : ∀ w err s {t} → S.observeException w err s ≡ just t → S.stage t ≡ S.stage s
exception-stage w err s eq with lookup w (S.workers s) | lookup w (Shared.admissions (S.shared s))
... | just worker | just a with S.pc worker | Shared.pc a
...   | S.calling | Shared.awaitHandshake _ _ = case just-injective eq of λ { refl → refl }
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
exception-stage w err s eq | nothing | _ = case eq of λ ()
exception-stage w err s eq | just _ | nothing = case eq of λ ()
result-stage : ∀ w s {t} → S.publishWorkerResult w s ≡ just t → S.stage t ≡ S.stage s
result-stage w s eq with lookup w (S.workers s)
... | nothing = case eq of λ ()
... | just worker with S.pc worker
...   | S.bodyExited r = case just-injective eq of λ { refl → refl }
...   | S.calling = case eq of λ ()
...   | S.closeDisconnected = case eq of λ ()
...   | S.closeException _ = case eq of λ ()
...   | S.closePrefix _ _ = case eq of λ ()
...   | S.resultAvailable _ = case eq of λ ()

enact-prefix-stage : ∀ w worker result outcome s {t} → S.enactPrefixClose w worker result outcome s ≡ just t →
  S.stage t ≡ S.stage s
enact-prefix-stage w worker result nothing s eq with N.step
  (S.runMachine (Machine.admissionStep w Admission.close)) (S.base s)
... | nothing = case eq of λ ()
... | just n = case just-injective eq of λ { refl → refl }
enact-prefix-stage w worker result (just err) s eq = case just-injective eq of λ
  { refl → refl }
close-prefix-stage : ∀ w worker failure result outcome s {t} →
  S.closePrefixWorker w worker failure result outcome s ≡ just t → S.stage t ≡ S.stage s
close-prefix-stage w worker failure result outcome s eq with S.prefixMatches w failure s
... | false = case eq of λ ()
... | true = enact-prefix-stage w worker result outcome s eq
close-stage : ∀ w outcome s {t} → S.closeWorker w outcome s ≡ just t → S.stage t ≡ S.stage s
close-stage w outcome s eq with lookup w (S.workers s)
... | nothing = case eq of λ ()
... | just worker with S.pc worker
...   | S.closeDisconnected = case just-injective eq of λ
  { refl → refl }
...   | S.closeException err = case just-injective eq of λ
  { refl → refl }
...   | S.closePrefix f r = close-prefix-stage w worker f r outcome s eq
...   | S.calling = case eq of λ ()
...   | S.bodyExited _ = case eq of λ ()
...   | S.resultAvailable _ = case eq of λ ()


-- Every Server step keeps the stage, or is a scope action.
step-stage : ∀ a s {t} → S.step a s ≡ just t → S.stage t ≡ S.stage s ⊎ Σ S.ScopeAction (λ x → a ≡ S.scope x)
step-stage (S.acceptedFork w req) s eq = inj₁ (fork-stage w req s eq)
step-stage (S.run a) s eq = inj₁ (inherit-stage a s eq)
step-stage (S.workerReturned w) s eq = inj₁ (return-stage w s eq)
step-stage (S.workerPrefixReturned w) s eq = inj₁ (prefix-return-stage w s eq)
step-stage (S.workerPrefixException w err) s eq = inj₁ (prefix-exception-stage w err s eq)
step-stage (S.workerException w err) s eq = inj₁ (exception-stage w err s eq)
step-stage (S.workerClose w outcome) s eq = inj₁ (close-stage w outcome s eq)
step-stage (S.workerResult w) s eq = inj₁ (result-stage w s eq)
step-stage (S.scope x) s eq = inj₂ (x , refl)

-- A scope plan sets the stage it names.
enact-scope-stage : ∀ p s {t} → S.enactScope p s ≡ just t → S.stage t ≡ S.nextStage p
enact-scope-stage p s eq with S.physicalAction p
... | nothing = case just-injective eq of λ { refl → refl }
... | just a with N.step a (S.base s)
...   | nothing = case eq of λ ()
...   | just n = case just-injective eq of λ { refl → refl }

-- Each scope plan into a post-join stage starts from a post-join stage, except
-- the cancel-and-join of the action thread.
choose-entry : ∀ x s {p} → S.chooseScope x s ≡ just p → post (S.nextStage p) ≡ true →
  post (S.stage s) ≡ true ⊎ x ≡ S.cancelJoinReturnedAction
choose-entry S.returnAction s chosen with S.stage s
... | S.serving = case just-injective chosen of λ { refl → λ () }
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
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.publishActionResult s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case just-injective chosen of λ { refl → λ () }
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.interruptServer s chosen with S.stage s
... | S.serving = case just-injective chosen of λ { refl → λ () }
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
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.selectActionWinner s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.requestAcceptCancel s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case just-injective chosen of λ { refl → λ () }
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.deliverAcceptAtWait s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case just-injective chosen of λ { refl → λ () }
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.closeListener s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case just-injective chosen of λ { refl → λ () }
... | S.acceptFailed = case just-injective chosen of λ { refl → λ () }
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.publishAcceptResult s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case just-injective chosen of λ { refl → λ () }
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.joinAccept s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.traceStopped s chosen with S.stage s
... | S.serving = case chosen of λ ()
... | S.actionBodyExited = case chosen of λ ()
... | S.actionResultAvailable = case chosen of λ ()
... | S.closingAccept = case chosen of λ ()
... | S.acceptCancelRequested = case chosen of λ ()
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case just-injective chosen of λ { refl → λ () }
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.cancelJoinReturnedAction s chosen with S.stage s
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
... | S.serverStopped = λ _ → inj₂ refl
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.requestIGCancel s chosen with S.stage s
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
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.acceptFails s chosen with S.stage s
... | S.serving = case just-injective chosen of λ { refl → λ () }
... | S.actionBodyExited = case just-injective chosen of λ { refl → λ () }
... | S.actionResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.closingAccept = case just-injective chosen of λ { refl → λ () }
... | S.acceptCancelRequested = case just-injective chosen of λ { refl → λ () }
... | S.acceptCancelDelivered = case chosen of λ ()
... | S.acceptFailed = case chosen of λ ()
... | S.acceptBodyExited = case chosen of λ ()
... | S.acceptResultAvailable = case chosen of λ ()
... | S.acceptJoined = case chosen of λ ()
... | S.serverStopped = case chosen of λ ()
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.beginCM s chosen with S.stage s
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
... | S.actionJoined = λ _ → inj₁ refl
... | S.igCancelRequested = λ _ → inj₁ refl
... | S.igJoined = λ _ → inj₁ refl
... | S.closingCM = λ _ → inj₁ refl
... | S.serverReturned = λ _ → inj₁ refl
choose-entry S.deliverIGBody s chosen with S.stage s | S.ig s | Machine.inboundRelease (O.core (S.source s)) | Machine.remoteCall (O.core (S.source s))
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
... | S.actionJoined | _ | _ | _ = λ _ → inj₁ refl
... | S.igCancelRequested | _ | _ | _ = λ _ → inj₁ refl
... | S.igJoined | _ | _ | _ = λ _ → inj₁ refl
... | S.closingCM | _ | _ | _ = λ _ → inj₁ refl
... | S.serverReturned | _ | _ | _ = λ _ → inj₁ refl
choose-entry S.joinIG s chosen with S.stage s | S.ig s
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
... | S.actionJoined | _ = λ _ → inj₁ refl
... | S.igCancelRequested | _ = λ _ → inj₁ refl
... | S.igJoined | _ = λ _ → inj₁ refl
... | S.closingCM | _ = λ _ → inj₁ refl
... | S.serverReturned | _ = λ _ → inj₁ refl
choose-entry S.igWins s chosen with S.stage s | S.ig s
... | S.serving | S.igLive = case chosen of λ ()
... | S.serving | S.igCaught = case chosen of λ ()
... | S.serving | S.igInactive = case chosen of λ ()
... | S.serving | S.igFlushed = case chosen of λ ()
... | S.serving | S.igBodyExited = case chosen of λ ()
... | S.serving | S.igResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.actionBodyExited | S.igLive = case chosen of λ ()
... | S.actionBodyExited | S.igCaught = case chosen of λ ()
... | S.actionBodyExited | S.igInactive = case chosen of λ ()
... | S.actionBodyExited | S.igFlushed = case chosen of λ ()
... | S.actionBodyExited | S.igBodyExited = case chosen of λ ()
... | S.actionBodyExited | S.igResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.actionResultAvailable | S.igLive = case chosen of λ ()
... | S.actionResultAvailable | S.igCaught = case chosen of λ ()
... | S.actionResultAvailable | S.igInactive = case chosen of λ ()
... | S.actionResultAvailable | S.igFlushed = case chosen of λ ()
... | S.actionResultAvailable | S.igBodyExited = case chosen of λ ()
... | S.actionResultAvailable | S.igResultAvailable = case just-injective chosen of λ { refl → λ () }
... | S.closingAccept | _ = case chosen of λ ()
... | S.acceptCancelRequested | _ = case chosen of λ ()
... | S.acceptCancelDelivered | _ = case chosen of λ ()
... | S.acceptFailed | _ = case chosen of λ ()
... | S.acceptBodyExited | _ = case chosen of λ ()
... | S.acceptResultAvailable | _ = case chosen of λ ()
... | S.acceptJoined | _ = case chosen of λ ()
... | S.serverStopped | _ = case chosen of λ ()
... | S.actionJoined | _ = λ _ → inj₁ refl
... | S.igCancelRequested | _ = λ _ → inj₁ refl
... | S.igJoined | _ = λ _ → inj₁ refl
... | S.closingCM | _ = λ _ → inj₁ refl
... | S.serverReturned | _ = λ _ → inj₁ refl
choose-entry S.finishServer s chosen with S.stage s | Close.phase (N.W.shutdown (N.R.base (N.raw (S.base s))))
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
... | S.actionJoined | _ = λ _ → inj₁ refl
... | S.igCancelRequested | _ = λ _ → inj₁ refl
... | S.igJoined | _ = λ _ → inj₁ refl
... | S.closingCM | _ = λ _ → inj₁ refl
... | S.serverReturned | _ = λ _ → inj₁ refl
choose-entry S.deactivateIG s chosen with S.ig s
... | S.igLive = case chosen of λ ()
... | S.igCaught = case just-injective chosen of λ { refl → λ post → inj₁ post }
... | S.igInactive = case chosen of λ ()
... | S.igFlushed = case chosen of λ ()
... | S.igBodyExited = case chosen of λ ()
... | S.igResultAvailable = case chosen of λ ()
choose-entry S.flushIG s chosen with S.ig s
... | S.igLive = case chosen of λ ()
... | S.igCaught = case chosen of λ ()
... | S.igInactive = case just-injective chosen of λ { refl → λ post → inj₁ post }
... | S.igFlushed = case chosen of λ ()
... | S.igBodyExited = case chosen of λ ()
... | S.igResultAvailable = case chosen of λ ()
choose-entry S.publishIGResult s chosen with S.ig s
... | S.igLive = case chosen of λ ()
... | S.igCaught = case chosen of λ ()
... | S.igInactive = case chosen of λ ()
... | S.igFlushed = case chosen of λ ()
... | S.igBodyExited = case just-injective chosen of λ { refl → λ post → inj₁ post }
... | S.igResultAvailable = case chosen of λ ()
choose-entry S.failIGBody s chosen with S.ig s | Machine.inboundRelease (O.core (S.source s)) | Machine.remoteCall (O.core (S.source s))
... | S.igLive | nothing | nothing = case just-injective chosen of λ { refl → λ post → inj₁ post }
... | S.igLive | nothing | just _ = case chosen of λ ()
... | S.igLive | just _ | _ = case chosen of λ ()
... | S.igCaught | _ | _ = case chosen of λ ()
... | S.igInactive | _ | _ = case chosen of λ ()
... | S.igFlushed | _ | _ = case chosen of λ ()
... | S.igBodyExited | _ | _ = case chosen of λ ()
... | S.igResultAvailable | _ | _ = case chosen of λ ()
choose-entry S.finishIGBody s chosen with S.ig s | IG.connections (IG.publishedState (Machine.inboundGovernor (O.core (S.source s)))) |
  IG.continuation (Machine.inboundGovernor (O.core (S.source s))) | IG.active (IG.execution (Machine.inboundGovernor (O.core (S.source s))))
... | S.igFlushed | [] | IG.exited | false = case just-injective chosen of λ { refl → λ post → inj₁ post }
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

scope-entry : ∀ x s {t} → S.scopeAdvance x s ≡ just t → post (S.stage t) ≡ true →
  post (S.stage s) ≡ true ⊎ x ≡ S.cancelJoinReturnedAction
scope-entry x s eq entered with S.chooseScope x s in chosen
... | nothing = case eq of λ ()
... | just p = choose-entry x s chosen (subst (λ st → post st ≡ true) (enact-scope-stage p s eq) entered)

-- An IG-exit run step is the Server step it delegates.
run-step : ∀ a s {t} → E.step (E.run a) s ≡ just t → S.step a (E.base s) ≡ just (E.base t)
run-step a s eq with E.runAllowed a s
... | false = case eq of λ ()
... | true with E.delegateExit a (E.exit s)
...   | nothing = case eq of λ ()
...   | just e with S.step a (E.base s)
...     | nothing = case eq of λ ()
...     | just server = case just-injective eq of λ { refl → refl }

-- Only a run action delegates to the Server.
choose-run : ∀ a s {a′ e} → E.choose a s ≡ just (E.delegate a′ e) → a ≡ E.run a′
choose-run (E.run a) s eq with E.runAllowed a s
... | false = case eq of λ ()
... | true with E.delegateExit a (E.exit s)
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → refl }
choose-run (E.receive at err) s eq with E.selectReceipt at err s
... | nothing = case eq of λ ()
... | just r = case eq of λ ()
choose-run (E.fail at f) s eq with E.selectFailure at (S.error f) s
... | nothing = case eq of λ ()
... | just r = case eq of λ ()
choose-run E.captureSnapshot s eq with E.phase (E.exit s) | S.ig (E.base s) | IG.active (IG.execution (E.governor s)) |
  IG.continuation (E.governor s) | Machine.inboundRelease (O.core (E.source s)) | Machine.remoteCall (O.core (E.source s)) |
  E.unique (IG.connections (IG.publishedState (E.governor s)))
... | E.caught | S.igFlushed | false | IG.exited | nothing | nothing | true = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.exited | nothing | nothing | false = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.exited | nothing | just _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.exited | just _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.sampleTime | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.exitFlush | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.inCM | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | (IG.armInactivity _) | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | (IG.awaitBatch _ _) | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | (IG.readNext _ _) | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | (IG.prepareNew _ _ _ _) | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | (IG.startResponders _ _ _ _ _) | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | (IG.publishDecision _ _ _) | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | (IG.stopAfterFailure _ _ _ _ _) | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | (IG.waitStopped _ _ _ _ _) | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | (IG.restartResponder _ _ _) | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | (IG.awaitRemoteIdle _ _ _ _) | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | (IG.needsCM _ _ _ _) | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | true | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igLive | _ | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igCaught | _ | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igInactive | _ | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igBodyExited | _ | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igResultAvailable | _ | _ | _ | _ | _ = case eq of λ ()
... | E.live | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | E.traversing | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | E.invoked | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | E.failed | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | E.bodyDone | _ | _ | _ | _ | _ | _ = case eq of λ ()
choose-run E.invokeFinal s eq with E.phase (E.exit s) | E.remaining (E.exit s)
... | E.traversing | _ ∷ _ = case eq of λ ()
... | E.traversing | [] = case eq of λ ()
... | E.live | _ = case eq of λ ()
... | E.caught | _ = case eq of λ ()
... | E.invoked | _ = case eq of λ ()
... | E.failed | _ = case eq of λ ()
... | E.bodyDone | _ = case eq of λ ()
choose-run E.returnFinal s eq with E.phase (E.exit s) | E.remaining (E.exit s)
... | E.invoked | _ ∷ _ = case eq of λ ()
... | E.invoked | [] = case eq of λ ()
... | E.live | _ = case eq of λ ()
... | E.caught | _ = case eq of λ ()
... | E.traversing | _ = case eq of λ ()
... | E.failed | _ = case eq of λ ()
... | E.bodyDone | _ = case eq of λ ()
choose-run (E.failFinal err) s eq with E.phase (E.exit s) | E.remaining (E.exit s)
... | E.invoked | _ ∷ _ = case eq of λ ()
... | E.invoked | [] = case eq of λ ()
... | E.live | _ = case eq of λ ()
... | E.caught | _ = case eq of λ ()
... | E.traversing | _ = case eq of λ ()
... | E.failed | _ = case eq of λ ()
... | E.bodyDone | _ = case eq of λ ()
choose-run E.finishFinal s eq with E.phase (E.exit s) | E.remaining (E.exit s) | E.outcome (E.exit s) | S.ig (E.base s)
... | E.traversing | _ ∷ _ | _ | _ = case eq of λ ()
... | E.traversing | [] | nothing | _ = case eq of λ ()
... | E.traversing | [] | just _ | S.igLive = case eq of λ ()
... | E.traversing | [] | just _ | S.igCaught = case eq of λ ()
... | E.traversing | [] | just _ | S.igInactive = case eq of λ ()
... | E.traversing | [] | just _ | S.igFlushed = case eq of λ ()
... | E.traversing | [] | just _ | S.igBodyExited = case eq of λ ()
... | E.traversing | [] | just _ | S.igResultAvailable = case eq of λ ()
... | E.failed | _ | nothing | _ = case eq of λ ()
... | E.failed | _ | just _ | S.igLive = case eq of λ ()
... | E.failed | _ | just _ | S.igCaught = case eq of λ ()
... | E.failed | _ | just _ | S.igInactive = case eq of λ ()
... | E.failed | _ | just _ | S.igFlushed = case eq of λ ()
... | E.failed | _ | just _ | S.igBodyExited = case eq of λ ()
... | E.failed | _ | just _ | S.igResultAvailable = case eq of λ ()
... | E.live | _ | _ | _ = case eq of λ ()
... | E.caught | _ | _ | _ = case eq of λ ()
... | E.invoked | _ | _ | _ = case eq of λ ()
... | E.bodyDone | _ | _ | _ = case eq of λ ()

-- Every IG-exit step keeps the stage, or runs a Server scope action.
ig-step-stage : ∀ a s {t} → E.step a s ≡ just t →
  S.stage (E.base t) ≡ S.stage (E.base s) ⊎ Σ S.ScopeAction (λ x → a ≡ E.run (S.scope x))
ig-step-stage a s eq with E.choose a s in chosen
... | nothing = case eq of λ ()
... | just (E.delegate a′ e) with S.step a′ (E.base s) in actual
...   | nothing = case eq of λ ()
...   | just server with step-stage a′ (E.base s) actual
...     | inj₁ same = case just-injective eq of λ { refl → inj₁ same }
...     | inj₂ (x , refl) = inj₂ (x , choose-run a s chosen)
ig-step-stage a s eq | just (E.local e) = case just-injective eq of λ { refl → inj₁ refl }
ig-step-stage a s eq | just (E.abandon r) = case just-injective eq of λ { refl → inj₁ refl }
ig-step-stage a s eq | just (E.ownFailure r f) = case just-injective eq of λ { refl → inj₁ refl }
ig-step-stage a s eq | just (E.finish e) = case just-injective eq of λ { refl → inj₁ refl }

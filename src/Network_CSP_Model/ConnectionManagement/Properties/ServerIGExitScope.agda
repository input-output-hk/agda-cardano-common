{-# OPTIONS --guardedness #-}

-- Owned normal-action winner prefix, ending at the IG cancellation request.
-- These steps do not inspect/erase a pending caller-run CM continuation.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerIGExitScope (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (refl)
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
private
  module S = Server isBearerClosed
  module E = Exit isBearerClosed

atStage : S.Stage → Bool → E.State → E.State
atStage pc listener s = record s { base = record (E.base s) { stage = pc; listenerOpen = listener } }
actions : List E.Action
actions =
  E.run (S.scope S.returnAction) ∷
  E.run (S.scope S.publishActionResult) ∷
  E.run (S.scope S.selectActionWinner) ∷
  E.run (S.scope S.requestAcceptCancel) ∷
  E.run (S.scope S.deliverAcceptAtWait) ∷
  E.run (S.scope S.closeListener) ∷
  E.run (S.scope S.publishAcceptResult) ∷
  E.run (S.scope S.joinAccept) ∷
  E.run (S.scope S.traceStopped) ∷
  E.run (S.scope S.cancelJoinReturnedAction) ∷
  E.run (S.scope S.requestIGCancel) ∷ []
path : ∀ s → E.Executes (atStage S.serving true s) actions (atStage S.igCancelRequested false s)
path s =
  E.next {t = atStage S.actionBodyExited true s} refl (E.next {t = atStage S.actionResultAvailable true s} refl (E.next {t = atStage S.closingAccept true s} refl (E.next {t = atStage S.acceptCancelRequested true s} refl (E.next {t = atStage S.acceptCancelDelivered true s} refl (E.next {t = atStage S.acceptBodyExited false s} refl (E.next {t = atStage S.acceptResultAvailable false s} refl (E.next {t = atStage S.acceptJoined false s} refl (E.next {t = atStage S.serverStopped false s} refl (E.next {t = atStage S.actionJoined false s} refl (E.next {t = atStage S.igCancelRequested false s} refl (E.done)))))))))))

{-# OPTIONS --guardedness #-}

-- Admission/API quiescence, residue part c1: once the outer composition has
-- finished, the inbound governor has no pending CM call. The IG exit's
-- snapshot step requires an exited, deactivated governor with no pending call
-- (Q). Q is preserved by every machine, outbound-machine and peer step (see
-- MachineQuiet and the CM peer chain), so it holds in every later IG-exit
-- phase. A finished IG body is reached only through that exit, and the Server
-- joins the IG (and so returns) only after it.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.IGPendingQuiet (isBearerClosed isIOManagerError : ErrorId → Bool) where

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
  module E = Exit isBearerClosed
  module K = Combined isBearerClosed isIOManagerError
  module PS = Supervision isIOManagerError
  module GP = PS.GP
  module C = Context isIOManagerError
  module N = Publication isBearerClosed
  module R = N.R
  module W = N.W
  module PubF = PublicationFacts isBearerClosed
  module ExitF = ExitFacts isBearerClosed
  module IGD = IGDone isBearerClosed
  module Stage = Entry isBearerClosed
  module SI5a = SI5aModel isBearerClosed isIOManagerError
  module SR = Relays isBearerClosed isIOManagerError

open import ConnectionManagement.Properties.ServerSourceQuiet isBearerClosed using (QC; QS; scope-parts; server-quiet; publication-quiet)

-- IG-exit phases after the snapshot step.
postCaught : E.Phase → Bool
postCaught E.traversing = true
postCaught E.invoked = true
postCaught E.failed = true
postCaught E.bodyDone = true
postCaught _ = false

-- The invariant: after the snapshot the governor is quiet; a finished IG
-- body implies that phase; a post-IG Server stage implies a finished body.
InvE : E.State → Set
InvE e = (postCaught (E.phase (E.exit e)) ≡ true → QC (E.source e)) ×
  (IGD.done (S.ig (E.base e)) ≡ true → postCaught (E.phase (E.exit e)) ≡ true) ×
  (IGD.post (S.stage (E.base e)) ≡ true → IGD.done (S.ig (E.base e)) ≡ true)

absurd-live : ∀ {A : Set} → IGD.done S.igLive ≡ true → A
absurd-live ()

reception-ig : ∀ e → E.receptionOpen e ≡ true → S.ig (E.base e) ≡ S.igLive
reception-ig e opened with E.phase (E.exit e) | E.received (E.exit e) | S.stage (E.base e) | S.ig (E.base e) | IG.active (IG.execution (E.governor e))
... | E.live | nothing | S.igCancelRequested | S.igLive | true = refl
... | E.live | nothing | S.serving | _ | _ = case opened of λ ()
... | E.live | nothing | S.actionBodyExited | _ | _ = case opened of λ ()
... | E.live | nothing | S.actionResultAvailable | _ | _ = case opened of λ ()
... | E.live | nothing | S.closingAccept | _ | _ = case opened of λ ()
... | E.live | nothing | S.acceptCancelRequested | _ | _ = case opened of λ ()
... | E.live | nothing | S.acceptCancelDelivered | _ | _ = case opened of λ ()
... | E.live | nothing | S.acceptFailed | _ | _ = case opened of λ ()
... | E.live | nothing | (S.acceptForkClosing _ _) | _ | _ = case opened of λ ()
... | E.live | nothing | S.acceptBodyExited | _ | _ = case opened of λ ()
... | E.live | nothing | S.acceptResultAvailable | _ | _ = case opened of λ ()
... | E.live | nothing | S.acceptJoined | _ | _ = case opened of λ ()
... | E.live | nothing | S.serverStopped | _ | _ = case opened of λ ()
... | E.live | nothing | S.actionJoined | _ | _ = case opened of λ ()
... | E.live | nothing | S.igCancelRequested | S.igLive | false = case opened of λ ()
... | E.live | nothing | S.igCancelRequested | S.igCaught | _ = case opened of λ ()
... | E.live | nothing | S.igCancelRequested | S.igInactive | _ = case opened of λ ()
... | E.live | nothing | S.igCancelRequested | S.igFlushed | _ = case opened of λ ()
... | E.live | nothing | S.igCancelRequested | S.igBodyExited | _ = case opened of λ ()
... | E.live | nothing | S.igCancelRequested | S.igResultAvailable | _ = case opened of λ ()
... | E.live | nothing | S.igJoined | _ | _ = case opened of λ ()
... | E.live | nothing | S.closingCM | _ | _ = case opened of λ ()
... | E.live | nothing | S.serverReturned | _ | _ = case opened of λ ()
... | E.live | just _ | _ | _ | _ = case opened of λ ()
... | E.caught | _ | _ | _ | _ = case opened of λ ()
... | E.traversing | _ | _ | _ | _ = case opened of λ ()
... | E.invoked | _ | _ | _ | _ = case opened of λ ()
... | E.failed | _ | _ | _ | _ = case opened of λ ()
... | E.bodyDone | _ | _ | _ | _ = case opened of λ ()
failure-ig : ∀ e → E.failureOpen e ≡ true → S.ig (E.base e) ≡ S.igLive
failure-ig e opened with E.phase (E.exit e) | E.received (E.exit e) | S.ig (E.base e) | IG.active (IG.execution (E.governor e))
... | E.live | nothing | S.igLive | true = refl
... | E.live | nothing | S.igLive | false = case opened of λ ()
... | E.live | nothing | S.igCaught | _ = case opened of λ ()
... | E.live | nothing | S.igInactive | _ = case opened of λ ()
... | E.live | nothing | S.igFlushed | _ = case opened of λ ()
... | E.live | nothing | S.igBodyExited | _ = case opened of λ ()
... | E.live | nothing | S.igResultAvailable | _ = case opened of λ ()
... | E.live | just _ | _ | _ = case opened of λ ()
... | E.caught | _ | _ | _ = case opened of λ ()
... | E.traversing | _ | _ | _ = case opened of λ ()
... | E.invoked | _ | _ | _ = case opened of λ ()
... | E.failed | _ | _ | _ = case opened of λ ()
... | E.bodyDone | _ | _ | _ = case opened of λ ()

delegate-phase : ∀ b x {ex} → E.delegateExit b x ≡ just ex → E.phase ex ≡ E.phase x
delegate-phase (S.scope S.publishIGResult) x eq with E.phase x in ph | E.outcome x | E.result x
... | E.bodyDone | just err | nothing = case just-injective eq of λ { refl → ph }
... | E.bodyDone | just err | just _ = case eq of λ ()
... | E.bodyDone | nothing | _ = case eq of λ ()
... | E.live | _ | _ = case eq of λ ()
... | E.caught | _ | _ = case eq of λ ()
... | E.traversing | _ | _ = case eq of λ ()
... | E.invoked | _ | _ = case eq of λ ()
... | E.failed | _ | _ = case eq of λ ()
delegate-phase (S.scope (S.forkFailure sock err)) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.finishForkFailure) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.returnAction) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.publishActionResult) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.selectActionWinner) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.requestAcceptCancel) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.deliverAcceptAtWait) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.closeListener) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.publishAcceptResult) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.joinAccept) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.traceStopped) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.cancelJoinReturnedAction) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.requestIGCancel) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.deliverIGBody) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.deactivateIG) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.flushIG) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.finishIGBody) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.joinIG) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.beginCM) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.finishServer) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.failIGBody) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.igWins) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.acceptFails) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.scope S.interruptServer) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.closeForkFailure outcome) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.acceptedFork w req) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.run a) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.workerRestore w) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.workerReturned w) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.workerPrefixReturned w) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.workerPrefixException w err) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.workerException w err) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.workerClose w r) x eq = case just-injective eq of λ { refl → refl }
delegate-phase (S.workerResult w) x eq = case just-injective eq of λ { refl → refl }

receipt-ig : ∀ at err e {r} → E.selectReceipt at err e ≡ just r → S.ig (E.base e) ≡ S.igLive
receipt-ig at err e eq with E.receptionOpen e in opened
... | false = case eq of λ ()
... | true = reception-ig e opened
failure-receipt-ig : ∀ at err e {r} → E.selectFailure at err e ≡ just r → S.ig (E.base e) ≡ S.igLive
failure-receipt-ig at err e eq with E.failureOpen e in opened
... | false = case eq of λ ()
... | true = failure-ig e opened

-- A finished IG body after a Server step was finished before it (the IG
-- exit wrapper refuses the Server's own finishIGBody).
ig-done-back : ∀ b e {t} → E.runAllowed b e ≡ true → S.step b (E.base e) ≡ just t →
  IGD.done (S.ig t) ≡ true → IGD.done (S.ig (E.base e)) ≡ true
ig-done-back b e allowed eq d with IGD.step-ig b (E.base e) eq
... | inj₁ same = subst (λ g → IGD.done g ≡ true) same d
... | inj₂ (x , refl) with scope-parts x (E.base e) eq
...   | p , chosen , enacted with IGD.ig-entry x (E.base e) chosen (subst (λ g → IGD.done g ≡ true) (IGD.enact-scope-ig p (E.base e) enacted) d)
...     | inj₁ before = before
...     | inj₂ refl = case allowed of λ ()
ig-done-forward : ∀ b s {t} → S.step b s ≡ just t → IGD.done (S.ig s) ≡ true → IGD.done (S.ig t) ≡ true
ig-done-forward b s eq d with IGD.step-ig b s eq
... | inj₁ same = subst (λ g → IGD.done g ≡ true) (sym same) d
... | inj₂ (x , refl) with scope-parts x s eq
...   | p , chosen , enacted = subst (λ g → IGD.done g ≡ true) (sym (IGD.enact-scope-ig p s enacted)) (IGD.ig-stays x s chosen d)
stage-post-back : ∀ b s {t} → S.step b s ≡ just t → IGD.post (S.stage t) ≡ true →
  IGD.post (S.stage s) ≡ true ⊎ IGD.done (S.ig s) ≡ true
stage-post-back b s eq entered with Stage.step-stage b s eq
... | inj₁ same = inj₁ (subst (λ st → IGD.post st ≡ true) same entered)
... | inj₂ (x , refl) with scope-parts x s eq
...   | p , chosen , enacted with IGD.post-entry x s chosen (subst (λ st → IGD.post st ≡ true) (Stage.enact-scope-stage p s enacted) entered)
...     | inj₁ before = inj₁ before
...     | inj₂ (_ , d) = inj₂ d

run-inv : ∀ b e ex server → E.runAllowed b e ≡ true → E.delegateExit b (E.exit e) ≡ just ex →
  S.step b (E.base e) ≡ just server → InvE e → InvE (E.igExitState server ex)
run-inv b e ex server allowed delegated stepped (ia , ib , ic) =
  (λ after → server-quiet b (E.base e) stepped (ia (subst (λ ph → postCaught ph ≡ true) phase after))) ,
  (λ d → subst (λ ph → postCaught ph ≡ true) (sym phase) (ib (ig-done-back b e allowed stepped d))) ,
  (λ entered → ig-done-forward b (E.base e) stepped (case stage-post-back b (E.base e) stepped entered of λ
    { (inj₁ before) → ic before ; (inj₂ d) → d }))
  where phase = delegate-phase b (E.exit e) delegated

e-inv : ∀ a e {e′} → E.step a e ≡ just e′ → InvE e → InvE e′
e-inv E.captureSnapshot e eq inv with E.phase (E.exit e) | S.ig (E.base e) in igEq | IG.active (IG.execution (E.governor e)) in act |
  IG.continuation (E.governor e) in cont | Machine.inboundRelease (O.core (E.source e)) in rel | Machine.remoteCall (O.core (E.source e)) in rem |
  E.unique (IG.connections (IG.publishedState (E.governor e)))
... | E.live | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igLive | _ | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igCaught | _ | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igInactive | _ | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | true | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.sampleTime | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.exitFlush | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.exited | nothing | nothing | false = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.exited | nothing | just _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.exited | just _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.inCM | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.armInactivity _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.awaitBatch _ _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.readNext _ _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.prepareNew _ _ _ _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.startResponders _ _ _ _ _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.publishDecision _ _ _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.stopAfterFailure _ _ _ _ _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.waitStopped _ _ _ _ _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.restartResponder _ _ _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.awaitRemoteIdle _ _ _ _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.needsCM _ _ _ _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igBodyExited | _ | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igResultAvailable | _ | _ | _ | _ | _ = case eq of λ ()
... | E.traversing | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | E.invoked | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | E.failed | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | E.bodyDone | _ | _ | _ | _ | _ | _ = case eq of λ ()
... | E.caught | S.igFlushed | false | IG.exited | nothing | nothing | true = case just-injective eq of λ { refl → (λ _ → (cont , act) , rel , rem) ,
  (λ d → case trans (sym (cong IGD.done igEq)) d of λ ()) , (λ p → case proj₂ (proj₂ inv) p of λ ()) }
e-inv E.invokeFinal e eq inv with E.phase (E.exit e) | E.remaining (E.exit e)
... | E.traversing | row ∷ rest = case just-injective eq of λ { refl → (λ _ → proj₁ inv refl) , (λ _ → refl) , proj₂ (proj₂ inv) }
... | E.traversing | [] = case eq of λ ()
... | E.live | _ = case eq of λ ()
... | E.caught | _ = case eq of λ ()
... | E.invoked | _ = case eq of λ ()
... | E.failed | _ = case eq of λ ()
... | E.bodyDone | _ = case eq of λ ()
e-inv E.returnFinal e eq inv with E.phase (E.exit e) | E.remaining (E.exit e)
... | E.invoked | row ∷ rest = case just-injective eq of λ { refl → (λ _ → proj₁ inv refl) , (λ _ → refl) , proj₂ (proj₂ inv) }
... | E.invoked | [] = case eq of λ ()
... | E.live | _ = case eq of λ ()
... | E.caught | _ = case eq of λ ()
... | E.traversing | _ = case eq of λ ()
... | E.failed | _ = case eq of λ ()
... | E.bodyDone | _ = case eq of λ ()
e-inv (E.failFinal err) e eq inv with E.phase (E.exit e) | E.remaining (E.exit e)
... | E.invoked | row ∷ rest = case just-injective eq of λ { refl → (λ _ → proj₁ inv refl) , (λ _ → refl) , proj₂ (proj₂ inv) }
... | E.invoked | [] = case eq of λ ()
... | E.live | _ = case eq of λ ()
... | E.caught | _ = case eq of λ ()
... | E.traversing | _ = case eq of λ ()
... | E.failed | _ = case eq of λ ()
... | E.bodyDone | _ = case eq of λ ()
e-inv E.finishFinal e eq inv with E.phase (E.exit e) | E.remaining (E.exit e) | E.outcome (E.exit e) | S.ig (E.base e)
... | E.traversing | [] | just err | S.igFlushed = case just-injective eq of λ { refl → (λ _ → proj₁ inv refl) , (λ _ → refl) , (λ _ → refl) }
... | E.failed | _ | just err | S.igFlushed = case just-injective eq of λ { refl → (λ _ → proj₁ inv refl) , (λ _ → refl) , (λ _ → refl) }
... | E.traversing | _ ∷ _ | _ | _ = case eq of λ ()
... | E.traversing | [] | nothing | _ = case eq of λ ()
... | E.traversing | [] | just _ | S.igLive = case eq of λ ()
... | E.traversing | [] | just _ | S.igCaught = case eq of λ ()
... | E.traversing | [] | just _ | S.igInactive = case eq of λ ()
... | E.traversing | [] | just _ | S.igBodyExited = case eq of λ ()
... | E.traversing | [] | just _ | S.igResultAvailable = case eq of λ ()
... | E.failed | _ | nothing | _ = case eq of λ ()
... | E.failed | _ | just _ | S.igLive = case eq of λ ()
... | E.failed | _ | just _ | S.igCaught = case eq of λ ()
... | E.failed | _ | just _ | S.igInactive = case eq of λ ()
... | E.failed | _ | just _ | S.igBodyExited = case eq of λ ()
... | E.failed | _ | just _ | S.igResultAvailable = case eq of λ ()
... | E.live | _ | _ | _ = case eq of λ ()
... | E.caught | _ | _ | _ = case eq of λ ()
... | E.invoked | _ | _ | _ = case eq of λ ()
... | E.bodyDone | _ | _ | _ = case eq of λ ()
e-inv (E.receive at err) e eq inv with E.selectReceipt at err e in selected
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → (λ ()) , (λ ()) ,
  (λ entered → absurd-live (subst (λ g → IGD.done g ≡ true) (receipt-ig at err e selected) (proj₂ (proj₂ inv) entered))) }
e-inv (E.fail at f) e eq inv with E.selectFailure at (S.error f) e in selected
... | nothing = case eq of λ ()
... | just r = case just-injective eq of λ { refl → (λ ()) , (λ ()) ,
  (λ entered → absurd-live (subst (λ g → IGD.done g ≡ true) (failure-receipt-ig at (S.error f) e selected) (proj₂ (proj₂ inv) entered))) }
e-inv (E.run b) e eq inv with E.runAllowed b e in allowed
... | false = case eq of λ ()
... | true with E.delegateExit b (E.exit e) in delegated
...   | nothing = case eq of λ ()
...   | just ex with S.step b (E.base e) in stepped
...     | nothing = case eq of λ ()
...     | just server = case just-injective eq of λ { refl → run-inv b e ex server allowed delegated stepped inv }


-- Shared composition and runtime: the peer side changes only the source.
QP : O.Configuration → Set
QP = QC
private
  module Governor = GovernorCM.StepLift isIOManagerError QP
    (λ c g same (q , rel , rem) → MQ.same-control-quiet {Machine.inboundGovernor (O.core c)} {g} same q , rel , rem)
    (λ w r c eq q → MQ.outbound-quiet (O.beginAcquire w r) c eq q)
    (λ w k c eq q → MQ.outbound-quiet (O.beginRelease w k) c eq q)
    (λ mid c eq q → MQ.outbound-quiet (O.inbound (Machine.igStep (IG.monitorCompletion mid))) c eq q)
    (λ _ → ⊤) (λ a c _ eq q → MQ.outbound-quiet a c eq q)
    (λ w err context c eq q → subst MQ.QuietCore (sym (Writer.start-core w err context c eq)) q)
    (λ c world q → q) (λ c acquired q → q)
  all-allowed : ∀ a → Governor.Allowed a
  all-allowed (GP.run (Sub.core _)) = tt
  all-allowed (GP.run Sub.publishPublicState) = tt
  all-allowed (GP.run (Sub.sampleTime _)) = tt
  all-allowed (GP.run (Sub.applyAt _)) = tt
  all-allowed (GP.run (Sub.setTargets _)) = tt
  all-allowed (GP.run (Sub.selectMonitor _)) = tt
  all-allowed (GP.run Sub.selectCompletion) = tt
  all-allowed (GP.run Sub.selectTargets) = tt
  all-allowed (GP.run Sub.selectWakeup) = tt
  all-allowed (GP.run Sub.registerWakeup) = tt
  all-allowed (GP.run Sub.expireWakeup) = tt
  all-allowed (GP.run Sub.cancelWakeup) = tt
  all-allowed (GP.run Sub.publishCounters) = tt
  all-allowed (GP.run Sub.traceSelection) = tt
  all-allowed (GP.run (Sub.selectPolicy _)) = tt
  all-allowed (GP.run (Sub.forkJob _ _ _)) = tt
  all-allowed (GP.run Sub.registerJob) = tt
  all-allowed (GP.run Sub.finishLaunch) = tt
  all-allowed (GP.run (Sub.jobStep _ _)) = tt
  all-allowed (GP.run (Sub.enqueueCompletion _ _)) = tt
  all-allowed (GP.run (Sub.deregisterJob _)) = tt
  all-allowed (GP.run (Sub.protocolResult _ _ _)) = tt
  all-allowed (GP.run (Sub.publishInitiatorResult _ _)) = tt
  all-allowed (GP.run (Sub.pollPeer _ _)) = tt
  all-allowed (GP.run (Sub.monitorStep _ _)) = tt
  all-allowed (GP.run (Sub.monitorFinished _)) = tt
  all-allowed (GP.run (Sub.observeInitiatorFailure _)) = tt
  all-allowed (GP.handoff w) = tt
  all-allowed (GP.beginClose o) = tt
  all-allowed GP.requestCancel = tt
  all-allowed GP.join = tt
  all-allowed GP.finishClose = tt
  all-allowed (GP.deliverCancellation err) = tt
  all-allowed (GP.deliverOpenCancellation err) = tt
  all-allowed (GP.cleanup j a) = tt
  all-allowed (GP.bodyUnwound j) = tt
  all-allowed (GP.recoverCloseFailure j) = tt
  all-allowed (GP.deregisterCancelled j) = tt
  all-allowed (GP.publishAsyncResult j) = tt
  module Peer = SupervisionCM.Lift isIOManagerError QP
    (λ action s eq → Governor.step-preserves action s (all-allowed action) eq)
    (λ w err context c eq q → subst MQ.QuietCore (sym (Writer.start-core w err context c eq)) q)

peer-quiet : ∀ a b {p} → PS.step a (K.peers b) ≡ just p → QC (K.source b) → QC (PS.cm p)
peer-quiet a b eq q = Peer.step-preserves a (K.peers b) eq
  (subst QC (sym (C.source-exact (K.source b) (K.context b))) q)

k-inv : ∀ a b {b′} → K.step a b ≡ just b′ → InvE (K.server b) → InvE (K.server b′)
k-inv (K.serverStep a) b eq inv with K.serverAllowed a b
... | false = case eq of λ ()
... | true with E.step a (K.server b) in stepped
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → e-inv a (K.server b) stepped inv }
k-inv (K.coreStep a) b eq inv with K.coreAllowed a b
... | false = case eq of λ ()
... | true with E.step (K.coreAction a) (K.server b) in stepped
...   | nothing = case eq of λ ()
...   | just e = case just-injective eq of λ { refl → e-inv (K.coreAction a) (K.server b) stepped inv }
k-inv (K.peerStep a) b eq (ia , ib , ic) with K.peerOpen b ∧ K.peerAllowed a b
... | false = case eq of λ ()
... | true with PS.step a (K.peers b) in stepped
...   | nothing = case eq of λ ()
...   | just p = case just-injective eq of λ { refl → (λ after → peer-quiet a b stepped (ia after)) , ib , ic }

module Protocols (canInitiate : HandleId → ℕ → Bool) where
  private
    module T = K.Protocols canInitiate
    module Outer = SR.Protocols canInitiate
    module Certified = RelaysFacts.Certified T.advance Outer.runtimeReturned
    module Done = SI5a.Protocols canInitiate
  Inv : T.Runtime → Set
  Inv s = InvE (K.server (T.base s))
  enact-inv : ∀ p s {t} → T.enact p s ≡ just t → Inv s → Inv t
  enact-inv (T.inherit a f) s eq inv with K.step a (T.base s) in stepped
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → k-inv a (T.base s) stepped inv }
  enact-inv (T.caller a f) s eq (ia , ib , ic) with PS.step a (K.peers (T.base s)) in stepped
  ... | nothing = case eq of λ ()
  ... | just p = case just-injective eq of λ { refl → (λ after → peer-quiet a (T.base s) stepped (ia after)) , ib , ic }
  enact-inv (T.local f) s eq inv = case just-injective eq of λ { refl → inv }
  enact-inv (T.reading r) s eq inv = case just-injective eq of λ { refl → inv }
  enact-inv (T.traceFault w rid result fs) s eq inv = case just-injective eq of λ { refl → inv }
  enact-inv (T.deliverTraceFault w rid result fs coordinator) s eq inv = case just-injective eq of λ { refl → inv }
  enact-inv (T.birth w capturedFrame pool j rid r f) s eq inv = case just-injective eq of λ { refl → inv }
  enact-inv (T.complete a rid r result) s eq inv with K.step a (T.base s) in stepped
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl →
    subst InvE (sym (SI5a.Protocols.cache-server canInitiate rid r result (T.front s) b)) (k-inv a (T.base s) stepped inv) }
  advance-inv : ∀ a s {t} → T.advance a s ≡ just t → Inv s → Inv t
  advance-inv a s eq with T.choose a s
  ... | nothing = case eq of λ ()
  ... | just p = enact-inv p s eq
  runs-inv : ∀ {s as t} → T.Runs s as t → Inv s → Inv t
  runs-inv T.stop inv = inv
  runs-inv (T.more {s = s} {a = a} eq rest) inv = runs-inv rest (advance-inv a s eq inv)

  -- Initialization: the IG exit is live, the IG thread live, the Server serving.
  initial-inv : ∀ c g {s} → T.initialize c g ≡ just s → Inv s
  initial-inv c g eq with K.initial c g in kInit
  ... | nothing = case eq of λ ()
  ... | just b = case just-injective eq of λ { refl → k-initial c g kInit }
    where
    s-initial : ∀ c {s} → S.initial c ≡ just s → S.ig s ≡ S.igLive × S.stage s ≡ S.serving
    s-initial c eq with Shared.admissions (Machine.world (O.core c)) | Shared.sockets (Machine.world (O.core c)) | N.initial c
    ... | [] | [] | just n = case just-injective eq of λ { refl → refl , refl }
    ... | [] | [] | nothing = case eq of λ ()
    ... | [] | _ ∷ _ | _ = case eq of λ ()
    ... | _ ∷ _ | _ | _ = case eq of λ ()
    e-initial : ∀ c {e} → E.initial c ≡ just e → InvE e
    e-initial c eq with Machine.inboundRelease (O.core c) | Machine.remoteCall (O.core c) | S.initial c in sInit
    ... | nothing | nothing | just server = case just-injective eq of λ { refl →
      (λ ()) ,
      (λ d → absurd-live (subst (λ g → IGD.done g ≡ true) (proj₁ (s-initial c sInit)) d)) ,
      (λ entered → case subst (λ st → IGD.post st ≡ true) (proj₂ (s-initial c sInit)) entered of λ ()) }
    ... | nothing | nothing | nothing = case eq of λ ()
    ... | nothing | just _ | _ = case eq of λ ()
    ... | just _ | _ | _ = case eq of λ ()
    k-initial : ∀ c g {b} → K.initial c g ≡ just b → InvE (K.server b)
    k-initial c g eq with E.initial c in eInit
    ... | nothing = case eq of λ ()
    ... | just e = case just-injective eq of λ { refl → e-initial c eInit }

  -- c1: at the finished outer state the inbound governor is exited and
  -- deactivated, and has neither a pending release nor a pending remote call.
  record IGQuiet (final : T.Runtime) : Set where
    field
      exited : IG.continuation (Machine.inboundGovernor (O.core (T.sourceOf final))) ≡ IG.exited
      inactive : IG.active (IG.execution (Machine.inboundGovernor (O.core (T.sourceOf final)))) ≡ false
      noRelease : Machine.inboundRelease (O.core (T.sourceOf final)) ≡ nothing
      noRemote : Machine.remoteCall (O.core (T.sourceOf final)) ≡ nothing

  ig-quiet : ∀ {c g start scheduled as final t} → T.initialize c g ≡ just start →
    Outer.Executes (Outer.outer start (RR.initial scheduled)) as (Outer.outer final (RR.relaysState t RR.finished)) →
    IGQuiet final
  ig-quiet {c} {g} {final = final} initialized path with Done.outer-runs path | Done.complete initialized path
  ... | events , inner | certificate with runs-inv inner (initial-inv c g initialized)
  ...   | ia , ib , ic with ia (ib (ic (subst (λ st → IGD.post st ≡ true) (sym (Done.Complete.serverReturned certificate)) refl)))
  ...     | (exitedNow , inactiveNow) , rel , rem = record
    { exited = exitedNow ; inactive = inactiveNow ; noRelease = rel ; noRemote = rem }

{-# OPTIONS --guardedness #-}

-- Close-failure recovery may write acquired only for a detached job caller.
-- The supporting metadata and A/R derive that caller's frame absence.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesRecovery
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Maybe using (just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (JobId; WorkerId)
open import ConnectionManagement.Store using (lookup; put; delete)
open import ConnectionManagement.Properties.Stores using (delete-unique; lookup-put-other)
open import ConnectionManagement.Properties.OwnedFramesStores using (delete-self; delete-other)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob; unwinding-no-frames)

-- Publishing to an absent acquisition caller preserves the exact A/R clauses.
acquired-absent-inv : ∀ c k w result → lookup w (O.acquiring c) ≡ nothing → Inv c k →
  Inv (record c { acquired = put w result (O.acquired c) }) k
acquired-absent-inv c k w result absent inv = owned-frames acq (releasing inv)
  where
  acq : ∀ q → is-just (lookup q (O.acquiring c)) ≡ true →
    lookup q (put w result (O.acquired c)) ≡ nothing × Owner q J.awaitAcquire k
  acq q present with q ≟ w
  ... | yes refl = case trans (sym (cong is-just absent)) present of λ ()
  ... | no apart = trans (lookup-put-other w q result (O.acquired c) apart)
    (proj₁ (acquiring inv q present)) , proj₂ (acquiring inv q present)

-- Named recovery writer; the canceled handle resumes and its unwind row leaves.
recover-context : C.Context → JobId → WorkerId → GP.Pool.State → C.Context
recover-context k j w p = record k
  { governorPool = p; unwinding = delete j (C.unwinding k)
  ; regions = put w Cancel.ordinary (C.regions k) }

-- Resuming a non-running handle preserves all pre-existing ownership witnesses.
resume-owner : ∀ k j w p → lookup j (GP.Pool.handles (C.governorPool k)) ≡ just GP.Pool.bodyUnwinding →
  GP.Pool.handles p ≡ put j GP.Pool.bodyRunning (GP.Pool.handles (C.governorPool k)) →
  ∀ q pc → Owner q pc k → Owner q pc (recover-context k j w p)
resume-owner k j w p unwound handles q pc (inj₁ foreign) = inj₁ foreign
resume-owner k j w p unwound handles q pc (inj₂ (inj₁ owner)) with JobAwait.job owner ≟ j
... | yes refl = case trans (sym unwound) (JobAwait.running owner) of λ ()
... | no apart = inj₂ (inj₁ (job-await (JobAwait.job owner) (JobAwait.frame owner)
  (JobAwait.found owner) (JobAwait.caller owner) (JobAwait.waiting owner)
  (trans (cong (lookup (JobAwait.job owner)) handles)
    (trans (lookup-put-other j (JobAwait.job owner) GP.Pool.bodyRunning (GP.Pool.handles (C.governorPool k)) apart) (JobAwait.running owner)))))
resume-owner k j w p unwound handles q pc (inj₂ (inj₂ owner)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref owner) (FollowAwait.frame owner) (FollowAwait.found owner)
    (FollowAwait.caller owner) (FollowAwait.waiting owner) (FollowAwait.tid owner)
    (FollowAwait.thread owner) (FollowAwait.byPeer owner) (FollowAwait.worker owner)
    (FollowAwait.running owner) (FollowAwait.observing owner)))

-- Followups do not observe the resumed governor handle or the region note.
recover-follow : ∀ k j w p ref f → FollowThread ref f k → FollowThread ref f (recover-context k j w p)
recover-follow k j w p ref f old = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old
  ; found = FollowThread.found old; caller = FollowThread.caller old
  ; running = FollowThread.running old; observing = FollowThread.observing old }

-- Deletion of the unique unwind row removes the only non-running obligation
-- for the resumed handle; all other detached handles are untouched.
recover-aux : ∀ k j w p →
  GP.Pool.handles p ≡ put j GP.Pool.bodyRunning (GP.Pool.handles (C.governorPool k)) →
  Aux k → Aux (recover-context k j w p)
recover-aux k j w p handles old = record
  { jobKeys = Aux.jobKeys old; monitorKeys = Aux.monitorKeys old; followKeys = Aux.followKeys old
  ; unwindKeys = delete-unique j (C.unwinding k) (Aux.unwindKeys old)
  ; jobCallers = Aux.jobCallers old; jobNotMonitor = Aux.jobNotMonitor old
  ; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = λ ref f found → recover-follow k j w p ref f (Aux.followThreads old ref f found)
  ; unwindingJobs = unwinds }
  where
  unwinds : ∀ q f → lookup q (delete j (C.unwinding k)) ≡ just f → UnwindJob q f (recover-context k j w p)
  unwinds q f found with q ≟ j
  ... | yes refl = case trans (sym (delete-self j (C.unwinding k) (Aux.unwindKeys old))) found of λ ()
  ... | no apart = record
    { frame = UnwindJob.frame backing; found = UnwindJob.found backing
    ; caller = UnwindJob.caller backing; phase = UnwindJob.phase backing
    ; handle = trans (cong (lookup q) handles)
        (trans (lookup-put-other j q GP.Pool.bodyRunning (GP.Pool.handles (C.governorPool k)) apart) (UnwindJob.handle backing))
    ; notRunning = UnwindJob.notRunning backing }
    where
    backing = Aux.unwindingJobs old q f (trans (sym (delete-other j q (C.unwinding k) apart)) found)

-- The recovered exception is published only after Unw supplies frame absence.
recover-inv : ∀ c k j f err p → lookup j (C.unwinding k) ≡ just f →
  lookup j (GP.Pool.handles (C.governorPool k)) ≡ just GP.Pool.bodyUnwinding →
  GP.Pool.handles p ≡ put j GP.Pool.bodyRunning (GP.Pool.handles (C.governorPool k)) →
  Inv c k → Aux k →
  Inv (record c { acquired = put (Cancel.caller f) (Cases.raised (Cases.ioFailure err)) (O.acquired c) })
    (recover-context k j (Cancel.caller f) p)
recover-inv c k j f err p found unwound handles inv aux = owned-frames
  (λ q present → let old = acquiring published q present in
    proj₁ old , resume-owner k j (Cancel.caller f) p unwound handles q J.awaitAcquire (proj₂ old))
  (λ q present → let old = releasing published q present in
    proj₁ old , resume-owner k j (Cancel.caller f) p unwound handles q J.awaitRelease (proj₂ old))
  where
  published = acquired-absent-inv c k (Cancel.caller f) (Cases.raised (Cases.ioFailure err))
    (proj₁ (unwinding-no-frames c k inv aux j f found)) inv

open import ConnectionManagement.Properties.OutboundKeys using (Unique)
import ConnectionManagement.Properties.OwnedFramesUniquePeers as UniqueFacts
import ConnectionManagement.Properties.OwnedFramesCancellation as CancellationFacts
import ConnectionManagement.Properties.OwnedFramesReach as FullReach
private
  module U = UniqueFacts isIOManagerError
  module D = CancellationFacts isBearerClosed isIOManagerError
  module R = FullReach isBearerClosed isIOManagerError

-- The actual resume writer requires an unwinding handle and changes only it.
resume-fields : ∀ j p {p′} → GP.Pool.step (GP.Pool.resumeAfterUnwindError j) p ≡ just p′ →
  lookup j (GP.Pool.handles p) ≡ just GP.Pool.bodyUnwinding ×
  GP.Pool.handles p′ ≡ put j GP.Pool.bodyRunning (GP.Pool.handles p)
resume-fields j p stepped with lookup j (GP.Pool.handles p) in found
... | just GP.Pool.bodyUnwinding = case just-injective stepped of λ { refl → refl , refl }
... | nothing = case stepped of λ ()
... | just GP.Pool.bodyRunning = case stepped of λ ()
... | just (GP.Pool.bodyReturned _) = case stepped of λ ()
... | just (GP.Pool.deregisterPending _) = case stepped of λ ()
... | just (GP.Pool.deregistered _) = case stepped of λ ()
... | just (GP.Pool.resultAvailable _) = case stepped of λ ()

-- Concrete governor recovery composes the source result write, handle resume,
-- unique unwind deletion and caller-region update without assuming Unw.
governor-recovery : ∀ j s {g′} → GP.step (GP.recoverCloseFailure j) (PS.governor s) ≡ just g′ →
  D.Held s → D.Held (record s { governor = g′ })
governor-recovery j s eq (inv , unique , aux) with lookup j (GP.unwinding (PS.governor s)) in found | lookup j (Sub.jobs (PS.machine s))
... | just f | just jf with Cancel.pc f | Cancel.original f | J.pc (Sub.execution jf)
...   | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring _ | J.awaitAcquire with
  GP.Pool.step (GP.Pool.resumeAfterUnwindError j) (GP.pool (PS.governor s)) in resumed
...     | just p′ = let facts = resume-fields j (GP.pool (PS.governor s)) resumed in
  case just-injective eq of λ { refl →
    recover-inv (PS.cm s) (C.capture s) j f err p′ found (proj₁ facts) (proj₂ facts) inv aux ,
    U.acquired-put (PS.cm s) (Cancel.caller f) (Cases.raised (Cases.ioFailure err)) unique ,
    recover-aux (C.capture s) j (Cancel.caller f) p′ (proj₂ facts) aux }
...     | nothing = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.cleaning active | _ | _ = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished Cancel.abandoned | _ | _ = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished Cancel.cleanupComplete | _ | _ = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.noCaller | _ = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.releasing active | _ = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.begin = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.startBundle t ns) = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.publishBundle t) = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.markWarm = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.forkMonitor = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.finishActivation = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitHot = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitAll = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.callRelease = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.awaitRelease = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | J.delayFailure = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.awaitCold result) = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.complete result) = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.acquirePolicy fault) = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeDelivery fault) = case eq of λ ()
governor-recovery j s eq held | just f | just jf | Cancel.finished (Cancel.socketCloseFailed err) | Cancel.acquiring active | (J.nodeRethrow fault) = case eq of λ ()
governor-recovery j s eq held | nothing | _ = case eq of λ ()
governor-recovery j s eq held | just f | nothing = case eq of λ ()

-- The PS adapter retains the exact recovery writer and its original guards.
recovery : ∀ j s {t} → PS.step (PS.run (GP.recoverCloseFailure j)) s ≡ just t → D.Held s → D.Held t
recovery j s stepped held with GP.step (GP.recoverCloseFailure j) (PS.governor s) in recovered
... | nothing = case stepped of λ ()
... | just g′ = case just-injective stepped of λ { refl → governor-recovery j s recovered held }

-- The concrete K recovery action preserves the full requested predicate.
k-recovery : ∀ j s {t} → K.step (K.peerStep (PS.run (GP.recoverCloseFailure j))) s ≡ just t → R.Reach s → R.Reach t
k-recovery j s stepped held with K.peerOpen s ∧ K.peerAllowed (PS.run (GP.recoverCloseFailure j)) s
... | false = case stepped of λ ()
... | true with PS.step (PS.run (GP.recoverCloseFailure j)) (K.peers s) in recovered
...   | nothing = case stepped of λ ()
...   | just p = case just-injective stepped of λ { refl → recovery j (K.peers s) recovered held }

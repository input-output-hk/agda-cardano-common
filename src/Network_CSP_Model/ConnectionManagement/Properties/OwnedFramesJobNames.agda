{-# OPTIONS --guardedness #-}

-- Caller identity transport across job-frame updates. Mutable continuation
-- fields do not affect the caller partition used by ownership and cancellation.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesJobNames
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (JobId; WorkerId)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Stores using (UniqueKeys; put-unique; lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Properties.OwnedFramesIdentity as Identity
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob)

-- Every old/new lookup has a corresponding row with exactly the same caller.
record SameJobs (before after : Store JobId Sub.JobFrame) : Set where
  field
    forward : ∀ j jf → lookup j before ≡ just jf →
      Σ Sub.JobFrame (λ next → lookup j after ≡ just next × J.caller (Sub.execution next) ≡ J.caller (Sub.execution jf))
    backward : ∀ j jf → lookup j after ≡ just jf →
      Σ Sub.JobFrame (λ old → lookup j before ≡ just old × J.caller (Sub.execution old) ≡ J.caller (Sub.execution jf))
    unowned : ∀ w → GP.unowned w after ≡ GP.unowned w before

-- Explicit equality-decision cases avoid rewriting a projected worker under
-- DecEq's generated with-function.
unowned-head : ∀ w j old next rows → J.caller (Sub.execution next) ≡ J.caller (Sub.execution old) →
  GP.unowned w ((j , next) ∷ rows) ≡ GP.unowned w ((j , old) ∷ rows)
unowned-head w j old next rows caller with w ≟ J.caller (Sub.execution next) | w ≟ J.caller (Sub.execution old)
... | yes same | yes other = refl
... | yes same | no apart = ⊥-elim (apart (trans same caller))
... | no apart | yes same = ⊥-elim (apart (trans same (sym caller)))
... | no apart | no other = refl

-- Updating the actual first binding without changing its caller preserves the
-- structural unowned traversal, including any rows after that binding.
unowned-put : ∀ w j old next rows → lookup j rows ≡ just old →
  J.caller (Sub.execution next) ≡ J.caller (Sub.execution old) →
  GP.unowned w (put j next rows) ≡ GP.unowned w rows
unowned-put w j old next [] () caller
unowned-put w j old next ((q , jf) ∷ rows) found caller with j ≟ q
... | yes refl with just-injective found
...   | refl = unowned-head w j old next rows caller
unowned-put w j old next ((q , jf) ∷ rows) found caller | no apart with w ≟ J.caller (Sub.execution jf)
... | yes same = refl
... | no other = unowned-put w j old next rows found caller

-- A replacement of an existing job with the same caller realizes SameJobs.
replace-jobs : ∀ rows j old next → lookup j rows ≡ just old →
  J.caller (Sub.execution next) ≡ J.caller (Sub.execution old) → SameJobs rows (put j next rows)
replace-jobs rows j old next found caller = record
  { forward = forth; backward = back
  ; unowned = λ w → unowned-put w j old next rows found caller }
  where
  forth : ∀ q jf → lookup q rows ≡ just jf →
    Σ Sub.JobFrame (λ f → lookup q (put j next rows) ≡ just f × J.caller (Sub.execution f) ≡ J.caller (Sub.execution jf))
  forth q jf present with q ≟ j
  ... | yes refl with just-injective (trans (sym found) present)
  ...   | refl = next , lookup-put j next rows , caller
  forth q jf present | no apart = jf , trans (lookup-put-other j q next rows apart) present , refl
  back : ∀ q jf → lookup q (put j next rows) ≡ just jf →
    Σ Sub.JobFrame (λ f → lookup q rows ≡ just f × J.caller (Sub.execution f) ≡ J.caller (Sub.execution jf))
  back q jf present with q ≟ j
  ... | yes refl with just-injective (trans (sym (lookup-put j next rows)) present)
  ...   | refl = old , found , sym caller
  back q jf present | no apart = jf , trans (sym (lookup-put-other j q next rows apart)) present , refl

-- Named writer for job metadata; its source and all pool/thread fields are absent.
job-context : C.Context → Store JobId Sub.JobFrame → C.Context
job-context k rows = record k { subsystem = record (C.subsystem k) { jobs = rows } }

-- Followup attachment does not depend on the job table.
job-follow : ∀ k rows ref f → FollowThread ref f k → FollowThread ref f (job-context k rows)
job-follow k rows ref f old = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old
  ; found = FollowThread.found old; caller = FollowThread.caller old
  ; running = FollowThread.running old; observing = FollowThread.observing old }

-- Existing detached callers keep their job backing after caller-preserving edits.
job-unwind : ∀ k rows → SameJobs (C.SubContext.jobs (C.subsystem k)) rows →
  ∀ j f → UnwindJob j f k → UnwindJob j f (job-context k rows)
job-unwind k rows same j f old with SameJobs.forward same j (UnwindJob.frame old) (UnwindJob.found old)
... | next , found , caller = record
  { frame = next; found = found; caller = trans (UnwindJob.caller old) (sym caller)
  ; phase = UnwindJob.phase old; handle = UnwindJob.handle old; notRunning = UnwindJob.notRunning old }

-- Caller uniqueness, disjointness and unwind correspondence all transport.
job-aux : ∀ k rows → UniqueKeys rows → SameJobs (C.SubContext.jobs (C.subsystem k)) rows →
  Aux k → Aux (job-context k rows)
job-aux k rows unique same old = record
  { jobKeys = unique; monitorKeys = Aux.monitorKeys old; followKeys = Aux.followKeys old
  ; unwindKeys = Aux.unwindKeys old; jobCallers = callers; jobNotMonitor = disjoint
  ; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = λ ref f found → job-follow k rows ref f (Aux.followThreads old ref f found)
  ; unwindingJobs = λ j f found → job-unwind k rows same j f (Aux.unwindingJobs old j f found) }
  where
  callers : ∀ j jf q qf → lookup j rows ≡ just jf → lookup q rows ≡ just qf →
    J.caller (Sub.execution jf) ≡ J.caller (Sub.execution qf) → j ≡ q
  callers j jf q qf found₁ found₂ caller with SameJobs.backward same j jf found₁ | SameJobs.backward same q qf found₂
  ... | old₁ , before₁ , same₁ | old₂ , before₂ , same₂ =
    Aux.jobCallers old j old₁ q old₂ before₁ before₂ (trans same₁ (trans caller (sym same₂)))
  disjoint : ∀ j jf → lookup j rows ≡ just jf → PS.byWorker (J.caller (Sub.execution jf)) (C.monitors k) ≡ nothing
  disjoint j jf found with SameJobs.backward same j jf found
  ... | previous , before , caller = subst (λ w → PS.byWorker w (C.monitors k) ≡ nothing) caller
    (Aux.jobNotMonitor old j previous before)

-- Every successful J.step preserves the job caller partition and all Aux
-- clauses before the separate physical handle-return update.
job-step-aux : ∀ k j jf a w {next w′} →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  J.step a (Sub.execution jf) w ≡ just (next , w′) → Aux k →
  Aux (job-context k (put j (record jf { execution = next }) (C.SubContext.jobs (C.subsystem k))))
job-step-aux k j jf a w found stepped old = job-aux k _
  (put-unique j _ _ (Aux.jobKeys old))
  (replace-jobs _ j jf _ found (Identity.step-caller a (Sub.execution jf) w stepped)) old

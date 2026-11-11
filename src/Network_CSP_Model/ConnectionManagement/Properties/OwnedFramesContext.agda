{-# OPTIONS --guardedness #-}

-- Frame ownership observes six pieces of context. All scheduling, peer-world,
-- scope, policy, region and pool-cursor fields can be supplied independently.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesContext
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob)

-- Copy exactly the observed fields into an arbitrary target context.
copy-observed : C.Context → C.Context → C.Context
copy-observed k target = record target
  { subsystem = record (C.subsystem target)
      { jobs = C.SubContext.jobs (C.subsystem k)
      ; monitors = C.SubContext.monitors (C.subsystem k) }
  ; governorPool = record (C.governorPool target) { handles = GP.Pool.handles (C.governorPool k) }
  ; monitorPool = record (C.monitorPool target) { handles = PS.Pool.handles (C.monitorPool k) }
  ; monitors = C.monitors k; unwinding = C.unwinding k }

-- Every exact owner witness is independent of the remaining context fields.
copy-owner : ∀ k target w pc → Owner w pc k → Owner w pc (copy-observed k target)
copy-owner k target w pc (inj₁ foreign) = inj₁ foreign
copy-owner k target w pc (inj₂ (inj₁ old)) = inj₂ (inj₁
  (job-await (JobAwait.job old) (JobAwait.frame old) (JobAwait.found old)
    (JobAwait.caller old) (JobAwait.waiting old) (JobAwait.running old)))
copy-owner k target w pc (inj₂ (inj₂ old)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref old) (FollowAwait.frame old) (FollowAwait.found old)
    (FollowAwait.caller old) (FollowAwait.waiting old) (FollowAwait.tid old)
    (FollowAwait.thread old) (FollowAwait.byPeer old) (FollowAwait.worker old)
    (FollowAwait.running old) (FollowAwait.observing old)))

-- This transport retains A/R exactly, including both empty-result consequences.
copy-inv : ∀ c k target → Inv c k → Inv c (copy-observed k target)
copy-inv c k target inv = owned-frames
  (λ w present → let old = acquiring inv w present in
    proj₁ old , copy-owner k target w _ (proj₂ old))
  (λ w present → let old = releasing inv w present in
    proj₁ old , copy-owner k target w _ (proj₂ old))

-- Followup attachment uses only the copied tables and monitor handles.
copy-follow : ∀ k target ref f → FollowThread ref f k → FollowThread ref f (copy-observed k target)
copy-follow k target ref f old = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old
  ; found = FollowThread.found old; caller = FollowThread.caller old
  ; running = FollowThread.running old; observing = FollowThread.observing old }

-- Detached-job correspondence uses only copied jobs and governor handles.
copy-unwind : ∀ k target j f → UnwindJob j f k → UnwindJob j f (copy-observed k target)
copy-unwind k target j f old = record
  { frame = UnwindJob.frame old; found = UnwindJob.found old
  ; caller = UnwindJob.caller old; phase = UnwindJob.phase old
  ; handle = UnwindJob.handle old; notRunning = UnwindJob.notRunning old }

-- All auxiliary clauses therefore ignore the other scheduling/world fields.
copy-aux : ∀ k target → Aux k → Aux (copy-observed k target)
copy-aux k target old = record
  { jobKeys = Aux.jobKeys old; monitorKeys = Aux.monitorKeys old
  ; followKeys = Aux.followKeys old; unwindKeys = Aux.unwindKeys old
  ; jobCallers = Aux.jobCallers old; jobNotMonitor = Aux.jobNotMonitor old
  ; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = λ ref f found → copy-follow k target ref f (Aux.followThreads old ref f found)
  ; unwindingJobs = λ j f found → copy-unwind k target j f (Aux.unwindingJobs old j f found) }

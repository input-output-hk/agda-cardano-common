{-# OPTIONS --guardedness #-}

-- Transport exact ownership through stable changes of either physical pool.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesPoolTransport
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesPoolStable as Kernel
import ConnectionManagement.Properties.OwnedFramesCancellation as Cancellation
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob)
module G = Kernel GP.Body true
module B = Kernel (Maybe ErrorId) false
private module D = Cancellation isBearerClosed isIOManagerError

-- Named writers leave all caller, job, followup and thread tables unchanged.
gov-context : C.Context → GP.Pool.State → C.Context
gov-context k p = record k { governorPool = p }
bg-context : C.Context → PS.Pool.State → C.Context
bg-context k p = record k { monitorPool = p }

-- A stable governor pool preserves the running-body part of each job owner.
gov-owner : ∀ k p → G.Stable (C.governorPool k) p → ∀ w pc → Owner w pc k → Owner w pc (gov-context k p)
gov-owner k p stable w pc (inj₁ foreign) = inj₁ foreign
gov-owner k p stable w pc (inj₂ (inj₁ old)) = inj₂ (inj₁
  (job-await (JobAwait.job old) (JobAwait.frame old) (JobAwait.found old)
    (JobAwait.caller old) (JobAwait.waiting old) (G.Stable.running stable (JobAwait.job old) (JobAwait.running old))))
gov-owner k p stable w pc (inj₂ (inj₂ old)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref old) (FollowAwait.frame old) (FollowAwait.found old)
    (FollowAwait.caller old) (FollowAwait.waiting old) (FollowAwait.tid old) (FollowAwait.thread old)
    (FollowAwait.byPeer old) (FollowAwait.worker old) (FollowAwait.running old) (FollowAwait.observing old)))

-- A stable monitor pool preserves the corresponding part of a followup owner.
bg-owner : ∀ k p → B.Stable (C.monitorPool k) p → ∀ w pc → Owner w pc k → Owner w pc (bg-context k p)
bg-owner k p stable w pc (inj₁ foreign) = inj₁ foreign
bg-owner k p stable w pc (inj₂ (inj₁ old)) = inj₂ (inj₁
  (job-await (JobAwait.job old) (JobAwait.frame old) (JobAwait.found old)
    (JobAwait.caller old) (JobAwait.waiting old) (JobAwait.running old)))
bg-owner k p stable w pc (inj₂ (inj₂ old)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref old) (FollowAwait.frame old) (FollowAwait.found old)
    (FollowAwait.caller old) (FollowAwait.waiting old) (FollowAwait.tid old) (FollowAwait.thread old)
    (FollowAwait.byPeer old) (FollowAwait.worker old)
    (B.Stable.running stable (FollowAwait.tid old) (FollowAwait.running old)) (FollowAwait.observing old)))

-- A/R retain their exact result-table consequences through either transport.
gov-inv : ∀ c k p → G.Stable (C.governorPool k) p → Inv c k → Inv c (gov-context k p)
gov-inv c k p stable inv = owned-frames
  (λ w found → let old = acquiring inv w found in proj₁ old , gov-owner k p stable w _ (proj₂ old))
  (λ w found → let old = releasing inv w found in proj₁ old , gov-owner k p stable w _ (proj₂ old))
bg-inv : ∀ c k p → B.Stable (C.monitorPool k) p → Inv c k → Inv c (bg-context k p)
bg-inv c k p stable inv = owned-frames
  (λ w found → let old = acquiring inv w found in proj₁ old , bg-owner k p stable w _ (proj₂ old))
  (λ w found → let old = releasing inv w found in proj₁ old , bg-owner k p stable w _ (proj₂ old))

-- Detached governor callers retain their non-running historical handles.
gov-unwind : ∀ k p → G.Stable (C.governorPool k) p → ∀ j f → UnwindJob j f k → UnwindJob j f (gov-context k p)
gov-unwind k p stable j f old with G.Stable.stopped stable j (UnwindJob.phase old) (UnwindJob.handle old) (UnwindJob.notRunning old)
... | next , found , stopped = record
  { frame = UnwindJob.frame old; found = UnwindJob.found old; caller = UnwindJob.caller old
  ; phase = next; handle = found; notRunning = stopped }

-- The independent pool does not participate in a followup's thread attachment.
gov-follow : ∀ k p ref f → FollowThread ref f k → FollowThread ref f (gov-context k p)
gov-follow k p ref f old = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old; found = FollowThread.found old
  ; caller = FollowThread.caller old; running = FollowThread.running old; observing = FollowThread.observing old }

-- A stable monitor pool retains every active followup's running handle.
bg-follow : ∀ k p → B.Stable (C.monitorPool k) p → ∀ ref f → FollowThread ref f k → FollowThread ref f (bg-context k p)
bg-follow k p stable ref f old = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old; found = FollowThread.found old; caller = FollowThread.caller old
  ; running = B.Stable.running stable (FollowThread.tid old) (FollowThread.running old); observing = FollowThread.observing old }

-- Governor unwind backing ignores the independent monitor pool.
bg-unwind : ∀ k p j f → UnwindJob j f k → UnwindJob j f (bg-context k p)
bg-unwind k p j f old = record
  { frame = UnwindJob.frame old; found = UnwindJob.found old; caller = UnwindJob.caller old
  ; phase = UnwindJob.phase old; handle = UnwindJob.handle old; notRunning = UnwindJob.notRunning old }

-- All auxiliary clauses survive the stable governor-pool update.
gov-aux : ∀ k p → G.Stable (C.governorPool k) p → Aux k → Aux (gov-context k p)
gov-aux k p stable old = record
  { jobKeys = Aux.jobKeys old; monitorKeys = Aux.monitorKeys old; followKeys = Aux.followKeys old; unwindKeys = Aux.unwindKeys old
  ; jobCallers = Aux.jobCallers old; jobNotMonitor = Aux.jobNotMonitor old; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = λ ref f found → gov-follow k p ref f (Aux.followThreads old ref f found)
  ; unwindingJobs = λ j f found → gov-unwind k p stable j f (Aux.unwindingJobs old j f found) }

-- All auxiliary clauses likewise survive a stable monitor-pool update.
bg-aux : ∀ k p → B.Stable (C.monitorPool k) p → Aux k → Aux (bg-context k p)
bg-aux k p stable old = record
  { jobKeys = Aux.jobKeys old; monitorKeys = Aux.monitorKeys old; followKeys = Aux.followKeys old; unwindKeys = Aux.unwindKeys old
  ; jobCallers = Aux.jobCallers old; jobNotMonitor = Aux.jobNotMonitor old; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = λ ref f found → bg-follow k p stable ref f (Aux.followThreads old ref f found)
  ; unwindingJobs = λ j f found → bg-unwind k p j f (Aux.unwindingJobs old j f found) }

-- The actual state writer has exactly this named observed context.
gov-held : ∀ s p → G.Stable (GP.pool (PS.governor s)) p → D.Held s → D.Held (record s { governor = record (PS.governor s) { pool = p } })
gov-held s p stable (inv , unique , aux) = gov-inv (PS.cm s) (C.capture s) p stable inv , unique , gov-aux (C.capture s) p stable aux
bg-held : ∀ s p → B.Stable (PS.monitorPool s) p → D.Held s → D.Held (record s { monitorPool = p })
bg-held s p stable (inv , unique , aux) = bg-inv (PS.cm s) (C.capture s) p stable inv , unique , bg-aux (C.capture s) p stable aux

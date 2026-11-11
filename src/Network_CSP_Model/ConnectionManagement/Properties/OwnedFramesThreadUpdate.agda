{-# OPTIONS --guardedness #-}

-- Monitor lifecycle writes retain immutable worker/peer identities. Active
-- followups additionally require their observing thread and running handle.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesThreadUpdate
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Stores using (UniqueKeys; put-unique; lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesThreads as ThreadFacts
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob)
private module T = ThreadFacts isIOManagerError

-- Named writer for a thread row and its independent monitor-pool state.
thread-context : C.Context → ConnectionManagement.Domain.JobId → PS.Thread → PS.Pool.State → C.Context
thread-context k tid next p = record k { monitors = put tid next (C.monitors k); monitorPool = p }

-- Backward lookup transport retains the two immutable thread names.
thread-back : ∀ (rows : Store ConnectionManagement.Domain.JobId PS.Thread) tid old next → lookup tid rows ≡ just old → PS.worker next ≡ PS.worker old →
  PS.peerRef next ≡ PS.peerRef old → ∀ uid t → lookup uid (put tid next rows) ≡ just t →
  Σ PS.Thread (λ before → lookup uid rows ≡ just before × PS.worker before ≡ PS.worker t × PS.peerRef before ≡ PS.peerRef t)
thread-back rows tid old next saved worker peer uid t found with uid ≟ tid
... | yes refl with just-injective (trans (sym (lookup-put tid next rows)) found)
...   | refl = old , saved , sym worker , sym peer
thread-back rows tid old next saved worker peer uid t found | no apart = t , trans (sym (lookup-put-other tid uid next rows apart)) found , refl , refl

-- Only a followup currently attached to the updated handle needs an explicit
-- observing/running certificate for its replacement.
KeepObserving : C.Context → ConnectionManagement.Domain.JobId → PS.Thread → PS.Pool.State → Set
KeepObserving k tid next p = ∀ ref f → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f →
  (backing : FollowThread ref f k) → FollowThread.tid backing ≡ tid →
  PS.pc next ≡ PS.observing × lookup tid (PS.Pool.handles p) ≡ just PS.Pool.bodyRunning

-- Active followup witnesses select the new row or retain their other row.
update-follow : ∀ k tid old next p → UniqueKeys (C.monitors k) → lookup tid (C.monitors k) ≡ just old →
  PS.worker next ≡ PS.worker old → PS.peerRef next ≡ PS.peerRef old →
  (∀ uid → uid ≢ tid → lookup uid (PS.Pool.handles p) ≡ lookup uid (PS.Pool.handles (C.monitorPool k))) →
  KeepObserving k tid next p → ∀ ref f → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f →
  FollowThread ref f k → FollowThread ref f (thread-context k tid next p)
update-follow k tid old next p unique saved worker peer others keep ref f present backing with FollowThread.tid backing ≟ tid
... | yes refl with just-injective (trans (sym saved)
  (T.byPeer-lookup ref (C.monitors k) unique tid (FollowThread.thread backing) (FollowThread.found backing)))
...   | refl = record
  { tid = tid; thread = next
  ; found = T.byPeer-put-same ref (C.monitors k) tid old next saved peer (FollowThread.found backing)
  ; caller = trans (FollowThread.caller backing) (sym worker)
  ; running = proj₂ (keep ref f present backing refl); observing = proj₁ (keep ref f present backing refl) }
update-follow k tid old next p unique saved worker peer others keep ref f present backing | no apart = record
  { tid = FollowThread.tid backing; thread = FollowThread.thread backing
  ; found = T.byPeer-put-other ref (C.monitors k) tid old next (FollowThread.tid backing)
      (FollowThread.thread backing) saved peer apart (FollowThread.found backing)
  ; caller = FollowThread.caller backing
  ; running = trans (others (FollowThread.tid backing) apart) (FollowThread.running backing)
  ; observing = FollowThread.observing backing }

-- All three owner alternatives survive this explicitly certified thread update.
update-owner : ∀ k tid old next p → UniqueKeys (C.monitors k) → lookup tid (C.monitors k) ≡ just old →
  PS.worker next ≡ PS.worker old → PS.peerRef next ≡ PS.peerRef old →
  (∀ uid → uid ≢ tid → lookup uid (PS.Pool.handles p) ≡ lookup uid (PS.Pool.handles (C.monitorPool k))) →
  KeepObserving k tid next p → ∀ w pc → Owner w pc k → Owner w pc (thread-context k tid next p)
update-owner k tid old next p unique saved worker peer others keep w pc (inj₁ foreign) = inj₁
  (proj₁ foreign , T.byWorker-put-none w (C.monitors k) tid old next saved worker (proj₂ foreign))
update-owner k tid old next p unique saved worker peer others keep w pc (inj₂ (inj₁ owner)) = inj₂ (inj₁
  (job-await (JobAwait.job owner) (JobAwait.frame owner) (JobAwait.found owner)
    (JobAwait.caller owner) (JobAwait.waiting owner) (JobAwait.running owner)))
update-owner k tid old next p unique saved worker peer others keep w pc (inj₂ (inj₂ owner)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref owner) (FollowAwait.frame owner) (FollowAwait.found owner)
    (FollowAwait.caller owner) (FollowAwait.waiting owner) (FollowThread.tid updated) (FollowThread.thread updated)
    (FollowThread.found updated) (trans (sym (FollowThread.caller updated)) (FollowAwait.caller owner))
    (FollowThread.running updated) (FollowThread.observing updated)))
  where
  backing : FollowThread (FollowAwait.ref owner) (FollowAwait.frame owner) k
  backing = record
    { tid = FollowAwait.tid owner; thread = FollowAwait.thread owner; found = FollowAwait.byPeer owner
    ; caller = trans (FollowAwait.caller owner) (sym (FollowAwait.worker owner))
    ; running = FollowAwait.running owner; observing = FollowAwait.observing owner }
  updated = update-follow k tid old next p unique saved worker peer others keep
    (FollowAwait.ref owner) (FollowAwait.frame owner) (FollowAwait.found owner) backing

-- A/R transport follows directly from the exact owner transport above.
update-inv : ∀ c k tid old next p → UniqueKeys (C.monitors k) → lookup tid (C.monitors k) ≡ just old →
  PS.worker next ≡ PS.worker old → PS.peerRef next ≡ PS.peerRef old →
  (∀ uid → uid ≢ tid → lookup uid (PS.Pool.handles p) ≡ lookup uid (PS.Pool.handles (C.monitorPool k))) →
  KeepObserving k tid next p → Inv c k → Inv c (thread-context k tid next p)
update-inv c k tid old next p unique saved worker peer others keep inv = owned-frames
  (λ w present → let owner = acquiring inv w present in proj₁ owner ,
    update-owner k tid old next p unique saved worker peer others keep w _ (proj₂ owner))
  (λ w present → let owner = releasing inv w present in proj₁ owner ,
    update-owner k tid old next p unique saved worker peer others keep w _ (proj₂ owner))

-- Job unwind correspondence is independent of the monitor table/pool.
update-unwind : ∀ k tid next p j f → UnwindJob j f k → UnwindJob j f (thread-context k tid next p)
update-unwind k tid next p j f old = record
  { frame = UnwindJob.frame old; found = UnwindJob.found old; caller = UnwindJob.caller old
  ; phase = UnwindJob.phase old; handle = UnwindJob.handle old; notRunning = UnwindJob.notRunning old }

-- Name injectivity and job/monitor separation survive immutable-name writes.
update-aux : ∀ k tid old next p → lookup tid (C.monitors k) ≡ just old →
  PS.worker next ≡ PS.worker old → PS.peerRef next ≡ PS.peerRef old →
  (∀ uid → uid ≢ tid → lookup uid (PS.Pool.handles p) ≡ lookup uid (PS.Pool.handles (C.monitorPool k))) →
  KeepObserving k tid next p → Aux k → Aux (thread-context k tid next p)
update-aux k tid old next p saved worker peer others keep aux = record
  { jobKeys = Aux.jobKeys aux; monitorKeys = put-unique tid next (C.monitors k) (Aux.monitorKeys aux)
  ; followKeys = Aux.followKeys aux; unwindKeys = Aux.unwindKeys aux; jobCallers = Aux.jobCallers aux
  ; jobNotMonitor = λ j jf found → T.byWorker-put-none (J.caller (Sub.execution jf)) (C.monitors k) tid old next saved worker (Aux.jobNotMonitor aux j jf found)
  ; threadWorkers = workers; threadPeers = peers
  ; followThreads = λ ref f found → update-follow k tid old next p (Aux.monitorKeys aux) saved worker peer others keep ref f found (Aux.followThreads aux ref f found)
  ; unwindingJobs = λ j f found → update-unwind k tid next p j f (Aux.unwindingJobs aux j f found) }
  where
  workers : ∀ uid u vid v → lookup uid (put tid next (C.monitors k)) ≡ just u →
    lookup vid (put tid next (C.monitors k)) ≡ just v → PS.worker u ≡ PS.worker v → uid ≡ vid
  workers uid u vid v found₁ found₂ same with thread-back (C.monitors k) tid old next saved worker peer uid u found₁ |
    thread-back (C.monitors k) tid old next saved worker peer vid v found₂
  ... | u₀ , before₁ , worker₁ , peer₁ | v₀ , before₂ , worker₂ , peer₂ =
    Aux.threadWorkers aux uid u₀ vid v₀ before₁ before₂ (trans worker₁ (trans same (sym worker₂)))
  peers : ∀ uid u vid v → lookup uid (put tid next (C.monitors k)) ≡ just u →
    lookup vid (put tid next (C.monitors k)) ≡ just v → PS.peerRef u ≡ PS.peerRef v → uid ≡ vid
  peers uid u vid v found₁ found₂ same with thread-back (C.monitors k) tid old next saved worker peer uid u found₁ |
    thread-back (C.monitors k) tid old next saved worker peer vid v found₂
  ... | u₀ , before₁ , worker₁ , peer₁ | v₀ , before₂ , worker₂ , peer₂ =
    Aux.threadPeers aux uid u₀ vid v₀ before₁ before₂ (trans peer₁ (trans same (sym peer₂)))

-- A PC-preserving update with unchanged handles keeps active observers alive.
keep-stable : ∀ k tid old next p → UniqueKeys (C.monitors k) → lookup tid (C.monitors k) ≡ just old →
  PS.pc next ≡ PS.pc old → PS.Pool.handles p ≡ PS.Pool.handles (C.monitorPool k) → KeepObserving k tid next p
keep-stable k tid old next p unique saved pc handles ref f present backing refl with
  just-injective (trans (sym saved) (T.byPeer-lookup ref (C.monitors k) unique tid (FollowThread.thread backing) (FollowThread.found backing)))
... | refl = trans pc (FollowThread.observing backing) , trans (cong (lookup tid) handles) (FollowThread.running backing)

-- A non-observing current thread cannot back an active followup at its handle.
keep-stopped : ∀ k tid old next p → UniqueKeys (C.monitors k) → lookup tid (C.monitors k) ≡ just old →
  PS.pc old ≢ PS.observing → KeepObserving k tid next p
keep-stopped k tid old next p unique saved stopped ref f present backing refl with
  just-injective (trans (sym saved) (T.byPeer-lookup ref (C.monitors k) unique tid (FollowThread.thread backing) (FollowThread.found backing)))
... | refl = ⊥-elim (stopped (FollowThread.observing backing))

-- After detach deletes this peer's followup, any observing/running obligation
-- for this handle is impossible, even if the old PC was observing.
keep-detached : ∀ k tid old next p → UniqueKeys (C.monitors k) → lookup tid (C.monitors k) ≡ just old →
  lookup (PS.peerRef old) (C.SubContext.monitors (C.subsystem k)) ≡ nothing → KeepObserving k tid next p
keep-detached k tid old next p unique saved absent ref f present backing refl with
  just-injective (trans (sym saved) (T.byPeer-lookup ref (C.monitors k) unique tid (FollowThread.thread backing) (FollowThread.found backing)))
... | refl = case trans (sym absent) (trans
  (cong (λ q → lookup q (C.SubContext.monitors (C.subsystem k))) (T.byPeer-ref ref (C.monitors k) tid old (FollowThread.found backing))) present) of λ ()

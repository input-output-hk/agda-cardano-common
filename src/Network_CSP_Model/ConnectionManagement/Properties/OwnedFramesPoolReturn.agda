{-# OPTIONS --guardedness #-}

-- Job body return updates the handle only after its continuation is complete.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesPoolReturn
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob)

-- Only the pool metadata is replaced at a physical body-return boundary.
pool-context : C.Context → GP.Pool.State → C.Context
pool-context k p = record k { governorPool = p }

-- A completed row cannot also be a matching await witness for that same job.
return-owner : ∀ k j jf p phase → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  GP.Pool.handles p ≡ put j phase (GP.Pool.handles (C.governorPool k)) →
  ∀ q pc → J.pc (Sub.execution jf) ≢ pc → Owner q pc k → Owner q pc (pool-context k p)
return-owner k j jf p phase found handles q pc different (inj₁ foreign) = inj₁ foreign
return-owner k j jf p phase found handles q pc different (inj₂ (inj₁ old)) with JobAwait.job old ≟ j
... | yes refl = case just-injective (trans (sym found) (JobAwait.found old)) of λ
  { refl → ⊥-elim (different (JobAwait.waiting old)) }
... | no apart = inj₂ (inj₁ (job-await (JobAwait.job old) (JobAwait.frame old) (JobAwait.found old)
  (JobAwait.caller old) (JobAwait.waiting old)
  (trans (cong (lookup (JobAwait.job old)) handles)
    (trans (lookup-put-other j (JobAwait.job old) phase (GP.Pool.handles (C.governorPool k)) apart) (JobAwait.running old)))))
return-owner k j jf p phase found handles q pc different (inj₂ (inj₂ old)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref old) (FollowAwait.frame old) (FollowAwait.found old)
    (FollowAwait.caller old) (FollowAwait.waiting old) (FollowAwait.tid old)
    (FollowAwait.thread old) (FollowAwait.byPeer old) (FollowAwait.worker old)
    (FollowAwait.running old) (FollowAwait.observing old)))

-- Both ownership clauses survive a completed job's pool handle write.
return-inv : ∀ c k j jf p phase result → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf →
  J.pc (Sub.execution jf) ≡ J.complete result →
  GP.Pool.handles p ≡ put j phase (GP.Pool.handles (C.governorPool k)) → Inv c k → Inv c (pool-context k p)
return-inv c k j jf p phase result found complete handles inv = owned-frames
  (λ q present → let old = acquiring inv q present in proj₁ old , return-owner k j jf p phase found handles q J.awaitAcquire
    (λ eq → case trans (sym complete) eq of λ ()) (proj₂ old))
  (λ q present → let old = releasing inv q present in proj₁ old , return-owner k j jf p phase found handles q J.awaitRelease
    (λ eq → case trans (sym complete) eq of λ ()) (proj₂ old))

-- Followup ownership observes the independent monitor pool.
pool-follow : ∀ k p ref f → FollowThread ref f k → FollowThread ref f (pool-context k p)
pool-follow k p ref f old = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old
  ; found = FollowThread.found old; caller = FollowThread.caller old
  ; running = FollowThread.running old; observing = FollowThread.observing old }

-- No detached row can name the handle that was running before body return.
return-aux : ∀ k j p phase → lookup j (GP.Pool.handles (C.governorPool k)) ≡ just GP.Pool.bodyRunning →
  GP.Pool.handles p ≡ put j phase (GP.Pool.handles (C.governorPool k)) → Aux k → Aux (pool-context k p)
return-aux k j p phase running handles old = record
  { jobKeys = Aux.jobKeys old; monitorKeys = Aux.monitorKeys old; followKeys = Aux.followKeys old
  ; unwindKeys = Aux.unwindKeys old; jobCallers = Aux.jobCallers old; jobNotMonitor = Aux.jobNotMonitor old
  ; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = λ ref f found → pool-follow k p ref f (Aux.followThreads old ref f found)
  ; unwindingJobs = unwinds }
  where
  unwinds : ∀ q f → lookup q (C.unwinding k) ≡ just f → UnwindJob q f (pool-context k p)
  unwinds q f found with q ≟ j
  ... | yes refl = ⊥-elim (UnwindJob.notRunning backing (just-injective (trans (sym (UnwindJob.handle backing)) running)))
    where backing = Aux.unwindingJobs old j f found
  ... | no apart = record
    { frame = UnwindJob.frame backing; found = UnwindJob.found backing; caller = UnwindJob.caller backing
    ; phase = UnwindJob.phase backing
    ; handle = trans (cong (lookup q) handles)
      (trans (lookup-put-other j q phase (GP.Pool.handles (C.governorPool k)) apart) (UnwindJob.handle backing))
    ; notRunning = UnwindJob.notRunning backing }
    where backing = Aux.unwindingJobs old q f found

-- The actual bodyReturned writer exposes its old handle and exact update.
returned-fields : ∀ j captured p {p′} → GP.Pool.step (GP.Pool.bodyReturnedWith j captured) p ≡ just p′ →
  lookup j (GP.Pool.handles p) ≡ just GP.Pool.bodyRunning ×
  GP.Pool.handles p′ ≡ put j (GP.Pool.bodyReturned captured) (GP.Pool.handles p)
returned-fields j captured p stepped with lookup j (GP.Pool.handles p) in found
... | just GP.Pool.bodyRunning = case just-injective stepped of λ { refl → refl , refl }
... | nothing = case stepped of λ ()
... | just GP.Pool.bodyUnwinding = case stepped of λ ()
... | just (GP.Pool.bodyReturned _) = case stepped of λ ()
... | just (GP.Pool.deregisterPending _) = case stepped of λ ()
... | just (GP.Pool.deregistered _) = case stepped of λ ()
... | just (GP.Pool.resultAvailable _) = case stepped of λ ()

-- noteReturn is either unchanged pool metadata or an actual completed-body write.
note-return : ∀ c k j a machine {p′} → Sub.jobs machine ≡ C.SubContext.jobs (C.subsystem k) →
  GP.noteReturn (Sub.jobStep j a) machine (C.governorPool k) ≡ just p′ →
  Inv c k → Aux k → Inv c (pool-context k p′) × Aux (pool-context k p′)
note-return c k j a machine same stepped inv aux rewrite same with lookup j (C.SubContext.jobs (C.subsystem k)) in found
... | nothing = case stepped of λ ()
... | just jf with J.pc (Sub.execution jf) in complete
...   | J.complete result with GP.Pool.step
  (GP.Pool.bodyReturnedWith j (GP.body j (J.work (Sub.execution jf)) result)) (C.governorPool k) in returned
...     | nothing = case stepped of λ ()
...     | just p′ = case just-injective stepped of λ { refl →
  return-inv c k j jf p′ (GP.Pool.bodyReturned (GP.body j (J.work (Sub.execution jf)) result)) result found complete (proj₂ facts) inv ,
  return-aux k j p′ (GP.Pool.bodyReturned (GP.body j (J.work (Sub.execution jf)) result)) (proj₁ facts) (proj₂ facts) aux }
  where facts = returned-fields j (GP.body j (J.work (Sub.execution jf)) result) (C.governorPool k) returned
note-return c k j a machine same stepped inv aux | just jf | J.begin = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | J.awaitAcquire = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | (J.startBundle t ns) = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | (J.publishBundle t) = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | J.markWarm = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | J.forkMonitor = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | J.finishActivation = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | J.awaitHot = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | J.awaitAll = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | J.callRelease = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | J.awaitRelease = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | J.delayFailure = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | (J.awaitCold result) = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | (J.acquirePolicy fault) = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | (J.nodeDelivery fault) = case just-injective stepped of λ { refl → inv , aux }
note-return c k j a machine same stepped inv aux | just jf | (J.nodeRethrow fault) = case just-injective stepped of λ { refl → inv , aux }

{-# OPTIONS --guardedness #-}

-- Updating a detached cleanup continuation retains its caller identity.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesUnwindContext
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (put-unique; lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob)

-- Named detached-continuation writer, independent of active callers and pools.
unwind-context : C.Context → ConnectionManagement.Domain.JobId → Cancel.Frame → C.Context
unwind-context k j next = record k { unwinding = put j next (C.unwinding k) }

-- Exact frame owners do not inspect detached cleanup continuations.
unwind-owner : ∀ k j next w pc → Owner w pc k → Owner w pc (unwind-context k j next)
unwind-owner k j next w pc (inj₁ foreign) = inj₁ foreign
unwind-owner k j next w pc (inj₂ (inj₁ old)) = inj₂ (inj₁
  (job-await (JobAwait.job old) (JobAwait.frame old) (JobAwait.found old) (JobAwait.caller old) (JobAwait.waiting old) (JobAwait.running old)))
unwind-owner k j next w pc (inj₂ (inj₂ old)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref old) (FollowAwait.frame old) (FollowAwait.found old) (FollowAwait.caller old) (FollowAwait.waiting old)
    (FollowAwait.tid old) (FollowAwait.thread old) (FollowAwait.byPeer old) (FollowAwait.worker old) (FollowAwait.running old) (FollowAwait.observing old)))

-- A/R therefore retain both their result and exact ownership consequences.
unwind-inv : ∀ c k j next → Inv c k → Inv c (unwind-context k j next)
unwind-inv c k j next inv = owned-frames
  (λ w found → let old = acquiring inv w found in proj₁ old , unwind-owner k j next w _ (proj₂ old))
  (λ w found → let old = releasing inv w found in proj₁ old , unwind-owner k j next w _ (proj₂ old))

-- Active followup attachment also ignores the detached governor table.
unwind-follow : ∀ k j next ref f → FollowThread ref f k → FollowThread ref f (unwind-context k j next)
unwind-follow k j next ref f old = record
  { tid = FollowThread.tid old; thread = FollowThread.thread old; found = FollowThread.found old
  ; caller = FollowThread.caller old; running = FollowThread.running old; observing = FollowThread.observing old }

-- An identity-preserving cleanup update keeps its original job and stopped handle.
unwind-aux : ∀ k j old next → lookup j (C.unwinding k) ≡ just old → Cancel.caller next ≡ Cancel.caller old → Aux k → Aux (unwind-context k j next)
unwind-aux k j old next saved caller aux = record
  { jobKeys = Aux.jobKeys aux; monitorKeys = Aux.monitorKeys aux; followKeys = Aux.followKeys aux
  ; unwindKeys = put-unique j next (C.unwinding k) (Aux.unwindKeys aux)
  ; jobCallers = Aux.jobCallers aux; jobNotMonitor = Aux.jobNotMonitor aux; threadWorkers = Aux.threadWorkers aux; threadPeers = Aux.threadPeers aux
  ; followThreads = λ ref f found → unwind-follow k j next ref f (Aux.followThreads aux ref f found)
  ; unwindingJobs = unwinds }
  where
  unwinds : ∀ uid f → lookup uid (put j next (C.unwinding k)) ≡ just f → UnwindJob uid f (unwind-context k j next)
  unwinds uid f found with uid ≟ j
  ... | yes refl with just-injective (trans (sym (lookup-put j next (C.unwinding k))) found)
  ...   | refl = record
    { frame = UnwindJob.frame backing; found = UnwindJob.found backing; caller = trans caller (UnwindJob.caller backing)
    ; phase = UnwindJob.phase backing; handle = UnwindJob.handle backing; notRunning = UnwindJob.notRunning backing }
    where backing = Aux.unwindingJobs aux j old saved
  unwinds uid f found | no apart = record
    { frame = UnwindJob.frame backing; found = UnwindJob.found backing; caller = UnwindJob.caller backing
    ; phase = UnwindJob.phase backing; handle = UnwindJob.handle backing; notRunning = UnwindJob.notRunning backing }
    where backing = Aux.unwindingJobs aux uid f (trans (sym (lookup-put-other j uid next (C.unwinding k) apart)) found)

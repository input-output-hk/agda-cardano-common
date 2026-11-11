{-# OPTIONS --guardedness #-}

-- Poll may create a logical followup at a previously absent peer key.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesFollowBirth
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (put-unique; lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesFollowStep as FollowFacts
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux; FollowThread; UnwindJob)
private module F = FollowFacts isBearerClosed isIOManagerError

-- No old followup owner can name the previously absent peer key.
born-owner : ∀ k ref next → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ nothing →
  ∀ w pc → Owner w pc k → Owner w pc (F.follow-context k ref next)
born-owner k ref next empty w pc (inj₁ foreign) = inj₁ foreign
born-owner k ref next empty w pc (inj₂ (inj₁ old)) = inj₂ (inj₁
  (job-await (JobAwait.job old) (JobAwait.frame old) (JobAwait.found old) (JobAwait.caller old) (JobAwait.waiting old) (JobAwait.running old)))
born-owner k ref next empty w pc (inj₂ (inj₂ old)) with FollowAwait.ref old ≟ ref
... | yes refl = case trans (sym empty) (FollowAwait.found old) of λ ()
... | no apart = inj₂ (inj₂
  (follow-await (FollowAwait.ref old) (FollowAwait.frame old)
    (trans (lookup-put-other ref (FollowAwait.ref old) next (C.SubContext.monitors (C.subsystem k)) apart) (FollowAwait.found old))
    (FollowAwait.caller old) (FollowAwait.waiting old) (FollowAwait.tid old) (FollowAwait.thread old)
    (FollowAwait.byPeer old) (FollowAwait.worker old) (FollowAwait.running old) (FollowAwait.observing old)))

-- Creation alone changes no source frame or result table.
born-inv : ∀ c k ref next → lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ nothing → Inv c k → Inv c (F.follow-context k ref next)
born-inv c k ref next empty inv = owned-frames
  (λ w found → let old = acquiring inv w found in proj₁ old , born-owner k ref next empty w _ (proj₂ old))
  (λ w found → let old = releasing inv w found in proj₁ old , born-owner k ref next empty w _ (proj₂ old))

-- The real poll caller/physical-thread certificate supplies F for the new row.
born-aux : ∀ k ref next → FollowThread ref next k → Aux k → Aux (F.follow-context k ref next)
born-aux k ref next attached old = record
  { jobKeys = Aux.jobKeys old; monitorKeys = Aux.monitorKeys old
  ; followKeys = put-unique ref next (C.SubContext.monitors (C.subsystem k)) (Aux.followKeys old); unwindKeys = Aux.unwindKeys old
  ; jobCallers = Aux.jobCallers old; jobNotMonitor = Aux.jobNotMonitor old; threadWorkers = Aux.threadWorkers old; threadPeers = Aux.threadPeers old
  ; followThreads = follows
  ; unwindingJobs = λ j f found → F.copy-unwind k ref next j f (Aux.unwindingJobs old j f found) }
  where
  follows : ∀ q f → lookup q (put ref next (C.SubContext.monitors (C.subsystem k))) ≡ just f → FollowThread q f (F.follow-context k ref next)
  follows q f found with q ≟ ref
  ... | yes refl with just-injective (trans (sym (lookup-put ref next (C.SubContext.monitors (C.subsystem k)))) found)
  ...   | refl = F.copy-follow k ref next ref next attached
  follows q f found | no apart = F.copy-follow k ref next q f (Aux.followThreads old q f
    (trans (sym (lookup-put-other ref q next (C.SubContext.monitors (C.subsystem k)) apart)) found))

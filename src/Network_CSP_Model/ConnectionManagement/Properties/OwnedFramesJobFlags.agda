{-# OPTIONS --guardedness #-}

-- Job bookkeeping flags retain execution; establishment adapters change only
-- a non-await continuation while retaining its captured caller.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesJobFlags
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (put-unique; lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesJobNames as Names
import ConnectionManagement.Properties.OwnedFramesJobStep as StepFacts
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux)
private
  module N = Names isBearerClosed isIOManagerError
  module S = StepFacts isBearerClosed isIOManagerError

-- An unchanged execution transports even an await witness at the updated row.
flags-owner : ∀ k j old next → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just old →
  Sub.execution next ≡ Sub.execution old → ∀ w pc → Owner w pc k →
  Owner w pc (N.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
flags-owner k j old next saved execution w pc (inj₁ foreign) = inj₁
  (trans (N.SameJobs.unowned (N.replace-jobs (C.SubContext.jobs (C.subsystem k)) j old next saved (cong J.caller execution)) w) (proj₁ foreign) , proj₂ foreign)
flags-owner k j old next saved execution w pc (inj₂ (inj₁ owner)) with JobAwait.job owner ≟ j
... | yes refl with just-injective (trans (sym saved) (JobAwait.found owner))
...   | refl = inj₂ (inj₁ (job-await j next (lookup-put j next (C.SubContext.jobs (C.subsystem k)))
  (trans (cong J.caller execution) (JobAwait.caller owner)) (trans (cong J.pc execution) (JobAwait.waiting owner)) (JobAwait.running owner)))
flags-owner k j old next saved execution w pc (inj₂ (inj₁ owner)) | no apart = inj₂ (inj₁
  (job-await (JobAwait.job owner) (JobAwait.frame owner)
    (trans (lookup-put-other j (JobAwait.job owner) next (C.SubContext.jobs (C.subsystem k)) apart) (JobAwait.found owner))
    (JobAwait.caller owner) (JobAwait.waiting owner) (JobAwait.running owner)))
flags-owner k j old next saved execution w pc (inj₂ (inj₂ owner)) = inj₂ (inj₂
  (follow-await (FollowAwait.ref owner) (FollowAwait.frame owner) (FollowAwait.found owner)
    (FollowAwait.caller owner) (FollowAwait.waiting owner) (FollowAwait.tid owner) (FollowAwait.thread owner)
    (FollowAwait.byPeer owner) (FollowAwait.worker owner) (FollowAwait.running owner) (FollowAwait.observing owner)))

-- Both ownership clauses retain their exact source-result consequences.
flags-inv : ∀ c k j old next → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just old →
  Sub.execution next ≡ Sub.execution old → Inv c k → Inv c (N.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
flags-inv c k j old next saved execution inv = owned-frames
  (λ w present → let owner = acquiring inv w present in proj₁ owner , flags-owner k j old next saved execution w _ (proj₂ owner))
  (λ w present → let owner = releasing inv w present in proj₁ owner , flags-owner k j old next saved execution w _ (proj₂ owner))

-- Caller-preserving writes maintain all metadata clauses, independent of PC.
caller-aux : ∀ k j old next → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just old →
  J.caller (Sub.execution next) ≡ J.caller (Sub.execution old) → Aux k →
  Aux (N.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
caller-aux k j old next saved caller aux = N.job-aux k _ (put-unique j next _ (Aux.jobKeys aux))
  (N.replace-jobs _ j old next saved caller) aux

-- A known non-await PC excludes an owner for this same job identity.
nonawait-owner : ∀ k j old → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just old →
  ∀ w pc → J.pc (Sub.execution old) ≢ pc → (owner : JobAwait w pc k) → JobAwait.job owner ≢ j
nonawait-owner k j old saved w pc different owner refl with just-injective (trans (sym saved) (JobAwait.found owner))
... | refl = different (JobAwait.waiting owner)

-- Establishment's explicit adapter may therefore replace its continuation PC.
change-inv : ∀ c k j old next → lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just old →
  J.caller (Sub.execution next) ≡ J.caller (Sub.execution old) →
  J.pc (Sub.execution old) ≢ J.awaitAcquire → J.pc (Sub.execution old) ≢ J.awaitRelease →
  Inv c k → Inv c (N.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
change-inv c k j old next saved caller not-acquire not-release inv = owned-frames
  (λ w present → let owner = acquiring inv w present in proj₁ owner ,
    S.replace-owner k j old next saved caller w J.awaitAcquire (nonawait-owner k j old saved w J.awaitAcquire not-acquire) (proj₂ owner))
  (λ w present → let owner = releasing inv w present in proj₁ owner ,
    S.replace-owner k j old next saved caller w J.awaitRelease (nonawait-owner k j old saved w J.awaitRelease not-release) (proj₂ owner))

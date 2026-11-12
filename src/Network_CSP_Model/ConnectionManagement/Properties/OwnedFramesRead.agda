{-# OPTIONS --guardedness #-}

-- Physical failed-result reads replace a continuation outside the two CM
-- await PCs. They keep the caller partition and cannot replace a frame owner.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool; true)
module ConnectionManagement.Properties.OwnedFramesRead
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Maybe using (just; nothing; is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (put-unique)
open import ConnectionManagement.Properties.OutboundKeys using (Unique)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Properties.OwnedFrames as Frames
import ConnectionManagement.Properties.OwnedFramesAux as Auxiliary
import ConnectionManagement.Properties.OwnedFramesJobNames as NamesFacts
import ConnectionManagement.Properties.OwnedFramesJobStep as JobFacts
import ConnectionManagement.Properties.OwnedFramesFollowStep as FollowFacts
import ConnectionManagement.Properties.OwnedFramesContext as ContextFacts
open Frames isBearerClosed isIOManagerError
open Auxiliary isBearerClosed isIOManagerError using (Aux)
private
  module Names = NamesFacts isBearerClosed isIOManagerError
  module Jobs = JobFacts isBearerClosed isIOManagerError
  module Follow = FollowFacts isBearerClosed isIOManagerError
  module V = ContextFacts isBearerClosed isIOManagerError

-- Reach's source and metadata formulation permits transport to a new context.
Held : O.Configuration → C.Context → Set
Held c k = Inv c k × Unique c × Aux k

-- Fields outside the six ownership observations can change independently.
copy-held : ∀ c k target → V.copy-observed k target ≡ target → Held c k → Held c target
copy-held c k target same (inv , unique , aux) = subst (Held c) same
  (V.copy-inv c k target inv , unique , V.copy-aux k target aux)

-- Reading a result is allowed only outside both CM result waits.
NotAwait : J.Frame → Set
NotAwait f = J.pc f ≢ J.awaitAcquire × J.pc f ≢ J.awaitRelease

-- A job replacement outside those waits cannot replace an awaiting owner.
job-read : ∀ c k j jf next →
  lookup j (C.SubContext.jobs (C.subsystem k)) ≡ just jf → NotAwait (Sub.execution jf) →
  J.caller (Sub.execution next) ≡ J.caller (Sub.execution jf) → Held c k →
  Held c (Names.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
job-read c k j jf next found away caller (inv , unique , aux) = owned-frames acq rel , unique ,
  Names.job-aux k _ (put-unique j next _ (Aux.jobKeys aux))
    (Names.replace-jobs _ j jf next found caller) aux
  where
  cannot : ∀ q pc → J.pc (Sub.execution jf) ≢ pc → (owner : JobAwait q pc k) → JobAwait.job owner ≢ j
  cannot q pc apart owner refl with just-injective (trans (sym found) (JobAwait.found owner))
  ... | refl = apart (JobAwait.waiting owner)
  acq : ∀ q → is-just (lookup q (O.acquiring c)) ≡ true →
    lookup q (O.acquired c) ≡ nothing × Owner q J.awaitAcquire (Names.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
  acq q present = proj₁ old , Jobs.replace-owner k j jf next found caller q J.awaitAcquire
    (cannot q J.awaitAcquire (proj₁ away)) (proj₂ old)
    where old = acquiring inv q present
  rel : ∀ q → is-just (lookup q (O.releasing c)) ≡ true →
    lookup q (O.released c) ≡ nothing × Owner q J.awaitRelease (Names.job-context k (put j next (C.SubContext.jobs (C.subsystem k))))
  rel q present = proj₁ old , Jobs.replace-owner k j jf next found caller q J.awaitRelease
    (cannot q J.awaitRelease (proj₂ away)) (proj₂ old)
    where old = releasing inv q present

-- Followup replacements have the same exclusion and keep their observing thread.
follow-read : ∀ c k ref f next →
  lookup ref (C.SubContext.monitors (C.subsystem k)) ≡ just f → NotAwait f →
  J.caller next ≡ J.caller f → Held c k → Held c (Follow.follow-context k ref next)
follow-read c k ref f next found away caller (inv , unique , aux) =
  owned-frames acq rel , unique , Follow.follow-aux k ref f next found caller aux
  where
  cannot : ∀ q pc → J.pc f ≢ pc → (owner : FollowAwait q pc k) → FollowAwait.ref owner ≢ ref
  cannot q pc apart owner refl with just-injective (trans (sym found) (FollowAwait.found owner))
  ... | refl = apart (FollowAwait.waiting owner)
  acq : ∀ q → is-just (lookup q (O.acquiring c)) ≡ true →
    lookup q (O.acquired c) ≡ nothing × Owner q J.awaitAcquire (Follow.follow-context k ref next)
  acq q present = proj₁ old , Follow.replace-owner k ref next q J.awaitAcquire
    (cannot q J.awaitAcquire (proj₁ away)) (proj₂ old)
    where old = acquiring inv q present
  rel : ∀ q → is-just (lookup q (O.releasing c)) ≡ true →
    lookup q (O.released c) ≡ nothing × Owner q J.awaitRelease (Follow.follow-context k ref next)
  rel q present = proj₁ old , Follow.replace-owner k ref next q J.awaitRelease
    (cannot q J.awaitRelease (proj₂ away)) (proj₂ old)
    where old = releasing inv q present

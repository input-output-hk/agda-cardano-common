{-# OPTIONS --guardedness #-}

-- Local non-advancement facts for the ownership witnesses. Matching the
-- followup's await PC to the frame kind makes the required result premise exact.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesAwait
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (proj₁)
open import Data.Empty using (⊥)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Properties.AwaitStuck as Stuck
import ConnectionManagement.Properties.OwnedFrames as Frames
open Frames isBearerClosed isIOManagerError

-- Equality of the caller and PC reduces an arbitrary frame to AwaitStuck.
acquire-stuck : ∀ a f c peers w → J.caller f ≡ w → J.pc f ≡ J.awaitAcquire →
  lookup w (O.acquired c) ≡ nothing → J.step a f (J.world c peers) ≡ nothing
acquire-stuck a (J.frame work caller child sock ref pc) c peers w refl refl none =
  Stuck.acquire-stuck a work caller child sock ref (J.world c peers) none

-- The release case reads the other result table.
release-stuck : ∀ a f c peers w → J.caller f ≡ w → J.pc f ≡ J.awaitRelease →
  lookup w (O.released c) ≡ nothing → J.step a f (J.world c peers) ≡ nothing
release-stuck a (J.frame work caller child sock ref pc) c peers w refl refl none =
  Stuck.release-stuck a work caller child sock ref (J.world c peers) none

-- A witnessed job owning an acquisition cannot advance its await frame.
job-acquire-stuck : ∀ s → Owned s → ∀ w f →
  lookup w (O.acquiring (K.source s)) ≡ just f →
  (j : JobAwait w J.awaitAcquire (K.context s)) → ∀ a peers →
  J.step a (Sub.execution (JobAwait.frame j)) (J.world (K.source s) peers) ≡ nothing
job-acquire-stuck s inv w f found j a peers = acquire-stuck a _ (K.source s) peers w
  (JobAwait.caller j) (JobAwait.waiting j) (proj₁ (acquire-owner s inv w f found))

-- The release ownership witness is equally frozen until its result arrives.
job-release-stuck : ∀ s → Owned s → ∀ w f →
  lookup w (O.releasing (K.source s)) ≡ just f →
  (j : JobAwait w J.awaitRelease (K.context s)) → ∀ a peers →
  J.step a (Sub.execution (JobAwait.frame j)) (J.world (K.source s) peers) ≡ nothing
job-release-stuck s inv w f found j a peers = release-stuck a _ (K.source s) peers w
  (JobAwait.caller j) (JobAwait.waiting j) (proj₁ (release-owner s inv w f found))

-- A followup has the same result dependency as a governor-owned job.
follow-acquire-stuck : ∀ s → Owned s → ∀ w f →
  lookup w (O.acquiring (K.source s)) ≡ just f →
  (follow : FollowAwait w J.awaitAcquire (K.context s)) → ∀ a peers →
  J.step a (FollowAwait.frame follow) (J.world (K.source s) peers) ≡ nothing
follow-acquire-stuck s inv w f found follow a peers = acquire-stuck a _ (K.source s) peers w
  (FollowAwait.caller follow) (FollowAwait.waiting follow) (proj₁ (acquire-owner s inv w f found))

-- A releasing followup cannot leave awaitRelease before the CM return.
follow-release-stuck : ∀ s → Owned s → ∀ w f →
  lookup w (O.releasing (K.source s)) ≡ just f →
  (follow : FollowAwait w J.awaitRelease (K.context s)) → ∀ a peers →
  J.step a (FollowAwait.frame follow) (J.world (K.source s) peers) ≡ nothing
follow-release-stuck s inv w f found follow a peers = release-stuck a _ (K.source s) peers w
  (FollowAwait.caller follow) (FollowAwait.waiting follow) (proj₁ (release-owner s inv w f found))

-- A fresh pool identity cannot overwrite the row of any JobAwait witness.
fork-distinct : ∀ next k w pc → lookup next (GP.Pool.handles (C.governorPool k)) ≡ nothing →
  (j : JobAwait w pc k) → JobAwait.job j ≢ next
fork-distinct next k w pc fresh j refl = case trans (sym fresh) (JobAwait.running j) of λ ()

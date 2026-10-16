{-# OPTIONS --guardedness #-}

-- Instantiate both reverse-order publications and exclude repeated success.
module ConnectionManagement.Negative.RegistryPublication where

open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Empty using (⊥)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Rules.OriginRegistry
import ConnectionManagement.Rules.OriginMonitor as Single
open import ConnectionManagement.Properties.RegistryPublication
import ConnectionManagement.Properties.OriginRegistry as Registry
import ConnectionManagement.Properties.RegistryUnique as Unique
open import ConnectionManagement.CSP.RegistryPublication
import ConnectionManagement.CSP.RegistryAdmission as A
open import ConnectionManagement.Scenarios.Admission using (child₀; child₁)
import ConnectionManagement.Negative.RegistryUnique

-- These are the same selection/fork-derived premises used by the full witness.
allocation-supported : Registry.Supported A.allocation-prefix
allocation-supported = Registry.next tt (Registry.next tt (Registry.next tt (Registry.next tt (Registry.next tt (Registry.next A.first-resources (Registry.next tt (Registry.next tt (Registry.next tt (Registry.next tt (Registry.next tt (Registry.next tt (Registry.next tt (Registry.next tt (Registry.next tt (Registry.next A.second-resources (Registry.done))))))))))))))))

second-sound : Sound child₁ (ident 1) duplex A.s16 A.s17
second-sound = reachable-publication child₁ (ident 1) duplex A.allocation-prefix allocation-supported refl

-- The second publication retains resources/origins and identity uniqueness for
-- the first handler's subsequent publication.
first-sound : Sound child₀ (ident 0) duplex A.s17 A.s18
first-sound = publication-sound child₀ (ident 0) duplex A.s17 refl
  (Registry.invariant-step A.publication₂ A.s16 refl tt (Registry.reachable A.allocation-prefix allocation-supported))
  (Unique.step-unique A.publication₂ A.s16 refl (Unique.reachable-unique A.allocation-prefix))

-- Once both entries are published, neither can serve as a pending success entry.
no-pending : ∀ e tk → e ∈ entries A.s18 → phase e ≡ Single.awaitingPublication tk → ⊥
no-pending e tk (here refl) ()
no-pending e tk (there (here refl)) ()
no-pending e tk (there (there ())) pending
no-republication-certificate : ∀ w hid f {s′} → ¬ Sound w hid f A.s18 s′
no-republication-certificate w hid f sound =
  no-pending (Sound.selected sound) (Sound.ticket sound) (Sound.present sound) (Sound.pending sound)

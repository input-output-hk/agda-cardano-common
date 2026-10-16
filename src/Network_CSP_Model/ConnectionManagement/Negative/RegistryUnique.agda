{-# OPTIONS --guardedness #-}

-- Duplicate identities are unreachable even when the other identity differs.
module ConnectionManagement.Negative.RegistryUnique where

open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using ([]; _∷_)
open import Data.List.Relation.Unary.AllPairs using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.OriginMonitor using (target; awaitingAllocation)
open import ConnectionManagement.Properties.RegistryUnique
open import ConnectionManagement.CSP.RegistryUnique
import ConnectionManagement.CSP.RegistryAdmission as Admission
import ConnectionManagement.Negative.OriginRegistry as Synthetic
import ConnectionManagement.Negative.RegistryAdmission

admission-unique : Unique (entries Admission.s18)
admission-unique = reachable-unique Admission.path
synthetic-unique : Unique (entries Synthetic.s₄)
synthetic-unique = reachable-unique Synthetic.path

-- The two fields are individually unique, not merely their ordered pairs.
no-duplicate-worker : ∀ w hid hid′ p p′ → ¬ Unique
  (entry (target w hid) p ∷ entry (target w hid′) p′ ∷ [])
no-duplicate-worker w hid hid′ p p′ (((apart , _) ∷ _) ∷ _) = apart refl
no-duplicate-handle : ∀ w w′ hid p p′ → ¬ Unique
  (entry (target w hid) p ∷ entry (target w′ hid) p′ ∷ [])
no-duplicate-handle w w′ hid p p′ (((_ , apart) ∷ _) ∷ _) = apart refl

-- Arbitrary pre-seeded registries need not satisfy uniqueness. Neither forged
-- endpoint can be reached from ANY empty-registry initial machine configuration.
worker-forgery handle-forgery : State
worker-forgery = registry (machine Admission.s18)
  (entry (target (ident 2) (ident 0)) awaitingAllocation ∷
   entry (target (ident 2) (ident 1)) awaitingAllocation ∷ [])
handle-forgery = registry (machine Admission.s18)
  (entry (target (ident 2) (ident 0)) awaitingAllocation ∷
   entry (target (ident 3) (ident 0)) awaitingAllocation ∷ [])
worker-forgery-unreachable : ∀ {c as} → ¬ Executes (start c) as worker-forgery
worker-forgery-unreachable path = no-duplicate-worker (ident 2) (ident 0) (ident 1) awaitingAllocation awaitingAllocation (reachable-unique path)
handle-forgery-unreachable : ∀ {c as} → ¬ Executes (start c) as handle-forgery
handle-forgery-unreachable path = no-duplicate-handle (ident 2) (ident 3) (ident 0) awaitingAllocation awaitingAllocation (reachable-unique path)

{-# OPTIONS --guardedness #-}

-- Retention alone permits a second owner; the uniqueness invariant excludes it.
module ConnectionManagement.Negative.HandlerUniqueOwnership where

open import Data.Bool using (false)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Fixtures using (start)
open import ConnectionManagement.Scenarios.Admission using (child₀; child₁)
open import ConnectionManagement.Properties.HandlerCapture using (Retains; fresh-retains)
open import ConnectionManagement.Properties.HandlerUniqueOwnership using (Unique)
open import ConnectionManagement.Properties.HandlerUniqueOwnershipInvariant using (exec-preserves)
import ConnectionManagement.Properties.HandlerValidity as V
import ConnectionManagement.Rules.HandlerLifecycle as L

ownedFrame : L.Frame
ownedFrame = L.frame (ident 0) (errorId 7) L.monitoring
single shared duplicateKey : Configuration
single = record start { handlerLifecycles = (child₀ , ownedFrame) ∷ [] }
shared = record start { handlerLifecycles = (child₀ , ownedFrame) ∷ (child₁ , ownedFrame) ∷ [] }
duplicateKey = record start { handlerLifecycles = (child₀ , ownedFrame) ∷ (child₀ , ownedFrame) ∷ [] }
single-unique : Unique (handlerLifecycles single)
single-unique = refl
sharing-retains-old-capture : Retains (handlerLifecycles single) (handlerLifecycles shared)
sharing-retains-old-capture = fresh-retains child₁ ownedFrame (handlerLifecycles single) refl
shared-owner-rejected : V.uniqueOwners (handlerLifecycles shared) ≡ false
shared-owner-rejected = refl
duplicate-key-rejected : V.uniqueOwners (handlerLifecycles duplicateKey) ≡ false
duplicate-key-rejected = refl
shared-not-unique : ¬ Unique (handlerLifecycles shared)
shared-not-unique ()
duplicate-not-unique : ¬ Unique (handlerLifecycles duplicateKey)
duplicate-not-unique ()
no-sharing-execution : ∀ {as} → ¬ Executes single as shared
no-sharing-execution path = shared-not-unique (exec-preserves single-unique path)
no-duplicate-execution : ∀ {as} → ¬ Executes single as duplicateKey
no-duplicate-execution path = duplicate-not-unique (exec-preserves single-unique path)

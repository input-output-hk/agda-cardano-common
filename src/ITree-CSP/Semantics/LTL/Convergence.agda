{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; Σ-syntax; _,_)
open import Data.Sum using (_⊎_)
open import Data.Empty using (⊥; ⊥-elim)

open import Process_Trees

module Semantics.LTL.Convergence
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open PTree

open import Semantics.LTS      {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.DRBisim  {ℓ} {ℓe} {ℓi} {E} {I} using (DRbisim)
open import Semantics.Deadlock {ℓ} {ℓe} {ℓi} {E} {I} using (IsStuck)

data Converges {ℓr} {R : Set ℓr} : PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  cvg : ∀ {t} → (∀ {t′} → t ─[ τ ]─► t′ → Converges t′) → Converges t

stuck⇒Converges : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} → IsStuck t → Converges t
stuck⇒Converges stuck = cvg (λ tτ → ⊥-elim (stuck tτ))

τ-progress : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
τ-progress t = (Σ[ t′ ∈ _ ] (t ─[ τ ]─► t′)) ⊎ (∀ {t′} → t ─[ τ ]─► t′ → ⊥)

data _↠_ {ℓr} {R : Set ℓr} : PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  ↠-refl : ∀ {t} → t ↠ t
  ↠-τ    : ∀ {t t′ t″}   → t ─[ τ ]─► t′      → t′ ↠ t″ → t ↠ t″
  ↠-ev   : ∀ {t t′ t″ l} → t ─[ ev l ]─► t′   → t′ ↠ t″ → t ↠ t″

↠-trans : ∀ {ℓr} {R : Set ℓr} {t t′ t″ : PTree E I R} → t ↠ t′ → t′ ↠ t″ → t ↠ t″
↠-trans ↠-refl        q = q
↠-trans (↠-τ  s rest) q = ↠-τ  s (↠-trans rest q)
↠-trans (↠-ev s rest) q = ↠-ev s (↠-trans rest q)

record Realisable {ℓr} (R : Set ℓr) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  field
    τprog : ∀ (s : PTree E I R) → τ-progress s
    conv  : ∀ {s u : PTree E I R} → DRbisim R u s → IsStuck u → Converges s

open Realisable public

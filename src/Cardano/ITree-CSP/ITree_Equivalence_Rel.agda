{-# OPTIONS --guardedness #-}
-- {-# OPTIONS --cubical-compatible --no-import-sorts #-}

-- open import Agda.Buildin.Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)
open import Relation.Unary
open import Function using (case_of_)

open import Data.Maybe.Relation.Binary.Pointwise using (Pointwise)
open import Relation.Binary                       using (Rel)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Interaction_Trees

module ITree_Equivalence_Rel where

-- One step of bisimulation, parameterized by:
--   RetRel  : how to relate values at (ret _) nodes
--   TreeRel : how to relate subtrees at recursive positions
--             (will be tied coinductively to produce the fixpoint)
data NodeKindF {ℓ ℓe ℓi ℓr ℓ≡ ℓ≈ : Level}
               {E : Set ℓ → Set ℓe}
               {I : Set ℓ → Set ℓi}
               {R : Set ℓr}
               (RetRel  : Rel R ℓ≡)
               (TreeRel : Rel (ITree E I R) ℓ≈)
             : Rel (NodeKind E I R) (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓ≈ ⊔ ℓr) where

  retF : ∀ {r₁ r₂}
       → RetRel r₁ r₂
       → NodeKindF RetRel TreeRel (ret r₁) (ret r₂)

  silF : ∀ {t₁ t₂}
       → TreeRel t₁ t₂
       → NodeKindF RetRel TreeRel (sil t₁) (sil t₂)

  -- Pointwise TreeRel replaces the manual MaybeITree≈ entirely
  visF : ∀ {f₁ f₂}
       → (∀ (at : AnyTypes E) (a : proj₁ at)
          → Pointwise TreeRel (f₁ at a) (f₂ at a))
       → NodeKindF RetRel TreeRel (vis f₁) (vis f₂)

  invF : ∀ {f₁ f₂}
       → (∀ (i : AnyTypes I) (a : proj₁ i)
          → Pointwise TreeRel (f₁ i a) (f₂ i a))
       → NodeKindF RetRel TreeRel (inv f₁) (inv f₂)

-- Bisim RetRel is the greatest fixpoint of (NodeKindF RetRel)
-- i.e., ν X. NodeKindF RetRel X
record Bisim {ℓ ℓe ℓi ℓr ℓ≡ : Level}
             {E : Set ℓ → Set ℓe}
             {I : Set ℓ → Set ℓi}
             {R : Set ℓr}
             (RetRel : Rel R ℓ≡)
             (t₁ t₂ : ITree E I R)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓr) where
  coinductive
  field
    step : NodeKindF RetRel (Bisim RetRel) (ITree.force t₁) (ITree.force t₂)

-- Standard strong bisimulation: propositional equality on return values
_≈_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → Rel (ITree E I R) _
_≈_ = Bisim _≡_

-- Ignore return values entirely (e.g., for divergence checking)
_≈⊤_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → Rel (ITree E I R) _
_≈⊤_ {ℓr = ℓr}  = Bisim (λ _ _ → ⊤ {lzero})

-- Return values related by some custom _~_
_≈[_]_ : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ITree E I R → Rel R ℓ≡ → ITree E I R → Set _
t₁ ≈[ _~_ ] t₂ = Bisim _~_ t₁ t₂

-- Closed under a setoid on R
open import Relation.Binary using (Setoid)

bisimSetoid : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} 
  → (S : Setoid ℓr ℓ≡) → Rel (ITree E I (Setoid.Carrier S)) _
bisimSetoid S = Bisim (Setoid._≈_ S)

import Data.Maybe.Relation.Binary.Pointwise as MPW
open import Relation.Binary using (IsEquivalence)

module BisimEquiv
  {ℓ ℓe ℓi ℓr ℓ≡ : Level}
  {E : Set ℓ → Set ℓe}
  {I : Set ℓ → Set ℓi}
  {R : Set ℓr}
  {RetRel : Rel R ℓ≡}
  (retEq : IsEquivalence RetRel) where

  open IsEquivalence retEq renaming (refl to ret-refl; sym to ret-sym; trans to ret-trans)

  bisim-refl : ∀ (t : ITree E I R) → Bisim RetRel t t
  bisim-refl t .Bisim.step
    with ITree.force t
  ... | ret r  = retF ret-refl
  ... | sil t' = silF (bisim-refl t')
  ... | vis f  = visF (λ at a → go (f at a))
    where
      go : ∀ m → Pointwise (Bisim RetRel) m m
      go (just t') = MPW.just (bisim-refl t')
      go nothing   = MPW.nothing
  ... | inv f  = invF (λ i a → go (f i a))
    where
      go : ∀ m → Pointwise (Bisim RetRel) m m
      go (just t') = MPW.just (bisim-refl t')
      go nothing   = MPW.nothing

  {-# NON_TERMINATING #-}
  bisim-sym : ∀ {t₁ t₂ : ITree E I R} → Bisim RetRel t₁ t₂ → Bisim RetRel t₂ t₁
  bisim-sym {t₁} {t₂} p .Bisim.step
    with ITree.force t₁ | ITree.force t₂ | p .Bisim.step
  ... | ret _  | ret _  | retF r    = retF (ret-sym r)
  ... | sil _  | sil _  | silF q    = silF (bisim-sym q)
  ... | vis _  | vis _  | visF h    = visF (λ at a → MPW.sym bisim-sym (h at a))
  ... | inv _  | inv _  | invF h    = invF (λ i  a → MPW.sym bisim-sym (h i  a))

  {-# NON_TERMINATING #-}
  bisim-trans : ∀ {t₁ t₂ t₃ : ITree E I R}
              → Bisim RetRel t₁ t₂ → Bisim RetRel t₂ t₃ → Bisim RetRel t₁ t₃
  bisim-trans {t₁} {t₂} {t₃} p q .Bisim.step
    with ITree.force t₁ | ITree.force t₂ | ITree.force t₃
       | p .Bisim.step  | q .Bisim.step
  ... | ret _  | ret _  | ret _  | retF r₁  | retF r₂  = retF (ret-trans r₁ r₂)
  ... | sil _  | sil _  | sil _  | silF p'  | silF q'  = silF (bisim-trans p' q')
  ... | vis _  | vis _  | vis _  | visF hp  | visF hq  =
        visF (λ at a → MPW.trans bisim-trans (hp at a) (hq at a))
  ... | inv _  | inv _  | inv _  | invF hp  | invF hq  =
        invF (λ i  a → MPW.trans bisim-trans (hp i  a) (hq i  a))

  -- Package as a Setoid
  Bisim-isEquivalence : IsEquivalence (Bisim RetRel)
  Bisim-isEquivalence = record
    { refl  = bisim-refl _
    ; sym   = bisim-sym
    ; trans = bisim-trans
    }

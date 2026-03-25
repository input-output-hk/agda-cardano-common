{-
  This module defines strong bisimulation between ITrees where
    - invisible choice's indices are discarded and only their children (ITrees) matter;
    - internal tau is not omitted in transition relations.    
-}

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
-- open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Unary
open import Function using (case_of_)

open import Data.Maybe.Relation.Binary.Pointwise using (Pointwise)
  renaming (just to pw-just; nothing to pw-nothing; sym to pw-sym; trans to pw-trans)
open import Relation.Binary                       using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans; refl)

open import Interaction_Trees
open import ITree_Relations.LTS using (Label; ev; τ; _─[_]─►_; sSil;
  _─[τ^_]─►_; τ^-zero; τ^-suc)
open import ITree_Relations.Divergence

module ITree_Relations.StrongBisim where

-- One step of bisimulation, parameterized by:
--   RetRel  : how to relate values at (ret _) nodes
--   TreeRel : how to relate subtrees at recursive positions
--             (will be tied coinductively to produce the fixpoint)
data SNodeKindF {ℓ ℓe ℓi ℓr ℓ≡ ℓ≈ : Level}
               {E : Set ℓ → Set ℓe}
               {I : Set ℓ → Set ℓi}
               {R : Set ℓr}
               (RetRel  : Rel R ℓ≡)
               (TreeRel : Rel (ITree E I R) ℓ≈)
             : Rel (NodeKind E I R) (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓ≈ ⊔ ℓr) where

  retF : ∀ {r₁ r₂}
       → RetRel r₁ r₂
       → SNodeKindF RetRel TreeRel (ret r₁) (ret r₂)

  silF : ∀ {t₁ t₂}
       → TreeRel t₁ t₂
       → SNodeKindF RetRel TreeRel (sil t₁) (sil t₂)

  visF : ∀ {f₁ f₂}
       → (∀ (at : AnyTypes E) (a : proj₁ at)
          → Pointwise TreeRel (f₁ at a) (f₂ at a))
       → SNodeKindF RetRel TreeRel (vis f₁) (vis f₂)

  -- check the equivalence in the codomain only
  invF : ∀ {f₁ f₂}
       → (∀ {t₁} → Image f₁ t₁
          → Σ[ t₂ ∈ ITree E I R ] (Image f₂ t₂ × TreeRel t₁ t₂))
       → (∀ {t₂} → Image f₂ t₂
          → Σ[ t₁ ∈ ITree E I R ] (Image f₁ t₁ × TreeRel t₁ t₂))
       → SNodeKindF RetRel TreeRel (inv f₁) (inv f₂)

-- Sbisim RetRel is the greatest fixpoint of (SNodeKindF RetRel)
-- i.e., ν X. SNodeKindF RetRel X
record Sbisim {ℓ ℓe ℓi ℓr ℓ≡ : Level}
             {E : Set ℓ → Set ℓe}
             {I : Set ℓ → Set ℓi}
             {R : Set ℓr}
             (RetRel : Rel R ℓ≡)
             (t₁ t₂ : ITree E I R)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓr) where
  coinductive
  field
    step : SNodeKindF RetRel (Sbisim RetRel) (ITree.force t₁) (ITree.force t₂)

-- Standard strong bisimulation: propositional equality on return values
_≈_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → Rel (ITree E I R) _
_≈_ = Sbisim _≡_

-- open SNodeKindF
open Sbisim
open Divergent

div-≈ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      {P Q : ITree E I R}
      → Divergent P
      → Divergent Q
      → P ≈ Q
div-≈ dp dq .step with dp .step | dq .step
... | sSil eqP | sSil eqQ
  rewrite eqP | eqQ = silF (div-≈ (dp .diverge) (dq .diverge))

-- Ignore return values entirely (e.g., for divergence checking)
_≈⊤_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → Rel (ITree E I R) _
_≈⊤_ {ℓr = ℓr}  = Sbisim (λ _ _ → ⊤ {lzero})

-- Return values related by some custom _~_
_≈[_]_ : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ITree E I R → Rel R ℓ≡ → ITree E I R → Set _
t₁ ≈[ _~_ ] t₂ = Sbisim _~_ t₁ t₂

-- Closed under a setoid on R
open import Relation.Binary using (Setoid)

sbisimSetoid : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} 
  → (S : Setoid ℓr ℓ≡) → Rel (ITree E I (Setoid.Carrier S)) _
sbisimSetoid S = Sbisim (Setoid._≈_ S)

module SbisimEquiv
  {ℓ ℓe ℓi ℓr ℓ≡ : Level}
  {E : Set ℓ → Set ℓe}
  {I : Set ℓ → Set ℓi}
  {R : Set ℓr}
  {RetRel : Rel R ℓ≡}
  (retEq : IsEquivalence RetRel) where

  {- This is equivalent to 
  ret-refl  : RetRel r r
  ret-sym   : RetRel r₁ r₂ → RetRel r₂ r₁
  ret-trans : RetRel r₁ r₂ → RetRel r₂ r₃ → RetRel r₁ r₃
  -}
  open IsEquivalence retEq renaming (refl to ret-refl; sym to ret-sym; trans to ret-trans)

  sbisim-refl : ∀ (t : ITree E I R) → Sbisim RetRel t t
  sbisim-refl t .Sbisim.step
    with ITree.force t
  ... | ret r  = retF ret-refl
  ... | sil t' = silF (sbisim-refl t')
  ... | vis f  = visF (λ at a → go (f at a))
    where
      go : ∀ m → Pointwise (Sbisim RetRel) m m
      go (just t') = pw-just (sbisim-refl t')
      go nothing   = pw-nothing
      
  ... | inv f  = invF
        (λ {t′} (i , a , eq) → t′ , (i , a , eq) , sbisim-refl t′)
        (λ {t′} (i , a , eq) → t′ , (i , a , eq) , sbisim-refl t′)

  {-# NON_TERMINATING #-}
  sbisim-sym : ∀ {t₁ t₂ : ITree E I R} → Sbisim RetRel t₁ t₂ → Sbisim RetRel t₂ t₁
  sbisim-sym {t₁} {t₂} p .Sbisim.step
    with ITree.force t₁ | ITree.force t₂ | p .Sbisim.step
  ... | ret _  | ret _  | retF r    = retF (ret-sym r)
  ... | sil _  | sil _  | silF q    = silF (sbisim-sym q)
  ... | vis _  | vis _  | visF h    = visF (λ at a → pw-sym sbisim-sym (h at a))
  ... | inv _ | inv _ | invF h-fwd h-bwd = invF
        (λ {t₁} img →
          let (t₂ , img₂ , rel) = h-bwd img
          in  t₂ , img₂ , sbisim-sym rel)
        (λ {t₂} img →
          let (t₁ , img₁ , rel) = h-fwd img
          in  t₁ , img₁ , sbisim-sym rel)

  {-# NON_TERMINATING #-}
  sbisim-trans : ∀ {t₁ t₂ t₃ : ITree E I R}
              → Sbisim RetRel t₁ t₂ → Sbisim RetRel t₂ t₃ → Sbisim RetRel t₁ t₃
  sbisim-trans {t₁} {t₂} {t₃} p q .Sbisim.step
    with ITree.force t₁ | ITree.force t₂ | ITree.force t₃
       | p .Sbisim.step  | q .Sbisim.step
  ... | ret _  | ret _  | ret _  | retF r₁  | retF r₂  = retF (ret-trans r₁ r₂)
  ... | sil _  | sil _  | sil _  | silF p'  | silF q'  = silF (sbisim-trans p' q')
  ... | vis _  | vis _  | vis _  | visF hp  | visF hq  = visF
        (λ at a → pw-trans sbisim-trans (hp at a) (hq at a))
  ... | inv _  | inv _  | inv _  | invF hp-fwd hp-bwd  | invF hq-fwd hq-bwd = invF
        (λ {t₁} img →
          let (t₂ , img₂ , rel₁) = hp-fwd img
              (t₃ , img₃ , rel₂) = hq-fwd img₂
          in  t₃ , img₃ , sbisim-trans rel₁ rel₂)
        (λ {t₃} img →
          let (t₂ , img₂ , rel₂) = hq-bwd img
              (t₁ , img₁ , rel₁) = hp-bwd img₂
          in  t₁ , img₁ , sbisim-trans rel₁ rel₂)


  -- Package as a Setoid
  Sbisim-isEquivalence : IsEquivalence (Sbisim RetRel)
  Sbisim-isEquivalence = record
    { refl  = sbisim-refl _
    ; sym   = sbisim-sym
    ; trans = sbisim-trans
    }

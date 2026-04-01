{-
This module defines a parametrised (by a relation RetRel for R) structural coinductive pointwise
equivalence for two ITrees.

In particular, even for `inv fP` and `inv fQ`, `fP` is expected to be equal to `fQ` by `RetRel`.
This is different from bisimulation where `fP` and `fQ` are not expected to be equal if they
have the same ranges or codomain. That is, they can have different indices, but their continuous
sub-trees are the same, representing nondeterministic choice of a same set of trees.

-}


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
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans; refl)

open import Interaction_Trees

module ITree_Relations.Equivalence_Rel where

-- One step of bisimulation, parameterized by:
--   RetRel  : how to relate values at (ret _) nodes
--   TreeRel : how to relate subtrees at recursive positions
--             (will be tied coinductively to produce the fixpoint)
data EqNodeKindF {ℓ ℓe ℓi ℓr ℓ≡ ℓ≈ : Level}
               {E : Set ℓ → Set ℓe}
               {I : Set ℓ → Set ℓi}
               {R : Set ℓr}
               (RetRel  : Rel R ℓ≡)
               (TreeRel : Rel (ITree E I R) ℓ≈)
             : Rel (NodeKind E I R) (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓ≈ ⊔ ℓr) where

  retF : ∀ {r₁ r₂}
       → RetRel r₁ r₂
       → EqNodeKindF RetRel TreeRel (ret r₁) (ret r₂)

  silF : ∀ {t₁ t₂}
       → TreeRel t₁ t₂
       → EqNodeKindF RetRel TreeRel (sil t₁) (sil t₂)

  visF : ∀ {f₁ f₂}
       → (∀ (at : AnyTypes E) (a : proj₁ at)
       → Pointwise TreeRel (f₁ at a) (f₂ at a))
       → EqNodeKindF RetRel TreeRel (vis f₁) (vis f₂)

  -- The evidence is also match. Does it too strong?
  -- For structual equivalence here, it exactly means that
  invF : ∀ {f₁ f₂ i₁ i₂ a₁ a₂ p₁ p₂}
       → (eq-idx : i₁ ≡ i₂) -- The indices are the same
       → (subst (λ i → proj₁ i) eq-idx a₁ ≡ a₂) -- Now a₁ and a₂ can be compared
       → (∀ (i : AnyTypes I) (val : proj₁ i)
          → Pointwise TreeRel (f₁ i val) (f₂ i val))
       → EqNodeKindF RetRel TreeRel (inv f₁ i₁ a₁ p₁) (inv f₂ i₂ a₂ p₂)

{-
  -- Use this weak version if the previous one is too strong
  invF : ∀ {f₁ f₂ i₁ i₂ a₁ a₂ p₁ p₂}
       → (∀ (i : AnyTypes I) (val : proj₁ i)
          → Pointwise TreeRel (f₁ i val) (f₂ i val))
       → EqNodeKindF RetRel TreeRel (inv f₁ i₁ a₁ p₁) (inv f₂ i₂ a₂ p₂)       
-}

{-
  invF : ∀ {f₁ f₂}
       → (∀ (i : AnyTypes I) (a : proj₁ i)
       → Pointwise TreeRel (f₁ i a) (f₂ i a))
       → EqNodeKindF RetRel TreeRel (inv f₁) (inv f₂)
-}       

-- Bisim RetRel is the greatest fixpoint of (EqNodeKindF RetRel)
-- i.e., ν X. EqNodeKindF RetRel X
record SEquiv {ℓ ℓe ℓi ℓr ℓ≡ : Level}
             {E : Set ℓ → Set ℓe}
             {I : Set ℓ → Set ℓi}
             {R : Set ℓr}
             (RetRel : Rel R ℓ≡)
             (t₁ t₂ : ITree E I R)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓr) where
  coinductive
  field
    step : EqNodeKindF RetRel (SEquiv RetRel) (ITree.force t₁) (ITree.force t₂)

-- Standard strong bisimulation: propositional equality on return values
_≈_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → Rel (ITree E I R) _
_≈_ = SEquiv _≡_

-- Ignore return values entirely (e.g., for divergence checking)
_≈⊤_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → Rel (ITree E I R) _
_≈⊤_ {ℓr = ℓr}  = SEquiv (λ _ _ → ⊤ {lzero})

-- Return values related by some custom _~_
_≈[_]_ : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ITree E I R → Rel R ℓ≡ → ITree E I R → Set _
t₁ ≈[ _~_ ] t₂ = SEquiv _~_ t₁ t₂

-- Closed under a setoid on R
open import Relation.Binary using (Setoid)

sequivSetoid : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} 
  → (S : Setoid ℓr ℓ≡) → Rel (ITree E I (Setoid.Carrier S)) _
sequivSetoid S = SEquiv (Setoid._≈_ S)

import Data.Maybe.Relation.Binary.Pointwise as MPW
open import Relation.Binary using (IsEquivalence)

module SEquivEquiv
  {ℓ ℓe ℓi ℓr ℓ≡ : Level}
  {E : Set ℓ → Set ℓe}
  {I : Set ℓ → Set ℓi}
  {R : Set ℓr}
  {RetRel : Rel R ℓ≡}
  (retEq : IsEquivalence RetRel) where

  open IsEquivalence retEq renaming (refl to ret-refl; sym to ret-sym; trans to ret-trans)

  sequiv-refl : ∀ (t : ITree E I R) → SEquiv RetRel t t
  sequiv-refl t .SEquiv.step
    with ITree.force t
  ... | ret r  = retF ret-refl
  ... | sil t' = silF (sequiv-refl t')
  ... | vis f  = visF (λ at a → go (f at a))
    where
      go : ∀ m → Pointwise (SEquiv RetRel) m m
      go (just t') = MPW.just (sequiv-refl t')
      go nothing   = MPW.nothing
--  ... | inv f i a p = invF (λ i a → go (f i a))
  ... | inv f i a p = invF refl refl (λ i' a' → go (f i' a'))
    where
      go : ∀ m → Pointwise (SEquiv RetRel) m m
      go (just t') = MPW.just (sequiv-refl t')
      go nothing   = MPW.nothing

  {-# NON_TERMINATING #-}
  sequiv-sym : ∀ {t₁ t₂ : ITree E I R} → SEquiv RetRel t₁ t₂ → SEquiv RetRel t₂ t₁
  sequiv-sym {t₁} {t₂} p .SEquiv.step
    with ITree.force t₁ | ITree.force t₂ | p .SEquiv.step
  ... | ret _  | ret _  | retF r    = retF (ret-sym r)
  ... | sil _  | sil _  | silF q    = silF (sequiv-sym q)
  ... | vis _  | vis _  | visF h    = visF (λ at a → MPW.sym sequiv-sym (h at a))
  ... | inv _ _ _ _  | inv _ _ _ _ | invF eq-idx eq-val h = invF
      (sym eq-idx) (sym-val eq-idx eq-val) (λ i  a → MPW.sym sequiv-sym (h i  a))
    where
      -- Helper to handle the symmetry of the witness value when the index changes
      sym-val : ∀ {i₁ i₂} {a₁ : proj₁ i₁} {a₂ : proj₁ i₂}
              → (e : i₁ ≡ i₂) 
              → subst (λ i → proj₁ i) e a₁ ≡ a₂ 
              → subst (λ i → proj₁ i) (sym e) a₂ ≡ a₁
      sym-val refl refl = refl
    

  {-# NON_TERMINATING #-}
  sequiv-trans : ∀ {t₁ t₂ t₃ : ITree E I R}
              → SEquiv RetRel t₁ t₂ → SEquiv RetRel t₂ t₃ → SEquiv RetRel t₁ t₃
  sequiv-trans {t₁} {t₂} {t₃} p q .SEquiv.step
    with ITree.force t₁ | ITree.force t₂ | ITree.force t₃
       | p .SEquiv.step  | q .SEquiv.step
  ... | ret _  | ret _  | ret _  | retF r₁  | retF r₂  = retF (ret-trans r₁ r₂)
  ... | sil _  | sil _  | sil _  | silF p'  | silF q'  = silF (sequiv-trans p' q')
  ... | vis _  | vis _  | vis _  | visF hp  | visF hq  =
        visF (λ at a → MPW.trans sequiv-trans (hp at a) (hq at a))
  ... | inv _ _ _ _ | inv _ _ _ _  | inv _ _ _ _  | invF eq-idx-p eq-val-p hp  | invF eq-idx-q eq-val-q hq  =
        invF (trans eq-idx-p eq-idx-q) 
           (trans-val eq-idx-p eq-idx-q eq-val-p eq-val-q)
           (λ i  a → MPW.trans sequiv-trans (hp i  a) (hq i  a))
      where
        -- Helper to handle transitivity of the dependent witness values
        trans-val : ∀ {i₁ i₂ i₃} {a₁ : proj₁ i₁} {a₂ : proj₁ i₂} {a₃ : proj₁ i₃}
                  → (e1 : i₁ ≡ i₂) (e2 : i₂ ≡ i₃)
                  → subst (λ i → proj₁ i) e1 a₁ ≡ a₂ 
                  → subst (λ i → proj₁ i) e2 a₂ ≡ a₃
                  → subst (λ i → proj₁ i) (trans e1 e2) a₁ ≡ a₃
        trans-val refl refl refl refl = refl           

  -- Package as a Setoid
  SEquiv-isEquivalence : IsEquivalence (SEquiv RetRel)
  SEquiv-isEquivalence = record
    { refl  = sequiv-refl _
    ; sym   = sequiv-sym
    ; trans = sequiv-trans
    }

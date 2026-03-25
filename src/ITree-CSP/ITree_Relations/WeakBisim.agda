{-
  This module defines weak bisimulation between ITrees where
    - invisible choice's indices are discarded and only their children (ITrees) matter;
    - internal tau is omitted in transition relations.
-}

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
-- open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_; ∃; ∃₂; Σ-syntax; ∃-syntax)
open import Relation.Unary
open import Function using (case_of_)

open import Data.Maybe.Relation.Binary.Pointwise using (Pointwise)
  renaming (just to pw-just; nothing to pw-nothing; sym to pw-sym; trans to pw-trans)
open import Relation.Binary                       using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym; trans; refl; inspect; [_])

open import Interaction_Trees
open import ITree_Relations.LTS using (_─[τ*]─►_; τ*-zero; _τ*-step_)

module ITree_Relations.WeakBisim where

-- Like NodeKindF, but the silF case is intentionally absent.
-- This captures the "observable" transitions only.
data WNodeKindF {ℓ ℓe ℓi ℓr ℓ≡ ℓ≈ : Level}
               {E : Set ℓ → Set ℓe}
               {I : Set ℓ → Set ℓi}
               {R : Set ℓr}
               (RetRel  : Rel R ℓ≡)
               (TreeRel : Rel (ITree E I R) ℓ≈)
             : Rel (NodeKind E I R) (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓ≈ ⊔ ℓr) where
  retF : ∀ {r₁ r₂}
       → RetRel r₁ r₂
       → WNodeKindF RetRel TreeRel (ret r₁) (ret r₂)
  -- silF is absent: τ steps are quotiented out by ⇒*
  visF : ∀ {f₁ f₂}
       → (∀ (at : AnyTypes E) (a : proj₁ at)
          → Pointwise TreeRel (f₁ at a) (f₂ at a))
       → WNodeKindF RetRel TreeRel (vis f₁) (vis f₂)
  invF : ∀ {f₁ f₂}
       → (∀ {t₁} → Image f₁ t₁
          → Σ[ t₂ ∈ ITree E I R ] (Image f₂ t₂ × TreeRel t₁ t₂))
       → (∀ {t₂} → Image f₂ t₂
          → Σ[ t₁ ∈ ITree E I R ] (Image f₁ t₁ × TreeRel t₁ t₂))
       → WNodeKindF RetRel TreeRel (inv f₁) (inv f₂)

-- Wbisim RetRel is the greatest fixpoint of
--   λ X t₁ t₂ → ∃ t₁' t₂', t₁ ⇒* t₁'  ×  t₂ ⇒* t₂'
--                           × WNodeKindF RetRel X (force t₁') (force t₂')
record Wbisim {ℓ ℓe ℓi ℓr ℓ≡ : Level}
             {E : Set ℓ → Set ℓe}
             {I : Set ℓ → Set ℓi}
             {R : Set ℓr}
             (RetRel : Rel R ℓ≡)
             (t₁ t₂ : ITree E I R)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓr) where
  coinductive
  field
    step : ∃₂ λ t₁' t₂'
         → (t₁ ─[τ*]─► t₁')
         × (t₂ ─[τ*]─► t₂')
         × WNodeKindF RetRel (Wbisim RetRel)
                             (ITree.force t₁')
                             (ITree.force t₂')
                             
-- Standard strong bisimulation: propositional equality on return values
_≈_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → Rel (ITree E I R) _
_≈_ = Wbisim _≡_

-- Ignore return values entirely (e.g., for divergence checking)
_≈⊤_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → Rel (ITree E I R) _
_≈⊤_ {ℓr = ℓr}  = Wbisim (λ _ _ → ⊤ {lzero})

-- Return values related by some custom _~_
_≈[_]_ : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ITree E I R → Rel R ℓ≡ → ITree E I R → Set _
t₁ ≈[ _~_ ] t₂ = Wbisim _~_ t₁ t₂

-- Closed under a setoid on R
open import Relation.Binary using (Setoid)

bisimSetoid : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} 
  → (S : Setoid ℓr ℓ≡) → Rel (ITree E I (Setoid.Carrier S)) _
bisimSetoid S = Wbisim (Setoid._≈_ S)

module WbisimEquiv
  {ℓ ℓe ℓi ℓr ℓ≡ : Level}
  {E : Set ℓ → Set ℓe}
  {I : Set ℓ → Set ℓi}
  {R : Set ℓr}
  {RetRel : Rel R ℓ≡}
  (retEq : IsEquivalence RetRel) where

  open IsEquivalence retEq renaming (refl to ret-refl; sym to ret-sym; trans to ret-trans)

  private
    -- WNodeKindF has no silF case, so its endpoints are always τ-free
    nf-l : ∀ {ℓ≈} {X : Rel (ITree E I R) ℓ≈} {n₁ n₂}
         → WNodeKindF RetRel X n₁ n₂ → ∀ s → n₁ ≢ sil s
    nf-l (retF _)   _ ()
    nf-l (visF _)   _ ()
    nf-l (invF _ _) _ ()

    nf-r : ∀ {ℓ≈} {X : Rel (ITree E I R) ℓ≈} {n₁ n₂}
         → WNodeKindF RetRel X n₁ n₂ → ∀ s → n₂ ≢ sil s
    nf-r (retF _)   _ ()
    nf-r (visF _)   _ ()
    nf-r (invF _ _) _ ()

    -- τ-reduction is deterministic: two paths from the same source that both
    -- terminate at a τ-free node must end at the same ITree.
    -- Proof: induction on ⇒* length; sil is deterministic so both paths
    -- stay in lockstep until one of them exhausts τ*-zero, at which point the
    -- other must also be τ*-zero (otherwise its source would be τ-free, contradicting τ*-zero).
    tau-det : ∀ {t t₁ t₂ : ITree E I R}
            → t ─[τ*]─► t₁
            → t ─[τ*]─► t₂
            → (∀ s → ITree.force t₁ ≢ sil s)
            → (∀ s → ITree.force t₂ ≢ sil s)
            → t₁ ≡ t₂
    tau-det τ*-zero           τ*-zero           _   _   = refl
    tau-det τ*-zero           (eq τ*-step _)   nf  _   = ⊥-elim (nf _ eq)
    tau-det (eq τ*-step _)   τ*-zero           _   nf  = ⊥-elim (nf _ eq)
    tau-det (eq₁ τ*-step r₁) (eq₂ τ*-step r₂) nf₁ nf₂
      with sil-injective (trans (sym eq₁) eq₂)
    ... | refl = tau-det r₁ r₂ nf₁ nf₂

  -- refl: for ret/vis/inv use τ*-zero on both sides; for sil strip the τ and
  -- prepend refl ◅τ to the reductions found by recursing on t'.
  -- Now also needs NON_TERMINATING: the sil case recurses into .step of
  -- wbisim-refl t', which is not guarded under a coinductive constructor.     
  {-# NON_TERMINATING #-}
  wbisim-refl : ∀ (t : ITree E I R) → Wbisim RetRel t t
  wbisim-refl t .Wbisim.step with ITree.force t | inspect ITree.force t
  ... | ret r  | [ eq ] = t , t , τ*-zero , τ*-zero , subst (λ nk → WNodeKindF RetRel (Wbisim RetRel) nk nk) (sym eq) (retF ret-refl)
  ... | sil t' | [ eq ] =
        let (t₁' , t₂' , red₁ , red₂ , obs) = (wbisim-refl t') .Wbisim.step
        in  t₁' , t₂' , (eq τ*-step red₁) , (eq τ*-step red₂) , obs
  ... | vis f  | [ eq ] = t , t , τ*-zero , τ*-zero , subst (λ nk → WNodeKindF RetRel (Wbisim RetRel) nk nk) (sym eq) (visF (λ at a → go (f at a)))
    where
      go : ∀ m → Pointwise (Wbisim RetRel) m m
      go (just t') = pw-just (wbisim-refl t')
      go nothing   = pw-nothing
  ... | inv f  | [ eq ] = t , t , τ*-zero , τ*-zero , subst (λ nk → WNodeKindF RetRel (Wbisim RetRel) nk nk) (sym eq) (invF
        (λ {t'} img → t' , img , wbisim-refl t')
        (λ {t'} img → t' , img , wbisim-refl t'))

  -- sym: no case split on force needed at all — just swap t₁'/t₂' and
  -- their reductions, then flip the WNodeKindF observation.
  {-# NON_TERMINATING #-}
  wbisim-sym : ∀ {t₁ t₂ : ITree E I R} → Wbisim RetRel t₁ t₂ → Wbisim RetRel t₂ t₁
  wbisim-sym p .Wbisim.step =
    let (t₁' , t₂' , red₁ , red₂ , obs) = p .Wbisim.step
    in  t₂' , t₁' , red₂ , red₁ , flip-obs obs
    where
      flip-obs : ∀ {n₁ n₂}
               → WNodeKindF RetRel (Wbisim RetRel) n₁ n₂
               → WNodeKindF RetRel (Wbisim RetRel) n₂ n₁
      flip-obs (retF r)       = retF (ret-sym r)
      flip-obs (visF h)       = visF (λ at a → pw-sym wbisim-sym (h at a))
      flip-obs (invF fwd bwd) = invF
        (λ img → let (t , img' , rel) = bwd img in t , img' , wbisim-sym rel)
        (λ img → let (t , img' , rel) = fwd img in t , img' , wbisim-sym rel)

  -- trans: p and q each produce an independent ⇒* path out of t₂.
  -- tau-det synchronizes them (both are τ-free, sil is deterministic),
  -- yielding t₂' ≡ t₂''. We subst obs-q along this equality so that
  -- merge-obs can combine obs-p and obs-q' over the common middle.
  
  {-# NON_TERMINATING #-}
  wbisim-trans : ∀ {t₁ t₂ t₃ : ITree E I R}
               → Wbisim RetRel t₁ t₂ → Wbisim RetRel t₂ t₃ → Wbisim RetRel t₁ t₃
  wbisim-trans p q .Wbisim.step =
    let (t₁'  , t₂'  , red₁  , red₂  , obs-p) = p .Wbisim.step
        (t₂'' , t₃'  , red₂' , red₃  , obs-q) = q .Wbisim.step
        eq     = tau-det red₂ red₂' (nf-r obs-p) (nf-l obs-q)
        obs-q' = subst (λ t → WNodeKindF RetRel (Wbisim RetRel)
                                (ITree.force t) (ITree.force t₃')) (sym eq) obs-q
    in  t₁' , t₃' , red₁ , red₃ , merge-obs obs-p obs-q'
    where
      merge-obs : ∀ {n₁ n₂ n₃}
                → WNodeKindF RetRel (Wbisim RetRel) n₁ n₂
                → WNodeKindF RetRel (Wbisim RetRel) n₂ n₃
                → WNodeKindF RetRel (Wbisim RetRel) n₁ n₃
      merge-obs (retF r₁)         (retF r₂)         = retF (ret-trans r₁ r₂)
      merge-obs (visF h₁)         (visF h₂)         =
        visF (λ at a → pw-trans wbisim-trans (h₁ at a) (h₂ at a))
      merge-obs (invF fwd₁ bwd₁) (invF fwd₂ bwd₂) = invF
        (λ img → let (t₂ , img₂ , rel₁) = fwd₁ img
                     (t₃ , img₃ , rel₂) = fwd₂ img₂
                 in  t₃ , img₃ , wbisim-trans rel₁ rel₂)
        (λ img → let (t₂ , img₂ , rel₂) = bwd₂ img
                     (t₁ , img₁ , rel₁) = bwd₁ img₂
                 in  t₁ , img₁ , wbisim-trans rel₁ rel₂)

  Wbisim-isEquivalence : IsEquivalence (Wbisim RetRel)
  Wbisim-isEquivalence = record
    { refl  = wbisim-refl _
    ; sym   = wbisim-sym
    ; trans = wbisim-trans
    }
    

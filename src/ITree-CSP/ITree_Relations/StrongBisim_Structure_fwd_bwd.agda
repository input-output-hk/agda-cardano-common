{-
  This module defines strong bisimulation between ITrees where
    - invisible choice's indices are discarded and only their children (ITrees) matter;
    - internal tau is not omitted in transition relations.    
-}

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing; Is-just) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Unary
open import Function using (case_of_; _↔_)
open import Data.Sum using (_⊎_; inj₁; inj₂)

open import Data.Maybe.Relation.Binary.Pointwise using (Pointwise)
  renaming (just to pw-just; nothing to pw-nothing; sym to pw-sym; trans to pw-trans)
open import Relation.Binary                       using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym; trans; refl)
open import Data.List using (List; _++_; _∷_; []; length; reverse; map; foldr; downFrom)
open import Function.Bundles using (_⇔_; mk⇔)

open import Prelude
open import Interaction_Trees
open import ITree_Relations.LTS {-using (EvLabel; Label; ev; τ; _─[_]─►_; sSil; sInv; sVis; τ-inv; 
                                      _─[τ^_]─►_; τ^-zero; τ^-suc;
                                      _═⟨_⟩═►_; bNil; bTau; bStep;
                                      ) -}
open import ITree_Relations.Divergence

module ITree_Relations.StrongBisim where
open Traces

-----------------------------------------------------------------------------------------
-- One-sided simulation: every structural obligation of t₁ is matched by t₂
-- All fields are FUNCTION-typed, so corecursive calls inside them are guarded by λ.

record SSimF {ℓ ℓe ℓi ℓr ℓ≡ ℓ≈ : Level}
             {E : Set ℓ → Set ℓe}
             {I : Set ℓ → Set ℓi}
             {R : Set ℓr}
             (RetRel  : Rel R ℓ≡)
             (TreeRel : Rel (ITree E I R) ℓ≈)
             (t₁ t₂   : ITree E I R)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓ≈ ⊔ ℓr) where
  field
    -- ret case: t₁ is a return, t₂ must be a related return
    on-ret  : ∀ {r}
            → ITree.force t₁ ≡ ret r
            → Σ[ r' ∈ _ ]
              ( ITree.force t₂ ≡ ret r'
              × RetRel r r' )

    -- sil case: t₁ is silent, t₂ must be silent with a related continuation
    on-sil  : ∀ {t₁'}
            → ITree.force t₁ ≡ sil t₁'
            → Σ[ t₂' ∈ ITree E I R ]
              ( ITree.force t₂ ≡ sil t₂'
              × TreeRel t₁' t₂' )

    -- vis case: t₁ is visible, t₂ must be visible with pointwise-related branches
    on-vis  : ∀ {f₁}
            → ITree.force t₁ ≡ vis f₁
            → Σ[ f₂ ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))) ]
              ( ITree.force t₂ ≡ vis f₂
              × (∀ (at : AnyTypes E) (a : proj₁ at)
                 → Pointwise TreeRel (f₁ at a) (f₂ at a)) )

    -- ndbr case: t₁ is a nondeterministic branch,
    -- t₂ must be an ndbr whose IMAGE is forward-covered by t₂'s image
    -- (backward coverage comes from Sbisim.bwd)
    on-ndbr : ∀ {f₁ : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
                {i₁ : AnyTypes I} {a₁ : proj₁ i₁} {p₁ : Is-just (f₁ i₁ a₁)}
            → ITree.force t₁ ≡ ndbr f₁ i₁ a₁ p₁
            → Σ[ f₂ ∈ ((i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))) ]
              Σ[ i₂ ∈ AnyTypes I ] Σ[ a₂ ∈ proj₁ i₂ ] Σ[ p₂ ∈ Is-just (f₂ i₂ a₂) ]
              ( ITree.force t₂ ≡ ndbr f₂ i₂ a₂ p₂
              × (∀ {t} → Image f₁ t
                 → Σ[ t' ∈ ITree E I R ] (Image f₂ t' × TreeRel t t')) )

-----------------------------------------------------------------------------------------
-- Sbisim: greatest fixpoint, now with explicit fwd/bwd like DRWbisim
-- This makes sym trivial (just swap fields) — NO termination issues.

record Sbisim {ℓ ℓe ℓi ℓr ℓ≡ : Level}
              {E : Set ℓ → Set ℓe}
              {I : Set ℓ → Set ℓi}
              {R : Set ℓr}
              (RetRel : Rel R ℓ≡)
              (t₁ t₂  : ITree E I R)
            : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓr) where
  coinductive
  field
    fwd : SSimF RetRel (Sbisim RetRel) t₁ t₂
    bwd : SSimF RetRel (Sbisim RetRel) t₂ t₁

{-    
-----------------------------------------------------------------------------------------
-- Define strong bisimulation

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

  -- Check the equivalence in the codomain only
  -- The dependent witness is also ignored. So it is a weaker than Structural Equivalence in this aspect too.
  ndbrF : ∀ {f₁ f₂ i₁ i₂ a₁ a₂ p₁ p₂}
       → (∀ {t₁} → Image f₁ t₁
          → Σ[ t₂ ∈ ITree E I R ] (Image f₂ t₂ × TreeRel t₁ t₂))
       → (∀ {t₂} → Image f₂ t₂
          → Σ[ t₁ ∈ ITree E I R ] (Image f₁ t₁ × TreeRel t₁ t₂))
       → SNodeKindF RetRel TreeRel (ndbr f₁ i₁ a₁ p₁) (ndbr f₂ i₂ a₂ p₂)

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
-}

-----------------------------------------------------------------------------------------
-- Some simple Sbisim with special RetRel

-- Standard strong bisimulation: propositional equality on return values
_≈_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → Rel (ITree E I R) _
_≈_ = Sbisim _≡_

-- Ignore return values entirely (e.g., for divergence checking)
_≈⊤_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → Rel (ITree E I R) _
_≈⊤_ {ℓr = ℓr}  = Sbisim (λ _ _ → ⊤ {lzero})

-- Return values related by some custom _~_
_≈[_]_ : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ITree E I R → Rel R ℓ≡ → ITree E I R → Set _
t₁ ≈[ _~_ ] t₂ = Sbisim _~_ t₁ t₂

-----------------------------------------------------------------------------------------
--
open import Relation.Binary using (Setoid)

{-
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
  sbisim-refl t .Sbisim.fwd = fwdF
    where
    fwdF : SSimF RetRel (Sbisim RetRel) t t

    fwdF .SSimF.on-ret eq =
      let refl = eq in _ , (refl , ret-refl)

    fwdF .SSimF.on-sil eq =
      let refl = eq in _ , (refl , sbisim-refl _)

    fwdF .SSimF.on-vis eq =
      let refl = eq in _ , (refl , λ at a → go (f at a))
      where
        f = {!!} -- extracted from eq
        go : ∀ m → Pointwise (Sbisim RetRel) m m
        go (just t') = pw-just (sbisim-refl t')
        go nothing   = pw-nothing

    fwdF .SSimF.on-ndbr eq =
      let refl = eq in _ , _ , _ , _ ,
        (refl , λ img → _ , (img , sbisim-refl _))

  sbisim-refl t .Sbisim.bwd = sbisim-refl t .Sbisim.fwd


  sbisim-sym : ∀ {t₁ t₂} → Sbisim RetRel t₁ t₂ → Sbisim RetRel t₂ t₁
  sbisim-sym p .Sbisim.fwd = p .Sbisim.bwd
  sbisim-sym p .Sbisim.bwd = p .Sbisim.fwd

  sbisim-trans
    : ∀ {t₁ t₂ t₃}
    → Sbisim RetRel t₁ t₂
    → Sbisim RetRel t₂ t₃
    → Sbisim RetRel t₁ t₃

  transF
    : ∀ {t₁ t₂ t₃}
    → SSimF RetRel (Sbisim RetRel) t₁ t₂
    → SSimF RetRel (Sbisim RetRel) t₂ t₃
    → SSimF RetRel (Sbisim RetRel) t₁ t₃
  transF f g .SSimF.on-ret eq1 =
    let (r2 , (eq2 , rel1)) = f .SSimF.on-ret eq1
        (r3 , (eq3 , rel2)) = g .SSimF.on-ret eq2
    in  r3 , (eq3 , ret-trans rel1 rel2)

  transF f g .SSimF.on-sil eq1 =
    let (t₂ , (eq2 , rel1)) = f .SSimF.on-sil eq1
        (t₃ , (eq3 , rel2)) = g .SSimF.on-sil eq2
    in  t₃ , (eq3 , sbisim-trans rel1 rel2)

  transF f g .SSimF.on-vis eq1 =
    let (f2 , (eq2 , h1)) = f .SSimF.on-vis eq1
        (f3 , (eq3 , h2)) = g .SSimF.on-vis eq2
    in
    f3 , (eq3 , λ at a →
      pw-trans sbisim-trans (h1 at a) (h2 at a))

  transF f g .SSimF.on-ndbr eq1 =
    let (f2 , i2 , a2 , p2 , (eq2 , h1)) = f .SSimF.on-ndbr eq1
        (f3 , i3 , a3 , p3 , (eq3 , h2)) = g .SSimF.on-ndbr eq2
    in
    f3 , i3 , a3 , p3 ,
      ( eq3
      , λ img →
          let (t₂ , (img2 , rel1)) = h1 img
              (t₃ , (img3 , rel2)) = h2 img2
          in  t₃ , (img3 , sbisim-trans rel1 rel2)
      )

{-  sbisim-trans
    : ∀ {t₁ t₂ t₃}
    → Sbisim RetRel t₁ t₂
    → Sbisim RetRel t₂ t₃
    → Sbisim RetRel t₁ t₃
-}
  sbisim-trans p q .Sbisim.fwd =
    transF (p .Sbisim.fwd) (q .Sbisim.fwd)

  sbisim-trans p q .Sbisim.bwd =
    transF (q .Sbisim.bwd) (p .Sbisim.bwd)

  -- Package as a Setoid
  Sbisim-isEquivalence : IsEquivalence (Sbisim RetRel)
  Sbisim-isEquivalence = record
    { refl  = sbisim-refl _
    ; sym   = sbisim-sym
    ; trans = sbisim-trans
    }
-}

module SbisimEquiv
  {l le li lr l≡ : Level}
  {E : Set l → Set le}
  {I : Set l → Set li}
  {R : Set lr}
  {RetRel : Rel R l≡}
  (retEq : IsEquivalence RetRel) where

  open IsEquivalence retEq renaming (refl to ret-refl; sym to ret-sym; trans to ret-trans)

  -----------------------------------------------------------------------------------------
  -- Reflexivity

  ssim-refl   : ∀ (t : ITree E I R) → SSimF RetRel (Sbisim RetRel) t t
  sbisim-refl : ∀ (t : ITree E I R) → Sbisim RetRel t t

  sbisim-refl t .Sbisim.fwd = ssim-refl t
  sbisim-refl t .Sbisim.bwd = ssim-refl t

  ssim-refl t .SSimF.on-ret eq =
      _ , eq , ret-refl

  ssim-refl t .SSimF.on-sil eq =
      _ , eq , sbisim-refl _                          -- guarded: under λ of on-sil ✓

  ssim-refl t .SSimF.on-vis {f₁ = f} eq =
      f , eq , λ at a → go (f at a)
    where
      go : ∀ (m : Maybe (ITree E I R)) → Pointwise (Sbisim RetRel) m m
      go (just t') = pw-just (sbisim-refl t')   -- guarded: under λ of on-vis ✓
      go nothing   = pw-nothing
{-      
  ssim-refl t .SSimF.on-vis eq =
      _ , eq , λ at a → go at a eq
    where
      go : ∀ at a → ITree.force t ≡ vis _
         → Pointwise (Sbisim RetRel) _ _
      go at a refl with ITree.force t
      ... | vis f with f at a
      ... | just t' = pw-just (sbisim-refl t')        -- guarded: under λ of on-vis ✓
      ... | nothing  = pw-nothing
-}
  ssim-refl t .SSimF.on-ndbr eq =
      _ , _ , _ , _ , eq
      , λ img → _ , img , sbisim-refl _               -- guarded: under λ of on-ndbr ✓

  -----------------------------------------------------------------------------------------
  -- Symmetry: swap fwd/bwd — zero corecursive calls, trivially guarded ✓

  sbisim-sym : ∀ {t₁ t₂ : ITree E I R} → Sbisim RetRel t₁ t₂ → Sbisim RetRel t₂ t₁
  sbisim-sym p .Sbisim.fwd = p .Sbisim.bwd
  sbisim-sym p .Sbisim.bwd = p .Sbisim.fwd

  -----------------------------------------------------------------------------------------
  -- Transitivity

  sbisim-trans : ∀ {t₁ t₂ t₃ : ITree E I R}
               → Sbisim RetRel t₁ t₂
               → Sbisim RetRel t₂ t₃
               → Sbisim RetRel t₁ t₃
  ssim-trans   : ∀ {t₁ t₂ t₃ : ITree E I R}
               → SSimF RetRel (Sbisim RetRel) t₁ t₂
               → Sbisim RetRel t₂ t₃
               → SSimF RetRel (Sbisim RetRel) t₁ t₃

  on-ret-trans  : ∀ {t₁ t₂ t₃ : ITree E I R} {r}
                → ITree.force t₁ ≡ ret r
                → SSimF RetRel (Sbisim RetRel) t₁ t₂
                → Sbisim RetRel t₂ t₃
                → Σ[ r' ∈ R ] (ITree.force t₃ ≡ ret r' × RetRel r r')
  on-ret-trans eq s12 b23
      with s12 .SSimF.on-ret eq
  ... | r'  , eq2 , rel12
      with b23 .Sbisim.fwd .SSimF.on-ret eq2
  ... | r'' , eq3 , rel23
      = r'' , eq3 , ret-trans rel12 rel23

  on-sil-trans  : ∀ {t₁ t₂ t₃ t₁' : ITree E I R}
                → ITree.force t₁ ≡ sil t₁'
                → SSimF RetRel (Sbisim RetRel) t₁ t₂
                → Sbisim RetRel t₂ t₃
                → Σ[ t₃' ∈ ITree E I R ]
                  ( ITree.force t₃ ≡ sil t₃'
                  × Sbisim RetRel t₁' t₃' )
  on-sil-trans eq s12 b23
      with s12 .SSimF.on-sil eq
  ... | t₂' , eq2 , rel12
      with b23 .Sbisim.fwd .SSimF.on-sil eq2
  ... | t₃' , eq3 , rel23
      = t₃' , eq3 , sbisim-trans rel12 rel23        -- with is in helper, not in ssim-trans ✓

  on-vis-trans  : ∀ {t₁ t₂ t₃ : ITree E I R}
                  {f1 : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
                → ITree.force t₁ ≡ vis f1
                → SSimF RetRel (Sbisim RetRel) t₁ t₂
                → Sbisim RetRel t₂ t₃
                → Σ[ f3 ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))) ]
                  ( ITree.force t₃ ≡ vis f3
                  × (∀ at a → Pointwise (Sbisim RetRel) (f1 at a) (f3 at a)) )
  on-vis-trans eq s12 b23
      with s12 .SSimF.on-vis eq
  ... | f2 , eq2 , h12
      with b23 .Sbisim.fwd .SSimF.on-vis eq2
  ... | f3 , eq3 , h23
      = f3 , eq3
      , λ at a → pw-trans sbisim-trans (h12 at a) (h23 at a)   -- under λ at a ✓

  on-ndbr-trans : ∀ {t₁ t₂ t₃ : ITree E I R}
                  {f1 : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
                  {i1 : AnyTypes I} {a1 : proj₁ i1} {p1 : Is-just (f1 i1 a1)}
                → ITree.force t₁ ≡ ndbr f1 i1 a1 p1
                → SSimF RetRel (Sbisim RetRel) t₁ t₂
                → Sbisim RetRel t₂ t₃
                → Σ[ f3 ∈ ((i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))) ]
                  Σ[ i3 ∈ AnyTypes I ] Σ[ a3 ∈ proj₁ i3 ] Σ[ p3 ∈ Is-just (f3 i3 a3) ]
                  ( ITree.force t₃ ≡ ndbr f3 i3 a3 p3
                  × (∀ {t} → Image f1 t
                     → Σ[ t' ∈ ITree E I R ] (Image f3 t' × Sbisim RetRel t t')) )
  on-ndbr-trans eq s12 b23
      with s12 .SSimF.on-ndbr eq
  ... | f2 , i2 , a2 , p2 , eq2 , fwd12
      with b23 .Sbisim.fwd .SSimF.on-ndbr eq2
  ... | f3 , i3 , a3 , p3 , eq3 , fwd23
      = f3 , i3 , a3 , p3 , eq3
      , λ img →
          let t₂' , img2 , rel12 = fwd12 img
              t₃' , img3 , rel23 = fwd23 img2
          in  t₃' , img3 , sbisim-trans rel12 rel23  -- under λ img ✓

  -----------------------------------------------------------------------------------------
  -- ssim-trans: NO with clauses — just dispatch to helpers

  ssim-trans s12 b23 .SSimF.on-ret  eq = on-ret-trans  eq s12 b23
  ssim-trans s12 b23 .SSimF.on-sil  eq = on-sil-trans  eq s12 b23
  ssim-trans s12 b23 .SSimF.on-vis  eq = on-vis-trans  eq s12 b23
  ssim-trans s12 b23 .SSimF.on-ndbr eq = on-ndbr-trans eq s12 b23

  sbisim-trans p q .Sbisim.fwd = ssim-trans (p .Sbisim.fwd) q
  sbisim-trans p q .Sbisim.bwd = ssim-trans (q .Sbisim.bwd) (sbisim-sym p)
{-  
  -- fwd: chain t₁→t₂ sim with t₂→t₃ bisim
  -- bwd: chain t₃→t₂ sim (from q.bwd) with t₂→t₁ bisim (sym p)
  sbisim-trans p q .Sbisim.fwd = ssim-trans (p .Sbisim.fwd) q
  sbisim-trans p q .Sbisim.bwd = ssim-trans (q .Sbisim.bwd) (sbisim-sym p)

  ssim-trans s12 b23 .SSimF.on-ret eq
      with s12 .SSimF.on-ret eq
  ... | r'  , eq2 , rel12
      with b23 .Sbisim.fwd .SSimF.on-ret eq2
  ... | r'' , eq3 , rel23
      = r'' , eq3 , ret-trans rel12 rel23

  ssim-trans s12 b23 .SSimF.on-sil eq
      with s12 .SSimF.on-sil eq
  ... | t₂' , eq2 , rel12
      with b23 .Sbisim.fwd .SSimF.on-sil eq2
  ... | t₃' , eq3 , rel23
      = t₃' , eq3 , sbisim-trans rel12 rel23          -- guarded: under λ of on-sil ✓

  ssim-trans s12 b23 .SSimF.on-vis eq
      with s12 .SSimF.on-vis eq
  ... | f2 , eq2 , h12
      with b23 .Sbisim.fwd .SSimF.on-vis eq2
  ... | f3 , eq3 , h23
      = f3 , eq3
      , λ at a → pw-trans sbisim-trans (h12 at a) (h23 at a)
                                                       -- guarded: under λ at a ✓

  ssim-trans s12 b23 .SSimF.on-ndbr eq
      with s12 .SSimF.on-ndbr eq
  ... | f2 , i2 , a2 , p2 , eq2 , fwd12
      with b23 .Sbisim.fwd .SSimF.on-ndbr eq2
  ... | f3 , i3 , a3 , p3 , eq3 , fwd23
      = f3 , i3 , a3 , p3 , eq3
      , λ img →
          let t₂' , img2 , rel12 = fwd12 img
              t₃' , img3 , rel23 = fwd23 img2
          in  t₃' , img3 , sbisim-trans rel12 rel23   -- guarded: under λ img ✓
-}
  -----------------------------------------------------------------------------------------
  Sbisim-isEquivalence : IsEquivalence (Sbisim RetRel)
  Sbisim-isEquivalence = record
    { refl  = sbisim-refl _
    ; sym   = sbisim-sym
    ; trans = sbisim-trans
    }

{-
-- Extract matching sil continuation from a bisimulation
sbisim-sil : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             {t t' t₁ : ITree E I R}
           → t ≈ t'
           → ITree.force t ≡ sil t₁
           → Σ[ t₂ ∈ ITree E I R ] (ITree.force t' ≡ sil t₂ × t₁ ≈ t₂)
sbisim-sil {t = t} {t' = t'} {t₁ = t₁} t≈t' force-eq
  with ITree.force t | ITree.force t' | Sbisim.step t≈t'
-- We name the forced nodes 'w' and 'w'' to avoid the "function call" problem
... | w | w' | step-val 
  -- Now we refine 'w' using our equality 'force-eq'
  with w | force-eq
... | .(sil t₁) | refl 
  -- Finally, we match on the step. 
  -- Since 'w' is now 'sil t₁', only 'silF' is valid.
  with step-val
... | silF t₁≈t₂ = _ , refl , t₁≈t₂    

-- Extract matching vis continuation from a bisimulation
sbisim-vis : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {t t' : ITree E I R}
               {f₁ : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
           → t ≈ t'
           → ITree.force t ≡ vis f₁
           → Σ[ f₂ ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))) ]
             ( ITree.force t' ≡ vis f₂
             × (∀ (at : AnyTypes E) (a : proj₁ at)
                → Pointwise (Sbisim _≡_) (f₁ at a) (f₂ at a)) )
sbisim-vis {t = t} {t' = t'} {f₁ = f₁} bisim eq
  with ITree.force t | ITree.force t' | Sbisim.step bisim
... | w | w' | step-val 
  with w | eq
... | .(vis f₁) | refl 
  with step-val
... | visF h = _ , refl , h

-- Extract matching ndbr continuation from a bisimulation
sbisim-ndbr : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {t t' : ITree E I R}
               {f₁ : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
               {i₁ : AnyTypes I} {a₁ : proj₁ i₁} {p₁ : Is-just (f₁ i₁ a₁)}
           → t ≈ t'
           → ITree.force t ≡ ndbr f₁ i₁ a₁ p₁
           → Σ[ f₂ ∈ ((i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))) ]
             Σ[ i₂ ∈ AnyTypes I ] Σ[ a₂ ∈ proj₁ i₂ ] Σ[ p₂ ∈ Is-just (f₂ i₂ a₂) ]
             ( ITree.force t' ≡ ndbr f₂ i₂ a₂ p₂
             × (∀ {t₁} → Image f₁ t₁ → Σ[ t₂ ∈ ITree E I R ] (Image f₂ t₂ × t₁ ≈ t₂))
             × (∀ {t₂} → Image f₂ t₂ → Σ[ t₁ ∈ ITree E I R ] (Image f₁ t₁ × t₁ ≈ t₂)) )
sbisim-ndbr {t = t} {t' = t'} {f₁ = f₁} {i₁ = i₁} {a₁ = a₁} {p₁ = p₁} bisim eq
  with ITree.force t | ITree.force t' | Sbisim.step bisim
... | w | w' | step-val 
  with w | eq
... | .(ndbr f₁ i₁ a₁ p₁) | refl 
  with step-val
-- Here we extract f₂, i₂, a₂, p₂ from the result of the forced node w'
... | ndbrF {f₂ = f₂} {i₂ = i₂} {a₂ = a₂} {p₂ = p₂} fwd bwd = 
    f₂ , i₂ , a₂ , p₂ , refl , fwd , bwd

sbisim-ndbr' : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {t t' : ITree E I R}
               {f₁ : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
               {i₁ : AnyTypes I} {a₁ : proj₁ i₁} {p₁ : Is-just (f₁ i₁ a₁)}
           → t ≈ t'
           → ITree.force t ≡ ndbr f₁ i₁ a₁ p₁
           → Σ[ f₂ ∈ ((i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))) ]
             Σ[ i₂ ∈ AnyTypes I ] Σ[ a₂ ∈ proj₁ i₂ ] Σ[ p₂ ∈ Is-just (f₂ i₂ a₂) ]
             ( ITree.force t' ≡ ndbr f₂ i₂ a₂ p₂
             × (∀ {t₁} → Image f₁ t₁ → Σ[ t₂ ∈ ITree E I R ] (Image f₂ t₂ × t₁ ≈ t₂))
             × (∀ {t₂} → Image f₂ t₂ → Σ[ t₁ ∈ ITree E I R ] (Image f₁ t₁ × t₁ ≈ t₂)) )
sbisim-ndbr' {t = t} {t' = t'} {f₁ = f₁} {i₁ = i₁} {a₁ = a₁} {p₁ = p₁} bisim eq
    with ITree.force t | ITree.force t' | Sbisim.step bisim | eq
... | .(ndbr f₁ i₁ a₁ p₁) | ndbr f₂ i₂ a₂ p₂ | ndbrF fwd bwd | refl
    = f₂ , i₂ , a₂ , p₂ , refl , fwd , bwd        

sbisim-ndbr-fwd : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                   {t t' t₁ : ITree E I R}
                   {f₁ : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
                   {i₁ : AnyTypes I} {a₁ : proj₁ i₁} {p₁ : Is-just (f₁ i₁ a₁)}
               → t ≈ t'
               → ITree.force t ≡ ndbr f₁ i₁ a₁ p₁
               → Image f₁ t₁
               → Σ[ t₂ ∈ ITree E I R ] (t' ─[ τ ]─► t₂ × t₁ ≈ t₂)
sbisim-ndbr-fwd {t = t} {t' = t'} {f₁ = f₁} {i₁ = i₁} {a₁ = a₁} {p₁ = p₁} bisim eq im
    with ITree.force t | ITree.force t' in eq-t' | Sbisim.step bisim | eq
... | .(ndbr f₁ i₁ a₁ p₁) | ndbr f₂ i₂ a₂ p₂ | ndbrF fwd _ | refl
    with fwd im
... | t₂ , (i' , a' , wit₂) , sim
    = t₂ , sNdbr eq-t' wit₂ , sim

pair-η : ∀ {ℓ ℓ'} {A : Set ℓ} {B : A → Set ℓ'} (p : Σ A B)
       → (proj₁ p , proj₂ p) ≡ p
pair-η (x , y) = refl

-----------------------------------------------------------------------------------------
-- Sbisim isEquivalence

-- Closed under a setoid on R
open import Relation.Binary using (Setoid)

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
      
  ... | ndbr f _ _ _  = ndbrF
        (λ {t′} (i , a , eq) → t′ , (i , a , eq) , sbisim-refl t′)
        (λ {t′} (i , a , eq) → t′ , (i , a , eq) , sbisim-refl t′)

  -- {-# NON_TERMINATING #-}
  sbisim-sym : ∀ {t₁ t₂ : ITree E I R} → Sbisim RetRel t₁ t₂ → Sbisim RetRel t₂ t₁
  sbisim-sym {t₁} {t₂} p .Sbisim.step
    with ITree.force t₁ | ITree.force t₂ | p .Sbisim.step
  ... | ret _  | ret _  | retF r    = retF (ret-sym r)
  ... | sil _  | sil _  | silF q    = silF (sbisim-sym q)
  ... | vis _  | vis _  | visF h    = visF (λ at a → pw-sym sbisim-sym (h at a))
  ... | ndbr _ _ _ _ | ndbr _ _ _ _ | ndbrF h-fwd h-bwd = ndbrF
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
  ... | ndbr _ _ _ _ | ndbr _ _ _ _ | ndbr _ _ _ _  | ndbrF hp-fwd hp-bwd  | ndbrF hq-fwd hq-bwd = ndbrF
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

-- Extract the witnessed tree from Is-just
to-witness : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} → Is-just m → A
to-witness {m = just x} _ = x

just-to-witness : ∀ {ℓ} {A : Set ℓ} {m : Maybe A} (p : Is-just m)
                → m ≡ just (to-witness p)
just-to-witness {m = just _} _ = refl

-- Forward: bisimilar process matches every trace
traces-fwd : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {t t' : ITree E I R} {s : List (EvLabel E)} {t'' : ITree E I R}
           → t ≈ t'
           → t ═⟨ s ⟩═► t''
           → Σ[ t''' ∈ ITree E I R ] (t' ═⟨ s ⟩═► t''' × t'' ≈ t''')

traces-fwd bisim bNil = _ , bNil , bisim

traces-fwd bisim (bTau (sSil eq) rest)
    with sbisim-sil bisim eq
... | t₂ , eq' , sim
    with traces-fwd sim rest
... | t''' , steps , bisim'
    = t''' , bTau (sSil eq') steps , bisim'

traces-fwd bisim (bTau (sNdbr {i = i} {a = a} eq wit) rest)
  with sbisim-ndbr-fwd bisim eq (i , a , wit)
... | t₂' , step₂ , sim
  with traces-fwd sim rest
... | t''' , steps , bisim'
  = t''' , bTau step₂ steps , bisim'

traces-fwd bisim (bStep (sVis {f = f} {at = at} {a = a} {t′ = t′} eq f-eq) rest)
  with sbisim-vis bisim eq
... | f₂ , eq' , h
  with f at a | f₂ at a in eq-f₂ | h at a | f-eq
... | just t₁ | just t₂ | pw-just sim | refl
-- eqf₂   : just t₁ ≡ just t′
  with traces-fwd sim rest
... | t''' , steps , bisim'
  = t''' , bStep (sVis eq' eq-f₂) steps , bisim'

-- The full theorem: ⇔ by symmetry using sbisim-sym
sbisim-traces : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                {t t' : ITree E I R}
              → t ≈ t'
              → ∀ {s} → traces t s ⇔ traces t' s
sbisim-traces bisim = mk⇔
  (λ { (t'' , tr) → let t''' , tr' , _ = traces-fwd bisim tr
                     in  t''' , tr' })
  (λ { (t'' , tr) → let t''' , tr' , _ = traces-fwd (SbisimEquiv.sbisim-sym ≡-equiv bisim) tr
                     in  t''' , tr' })

-}

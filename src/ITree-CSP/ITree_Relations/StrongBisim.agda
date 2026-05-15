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
open import ITree_Relations.FailuresDivergences

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
    {-
    -- ret case remains structural because 'ret' doesn't "transition" to a new tree
    on-ret  : ∀ {r}
            → ITree.force t₁ ≡ ret r
            → Σ[ r' ∈ R ]
              ( ITree.force t₂ ≡ ret r'
              × RetRel r r' )
    -}
    on-ret : ∀ {r t₁'}
           → t₁ ─[ ev (√ r) ]─► t₁'
           → Σ[ t₂' ∈ ITree E I R ]
                ( t₂ ─[ ev (√ r) ]─► t₂'
              × TreeRel t₁' t₂' )

    -- Visible transitions: If t₁ can do 'l', t₂ must do 'l' to a related state
    on-vis  : ∀ {l : Event E} {t₁'}
            → t₁ ─[ ev (evl l) ]─► t₁'
            → Σ[ t₂' ∈ ITree E I R ]
                ( t₂ ─[ ev (evl l) ]─► t₂'
              × TreeRel t₁' t₂' )

    -- Silent transitions: Handles both 'sil' and 'ndbr' steps from your LTS
    on-tau  : ∀ {t₁'}
            → t₁ ─[ τ ]─► t₁'
            → Σ[ t₂' ∈ ITree E I R ]
              ( t₂ ─[ τ ]─► t₂'
              × TreeRel t₁' t₂' )
              
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

-----------------------------------------------------------------------------------------
-- Some simple Sbisim with special RetRel

-- Standard strong bisimulation: propositional equality on return values
_∼_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → Rel (ITree E I R) _
_∼_ = Sbisim _≡_

-- Ignore return values entirely (e.g., for divergence checking)
_∼⊤_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → Rel (ITree E I R) _
_∼⊤_ {ℓr = ℓr}  = Sbisim (λ _ _ → ⊤ {lzero})

-- Return values related by some custom _~_
_∼[_]_ : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ITree E I R → Rel R ℓ≡ → ITree E I R → Set _
t₁ ∼[ _~_ ] t₂ = Sbisim _~_ t₁ t₂

-----------------------------------------------------------------------------------------
--
open import Relation.Binary using (Setoid)

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

--  ssim-refl t .SSimF.on-ret eq = _ , eq , ret-refl
  ssim-refl t .SSimF.on-ret eq = _ , eq , sbisim-refl _

  -- We match on the transition proof 'step'
  ssim-refl t .SSimF.on-tau step = _ , step , sbisim-refl _
  
  ssim-refl t .SSimF.on-vis step = _ , step , sbisim-refl _

  -----------------------------------------------------------------------------------------
  -- Symmetry
  
  sbisim-sym : ∀ {t₁ t₂ : ITree E I R} → Sbisim RetRel t₁ t₂ → Sbisim RetRel t₂ t₁
  sbisim-sym p .Sbisim.fwd = p .Sbisim.bwd
  sbisim-sym p .Sbisim.bwd = p .Sbisim.fwd

  -----------------------------------------------------------------------------------------
  -- Transitivity Helpers

  ssim-trans : ∀ {t₁ t₂ t₃ : ITree E I R}
               → SSimF RetRel (Sbisim RetRel) t₁ t₂
               → Sbisim RetRel t₂ t₃
               → SSimF RetRel (Sbisim RetRel) t₁ t₃

  sbisim-trans : ∀ {t₁ t₂ t₃}
    → Sbisim RetRel t₁ t₂
    → Sbisim RetRel t₂ t₃
    → Sbisim RetRel t₁ t₃

{-
  on-ret-trans : ∀ {t₁ t₂ t₃ : ITree E I R} {r}
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
-}
  on-ret-trans : ∀ {t₁ t₂ t₃ t₁' : ITree E I R} {r : R}
                → t₁ ─[ ev (√ r) ]─► t₁'
                → SSimF RetRel (Sbisim RetRel) t₁ t₂
                → Sbisim RetRel t₂ t₃
                → Σ[ t₃' ∈ ITree E I R ] (t₃ ─[ ev (√ r) ]─► t₃' × Sbisim RetRel t₁' t₃')
  on-ret-trans step s12 b23
      with s12 .SSimF.on-ret step
  ... | t₂' , step12 , rel12
      with b23 .Sbisim.fwd .SSimF.on-ret step12
  ... | t₃' , step23 , rel23
      = t₃' , step23 , sbisim-trans rel12 rel23

  -- This replaces on-sil-trans and on-ndbr-trans
  on-tau-trans : ∀ {t₁ t₂ t₃ t₁' : ITree E I R}
                → t₁ ─[ τ ]─► t₁'
                → SSimF RetRel (Sbisim RetRel) t₁ t₂
                → Sbisim RetRel t₂ t₃
                → Σ[ t₃' ∈ ITree E I R ] (t₃ ─[ τ ]─► t₃' × Sbisim RetRel t₁' t₃')
  on-tau-trans step s12 b23
      with s12 .SSimF.on-tau step
  ... | t₂' , step12 , rel12
      with b23 .Sbisim.fwd .SSimF.on-tau step12
  ... | t₃' , step23 , rel23
      = t₃' , step23 , sbisim-trans rel12 rel23

  on-vis-trans : ∀ {t₁ t₂ t₃ t₁' : ITree E I R} {l}
                → t₁ ─[ ev (evl l) ]─► t₁'
                → SSimF RetRel (Sbisim RetRel) t₁ t₂
                → Sbisim RetRel t₂ t₃
                → Σ[ t₃' ∈ ITree E I R ] (t₃ ─[ ev (evl l) ]─► t₃' × Sbisim RetRel t₁' t₃')
  on-vis-trans step s12 b23
      with s12 .SSimF.on-vis step
  ... | t₂' , step12 , rel12
      with b23 .Sbisim.fwd .SSimF.on-vis step12
  ... | t₃' , step23 , rel23
      = t₃' , step23 , sbisim-trans rel12 rel23

  -----------------------------------------------------------------------------------------
  -- Main Transitivity Logic

  ssim-trans s12 b23 .SSimF.on-ret  eq   = on-ret-trans eq s12 b23
  ssim-trans s12 b23 .SSimF.on-tau  step = on-tau-trans step s12 b23
  ssim-trans s12 b23 .SSimF.on-vis  step = on-vis-trans step s12 b23

  sbisim-trans p q .Sbisim.fwd = ssim-trans (p .Sbisim.fwd) q
  sbisim-trans p q .Sbisim.bwd = ssim-trans (q .Sbisim.bwd) (sbisim-sym p)

  -- Package as a Setoid
  Sbisim-isEquivalence : IsEquivalence (Sbisim RetRel)
  Sbisim-isEquivalence = record
    { refl  = sbisim-refl _
    ; sym   = sbisim-sym
    ; trans = sbisim-trans
    }



-----------------------------------------------------------------------------------------
-- Extraction lemmas — now trivial wrappers around on-tau / on-vis

-- sil case: feed sSil step into on-tau
sbisim-sil : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             {t t' t₁ : ITree E I R}
           → t ∼ t'
           → ITree.force t ≡ sil t₁
           → Σ[ t₂ ∈ ITree E I R ] (t' ─[ τ ]─► t₂ × t₁ ∼ t₂)
sbisim-sil bisim eq =
    bisim .Sbisim.fwd .SSimF.on-tau (sSil eq)

-- ndbr case: feed sNdbr step into on-tau
sbisim-ndbr-fwd : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                  {t t' t₁ : ITree E I R}
                  {f : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
                  {i : AnyTypes I} {a : proj₁ i} {p : Is-just (f i a)}
                → t ∼ t'
                → ITree.force t ≡ ndbr f i a p
                → Image f t₁
                → Σ[ t₂ ∈ ITree E I R ] (t' ─[ τ ]─► t₂ × t₁ ∼ t₂)
sbisim-ndbr-fwd bisim eq (i , a , wit) =
    bisim .Sbisim.fwd .SSimF.on-tau (sNdbr eq wit)

-- vis case: feed sVis step into on-vis
sbisim-vis : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {t t' t₁' : ITree E I R}
               {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
               {at : AnyTypes E} {a : proj₁ at}
           → t ∼ t'
           → ITree.force t ≡ vis f
           → f at a ≡ just t₁'
           → Σ[ t₂' ∈ ITree E I R ]
             ( t' ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t₂'
             × t₁' ∼ t₂' )
sbisim-vis bisim eq f-eq =
    bisim .Sbisim.fwd .SSimF.on-vis (sVis eq f-eq)

-----------------------------------------------------------------------------------------
-- Trace preservation

traces-fwd : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             {t t' : ITree E I R} {s : List (Event√ E R)} {t'' : ITree E I R}
           → t ∼ t'
           → t ═⟨ s ⟩═► t''
           → Σ[ t''' ∈ ITree E I R ] (t' ═⟨ s ⟩═► t''' × t'' ∼ t''')

traces-fwd bisim bNil =
    _ , bNil , bisim

-- sSil: t does τ via sil node
traces-fwd bisim (bTau step@(sSil _) rest)
    with bisim .Sbisim.fwd .SSimF.on-tau step
... | t₂' , step' , bisim'
    with traces-fwd bisim' rest
... | t''' , rest' , bisim''
    = t''' , bTau step' rest' , bisim''

-- sNdbr: t does τ via ndbr node
traces-fwd bisim (bTau step@(sNdbr _ _) rest)
    with bisim .Sbisim.fwd .SSimF.on-tau step
... | t₂' , step' , bisim'
    with traces-fwd bisim' rest
... | t''' , rest' , bisim''
    = t''' , bTau step' rest' , bisim''

-- sMixSlide: t does τ via mix's silent timeout
traces-fwd bisim (bTau step@(sMixSlide _) rest)
    with bisim .Sbisim.fwd .SSimF.on-tau step
... | t₂' , step' , bisim'
    with traces-fwd bisim' rest
... | t''' , rest' , bisim''
    = t''' , bTau step' rest' , bisim''

-- sVis: t does a visible step
traces-fwd bisim (bStep step@(sRet _) rest)
    with bisim .Sbisim.fwd .SSimF.on-ret step
... | t₂' , step' , bisim'
    with traces-fwd bisim' rest
... | t''' , rest' , bisim''
    = t''' , bStep step' rest' , bisim''

-- sVis: t does a visible step
traces-fwd bisim (bStep step@(sVis _ _) rest)
    with bisim .Sbisim.fwd .SSimF.on-vis step
... | t₂' , step' , bisim'
    with traces-fwd bisim' rest
... | t''' , rest' , bisim''
    = t''' , bStep step' rest' , bisim''

-- sMixVis: t does a visible step from a mix node
traces-fwd bisim (bStep step@(sMixVis _ _) rest)
    with bisim .Sbisim.fwd .SSimF.on-vis step
... | t₂' , step' , bisim'
    with traces-fwd bisim' rest
... | t''' , rest' , bisim''
    = t''' , bStep step' rest' , bisim''

-----------------------------------------------------------------------------------------
sbisim-traces : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                {t t' : ITree E I R}
              → t ∼ t'
              → ∀ {s} → traces t s ⇔ traces t' s
sbisim-traces bisim = mk⇔
    (λ { (t'' , tr) →
        let t''' , tr' , _ = traces-fwd bisim tr
        in  t''' , tr' })
    (λ { (t'' , tr) →
        let t''' , tr' , _ = traces-fwd (SbisimEquiv.sbisim-sym ≡-equiv bisim) tr
        in  t''' , tr' })


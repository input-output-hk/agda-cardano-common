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

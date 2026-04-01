{-
  This module defines weak bisimulation between ITrees where
    - invisible choice's indices are discarded and only their children (ITrees) matter;
    - internal tau is omitted in transition relations.

  This bisimulation is not able to distinguish the two processes below. It will treat them equally.
  -- P = a → STOP
  -- Q = (τ → Q)  ⊓  (a → STOP)    -- internal choice: diverge or do a
-}

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
-- open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; ∃₂; Σ-syntax; ∃-syntax)
open import Relation.Unary
open import Function using (case_of_)

open import Data.Maybe.Relation.Binary.Pointwise using (Pointwise)
  renaming (just to pw-just; nothing to pw-nothing; sym to pw-sym; trans to pw-trans)
open import Relation.Binary                       using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym; trans; refl; inspect; [_])

open import Interaction_Trees
open import ITree_Relations.LTS using (EvLabel; evLabel; Label;
  _─[_]─►_; sSil; sVis; sInv;
  _─[τ*]─►_; τ*-zero; τ*-step; -- τ*-sil; τ*-inv;
  _═[_]═►_; weak-τ; weak-ev
  )
open import ITree_Relations.Divergence

module ITree_Relations.DRWeakBisim1 where
open Label
open EvLabel

-- One-sided weak simulation: every step of t₁ is weakly matched by t₂
record DRWSimF {ℓ ℓe ℓi ℓr ℓ≡ ℓ≈ : Level}
             {E : Set ℓ → Set ℓe}
             {I : Set ℓ → Set ℓi}
             {R : Set ℓr}
             (RetRel  : Rel R ℓ≡)
             (TreeRel : Rel (ITree E I R) ℓ≈)
             (t₁ t₂  : ITree E I R)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓ≈ ⊔ ℓr) where
  field
    -- If t₁ is a return node, t₂ must weakly (via τ*) reach a related return node
    on-ret : ∀ {r}
           → ITree.force t₁ ≡ ret r
           → Σ[ t₂' ∈ ITree E I R ]
             Σ[ r'  ∈ R ]
             ( t₂ ═[ τ ]═► t₂'
             × ITree.force t₂' ≡ ret r'
             × RetRel r r' )

    -- If t₁ takes a visible step, t₂ must weakly match it
    on-vis : ∀ {at : AnyTypes E} {a : proj₁ at} {t₁'}
           → t₁ ─[ ev (evLabel (proj₁ at) (proj₂ at) a) ]─► t₁'
           → Σ[ t₂' ∈ ITree E I R ]
             ( t₂ ═[ ev (evLabel (proj₁ at) (proj₂ at) a) ]═► t₂'
             × TreeRel t₁' t₂' )

    -- If t₁ takes a silent step, t₂ must weakly match it (via ═[τ]═►)
    on-tau : ∀ {t₁'}
           → t₁ ─[ τ ]─► t₁'
           → Σ[ t₂' ∈ ITree E I R ]
             ( t₂ ═[ τ ]═► t₂'
             × TreeRel t₁' t₂' )

    on-div : Divergent t₁ → Divergent t₂

-- Weak bisimulation: simulation in both directions, coinductively
record DRWbisim {ℓ ℓe ℓi ℓr ℓ≡ : Level}
              {E : Set ℓ → Set ℓe}
              {I : Set ℓ → Set ℓi}
              {R : Set ℓr}
              (RetRel : Rel R ℓ≡)
              (t₁ t₂ : ITree E I R)
            : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓr) where
  coinductive
  field
    fwd : DRWSimF RetRel (DRWbisim RetRel) t₁ t₂  -- t₁ is simulated by t₂
    bwd : DRWSimF RetRel (DRWbisim RetRel) t₂ t₁  -- t₂ is simulated by t₁
    

{-
record DRWbisim {ℓ ℓe ℓi ℓr ℓ≡ : Level}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (RetRel : Rel R ℓ≡)
  (t₁ t₂ : ITree E I R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓ≡ ⊔ ℓr) where
  coinductive
  field
    -- 1. If t₁ takes a step, t₂ matches it weakly
    match-L : ∀ {L t₁'} 
      → (t₁ ─[ L ]─► t₁') 
      → Σ[ t₂' ∈ ITree E I R ] (t₂ ═[ L ]═► t₂' × DRWbisim RetRel t₁' t₂')

    -- 2. If t₂ takes a step, t₁ matches it weakly (Symmetry)
    match-R : ∀ {L t₂'} 
      → (t₂ ─[ L ]─► t₂') 
      → Σ[ t₁' ∈ ITree E I R ] (t₁ ═[ L ]═► t₁' × DRWbisim RetRel t₁' t₂')

    -- 3. Termination matching
    match-ret : ∀ {r₁}
      → ITree.force t₁ ≡ ret r₁
      → ITree.force t₂ ≡ ret r₂
      → Σ[ r₂ ∈ R ] (t₂ ═[ Label.τ ]═► (itree (ret r₂)) × RetRel r₁ r₂)
-}      

-- Standard strong bisimulation: propositional equality on return values
_≈_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → Rel (ITree E I R) _
_≈_ = DRWbisim _≡_

-- Ignore return values entirely (e.g., for divergence checking)
_≈⊤_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → Rel (ITree E I R) _
_≈⊤_ {ℓr = ℓr}  = DRWbisim (λ _ _ → ⊤ {lzero})

-- Return values related by some custom _~_
_≈[_]_ : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ITree E I R → Rel R ℓ≡ → ITree E I R → Set _
t₁ ≈[ _~_ ] t₂ = DRWbisim _~_ t₁ t₂

-- Closed under a setoid on R
open import Relation.Binary using (Setoid)

bisimSetoid : ∀ {ℓ ℓe ℓi ℓr ℓ≡} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} 
  → (S : Setoid ℓr ℓ≡) → Rel (ITree E I (Setoid.Carrier S)) _
bisimSetoid S = DRWbisim (Setoid._≈_ S)

module DRWbisimEquiv
  {ℓ ℓe ℓi ℓr ℓ≡ : Level}
  {E : Set ℓ → Set ℓe}
  {I : Set ℓ → Set ℓi}
  {R : Set ℓr}
  {RetRel : Rel R ℓ≡}
  (retEq : IsEquivalence RetRel) where

  open IsEquivalence retEq renaming (refl to ret-refl; sym to ret-sym; trans to ret-trans)

  private
    -- Helper 1: concatenate τ* chains
    τ*-concat : ∀ {ℓ ℓe ℓi ℓr : Level}
              {E : Set ℓ → Set ℓe}
              {I : Set ℓ → Set ℓi}
              {R : Set ℓr}
              {t t' t'' : ITree E I R}
               → t ─[τ*]─► t' → t' ─[τ*]─► t'' → t ─[τ*]─► t''
    τ*-concat τ*-zero       q = q
    τ*-concat (τ*-step s p) q = τ*-step s (τ*-concat p q)

    -- Helper 2: propagate a τ* chain through a bisimulation
    lift-τ* : ∀ {t t' s}
            → t ─[τ*]─► t'
            → DRWbisim RetRel t s
            → Σ[ s' ∈ ITree E I R ] (s ─[τ*]─► s' × DRWbisim RetRel t' s')
    lift-τ* {t} {.t} τ*-zero       p = _ , τ*-zero , p
    lift-τ* (τ*-step step rest) p
        with p .DRWbisim.fwd .DRWSimF.on-tau step
    ... | s-mid , weak-τ s-steps , bisim-mid
        with lift-τ* rest bisim-mid
    ... | s' , s-rest , bisim-fin
        = s' , τ*-concat s-steps s-rest , bisim-fin
        
    -- Helper 3: propagate a weak visible transition through a bisimulation
    lift-weak-ev : ∀ {t t' s at a}
                 → t ═[ ev (evLabel (proj₁ at) (proj₂ at) a) ]═► t'
                 → DRWbisim RetRel t s
                 → Σ[ s' ∈ ITree E I R ]
                   ( s ═[ ev (evLabel (proj₁ at) (proj₂ at) a) ]═► s'
                   × DRWbisim RetRel t' s')
    lift-weak-ev (weak-ev pre step post) p =
        let s-pre-end  , s-pre-steps , bisim-pre = lift-τ* pre p
            s-vis-end  , s-vis-step  , bisim-vis = bisim-pre .DRWbisim.fwd .DRWSimF.on-vis step
            s-post-end , s-post-steps , bisim-post = lift-τ* post bisim-vis
        in  s-post-end , splice s-pre-steps s-vis-step s-post-steps , bisim-post
      where
        -- Splice a τ* prefix and τ* suffix around a weak-ev
        splice : ∀ {s s-mid s-end s' at a}
               → s     ─[τ*]─► s-mid
               → s-mid ═[ ev (evLabel (proj₁ at) (proj₂ at) a) ]═► s-end
               → s-end ─[τ*]─► s'
               → s     ═[ ev (evLabel (proj₁ at) (proj₂ at) a) ]═► s'
        splice pre (weak-ev mid-pre vis-step mid-post) post =
            weak-ev (τ*-concat pre mid-pre) vis-step (τ*-concat mid-post post)

  {-# NON_TERMINATING #-}
  drwbisim-refl : ∀ (t : ITree E I R) → DRWbisim RetRel t t
  sim-refl    : ∀ (t : ITree E I R) → DRWSimF RetRel (DRWbisim RetRel) t t

  -- Both directions are identical since t simulates itself
  drwbisim-refl t .DRWbisim.fwd = sim-refl t
  drwbisim-refl t .DRWbisim.bwd = sim-refl t

  -- on-ret: t itself is the witness; reach ret via empty τ* chain
  sim-refl t .DRWSimF.on-ret eq =
      t , _ , weak-τ τ*-zero , eq , ret-refl

  -- on-vis: match the same visible step with empty τ* on both sides
  sim-refl t .DRWSimF.on-vis {t₁' = t'} step =
      t' , weak-ev τ*-zero step τ*-zero , drwbisim-refl t'

  -- on-tau: wrap the single τ step into a weak-τ, then close coinductively
  sim-refl t .DRWSimF.on-tau {t₁' = t'} step =
      t' , weak-τ (τ*-step step τ*-zero) , drwbisim-refl t'

  sim-refl t .DRWSimF.on-div d = d

  -- Symmetry: trivially swap fwd and bwd
  drwbisim-sym : ∀ {t₁ t₂ : ITree E I R} → DRWbisim RetRel t₁ t₂ → DRWbisim RetRel t₂ t₁
  drwbisim-sym p .DRWbisim.fwd = p .DRWbisim.bwd
  drwbisim-sym p .DRWbisim.bwd = p .DRWbisim.fwd

  drwbisim-trans : ∀ {t₁ t₂ t₃}
               → DRWbisim RetRel t₁ t₂ → DRWbisim RetRel t₂ t₃ → DRWbisim RetRel t₁ t₃
  drwsim-trans   : ∀ {t₁ t₂ t₃}
               → DRWSimF RetRel (DRWbisim RetRel) t₁ t₂
               → DRWbisim RetRel t₂ t₃
               → DRWSimF RetRel (DRWbisim RetRel) t₁ t₃

  on-ret-trans : ∀ {t₁ t₂ t₃ : ITree E I R} {r}
               → ITree.force t₁ ≡ ret r
               → DRWSimF RetRel (DRWbisim RetRel) t₁ t₂
               → DRWbisim RetRel t₂ t₃
               → Σ[ t₃' ∈ ITree E I R ] Σ[ r' ∈ R ]
                 ( t₃ ═[ τ ]═► t₃'
                 × ITree.force t₃' ≡ ret r'
                 × RetRel r r' )
  on-ret-trans eq sim₁₂ bisim₂₃
      with sim₁₂ .DRWSimF.on-ret eq
  ... | t₂' , r' , weak-τ chain₁₂ , eq₂ , rel₁₂
      with lift-τ* chain₁₂ bisim₂₃
  ... | t₃' , t₃-chain , bisim-mid
      with bisim-mid .DRWbisim.fwd .DRWSimF.on-ret eq₂
  ... | t₃'' , r'' , weak-τ chain₂₃ , eq₃ , rel₂₃
      = t₃'' , r'' , weak-τ (τ*-concat t₃-chain chain₂₃) , eq₃ , ret-trans rel₁₂ rel₂₃

  on-tau-trans : ∀ {t₁ t₂ t₃ t₁' : ITree E I R}
               → t₁ ─[ τ ]─► t₁'
               → DRWSimF RetRel (DRWbisim RetRel) t₁ t₂
               → DRWbisim RetRel t₂ t₃
               → Σ[ t₃' ∈ ITree E I R ]
                 ( t₃ ═[ τ ]═► t₃'
                 × DRWbisim RetRel t₁' t₃' )
  on-tau-trans step sim₁₂ bisim₂₃
      with sim₁₂ .DRWSimF.on-tau step
  ... | t₂' , weak-τ chain₁₂ , bisim₁₂'
      with lift-τ* chain₁₂ bisim₂₃
  ... | t₃' , chain₂₃ , bisim₂₃'
      = t₃' , weak-τ chain₂₃ , drwbisim-trans bisim₁₂' bisim₂₃'

  on-vis-trans : ∀ {t₁ t₂ t₃ t₁' : ITree E I R} {at : AnyTypes E} {a : proj₁ at}
               → t₁ ─[ ev (evLabel (proj₁ at) (proj₂ at) a) ]─► t₁'
               → DRWSimF RetRel (DRWbisim RetRel) t₁ t₂
               → DRWbisim RetRel t₂ t₃
               → Σ[ t₃' ∈ ITree E I R ]
                 ( t₃ ═[ ev (evLabel (proj₁ at) (proj₂ at) a) ]═► t₃'
                 × DRWbisim RetRel t₁' t₃' )
  on-vis-trans step sim₁₂ bisim₂₃
      with sim₁₂ .DRWSimF.on-vis step
  ... | t₂' , t₂-step , bisim₁₂'
      with lift-weak-ev t₂-step bisim₂₃
  ... | t₃' , t₃-step , bisim₂₃'
      = t₃' , t₃-step , drwbisim-trans bisim₁₂' bisim₂₃'

  on-div-trans : ∀ {t₁ t₂ t₃ : ITree E I R}
               → DRWSimF RetRel (DRWbisim RetRel) t₁ t₂
               → DRWbisim RetRel t₂ t₃
               → Divergent t₁
               → Divergent t₃
  on-div-trans sim₁₂ bisim₂₃ d
      with sim₁₂ .DRWSimF.on-div d
         | bisim₂₃ .DRWbisim.fwd .DRWSimF.on-div
  ... | d₂ | on-div₂₃ = on-div₂₃ d₂

{-
  wsim-trans : ∀ {t₁ t₂ t₃ : ITree E I R}
             → DRWSimF RetRel (WBisim RetRel) t₁ t₂
             → WBisim RetRel t₂ t₃
             → DRWSimF RetRel (WBisim RetRel) t₁ t₃
-}             
  drwsim-trans sim₁₂ bisim₂₃ .DRWSimF.on-ret eq  = on-ret-trans eq  sim₁₂ bisim₂₃
  drwsim-trans sim₁₂ bisim₂₃ .DRWSimF.on-tau step = on-tau-trans step sim₁₂ bisim₂₃
  drwsim-trans sim₁₂ bisim₂₃ .DRWSimF.on-vis step = on-vis-trans step sim₁₂ bisim₂₃
  drwsim-trans sim₁₂ bisim₂₃ .DRWSimF.on-div d = on-div-trans sim₁₂ bisim₂₃ d  

{-
  drwbisim-trans : ∀ {t₁ t₂ t₃ : ITree E I R}
               → WBisim RetRel t₁ t₂ → WBisim RetRel t₂ t₃ → WBisim RetRel t₁ t₃
-}               
  drwbisim-trans p q .DRWbisim.fwd = drwsim-trans (p .DRWbisim.fwd) q
  drwbisim-trans p q .DRWbisim.bwd = drwsim-trans (q .DRWbisim.bwd) (drwbisim-sym p)


  DRWbisim-isEquivalence : IsEquivalence (DRWbisim RetRel)
  DRWbisim-isEquivalence = record
    { refl  = drwbisim-refl _
    ; sym   = drwbisim-sym
    ; trans = drwbisim-trans
    }
    

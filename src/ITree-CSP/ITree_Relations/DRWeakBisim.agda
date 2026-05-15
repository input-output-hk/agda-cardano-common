{-
  This module defines divergence-respecting weak bisimulation (DRW-Bisimulation) between ITrees where
    - invisible choice's indices are discarded and only their children (ITrees) matter;
    - internal tau is omitted in transition relations;
    - one process is divergent and the other is too.

  This DRW-bisimulation is able to distinguish the two CSP processes below. 
  -- P = a → STOP
  -- Q = (τ → Q)  ⊓  (a → STOP)    -- internal choice: diverge or do a
-}


{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing; Is-just) renaming (map to mapMaybe)
-- open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit.Base using () renaming (tt to tt₀)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; ∃₂; Σ-syntax; ∃-syntax)
open import Relation.Unary
open import Function using (case_of_)

open import Data.Maybe.Relation.Binary.Pointwise using (Pointwise)
  renaming (just to pw-just; nothing to pw-nothing; sym to pw-sym; trans to pw-trans)
open import Relation.Binary                       using (Rel; IsEquivalence)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym; trans; refl; inspect; [_])

open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (¬_)

open import Prelude
open import Interaction_Trees
open import ITree_Relations.LTS using (Event; evLabel; Event√; Label;
  _─[_]─►_; sRet; sSil; sVis; sNdbr; sMixVis; sMixSlide;
  _─[τ*]─►_; τ*-zero; τ*-step; -- τ*-sil; τ*-inv;
  _═[_]═►_; weak-τ; weak-ev;
  _═⟨_⟩═►_; bNil; bTau; bStep;
  τ-from-force-vis-impossible;
  module Traces
  )
open import ITree_Relations.FailuresDivergences

module ITree_Relations.DRWeakBisim where
open Label
open Event
open Event√

-----------------------------------------------------------------------------------------
-- Define divergence-respecting weak bisimulation

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
           → t₁ ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t₁'
           → Σ[ t₂' ∈ ITree E I R ]
             ( t₂ ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t₂'
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

-----------------------------------------------------------------------------------------
-- Some simple DRWbisim with special RetRel

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

-----------------------------------------------------------------------------------------
-- DRWbisim isEquivalence

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
                 → t ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t'
                 → DRWbisim RetRel t s
                 → Σ[ s' ∈ ITree E I R ]
                   ( s ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► s'
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
               → s-mid ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► s-end
               → s-end ─[τ*]─► s'
               → s     ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► s'
        splice pre (weak-ev mid-pre vis-step mid-post) post =
            weak-ev (τ*-concat pre mid-pre) vis-step (τ*-concat mid-post post)

  -----------------------------------------------------------------------------------------
  -- drwbisim-refl 

  -- declare first
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

  -----------------------------------------------------------------------------------------
  -- Symmetry: trivially swap fwd and bwd
  drwbisim-sym : ∀ {t₁ t₂ : ITree E I R} → DRWbisim RetRel t₁ t₂ → DRWbisim RetRel t₂ t₁
  drwbisim-sym p .DRWbisim.fwd = p .DRWbisim.bwd
  drwbisim-sym p .DRWbisim.bwd = p .DRWbisim.fwd

  -----------------------------------------------------------------------------------------
  -- Transitivity: 
  drwbisim-trans : ∀ {t₁ t₂ t₃}
               → DRWbisim RetRel t₁ t₂
               → DRWbisim RetRel t₂ t₃
               → DRWbisim RetRel t₁ t₃
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
               → t₁ ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t₁'
               → DRWSimF RetRel (DRWbisim RetRel) t₁ t₂
               → DRWbisim RetRel t₂ t₃
               → Σ[ t₃' ∈ ITree E I R ]
                 ( t₃ ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► t₃'
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
  
  drwbisim-trans p q .DRWbisim.fwd = drwsim-trans (p .DRWbisim.fwd) q
  drwbisim-trans p q .DRWbisim.bwd = drwsim-trans (q .DRWbisim.bwd) (drwbisim-sym p)


  DRWbisim-isEquivalence : IsEquivalence (DRWbisim RetRel)
  DRWbisim-isEquivalence = record
    { refl  = drwbisim-refl _
    ; sym   = drwbisim-sym
    ; trans = drwbisim-trans
    }
    
-----------------------------------------------------------------------------------------
-- Lemmas for DRWbisim

-- div is equal to itself
div-drw : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (div {E = E} {I = I} {R = R}) ≈ div
div-drw = DRWbisimEquiv.drwbisim-refl ≡-equiv div  

-- A divergent process cannot be at ret
divergent-not-ret : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                    {t : ITree E I R} {r : R}
                  → Divergent t → ITree.force t ≡ ret r → ⊥
divergent-not-ret d eq with d .Divergent.step
... | sSil eq'   = case trans (sym eq') eq of λ ()
... | sNdbr eq' _ = case trans (sym eq') eq of λ ()
... | sMixSlide eq' = case trans (sym eq') eq of λ ()

{- This is not true now because P ▷ Q can both diverge and vis
-- A divergent process cannot take a visible step
divergent-not-vis : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                    {t t' : ITree E I R} {el : Event E}
                  → Divergent t → t ─[ ev (evl el) ]─► t' → ⊥
divergent-not-vis d (sVis eq _) with d .Divergent.step
... | sSil eq'   = case trans (sym eq') eq of λ ()
... | sNdbr eq' _ = case trans (sym eq') eq of λ ()
... | sMixSlide eq' = case trans (sym eq') eq of λ ()
-- sMixVis: t is mix-shaped. Three τ-step shapes for d:
--   sSil/sNdbr give immediate force-shape contradictions.
--   sMixSlide is NOT a contradiction: a mix node legitimately offers BOTH
--   a visible event (via sMixVis) AND a silent slide. The lemma comment
--   above already notes the lemma is not true in general; this case makes
--   the failure explicit. Left as a hole pending a redesign of the lemma.
divergent-not-vis d (sMixVis eq _) with d .Divergent.step
... | sSil eq'      = case trans (sym eq') eq of λ ()
... | sNdbr eq' _   = case trans (sym eq') eq of λ ()
... | sMixSlide eq' = case trans (sym eq') eq of λ ()
-}

{- This however it is not true generally, such as
  P = τ → τ → τ → ...           (pure silent divergence)
  Q = vis e (λ _ → τ → τ → ...) (does a visible event, then diverges)
-}
{-
mutual
  {-# NON_TERMINATING #-}
  sim-div : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {P Q : ITree E I R}
          → Divergent P → Divergent Q
          → DRWSimF _≡_ (DRWbisim _≡_) P Q
  sim-div dP dQ .DRWSimF.on-ret eq =
      ⊥-elim (divergent-not-ret dP eq)
  sim-div dP dQ .DRWSimF.on-vis step =
      ⊥-elim (divergent-not-vis dP step)
  sim-div dP dQ .DRWSimF.on-tau step = 
      --let eq-next = tau-det step (dP .Divergent.step)
      --in
        dQ .Divergent.next
        , weak-τ (τ*-step (dQ .Divergent.step) τ*-zero)
        , subst (λ t → DRWbisim _≡_ t (dQ .Divergent.next)) (sym {!!})
                (div-≈ (dP .Divergent.diverge) (dQ .Divergent.diverge))

  {-
      let eq-next = tau-det step (dP .Divergent.step)
      in  dQ .next
        , weak-τ (τ*-step (dQ .step) τ*-zero)
        , subst (λ t → DRWbisim _≡_ t (dQ .next)) (sym eq-next)
                (div-≈ (dP .diverge) (dQ .diverge))
  -}              
  sim-div dP dQ .DRWSimF.on-div _ = dQ

  -- All divergent ITrees are DRWbisimilar. This might not be true considering nondeterministic choice?
  -- div ⊓ (a -> Stop) ≟ div
  div-≈ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {P Q : ITree E I R}
        → Divergent P
        → Divergent Q
        → DRWbisim _≡_ P Q
  div-≈ dP dQ .DRWbisim.fwd = sim-div dP dQ
  div-≈ dP dQ .DRWbisim.bwd = sim-div dQ dP
-}

-- Divergence respecting
sim-div-preserved : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {P Q : ITree E I R}
        → Divergent P
        → P ≈ Q
        → Divergent Q
sim-div-preserved dP bisim = DRWSimF.on-div (DRWbisim.fwd bisim) dP

-----------------------------------------------------------------------------------------
-- Trace, divergence, and failure preservation under DRWbisim _≡_.
--
-- These show that `_≈_` (= `DRWbisim _≡_`) is consistent with the standard
-- denotational models of CSP defined in `ITree_Relations.LTS`:
--   • traces      (sequences of `Event√` reachable via `═⟨_⟩═►`)
--   • divergences (traces extended into a divergent state)
--   • failures    (traces ending at a process refusing some event-set)
--
-- The argument is the usual "lift big-step traces through bisim" reduction:
-- a witnessed `t ═⟨ s ⟩═► t'` plus a bisim `t ≈ u` produces a matching
-- witnessed `u ═⟨ s ⟩═► u'` with `t' ≈ u'`.  Failures additionally need a
-- `_ref_` lift, which goes through for `ref-tick` directly via `on-ret`,
-- and for `ref-stable` via a stabilisation step (postulated; see comment).
-----------------------------------------------------------------------------------------
module Preservation
  {ℓ ℓe ℓi ℓr : Level}
  {E : Set ℓ → Set ℓe}
  {I : Set ℓ → Set ℓi}
  {R : Set ℓr}
  where

  open Traces
  open Failures
  open import Data.List.Properties using (++-assoc)
  open Relation.Binary.PropositionalEquality using (cong)

  -- Prepend a τ*-chain in front of a big-step trace.  Each τ-step turns
  -- into one `bTau` constructor, leaving the visible-label list `s`
  -- unchanged.
  τ*-prepend-bigstep : ∀ {t t' t'' : ITree E I R} {s : List (Event√ E R)}
                     → t ─[τ*]─► t'
                     → t' ═⟨ s ⟩═► t''
                     → t ═⟨ s ⟩═► t''
  τ*-prepend-bigstep τ*-zero       bs = bs
  τ*-prepend-bigstep (τ*-step s p) bs = bTau s (τ*-prepend-bigstep p bs)

  -- `deadlock` (force = vis (λ _ _ → nothing)) admits no LTS transitions
  -- at all.  Used to discharge the `bStep (sRet _) _` continuation in
  -- `lift-bigstep`: after a √ event the residual must be `bNil`.
  deadlock-no-step : ∀ {l : Label E R} {t' : ITree E I R}
                   → (deadlock {E = E} {I = I} {R = R}) ─[ l ]─► t' → ⊥
  deadlock-no-step (sRet ())
  deadlock-no-step (sSil ())
  deadlock-no-step (sVis refl ())
  deadlock-no-step (sNdbr () _)

  -----------------------------------------------------------------------------------------
  -- The core lifting lemma.  Lift a big-step `t ═⟨ s ⟩═► t'` along a
  -- bisim `t ≈ u` to a matching `u ═⟨ s ⟩═► u'` with `t' ≈ u'`.  Three
  -- cases on the big-step constructor; in the visible-step case we also
  -- split on whether the event is `evl _` (handled by `on-vis`) or `√ x`
  -- (handled by `on-ret`).
  lift-bigstep : ∀ {t t' u : ITree E I R} {s : List (Event√ E R)}
               → t ═⟨ s ⟩═► t'
               → DRWbisim _≡_ t u
               → Σ[ u' ∈ ITree E I R ]
                 ( u ═⟨ s ⟩═► u' × DRWbisim _≡_ t' u')
  -- bNil: trivial; u' = u, with `bNil` on the matching side.
  lift-bigstep bNil bisim = _ , bNil , bisim
  -- bTau: lift the τ-step via `on-tau`, then recurse.  The matching
  -- side gets a τ*-prefix (zero or more `bTau` constructors).
  lift-bigstep (bTau step rest) bisim
    with bisim .DRWbisim.fwd .DRWSimF.on-tau step
  ... | umid , weak-τ chain , bisim-mid
    with lift-bigstep rest bisim-mid
  ... | u' , rest-u , bisim-fin =
        u' , τ*-prepend-bigstep chain rest-u , bisim-fin
  -- bStep / sVis: lift via `on-vis` to a weak visible step
  --   u ─[τ*]─► u-pre ─[ev (evl _)]─► u-mid ─[τ*]─► umid
  -- and recurse on the residual.
  lift-bigstep (bStep (sVis force-eq f-eq) rest) bisim
    with bisim .DRWbisim.fwd .DRWSimF.on-vis (sVis force-eq f-eq)
  ... | umid , weak-ev pre vis-step post , bisim-mid
    with lift-bigstep rest bisim-mid
  ... | u' , rest-u , bisim-fin =
        u' ,
        τ*-prepend-bigstep pre
          (bStep vis-step (τ*-prepend-bigstep post rest-u)) ,
        bisim-fin
  -- bStep / sMixVis: a visible event from a mix node. Lift via `on-vis`
  -- exactly as for sVis.
  lift-bigstep (bStep (sMixVis force-eq f-eq) rest) bisim
    with bisim .DRWbisim.fwd .DRWSimF.on-vis (sMixVis force-eq f-eq)
  ... | umid , weak-ev pre vis-step post , bisim-mid
    with lift-bigstep rest bisim-mid
  ... | u' , rest-u , bisim-fin =
        u' ,
        τ*-prepend-bigstep pre
          (bStep vis-step (τ*-prepend-bigstep post rest-u)) ,
        bisim-fin
  -- bStep / sRet: a √ x event.  By sRet, `force t ≡ ret x` and the
  -- successor is `deadlock`, which has no transitions, so the residual
  -- big-step is forced to be `bNil`.  Use `on-ret` to lift to a τ*-chain
  -- ending in a ret-state, then perform `sRet refl` for the matching
  -- √ x step.
  lift-bigstep (bStep (sRet eq) bNil) bisim
    with bisim .DRWbisim.fwd .DRWSimF.on-ret eq
  ... | upre , r' , weak-τ chain , force-upre-eq , refl =
        deadlock ,
        τ*-prepend-bigstep chain (bStep (sRet force-upre-eq) bNil) ,
        DRWbisimEquiv.drwbisim-refl ≡-equiv deadlock
  -- The other residual constructors discharge via `deadlock-no-step`.
  lift-bigstep (bStep (sRet _) (bTau step _)) _ =
        ⊥-elim (deadlock-no-step step)
  lift-bigstep (bStep (sRet _) (bStep step _)) _ =
        ⊥-elim (deadlock-no-step step)

  -----------------------------------------------------------------------------------------
  -- Trace preservation
  --
  --   t ≈ u  ⇒  ∀ s.  traces t s  ⇒  traces u s
  --
  -- Direct corollary of `lift-bigstep` (we throw away the residual
  -- bisim witness).
  traces-preserved : ∀ {t u : ITree E I R} {s : List (Event√ E R)}
                   → DRWbisim _≡_ t u
                   → traces t s
                   → traces u s
  traces-preserved bisim (t' , bigstep)
    with lift-bigstep bigstep bisim
  ... | u' , u-bigstep , _ = u' , u-bigstep

  -----------------------------------------------------------------------------------------
  -- Divergence preservation
  --
  --   t ≈ u  ⇒  ∀ s.  divergences t s  ⇒  divergences u s
  --
  -- Lift the trace prefix via `lift-bigstep`, then carry the divergent
  -- witness across the resulting bisim using `sim-div-preserved`.
  divergences-preserved : ∀ {t u : ITree E I R} {s : List (Event√ E R)}
                        → DRWbisim _≡_ t u
                        → divergences t s
                        → divergences u s
  divergences-preserved bisim div
    with lift-bigstep (div .IsDivergence.reach) bisim
  ... | u' , u-reach , bisim-end = record
          { prefix  = div .IsDivergence.prefix
          ; suffix  = div .IsDivergence.suffix
          ; split   = div .IsDivergence.split
          ; witness = u'
          ; reach   = u-reach
          ; divwit  = sim-div-preserved (div .IsDivergence.divwit) bisim-end
          }

  -----------------------------------------------------------------------------------------
  -- Refusal preservation along bisim
  --
  --   t' ref B  ∧  t' ≈ u'  ⇒  ∃ u'' .  u' ─[τ*]─► u''  ×  u'' ref B
  --
  -- Two cases of `_ref_`:
  --
  --   • `ref-tick` (t' ─[ev (√ x)]─► _, x ∉ B): direct via `on-ret` —
  --     u' has a τ*-chain to a ret-state on r' with x ≡ r', and that
  --     ret-state can fire √ x (= √ r') to deadlock.  No `B`-event
  --     constraint to discharge.
  --
  --   • `ref-stable` (t' is vis-shaped, refuses every e ∈ B): we walk
  --     the τ-structure of `u'` until we hit a `vis`-state.  Each τ-step
  --     of `u'` lands at a state that is *still* bisim-related to `t'`
  --     (because `t'` is stable, so the matching weak-τ chain on the
  --     `t'` side must be empty).  Termination is justified by
  --     non-divergence of `u'` (inherited from `t'` via DRWbisim being
  --     divergence-respecting).  We reify this as an inductive accessibility
  --     predicate `τ-Acc u'` and recurse structurally on its acc-subterm.
  --     The bridge `τ-Acc-from-stable-bisim` is *proved* constructively up
  --     to the single isolated classical principle `¬-divergent→τ-Acc`
  --     (bar induction / double-negation elimination over the coinductive
  --     `Divergent` predicate — not provable in plain MLTT).  The stable
  --     derivative refuses `B` because any `u'' ─[ev e]─► _` would, by bwd
  --     bisim, induce a weak `t' ─[ev e]─► _`, contradicting `t' ref B` at
  --     `e ∈ B`.

  -- Inductive accessibility along τ-steps.  `τ-Acc t` asserts that every
  -- τ-descent from `t` is finite — i.e., the τ-tree of `t` is well-founded.
  -- Used to make `refuse-stabilise` structurally terminating.
  data τ-Acc (t : ITree E I R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
    τ-acc : (∀ {t' : ITree E I R} → t ─[ Label.τ ]─► t' → τ-Acc t') → τ-Acc t

  -- A stable tree (force ≡ vis _) makes no τ-step, so it is trivially τ-Acc.
  stable→τ-Acc : ∀ {t : ITree E I R}
                  {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
              → ITree.force t ≡ vis f
              → τ-Acc t
  stable→τ-Acc force-t-vis = τ-acc λ step →
    ⊥-elim (τ-from-force-vis-impossible force-t-vis step)

  -- A divergent tree cannot be stable: its first τ-step (sSil/sNdbr/sMixSlide)
  -- exposes `force ∈ {sil, ndbr, mix}` which clashes with `force ≡ vis _`.
  -- This is the constructive half of the "stable ⇒ ¬ Divergent" argument.
  divergent→not-stable : ∀ {t : ITree E I R}
                          {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
                      → Divergent t
                      → ITree.force t ≡ vis f
                      → ⊥
  divergent→not-stable d eq with d .Divergent.step
  ... | sSil eq'      = vis≢sil  (trans (sym eq) eq')
  ... | sNdbr eq' _   = vis≢ndbr (trans (sym eq) eq')
  ... | sMixSlide eq' = vis≢mix  (trans (sym eq) eq')

  -- Constructive: `t` stable + `t ≈ u` ⇒ `u` is not divergent.
  -- Proof: any divergence of `u` is transported to a divergence of `t`
  -- by `bisim.bwd.on-div`, which then contradicts stability of `t`.
  stable-bisim→¬-divergent :
    ∀ {t u : ITree E I R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
    → ITree.force t ≡ vis f
    → DRWbisim _≡_ t u
    → Divergent u → ⊥
  stable-bisim→¬-divergent force-t-vis bisim div-u =
    divergent→not-stable (bisim .DRWbisim.bwd .DRWSimF.on-div div-u) force-t-vis

  -- Classical principle: a non-divergent tree is τ-Acc.  This is the only
  -- non-constructive step.  Going from `¬ Divergent u` (a negated coinductive
  -- predicate, computationally just a function to `⊥`) to the inductive
  -- accessibility witness `τ-Acc u` requires bar induction / double-negation
  -- elimination — not provable in plain MLTT.  Postulating it is standard
  -- (it is a known classically-true principle, sound to assume).
  postulate
    ¬-divergent→τ-Acc :
      ∀ {t : ITree E I R} → (Divergent t → ⊥) → τ-Acc t

  -- The full bridge used by `refuse-stabilise`, now constructive modulo
  -- the single isolated classical principle above.
  τ-Acc-from-stable-bisim :
    ∀ {t u : ITree E I R}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
    → ITree.force t ≡ vis f
    → DRWbisim _≡_ t u
    → τ-Acc u
  τ-Acc-from-stable-bisim force-t-vis bisim =
    ¬-divergent→τ-Acc (stable-bisim→¬-divergent force-t-vis bisim)

  -- A `─[τ*]─►`-chain out of a stable (vis-shaped) tree must be empty.
  stable-τ*-id : ∀ {t t' : ITree E I R} {f}
               → ITree.force t ≡ vis f
               → t ─[τ*]─► t' → t' ≡ t
  stable-τ*-id eq τ*-zero = refl
  stable-τ*-id eq (τ*-step (sSil eq')   _) = case trans (sym eq) eq' of λ ()
  stable-τ*-id eq (τ*-step (sNdbr eq' _) _) = case trans (sym eq) eq' of λ ()
  stable-τ*-id eq (τ*-step (sMixSlide eq') _) = case trans (sym eq) eq' of λ ()

  -- `force t ≡ vis _` ⇒ `isStable t`.  `isStable` is defined by a
  -- with-clause on `force`, so we abstract over `force t` and the
  -- propositional equation simultaneously to make Agda reduce.
  force-vis→isStable : ∀ {t : ITree E I R} {f}
                     → ITree.force t ≡ vis f
                     → isStable t
  force-vis→isStable {t} eq with ITree.force t | eq
  ... | vis _        | _   = tt₀
  ... | ret _        | ()
  ... | sil _        | ()
  ... | ndbr _ _ _ _ | ()
  ... | mix _ _      | ()

  -- Witness extraction from `Is-just`: if `Is-just m` holds, then
  -- `m ≡ just x` for some explicit `x`.
  is-just-witness : ∀ {ℓ' : Level} {A : Set ℓ'} {m : Maybe A}
                  → Is-just m → Σ[ x ∈ A ] (m ≡ just x)
  is-just-witness {m = just x}  _  = x , refl
  is-just-witness {m = nothing} ()

  -- A stable tree's bisim partner cannot be in `ret`-shape: bwd `on-ret`
  -- would force a τ*-chain on the stable side ending at `ret`, but the
  -- stable side admits no τ-step, hence its only τ*-chain is the empty
  -- one — and that ends at `vis`, not `ret`.
  ret-not-bisim-vis : ∀ {t u : ITree E I R} {r f}
                    → ITree.force t ≡ vis f
                    → ITree.force u ≡ ret r
                    → DRWbisim _≡_ t u
                    → ⊥
  ret-not-bisim-vis force-t-vis force-u-ret bisim
    with bisim .DRWbisim.bwd .DRWSimF.on-ret force-u-ret
  ... | t' , _ , weak-τ chain , force-t'-ret , _
    with stable-τ*-id force-t-vis chain
  ... | refl = case trans (sym force-t-vis) force-t'-ret of λ ()

  -- If `t` is stable and refuses `B`, then any stable bisim partner of
  -- `t` also refuses `B` (events forbidden at `t` are forbidden at
  -- partners — direct via bwd `on-vis`/`on-ret`).
  bisim-stable-refuses : ∀ {ℓB} {t u : ITree E I R} {B : Event√ E R → Set ℓB}
                            {ft fU}
                       → ITree.force t ≡ vis ft
                       → ITree.force u ≡ vis fU
                       → t ref B
                       → DRWbisim _≡_ t u
                       → u ref B
  bisim-stable-refuses
      {t = t} {u = u} {B = B}
      force-t-vis force-u-vis (ref-tick {x = x} (sRet force-t-ret) _) _ =
    -- ref-tick on `t` would force `force t ≡ ret x`, but `t` is vis.
    case trans (sym force-t-vis) force-t-ret of λ ()
  bisim-stable-refuses
      {t = t} {u = u} {B = B}
      force-t-vis force-u-vis (ref-stable {P = .t} _ t-refuses) bisim =
    ref-stable {P = u} (force-vis→isStable {t = u} force-u-vis) u-refuses
    where
      u-refuses : ∀ e → B e → ∀ {Q : ITree E I R} → ¬ (u ─[ ev e ]─► Q)
      -- u-step via sRet would need `force u ≡ ret _`, contradicting vis.
      u-refuses e Be (sRet force-u-ret) =
            case trans (sym force-u-vis) force-u-ret of λ ()
      -- u-step via sVis: bwd lifts to a weak-vis transition out of `t`.
      -- The τ*-prefix on `t` must be empty (stable), so it reduces to a
      -- direct sVis-step on `t` with the same event — discharged by
      -- `t-refuses`.
      u-refuses e Be (sVis force-eq f-eq)
        with bisim .DRWbisim.bwd .DRWSimF.on-vis (sVis force-eq f-eq)
      ... | _ , weak-ev pre vis-step _ , _
        with stable-τ*-id force-t-vis pre
      ... | refl = t-refuses e Be vis-step
      -- u-step via sMixVis: u must in fact be a mix-node. The bwd-vis lift
      -- still applies, since the LTS only cares about the produced label.
      u-refuses e Be (sMixVis force-eq f-eq)
        with bisim .DRWbisim.bwd .DRWSimF.on-vis (sMixVis force-eq f-eq)
      ... | _ , weak-ev pre vis-step _ , _
        with stable-τ*-id force-t-vis pre
      ... | refl = t-refuses e Be vis-step

  -- Main recursion.  Walks the τ-structure of `u`; each iteration
  -- discharges one of (vis | ret | sil | ndbr | mix).  The vis case is the
  -- base — return `u` and discharge refusal via `bisim-stable-refuses`.
  -- The ret case is impossible (`ret-not-bisim-vis`).  The sil / ndbr /
  -- mix-slide cases recurse on the τ-derivative, prepending the step to
  -- the output τ*-chain.
  --
  -- Termination: the recursion is structural on the `τ-Acc u` argument.
  -- Each recursive call descends along one τ-step, consuming one layer
  -- of `τ-acc`.  The wrapper `ref-preserved` constructs `τ-Acc u` from
  -- `t` stable + `t ≈ u` via `τ-Acc-from-stable-bisim`, which is proved
  -- from the single classical postulate `¬-divergent→τ-Acc`.
  refuse-stabilise :
    ∀ {ℓB} {t u : ITree E I R} {B : Event√ E R → Set ℓB}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
    → DRWbisim _≡_ t u
    → ITree.force t ≡ vis f
    → t ref B
    → τ-Acc u
    → Σ[ u' ∈ ITree E I R ] (u ─[τ*]─► u' × u' ref B)
  refuse-stabilise {t = t} {u = u} bisim force-t-vis tref (τ-acc acc-f)
    with ITree.force u | inspect ITree.force u
  -- Base case: u itself is stable.  Refusal of B transfers via
  -- `bisim-stable-refuses`.
  ... | vis fU | [ force-u-eq ] =
        u , τ*-zero , bisim-stable-refuses force-t-vis force-u-eq tref bisim
  -- Impossible: u in ret-shape contradicts t in vis-shape under bisim.
  ... | ret r  | [ force-u-eq ] =
        ⊥-elim (ret-not-bisim-vis force-t-vis force-u-eq bisim)
  -- Sil-step: take one τ-step into u', re-establish `t ≈ u'` via bwd
  -- bisim (the matching τ*-chain on t is empty since t is stable),
  -- recurse on the smaller `τ-Acc u'`, prepend.
  ... | sil u' | [ force-u-eq ] =
        let step : u ─[ Label.τ ]─► u'
            step = sSil force-u-eq
        in case bisim .DRWbisim.bwd .DRWSimF.on-tau step of λ where
             (t' , weak-τ chain-t , bisim-u'-t') →
               case stable-τ*-id force-t-vis chain-t of λ where
                 refl →
                   let bisim-t-u' = DRWbisimEquiv.drwbisim-sym ≡-equiv bisim-u'-t'
                       u'' , chain-u' , ref-u'' =
                             refuse-stabilise bisim-t-u' force-t-vis tref (acc-f step)
                   in u'' , τ*-step step chain-u' , ref-u''
  -- Ndbr-step: pick the witnessed branch (wp gives Is-just (fU wi wa)),
  -- step into u-branch, then recurse like the sil case.
  ... | ndbr fU wi wa wp | [ force-u-eq ] =
        let u-branch , wp-eq = is-just-witness {m = fU wi wa} wp
            step : u ─[ Label.τ ]─► u-branch
            step = sNdbr {p = u} {f = fU} {wi = wi} {wa = wa} {prf = wp}
                         {i = wi} {a = wa} force-u-eq wp-eq
        in case bisim .DRWbisim.bwd .DRWSimF.on-tau step of λ where
             (t' , weak-τ chain-t , bisim-ub-t') →
               case stable-τ*-id force-t-vis chain-t of λ where
                 refl →
                   let bisim-t-ub = DRWbisimEquiv.drwbisim-sym ≡-equiv bisim-ub-t'
                       u'' , chain-ub , ref-u'' =
                             refuse-stabilise bisim-t-ub force-t-vis tref (acc-f step)
                   in u'' , τ*-step step chain-ub , ref-u''
  -- Mix-slide step: take the silent timeout τ to Qt, then recurse on Qt.
  ... | mix fU Qt | [ force-u-eq ] =
        let step : u ─[ Label.τ ]─► Qt
            step = sMixSlide {p = u} {f = fU} {Qt = Qt} force-u-eq
        in case bisim .DRWbisim.bwd .DRWSimF.on-tau step of λ where
             (t' , weak-τ chain-t , bisim-Qt-t') →
               case stable-τ*-id force-t-vis chain-t of λ where
                 refl →
                   let bisim-t-Qt = DRWbisimEquiv.drwbisim-sym ≡-equiv bisim-Qt-t'
                       u'' , chain-Qt , ref-u'' =
                             refuse-stabilise bisim-t-Qt force-t-vis tref (acc-f step)
                   in u'' , τ*-step step chain-Qt , ref-u''

{-
  refuse-stabilise-aux :
    ∀ {ℓB} {t u : ITree E I R} {B : Event√ E R → Set ℓB}
      {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
    → DRWbisim _≡_ t u
    → ITree.force t ≡ vis f
    → t ref B
    → Σ[ u' ∈ ITree E I R ](u ─[τ*]─► u' × u' ref B)
  refuse-stabilise-aux {t = t} {u = u} bisim force-t-vis tref
    with ITree.force u in u-eq | inspect ITree.force u
  -- Base case: u itself is stable.  Refusal of B transfers via
  -- `bisim-stable-refuses`.
  ... | vis fU | [ force-u-eq ] =
        u , τ*-zero , bisim-stable-refuses force-t-vis force-u-eq tref bisim
  -- Impossible: u in ret-shape contradicts t in vis-shape under bisim.
  ... | ret r  | [ force-u-eq ] =
        ⊥-elim (ret-not-bisim-vis force-t-vis force-u-eq bisim)
  -- Sil-step: take one τ-step into u', re-establish `t ≈ u'` via bwd
  -- bisim (the matching τ*-chain on t is empty since t is stable),
  -- recurse, prepend.
  ... | sil u' | [ force-u-eq ] =
        let step : u ─[ Label.τ ]─► u'
            step = sSil force-u-eq
        in case bisim .DRWbisim.bwd .DRWSimF.on-tau step of λ where
             (t' , weak-τ chain-t , bisim-u'-t') →
               case stable-τ*-id force-t-vis chain-t of λ where
                 refl →
                   let bisim-t-u' = DRWbisimEquiv.drwbisim-sym ≡-equiv bisim-u'-t'
                       u'' , chain-u' , ref-u'' =
                             refuse-stabilise-aux bisim-t-u' force-t-vis tref
                   in u'' , τ*-step step chain-u' , ref-u''
  -- Ndbr-step: pick the witnessed branch (wp gives Is-just (fU wi wa)),
  -- step into u-branch, then recurse like the sil case.
  ... | ndbr fU wi wa wp | [ force-u-eq ] = {!!}
      {-
        let u-branch , wp-eq = is-just-witness {m = fU wi wa} wp
            step : u ─[ Label.τ ]─► u-branch
            step = sNdbr {p = u} {f = fU} {wi = wi} {wa = wa} {prf = wp}
                         {i = wi} {a = wa} force-u-eq wp-eq
        in case bisim .DRWbisim.bwd .DRWSimF.on-tau step of λ where
             (t' , weak-τ chain-t , bisim-ub-t') →
               case stable-τ*-id force-t-vis chain-t of λ where
                 refl →
                   let bisim-t-ub = DRWbisimEquiv.drwbisim-sym ≡-equiv bisim-ub-t'
                       u'' , chain-ub , ref-u'' =
                             refuse-stabilise-aux bisim-t-ub force-t-vis tref
                   in u'' , τ*-step step chain-ub , ref-u''
      -}
  -- Mix-slide step: structurally analogous to the sil case but on Qt.
  -- Left as a hole, consistent with the ndbr hole above — these in-progress
  -- structural variants share the same termination obstacle.
  ... | mix fU Qt | [ force-u-eq ] = {!!}

-}

  -- ref-tick lifting: P ─[ev (√ x)]─► _ with ¬ B (√ x).  Use on-ret to
  -- get a τ*-chain in u to a ret-state on r' (with x ≡ r' under the
  -- propositional return-relation), then fire √ x there.
  refuse-tick-lift : ∀ {ℓB} {t u Q : ITree E I R} {x : R}
                       {B : Event√ E R → Set ℓB}
                   → DRWbisim _≡_ t u
                   → t ─[ ev (√ x) ]─► Q
                   → ¬ B (√ x)
                   → Σ[ u' ∈ ITree E I R ] (u ─[τ*]─► u' × u' ref B)
  refuse-tick-lift bisim (sRet eq) ¬Bx
    with bisim .DRWbisim.fwd .DRWSimF.on-ret eq
  ... | upre , r' , weak-τ chain , force-upre-eq , refl =
        upre , chain , ref-tick (sRet force-upre-eq) ¬Bx

  -- A stable tree's force is vis-shaped (extracted as a propositional
  -- equality so we can hand it off to `refuse-stabilise`).
  isStable→force-vis : ∀ {t : ITree E I R}
                     → isStable t
                     → Σ[ f ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))) ]
                       ITree.force t ≡ vis f
  isStable→force-vis {t} st with ITree.force t
  ... | vis f        = f , refl

  -- Top-level refusal lifting along bisim.
  ref-preserved : ∀ {ℓB} {t u : ITree E I R} {B : Event√ E R → Set ℓB}
                → DRWbisim _≡_ t u
                → t ref B
                → Σ[ u' ∈ ITree E I R ] (u ─[τ*]─► u' × u' ref B)
  ref-preserved bisim (ref-tick step ¬Bx) =
        refuse-tick-lift bisim step ¬Bx
  ref-preserved {t = t} {u = u} bisim (ref-stable {P = .t} stable refuses)
    with isStable→force-vis {t = t} stable
  ... | _ , force-eq =
        refuse-stabilise bisim force-eq (ref-stable {P = t} stable refuses)
                         (τ-Acc-from-stable-bisim force-eq bisim)

  -----------------------------------------------------------------------------------------
  -- Failure preservation
  --
  --   t ≈ u  ⇒  ∀ s B.  failures t s B  ⇒  failures u s B
  --
  -- Lift the trace prefix via `lift-bigstep` to obtain `u ═⟨ s ⟩═► u'`
  -- with `t' ≈ u'`, then lift the refusal via `ref-preserved` to get
  -- `u' ─[τ*]─► u''` refusing `B`.  Append the τ*-chain to the trace
  -- (via `τ*-prepend-bigstep` on a `bNil`-anchored extension): the
  -- visible label list stays `s` because each step is a `bTau`.
  bigstep-append-τ* : ∀ {t t' t'' : ITree E I R} {s : List (Event√ E R)}
                    → t ═⟨ s ⟩═► t'
                    → t' ─[τ*]─► t''
                    → t ═⟨ s ⟩═► t''
  bigstep-append-τ* bNil chain = τ*-prepend-bigstep chain bNil
  bigstep-append-τ* (bTau step rest) chain = bTau step (bigstep-append-τ* rest chain)
  bigstep-append-τ* (bStep step rest) chain = bStep step (bigstep-append-τ* rest chain)

  failures-preserved : ∀ {ℓB} {t u : ITree E I R} {s : List (Event√ E R)}
                         {B : Event√ E R → Set ℓB}
                     → DRWbisim _≡_ t u
                     → failures t s B
                     → failures u s B
  failures-preserved bisim (t' , bigstep , refusal)
    with lift-bigstep bigstep bisim
  ... | u' , u-bigstep , bisim-end
    with ref-preserved bisim-end refusal
  ... | u'' , chain , refusal-u =
        u'' , bigstep-append-τ* u-bigstep chain , refusal-u

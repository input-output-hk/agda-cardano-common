{-# OPTIONS --guardedness #-}

-- hide-slide (U13.3), MENU version over an arbitrary prefix-choice `pchoice v`
-- composed with a SLIDE/timeout to `Q`:
--
--   ((?x:A→P) ▷ Q) ∖ X  ≈FD  (?x:(A∖X)→(P∖X)) ▷ ⨅({Q∖X} ∪ { P[a]∖X | a∈X∩A })
--                      =  RPrefix v X  ▷  GChoiceS v Q X
--
-- This is Roscoe's hide-slide law: hiding distributes over the slide, the surviving
-- (non-hidden) menu remains a prefix choice that slides over the internal choice
-- ⨅(...), whose τ-branches are (tag0) the slide's TIMEOUT to Q∖X and (tag1) the
-- newly-hidden events P[a]∖X.  Like the full hide-step (HideStepFull) this consumes a
-- step but yields a τ, so it is a failures-divergences law, NOT a bisimulation.
-- Proof = two ≈FD hops (mirroring HideStepFull):
--
--   1. (S ∖ X)  ∼  fused = react V τc      where  S  = (pchoice v) ▷ Q,
--                                                  V  = hide-hVis X (react v ∅t),
--                                                  τc = hide-hTau X (react v τcS),
--                                                  τcS = ▷-slide (react v ∅t) Q.
--      The τ-maps are LITERALLY identical (both `hide-hTau X (react v τcS)`), but the
--      visible maps `hide-hVis X (react v τcS)` (of S ∖ X) and `hide-hVis X (react v ∅t)`
--      (of fused = the RPrefix one) are equal only POINTWISE — `hide-hVis` guards on
--      `dec at a` BEFORE reading `viewV`, so the two maps are NOT definitionally equal,
--      only extensionally (see hVis-eq).  Hence hop 1 is a genuine strong bisimulation
--      (re-emitting each step, rewriting the visible offer equation through hVis-eq),
--      not a force-equality; it is then lifted to ≈FD.
--   2. slide-fuse-FD : RPrefix v X ▷ GChoiceS v Q X  ≈FD  react V τc.
--
-- UNLIKE HideStepFull, the internal-choice operand here is ALWAYS unstable with NO
-- side-condition: the slide's TIMEOUT always provides GChoiceS v Q X ─[τ]→ (Q ∖ X).

open import Level using (Level)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module CSP.Laws.FD.HideSlide {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open EventSet
open import CSP.Guarded  E-≟
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_≈FD_; ≈FD-setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Traces.TraceLawsHide E-≟ using (Hide-τ)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (▷-timeout)
open import CSP.Laws.FD.SlideFuse E-≟ using (slide-fuse-FD)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- the slide-variant guarded internal choice  ⨅({Q∖X} ∪ { P[a]∖X | a∈X∩A })  =  τ part of (S ∖ X)
GChoiceS : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
           (Q : PTree E (ExtI E) R) (X : EventSet) → PTree E (ExtI E) R
GChoiceS v Q X = ptree (react ∅v (hide-hTau X (react v (▷-slide (react v ∅t) Q))))

-- `(S ∖ X)` and `GChoiceS v Q X` carry the SAME τ-map (hide-hTau X (react v τcS)),
-- differing only in their visible part — so a τ of the former is a τ of the latter.
hide-τ→gchoiceS-τ : {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                    {Q : PTree E (ExtI E) R} {X : EventSet} {M : PTree E (ExtI E) R}
                  → (((pchoice v) ▷ Q) ∖ X) ─[ τ ]─► M → (GChoiceS v Q X) ─[ τ ]─► M
hide-τ→gchoiceS-τ (sSil ())
hide-τ→gchoiceS-τ (sTau {i = i} {a = a} refl br) = sTau {i = i} {a = a} refl br

module _ (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         (Q : PTree E (ExtI E) R)
         (X : EventSet) where

  private
    S : PTree E (ExtI E) R
    S = (pchoice v) ▷ Q

    -- the fused react node both sides agree on  (τcS = ▷-slide (react v ∅t) Q inlined).
    -- Visible map is the RPrefix one (`hide-hVis X (react v ∅t)`): it agrees with
    -- (S ∖ X)'s visible map `hide-hVis X (react v τcS)` ONLY extensionally (hide-hVis
    -- guards on `dec at a` before reading `viewV`, so the two are NOT definitionally
    -- equal as maps — see hVis-eq) — hence hop 1 is a real bisim, not a force-eq.
    fused : PTree E (ExtI E) R
    fused = ptree (react (hide-hVis X (react v ∅t))
                         (hide-hTau X (react v (▷-slide (react v ∅t) Q))))

    -- the two visible maps agree pointwise (both guard on `dec at a` then read `v`)
    hVis-eq : (at : AnyTypes E) (a : proj₁ at)
            → hide-hVis X (react v (▷-slide (react v ∅t) Q)) at a
            ≡ hide-hVis X (react v ∅t) at a
    hVis-eq at a with X .dec at a
    ... | yes _ = refl
    ... | no  _ = refl

    -- (S ∖ X) ─[ev]→ M  ⇒  fused ─[ev]→ M   (rewrite the offer eqn across hVis-eq)
    SX→fused-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
                → (S ∖ X) ─[ ev l ]─► M → fused ─[ ev l ]─► M
    SX→fused-ev (sRet ())
    SX→fused-ev (sVis {at = at} {a = a} refl br) =
      sVis {at = at} {a = a} refl (trans (sym (hVis-eq at a)) br)

    fused→SX-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
                → fused ─[ ev l ]─► M → (S ∖ X) ─[ ev l ]─► M
    fused→SX-ev (sRet ())
    fused→SX-ev (sVis {at = at} {a = a} refl br) =
      sVis {at = at} {a = a} refl (trans (hVis-eq at a) br)

    -- τ-maps are literally identical, so τ-steps convert by re-emitting at the same index
    SX→fused-τ : {M : PTree E (ExtI E) R} → (S ∖ X) ─[ τ ]─► M → fused ─[ τ ]─► M
    SX→fused-τ (sSil ())
    SX→fused-τ (sTau {i = i} {a = a} refl br) = sTau {i = i} {a = a} refl br

    fused→SX-τ : {M : PTree E (ExtI E) R} → fused ─[ τ ]─► M → (S ∖ X) ─[ τ ]─► M
    fused→SX-τ (sSil ())
    fused→SX-τ (sTau {i = i} {a = a} refl br) = sTau {i = i} {a = a} refl br

    -- hop 1: (S ∖ X) and fused are strongly bisimilar (visible maps agree pointwise)
    SX∼fused : (S ∖ X) ∼ fused
    SX∼fused .Sbisim.fwd .SSimF.on-ev  step = _ , SX→fused-ev step , sbisim-refl _
    SX∼fused .Sbisim.fwd .SSimF.on-tau step = _ , SX→fused-τ  step , sbisim-refl _
    SX∼fused .Sbisim.bwd .SSimF.on-ev  step = _ , fused→SX-ev step , sbisim-refl _
    SX∼fused .Sbisim.bwd .SSimF.on-tau step = _ , fused→SX-τ  step , sbisim-refl _

    -- the slide's TIMEOUT makes GChoiceS unstable — NO side-condition needed
    qτ : Σ[ M ∈ PTree E (ExtI E) R ] (GChoiceS v Q X ─[ τ ]─► M)
    qτ = (Q ∖ X)
       , hide-τ→gchoiceS-τ (Hide-τ X S (▷-timeout (pchoice v) Q refl tt))

    -- lift hop-1 bisim to ≈FD
    fuse-FD : (S ∖ X) ≈FD fused
    fuse-FD = drbisim→≈FD (sbisim→drbisim SX∼fused)

    -- hop 2: the slide fuses (FD-direct core)
    slidefuse-FD : (RPrefix v X ▷ GChoiceS v Q X) ≈FD fused
    slidefuse-FD = slide-fuse-FD (hide-hVis X (react v ∅t))
                                 (hide-hTau X (react v (▷-slide (react v ∅t) Q))) qτ

  -- ((?x:A→P) ▷ Q) ∖ X  ≈FD  (?x:(A∖X)→(P∖X)) ▷ ⨅({Q∖X} ∪ { P[a]∖X | a∈X∩A })
  hide-slide-FD : (((pchoice v) ▷ Q) ∖ X) ≈FD (RPrefix v X ▷ GChoiceS v Q X)
  hide-slide-FD = begin
    ((pchoice v) ▷ Q) ∖ X          ≈⟨ fuse-FD ⟩
    fused                           ≈⟨ slidefuse-FD ⟨
    RPrefix v X ▷ GChoiceS v Q X   ∎
    where open SetoidReasoning (≈FD-setoid R)

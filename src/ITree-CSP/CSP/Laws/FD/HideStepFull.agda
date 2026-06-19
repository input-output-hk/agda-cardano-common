{-# OPTIONS --guardedness #-}

-- Full hide-step (T3.6 / U5.6, the A∩X≠∅ case), MENU version over an arbitrary
-- prefix-choice `pchoice v` (the menu `?x:A→P`, A = whatever v offers, multi-channel):
--
--   (?x:A→P) ∖ X  ≈FD  (?x:(A∖X)→(P∖X)) ▷ ⨅{ P a∖X | a∈A, a∈X }
--               =  RPrefix v X  ▷  GChoice v X
--
-- The tex flags this as "unlike the other step laws": it consumes one step but yields a
-- τ (the slide), so it is a failures-divergences law, NOT a bisimulation (the slide-τ
-- to the internal choice discards the surviving offers).  Proof = two ≈FD hops:
--
--   1. (pchoice v) ∖ X  ∼  react V τc      where  V  = hide-hVis X (react v ∅t)
--                                                 τc = hide-hTau X (react v ∅t).
--      These share their force DEFINITIONALLY — `(pchoice v) ∖ X` IS forced to react V τc,
--      and the RPrefix/GChoice operands are built from those very maps — so this is a
--      one-line force-equality bisimulation; NO connecting step-by-step bisim is needed.
--   2. slide-fuse-FD : RPrefix v X ▷ GChoice v X  ≈FD  react V τc      (the FD-direct core).
--
-- Requires the menu to offer at least one HIDDEN event (a witness off₀ : v (B,e₀) a₀ ≡
-- just M₀ with a₀∈X) so the internal choice is unstable — exactly the A∩X≠∅ side-condition.

open import Level using (Level)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module CSP.Laws.FD.HideStepFull {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import CSP.Guarded  E-≟
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_≈FD_; ≈FD-setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Traces.TraceLawsHide E-≟ using (Hide-hidden)
open import CSP.Laws.FD.SlideFuse E-≟ using (slide-fuse-FD)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- force-equal trees share outgoing steps, hence are strongly bisimilar.
retarget : {a b : PTree E (ExtI E) R} {l : Label R} {M : PTree E (ExtI E) R}
         → PTree.force a ≡ PTree.force b → a ─[ l ]─► M → b ─[ l ]─► M
retarget eq (sRet fe)    = sRet (trans (sym eq) fe)
retarget eq (sSil fe)    = sSil (trans (sym eq) fe)
retarget eq (sVis fe br) = sVis (trans (sym eq) fe) br
retarget eq (sTau fe br) = sTau (trans (sym eq) fe) br

sbisim-force-eq : {t u : PTree E (ExtI E) R} → PTree.force t ≡ PTree.force u → t ∼ u
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-ev  step = _ , retarget eq        step , sbisim-refl _
sbisim-force-eq eq .Sbisim.fwd .SSimF.on-tau step = _ , retarget eq        step , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-ev  step = _ , retarget (sym eq)  step , sbisim-refl _
sbisim-force-eq eq .Sbisim.bwd .SSimF.on-tau step = _ , retarget (sym eq)  step , sbisim-refl _

module _ (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         (X : EventSet)
         {B : Set ℓ} {e₀ : E B} {a₀ : B} {M₀ : PTree E (ExtI E) R}
         (mem₀ : EventSet.mem X (B , e₀) a₀)
         (off₀ : v (B , e₀) a₀ ≡ just M₀) where

  private
    -- the fused react node both sides agree on
    fused : PTree E (ExtI E) R
    fused = ptree (react (hide-hVis X (react v ∅t)) (hide-hTau X (react v ∅t)))

    -- the menu offers a hidden event ⇒ the internal choice GChoice v X is unstable
    qτ : Σ[ M ∈ PTree E (ExtI E) R ] (GChoice v X ─[ τ ]─► M)
    qτ = (M₀ ∖ X)
       , hide-τ→gchoice-τ
           (Hide-hidden X (pchoice v) mem₀ (sVis {at = B , e₀} {a = a₀} refl off₀))

    -- hop 1: force equality (definitional) ⇒ strong bisim ⇒ ≈FD
    fuse-FD : ((pchoice v) ∖ X) ≈FD fused
    fuse-FD = drbisim→≈FD (sbisim→drbisim (sbisim-force-eq refl))

    -- hop 2: the slide fuses (FD-direct core)
    slidefuse-FD : (RPrefix v X ▷ GChoice v X) ≈FD fused
    slidefuse-FD = slide-fuse-FD (hide-hVis X (react v ∅t)) (hide-hTau X (react v ∅t)) qτ

  -- (?x:A→P) ∖ X  ≈FD  (?x:(A∖X)→(P∖X)) ▷ ⨅{ P a∖X | a∈A∩X }
  hide-step-full-FD : ((pchoice v) ∖ X) ≈FD (RPrefix v X ▷ GChoice v X)
  hide-step-full-FD = begin
    (pchoice v) ∖ X          ≈⟨ fuse-FD ⟩
    fused                    ≈⟨ slidefuse-FD ⟨
    RPrefix v X ▷ GChoice v X ∎
    where open SetoidReasoning (≈FD-setoid R)

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Priority Law: `Pri` creates NO divergence — `divergences (Pri O P fb) ⊆
-- divergences P`.
--
-- IMPORTANT: the equality `divergences (Pri P) ≡ divergences P` is FALSE.
-- `Pri` PRUNES dominated visible offers (see CSP.Examples.PriSanity), so it can
-- prune the PATH to a divergence: with `a <ᵖ b`, `P = a→div □ b→Stop` has
-- `⟨a⟩… ∈ divergences P`, but `Pri O P fb` behaves as `b→Stop` with NO
-- divergence.  Hence only the ⊆ direction holds (Pri ADDS no divergence); the
-- reverse ⊇ fails exactly because Pri can prune away a divergent branch.
--
-- Enabling fact: every `Pri`-step's target is the prioritisation of an
-- underlying plain step of `P` (adequacy), and `∼` preserves `Diverges`
-- (`sbisim-div→`); τ-steps coincide (`τ-pri→`), visible steps of `Pri` are a
-- subset of `P`'s (`ev-pri→`).  So a divergence of `Pri O P fb` maps back along
-- the same trace to a divergence of `P`.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.List using (List)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)

open import Process_Trees

module CSP.Priority.Laws.Divergence {ℓ ℓe} {E : Set ℓ → Set ℓe} where

open PTree

open import Semantics.PriOrder          {ℓ} {ℓe} {E}
open import Semantics.LTS               {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Bisim             {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Failures          {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.FailuresDivergences {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.StrongImpliesDR   {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Deadlock          {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.DeadlockDR        {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import CSP.Priority.Base                {ℓ} {ℓe} {E}
open import CSP.Priority.Adequacy        {ℓ} {ℓe} {E}
import Semantics.PriLTS

module _ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo) where
  private
    module Spec = Semantics.PriLTS
                    {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {ℓo} {E} {ExtI E} (PriOrder.prop O)

  -- a prioritised visible step is a plain visible step
  ev-pri→ : {t t′ : PTree E (ExtI E) R} {e : Event√ R}
          → t Spec.─[ ev e ]─►ᵖ t′ → t ─[ ev e ]─► t′
  ev-pri→ (Spec.p√ st)     = st
  ev-pri→ (Spec.pMax _ st) = st
  ev-pri→ (Spec.pLo st _ _) = st

  -- CORE: `Pri` adds no divergence at the root — a divergence of `Pri O t fb`
  -- maps to one of `t` (each τ is an underlying τ of t; ∼ carries `Diverges`).
  -- Copatterns keep the corecursion guarded (under `.Diverges.rest`).
  pri-Diverges→ : {t : PTree E (ExtI E) R} {fb : FinBr t}
                → Diverges (Pri O t fb) → Diverges t
  pri-Diverges→ {fb = fb} d .Diverges.next with pri-adequacy-fwd O (Diverges.step d)
  ... | u′ , _ , _ , _ = u′
  pri-Diverges→ {fb = fb} d .Diverges.step with pri-adequacy-fwd O (Diverges.step d)
  ... | _ , _ , pstep , _ = Spec.τ-pri→ pstep
  pri-Diverges→ {fb = fb} d .Diverges.rest with pri-adequacy-fwd O (Diverges.step d)
  ... | _ , _ , _ , nx∼ = pri-Diverges→ (sbisim-div→ nx∼ (Diverges.rest d))

  -- a weak trace from ANY state ∼ to `Pri O t fb` lifts to a weak trace of `t`
  -- (the `∼` is threaded as an argument and the recursion is on the original
  -- `⟹` derivation — STRUCTURAL, so it terminates; `sbisim-trans` is inductive).
  pri-⟹∼ : ∀ {w₀ t w : PTree E (ExtI E) R} {fb : FinBr t} {s}
          → w₀ ∼ Pri O t fb → w₀ ⟹⟨ s ⟩ w
          → Σ[ w″ ∈ PTree E (ExtI E) R ] Σ[ fb″ ∈ FinBr w″ ]
              (t ⟹⟨ s ⟩ w″ × w ∼ Pri O w″ fb″)
  pri-⟹∼ {t = t} {fb = fb} w₀∼ ⟹-refl = t , fb , ⟹-refl , w₀∼
  pri-⟹∼ w₀∼ (⟹-τ step rest) with w₀∼ .Sbisim.fwd .SSimF.on-tau step
  ... | q′ , pstepPri , q∼q′ with pri-adequacy-fwd O pstepPri
  ...   | u′ , fb′ , pstep , q′∼ with pri-⟹∼ (sbisim-trans q∼q′ q′∼) rest
  ...     | w″ , fb″ , qtr , w∼ = w″ , fb″ , ⟹-τ (Spec.τ-pri→ pstep) qtr , w∼
  pri-⟹∼ w₀∼ (⟹-ev step rest) with w₀∼ .Sbisim.fwd .SSimF.on-ev step
  ... | q′ , pstepPri , q∼q′ with pri-adequacy-fwd O pstepPri
  ...   | u′ , fb′ , pstep , q′∼ with pri-⟹∼ (sbisim-trans q∼q′ q′∼) rest
  ...     | w″ , fb″ , qtr , w∼ = w″ , fb″ , ⟹-ev (ev-pri→ pstep) qtr , w∼

  -- MAIN: `divergences (Pri O P fb) ⊆ divergences P`  (Pri creates no divergence)
  pri-no-new-div : {P : PTree E (ExtI E) R} {fb : FinBr P} {s : List (Event√ R)}
                 → divergences (Pri O P fb) s → divergences P s
  pri-no-new-div {P} {fb} d with pri-⟹∼ (sbisim-refl (Pri O P fb)) (IsDivergence.reach d)
  ... | w″ , fb″ , Ptr , w∼ =
        record { prefix  = IsDivergence.prefix d
               ; suffix  = IsDivergence.suffix d
               ; split   = IsDivergence.split d
               ; witness = w″
               ; reach   = Ptr
               ; divwit  = pri-Diverges→ (sbisim-div→ w∼ (IsDivergence.divwit d)) }

  -- √-free weak trace lift (same shape as pri-⟹∼; `⟹∖√` never fires √, so only
  -- pMax/pLo visible steps occur — handled by `ev-pri→`).
  pri-⟹∖√∼ : ∀ {w₀ t w : PTree E (ExtI E) R} {fb : FinBr t} {s}
           → w₀ ∼ Pri O t fb → w₀ ⟹∖√⟨ s ⟩ w
           → Σ[ w″ ∈ PTree E (ExtI E) R ] Σ[ fb″ ∈ FinBr w″ ]
               (t ⟹∖√⟨ s ⟩ w″ × w ∼ Pri O w″ fb″)
  pri-⟹∖√∼ {t = t} {fb = fb} w₀∼ ∖√-refl = t , fb , ∖√-refl , w₀∼
  pri-⟹∖√∼ w₀∼ (∖√-τ step rest) with w₀∼ .Sbisim.fwd .SSimF.on-tau step
  ... | q′ , pstepPri , q∼q′ with pri-adequacy-fwd O pstepPri
  ...   | u′ , fb′ , pstep , q′∼ with pri-⟹∖√∼ (sbisim-trans q∼q′ q′∼) rest
  ...     | w″ , fb″ , qtr , w∼ = w″ , fb″ , ∖√-τ (Spec.τ-pri→ pstep) qtr , w∼
  pri-⟹∖√∼ w₀∼ (∖√-ev step rest) with w₀∼ .Sbisim.fwd .SSimF.on-ev step
  ... | q′ , pstepPri , q∼q′ with pri-adequacy-fwd O pstepPri
  ...   | u′ , fb′ , pstep , q′∼ with pri-⟹∖√∼ (sbisim-trans q∼q′ q′∼) rest
  ...     | w″ , fb″ , qtr , w∼ = w″ , fb″ , ∖√-ev (ev-pri→ pstep) qtr , w∼

  -- COROLLARY: `Pri` preserves divergence-freedom.
  pri-divFree : {P : PTree E (ExtI E) R} {fb : FinBr P}
              → DivergenceFree P → DivergenceFree (Pri O P fb)
  pri-divFree {P} {fb} dfP reach div-t′ with pri-⟹∖√∼ (sbisim-refl (Pri O P fb)) reach
  ... | w″ , fb″ , Preach , t′∼ = dfP Preach (pri-Diverges→ (sbisim-div→ t′∼ div-t′))

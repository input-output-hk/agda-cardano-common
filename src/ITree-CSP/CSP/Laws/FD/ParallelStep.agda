{-# OPTIONS --guardedness #-}

-- Parallel STEP law (T2.10 / U3.10, interface parallel):
--   (?x:A → P) ∥[X] (?x:B → Q) = ?x:C → R(x),
-- where C synchronises on `A` and interleaves outside `A` (sync ⇒ P∥Q; outside-`A` solo ⇒
-- P∥(prefix Q) / (prefix P)∥Q; outside-`A` both-offer ⇒ the ⊓ overlap).
--
-- In this spike a prefix-choice is `pchoice v = ptree (react v ∅t)` (stable, pure-visible),
-- and `par-pVis` IS exactly that C-merge of the two vis-maps.  So `Par (pchoice vA)
-- (pchoice vB)` BY DEFINITION forces to `react (par-pVis …) (par-pTau …)` — the same visible
-- map as `pchoice (par-pVis …)` plus a vacuous τ-part (par-pTau of two τ-free operands is
-- everywhere nothing).  Confirmed as a STRONG bisimulation (⇒ ≈FD).  Mirrors □-step-∼.

open import Level using (Level; lift)
open import Data.Maybe using (Maybe)
open import Data.Product using (_,_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Nullary using (Dec; ¬_; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Function using (case_of_)

open import Process_Trees

module CSP.Laws.FD.ParallelStep {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Mg)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD        {E = E} {I = ExtI E} using (drbisim→≈FD)

private
  variable
    ℓr ℓ₁ ℓ₂ : Level
    R  : Set ℓr
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂

-- ∥-step as a STRONG bisimulation: both sides offer exactly `par-pVis …` and have no τ.
-- on-ev rebuilds the same step (same map ⇒ same continuation); on-tau is vacuous
-- (par-pTau of two τ-free operands, resp. ∅t, is everywhere `nothing`).
Par-step-∼ : (A : EventSet) (merge : Mg R₁ R₂ R)
             (vA : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₁)))
             (vB : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₂)))
           → Par A merge (pchoice vA) (pchoice vB)
             ∼ pchoice (par-pVis A merge (react vA ∅t) (react vB ∅t) (pchoice vA) (pchoice vB))
Par-step-∼ A merge vA vB .Sbisim.fwd .SSimF.on-ev  (sVis refl br) = _ , sVis refl br , sbisim-refl _
Par-step-∼ A merge vA vB .Sbisim.fwd .SSimF.on-ev  (sRet ())
Par-step-∼ A merge vA vB .Sbisim.fwd .SSimF.on-tau (sSil ())
Par-step-∼ A merge vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , base _}            refl br) = case br of λ ()
Par-step-∼ A merge vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , fin}               refl br) = case br of λ ()
Par-step-∼ A merge vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , pair (base _) _}   refl br) = case br of λ ()
Par-step-∼ A merge vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , pair (pair _ _) _} refl br) = case br of λ ()
Par-step-∼ A merge vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , pair fin i′} {a = lift fzero , aa}           refl br) = case br of λ ()
Par-step-∼ A merge vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , pair fin i′} {a = lift (fsuc fzero) , aa}    refl br) = case br of λ ()
Par-step-∼ A merge vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , pair fin i′} {a = lift (fsuc (fsuc _)) , aa} refl br) = case br of λ ()
Par-step-∼ A merge vA vB .Sbisim.bwd .SSimF.on-ev  (sVis refl br) = _ , sVis refl br , sbisim-refl _
Par-step-∼ A merge vA vB .Sbisim.bwd .SSimF.on-ev  (sRet ())
Par-step-∼ A merge vA vB .Sbisim.bwd .SSimF.on-tau (sSil ())
Par-step-∼ A merge vA vB .Sbisim.bwd .SSimF.on-tau (sTau refl br) = case br of λ ()

-- the failures-divergences law follows.
Par-step-FD : (A : EventSet) (merge : Mg R₁ R₂ R)
              (vA : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₁)))
              (vB : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R₂)))
            → Par A merge (pchoice vA) (pchoice vB)
              ≈FD pchoice (par-pVis A merge (react vA ∅t) (react vB ∅t) (pchoice vA) (pchoice vB))
Par-step-FD A merge vA vB = drbisim→≈FD (sbisim→drbisim (Par-step-∼ A merge vA vB))

-- ⊤-merge (Par⊤) and interleaving (⦀) instances.
Par⊤-step-FD : (A : EventSet)
               (vA vB : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) (⊤ {ℓr}))))
             → (pchoice vA ∥⇘ A ⇙ pchoice vB)
               ≈FD pchoice (par-pVis A (λ _ _ → tt) (react vA ∅t) (react vB ∅t) (pchoice vA) (pchoice vB))
Par⊤-step-FD A vA vB = Par-step-FD A (λ _ _ → tt) vA vB

⦀-step-FD : (vA vB : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) (⊤ {ℓr}))))
          → (pchoice vA ⦀ pchoice vB)
            ≈FD pchoice (par-pVis ∅ES (λ _ _ → tt)
                          (react vA ∅t) (react vB ∅t) (pchoice vA) (pchoice vB))
⦀-step-FD vA vB = Par⊤-step-FD ∅ES vA vB

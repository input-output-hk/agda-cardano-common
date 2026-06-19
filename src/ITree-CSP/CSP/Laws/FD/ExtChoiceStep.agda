{-# OPTIONS --guardedness #-}

-- External-choice STEP law (TPC 1.14 / UCS 2.14):
--   (?x:A → P) □ (?x:B → Q) = ?x:A∪B → ((P ⊓ Q) ◁ x∈A∩B ▷ (P ◁ x∈A ▷ Q)).
--
-- In this spike the VISIBLE part of an react node IS prefix-choice `?x:A → P(x)` — the
-- map `v : (at) → ContinueType at (Maybe PTree)` with domain A and v(x) = just (P x).
-- So a prefix-choice is `pchoice v = ptree (react v ∅t)` (stable, pure-visible).
--
-- The conditional `(P⊓Q) ◁ x∈A∩B ▷ (P ◁ x∈A ▷ Q)` is EXACTLY what `mergeMaybe`/`mergeVis`
-- computes per event:  both offer ⇒ p⊓q;  only A ⇒ p;  only B ⇒ q;  neither ⇒ ∅.
-- Hence the RHS is `pchoice (mergeVis vA vB)`, and the law holds BY DEFINITION of □ on
-- two prefix-choices: force(pchoice vA □ pchoice vB) = react (mergeVis vA vB) (□-mt …),
-- which has the SAME visible map as the RHS and a vacuous τ-part (both operands τ-free).
-- We confirm it as a STRONG bisimulation (⇒ ≈FD).

open import Level using (Level; lift)
open import Data.Maybe using (Maybe)
open import Data.Product using (_,_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)
open import Function using (case_of_)

open import Process_Trees

module CSP.Laws.FD.ExtChoiceStep {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (_□_; _⊓_; mergeVis; ∅t; pchoice)
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD        {E = E} {I = ExtI E} using (drbisim→≈FD)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- □-step as a STRONG bisimulation: both sides offer exactly `mergeVis vA vB` and have
-- no τ.  on-ev rebuilds the same step (same map ⇒ same continuation); on-tau is vacuous
-- (□-mt of two τ-free operands, resp. ∅t, is everywhere `nothing`).
□-step-∼ : ⦃ _ : DecEq R ⦄
           (vA vB : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         → (pchoice vA □ pchoice vB) ∼ pchoice (mergeVis vA vB)
□-step-∼ vA vB .Sbisim.fwd .SSimF.on-ev  (sVis refl br) = _ , sVis refl br , sbisim-refl _
□-step-∼ vA vB .Sbisim.fwd .SSimF.on-ev  (sRet ())
□-step-∼ vA vB .Sbisim.fwd .SSimF.on-tau (sSil ())
□-step-∼ vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , base _}            refl br) = case br of λ ()
□-step-∼ vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , fin}               refl br) = case br of λ ()
□-step-∼ vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , pair (base _) _}   refl br) = case br of λ ()
□-step-∼ vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , pair (pair _ _) _} refl br) = case br of λ ()
□-step-∼ vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , pair fin i′} {a = lift fzero , aa}            refl br) = case br of λ ()
□-step-∼ vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , pair fin i′} {a = lift (fsuc fzero) , aa}     refl br) = case br of λ ()
□-step-∼ vA vB .Sbisim.fwd .SSimF.on-tau (sTau {i = _ , pair fin i′} {a = lift (fsuc (fsuc _)) , aa}  refl br) = case br of λ ()
□-step-∼ vA vB .Sbisim.bwd .SSimF.on-ev  (sVis refl br) = _ , sVis refl br , sbisim-refl _
□-step-∼ vA vB .Sbisim.bwd .SSimF.on-ev  (sRet ())
□-step-∼ vA vB .Sbisim.bwd .SSimF.on-tau (sSil ())
□-step-∼ vA vB .Sbisim.bwd .SSimF.on-tau (sTau refl br) = case br of λ ()

-- and the failures-divergences law follows.
□-step-FD : ⦃ _ : DecEq R ⦄
            (vA vB : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
          → (pchoice vA □ pchoice vB) ≈FD pchoice (mergeVis vA vB)
□-step-FD vA vB = drbisim→≈FD (sbisim→drbisim (□-step-∼ vA vB))

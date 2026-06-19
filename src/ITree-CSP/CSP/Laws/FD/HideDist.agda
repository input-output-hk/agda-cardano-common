{-# OPTIONS --guardedness #-}

-- Hiding distributes over internal choice (T3.1 / U5.1):  (P ⊓ Q) ∖ X ≈FD (P∖X) ⊓ (Q∖X).
--
-- Both sides are ⊓-shaped: they offer NO visible event, and a single internal τ on either
-- side resolves to exactly the SAME state — `P∖X` or `Q∖X`.  ((P⊓Q)∖X's resolving τ is the
-- ⊓-resolution lifted through hide, `Hide-τ ∘ ⊓-stepL/R`; the RHS's is `⊓-stepL/R` directly.)
-- So it is a (non-recursive) STRONG bisimulation with `sbisim-refl` continuations — like
-- □-step — lifted to ≈FD.

open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.HideDist {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepL; ⊓-stepR; ⊓-τ-inv)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (Hide-τ; Hide-τ-elim; HideτR; hτP; hτH; hide-hVis-inv; HideevR; heV; he√)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- an internal choice offers no visible event (force is `react ∅v …`).
⊓-no-ev : {P Q M : PTree E (ExtI E) R} {e : Event√ R} → (P ⊓ Q) ─[ ev e ]─► M → ⊥
⊓-no-ev (sRet eq)    = case eq of λ ()
⊓-no-ev (sVis eq br) with react-injective eq
... | refl , _ = case br of λ ()

module _ (A : EventSet) (P Q : PTree E (ExtI E) R) where

  dist-fwd-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
              → ((P ⊓ Q) ∖ A) ─[ ev l ]─► M
              → Σ[ M′ ∈ PTree E (ExtI E) R ] (((P ∖ A) ⊓ (Q ∖ A)) ─[ ev l ]─► M′) × (M ∼ M′)
  dist-fwd-ev (sVis eqf br) with hide-hVis-inv A (P ⊓ Q) eqf br
  ... | heV P′ ¬c Pev = ⊥-elim (⊓-no-ev Pev)
  dist-fwd-ev (sRet eqf) = case eqf of λ ()

  dist-fwd-tau : {M : PTree E (ExtI E) R}
               → ((P ⊓ Q) ∖ A) ─[ τ ]─► M
               → Σ[ M′ ∈ PTree E (ExtI E) R ] (((P ∖ A) ⊓ (Q ∖ A)) ─[ τ ]─► M′) × (M ∼ M′)
  dist-fwd-tau step with Hide-τ-elim A (P ⊓ Q) step
  ... | hτP P′ Pτ refl with ⊓-τ-inv P Q Pτ
  ...   | inj₁ refl = (P ∖ A) , ⊓-stepL (P ∖ A) (Q ∖ A) , sbisim-refl (P ∖ A)
  ...   | inj₂ refl = (Q ∖ A) , ⊓-stepR (P ∖ A) (Q ∖ A) , sbisim-refl (Q ∖ A)
  dist-fwd-tau step | hτH P′ c Pev refl = ⊥-elim (⊓-no-ev Pev)

  dist-bwd-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
              → ((P ∖ A) ⊓ (Q ∖ A)) ─[ ev l ]─► M
              → Σ[ M′ ∈ PTree E (ExtI E) R ] (((P ⊓ Q) ∖ A) ─[ ev l ]─► M′) × (M ∼ M′)
  dist-bwd-ev step = ⊥-elim (⊓-no-ev step)

  dist-bwd-tau : {M : PTree E (ExtI E) R}
               → ((P ∖ A) ⊓ (Q ∖ A)) ─[ τ ]─► M
               → Σ[ M′ ∈ PTree E (ExtI E) R ] (((P ⊓ Q) ∖ A) ─[ τ ]─► M′) × (M ∼ M′)
  dist-bwd-tau step with ⊓-τ-inv (P ∖ A) (Q ∖ A) step
  ... | inj₁ refl = (P ∖ A) , Hide-τ A (P ⊓ Q) (⊓-stepL P Q) , sbisim-refl (P ∖ A)
  ... | inj₂ refl = (Q ∖ A) , Hide-τ A (P ⊓ Q) (⊓-stepR P Q) , sbisim-refl (Q ∖ A)

  hide-dist-∼ : ((P ⊓ Q) ∖ A) ∼ ((P ∖ A) ⊓ (Q ∖ A))
  hide-dist-∼ .Sbisim.fwd .SSimF.on-ev  = dist-fwd-ev
  hide-dist-∼ .Sbisim.fwd .SSimF.on-tau = dist-fwd-tau
  hide-dist-∼ .Sbisim.bwd .SSimF.on-ev  = dist-bwd-ev
  hide-dist-∼ .Sbisim.bwd .SSimF.on-tau = dist-bwd-tau

  -- hide-dist (T3.1):  (P ⊓ Q) ∖ X ≈FD (P∖X) ⊓ (Q∖X)
  hide-dist-FD : ((P ⊓ Q) ∖ A) ≈FD ((P ∖ A) ⊓ (Q ∖ A))
  hide-dist-FD = drbisim→≈FD (sbisim→drbisim hide-dist-∼)

{-# OPTIONS --guardedness #-}

-- Renaming distributes over internal choice (T3.13):
--   (P ⊓ Q) ⟦ inv ⟧ⁱ ≈FD (P ⟦ inv ⟧ⁱ) ⊓ (Q ⟦ inv ⟧ⁱ).
--
-- Direct analogue of `CSP.Laws.FD.HideDist` (hide-dist).  Both sides are ⊓-shaped:
-- they offer NO visible event (⊓ = `react ∅v (br2 P Q)`, and renaming a ∅v offer
-- map yields no offers), and a single internal τ on either side resolves to exactly
-- the SAME state — `P ⟦ inv ⟧ⁱ` or `Q ⟦ inv ⟧ⁱ`.  ((P⊓Q)⟦inv⟧ⁱ's resolving τ is the
-- ⊓-resolution lifted through rename — `ren-τ-fwd ∘ ⊓-stepL/R`, recovered by
-- `ren-τ-inv` then `⊓-τ-inv`; the RHS's is `⊓-stepL/R` directly.)
-- So it is a (non-recursive) STRONG bisimulation with `sbisim-refl` continuations —
-- like □-step / hide-dist — lifted to ≈FD.

open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.RenameIChoiceDist {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (_⊓_)
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepL; ⊓-stepR; ⊓-τ-inv)
open import CSP.Laws.Traces.TraceLawsRename {E = E}
  using (_⟦_⟧ⁱ; ren-τ-fwd; ren-τ-inv; ren-ev-inv)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- an internal choice offers no visible event (force is `react ∅v …`).
⊓-no-ev : {P Q M : PTree E (ExtI E) R} {e : Event√ R} → (P ⊓ Q) ─[ ev e ]─► M → ⊥
⊓-no-ev (sRet eq)    = case eq of λ ()
⊓-no-ev (sVis eq br) with react-injective eq
... | refl , _ = case br of λ ()

-- the renamed internal choice offers no visible event either: a visible step of
-- (P⊓Q)⟦inv⟧ⁱ inverts (ren-ev-inv) to a visible step of P⊓Q (impossible) or a √
-- from `force (P⊓Q) = ret r` (impossible, since force(P⊓Q) = react …).
rename-⊓-no-ev : {inv : _} {P Q M : PTree E (ExtI E) R} {e : Event√ R}
               → ((P ⊓ Q) ⟦ inv ⟧ⁱ) ─[ ev e ]─► M → ⊥
rename-⊓-no-ev step with ren-ev-inv step
... | inj₁ (_ , _ , _ , _ , _ , Pev , _ , _ , _) = ⊓-no-ev Pev
... | inj₂ (_ , _ , eqret , _)                    = case eqret of λ ()

module _ (inv : _) (P Q : PTree E (ExtI E) R) where

  dist-fwd-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
              → ((P ⊓ Q) ⟦ inv ⟧ⁱ) ─[ ev l ]─► M
              → Σ[ M′ ∈ PTree E (ExtI E) R ]
                  (((P ⟦ inv ⟧ⁱ) ⊓ (Q ⟦ inv ⟧ⁱ)) ─[ ev l ]─► M′) × (M ∼ M′)
  dist-fwd-ev step = ⊥-elim (rename-⊓-no-ev step)

  dist-fwd-tau : {M : PTree E (ExtI E) R}
               → ((P ⊓ Q) ⟦ inv ⟧ⁱ) ─[ τ ]─► M
               → Σ[ M′ ∈ PTree E (ExtI E) R ]
                   (((P ⟦ inv ⟧ⁱ) ⊓ (Q ⟦ inv ⟧ⁱ)) ─[ τ ]─► M′) × (M ∼ M′)
  dist-fwd-tau step with ren-τ-inv step
  ... | P₁ , Pτ , refl with ⊓-τ-inv P Q Pτ
  ...   | inj₁ refl = (P ⟦ inv ⟧ⁱ) , ⊓-stepL (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ) , sbisim-refl (P ⟦ inv ⟧ⁱ)
  ...   | inj₂ refl = (Q ⟦ inv ⟧ⁱ) , ⊓-stepR (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ) , sbisim-refl (Q ⟦ inv ⟧ⁱ)

  dist-bwd-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
              → ((P ⟦ inv ⟧ⁱ) ⊓ (Q ⟦ inv ⟧ⁱ)) ─[ ev l ]─► M
              → Σ[ M′ ∈ PTree E (ExtI E) R ]
                  (((P ⊓ Q) ⟦ inv ⟧ⁱ) ─[ ev l ]─► M′) × (M ∼ M′)
  dist-bwd-ev step = ⊥-elim (⊓-no-ev step)

  dist-bwd-tau : {M : PTree E (ExtI E) R}
               → ((P ⟦ inv ⟧ⁱ) ⊓ (Q ⟦ inv ⟧ⁱ)) ─[ τ ]─► M
               → Σ[ M′ ∈ PTree E (ExtI E) R ]
                   (((P ⊓ Q) ⟦ inv ⟧ⁱ) ─[ τ ]─► M′) × (M ∼ M′)
  dist-bwd-tau step with ⊓-τ-inv (P ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ) step
  ... | inj₁ refl = (P ⟦ inv ⟧ⁱ) , ren-τ-fwd (⊓-stepL P Q) , sbisim-refl (P ⟦ inv ⟧ⁱ)
  ... | inj₂ refl = (Q ⟦ inv ⟧ⁱ) , ren-τ-fwd (⊓-stepR P Q) , sbisim-refl (Q ⟦ inv ⟧ⁱ)

  rename-⊓-dist-∼ : ((P ⊓ Q) ⟦ inv ⟧ⁱ) ∼ ((P ⟦ inv ⟧ⁱ) ⊓ (Q ⟦ inv ⟧ⁱ))
  rename-⊓-dist-∼ .Sbisim.fwd .SSimF.on-ev  = dist-fwd-ev
  rename-⊓-dist-∼ .Sbisim.fwd .SSimF.on-tau = dist-fwd-tau
  rename-⊓-dist-∼ .Sbisim.bwd .SSimF.on-ev  = dist-bwd-ev
  rename-⊓-dist-∼ .Sbisim.bwd .SSimF.on-tau = dist-bwd-tau

  -- rename-⊓-dist (T3.13):  (P ⊓ Q) ⟦ inv ⟧ⁱ ≈FD (P ⟦ inv ⟧ⁱ) ⊓ (Q ⟦ inv ⟧ⁱ)
  rename-⊓-dist-FD : ((P ⊓ Q) ⟦ inv ⟧ⁱ) ≈FD ((P ⟦ inv ⟧ⁱ) ⊓ (Q ⟦ inv ⟧ⁱ))
  rename-⊓-dist-FD = drbisim→≈FD (sbisim→drbisim rename-⊓-dist-∼)

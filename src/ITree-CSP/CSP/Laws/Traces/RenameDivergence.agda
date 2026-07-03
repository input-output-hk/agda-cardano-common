{-# OPTIONS --guardedness #-}

-- Cross-alphabet rename preserves divergence-freedom.
--
-- For the injective alphabet renaming `renameMap : PTree E₁ … → PTree E₂ …`,
-- every infinite τ-run of `renameMap P` reflects to an infinite τ-run of `P`
-- (each renamed τ-step is inverted by `ren-τ-inv` to a source τ-step), and every
-- √-free run of `renameMap P` is the image of a √-free run of `P` (via
-- `rename-∖√-elim` from `RenameDeadlock`).  Hence
-- `DivergenceFree P → DivergenceFree (renameMap P)`.

open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Process_Trees

module CSP.Laws.Traces.RenameDivergence {ℓ ℓe₁ ℓe₂}
  {E₁ : Set ℓ → Set ℓe₁} {E₂ : Set ℓ → Set ℓe₂}
  (ι      : ∀ {A} → E₁ A → E₂ A)
  (ι⁻¹    : ∀ {A} → E₂ A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e) where
open PTree
open import CSP.Rename {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv
open import CSP.Laws.Traces.RenameDeadlock {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv
import Semantics.LTS        {E = E₁} {I = ExtI E₁} as L1
import Semantics.LTS        {E = E₂} {I = ExtI E₂} as L2
import Semantics.DRBisim    {E = E₁} {I = ExtI E₁} as DR1
import Semantics.DRBisim    {E = E₂} {I = ExtI E₂} as DR2
import Semantics.DeadlockDR {E = E₁} {I = ExtI E₁} as DD1
import Semantics.DeadlockDR {E = E₂} {I = ExtI E₂} as DD2

-- Non-coinductive helper: invert one τ-step of a `renameMap P` divergence into a
-- source τ-step (via `ren-τ-inv {ι-vis-inv}`), bundling the `subst`-rewritten tail
-- as a divergence of `renameMap P₁`.  Splitting this off keeps the recursive call in
-- `rename-Diverges-inv` directly under the `.rest` copattern (genuinely guarded).
rdi-step : ∀ {ℓr} {Rr : Set ℓr} {P : PTree E₁ (ExtI E₁) Rr}
         → DR2.Diverges (renameMap P)
         → Σ[ P₁ ∈ PTree E₁ (ExtI E₁) Rr ]
             (P L1.─[ L1.τ ]─► P₁ × DR2.Diverges (renameMap P₁))
rdi-step {P = P} d with ren-τ-inv {inv = ι-vis-inv} {P = P} (d .DR2.Diverges.step)
... | P₁ , Pτ , eqW = P₁ , Pτ , subst DR2.Diverges eqW (d .DR2.Diverges.rest)

-- An infinite τ-run of `renameMap P` reflects to one of `P` (rename preserves τ;
-- each renamed τ-step is inverted by `ren-τ-inv` to a source τ-step).
rename-Diverges-inv : ∀ {ℓr} {Rr : Set ℓr} {P : PTree E₁ (ExtI E₁) Rr}
                    → DR2.Diverges (renameMap P) → DR1.Diverges P
rename-Diverges-inv d .DR1.Diverges.next = proj₁ (rdi-step d)
rename-Diverges-inv d .DR1.Diverges.step = proj₁ (proj₂ (rdi-step d))
rename-Diverges-inv d .DR1.Diverges.rest = rename-Diverges-inv (proj₂ (proj₂ (rdi-step d)))

-- Rename preserves divergence-freedom: a √-free run of `renameMap P` inverts to one
-- of `P`, and any divergence of its (renamed) endpoint reflects to a source
-- divergence, contradicting divergence-freedom of `P`.
rename-DivergenceFree : ∀ {ℓr} {Rr : Set ℓr} {P : PTree E₁ (ExtI E₁) Rr}
                      → DD1.DivergenceFree P → DD2.DivergenceFree (renameMap P)
rename-DivergenceFree dfP reach div with rename-∖√-elim reach
... | s , P′ , reachP , refl = dfP reachP (rename-Diverges-inv div)

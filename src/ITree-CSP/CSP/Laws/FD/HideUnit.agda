{-# OPTIONS --guardedness #-}

-- Null hiding (T3.4 / U5.4):  P ∖ ∅ ≈FD P.
--
-- Hiding the empty set changes nothing: `∅es` hides no event, so `P ∖ ∅es` offers exactly
-- P's visible events (Hide-keep), mirrors P's τ's (Hide-τ), and emits no new τ (the
-- hidden-event branch is empty since `∅es .mem ≡ ⊥`).  Hence a STRONG bisimulation
-- `P ∖ ∅es ∼ P`, lifted to ≈FD.  As for ⦀-unit, the backward direction needs the reversed
-- relation, so we define `hide-unit-∼` / `hide-unitR` mutually (never `sbisim-sym`).

open import Level using (Level)
open import Data.Empty using (⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.HideUnit {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (Hide-τ; Hide-keep; Hide-√; Hide-τ-elim; HideτR; hτP; hτH
        ; hide-hVis-inv; HideevR; heV; he√; fHide-ret-inv)
open import CSP.Laws.Traces.TraceLawsHideAlg E-≟ using (∅es)

private
  variable
    ℓr : Level
    R  : Set ℓr

hide-unit-∼ : (P : PTree E (ExtI E) R) → (P ∖ ∅es) ∼ P
hide-unitR  : (P : PTree E (ExtI E) R) → P ∼ (P ∖ ∅es)

-- forward: a move of `P ∖ ∅es` is mirrored by P.
unit-fwd-ev : (P : PTree E (ExtI E) R) {l : Event√ R} {M : PTree E (ExtI E) R}
            → (P ∖ ∅es) ─[ ev l ]─► M
            → Σ[ M′ ∈ PTree E (ExtI E) R ] ((P ─[ ev l ]─► M′) × (M ∼ M′))
unit-fwd-ev P (sVis eqf br) with hide-hVis-inv ∅es P eqf br
... | heV P′ ¬c Pev = P′ , Pev , hide-unit-∼ P′
unit-fwd-ev P (sRet eqf) = deadlock , sRet (fHide-ret-inv ∅es P eqf) , sbisim-refl deadlock

unit-fwd-tau : (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
             → (P ∖ ∅es) ─[ τ ]─► M
             → Σ[ M′ ∈ PTree E (ExtI E) R ] ((P ─[ τ ]─► M′) × (M ∼ M′))
unit-fwd-tau P step with Hide-τ-elim ∅es P step
... | hτP P′ Pτ refl     = P′ , Pτ , hide-unit-∼ P′
... | hτH P′ c Pev refl  = ⊥-elim c

-- backward: a move of P is mirrored by `P ∖ ∅es` (∅es hides nothing).
unit-bwd-ev : (P : PTree E (ExtI E) R) {l : Event√ R} {M : PTree E (ExtI E) R}
            → P ─[ ev l ]─► M
            → Σ[ M′ ∈ PTree E (ExtI E) R ] ((P ∖ ∅es) ─[ ev l ]─► M′) × (M ∼ M′)
unit-bwd-ev P (sVis {t′ = P′} eqP br) =
  P′ ∖ ∅es , Hide-keep ∅es P (λ ()) (sVis eqP br) , hide-unitR P′
unit-bwd-ev P (sRet eqP) = deadlock , Hide-√ ∅es P eqP , sbisim-refl deadlock

unit-bwd-tau : (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
             → P ─[ τ ]─► M
             → Σ[ M′ ∈ PTree E (ExtI E) R ] ((P ∖ ∅es) ─[ τ ]─► M′) × (M ∼ M′)
unit-bwd-tau P {M = M} step = M ∖ ∅es , Hide-τ ∅es P step , hide-unitR M

hide-unit-∼ P .Sbisim.fwd .SSimF.on-ev  = unit-fwd-ev  P
hide-unit-∼ P .Sbisim.fwd .SSimF.on-tau = unit-fwd-tau P
hide-unit-∼ P .Sbisim.bwd .SSimF.on-ev  = unit-bwd-ev  P
hide-unit-∼ P .Sbisim.bwd .SSimF.on-tau = unit-bwd-tau P
hide-unitR  P .Sbisim.fwd .SSimF.on-ev  = unit-bwd-ev  P
hide-unitR  P .Sbisim.fwd .SSimF.on-tau = unit-bwd-tau P
hide-unitR  P .Sbisim.bwd .SSimF.on-ev  = unit-fwd-ev  P
hide-unitR  P .Sbisim.bwd .SSimF.on-tau = unit-fwd-tau P

-- null-hiding (T3.4):  P ∖ ∅ ≈FD P
hide-unit-FD : (P : PTree E (ExtI E) R) → (P ∖ ∅es) ≈FD P
hide-unit-FD P = drbisim→≈FD (sbisim→drbisim (hide-unit-∼ P))

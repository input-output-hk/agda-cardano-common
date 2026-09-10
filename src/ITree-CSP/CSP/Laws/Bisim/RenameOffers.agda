{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- CROSS-ALPHABET transport of the two confinement invariants of
-- `CSP.Laws.Bisim.DRCongruenceRep` along the injective alphabet renaming
-- `renameInv` (hence `renameMap`) of `CSP.Rename`:
--
--   OffersOnly-renameInv : (α ⇒ β along `inv`) → OffersOnly α P
--                        → OffersOnly β (renameInv P inv)
--   NoRet-renameInv      : NoRet P → NoRet (renameInv P inv)
--
-- Both need TWO instances of `DRCongruenceRep` (source `E₁` and target `E₂`),
-- which is why they cannot live inside that module: a module cannot instantiate
-- itself at a second alphabet.  Everything else is generic — the proofs are the
-- `ren-τ-inv` / `ren-ev-inv` step inversions of
-- `CSP.Laws.Traces.RenameDeadlock`, exactly as `cong-renameInv` uses them.
--
-- No postulates, holes, or `NON_TERMINATING`.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using () renaming (tt to tt₀)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Process_Trees

module CSP.Laws.Bisim.RenameOffers {ℓ ℓe₁ ℓe₂}
  {E₁ : Set ℓ → Set ℓe₁} {E₂ : Set ℓ → Set ℓe₂}
  (E₁-≟ : (x y : AnyTypes E₁) → Dec (x ≡ y))
  (E₂-≟ : (x y : AnyTypes E₂) → Dec (x ≡ y))
  (ι      : ∀ {A} → E₁ A → E₂ A)
  (ι⁻¹    : ∀ {A} → E₂ A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e) where
open PTree

-- re-exported PUBLICLY: a caller must be able to NAME `ι-vis-inv` to state the alphabet
-- transport premise of `OffersOnly-renameMap`, and to name `renameMap` in its conclusion
open import CSP.Rename {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv public
  using (ConcEvent₁; renameInv; renameMap; ι-vis-inv)
open import CSP.Laws.Traces.RenameDeadlock {E₁ = E₁} {E₂ = E₂} ι ι⁻¹ ι-linv
  using (_⟦_⟧ⁱ; ren-τ-inv; ren-ev-inv; force-ren-ret-inv)
-- the source-side node predicate that `NoRet`'s `nowNR` field is phrased in
open import CSP.Laws.Traces.TraceLawsExtChoice E₁-≟ using (NonRet)
-- the confinement layer at each alphabet (source `R1`, target `R2`)
import CSP.Laws.Bisim.DRCongruenceRep E₁-≟ as R1
import CSP.Laws.Bisim.DRCongruenceRep E₂-≟ as R2
import Semantics.LTS {E = E₂} {I = ExtI E₂} as L2

private
  variable
    ℓr : Level
    Rr : Set ℓr

-- the per-target partial inverse that drives `renameInv` (as in `DRCongruence`)
RenInv : Set (lsuc ℓ ⊔ ℓe₁ ⊔ ℓe₂)
RenInv = (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁

------------------------------------------------------------------------
-- `OffersOnly` transports along the rename, given that the target alphabet
-- `β` covers the `inv`-image of the source alphabet `α`.  Every target step
-- inverts (`ren-ev-inv` / `ren-τ-inv`) to a source step of `P`, so the source
-- confinement answers it; the √ residual is `deadlock`.
------------------------------------------------------------------------

OffersOnly-renameInv : {P : PTree E₁ (ExtI E₁) Rr} {inv : RenInv}
                       {α : R1.Alpha} {β : R2.Alpha}
                     → (∀ bt b at a → inv bt b ≡ just (at , a) → α at a → β bt b)
                     → R1.OffersOnly α P → R2.OffersOnly β (P ⟦ inv ⟧ⁱ)
OffersOnly-renameInv {P = P} {inv = inv} h ooP .R2.OffersOnly.now st
  with ren-ev-inv {inv = inv} {P = P} st
... | inj₁ (at , a , bt , b , P₁ , Pev , eqinv , refl , refl) =
      h bt b at a eqinv (R1.OffersOnly.now ooP Pev)
... | inj₂ (r , () , _)
OffersOnly-renameInv {P = P} {inv = inv} h ooP .R2.OffersOnly.step {l = L2.τ} st
  with ren-τ-inv {inv = inv} {P = P} st
... | P₁ , Pτ , refl = OffersOnly-renameInv h (R1.OffersOnly.step ooP Pτ)
OffersOnly-renameInv {P = P} {inv = inv} h ooP .R2.OffersOnly.step {l = L2.ev e} st
  with ren-ev-inv {inv = inv} {P = P} st
... | inj₁ (at , a , bt , b , P₁ , Pev , eqinv , refl , refl) =
      OffersOnly-renameInv h (R1.OffersOnly.step ooP Pev)
... | inj₂ (r , refl , eqP , refl) = R2.OffersOnly-deadlock

-- the headline instance: the injective ALPHABET renaming induced by ι
OffersOnly-renameMap : {P : PTree E₁ (ExtI E₁) Rr} {α : R1.Alpha} {β : R2.Alpha}
                     → (∀ bt b at a → ι-vis-inv bt b ≡ just (at , a) → α at a → β bt b)
                     → R1.OffersOnly α P → R2.OffersOnly β (renameMap P)
OffersOnly-renameMap h ooP = OffersOnly-renameInv {inv = ι-vis-inv} h ooP

------------------------------------------------------------------------
-- `NoRet` transports along the rename: a renamed `ret` node came from a source
-- `ret` node (`force-ren-ret-inv`), and every target step inverts to a source
-- step, so non-termination is preserved verbatim.
------------------------------------------------------------------------

NoRet-renameInv : {P : PTree E₁ (ExtI E₁) Rr} {inv : RenInv}
                → R1.NoRet P → R2.NoRet (P ⟦ inv ⟧ⁱ)
NoRet-renameInv {P = P} {inv = inv} nr .R2.NoRet.nowNR
  with PTree.force (P ⟦ inv ⟧ⁱ) in eqW
... | sil _     = tt₀
... | react _ _ = tt₀
... | ret r     =
      subst NonRet (force-ren-ret-inv {inv = inv} {P = P} eqW) (R1.NoRet.nowNR nr)
NoRet-renameInv {P = P} {inv = inv} nr .R2.NoRet.stepNR {l = L2.τ} st
  with ren-τ-inv {inv = inv} {P = P} st
... | P₁ , Pτ , refl = NoRet-renameInv (R1.NoRet.stepNR nr Pτ)
NoRet-renameInv {P = P} {inv = inv} nr .R2.NoRet.stepNR {l = L2.ev e} st
  with ren-ev-inv {inv = inv} {P = P} st
... | inj₁ (at , a , bt , b , P₁ , Pev , eqinv , refl , refl) =
      NoRet-renameInv (R1.NoRet.stepNR nr Pev)
... | inj₂ (r , refl , eqP , refl) = ⊥-elim (subst NonRet eqP (R1.NoRet.nowNR nr))

-- the headline instance: the injective ALPHABET renaming induced by ι
NoRet-renameMap : {P : PTree E₁ (ExtI E₁) Rr} → R1.NoRet P → R2.NoRet (renameMap P)
NoRet-renameMap nr = NoRet-renameInv {inv = ι-vis-inv} nr

------------------------------------------------------------------------
-- IMAGE confinement: a renamed process offers only events that HAVE an
-- `inv`-preimage, whatever the source process does.  The source-side premise
-- is discharged vacuously (`OffersOnly-full`), so the whole confinement is a
-- pure case analysis on the target alphabet.
------------------------------------------------------------------------

OffersOnly-renameInv-image : {P : PTree E₁ (ExtI E₁) Rr} {inv : RenInv} {β : R2.Alpha}
                           → (∀ bt b at a → inv bt b ≡ just (at , a) → β bt b)
                           → R2.OffersOnly β (P ⟦ inv ⟧ⁱ)
OffersOnly-renameInv-image h =
  OffersOnly-renameInv (λ bt b at a eq _ → h bt b at a eq)
                       (R1.OffersOnly-full (λ _ _ → tt₀))

-- the `renameMap` instance
OffersOnly-renameMap-image : {P : PTree E₁ (ExtI E₁) Rr} {β : R2.Alpha}
                           → (∀ bt b at a → ι-vis-inv bt b ≡ just (at , a) → β bt b)
                           → R2.OffersOnly β (renameMap P)
OffersOnly-renameMap-image h = OffersOnly-renameInv-image {inv = ι-vis-inv} h

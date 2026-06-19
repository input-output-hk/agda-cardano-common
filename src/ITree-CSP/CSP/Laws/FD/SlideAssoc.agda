{-# OPTIONS --guardedness #-}

-- ▷-assoc (U13.12), CONDITIONAL form:  P ▷ (Q ▷ R) ≈FD (P ▷ Q) ▷ R   when Q is
-- non-terminating (NonRet (force Q)).
--
-- The unconditional law FAILS in this spike — its `▷` resolves a terminated operand
-- EAGERLY (force(P▷Q)|ret r = ret r), so for Q = SKIP the two sides differ (Q▷R = SKIP
-- drops R on the left, but the right's outer timeout keeps R; see Laws_status §11).  With
-- Q non-terminating that obstruction is gone and the law holds.
--
-- It is NOT a strong bisimulation (`▷` is τ-absorbing: the timeout τ's nest differently on
-- the two sides), so it is a coinductive DR-bisimulation, lifted to ≈FD.  The handlers are
-- uniform in P: a visible/√ step of `P ▷ X` is P's step passed through (`▷-ev-L`), and the
-- τ's are classified by `▷-τ-elim` (which itself discharges the ret-P case) — so no separate
-- force-P split is needed.  The backward direction's P-τ continuation needs the REVERSED
-- bisim, so we build `sa→`/`sa←` mutually (no `drbisim-sym`, which would unguard); the
-- divergence transfers are separate coinductive `slide-div→`/`slide-div←`.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.SlideAssoc {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.WeakBisim {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (DRbisim; Diverges; drbisim-refl)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Bisim.IterCong E-≟ using (ret-no-τ)
open import CSP.Laws.Traces.TraceLaws E-≟ using (force-▷-ret; ▷-τ-L; ▷-ev-L)
open import CSP.Laws.Traces.TraceLawsExtChoice     E-≟ using (NonRet)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (▷-τ-elim; ▷-ev-elim; ▷-timeout)

module _ {ℓr} {R : Set ℓr} (Q R₀ : PTree E (ExtI E) R) (ntQ : NonRet (PTree.force Q)) where

  L→ R→ : PTree E (ExtI E) R → PTree E (ExtI E) R
  L→ P = P ▷ (Q ▷ R₀)
  R→ P = (P ▷ Q) ▷ R₀

  -- Finite witnesses of the single τ-step a divergence transfer takes (see the long
  -- comment at slide-div→).  Declared up here so build→/build← can be module-level
  -- (a where-local build is invisible to the guardedness checker's mutual analysis).
  data Step→ (P : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    fz→ : (R→ P) ─[ τ ]─► (Q ▷ R₀) → Diverges (Q ▷ R₀) → Step→ P
    rc→ : (P' : PTree E (ExtI E) R) → (R→ P) ─[ τ ]─► (R→ P') → Diverges (L→ P') → Step→ P

  data Step← (P : PTree E (ExtI E) R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
    to0← : (L→ P) ─[ τ ]─► (Q ▷ R₀) → Diverges (Q ▷ R₀) → Step← P
    rc←  : (P' : PTree E (ExtI E) R) → (L→ P) ─[ τ ]─► (L→ P') → Diverges (R→ P') → Step← P

  -- forward declarations (no mutual block)
  sa→ : (P : PTree E (ExtI E) R) → DRbisim R (L→ P) (R→ P)
  sa← : (P : PTree E (ExtI E) R) → DRbisim R (R→ P) (L→ P)
  fwdW : (P : PTree E (ExtI E) R) → WSimF (DRbisim R) (L→ P) (R→ P)
  bwdW : (P : PTree E (ExtI E) R) → WSimF (DRbisim R) (R→ P) (L→ P)
  slide-div→ : (P : PTree E (ExtI E) R) → Diverges (L→ P) → Diverges (R→ P)
  slide-div← : (P : PTree E (ExtI E) R) → Diverges (R→ P) → Diverges (L→ P)
  build→ : (P : PTree E (ExtI E) R) → Step→ P → Diverges (R→ P)
  build← : (P : PTree E (ExtI E) R) → Step← P → Diverges (L→ P)

  sa→ P .DRbisim.fwd  = fwdW P
  sa→ P .DRbisim.bwd  = bwdW P
  sa→ P .DRbisim.div→ = slide-div→ P
  sa→ P .DRbisim.div← = slide-div← P

  sa← P .DRbisim.fwd  = bwdW P
  sa← P .DRbisim.bwd  = fwdW P
  sa← P .DRbisim.div→ = slide-div← P
  sa← P .DRbisim.div← = slide-div→ P

  -- forward weak-simulation  L→ P  ⊑  R→ P
  fwdW P .WSimF.on-ev step with ▷-ev-elim P (Q ▷ R₀) step
  ... | Pev = _ , wev τ*-refl (▷-ev-L {P = P ▷ Q} {Q = R₀} (▷-ev-L {P = P} {Q = Q} Pev)) τ*-refl
               , drbisim-refl _
  fwdW P .WSimF.on-tau step with PTree.force P in eqP
  ... | ret r = ⊥-elim (ret-no-τ (force-▷-ret {P = P} {Q = Q ▷ R₀} eqP) step)
  ... | sil _ with ▷-τ-elim P (Q ▷ R₀) step
  ...   | inj₁ refl =
          Q ▷ R₀ , wτ (τ*-step (▷-τ-L {P = P ▷ Q} {Q = R₀} (▷-timeout P Q eqP _)) τ*-refl)
                 , drbisim-refl (Q ▷ R₀)
  ...   | inj₂ (P' , Pτ , refl) =
          (P' ▷ Q) ▷ R₀
          , wτ (τ*-step (▷-τ-L {P = P ▷ Q} {Q = R₀} (▷-τ-L {P = P} {Q = Q} Pτ)) τ*-refl)
          , sa→ P'
  fwdW P .WSimF.on-tau step | react _ _ with ▷-τ-elim P (Q ▷ R₀) step
  ...   | inj₁ refl =
          Q ▷ R₀ , wτ (τ*-step (▷-τ-L {P = P ▷ Q} {Q = R₀} (▷-timeout P Q eqP _)) τ*-refl)
                 , drbisim-refl (Q ▷ R₀)
  ...   | inj₂ (P' , Pτ , refl) =
          (P' ▷ Q) ▷ R₀
          , wτ (τ*-step (▷-τ-L {P = P ▷ Q} {Q = R₀} (▷-τ-L {P = P} {Q = Q} Pτ)) τ*-refl)
          , sa→ P'

  -- backward weak-simulation  R→ P  ⊑  L→ P
  bwdW P .WSimF.on-ev step with ▷-ev-elim (P ▷ Q) R₀ step
  ... | PQev with ▷-ev-elim P Q PQev
  ...   | Pev = _ , wev τ*-refl (▷-ev-L {P = P} {Q = Q ▷ R₀} Pev) τ*-refl , drbisim-refl _
  bwdW P .WSimF.on-tau step with PTree.force P in eqP
  ... | ret r = ⊥-elim (ret-no-τ
                  (force-▷-ret {P = P ▷ Q} {Q = R₀} (force-▷-ret {P = P} {Q = Q} eqP)) step)
  ... | sil _ with ▷-τ-elim (P ▷ Q) R₀ step
  ...   | inj₁ refl =
          R₀ , wτ (τ*-step (▷-timeout P (Q ▷ R₀) eqP _)
                           (τ*-step (▷-timeout Q R₀ refl ntQ) τ*-refl))
             , drbisim-refl R₀
  ...   | inj₂ (M' , PQτ , refl) with ▷-τ-elim P Q PQτ
  ...     | inj₁ refl =
            Q ▷ R₀ , wτ (τ*-step (▷-timeout P (Q ▷ R₀) eqP _) τ*-refl) , drbisim-refl (Q ▷ R₀)
  ...     | inj₂ (P' , Pτ , refl) =
            P' ▷ (Q ▷ R₀) , wτ (τ*-step (▷-τ-L {P = P} {Q = Q ▷ R₀} Pτ) τ*-refl) , sa← P'
  bwdW P .WSimF.on-tau step | react _ _ with ▷-τ-elim (P ▷ Q) R₀ step
  ...   | inj₁ refl =
          R₀ , wτ (τ*-step (▷-timeout P (Q ▷ R₀) eqP _)
                           (τ*-step (▷-timeout Q R₀ refl ntQ) τ*-refl))
             , drbisim-refl R₀
  ...   | inj₂ (M' , PQτ , refl) with ▷-τ-elim P Q PQτ
  ...     | inj₁ refl =
            Q ▷ R₀ , wτ (τ*-step (▷-timeout P (Q ▷ R₀) eqP _) τ*-refl) , drbisim-refl (Q ▷ R₀)
  ...     | inj₂ (P' , Pτ , refl) =
            P' ▷ (Q ▷ R₀) , wτ (τ*-step (▷-τ-L {P = P} {Q = Q ▷ R₀} Pτ) τ*-refl) , sa← P'

  -- The corecursive divergence transfers must be guarded.  A direct `with`-cased
  -- definition hides the corecursive call inside a `with`-aux, which Agda's syntactic
  -- guardedness checker cannot see through.  So we split each transfer into:
  --   • a NON-corecursive `decompose` that does all the `with`-casing and returns a finite
  --     `Step` datum describing the single τ-step taken plus the residual divergence, and
  --   • a module-level `build` that re-emits the coinductive `Diverges` record with the
  --     corecursive call directly under its `rest` constructor (so the cycle passes a guard).

  -- divergence transfer →   (the τ-target is the projection d.next ⇒ use subst, not refl)
  decompose→ : (P : PTree E (ExtI E) R) → Diverges (L→ P) → Step→ P
  decompose→ P d with PTree.force P in eqP
  ... | ret r = ⊥-elim (ret-no-τ (force-▷-ret {P = P} {Q = Q ▷ R₀} eqP) (d .Diverges.step))
  ... | sil _ with ▷-τ-elim P (Q ▷ R₀) (d .Diverges.step)
  ...   | inj₁ eq = fz→ (▷-τ-L {P = P ▷ Q} {Q = R₀} (▷-timeout P Q eqP _))
                       (subst Diverges eq (d .Diverges.rest))
  ...   | inj₂ (P' , Pτ , eq) = rc→ P' (▷-τ-L {P = P ▷ Q} {Q = R₀} (▷-τ-L {P = P} {Q = Q} Pτ))
                                    (subst Diverges eq (d .Diverges.rest))
  decompose→ P d | react _ _ with ▷-τ-elim P (Q ▷ R₀) (d .Diverges.step)
  ...   | inj₁ eq = fz→ (▷-τ-L {P = P ▷ Q} {Q = R₀} (▷-timeout P Q eqP _))
                       (subst Diverges eq (d .Diverges.rest))
  ...   | inj₂ (P' , Pτ , eq) = rc→ P' (▷-τ-L {P = P ▷ Q} {Q = R₀} (▷-τ-L {P = P} {Q = Q} Pτ))
                                    (subst Diverges eq (d .Diverges.rest))

  -- build→ is the sole corecursive function: its only self-call sits under the `.rest`
  -- COPATTERN of the `Diverges` record (the guard Agda recognises — record-value syntax is
  -- not seen through), with `decompose→` inlined to feed the next seed.  slide-div→ is then a
  -- non-recursive wrapper.  (Routing the corecursion through slide-div→ would put a build→-call
  -- in a non-guarded position and fail termination.)
  build→ P (fz→ st rest)   .Diverges.next = Q ▷ R₀
  build→ P (fz→ st rest)   .Diverges.step = st
  build→ P (fz→ st rest)   .Diverges.rest = rest
  build→ P (rc→ P' st sub) .Diverges.next = R→ P'
  build→ P (rc→ P' st sub) .Diverges.step = st
  build→ P (rc→ P' st sub) .Diverges.rest = build→ P' (decompose→ P' sub)
  slide-div→ P d = build→ P (decompose→ P d)

  -- divergence transfer ←
  decompose← : (P : PTree E (ExtI E) R) → Diverges (R→ P) → Step← P
  decompose← P d with PTree.force P in eqP
  ... | ret r = ⊥-elim (ret-no-τ
                  (force-▷-ret {P = P ▷ Q} {Q = R₀} (force-▷-ret {P = P} {Q = Q} eqP)) (d .Diverges.step))
  ... | sil _ with ▷-τ-elim (P ▷ Q) R₀ (d .Diverges.step)
  ...   | inj₁ eq = to0← (▷-timeout P (Q ▷ R₀) eqP _)
                        (record { step = ▷-timeout Q R₀ refl ntQ
                                ; rest = subst Diverges eq (d .Diverges.rest) })
  ...   | inj₂ (M' , PQτ , eq) with ▷-τ-elim P Q PQτ
  ...     | inj₁ eq2 = to0← (▷-timeout P (Q ▷ R₀) eqP _)
                           (subst Diverges (trans eq (cong (_▷ R₀) eq2)) (d .Diverges.rest))
  ...     | inj₂ (P' , Pτ , eq2) = rc← P' (▷-τ-L {P = P} {Q = Q ▷ R₀} Pτ)
                                       (subst Diverges (trans eq (cong (_▷ R₀) eq2)) (d .Diverges.rest))
  decompose← P d | react _ _ with ▷-τ-elim (P ▷ Q) R₀ (d .Diverges.step)
  ...   | inj₁ eq = to0← (▷-timeout P (Q ▷ R₀) eqP _)
                        (record { step = ▷-timeout Q R₀ refl ntQ
                                ; rest = subst Diverges eq (d .Diverges.rest) })
  ...   | inj₂ (M' , PQτ , eq) with ▷-τ-elim P Q PQτ
  ...     | inj₁ eq2 = to0← (▷-timeout P (Q ▷ R₀) eqP _)
                           (subst Diverges (trans eq (cong (_▷ R₀) eq2)) (d .Diverges.rest))
  ...     | inj₂ (P' , Pτ , eq2) = rc← P' (▷-τ-L {P = P} {Q = Q ▷ R₀} Pτ)
                                       (subst Diverges (trans eq (cong (_▷ R₀) eq2)) (d .Diverges.rest))

  build← P (to0← st rest)  .Diverges.next = Q ▷ R₀
  build← P (to0← st rest)  .Diverges.step = st
  build← P (to0← st rest)  .Diverges.rest = rest
  build← P (rc← P' st sub) .Diverges.next = L→ P'
  build← P (rc← P' st sub) .Diverges.step = st
  build← P (rc← P' st sub) .Diverges.rest = build← P' (decompose← P' sub)
  slide-div← P d = build← P (decompose← P d)

  -- P ▷ (Q ▷ R)  ≈FD  (P ▷ Q) ▷ R     (Q non-terminating)
  slide-assoc-FD : (P : PTree E (ExtI E) R) → (P ▷ (Q ▷ R₀)) ≈FD ((P ▷ Q) ▷ R₀)
  slide-assoc-FD P = drbisim→≈FD (sa→ P)

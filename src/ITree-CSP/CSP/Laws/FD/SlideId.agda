{-# OPTIONS --guardedness #-}

-- ▷-id (U13.18):  P ▷ P  ≈FD  P.   General P, general R, NO side-condition, NO DecEq.
--
-- Both operands of the slide are the SAME process P.  Two regimes on `force P`:
--   • `force P = ret r`: `P ▷ P` and `P` have IDENTICAL force (`force-▷-ret`), so they
--     are strongly bisimilar (force-equality bisim) ⇒ ≈FD.
--   • `force P` live (sil/react, i.e. NonRet): the timeout `▷-timeout P P eqP _` fires
--     `(P ▷ P) ─[τ]─► P` in one step.  INTRO directions prepend that timeout to every
--     behaviour of P; ELIM directions collapse the operand split of `▷-reach-div` /
--     `▷-failures-elim` (both operands are P, so either injection lands on P).

open import Level using (Level; Lift; lift)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Laws.FD.SlideId {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS     {E = E} {I = ExtI E}
open import Semantics.Bisim   {E = E} {I = ExtI E}
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Refuses)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; div-extension-closed; failures⊥;
         _⊑F⊥_; _⊑D_; _⊑FD_; _≈FD_)
open import CSP.Laws.Traces.TraceLaws E-≟ using (force-▷-ret)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟ using (▷-timeout; ▷-τ-elim; ▷-ev-elim)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (▷-reach-div; div-τ-prepend; fail-τ-prepend; fail-ev-prepend; ▷-unstable)

-------------------------------------------------------------------------------------
-- Generic node-equality strong bisimulation (force-equal trees are ∼).
-- Copied verbatim from CSP.Laws.FD.SlideSkipResolve.
-------------------------------------------------------------------------------------

module _ {ℓr} {R : Set ℓr} where

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

-------------------------------------------------------------------------------------
-- The law.
-------------------------------------------------------------------------------------

module _ {ℓr} {R : Set ℓr} where

  -- ret regime: P ▷ P ∼ P (force-equality), lifted to ≈FD.
  ▷-id-ret-FD : (P : PTree E (ExtI E) R) {r : R}
              → PTree.force P ≡ ret r → (P ▷ P) ≈FD P
  ▷-id-ret-FD P eqP =
    drbisim→≈FD (sbisim→drbisim
      (sbisim-force-eq (trans (force-▷-ret {P = P} {Q = P} eqP) (sym eqP))))

  ----------------------------------------------------------------------------------
  -- live regime: the timeout (P ▷ P) ─[τ]─► P fires.  Build the four refinements.
  ----------------------------------------------------------------------------------

  -- INTRO (P ▷ P ⊑D P): every divergence of P lifts to P ▷ P via the timeout τ.
  ▷-id-⊑D-intro : (P : PTree E (ExtI E) R) {nP : NodeKind E (ExtI E) R}
                → PTree.force P ≡ nP → NonRet nP
                → ∀ {s} → divergences P s → divergences (P ▷ P) s
  ▷-id-⊑D-intro P eqP nt d = div-τ-prepend (▷-timeout P P eqP nt) d

  -- INTRO (P ▷ P ⊑F⊥ P): every failure⊥ of P lifts to P ▷ P via the timeout τ.
  ▷-id-⊑F⊥-intro : (P : PTree E (ExtI E) R) {nP : NodeKind E (ExtI E) R}
                 → PTree.force P ≡ nP → NonRet nP
                 → ∀ {s} {B : Event√ R → Set ℓr}
                 → failures⊥ P s B → failures⊥ (P ▷ P) s B
  ▷-id-⊑F⊥-intro P eqP nt (inj₁ f) = inj₁ (fail-τ-prepend (▷-timeout P P eqP nt) f)
  ▷-id-⊑F⊥-intro P eqP nt (inj₂ d) = inj₂ (▷-id-⊑D-intro P eqP nt d)

  -- ELIM (P ⊑D P ▷ P): every divergence of P ▷ P is a divergence of P.
  ▷-id-⊑D-elim : (P : PTree E (ExtI E) R)
               → ∀ {s} → divergences (P ▷ P) s → divergences P s
  ▷-id-⊑D-elim P d
    with ▷-reach-div P P (d .IsDivergence.reach) (d .IsDivergence.divwit)
  ... | inj₁ dP = subst (divergences P) (sym (d .IsDivergence.split)) (div-extension-closed dP)
  ... | inj₂ dP = subst (divergences P) (sym (d .IsDivergence.split)) (div-extension-closed dP)

  -- DecEq-free failures eliminator for the slide: a failure of P ▷ Q is a failure of P
  -- or of Q.  This is exactly ExtChoiceFD.▷-failures-elim, but standalone — the ▷-clauses
  -- of that mutual block never use DecEq (the DecEq came only from the □-mutual partner),
  -- so we reproduce them here.  A ▷-node is never stable, so the ⟹-refl base is vacuous;
  -- τ-steps either fire the timeout (→ Q) or slide P on; visible steps are P's own.
  ▷-fail-elim : (P Q : PTree E (ExtI E) R)
                {s : List (Event√ R)} {B : Event√ R → Set ℓr} {W : PTree E (ExtI E) R}
              → (P ▷ Q) ⟹⟨ s ⟩ W → Refuses W B → failures P s B ⊎ failures Q s B
  ▷-fail-elim P Q ⟹-refl ref = ⊥-elim (▷-unstable P Q (proj₁ ref))
  ▷-fail-elim P Q (⟹-τ step rest) ref with ▷-τ-elim P Q step
  ... | inj₁ refl              = inj₂ (_ , rest , ref)
  ... | inj₂ (P' , Pτ , refl) with ▷-fail-elim P' Q rest ref
  ...   | inj₁ fP' = inj₁ (fail-τ-prepend Pτ fP')
  ...   | inj₂ fQ  = inj₂ fQ
  ▷-fail-elim P Q (⟹-ev step rest) ref =
    inj₁ (fail-ev-prepend (▷-ev-elim P Q step) (_ , rest , ref))

  -- ELIM (P ⊑F⊥ P ▷ P): every failure⊥ of P ▷ P is a failure⊥ of P.  Both operands are
  -- P, so either injection of ▷-fail-elim lands on failures P.
  ▷-id-⊑F⊥-elim : (P : PTree E (ExtI E) R)
                → ∀ {s} {B : Event√ R → Set ℓr}
                → failures⊥ (P ▷ P) s B → failures⊥ P s B
  ▷-id-⊑F⊥-elim P (inj₁ (W , reach , ref)) with ▷-fail-elim P P reach ref
  ... | inj₁ fP = inj₁ fP
  ... | inj₂ fP = inj₁ fP
  ▷-id-⊑F⊥-elim P (inj₂ d) = inj₂ (▷-id-⊑D-elim P d)

  ▷-id-live-FD : (P : PTree E (ExtI E) R) {nP : NodeKind E (ExtI E) R}
               → PTree.force P ≡ nP → NonRet nP → (P ▷ P) ≈FD P
  ▷-id-live-FD P eqP nt =
    ((▷-id-⊑F⊥-intro P eqP nt , ▷-id-⊑D-intro P eqP nt)) ,
    ((▷-id-⊑F⊥-elim P , ▷-id-⊑D-elim P))

  -- The law.
  ▷-id-FD : (P : PTree E (ExtI E) R) → (P ▷ P) ≈FD P
  ▷-id-FD P with PTree.force P in eqP
  ... | ret r     = ▷-id-ret-FD P eqP
  ... | sil P'    = ▷-id-live-FD P eqP _
  ... | react v τc = ▷-id-live-FD P eqP _

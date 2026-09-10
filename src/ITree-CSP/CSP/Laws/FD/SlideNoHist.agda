{-# OPTIONS --guardedness #-}

-- Failures-divergences law (U13.25, ▷-nohist), built FD-direct, single-channel:
--
--   nohist-FD :  ((e ⟶ P) ▷ (e ⟶ Q))  ≈FD  (e ⟶ (λ x → P x ⊓ Q x))
--
-- Roscoe's "no-history" law  (?x:A → P) ▷ (?x:A → Q) = ?x:A → (P ⊓ Q).  In this spike we
-- use the SAME event e on both prefixes (single-channel), so the two prefixes share the
-- same domain A automatically: NO domain side-condition, and NO DecEq R is needed (▷, ⊓
-- and prefix all need none).
--
-- Write  S := (e ⟶ P) ▷ (e ⟶ Q),  PQ x := P x ⊓ Q x,  RHS := e ⟶ PQ = Prefix e PQ.
--
--   * LHS S: force = react (Prefix-cont e P) (slide-τ …) — offers e (→ P x), UNSTABLE
--     (the single timeout τ → e ⟶ Q), no other τ (prefix is τ-free).
--   * RHS Prefix e PQ: force = react (Prefix-cont e PQ) ∅t — STABLE, offers e (→ P x ⊓ Q x).
--
-- FD-direct (NOT a DR-bisimulation): the timeout target (e ⟶ Q) offers e → Q x, which the
-- RHS only reaches via the ⊓ inside P x ⊓ Q x.  ≈FD identifies them.  The proof recurses
-- manually on the slide's big-step (no ▷-failures-elim ⇒ no DecEq), exactly the
-- DecEq-free pattern of CSP.Laws.FD.SlideIChoiceExt, and decomposes each prefix with the
-- value-dependent prefix machinery of CSP.Laws.FD.InputDist.

open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using () renaming (tt to tt0)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.SlideNoHist {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Refuses)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; div-extension-closed; failures⊥;
         _⊇F⊥_; _⊇D_; _⊑FD_; _≈FD_)
open import CSP.Laws.Traces.TraceLaws E-≟ using (▷-ev-L)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (▷-timeout; ▷-τ-elim; ▷-ev-elim)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (▷-reach-div; div-τ-prepend; div-ev-prepend; fail-τ-prepend; fail-ev-prepend;
         ▷-unstable; stable-no-τ)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-failures←l; ⊓-failures←r; ⊓-div→; ⊓-div←l; ⊓-div←r; ⊓-failures⊥→)
open import CSP.Laws.FD.InputDist E-≟
  using (pfx-cont-just; pfx-refuses; pfx-failures→; pfx-failures-nil; pfx-failures-cons;
         pfx-div→; pfx-div-cons)

private
  variable
    ℓx : Level

-------------------------------------------------------------------------------------
-- Shared facts about the prefix head e ⟶ P (force = react _ ∅t : stable, NonRet, τ-free).
-------------------------------------------------------------------------------------

-- the prefix has no τ-step (force = react _ ∅t)
prefix-no-τ : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
              (e : E A) (P : A → PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
            → (e ⟶ P) ─[ τ ]─► M → ⊥
prefix-no-τ e P (sSil sile) = case sile of λ ()
prefix-no-τ e P (sTau refl br) = case br of λ ()

-- the prefix's visible event at value x reaches P x (the canonical prefix offer step)
pfx-ev-step : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr}
              (e : E A) (P : A → PTree E (ExtI E) R) (x : A)
            → (e ⟶ P) ─[ ev (evl (evLabel A e x)) ]─► P x
pfx-ev-step {A = A} e P x = sVis {at = A , e} {a = x} refl (pfx-cont-just e P x)

-------------------------------------------------------------------------------------
-- RHS→LHS : map failures⊥ / divergences of  RHS = Prefix e PQ  into  S = (e⟶P) ▷ (e⟶Q).
-- Gives  S ⊇F⊥ RHS  and  S ⊇D RHS.
-------------------------------------------------------------------------------------

module _ {ℓr} {A : Set ℓ} {R : Set ℓr} (e : E A) (P Q : A → PTree E (ExtI E) R) where

  private
    PQ : A → PTree E (ExtI E) R
    PQ x = P x ⊓ Q x

    S : PTree E (ExtI E) R
    S = (e ⟶ P) ▷ (e ⟶ Q)

  -- failures⊥ RHS → failures⊥ S   (the F⊥ component of S ⊇F⊥ RHS)
  RHS→S-F⊥ : ∀ {s} {B : Event√ R → Set ℓr} → failures⊥ (Prefix e PQ) s B → failures⊥ S s B
  RHS→S-F⊥ {B = B} (inj₁ (W , reach , ref)) with pfx-failures→ e PQ (W , reach , ref)
  -- nil: RHS refuses X at []; route to (e⟶Q) via the timeout (same prefix-domain refusal)
  ... | inj₁ (refl , ref′) =
        inj₁ (fail-τ-prepend (▷-timeout (e ⟶ P) (e ⟶ Q) refl tt0)
                (pfx-failures-nil e Q (pfx-refuses e PQ Q ref′)))
  -- cons: failure of PQ x at the tail; split P x / Q x summand and route accordingly
  ... | inj₂ (x , t , refl , fPQx) with ⊓-failures⊥→ (P x) (Q x) (inj₁ fPQx)
  ...   | inj₁ (inj₁ fPx) =
          inj₁ (fail-ev-prepend (▷-ev-L {Q = e ⟶ Q} (pfx-ev-step e P x)) fPx)
  ...   | inj₁ (inj₂ dPx) =
          inj₂ (div-ev-prepend (▷-ev-L {Q = e ⟶ Q} (pfx-ev-step e P x)) dPx)
  ...   | inj₂ (inj₁ fQx) =
          inj₁ (fail-τ-prepend (▷-timeout (e ⟶ P) (e ⟶ Q) refl tt0)
                  (fail-ev-prepend (pfx-ev-step e Q x) fQx))
  ...   | inj₂ (inj₂ dQx) =
          inj₂ (div-τ-prepend (▷-timeout (e ⟶ P) (e ⟶ Q) refl tt0)
                  (div-ev-prepend (pfx-ev-step e Q x) dQx))
  RHS→S-F⊥ {B = B} (inj₂ d) with pfx-div→ e PQ d
  ... | (x , t , refl , dPQx) with ⊓-div→ (P x) (Q x) dPQx
  ...   | inj₁ dPx =
          inj₂ (div-ev-prepend (▷-ev-L {Q = e ⟶ Q} (pfx-ev-step e P x)) dPx)
  ...   | inj₂ dQx =
          inj₂ (div-τ-prepend (▷-timeout (e ⟶ P) (e ⟶ Q) refl tt0)
                  (div-ev-prepend (pfx-ev-step e Q x) dQx))

  -- divergences RHS → divergences S   (the D component of S ⊇D RHS)
  RHS→S-D : ∀ {s} → divergences (Prefix e PQ) s → divergences S s
  RHS→S-D d with pfx-div→ e PQ d
  ... | (x , t , refl , dPQx) with ⊓-div→ (P x) (Q x) dPQx
  ...   | inj₁ dPx = div-ev-prepend (▷-ev-L {Q = e ⟶ Q} (pfx-ev-step e P x)) dPx
  ...   | inj₂ dQx = div-τ-prepend (▷-timeout (e ⟶ P) (e ⟶ Q) refl tt0)
                       (div-ev-prepend (pfx-ev-step e Q x) dQx)

  -----------------------------------------------------------------------------------
  -- LHS→RHS : map failures / divergences of S into RHS = Prefix e PQ.
  -- Gives  RHS ⊇F⊥ S  and  RHS ⊇D S.
  -----------------------------------------------------------------------------------

  -- failures: recurse on S's big-step.  S is unstable ⇒ the ⟹-refl base is vacuous.
  -- timeout τ → (e⟶Q): decompose with pfx-failures→ (nil ⇒ RHS refuses same X; cons ⇒
  -- failure of Q x, lift to PQ x via ⊓-failures←r).  prefix event → P x: rebuild the
  -- prefix big-step and decompose, lifting P x to PQ x via ⊓-failures←l.
  S→RHS-fail : ∀ {s} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
             → S ⟹⟨ s ⟩ W → Refuses W X → failures (Prefix e PQ) s X
  S→RHS-fail ⟹-refl ref = ⊥-elim (▷-unstable (e ⟶ P) (e ⟶ Q) (proj₁ ref))
  S→RHS-fail (⟹-τ step rest) ref with ▷-τ-elim (e ⟶ P) (e ⟶ Q) step
  ... | inj₁ refl with pfx-failures→ e Q (_ , rest , ref)
  ...   | inj₁ (refl , ref′)        = pfx-failures-nil e PQ (pfx-refuses e Q PQ ref′)
  ...   | inj₂ (x , t , refl , fQx) = pfx-failures-cons e PQ x (⊓-failures←r (P x) (Q x) fQx)
  S→RHS-fail (⟹-τ step rest) ref | inj₂ (P′ , Pτ , refl) = ⊥-elim (prefix-no-τ e P Pτ)
  S→RHS-fail (⟹-ev step rest) ref
    with pfx-failures→ e P (_ , ⟹-ev (▷-ev-elim (e ⟶ P) (e ⟶ Q) step) rest , ref)
  ... | inj₂ (x , t , refl , fPx) = pfx-failures-cons e PQ x (⊓-failures←l (P x) (Q x) fPx)

  -- divergences: project S's divergence onto an operand (▷-reach-div, DecEq-free), then
  -- decompose that prefix's divergence (cons) and lift the operand summand into PQ x.
  S→RHS-D : ∀ {s} → divergences S s → divergences (Prefix e PQ) s
  S→RHS-D d with ▷-reach-div (e ⟶ P) (e ⟶ Q) (d .IsDivergence.reach) (d .IsDivergence.divwit)
  ... | inj₁ dpre with pfx-div→ e P (subst (divergences (e ⟶ P)) (sym (d .IsDivergence.split))
                                          (div-extension-closed dpre))
  ...   | (x , t , refl , dPx) = pfx-div-cons e PQ x (⊓-div←l (P x) (Q x) dPx)
  S→RHS-D d | inj₂ dpre with pfx-div→ e Q (subst (divergences (e ⟶ Q)) (sym (d .IsDivergence.split))
                                               (div-extension-closed dpre))
  ...   | (x , t , refl , dQx) = pfx-div-cons e PQ x (⊓-div←r (P x) (Q x) dQx)

  -- failures⊥ S → failures⊥ RHS   (the F⊥ component of RHS ⊇F⊥ S)
  S→RHS-F⊥ : ∀ {s} {B : Event√ R → Set ℓr} → failures⊥ S s B → failures⊥ (Prefix e PQ) s B
  S→RHS-F⊥ (inj₁ (W , reach , ref)) = inj₁ (S→RHS-fail reach ref)
  S→RHS-F⊥ (inj₂ d)                 = inj₂ (S→RHS-D d)

-------------------------------------------------------------------------------------
-- THE LAW (U13.25, ▷-nohist, single-channel): pair the two ⊇F⊥ and two ⊇D refinements.
--   ≈FD = ((S⊇F⊥RHS, S⊇D RHS) , (RHS⊇F⊥S, RHS⊇D S)).
-------------------------------------------------------------------------------------

nohist-FD : ∀ {ℓr} {R : Set ℓr} {A : Set ℓ} (e : E A) (P Q : A → PTree E (ExtI E) R)
          → ((e ⟶ P) ▷ (e ⟶ Q)) ≈FD (e ⟶ (λ x → P x ⊓ Q x))
nohist-FD e P Q =
  (RHS→S-F⊥ e P Q , RHS→S-D e P Q) ,
  (S→RHS-F⊥ e P Q , S→RHS-D e P Q)

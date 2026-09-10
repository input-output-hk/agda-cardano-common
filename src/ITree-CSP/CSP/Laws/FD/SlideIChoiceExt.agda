{-# OPTIONS --guardedness #-}

-- Failures-divergences law (U13.22, ▷-⊓-ext), built FD-direct:
--
--   ▷-⊓-ext-FD :  (((e ⟶ P) ▷ P′) ⊓ Q)  ≈FD  ((e ⟶ P) ▷ (P′ ⊓ Q))
--
-- The internal-choice analogue of CSP.Laws.FD.ExtChoiceSlide.□-slide-FD.  Unlike that
-- law, ⊓ does NOT require DecEq R (⊓ is `react ∅v (br2 · ·)` — no offer merging, no √
-- bridges).  The LHS root  S ⊓ Q = react ∅v (br2 S Q)  has NO visible offers: Q is
-- reached only via the ⊓-resolution τ (⊓-stepR), and S via ⊓-stepL.  So the ⊓
-- decomposition lemmas (⊓-failures⊥→ / ⊓-div→) replace the root-event worker that
-- ExtChoiceSlide needed for the □ case.  The slide/prefix handling for the S-summand and
-- the RHS side is the same as ExtChoiceSlide, but routed through P′ ⊑ P′⊓Q.
--
-- It is NOT a DR-bisimulation (the ⊓-resolution τ fires at time 0 on the LHS but the
-- corresponding choice on the RHS is reached only after the timeout τ).  Hence FD-direct.
-- Write S := (e ⟶ P) ▷ P′ throughout.  LHS = S ⊓ Q, RHS = (e ⟶ P) ▷ (P′ ⊓ Q).

open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using () renaming (tt to tt0)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.SlideIChoiceExt {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.Refusals {E = E} {I = ExtI E} using (Refuses)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; div-extension-closed; empty-div; failures⊥;
         _⊇F⊥_; _⊇D_; _⊑FD_; _≈FD_)
open import CSP.Laws.Traces.TraceLaws E-≟ using (▷-ev-L)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (▷-timeout; ▷-τ-elim; ▷-ev-elim)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (▷-reach-div; ▷-reach-intro-L; div-τ-prepend; fail-τ-prepend; fail-ev-prepend;
         ▷-unstable; stable-no-τ)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepL; ⊓-stepR)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-failures→; ⊓-failures←l; ⊓-failures←r; ⊓-div→; ⊓-div←l; ⊓-div←r;
         ⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r)

private
  variable
    ℓr ℓx : Level
    R : Set ℓr
    A : Set ℓ

-------------------------------------------------------------------------------------
-- Shared facts about the prefix head e ⟶ P (force = react _ ∅t : stable, NonRet).
-------------------------------------------------------------------------------------

-- the prefix has no τ-step (force = react _ ∅t)
prefix-no-τ : (e : E A) (P : A → PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
            → (e ⟶ P) ─[ τ ]─► M → ⊥
prefix-no-τ e P (sSil sile) = case sile of λ ()
prefix-no-τ e P (sTau refl br) = case br of λ ()

-------------------------------------------------------------------------------------
-- Set-level divergence wrappers for the slide (copied from ExtChoiceSlide, which keeps
-- them private; built from the reach-* lemmas exported by ExtChoiceFD).
-------------------------------------------------------------------------------------

-- divergences (A ▷ B) ⊆ divergences A ∪ divergences B
▷-div-elim : (X Y : PTree E (ExtI E) R) {s : List (Event√ R)}
           → divergences (X ▷ Y) s → divergences X s ⊎ divergences Y s
▷-div-elim X Y d with ▷-reach-div X Y (d .IsDivergence.reach) (d .IsDivergence.divwit)
... | inj₁ dX = inj₁ (subst (divergences X) (sym (d .IsDivergence.split))
                            (div-extension-closed dX))
... | inj₂ dY = inj₂ (subst (divergences Y) (sym (d .IsDivergence.split))
                            (div-extension-closed dY))

-- divergences A ⊆ divergences (A ▷ B)
▷-div-intro-L : (X Y : PTree E (ExtI E) R) {s : List (Event√ R)}
              → divergences X s → divergences (X ▷ Y) s
▷-div-intro-L X Y d = subst (divergences (X ▷ Y)) (sym (d .IsDivergence.split))
  (div-extension-closed (▷-reach-intro-L X Y (d .IsDivergence.reach) (d .IsDivergence.divwit)))

-- divergences B ⊆ divergences (A ▷ B) when A is non-ret: fire the timeout first.
▷-div-intro-R : (X Y : PTree E (ExtI E) R) {nX : NodeKind E (ExtI E) R} {s : List (Event√ R)}
              → PTree.force X ≡ nX → NonRet nX → divergences Y s → divergences (X ▷ Y) s
▷-div-intro-R X Y eqX ntX d = div-τ-prepend (▷-timeout X Y eqX ntX) d

-------------------------------------------------------------------------------------
-- S-summand workers.  S = (e ⟶ P) ▷ P′.  Map an S behaviour into the RHS
-- (e ⟶ P) ▷ (P′ ⊓ Q), using P′ ⊑ P′ ⊓ Q on the right operand of the slide.  The prefix
-- (e ⟶ P) is STABLE (no τ) and NonRet — so S has exactly one τ (its timeout → P′), and
-- a visible event of S is the prefix's, which the RHS offers to the SAME P-continuation.
-------------------------------------------------------------------------------------

-- failures: recurse on S's big-step, keeping the event explicit (so no empty-s prefix
-- refusal ever needs to be matched: S is unstable, the ⟹-refl base is vacuous).
S→RHS-fail : (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → ((e ⟶ P) ▷ P′) ⟹⟨ s ⟩ W → Refuses W X
  → failures ((e ⟶ P) ▷ (P′ ⊓ Q)) s X
S→RHS-fail e P P′ Q ⟹-refl ref = ⊥-elim (▷-unstable (e ⟶ P) P′ (proj₁ ref))
S→RHS-fail e P P′ Q (⟹-τ step rest) ref with ▷-τ-elim (e ⟶ P) P′ step
... | inj₁ refl =
      fail-τ-prepend (▷-timeout (e ⟶ P) (P′ ⊓ Q) refl tt0)
        (⊓-failures←l P′ Q (_ , rest , ref))
... | inj₂ (P'' , Pτ , refl) = ⊥-elim (prefix-no-τ e P Pτ)
S→RHS-fail e P P′ Q (⟹-ev step rest) ref =
  fail-ev-prepend (▷-ev-L {Q = P′ ⊓ Q} (▷-ev-elim (e ⟶ P) P′ step)) (_ , rest , ref)

-- divergences: split S's divergence with ▷-div-elim into the prefix's (lift via the
-- prefix offer, unchanged P) or P′'s (lift to P′ ⊓ Q, then prepend the RHS timeout).
S→RHS-div : (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {s : List (Event√ R)}
  → divergences ((e ⟶ P) ▷ P′) s → divergences ((e ⟶ P) ▷ (P′ ⊓ Q)) s
S→RHS-div e P P′ Q d with ▷-div-elim (e ⟶ P) P′ d
... | inj₁ dpre = ▷-div-intro-L (e ⟶ P) (P′ ⊓ Q) dpre
... | inj₂ dP′  = ▷-div-intro-R (e ⟶ P) (P′ ⊓ Q) refl tt0 (⊓-div←l P′ Q dP′)

-------------------------------------------------------------------------------------
-- Divergence directions.   LHS = S ⊓ Q,  RHS = (e ⟶ P) ▷ (P′ ⊓ Q).
-------------------------------------------------------------------------------------

-- RHS ⊇D LHS : RHS recovers every LHS divergence (map div(S ⊓ Q) → div(RHS)).
-- ⊓-div→ splits div(S ⊓ Q) into div S (→ S→RHS-div) or div Q (→ RHS timeout, then ⊓-stepR).
▷-⊓-ext-⊆D :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
  → ((e ⟶ P) ▷ (P′ ⊓ Q)) ⊇D (((e ⟶ P) ▷ P′) ⊓ Q)
▷-⊓-ext-⊆D e P P′ Q d with ⊓-div→ ((e ⟶ P) ▷ P′) Q d
... | inj₁ dS = S→RHS-div e P P′ Q dS
... | inj₂ dQ =
      div-τ-prepend (▷-timeout (e ⟶ P) (P′ ⊓ Q) refl tt0)
        (div-τ-prepend (⊓-stepR P′ Q) dQ)

-- LHS ⊇D RHS : LHS recovers every RHS divergence (map div(RHS) → div(S ⊓ Q)).
-- ▷-div-elim splits div(RHS) into div(e ⟶ P) [→ S via ▷-div-intro-L, then ⊓-div←l] or
-- div(P′ ⊓ Q) [⊓-div→: div P′ → S via timeout intro, then ⊓-div←l; div Q → ⊓-div←r].
▷-⊓-ext-⊇D :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
  → (((e ⟶ P) ▷ P′) ⊓ Q) ⊇D ((e ⟶ P) ▷ (P′ ⊓ Q))
▷-⊓-ext-⊇D e P P′ Q d with ▷-div-elim (e ⟶ P) (P′ ⊓ Q) d
... | inj₁ dpre =
      ⊓-div←l ((e ⟶ P) ▷ P′) Q (▷-div-intro-L (e ⟶ P) P′ dpre)
... | inj₂ dP′Q with ⊓-div→ P′ Q dP′Q
...   | inj₁ dP′ =
        ⊓-div←l ((e ⟶ P) ▷ P′) Q (▷-div-intro-R (e ⟶ P) P′ refl tt0 dP′)
...   | inj₂ dQ  = ⊓-div←r ((e ⟶ P) ▷ P′) Q dQ

-------------------------------------------------------------------------------------
-- Failures directions.
-------------------------------------------------------------------------------------

-- RHS ⊇F⊥ LHS : RHS recovers every LHS stable failure⊥ (map failures⊥(S ⊓ Q) → RHS).
-- ⊓-failures⊥→ splits into the S-summand (→ S→RHS-fail / S→RHS-div) or the Q-summand
-- (→ RHS reaches Q in two τ's: timeout to P′ ⊓ Q, then ⊓-stepR).
▷-⊓-ext-⊆F⊥ :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
  → ((e ⟶ P) ▷ (P′ ⊓ Q)) ⊇F⊥ (((e ⟶ P) ▷ P′) ⊓ Q)
▷-⊓-ext-⊆F⊥ e P P′ Q f with ⊓-failures⊥→ ((e ⟶ P) ▷ P′) Q f
... | inj₁ (inj₁ (W , reach , ref)) = inj₁ (S→RHS-fail e P P′ Q reach ref)
... | inj₁ (inj₂ dS)                = inj₂ (S→RHS-div e P P′ Q dS)
... | inj₂ (inj₁ fQ) =
      inj₁ (fail-τ-prepend (▷-timeout (e ⟶ P) (P′ ⊓ Q) refl tt0)
             (fail-τ-prepend (⊓-stepR P′ Q) fQ))
... | inj₂ (inj₂ dQ) =
      inj₂ (div-τ-prepend (▷-timeout (e ⟶ P) (P′ ⊓ Q) refl tt0)
             (div-τ-prepend (⊓-stepR P′ Q) dQ))

-- LHS ⊇F⊥ RHS : LHS recovers every RHS stable failure (map failures(RHS) → S ⊓ Q).
-- Recurse on RHS's big-step: the timeout τ (→ P′ ⊓ Q, then ⊓-failures→ splits into P′
-- [→ S via S's own timeout, then ⊓-failures←l] or Q [→ ⊓-failures←r]); the prefix event
-- (→ S offers it via ▷-ev-L, then ⊓-failures←l).  The ⟹-refl base is vacuous (RHS unstable).
RHS→LHS-fail : (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
    {s : List (Event√ R)} {X : Event√ R → Set ℓx} {W : PTree E (ExtI E) R}
  → ((e ⟶ P) ▷ (P′ ⊓ Q)) ⟹⟨ s ⟩ W → Refuses W X
  → failures (((e ⟶ P) ▷ P′) ⊓ Q) s X
RHS→LHS-fail e P P′ Q ⟹-refl (st , _) =
  ⊥-elim (stable-no-τ st (▷-timeout (e ⟶ P) (P′ ⊓ Q) refl tt0))
RHS→LHS-fail e P P′ Q (⟹-τ step rest) ref with ▷-τ-elim (e ⟶ P) (P′ ⊓ Q) step
... | inj₁ refl with ⊓-failures→ P′ Q (_ , rest , ref)
...   | inj₁ fP′ =
        ⊓-failures←l ((e ⟶ P) ▷ P′) Q
          (fail-τ-prepend (▷-timeout (e ⟶ P) P′ refl tt0) fP′)
...   | inj₂ fQ  = ⊓-failures←r ((e ⟶ P) ▷ P′) Q fQ
RHS→LHS-fail e P P′ Q (⟹-τ step rest) ref | inj₂ (P'' , Pτ , refl) =
  ⊥-elim (prefix-no-τ e P Pτ)
RHS→LHS-fail e P P′ Q (⟹-ev step rest) ref =
  ⊓-failures←l ((e ⟶ P) ▷ P′) Q
    (fail-ev-prepend (▷-ev-L {Q = P′} (▷-ev-elim (e ⟶ P) (P′ ⊓ Q) step)) (_ , rest , ref))

▷-⊓-ext-⊇F⊥ :
    (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
  → (((e ⟶ P) ▷ P′) ⊓ Q) ⊇F⊥ ((e ⟶ P) ▷ (P′ ⊓ Q))
▷-⊓-ext-⊇F⊥ e P P′ Q (inj₁ (W , reach , ref)) =
  inj₁ (RHS→LHS-fail e P P′ Q reach ref)
▷-⊓-ext-⊇F⊥ e P P′ Q (inj₂ d) = inj₂ (▷-⊓-ext-⊇D e P P′ Q d)

-- assemble the ⊆F⊥ similarly (the divergence summand routes through ⊆D, but ⊆F⊥ is
-- already total over both summands above; this wrapper keeps the four-component shape).

-------------------------------------------------------------------------------------
-- THE LAW (U13.22, ▷-⊓-ext): pair the two ⊇F⊥ and the two ⊇D refinements.
--   ≈FD = ((LHS⊇F⊥RHS, LHS⊇D RHS) , (RHS⊇F⊥LHS, RHS⊇D LHS)).
-------------------------------------------------------------------------------------

▷-⊓-ext-FD : ∀ {ℓr} {R : Set ℓr} {A : Set ℓ}
             (e : E A) (P : A → PTree E (ExtI E) R) (P′ Q : PTree E (ExtI E) R)
           → (((e ⟶ P) ▷ P′) ⊓ Q) ≈FD ((e ⟶ P) ▷ (P′ ⊓ Q))
▷-⊓-ext-FD e P P′ Q =
  (▷-⊓-ext-⊇F⊥ e P P′ Q , ▷-⊓-ext-⊇D e P P′ Q) ,
  (▷-⊓-ext-⊆F⊥ e P P′ Q , ▷-⊓-ext-⊆D e P P′ Q)

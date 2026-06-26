{-# OPTIONS --guardedness #-}

-- Parallel distribution over internal choice (T2.12 / U3.12, interface parallel):
--   P ∥[X] (Q ⊓ R) ≈FD (P ∥[X] Q) ⊓ (P ∥[X] R)
-- (also T2.3 alphabetised / T2.9 interleaving — the spike's single `Par A merge`
-- operator covers them; the instances `Par⊤-⊓-dist-FD` / `⦀-⊓-dist-FD` follow.)
--
-- FD-DIRECT, not a weak bisim: the ⊓-resolution τ fires at time 0 on the RHS, but the LHS
-- keeps `Q ⊓ R` UNRESOLVED while P evolves (P can do its outside-`A` events before the choice is
-- made) — the same initial-timing mismatch that makes □-⊓-dist and ;-dist-r FD-only.
--
-- The proof is PURE MODULAR ROUTING over the existing parallel decomposition machinery
-- (Par-failures-elim / Par-failures-intro-top, Par-reach-div / Par-div-intro) and the ⊓
-- union laws (⊓-failures→/←l/←r, ⊓-div→/←l/←r, ⊓-⟹-peel/-inl/-inr).  The KEY observation:
-- the ⊓-resolution is a √-free τ that does NOT touch the interleaving — so a run of the
-- operand `Q ⊓ R` is (after one τ) a run of Q or of R at the SAME de-interleaved sub-trace,
-- with the SAME residual / ParInter / stability.  So the failures/divergences at a fixed
-- de-interleaving (sP, sQR) of `Par P (Q⊓R)` is exactly the union of those of `Par P Q` and
-- `Par P R`.  This mirrors the ;-dist-r assembly (SeqDistR) shape exactly.

open import Level using (Level)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.ParallelIChoiceDist {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS      {E = E} {I = ExtI E}
open import Semantics.Failures {E = E} {I = ExtI E} using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.DRBisim  {E = E} {I = ExtI E} using (Diverges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; failures⊥; IsDivergence; div-extension-closed; _⊑F⊥_; _⊑D_; _≈FD_)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepL; ⊓-stepR; ⊓-τ-inv)
open import CSP.Laws.Traces.TraceLawsParallel E-≟ using (Mg; Par-τ-R)
open import Semantics.DRImpliesFD {E = E} {I = ExtI E} using (stable-no-τ)
open import CSP.Laws.FD.ParallelDivergence E-≟
  using (ParDivOut; Par-reach-div; Par-div-intro)
open import CSP.Laws.FD.ParallelFailures E-≟
  using (ParFailOut; Par-failures-elim; Par-failures-intro-top)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-⟹-peel; ⊓-⟹-inl; ⊓-⟹-inr; ⊓-failures→; ⊓-failures←l; ⊓-failures←r
        ; ⊓-div→; ⊓-div←l; ⊓-div←r)

private
  variable
    ℓ₁ ℓ₂ ℓr ℓx : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- the coinductive divergence of `Q ⊓ R` resolves on its first τ into a divergence of one
-- operand (needed when the Par divergence sits at the still-unresolved choice node).
-------------------------------------------------------------------------------------
⊓-Diverges→ : (Q R₀ : PTree E (ExtI E) R) → Diverges (Q ⊓ R₀) → Diverges Q ⊎ Diverges R₀
⊓-Diverges→ Q R₀ d with d .Diverges.next | d .Diverges.rest | ⊓-τ-inv Q R₀ (d .Diverges.step)
... | _ | dr | inj₁ refl = inj₁ dr
... | _ | dr | inj₂ refl = inj₂ dr

-------------------------------------------------------------------------------------
-- the law, stated for the general `Par A merge` (no merge-associativity needed).
-------------------------------------------------------------------------------------
module _ (A : EventSet) (merge : Mg R₁ R₂ R)
         (P : PTree E (ExtI E) R₁) (Q R₀ : PTree E (ExtI E) R₂) where
  private
    PQ  = Par A merge P Q
    PR  = Par A merge P R₀
    LHS = Par A merge P (Q ⊓ R₀)
    RHS = PQ ⊓ PR

  -- failures of an operand-side composite lift to the choice-operand composite (prepend
  -- the resolving τ to the operand reach via ⊓-⟹-inl/inr; everything else is preserved).
  fail-lift-l : {s : List (Event√ R)} {X : Event√ R → Set ℓx} → failures PQ s X → failures LHS s X
  fail-lift-l f with Par-failures-elim A merge f
  ... | sP , sQ , P* , Q* , rP , rQ , inter , stW , pr =
        Par-failures-intro-top A merge (sP , sQ , P* , Q* , rP , ⊓-⟹-inl Q R₀ rQ , inter , stW , pr)

  fail-lift-r : {s : List (Event√ R)} {X : Event√ R → Set ℓx} → failures PR s X → failures LHS s X
  fail-lift-r f with Par-failures-elim A merge f
  ... | sP , sR , P* , R* , rP , rR , inter , stW , pr =
        Par-failures-intro-top A merge (sP , sR , P* , R* , rP , ⊓-⟹-inr Q R₀ rR , inter , stW , pr)

  div-lift-l : {s : List (Event√ R)} → divergences PQ s → divergences LHS s
  div-lift-l d =
    subst (divergences LHS) (sym (d .IsDivergence.split))
      (div-extension-closed {t = d .IsDivergence.suffix}
        (go (Par-reach-div A merge P Q (d .IsDivergence.reach) (d .IsDivergence.divwit))))
    where
      go : {pre : List (Event√ R)} → ParDivOut A merge P Q pre → divergences LHS pre
      go (sP , sQ , P* , Q* , rP , rQ , inter , dd) =
        Par-div-intro A merge P (Q ⊓ R₀) rP (⊓-⟹-inl Q R₀ rQ) inter dd

  div-lift-r : {s : List (Event√ R)} → divergences PR s → divergences LHS s
  div-lift-r d =
    subst (divergences LHS) (sym (d .IsDivergence.split))
      (div-extension-closed {t = d .IsDivergence.suffix}
        (go (Par-reach-div A merge P R₀ (d .IsDivergence.reach) (d .IsDivergence.divwit))))
    where
      go : {pre : List (Event√ R)} → ParDivOut A merge P R₀ pre → divergences LHS pre
      go (sP , sR , P* , R* , rP , rR , inter , dd) =
        Par-div-intro A merge P (Q ⊓ R₀) rP (⊓-⟹-inr Q R₀ rR) inter dd

  -- divergences RHS → divergences LHS
  dist-D₁ : LHS ⊑D RHS
  dist-D₁ d with ⊓-div→ PQ PR d
  ... | inj₁ dPQ = div-lift-l dPQ
  ... | inj₂ dPR = div-lift-r dPR

  -- failures⊥ RHS → failures⊥ LHS
  dist-F⊥₁ : LHS ⊑F⊥ RHS
  dist-F⊥₁ (inj₁ f) with ⊓-failures→ PQ PR f
  ... | inj₁ fPQ = inj₁ (fail-lift-l fPQ)
  ... | inj₂ fPR = inj₁ (fail-lift-r fPR)
  dist-F⊥₁ (inj₂ d) = inj₂ (dist-D₁ d)

  -- divergences LHS → divergences RHS
  dist-D₂ : RHS ⊑D LHS
  dist-D₂ d =
    subst (divergences RHS) (sym (d .IsDivergence.split))
      (div-extension-closed {t = d .IsDivergence.suffix}
        (route (Par-reach-div A merge P (Q ⊓ R₀) (d .IsDivergence.reach) (d .IsDivergence.divwit))))
    where
      route : {pre : List (Event√ R)} → ParDivOut A merge P (Q ⊓ R₀) pre → divergences RHS pre
      route (sP , sQR , P* , M* , rP , rQR , inter , dd) with ⊓-⟹-peel Q R₀ rQR
      ... | inj₂ (inj₁ rQ) = ⊓-div←l PQ PR (Par-div-intro A merge P Q  rP rQ inter dd)
      ... | inj₂ (inj₂ rR) = ⊓-div←r PQ PR (Par-div-intro A merge P R₀ rP rR inter dd)
      route (sP , sQR , P* , M* , rP , rQR , inter , inj₁ dP*) | inj₁ (refl , refl) =
            ⊓-div←l PQ PR (Par-div-intro A merge P Q rP ⟹-refl inter (inj₁ dP*))
      route (sP , sQR , P* , M* , rP , rQR , inter , inj₂ d⊓) | inj₁ (refl , refl) with ⊓-Diverges→ Q R₀ d⊓
      ...   | inj₁ dQ = ⊓-div←l PQ PR (Par-div-intro A merge P Q  rP ⟹-refl inter (inj₂ dQ))
      ...   | inj₂ dR = ⊓-div←r PQ PR (Par-div-intro A merge P R₀ rP ⟹-refl inter (inj₂ dR))

  -- failures⊥ LHS → failures⊥ RHS
  dist-F⊥₂ : RHS ⊑F⊥ LHS
  dist-F⊥₂ (inj₁ f) with Par-failures-elim A merge f
  ... | sP , sQR , P* , M* , rP , rQR , inter , stW , pr with ⊓-⟹-peel Q R₀ rQR
  ...   | inj₁ (refl , refl) =
          ⊥-elim (stable-no-τ stW (Par-τ-R A merge P* (Q ⊓ R₀) (⊓-stepL Q R₀)))
  ...   | inj₂ (inj₁ rQ) =
          inj₁ (⊓-failures←l PQ PR
                 (Par-failures-intro-top A merge (sP , sQR , P* , M* , rP , rQ , inter , stW , pr)))
  ...   | inj₂ (inj₂ rR) =
          inj₁ (⊓-failures←r PQ PR
                 (Par-failures-intro-top A merge (sP , sQR , P* , M* , rP , rR , inter , stW , pr)))
  dist-F⊥₂ (inj₂ d) = inj₂ (dist-D₂ d)

  -- ∥-dist-r (T2.12):  P ∥[X] (Q ⊓ R) ≈FD (P ∥[X] Q) ⊓ (P ∥[X] R)
  Par-⊓-dist-FD : LHS ≈FD RHS
  Par-⊓-dist-FD = (dist-F⊥₁ , dist-D₁) , (dist-F⊥₂ , dist-D₂)

-------------------------------------------------------------------------------------
-- instances: ⊤-merge (Par⊤) and interleaving (⦀, cs = ∅)
-------------------------------------------------------------------------------------
Par⊤-⊓-dist-FD : (A : EventSet) (P Q R₀ : PTree E (ExtI E) (⊤ {ℓr}))
               → (P ∥⇘ A ⇙ (Q ⊓ R₀)) ≈FD ((P ∥⇘ A ⇙ Q) ⊓ (P ∥⇘ A ⇙ R₀))
Par⊤-⊓-dist-FD A P Q R₀ = Par-⊓-dist-FD A (λ _ _ → tt) P Q R₀

⦀-⊓-dist-FD : (P Q R₀ : PTree E (ExtI E) (⊤ {ℓr})) → (P ⦀ (Q ⊓ R₀)) ≈FD ((P ⦀ Q) ⊓ (P ⦀ R₀))
⦀-⊓-dist-FD P Q R₀ = Par⊤-⊓-dist-FD ∅ES P Q R₀

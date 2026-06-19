{-# OPTIONS --guardedness #-}

-- Internal choice distributes over external choice (TPC 1.13 / UCS 2.13):
--   P ⊓ (Q □ S) = (P ⊓ Q) □ (P ⊓ S).
-- Marked ^* in the summary (not valid in EVERY model of the hierarchy) but TRUE in the
-- failures-divergences model N / Mᶠᵈ that we work in — which is what this proves.
--
-- This is the "other" distribution (⊓ over □), independent of the proved □-⊓-dist
-- (□ over ⊓): the naive algebraic expansion via □-⊓-dist introduces P□Q, P□S, Q□S terms
-- that don't cancel.  So it is FD-DIRECT, routing through the ⊓ failures/divergence UNION
-- decomposition and the □ failures []-conjunction / cons-disjunction split:
--   failures(P ⊓ X)        = failures P  ⊎ failures X          (⊓ = union)
--   failures(A □ B) []     = failures A [] × failures B []     (□ nil = conjunction)
--   failures(A □ B) (e∷s)  = failures A   ⊎ failures B  (cons) (□ cons = disjunction)
-- The []-case of the ⊐ direction is the ⊎/× distributivity (A⊎B)×(A⊎C) → A ⊎ (B×C).

open import Level using (Level)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.FD.IChoiceEChoiceDist {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (_⊓_; _□_)
open import Semantics.LTS      {E = E} {I = ExtI E} using (Event√)
open import Semantics.Failures {E = E} {I = ExtI E} using (failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; failures⊥; _⊑F⊥_; _⊑D_; _≈FD_)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-failures→; ⊓-failures←l; ⊓-failures←r; ⊓-div→; ⊓-div←l; ⊓-div←r)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (□-failures-elim; □-div-elim; □-div-intro-L; □-div-intro-R)
open import CSP.Laws.FD.ExtChoiceAssoc E-≟
  using (□-fail-nil-→; □-fail-nil-←; □-fail-intro-cons-L; □-fail-intro-cons-R)

private
  variable
    ℓr ℓx : Level
    R : Set ℓr

module _ ⦃ _ : DecEq R ⦄ (P Q S : PTree E (ExtI E) R) where

  -- failures(P ⊓ (Q □ S))  ⊆  failures((P ⊓ Q) □ (P ⊓ S))
  dist-fail-→ : {s : List (Event√ R)} {X : Event√ R → Set ℓx}
              → failures (P ⊓ (Q □ S)) s X → failures ((P ⊓ Q) □ (P ⊓ S)) s X
  dist-fail-→ {s = []} f with ⊓-failures→ P (Q □ S) f
  ... | inj₁ fP = □-fail-nil-← (P ⊓ Q) (P ⊓ S) (⊓-failures←l P Q fP) (⊓-failures←l P S fP)
  ... | inj₂ (W , reach , ref) with □-fail-nil-→ Q S reach ref
  ...   | fQ , fS = □-fail-nil-← (P ⊓ Q) (P ⊓ S) (⊓-failures←r P Q fQ) (⊓-failures←r P S fS)
  dist-fail-→ {s = e ∷ s'} f with ⊓-failures→ P (Q □ S) f
  ... | inj₁ fP with ⊓-failures←l P Q fP
  ...   | (_ , rpq , rfpq) = □-fail-intro-cons-L (P ⊓ Q) (P ⊓ S) rpq rfpq
  dist-fail-→ {s = e ∷ s'} f | inj₂ (W , reach , ref) with □-failures-elim Q S reach ref
  ...   | inj₁ fQ with ⊓-failures←r P Q fQ
  ...     | (_ , rpq , rfpq) = □-fail-intro-cons-L (P ⊓ Q) (P ⊓ S) rpq rfpq
  dist-fail-→ {s = e ∷ s'} f | inj₂ (W , reach , ref) | inj₂ fS with ⊓-failures←r P S fS
  ...     | (_ , rps , rfps) = □-fail-intro-cons-R (P ⊓ Q) (P ⊓ S) rps rfps

  -- failures((P ⊓ Q) □ (P ⊓ S))  ⊆  failures(P ⊓ (Q □ S))
  dist-fail-← : {s : List (Event√ R)} {X : Event√ R → Set ℓx}
              → failures ((P ⊓ Q) □ (P ⊓ S)) s X → failures (P ⊓ (Q □ S)) s X
  dist-fail-← {s = []} (W , reach , ref) with □-fail-nil-→ (P ⊓ Q) (P ⊓ S) reach ref
  ... | fPQ , fPS with ⊓-failures→ P Q fPQ | ⊓-failures→ P S fPS
  ...   | inj₁ fP | _       = ⊓-failures←l P (Q □ S) fP
  ...   | inj₂ _  | inj₁ fP = ⊓-failures←l P (Q □ S) fP
  ...   | inj₂ fQ | inj₂ fS = ⊓-failures←r P (Q □ S) (□-fail-nil-← Q S fQ fS)
  dist-fail-← {s = e ∷ s'} (W , reach , ref) with □-failures-elim (P ⊓ Q) (P ⊓ S) reach ref
  ... | inj₁ fPQ with ⊓-failures→ P Q fPQ
  ...   | inj₁ fP             = ⊓-failures←l P (Q □ S) fP
  ...   | inj₂ (_ , rq , rfq) = ⊓-failures←r P (Q □ S) (□-fail-intro-cons-L Q S rq rfq)
  dist-fail-← {s = e ∷ s'} (W , reach , ref) | inj₂ fPS with ⊓-failures→ P S fPS
  ...   | inj₁ fP             = ⊓-failures←l P (Q □ S) fP
  ...   | inj₂ (_ , rs , rfs) = ⊓-failures←r P (Q □ S) (□-fail-intro-cons-R Q S rs rfs)

  -- divergences (pure ⊎-routing through ⊓/□ union)
  dist-div-→ : {s : List (Event√ R)}
             → divergences (P ⊓ (Q □ S)) s → divergences ((P ⊓ Q) □ (P ⊓ S)) s
  dist-div-→ d with ⊓-div→ P (Q □ S) d
  ... | inj₁ dP = □-div-intro-L {P = P ⊓ Q} {Q = P ⊓ S} (⊓-div←l P Q dP)
  ... | inj₂ dQS with □-div-elim {P = Q} {Q = S} dQS
  ...   | inj₁ dQ = □-div-intro-L {P = P ⊓ Q} {Q = P ⊓ S} (⊓-div←r P Q dQ)
  ...   | inj₂ dS = □-div-intro-R {P = P ⊓ Q} {Q = P ⊓ S} (⊓-div←r P S dS)

  dist-div-← : {s : List (Event√ R)}
             → divergences ((P ⊓ Q) □ (P ⊓ S)) s → divergences (P ⊓ (Q □ S)) s
  dist-div-← d with □-div-elim {P = P ⊓ Q} {Q = P ⊓ S} d
  ... | inj₁ dPQ with ⊓-div→ P Q dPQ
  ...   | inj₁ dP = ⊓-div←l P (Q □ S) dP
  ...   | inj₂ dQ = ⊓-div←r P (Q □ S) (□-div-intro-L {P = Q} {Q = S} dQ)
  dist-div-← d | inj₂ dPS with ⊓-div→ P S dPS
  ...   | inj₁ dP = ⊓-div←l P (Q □ S) dP
  ...   | inj₂ dS = ⊓-div←r P (Q □ S) (□-div-intro-R {P = Q} {Q = S} dS)

  dist-⊑F⊥-← : (P ⊓ (Q □ S)) ⊑F⊥ ((P ⊓ Q) □ (P ⊓ S))
  dist-⊑F⊥-← (inj₁ f) = inj₁ (dist-fail-← f)
  dist-⊑F⊥-← (inj₂ d) = inj₂ (dist-div-← d)

  dist-⊑F⊥-→ : ((P ⊓ Q) □ (P ⊓ S)) ⊑F⊥ (P ⊓ (Q □ S))
  dist-⊑F⊥-→ (inj₁ f) = inj₁ (dist-fail-→ f)
  dist-⊑F⊥-→ (inj₂ d) = inj₂ (dist-div-→ d)

  ⊓-□-dist-FD : (P ⊓ (Q □ S)) ≈FD ((P ⊓ Q) □ (P ⊓ S))
  ⊓-□-dist-FD = (dist-⊑F⊥-← , dist-div-←) , (dist-⊑F⊥-→ , dist-div-→)

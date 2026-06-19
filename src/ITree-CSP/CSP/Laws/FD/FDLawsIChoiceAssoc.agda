{-# OPTIONS --guardedness #-}

-- ⊓-associativity is NEITHER a strong nor a weak bisimulation law (the intermediate
-- (P⊓Q) node has no bisimilar partner on the P⊓(Q⊓R) side).  But in the FD model it
-- is trivial: failures and divergences of an internal choice are the UNION of the
-- operands', and union is associative.  This module proves the ⊓ decomposition
-- lemmas (reusable) and assembles (P ⊓ Q) ⊓ R ≈FD P ⊓ (Q ⊓ R).
--
-- This demonstrates the second half of the strategy: when ≈DR is unavailable, prove
-- the law directly on FD= via failures/divergences set-equality.

open import Level using (Level; Lift; lift)
open import Data.Nat using (ℕ)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _++_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; _×_; proj₁; proj₂; Σ-syntax)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.FDLawsIChoiceAssoc {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E}
open import Semantics.DRBisim             {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Refusals            {E = E} {I = ExtI E} using (Refuses)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (IsDivergence; divergences; failures⊥; _⊑F⊥_; _⊑D_; _⊑FD_; _≈FD_)
open import CSP.Laws.Bisim.Laws     E-≟ using (⊓-stepL; ⊓-stepR; ⊓-τ-inv)

private
  variable
    ℓr ℓx : Level
    R : Set ℓr

-------------------------------------------------------------------------------------
-- An internal choice is never stable, and every big-step out of it either is the
-- empty (refl) step or has peeled off a τ into one operand.
-------------------------------------------------------------------------------------

⊓-unstable : (P Q : PTree E (ExtI E) R) → ¬ isStable (P ⊓ Q)
⊓-unstable P Q st = case st (Lift ℓ (Fin 2) , fin) (lift fzero) of λ ()

⊓-⟹-peel : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)} {W : PTree E (ExtI E) R}
          → (P ⊓ Q) ⟹⟨ s ⟩ W
          → ((P ⊓ Q) ≡ W × s ≡ []) ⊎ (P ⟹⟨ s ⟩ W) ⊎ (Q ⟹⟨ s ⟩ W)
⊓-⟹-peel P Q ⟹-refl              = inj₁ (refl , refl)
⊓-⟹-peel P Q (⟹-τ step rest) with ⊓-τ-inv P Q step
... | inj₁ refl = inj₂ (inj₁ rest)
... | inj₂ refl = inj₂ (inj₂ rest)
⊓-⟹-peel P Q (⟹-ev (sRet ()) _)
⊓-⟹-peel P Q (⟹-ev (sVis refl ()) _)

-- prepend the choosing τ to lift an operand's big-step into the choice's
⊓-⟹-inl : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)} {W : PTree E (ExtI E) R}
        → P ⟹⟨ s ⟩ W → (P ⊓ Q) ⟹⟨ s ⟩ W
⊓-⟹-inl P Q pw = ⟹-τ (⊓-stepL P Q) pw

⊓-⟹-inr : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)} {W : PTree E (ExtI E) R}
        → Q ⟹⟨ s ⟩ W → (P ⊓ Q) ⟹⟨ s ⟩ W
⊓-⟹-inr P Q qw = ⟹-τ (⊓-stepR P Q) qw

-------------------------------------------------------------------------------------
-- Failures of ⊓ = union of failures (the choice itself, being unstable, contributes
-- no refusal).
-------------------------------------------------------------------------------------

⊓-failures→ : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)} {X : Event√ R → Set ℓx}
            → failures (P ⊓ Q) s X → failures P s X ⊎ failures Q s X
⊓-failures→ P Q (W , pw , ref) with ⊓-⟹-peel P Q pw
... | inj₁ (eqW , _)  = ⊥-elim (⊓-unstable P Q (subst isStable (sym eqW) (proj₁ ref)))
... | inj₂ (inj₁ pw′) = inj₁ (W , pw′ , ref)
... | inj₂ (inj₂ pw′) = inj₂ (W , pw′ , ref)

⊓-failures←l : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)} {X : Event√ R → Set ℓx}
             → failures P s X → failures (P ⊓ Q) s X
⊓-failures←l P Q (W , pw , ref) = W , ⊓-⟹-inl P Q pw , ref

⊓-failures←r : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)} {X : Event√ R → Set ℓx}
             → failures Q s X → failures (P ⊓ Q) s X
⊓-failures←r P Q (W , qw , ref) = W , ⊓-⟹-inr P Q qw , ref

-------------------------------------------------------------------------------------
-- Divergences of ⊓ = union of divergences.
-------------------------------------------------------------------------------------

⊓-div→ : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)}
       → divergences (P ⊓ Q) s → divergences P s ⊎ divergences Q s
⊓-div→ P Q {s = s} d with ⊓-⟹-peel P Q (d .IsDivergence.reach)
... | inj₂ (inj₁ reachP) =
        inj₁ (record { prefix  = d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
                     ; split   = d .IsDivergence.split  ; witness = d .IsDivergence.witness
                     ; reach   = reachP                 ; divwit  = d .IsDivergence.divwit })
... | inj₂ (inj₂ reachQ) =
        inj₂ (record { prefix  = d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
                     ; split   = d .IsDivergence.split  ; witness = d .IsDivergence.witness
                     ; reach   = reachQ                 ; divwit  = d .IsDivergence.divwit })
... | inj₁ (eqW , _) with subst Diverges (sym eqW) (d .IsDivergence.divwit)
...   | dPQ with ⊓-τ-inv P Q (dPQ .Diverges.step)
...     | inj₁ eqP = inj₁ (record { prefix = [] ; suffix = s ; split = refl
                                  ; witness = P ; reach = ⟹-refl
                                  ; divwit = subst Diverges eqP (dPQ .Diverges.rest) })
...     | inj₂ eqQ = inj₂ (record { prefix = [] ; suffix = s ; split = refl
                                  ; witness = Q ; reach = ⟹-refl
                                  ; divwit = subst Diverges eqQ (dPQ .Diverges.rest) })

⊓-div←l : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)}
        → divergences P s → divergences (P ⊓ Q) s
⊓-div←l P Q d = record
  { prefix  = d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split   = d .IsDivergence.split  ; witness = d .IsDivergence.witness
  ; reach   = ⊓-⟹-inl P Q (d .IsDivergence.reach) ; divwit = d .IsDivergence.divwit }

⊓-div←r : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)}
        → divergences Q s → divergences (P ⊓ Q) s
⊓-div←r P Q d = record
  { prefix  = d .IsDivergence.prefix ; suffix = d .IsDivergence.suffix
  ; split   = d .IsDivergence.split  ; witness = d .IsDivergence.witness
  ; reach   = ⊓-⟹-inr P Q (d .IsDivergence.reach) ; divwit = d .IsDivergence.divwit }

-------------------------------------------------------------------------------------
-- failures⊥ = failures ⊎ divergences, so the same union split lifts.
-------------------------------------------------------------------------------------

⊓-failures⊥→ : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)} {B : Event√ R → Set ℓr}
             → failures⊥ (P ⊓ Q) s B → failures⊥ P s B ⊎ failures⊥ Q s B
⊓-failures⊥→ P Q (inj₁ f) with ⊓-failures→ P Q f
... | inj₁ fP = inj₁ (inj₁ fP)
... | inj₂ fQ = inj₂ (inj₁ fQ)
⊓-failures⊥→ P Q (inj₂ d) with ⊓-div→ P Q d
... | inj₁ dP = inj₁ (inj₂ dP)
... | inj₂ dQ = inj₂ (inj₂ dQ)

⊓-failures⊥←l : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)} {B : Event√ R → Set ℓr}
              → failures⊥ P s B → failures⊥ (P ⊓ Q) s B
⊓-failures⊥←l P Q (inj₁ fP) = inj₁ (⊓-failures←l P Q fP)
⊓-failures⊥←l P Q (inj₂ dP) = inj₂ (⊓-div←l P Q dP)

⊓-failures⊥←r : (P Q : PTree E (ExtI E) R) {s : List (Event√ R)} {B : Event√ R → Set ℓr}
              → failures⊥ Q s B → failures⊥ (P ⊓ Q) s B
⊓-failures⊥←r P Q (inj₁ fQ) = inj₁ (⊓-failures←r P Q fQ)
⊓-failures⊥←r P Q (inj₂ dQ) = inj₂ (⊓-div←r P Q dQ)

-------------------------------------------------------------------------------------
-- Associativity by union-reassociation.
-------------------------------------------------------------------------------------

module _ (P Q S : PTree E (ExtI E) R) where

  -- failures⊥ refinement, both directions
  assoc-⊑F⊥-RL : ((P ⊓ Q) ⊓ S) ⊑F⊥ (P ⊓ (Q ⊓ S))
  assoc-⊑F⊥-RL f with ⊓-failures⊥→ P (Q ⊓ S) f
  ... | inj₁ fP   = ⊓-failures⊥←l (P ⊓ Q) S (⊓-failures⊥←l P Q fP)
  ... | inj₂ fQS with ⊓-failures⊥→ Q S fQS
  ...   | inj₁ fQ = ⊓-failures⊥←l (P ⊓ Q) S (⊓-failures⊥←r P Q fQ)
  ...   | inj₂ fS = ⊓-failures⊥←r (P ⊓ Q) S fS

  assoc-⊑F⊥-LR : (P ⊓ (Q ⊓ S)) ⊑F⊥ ((P ⊓ Q) ⊓ S)
  assoc-⊑F⊥-LR f with ⊓-failures⊥→ (P ⊓ Q) S f
  ... | inj₂ fS   = ⊓-failures⊥←r P (Q ⊓ S) (⊓-failures⊥←r Q S fS)
  ... | inj₁ fPQ with ⊓-failures⊥→ P Q fPQ
  ...   | inj₁ fP = ⊓-failures⊥←l P (Q ⊓ S) fP
  ...   | inj₂ fQ = ⊓-failures⊥←r P (Q ⊓ S) (⊓-failures⊥←l Q S fQ)

  assoc-⊑D-RL : ((P ⊓ Q) ⊓ S) ⊑D (P ⊓ (Q ⊓ S))
  assoc-⊑D-RL d with ⊓-div→ P (Q ⊓ S) d
  ... | inj₁ dP   = ⊓-div←l (P ⊓ Q) S (⊓-div←l P Q dP)
  ... | inj₂ dQS with ⊓-div→ Q S dQS
  ...   | inj₁ dQ = ⊓-div←l (P ⊓ Q) S (⊓-div←r P Q dQ)
  ...   | inj₂ dS = ⊓-div←r (P ⊓ Q) S dS

  assoc-⊑D-LR : (P ⊓ (Q ⊓ S)) ⊑D ((P ⊓ Q) ⊓ S)
  assoc-⊑D-LR d with ⊓-div→ (P ⊓ Q) S d
  ... | inj₂ dS   = ⊓-div←r P (Q ⊓ S) (⊓-div←r Q S dS)
  ... | inj₁ dPQ with ⊓-div→ P Q dPQ
  ...   | inj₁ dP = ⊓-div←l P (Q ⊓ S) dP
  ...   | inj₂ dQ = ⊓-div←r P (Q ⊓ S) (⊓-div←l Q S dQ)

  ⊓-assoc-FD : ((P ⊓ Q) ⊓ S) ≈FD (P ⊓ (Q ⊓ S))
  ⊓-assoc-FD = (assoc-⊑F⊥-RL , assoc-⊑D-RL) , (assoc-⊑F⊥-LR , assoc-⊑D-LR)

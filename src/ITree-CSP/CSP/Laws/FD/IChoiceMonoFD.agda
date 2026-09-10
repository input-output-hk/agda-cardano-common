{-# OPTIONS --guardedness #-}

-- FACT-SHAPED `⊑FD`-MONOTONICITY for internal choice: `⊓-mono-⊑FD` takes two `⊑FD`
-- FACTS and returns a `⊑FD` fact.  This is the TRUE PRECONGRUENCE for `⊓`.  The
-- replicated folds `⨅⁺-mono-⊑FD` / `⨅Fin-mono-⊑FD` (bottom of the file) are plain
-- inductions over it, and inherit exactly its (empty) postulate set.
--
-- WHY A SEPARATE LAW (the three shapes of "monotonicity" in this repo):
--
--   1. `FSim → FSim`   (e.g. `⊓-fsim`, `□-fsim`, `Hide-fsim`) — the congruence.  This is
--      what composes an FSim tower, and it is essential.
--   2. `⊑FD → ⊑FD`     (THIS module, `Par-mono-⊑FD`, `⟶₀-mono-⊑FD`, `loop0-mono-⊑FD`) —
--      the true precongruence, and the VALUABLE shape.  A `⊑FD` premise can come from
--      ANY source: a hand-built bisimulation, a denotational argument, an earlier
--      refinement step, or a cashed-out `FSim`.  It composes freely.
--   3. `FSim → ⊑FD`    (cash-out wrappers) — `fsim→⊑FD (⊓-fsim …)`, a one-liner every
--      caller can write.  It adds a NAME, not power, and since `⊑FD → FSim`
--      completeness is out of scope (`CSP/Laws_status.md:1104`) it can NEVER consume a
--      `⊑FD` fact.  A shape-3 `⊓-mono-⊑FD` previously lived in
--      `CSP.Laws.FSim.IChoiceCong`; it was RETIRED in favour of the law below, which is
--      strictly stronger (feed it `fsim→⊑FD (⊓-fsim …)` to recover the old use).  Please
--      do not re-add it — keep `⊓-fsim` for towers and this law for facts.
--
-- WHY IT IS CHEAP: `⊓`'s failures and divergences are exactly the UNION of the two
-- operands' (the `⊓` root itself is unstable, so it contributes no refusal of its own).
-- The whole proof is therefore "transfer each side of a union through its hypothesis",
-- reusing the union decomposition/introduction lemmas already proved for
-- `⊓`-associativity in `CSP.Laws.FD.FDLawsIChoiceAssoc`.  Contrast `Par-mono-⊑FD`
-- (`CSP.Laws.FD.ParallelMonoFD`), whose 700 lines exist because parallel failures need
-- ban-set carving and trace re-interleaving.
--
-- Layout mirrors `ParallelMonoFD`: the `⊇F⊥` and `⊇D` halves are proved separately and
-- then paired (`_⊑FD_ = (_⊇F⊥_) × (_⊇D_)`).
--
-- POSTULATES: none local.  Inherited: NONE — `FDLawsIChoiceAssoc`'s ⊓ union lemmas and
-- `CSP.Laws.Bisim.Laws`'s `⊓-τ-inv`/`⊓-stepL`/`⊓-stepR` are all constructive.

open import Level using (Level)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
  renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.FD.IChoiceMonoFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_⊇F⊥_; _⊇D_; _⊑FD_)
open import CSP.Laws.FD.FDLawsIChoiceAssoc E-≟
  using (⊓-failures⊥→; ⊓-failures⊥←l; ⊓-failures⊥←r; ⊓-div→; ⊓-div←l; ⊓-div←r)

private
  variable
    ℓr : Level
    R : Set ℓr

-------------------------------------------------------------------------------------
-- The two halves, then the headline.
-------------------------------------------------------------------------------------

-- ⊓ is ⊇F⊥-monotone in both operands: a divergence-strict failure of the target choice
-- belongs to one target operand, transfers through that operand's hypothesis, and is
-- re-injected into the source choice on the same side
⊓-mono-⊇F⊥ : {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
           → P₁ ⊇F⊥ P₂ → Q₁ ⊇F⊥ Q₂ → (P₁ ⊓ Q₁) ⊇F⊥ (P₂ ⊓ Q₂)
⊓-mono-⊇F⊥ {P₁ = P₁} {P₂ = P₂} {Q₁ = Q₁} {Q₂ = Q₂} fP fQ f
  with ⊓-failures⊥→ P₂ Q₂ f
... | inj₁ fP₂ = ⊓-failures⊥←l P₁ Q₁ (fP fP₂)
... | inj₂ fQ₂ = ⊓-failures⊥←r P₁ Q₁ (fQ fQ₂)

-- ⊓ is ⊇D-monotone in both operands: same union split, on divergences
⊓-mono-⊇D : {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
          → P₁ ⊇D P₂ → Q₁ ⊇D Q₂ → (P₁ ⊓ Q₁) ⊇D (P₂ ⊓ Q₂)
⊓-mono-⊇D {P₁ = P₁} {P₂ = P₂} {Q₁ = Q₁} {Q₂ = Q₂} dP dQ d
  with ⊓-div→ P₂ Q₂ d
... | inj₁ dP₂ = ⊓-div←l P₁ Q₁ (dP dP₂)
... | inj₂ dQ₂ = ⊓-div←r P₁ Q₁ (dQ dQ₂)

-- HEADLINE: internal choice is a ⊑FD-PRECONGRUENCE — `⊑FD` facts in, `⊑FD` fact out,
-- unconditionally (no divergence-freedom, no alphabet, no König side condition)
⊓-mono-⊑FD : {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
           → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂ → (P₁ ⊓ Q₁) ⊑FD (P₂ ⊓ Q₂)
⊓-mono-⊑FD (fP , dP) (fQ , dQ) = ⊓-mono-⊇F⊥ fP fQ , ⊓-mono-⊇D dP dQ

-------------------------------------------------------------------------------------
-- The REPLICATED-INTERNAL-CHOICE folds, FACT-SHAPED.
--
-- ⚠ BOTH FOLDS ARE NON-EMPTY, so — unlike `⦀Fin`/`⦀⋆` (`CSP.Laws.FD.ParallelMonoFD`,
-- Layer 8) and `□Fin`/`□⋆` (`CSP.Laws.FD.ExtChoiceMonoFD`, Layer 3), whose base cases
-- are the units `Skip`/`Stop` and therefore need `⊑FD-refl` — these bottom out on an
-- OPERAND, so the base case is just the corresponding hypothesis and `⊑FD-refl` is
-- never used:
--   `⨅⁺ P []       = P`            (head+list, `CSP.Operators`:137)
--   `⨅⁺ P (Q ∷ qs) = P ⊓ ⨅⁺ Q qs`  — note the recursion RE-HEADS on the list's head,
--                                    so the induction consumes the `Pointwise` cell
--                                    and passes it on as the new head hypothesis
--   `⨅Fin zero    f = f fzero`     (`Fin (suc n)`-indexed, `CSP.Operators`:143)
-- No side condition, since `⊓-mono-⊑FD` above has none.
-------------------------------------------------------------------------------------

-- `⨅⁺` is ⊑FD-monotone in its head and (pointwise) in its tail list, unconditionally
⨅⁺-mono-⊑FD : {P₁ P₂ : PTree E (ExtI E) R} {Ps Qs : List (PTree E (ExtI E) R)}
            → P₁ ⊑FD P₂ → Pointwise _⊑FD_ Ps Qs → ⨅⁺ P₁ Ps ⊑FD ⨅⁺ P₂ Qs
⨅⁺-mono-⊑FD hP []ᵖ       = hP
⨅⁺-mono-⊑FD hP (q ∷ᵖ qs) = ⊓-mono-⊑FD hP (⨅⁺-mono-⊑FD q qs)

-- `⨅Fin` is ⊑FD-monotone in its `Fin (suc n)`-indexed family, pointwise and
-- unconditionally
⨅Fin-mono-⊑FD : {n : ℕ} {f g : Fin (suc n) → PTree E (ExtI E) R}
              → (∀ i → f i ⊑FD g i) → ⨅Fin n f ⊑FD ⨅Fin n g
⨅Fin-mono-⊑FD {n = zero}  h = h fzero
⨅Fin-mono-⊑FD {n = suc n} h = ⊓-mono-⊑FD (h fzero) (⨅Fin-mono-⊑FD (λ i → h (fsuc i)))

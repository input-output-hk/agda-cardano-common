{-# OPTIONS --guardedness #-}

-- FACT-SHAPED `⊑FD`-MONOTONICITY for EXTERNAL CHOICE: `□-mono-⊑FD` takes two `⊑FD`
-- FACTS and returns a `⊑FD` fact.  This is the TRUE PRECONGRUENCE for `_□_`, monotone in
-- BOTH operands, unconditionally (no divergence-freedom, no `Sep`-style separation, no
-- König side condition beyond what `□`'s own divergence theory already inherits), plus
-- the replicated folds `□Fin-mono-⊑FD` / `□⋆-mono-⊑FD` (Layer 3).
--
-- WHY A SEPARATE LAW: see `CSP.Laws.FD.IChoiceMonoFD`'s header for the three-shape
-- taxonomy (`FSim → FSim` congruence / `⊑FD → ⊑FD` precongruence / `FSim → ⊑FD`
-- cash-out).  The shape-3 `□-mono-⊑FD` that used to live in
-- `CSP.Laws.FSim.ExtChoiceCong` was RETIRED in favour of the law below, which is
-- strictly stronger (write `fsim→⊑FD (□-fsim … …)` to recover the old use).  Keep
-- `□-fsim` for FSim towers and this law for facts.
--
-- PROOF ARCHITECTURE — pure ROUTING through the `□` FD theory that `ExtChoiceFD` and
-- `ExtChoiceAssoc` already built for associativity/commutativity.  Nothing new is
-- proved here; the only content is the observation that the SAME decompositions that
-- make `□-comm-fail` / `□-assoc-fail` work also make monotonicity work, once the two
-- transfer arms are allowed to fall into the divergence summand.
--
--   ⊇D  half : `□-div-elim` splits a target divergence onto ONE operand (`□`'s
--              divergences are the UNION of the operands'); transfer it through that
--              operand's `⊇D` and re-inject with `□-div-intro-L` / `-R`.
--
--   ⊇F⊥ half : the trace decides the shape, exactly as in `□-comm-fail`.
--              • `s ≡ []`  — `□`'s nil-failures are the INTERSECTION of the operands'
--                (a stable `P □ Q` refusing `X` needs BOTH operands to refuse `X`, since
--                `mergeVis` offers whatever either offers).  So `□-fail-nil-→` projects
--                the target refusal onto BOTH targets, each is transferred through its
--                own `⊇F⊥`, and `□-fail-nil-←` re-joins the two refined nil-failures.
--                If EITHER transfer returns a divergence instead, the whole composite
--                diverges at `[]` (`□-div-intro-L`/`-R`) and we land in the `failures⊥`
--                divergence summand.
--              • `s ≡ e ∷ s′` — the leading event has already committed to one operand,
--                so the intersection collapses to a union: `□-failures-elim` picks the
--                side, that side's `⊇F⊥` transfers the failure, and
--                `□-fail-intro-cons-L`/`-R` lifts it back (leading τ's via
--                `□-fail-τ-pre-L/R`, the event via `□-ev-toL/toR` — all internal to
--                `ExtChoiceAssoc`).
--
-- The `▷` escape that `□`'s `ret`-handling creates (`□-slide-RQ` / `□-slide-PR`) needs no
-- attention HERE: `□-reach-div` / `□-failures-elim` are already mutually recursive with
-- their `▷` analogues (`▷-reach-div` / `▷-failures-elim`), so the escape is absorbed
-- inside the elimination and both eliminations land back on the two operands.
--
-- POSTULATES: ZERO local.  INHERITED: `□-Diverges→` and `▷-Diverges→` (both
-- `CSP.Laws.FD.ExtChoiceDivergence`), reached through `□-div-elim` / `□-reach-div` /
-- `□-div-intro-L/R`; each is certified derivable from a single `dne` in
-- `CSP.Laws.ClassicalFromLEM`.  This inheritance is UNAVOIDABLE for any `□` law that
-- touches divergences — `□`'s divergence projection is a genuine König step (unlike
-- throw's structural `Θ-Diverges→`, see `CSP.Laws.FD.ThrowMonoFD`), because a `P □ Q`
-- τ-path can alternate between the two operands forever without either diverging on its
-- own trace prefix.  The FAILURES half additionally reaches `offer-LEM` through
-- `ExtChoiceAssoc`.  `agda --safe` therefore fails on the inherited postulates only.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Binary.Pointwise using (Pointwise)
  renaming ([] to []ᵖ; _∷_ to _∷ᵖ_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.FD.ExtChoiceMonoFD {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} using (Event√)
open import Semantics.Failures            {E = E} {I = ExtI E} using (failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_⊇F⊥_; _⊇D_; _⊑FD_; failures⊥; divergences; ⊑FD-refl)
open import CSP.Laws.FD.ExtChoiceFD E-≟
  using (□-failures-elim; □-div-elim; □-div-intro-L; □-div-intro-R)
open import CSP.Laws.FD.ExtChoiceAssoc E-≟
  using (□-fail-nil-→; □-fail-nil-←; □-fail-intro-cons-L; □-fail-intro-cons-R)

private
  variable
    ℓr : Level
    R : Set ℓr

-------------------------------------------------------------------------------------
-- Layer 1 : the two halves.
-------------------------------------------------------------------------------------

-- `□` is ⊇D-monotone in both operands: `□`'s divergences are the UNION of the operands',
-- so a target divergence belongs to one target operand, transfers through that operand's
-- `⊇D`, and is re-injected into the source choice on the same side
□-mono-⊇D : ⦃ _ : DecEq R ⦄ {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
          → P₁ ⊇D P₂ → Q₁ ⊇D Q₂ → (P₁ □ Q₁) ⊇D (P₂ □ Q₂)
□-mono-⊇D {P₁ = P₁} {P₂ = P₂} {Q₁ = Q₁} {Q₂ = Q₂} dP dQ d
  with □-div-elim {P = P₂} {Q = Q₂} d
... | inj₁ dP₂ = □-div-intro-L {P = P₁} {Q = Q₁} (dP dP₂)
... | inj₂ dQ₂ = □-div-intro-R {P = P₁} {Q = Q₁} (dQ dQ₂)

-- transfer a target STABLE failure of `P₂ □ Q₂`.  At `[]` the refusal is the operands'
-- INTERSECTION (project to both, transfer both, re-join); at `e ∷ s′` the leading event
-- has committed to one operand, so it is a UNION (pick the side, transfer, lift back).
-- Either arm may return a divergence, which re-injects into the `failures⊥` summand.
□-mono-fail : ⦃ _ : DecEq R ⦄ (P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R)
            → P₁ ⊇F⊥ P₂ → Q₁ ⊇F⊥ Q₂
            → {s : List (Event√ R)} {X : Event√ R → Set ℓr}
            → failures (P₂ □ Q₂) s X → failures⊥ (P₁ □ Q₁) s X
-- [] : the nil-failure conjunction
□-mono-fail P₁ P₂ Q₁ Q₂ fP fQ {s = []} (W , reach , ref)
  with □-fail-nil-→ P₂ Q₂ reach ref
... | fP₂ , fQ₂ with fP (inj₁ fP₂) | fQ (inj₁ fQ₂)
...   | inj₁ fP₁ | inj₁ fQ₁ = inj₁ (□-fail-nil-← P₁ Q₁ fP₁ fQ₁)
...   | inj₁ _   | inj₂ dQ₁ = inj₂ (□-div-intro-R {P = P₁} {Q = Q₁} dQ₁)
...   | inj₂ dP₁ | _        = inj₂ (□-div-intro-L {P = P₁} {Q = Q₁} dP₁)
-- e ∷ s′ : the committed-operand disjunction
□-mono-fail P₁ P₂ Q₁ Q₂ fP fQ {s = e ∷ s′} (W , reach , ref)
  with □-failures-elim P₂ Q₂ reach ref
... | inj₁ fP₂ with fP (inj₁ fP₂)
...   | inj₁ (WP , rP , refP) = inj₁ (□-fail-intro-cons-L P₁ Q₁ rP refP)
...   | inj₂ dP₁              = inj₂ (□-div-intro-L {P = P₁} {Q = Q₁} dP₁)
□-mono-fail P₁ P₂ Q₁ Q₂ fP fQ {s = e ∷ s′} (W , reach , ref) | inj₂ fQ₂ with fQ (inj₁ fQ₂)
...   | inj₁ (WQ , rQ , refQ) = inj₁ (□-fail-intro-cons-R P₁ Q₁ rQ refQ)
...   | inj₂ dQ₁              = inj₂ (□-div-intro-R {P = P₁} {Q = Q₁} dQ₁)

-- `□` is ⊇F⊥-monotone in both operands (a target divergence routes through the ⊇D half)
□-mono-⊇F⊥ : ⦃ _ : DecEq R ⦄ {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
           → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂ → (P₁ □ Q₁) ⊇F⊥ (P₂ □ Q₂)
□-mono-⊇F⊥ {P₁ = P₁} {P₂ = P₂} {Q₁ = Q₁} {Q₂ = Q₂} (fP , dP) (fQ , dQ) (inj₁ f) =
  □-mono-fail P₁ P₂ Q₁ Q₂ fP fQ f
□-mono-⊇F⊥ hP hQ (inj₂ d) = inj₂ (□-mono-⊇D (proj₂ hP) (proj₂ hQ) d)

-------------------------------------------------------------------------------------
-- Layer 2 : the headline.
-------------------------------------------------------------------------------------

-- HEADLINE: external choice is a ⊑FD-PRECONGRUENCE — `⊑FD` facts in, `⊑FD` fact out, in
-- BOTH operands, unconditionally
□-mono-⊑FD : ⦃ _ : DecEq R ⦄ {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
           → P₁ ⊑FD P₂ → Q₁ ⊑FD Q₂ → (P₁ □ Q₁) ⊑FD (P₂ □ Q₂)
□-mono-⊑FD hP hQ = □-mono-⊇F⊥ hP hQ , □-mono-⊇D (proj₂ hP) (proj₂ hQ)

-------------------------------------------------------------------------------------
-- Layer 3 : the REPLICATED-CHOICE folds, FACT-SHAPED.
--
-- `□Fin` / `□⋆` are plain right folds of `_□_` over `Stop` (`□Fin zero f = Stop`,
-- `□⋆ [] = Stop`), and the binary law above carries NO side condition, so these are one
-- line each: structural recursion with `⊑FD-refl Stop` at the empty fold.  Mirrors
-- `⦀Fin-mono-⊑FD` / `⦀⋆-mono-⊑FD` (`CSP.Laws.FD.ParallelMonoFD`, Layer 8) — except that
-- those had to shed `⦀Fin-fsim`'s pairwise-disjointness and `OffersOnly` hypotheses,
-- whereas `□Fin-fsim` / `□⋆-fsim` never had any to shed.
-------------------------------------------------------------------------------------

-- `□Fin` is ⊑FD-monotone in its `Fin`-indexed family, pointwise and unconditionally
□Fin-mono-⊑FD : ⦃ _ : DecEq R ⦄ {n : ℕ} {f g : Fin n → PTree E (ExtI E) R}
              → (∀ i → f i ⊑FD g i) → □Fin n f ⊑FD □Fin n g
□Fin-mono-⊑FD {n = zero}  h = ⊑FD-refl Stop
□Fin-mono-⊑FD {n = suc n} h = □-mono-⊑FD (h fzero) (□Fin-mono-⊑FD (λ i → h (fsuc i)))

-- `□⋆` is ⊑FD-monotone in its list of operands, pointwise and unconditionally
□⋆-mono-⊑FD : ⦃ _ : DecEq R ⦄ {Ps Qs : List (PTree E (ExtI E) R)}
            → Pointwise _⊑FD_ Ps Qs → □⋆ Ps ⊑FD □⋆ Qs
□⋆-mono-⊑FD []ᵖ       = ⊑FD-refl Stop
□⋆-mono-⊑FD (p ∷ᵖ ps) = □-mono-⊑FD p (□⋆-mono-⊑FD ps)

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- The generic divergence-freedom layer: ONE home for the notions that the
-- coinduction principles keep asking for.
--
-- Three strengths of "does not diverge", from strongest to weakest:
--
--   * `τ-Acc t`          — τ-accessibility: an INDUCTIVE well-foundedness
--                          certificate for the τ-relation out of `t`.  This is
--                          the backbone of the whole calculus, because it
--                          REDUCES: an operator closure lemma can recurse on it,
--                          whereas a `¬ Diverges` hypothesis is a black box.
--   * `¬ Diverges t`     — no infinite τ-run FROM `t`.  This is exactly the
--                          shape `Semantics.BisimFromRel`'s `DRFromRel` (`ndivL`,
--                          `ndivR`) and `FSimFromRel` (`ndivL`) demand.
--   * `DivergenceFree t` — no infinite τ-run from any √-FREE-REACHABLE state.
--                          The consumer-facing notion (livelock-freedom).
--
-- Why `τ-Acc` and not `¬ Diverges` is the right primary for a COMPOSITIONAL
-- calculus: the negative form is not constructively closed under the operators.
-- E.g. from `Diverges (P □ Q)` one cannot build `Diverges P ⊎ Diverges Q`
-- without deciding which operand takes infinitely many of the τ's — a König /
-- classical step.  Induction on `τ-Acc P` and `τ-Acc Q`, by contrast, is
-- structural.  So `CSP.Laws.DivFree.Closure` proves `τ-Acc` closure and derives
-- `¬ Diverges` through `τ-Acc→¬Div`.
--
-- Gathered here (see each item for its previous home; the previous homes all
-- RE-EXPORT what moved, so no downstream module needed editing):
--   * `τ-Acc` / `acc` / `accSub` / `τ-Acc→¬Div`  ← `Semantics.TauAcc`  (moved)
--   * `DivergenceFree`                            ← `Semantics.DeadlockDR` (moved)
--   * `stable→¬div`                               ← `Semantics.Stability` (re-exported;
--       `Stability` is a deliberately postulate-free module that other things
--       depend on, so it keeps ownership)
--   * `div-diverges` / `deadlock-no-τ` / `deadlock-converges`
--                                                 ← `Semantics.DRBisim` (re-exported;
--       they sit next to `div≉DR-deadlock`, the pathology they exist to refute)
--
-- NOT here: `drbisim-divergenceFree` (`≈DR` transfer of `DivergenceFree`).  It
-- stays in `Semantics.DeadlockDR` because its proof needs `drbisim-trace-sim`
-- and the `⟹∖√` run-plumbing that live there; pulling it in would invert the
-- dependency (`DeadlockDR` imports this module, not the other way round).
--
-- Generic: parametric in `E` and `I`, exactly like `Semantics.LTS` /
-- `Semantics.FinBr`.  The CSP layer instantiates `I = ExtI E`.
--
-- `--safe`-clean: no `postulate`, no `NON_TERMINATING`, no `--sized-types`;
-- verified with `agda --safe Semantics/DivergenceFree.agda`.  The pragma itself
-- says only `--guardedness` because `--safe` is CO-infective: a `--safe`-pragma'd
-- module may not import `Process_Trees` / `Semantics.LTS` / `Semantics.DRBisim`,
-- none of which carry the pragma (they are safe in fact, just not by pragma).
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module Semantics.DivergenceFree {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree

open import Semantics.LTS      {ℓ} {ℓe} {ℓi} {E} {I} hiding (Diverges)
open import Semantics.Deadlock {ℓ} {ℓe} {ℓi} {E} {I} using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-τ; ∖√-ev)

-- `Diverges` and the two canonical (non-)divergence witnesses, re-exported from
-- their home in `Semantics.DRBisim`.
open import Semantics.DRBisim {ℓ} {ℓe} {ℓi} {E} {I}
  using (Diverges; div-diverges; deadlock-no-τ; deadlock-converges) public

-- A stable state performs no τ at all, hence cannot diverge: re-exported from
-- `Semantics.Stability` (which stays the owner — it is postulate-free by design).
open import Semantics.Stability {ℓ} {ℓe} {ℓi} {E} {I}
  using (stable-no-τ; stable→¬div; stable→τ*-refl) public

------------------------------------------------------------------------
-- §1.  τ-accessibility (moved verbatim from `Semantics.TauAcc`).
------------------------------------------------------------------------

-- τ-accessibility: every τ-successor is again τ-accessible (backwards WF).
data τ-Acc {ℓr} {R : Set ℓr} (t : PTree E I R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  acc : (∀ {t′} → t ─[ τ ]─► t′ → τ-Acc t′) → τ-Acc t

-- follow a τ-step into the sub-accessibility (the accessor)
accSub : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R} → τ-Acc t → t ─[ τ ]─► t′ → τ-Acc t′
accSub (acc f) st = f st

-- τ-accessible ⇒ no infinite τ-sequence (`Diverges` imported from LTS);
-- well-foundedness rules out divergence
τ-Acc→¬Div : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} → τ-Acc t → ¬ Diverges t
τ-Acc→¬Div (acc f) d = τ-Acc→¬Div (f (Diverges.step d)) (Diverges.rest d)

------------------------------------------------------------------------
-- §2.  Leaf certificates: the node shapes that have no τ at all.
------------------------------------------------------------------------

-- a `ret` node has no τ-step (`sSil`/`sTau` both contradict the force equation)
ret→no-τ : ∀ {ℓr} {R : Set ℓr} {t u : PTree E I R} {r : R}
         → PTree.force t ≡ ret r → t ─[ τ ]─► u → ⊥
ret→no-τ eqf (sSil sileq)   with trans (sym sileq) eqf
... | ()
ret→no-τ eqf (sTau reqf _)  with trans (sym reqf) eqf
... | ()

-- … so it is τ-accessible (vacuously)
ret→τ-Acc : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} {r : R}
          → PTree.force t ≡ ret r → τ-Acc t
ret→τ-Acc eqf = acc λ st → ⊥-elim (ret→no-τ eqf st)

-- a STABLE state is τ-accessible (vacuously): `stable-no-τ` refutes every τ
stable→τ-Acc : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} → isStable t → τ-Acc t
stable→τ-Acc stb = acc λ st → ⊥-elim (stable-no-τ stb st)

-- Two states with the SAME forced node have the same τ-steps: transport one
-- across.  (Used where an operator's node is literally an operand's node — e.g.
-- `force (P >>= k) ≡ force (k r)` when `P` returns `r`.)
τ-step-transport : ∀ {ℓr} {R : Set ℓr} {t u M : PTree E I R}
                 → PTree.force t ≡ PTree.force u → t ─[ τ ]─► M → u ─[ τ ]─► M
τ-step-transport eq (sSil sileq)  = sSil (trans (sym eq) sileq)
τ-step-transport eq (sTau req br) = sTau (trans (sym eq) req) br

-- a `sil` node is τ-accessible as soon as its unique successor is
sil→τ-Acc : ∀ {ℓr} {R : Set ℓr} {t c : PTree E I R}
          → PTree.force t ≡ sil c → τ-Acc c → τ-Acc t
sil→τ-Acc {t = t} {c = c} eqf ac = acc go
  where
    -- the only τ out of a `sil` node lands on `c`
    go : ∀ {u} → t ─[ τ ]─► u → τ-Acc u
    go (sSil sileq)  with trans (sym sileq) eqf
    ... | refl = ac
    go (sTau reqf _) with trans (sym reqf) eqf
    ... | ()

------------------------------------------------------------------------
-- §3.  Divergence-freedom over √-free reachability (moved from `DeadlockDR`).
------------------------------------------------------------------------

-- Divergence-free: no √-free-reachable state can perform an infinite τ-run.
DivergenceFree : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
DivergenceFree {R = R} t =
  ∀ {s : List Event} {t′ : PTree E I R} → t ⟹∖√⟨ s ⟩ t′ → ¬ Diverges t′

-- The τ-Acc-level counterpart: τ-accessible at every √-free-reachable state.
-- This is what an operator calculus would have to establish to conclude
-- `DivergenceFree` compositionally (it additionally needs the per-operator
-- VISIBLE-step inversions, not just the τ ones).
τ-AccReach : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
τ-AccReach {R = R} t =
  ∀ {s : List Event} {t′ : PTree E I R} → t ⟹∖√⟨ s ⟩ t′ → τ-Acc t′

-- … and the bridge to the consumer-facing notion.
τ-AccReach→DivergenceFree : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                          → τ-AccReach t → DivergenceFree t
τ-AccReach→DivergenceFree ar reach = τ-Acc→¬Div (ar reach)

-- `DivergenceFree` at the root in particular says the root does not diverge.
divergenceFree→¬Div : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                    → DivergenceFree t → ¬ Diverges t
divergenceFree→¬Div df = df ∖√-refl

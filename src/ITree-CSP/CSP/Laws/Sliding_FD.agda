{-
  Sliding-choice laws for ITree-CSP under failures-divergences
  equivalence `_≃FD_`.

  This module replaces the six `▷-step-*` postulates that used to live
  in `CSP.Laws.FailuresDivergences` (lines 485–526) and which became
  unprovable after the `_▷_` operator was extended with the `mix`
  constructor and with a Q-ndbr-distributes-first clause in
  `CSP.Definitions.Operators` (lines 390–421).

  ---------------------------------------------------------------------
  Truth table for `force (P ▷ Q)`
  ---------------------------------------------------------------------

  The operator branches on `force Q` FIRST.  If `force Q = ndbr fQ wi wa wp`
  then the result is `ndbr (mergeNdbr▷-R P fQ) wi wa _`, **regardless of
  the shape of `force P`** (i.e. Q's internal nondeterminism distributes
  through `▷` on the right).

  Only when `force Q ≢ ndbr _ _ _ _` do the P-shape clauses apply.  Let
  `force Q ≢ ndbr _ _ _ _` (predicate `Q-not-ndbr Q` below).  Then:

       force P             force (P ▷ Q)
       ---------           -------------------------------
       ret r               ret r
       sil P'              sil (P' ▷ Q)
       vis fP              mix fP Q
       ndbr fP wi wa wp    ndbr (mergeNdbr▷-L fP Q) wi wa _
       mix fP P'           mix fP (P' ▷ Q)

  (And in the Q-is-ndbr row, every entry collapses to
   `ndbr (mergeNdbr▷-R P fQ) …`.)

  Consequences for the formerly-postulated step lemmas:

   * `▷-step-sil-τ`     : KEPT — with `Q-not-ndbr Q`, `force (P ▷ Q)`
                          reduces to `sil (P' ▷ Q)`, so `sSil` applies.

   * `▷-step-ret-√`     : KEPT — with `Q-not-ndbr Q`, `force (P ▷ Q)`
                          reduces to `ret r`, so `sRet` applies.

   * `▷-step-vis-τ-L`   : DELETED — when `force P ≡ vis fP` and
                          `Q-not-ndbr Q`, `force (P ▷ Q) ≡ mix fP Q`.
                          The `mix` node has no τ-transition to
                          `P □ Q`.  The only τ-step from `mix fP Q` is
                          `sMixSlide` going to `Q` (covered by `-R`),
                          and visible offers from `fP` resolve via
                          `sMixVis` directly to a P-branch — not via a
                          τ-routed `P □ Q` intermediate.

   * `▷-step-vis-τ-R`   : KEPT (restated) — with `Q-not-ndbr Q`,
                          `force (P ▷ Q) ≡ mix fP Q`, hence `sMixSlide`
                          gives `(P ▷ Q) ─[τ]─► Q` directly.

   * `▷-step-ndbr-τ-L`  : RESTATED — when `force P ≡ ndbr fP …`
                          and `Q-not-ndbr Q`, `force (P ▷ Q)` reduces
                          to a fresh `ndbr (mergeNdbr▷-L fP Q) …`, NOT
                          to `P □ Q`.  The τ-steps available from
                          there go to `P' ▷ Q` for any branch
                          `fP i a ≡ just P'`, so the restated form
                          takes that branch-witness as an extra
                          premise.

   * `▷-step-ndbr-τ-R`  : DELETED — when `force P ≡ ndbr fP …` and
                          `Q-not-ndbr Q`, `force (P ▷ Q)` is an
                          `ndbr (mergeNdbr▷-L fP Q) …` node whose
                          τ-steps go to `P' ▷ Q` only, not to `Q`.
                          The "fall-through to Q" intuition is now
                          discharged either (a) when Q itself is an
                          `ndbr` via the Q-distribution clause, or
                          (b) when P is `vis`/`mix` via `sMixSlide`.

  No callers in the current tree depend on these names — verified by
  `grep -rn "▷-step" src/`.
-}

{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_)
                 renaming (zero to lzero; suc to lsuc)
open import Data.Product using (Σ; ∃; _,_; proj₁; proj₂; _×_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤)
open import Data.List using (List; _∷_; []; _++_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; no; ¬_)
open import Relation.Binary.PropositionalEquality
     using (_≡_; _≢_; refl)

open import Class.DecEq using (DecEq)

open import Prelude
open import Interaction_Trees
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences
open Traces
open Failures
open IsDivergence

module CSP.Laws.Sliding_FD
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

open ITree
open Label
open Event√

-----------------------------------------------------------------------------
-- Side-condition: `force Q` is not an `ndbr` node.
--
-- This is the precondition needed to "expose" the P-shape clauses of
-- `force (P ▷ Q)`.  When Q is an `ndbr`, the Q-distribution clause
-- fires regardless of P, and the lemmas below do NOT apply — that
-- case is the subject of `▷-step-Q-ndbr` (task A3).
-----------------------------------------------------------------------------

Q-not-ndbr : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           → ITree E (ExtI I) R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Q-not-ndbr {ℓi = ℓi} {ℓr = ℓr} {I = I} {R = R} Q =
  ∀ (f  : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R)))
    (wi : AnyTypes (ExtI I)) (wa : proj₁ wi) (wp : Is-just (f wi wa))
  → ITree.force Q ≢ ndbr f wi wa wp

-----------------------------------------------------------------------------
-- Force-shape lemmas: explicit reduction of `force (P ▷ Q)`.
--
-- The first five (`force-▷-{sil,ret,vis,mix,ndbr}`) handle the
-- Q-not-ndbr case: case analyses on `force Q` driven by the
-- `Q-not-ndbr` assumption.  Each one fires the contradiction in the
-- impossible `ndbr` branch and returns `refl` in every other branch.
--
-- The sixth (`force-▷-Q-ndbr`) handles the Q-is-ndbr case: when
-- `force Q ≡ ndbr fQ wi wa wp`, the Q-distribution clause of `_▷_`
-- fires regardless of `force P`, so `force (P ▷ Q)` is itself an
-- `ndbr (mergeNdbr▷-R P fQ) wi wa _` node.
-----------------------------------------------------------------------------

force-▷-sil : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
              {P P' Q : ITree E (ExtI I) R}
            → ITree.force P ≡ sil P'
            → Q-not-ndbr Q
            → ITree.force (P ▷ Q) ≡ sil (P' ▷ Q)
force-▷-sil {P = P} {P' = P'} {Q = Q} eqP nndbr with ITree.force Q | nndbr
... | ret _                  | _    rewrite eqP = refl
... | sil _                  | _    rewrite eqP = refl
... | vis _                  | _    rewrite eqP = refl
... | mix _ _                | _    rewrite eqP = refl
... | ndbr f wi wa wp        | nn   = ⊥-elim (nn f wi wa wp refl)

force-▷-ret : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
              {P Q : ITree E (ExtI I) R} {r : R}
            → ITree.force P ≡ ret r
            → Q-not-ndbr Q
            → ITree.force (P ▷ Q) ≡ ret r
force-▷-ret {P = P} {Q = Q} {r = r} eqP nndbr with ITree.force Q | nndbr
... | ret _                  | _    rewrite eqP = refl
... | sil _                  | _    rewrite eqP = refl
... | vis _                  | _    rewrite eqP = refl
... | mix _ _                | _    rewrite eqP = refl
... | ndbr f wi wa wp        | nn   = ⊥-elim (nn f wi wa wp refl)

force-▷-vis : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
              {P Q : ITree E (ExtI I) R}
              {fP : (at : AnyTypes E)
                  → ContinueType at (Maybe (ITree E (ExtI I) R))}
            → ITree.force P ≡ vis fP
            → Q-not-ndbr Q
            → ITree.force (P ▷ Q) ≡ mix fP Q
force-▷-vis {P = P} {Q = Q} {fP = fP} eqP nndbr with ITree.force Q | nndbr
... | ret _                  | _    rewrite eqP = refl
... | sil _                  | _    rewrite eqP = refl
... | vis _                  | _    rewrite eqP = refl
... | mix _ _                | _    rewrite eqP = refl
... | ndbr f wi wa wp        | nn   = ⊥-elim (nn f wi wa wp refl)

force-▷-ndbr : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
               {P Q : ITree E (ExtI I) R}
               {fP : (i : AnyTypes (ExtI I))
                   → ContinueType i (Maybe (ITree E (ExtI I) R))}
               {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
               {wp : Is-just (fP wi wa)}
             → ITree.force P ≡ ndbr fP wi wa wp
             → Q-not-ndbr Q
             → ITree.force (P ▷ Q)
                 ≡ ndbr (mergeNdbr▷-L fP Q) wi wa
                        (mergeNdbr▷-L-witness fP Q wp)
force-▷-ndbr {P = P} {Q = Q} {fP = fP} eqP nndbr with ITree.force Q | nndbr
... | ret _                  | _    rewrite eqP = refl
... | sil _                  | _    rewrite eqP = refl
... | vis _                  | _    rewrite eqP = refl
... | mix _ _                | _    rewrite eqP = refl
... | ndbr f wi wa wp        | nn   = ⊥-elim (nn f wi wa wp refl)

-- Auxiliary force-shape lemma: `force P ≡ mix fP P'` and `Q-not-ndbr Q`
-- propagates to `force (P ▷ Q) ≡ mix fP (P' ▷ Q)`.  Mirrors the other
-- `force-▷-*` lemmas; used in the `sMixSlide` case of P's τ-step in
-- `▷-divergences-introP` and `▷-divergences-elim-go`.
force-▷-mix : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
              {P P' Q : ITree E (ExtI I) R}
              {fP : (at : AnyTypes E)
                  → ContinueType at (Maybe (ITree E (ExtI I) R))}
            → ITree.force P ≡ mix fP P'
            → Q-not-ndbr Q
            → ITree.force (P ▷ Q) ≡ mix fP (P' ▷ Q)
force-▷-mix {P = P} {Q = Q} eqP nndbr with ITree.force Q | nndbr
... | ret _                  | _    rewrite eqP = refl
... | sil _                  | _    rewrite eqP = refl
... | vis _                  | _    rewrite eqP = refl
... | mix _ _                | _    rewrite eqP = refl
... | ndbr f wi wa wp        | nn   = ⊥-elim (nn f wi wa wp refl)

-- Force-shape lemma for the Q-is-ndbr branch.
force-▷-Q-ndbr : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                 {P Q : ITree E (ExtI I) R}
                 {fQ : (i : AnyTypes (ExtI I))
                     → ContinueType i (Maybe (ITree E (ExtI I) R))}
                 {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
                 {wp : Is-just (fQ wi wa)}
               → ITree.force Q ≡ ndbr fQ wi wa wp
               → ITree.force (P ▷ Q)
                   ≡ ndbr (mergeNdbr▷-R P fQ) wi wa
                          (mergeNdbr▷-R-witness P fQ wp)
force-▷-Q-ndbr {P = P} {Q = Q} eqQ with ITree.force P
... | ret _        rewrite eqQ = refl
... | sil _        rewrite eqQ = refl
... | vis _        rewrite eqQ = refl
... | mix _ _      rewrite eqQ = refl
... | ndbr _ _ _ _ rewrite eqQ = refl

-----------------------------------------------------------------------------
-- ▷-step lemmas (restated forms of the former postulates).
-----------------------------------------------------------------------------

-- KEPT: τ-step from P propagates through ▷ on the left.
▷-step-sil-τ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
               {P P' Q : ITree E (ExtI I) R}
             → ITree.force P ≡ sil P'
             → Q-not-ndbr Q
             → (P ▷ Q) ─[ τ ]─► (P' ▷ Q)
▷-step-sil-τ eqP nndbr = sSil (force-▷-sil eqP nndbr)

-- KEPT: terminating P fires its √ immediately through ▷.
▷-step-ret-√ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
               {P Q : ITree E (ExtI I) R} {r : R}
             → ITree.force P ≡ ret r
             → Q-not-ndbr Q
             → (P ▷ Q) ─[ ev (√ r) ]─► deadlock
▷-step-ret-√ eqP nndbr = sRet (force-▷-ret eqP nndbr)

-- DELETED: `▷-step-vis-τ-L`.
--   Was: `force P ≡ vis fP → (P ▷ Q) ─[τ]─► (P □ Q)`.
--   Reason: under the current `_▷_` definition, `force (P ▷ Q)` reduces
--   to `mix fP Q` when `force P ≡ vis fP` and `Q` is not `ndbr`.  The
--   `mix` constructor has no τ-step to `P □ Q`; its only τ-step is
--   `sMixSlide` to `Q` (covered by `-R` below) and its visible offers
--   resolve via `sMixVis` directly.

-- KEPT (restated as direct τ-slide off the mix node).
▷-step-vis-τ-R : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                 {P Q : ITree E (ExtI I) R}
                 {fP : (at : AnyTypes E)
                     → ContinueType at (Maybe (ITree E (ExtI I) R))}
               → ITree.force P ≡ vis fP
               → Q-not-ndbr Q
               → (P ▷ Q) ─[ τ ]─► Q
▷-step-vis-τ-R eqP nndbr = sMixSlide (force-▷-vis eqP nndbr)

-- DELETED + RESTATED: `▷-step-ndbr-τ-L` and `▷-step-ndbr-τ-R`.
--   Was-L: `force P ≡ ndbr fP wi wa wp → (P ▷ Q) ─[τ]─► (P □ Q)`.
--   Was-R: `force P ≡ ndbr fP wi wa wp → (P ▷ Q) ─[τ]─► Q`.
--   Reason: under the current `_▷_` definition, when `force P ≡ ndbr fP …`
--   and `Q` is not `ndbr`, `force (P ▷ Q)` is itself an
--   `ndbr (mergeNdbr▷-L fP Q) wi wa _` node.  The τ-steps available
--   from it (via `sNdbr`) go to `P' ▷ Q` for each branch
--   `fP i a ≡ just P'`.  Neither `P □ Q` nor `Q` is a direct
--   τ-successor.
--
-- Helper: distribute `mergeNdbr▷-L` over a known `just`-branch.
merge-▷-L-just :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (fP : (i : AnyTypes (ExtI I))
        → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → (Q P' : ITree E (ExtI I) R)
  → (i : AnyTypes (ExtI I)) → (a : proj₁ i)
  → fP i a ≡ just P'
  → mergeNdbr▷-L fP Q i a ≡ just (P' ▷ Q)
merge-▷-L-just fP Q P' i a eq with fP i a
merge-▷-L-just fP Q P' i a refl | just _ = refl

-- Helper: with `Is-just (fQ wi wa)`, the merged Q-distribution branch
-- is a `just`.
merge-▷-R-just :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P : ITree E (ExtI I) R)
  → (fQ : (i : AnyTypes (ExtI I))
        → ContinueType i (Maybe (ITree E (ExtI I) R)))
  → ∀ {wi wa}
  → (wp : Is-just (fQ wi wa))
  → ∃ λ Q' → mergeNdbr▷-R P fQ wi wa ≡ just (P ▷ Q')
merge-▷-R-just P fQ {wi} {wa} wp with fQ wi wa | wp
... | just Q'' | _ = Q'' , refl

-- Restated form (the canonical operational fact):
▷-step-ndbr-τ-L : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                   {P P' Q : ITree E (ExtI I) R}
                   {fP : (i : AnyTypes (ExtI I))
                       → ContinueType i (Maybe (ITree E (ExtI I) R))}
                   {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
                   {wp : Is-just (fP wi wa)}
                   {i  : AnyTypes (ExtI I)} {a : proj₁ i}
                 → ITree.force P ≡ ndbr fP wi wa wp
                 → Q-not-ndbr Q
                 → fP i a ≡ just P'
                 → (P ▷ Q) ─[ τ ]─► (P' ▷ Q)
▷-step-ndbr-τ-L {P = P} {P' = P'} {Q = Q} {fP = fP}
                 {wi = wi} {wa = wa} {wp = wp} {i = i} {a = a}
                 eqP nndbr eqBr =
  sNdbr {f   = mergeNdbr▷-L fP Q}
        {wi  = wi}  {wa  = wa}
        {prf = mergeNdbr▷-L-witness fP Q wp}
        {i   = i}   {a   = a}
        (force-▷-ndbr eqP nndbr)
        (merge-▷-L-just fP Q P' i a eqBr)

-----------------------------------------------------------------------------
-- ▷-step-Q-ndbr: τ-step under Q's ndbr distribution clause.
--
-- This discharges the case excluded by `Q-not-ndbr`.  When
-- `force Q ≡ ndbr fQ wi wa wp`, the Q-distribution clause of `_▷_`
-- fires regardless of `force P`, so `force (P ▷ Q)` is itself an
-- `ndbr (mergeNdbr▷-R P fQ) wi wa _` node.  Taking branch `(wi, wa)`
-- via `sNdbr` yields a τ-step to `P ▷ Q''`, where `Q''` is the tree
-- that `wp` selects from `fQ wi wa`.  We existentialise the residual
-- because its precise shape depends on the merge helper.
-----------------------------------------------------------------------------

▷-step-Q-ndbr : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                {P Q : ITree E (ExtI I) R}
                {fQ : (i : AnyTypes (ExtI I))
                    → ContinueType i (Maybe (ITree E (ExtI I) R))}
                {wi : AnyTypes (ExtI I)} {wa : proj₁ wi}
                {wp : Is-just (fQ wi wa)}
              → ITree.force Q ≡ ndbr fQ wi wa wp
              → ∃ λ Q' → (P ▷ Q) ─[ τ ]─► Q'
▷-step-Q-ndbr {P = P} {Q = Q} {fQ = fQ} {wi = wi} {wa = wa} {wp = wp} eqQ
  with merge-▷-R-just P fQ {wi} {wa} wp
... | Q'' , mergeEq =
  (P ▷ Q'') ,
  sNdbr {f   = mergeNdbr▷-R P fQ}
        {wi  = wi}  {wa  = wa}
        {prf = mergeNdbr▷-R-witness P fQ wp}
        {i   = wi}  {a   = wa}
        (force-▷-Q-ndbr eqQ)
        mergeEq

-----------------------------------------------------------------------------
-- Stability of `P ▷ Q`.
--
-- Under the truth-table for `force (P ▷ Q)`, the head node is always
-- one of `ret`, `sil`, `mix`, or `ndbr` — never `vis`.  Since
-- `isStable` (in `Interaction_Trees`) is inhabited only when
-- `force t ≡ vis _`, `(P ▷ Q)` is never stable.  Operationally this
-- says `(P ▷ Q)` always has some τ-progress available (either P's
-- own τ, the slide to Q, or a non-deterministic branch), so
-- refusals of `(P ▷ Q)` can only arise from the `√ r` step (when
-- `force P ≡ ret r` and `Q-not-ndbr Q`).
-----------------------------------------------------------------------------

-- Auxiliary: `force (P ▷ Q)` is never a `vis` node.  This is a pure
-- consequence of the truth-table — no premises.
▷-force-never-vis :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R}
    {fP : (at : AnyTypes E)
        → ContinueType at (Maybe (ITree E (ExtI I) R))}
  → ¬ (ITree.force (P ▷ Q) ≡ vis fP)
▷-force-never-vis {P = P} {Q = Q} with ITree.force P | ITree.force Q
... | _            | ndbr _ _ _ _ = λ ()
... | ret _        | ret _        = λ ()
... | ret _        | sil _        = λ ()
... | ret _        | vis _        = λ ()
... | ret _        | mix _ _      = λ ()
... | sil _        | ret _        = λ ()
... | sil _        | sil _        = λ ()
... | sil _        | vis _        = λ ()
... | sil _        | mix _ _      = λ ()
... | vis _        | ret _        = λ ()
... | vis _        | sil _        = λ ()
... | vis _        | vis _        = λ ()
... | vis _        | mix _ _      = λ ()
... | ndbr _ _ _ _ | ret _        = λ ()
... | ndbr _ _ _ _ | sil _        = λ ()
... | ndbr _ _ _ _ | vis _        = λ ()
... | ndbr _ _ _ _ | mix _ _      = λ ()
... | mix _ _      | ret _        = λ ()
... | mix _ _      | sil _        = λ ()
... | mix _ _      | vis _        = λ ()
... | mix _ _      | mix _ _      = λ ()

-- `(P ▷ Q)` is never stable, derived from `▷-force-never-vis`.
▷-never-stable : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
                 {P Q : ITree E (ExtI I) R}
               → ¬ isStable (P ▷ Q)
▷-never-stable {P = P} {Q = Q} s with ITree.force (P ▷ Q) in eqPQ
... | ret _        = s
... | sil _        = s
... | vis fP       = ⊥-elim (▷-force-never-vis {P = P} {Q = Q} {fP = fP} eqPQ)
... | ndbr _ _ _ _ = s
... | mix _ _      = s

-----------------------------------------------------------------------------
-- A5: bigstep decomposition of `P ▷ Q`.
--
-- A bigstep `(P ▷ Q) ═⟨ s ⟩═► T` decomposes into either a P-trace of `s`
-- or a Q-trace of `s`.  This mirrors `sliding-trace-helper` from
-- `CSP.Laws.Traces` (lines 3117-3406), but produces a two-case datatype
-- `▷BigStepSplit` instead of a `⊎`.
--
-- Note: the `Ret-fired-then-deadlock` shape (P-side `√ r` then any tail
-- from deadlock) is absorbed into the `in-P` constructor — the bigstep
-- `(t-f , bStep (sRet eqP) tail)` typechecks naturally as a P-trace
-- ending in `√ r`.
-----------------------------------------------------------------------------

data ▷BigStepSplit
    {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    (P Q : ITree E (ExtI I) R)
  : List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  in-P : ∀ {s} → traces P s → ▷BigStepSplit P Q s
  in-Q : ∀ {s} → traces Q s → ▷BigStepSplit P Q s

-----------------------------------------------------------------------------
-- The decomposition lemma.
--
-- Proof strategy: induct on the bigstep.  Mirror the case structure of
-- `sliding-trace-helper`:
--   * `bNil`                      → in-P with `bNil`.
--   * `bTau (sSil eqP) tail`      → recurse on residual P'; rebuild P-trace.
--   * `bTau (sNdbr eq eq-j) tail` → either Q-distribution (any P shape,
--                                    Q is `ndbr`) or P-distribution (P is
--                                    `ndbr`, Q is not).
--   * `bStep (sVis _ _) _`        → absurd; `force (P ▷ Q)` is never `vis`.
--   * `bStep (sRet eqP) tail`     → must have `force P ≡ ret r` and Q not
--                                    `ndbr`; build P-trace directly.
--   * `bTau (sMixSlide eq) tail`  → mix node from `vis P` or `mix … P'`;
--                                    `vis` slides to Q (in-Q), `mix _ P'`
--                                    recurses (P-trace).
--   * `bStep (sMixVis _ _) _`     → P-side visible firing; build P-trace.
-----------------------------------------------------------------------------

▷-bigstep-decomp :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R}
    {s : List (Event√ E R)} {T : ITree E (ExtI I) R}
  → (P ▷ Q) ═⟨ s ⟩═► T
  → ▷BigStepSplit P Q s

-- Base case.
▷-bigstep-decomp {P = P} bNil = in-P (P , bNil)

-- 1. sSil: only productive when force P ≡ sil P' and force Q is not ndbr.
▷-bigstep-decomp {P = P} {Q = Q} {T = T} (bTau (sSil eq) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | sil P' | ret _ | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sSil eq-P) trP')
      (in-Q trQ)           → in-Q trQ
... | sil P' | sil _ | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sSil eq-P) trP')
      (in-Q trQ)           → in-Q trQ
... | sil P' | vis _ | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sSil eq-P) trP')
      (in-Q trQ)           → in-Q trQ
... | sil P' | mix _ _ | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sSil eq-P) trP')
      (in-Q trQ)           → in-Q trQ
... | sil _ | ndbr _ _ _ _ | ()
-- ret | * : force = ret (or ndbr when *=ndbr); no sSil.
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | mix _ _ | ()
... | ret _ | ndbr _ _ _ _ | ()
-- vis | * : force = mix fP Q (or ndbr when *=ndbr); no sSil.
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | mix _ _ | ()
... | vis _ | ndbr _ _ _ _ | ()
-- ndbr | * : force = ndbr (P-distr or Q-distr); no sSil.
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
-- mix | * : force = mix (or ndbr when *=ndbr); no sSil.
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | mix _ _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()

-- 2. sNdbr: productive when force(P ▷ Q) is ndbr.
--    (a) Q.force = ndbr fQ → Q distributes; any P shape.
--    (b) Q.force ≠ ndbr ∧ P.force = ndbr fP → P distributes.
-- (a) Q distributes — five P-shapes × ndbr Q.
▷-bigstep-decomp {P = P} {Q = Q} {T = T}
                 (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-bigstep-decomp {P = P} {Q = Q'} {T = T} big-step of λ where
      (in-P trP)           → in-P trP
      (in-Q (tend , trQ')) → in-Q (tend , bTau (sNdbr eq-Q fq-eq) trQ')
... | nothing | ()
▷-bigstep-decomp {P = P} {Q = Q} {T = T}
                 (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | sil _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-bigstep-decomp {P = P} {Q = Q'} {T = T} big-step of λ where
      (in-P trP)           → in-P trP
      (in-Q (tend , trQ')) → in-Q (tend , bTau (sNdbr eq-Q fq-eq) trQ')
... | nothing | ()
▷-bigstep-decomp {P = P} {Q = Q} {T = T}
                 (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | vis _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-bigstep-decomp {P = P} {Q = Q'} {T = T} big-step of λ where
      (in-P trP)           → in-P trP
      (in-Q (tend , trQ')) → in-Q (tend , bTau (sNdbr eq-Q fq-eq) trQ')
... | nothing | ()
▷-bigstep-decomp {P = P} {Q = Q} {T = T}
                 (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | ndbr _ _ _ _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-bigstep-decomp {P = P} {Q = Q'} {T = T} big-step of λ where
      (in-P trP)           → in-P trP
      (in-Q (tend , trQ')) → in-Q (tend , bTau (sNdbr eq-Q fq-eq) trQ')
... | nothing | ()
▷-bigstep-decomp {P = P} {Q = Q} {T = T}
                 (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | mix _ _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-bigstep-decomp {P = P} {Q = Q'} {T = T} big-step of λ where
      (in-P trP)           → in-P trP
      (in-Q (tend , trQ')) → in-Q (tend , bTau (sNdbr eq-Q fq-eq) trQ')
... | nothing | ()
-- (b) P distributes — P is `ndbr`, Q is not.
▷-bigstep-decomp {P = P} {Q = Q} {T = T}
                 (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | ndbr fP _ _ _ | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sNdbr eq-P fp-eq) trP')
      (in-Q trQ)           → in-Q trQ
... | nothing | ()
▷-bigstep-decomp {P = P} {Q = Q} {T = T}
                 (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | ndbr fP _ _ _ | sil _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sNdbr eq-P fp-eq) trP')
      (in-Q trQ)           → in-Q trQ
... | nothing | ()
▷-bigstep-decomp {P = P} {Q = Q} {T = T}
                 (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | ndbr fP _ _ _ | vis _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sNdbr eq-P fp-eq) trP')
      (in-Q trQ)           → in-Q trQ
... | nothing | ()
▷-bigstep-decomp {P = P} {Q = Q} {T = T}
                 (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step)
  | ndbr fP _ _ _ | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sNdbr eq-P fp-eq) trP')
      (in-Q trQ)           → in-Q trQ
... | nothing | ()
-- Absurd cases — force(P ▷ Q) is not ndbr.
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | ret _ | ret _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | ret _ | sil _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | ret _ | vis _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | ret _ | mix _ _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | sil _ | ret _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | sil _ | sil _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | sil _ | vis _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | sil _ | mix _ _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | vis _ | ret _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | vis _ | sil _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | vis _ | vis _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | vis _ | mix _ _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | mix _ _ | ret _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | mix _ _ | sil _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | mix _ _ | vis _ | ()
▷-bigstep-decomp (bTau (sNdbr eq eq-j) big-step) | mix _ _ | mix _ _ | ()

-- 3. sVis: under new ▷, force(P ▷ Q) is never `vis _`.  All absurd.
▷-bigstep-decomp {P = P} {Q = Q} (bStep (sVis eq eq-j) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | vis _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | mix _ _ | ()

-- 4. sRet: productive only when force P ≡ ret r and Q is not ndbr.
▷-bigstep-decomp {P = P} {Q = Q} {T = T} (bStep (sRet eq) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret r | ndbr _ _ _ _ | ()  -- ret|ndbr produces ndbr, not ret
... | ret r | ret _ | refl =
    in-P (T , bStep (sRet eq-P) big-step)
... | ret r | sil _ | refl =
    in-P (T , bStep (sRet eq-P) big-step)
... | ret r | vis _ | refl =
    in-P (T , bStep (sRet eq-P) big-step)
... | ret r | mix _ _ | refl =
    in-P (T , bStep (sRet eq-P) big-step)
-- All other P-shapes are absurd (force is not ret).
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | vis _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | mix _ _ | ()

-- 5. sMixSlide:
--    P=vis fP, Q≠ndbr → force = mix fP Q.  Slide goes to Q → in-Q.
--    P=mix fP P', Q≠ndbr → force = mix fP (P' ▷ Q).  Slide goes to (P' ▷ Q); recurse.
▷-bigstep-decomp {P = P} {Q = Q} {T = T} (bTau (sMixSlide eq) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | vis _ | ret _   | refl = in-Q (T , big-step)
... | vis _ | sil _   | refl = in-Q (T , big-step)
... | vis _ | vis _   | refl = in-Q (T , big-step)
... | vis _ | mix _ _ | refl = in-Q (T , big-step)
... | vis _ | ndbr _ _ _ _ | ()
... | mix _ P' | ret _   | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sMixSlide eq-P) trP')
      (in-Q trQ)           → in-Q trQ
... | mix _ P' | sil _   | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sMixSlide eq-P) trP')
      (in-Q trQ)           → in-Q trQ
... | mix _ P' | vis _   | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sMixSlide eq-P) trP')
      (in-Q trQ)           → in-Q trQ
... | mix _ P' | mix _ _ | refl =
    case ▷-bigstep-decomp {P = P'} {Q = Q} {T = T} big-step of λ where
      (in-P (tend , trP')) → in-P (tend , bTau (sMixSlide eq-P) trP')
      (in-Q trQ)           → in-Q trQ
... | mix _ _  | ndbr _ _ _ _ | ()
-- Absurd shapes: force isn't mix.
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()

-- 6. sMixVis:
--    P=vis fP,  Q≠ndbr → force = mix fP Q.  Visible fire from fP — P-side step.
--    P=mix _ _, Q≠ndbr → force = mix fP (P' ▷ Q).  Visible fire — P-side step.
▷-bigstep-decomp {P = P} {Q = Q} {T = T}
                 (bStep (sMixVis {at = at} {a = a} eq eq-j) big-step)
  with P .force in eq-P | Q .force in eq-Q | eq
... | vis _ | ret _   | refl = in-P (T , bStep (sVis eq-P eq-j) big-step)
... | vis _ | sil _   | refl = in-P (T , bStep (sVis eq-P eq-j) big-step)
... | vis _ | vis _   | refl = in-P (T , bStep (sVis eq-P eq-j) big-step)
... | vis _ | mix _ _ | refl = in-P (T , bStep (sVis eq-P eq-j) big-step)
... | vis _ | ndbr _ _ _ _ | ()
... | mix _ _ | ret _   | refl = in-P (T , bStep (sMixVis eq-P eq-j) big-step)
... | mix _ _ | sil _   | refl = in-P (T , bStep (sMixVis eq-P eq-j) big-step)
... | mix _ _ | vis _   | refl = in-P (T , bStep (sMixVis eq-P eq-j) big-step)
... | mix _ _ | mix _ _ | refl = in-P (T , bStep (sMixVis eq-P eq-j) big-step)
... | mix _ _ | ndbr _ _ _ _ | ()
-- Absurd shapes: force isn't mix.
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()

-----------------------------------------------------------------------------
-- A6: failures decomposition for `_▷_`.
--
-- A failure of `(P ▷ Q)` decomposes into a failure of `P` or a failure
-- of `Q`.  The proof mirrors `▷-bigstep-decomp` but threads the refusal
-- witness `T ref B` through each branch (option "C" — inline case
-- analysis, since the existing decomp hides the residual).
--
-- The only non-trivial leaf is `bNil`, where the residual is literally
-- `(P ▷ Q)` and we must invert `(P ▷ Q) ref B`:
--
--   * `ref-stable`: ruled out by `▷-never-stable`.
--   * `ref-tick`: fires `ev (√ x)`, which can only come from `sRet`
--                 (sVis/sMixVis fire `evl _`, never `√ _`).  By the
--                 truth-table, `force (P ▷ Q) ≡ ret x` forces
--                 `force P ≡ ret x` (and Q-not-ndbr), so `P ref B` via
--                 `ref-tick (sRet …) ¬B√x`.
--
-- Other leaves preserve the residual `T` from the input bigstep, so the
-- refusal carries through unchanged.
-----------------------------------------------------------------------------

-- Helper: invert `(P ▷ Q) ref B` at the empty trace into `P ref B`.
-- The only non-absurd case is `ref-tick` via `sRet`, which forces
-- `force P ≡ ret x`.
▷-ref-bNil-elim :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R} {B : Event√ E R → Set ℓB}
  → (P ▷ Q) ref B → P ref B
▷-ref-bNil-elim {P = P} {Q = Q} (ref-stable s _) =
  ⊥-elim (▷-never-stable {P = P} {Q = Q} s)
▷-ref-bNil-elim {P = P} {Q = Q} (ref-tick (sRet eqPQ) ¬B√x)
  with P .force in eq-P | Q .force in eq-Q | eqPQ
... | ret r | ret _   | refl = ref-tick (sRet eq-P) ¬B√x
... | ret r | sil _   | refl = ref-tick (sRet eq-P) ¬B√x
... | ret r | vis _   | refl = ref-tick (sRet eq-P) ¬B√x
... | ret r | mix _ _ | refl = ref-tick (sRet eq-P) ¬B√x
... | ret _ | ndbr _ _ _ _ | ()
... | sil _ | ret _   | ()
... | sil _ | sil _   | ()
... | sil _ | vis _   | ()
... | sil _ | mix _ _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | vis _ | ret _   | ()
... | vis _ | sil _   | ()
... | vis _ | vis _   | ()
... | vis _ | mix _ _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | ret _   | ()
... | ndbr _ _ _ _ | sil _   | ()
... | ndbr _ _ _ _ | vis _   | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | ret _   | ()
... | mix _ _ | sil _   | ()
... | mix _ _ | vis _   | ()
... | mix _ _ | mix _ _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()

-- Recursive helper: takes P, Q, the bigstep, and the refusal as explicit
-- arguments so the termination checker sees the bigstep shrink.
▷-failures-trace-go :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    (P Q : ITree E (ExtI I) R) (T : ITree E (ExtI I) R)
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → (P ▷ Q) ═⟨ s ⟩═► T → T ref B
  → failures P s B ⊎ failures Q s B

-- Base case.  T = (P ▷ Q); invert refusal via `▷-ref-bNil-elim`.
▷-failures-trace-go P Q _ bNil refusal =
  inj₁ (P , bNil , ▷-ref-bNil-elim refusal)

-- 1. sSil: only productive when force P ≡ sil P' and force Q ≠ ndbr.
▷-failures-trace-go P Q _ (bTau (sSil eq) big-step) refusal
  with P .force in eq-P | Q .force in eq-Q | eq
... | sil P' | ret _ | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sSil eq-P) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | sil P' | sil _ | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sSil eq-P) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | sil P' | vis _ | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sSil eq-P) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | sil P' | mix _ _ | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sSil eq-P) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | sil _ | ndbr _ _ _ _ | ()
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | mix _ _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | mix _ _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | mix _ _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()

-- 2. sNdbr: productive when force(P ▷ Q) is ndbr.
-- (a) Q distributes — five P-shapes × ndbr Q.
▷-failures-trace-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) refusal
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-failures-trace-go P Q' _ big-step refusal of λ where
      (inj₁ pFail)               → inj₁ pFail
      (inj₂ (tend , trQ' , ref)) → inj₂ (tend , bTau (sNdbr eq-Q fq-eq) trQ' , ref)
... | nothing | ()
▷-failures-trace-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) refusal
  | sil _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-failures-trace-go P Q' _ big-step refusal of λ where
      (inj₁ pFail)               → inj₁ pFail
      (inj₂ (tend , trQ' , ref)) → inj₂ (tend , bTau (sNdbr eq-Q fq-eq) trQ' , ref)
... | nothing | ()
▷-failures-trace-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) refusal
  | vis _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-failures-trace-go P Q' _ big-step refusal of λ where
      (inj₁ pFail)               → inj₁ pFail
      (inj₂ (tend , trQ' , ref)) → inj₂ (tend , bTau (sNdbr eq-Q fq-eq) trQ' , ref)
... | nothing | ()
▷-failures-trace-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) refusal
  | ndbr _ _ _ _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-failures-trace-go P Q' _ big-step refusal of λ where
      (inj₁ pFail)               → inj₁ pFail
      (inj₂ (tend , trQ' , ref)) → inj₂ (tend , bTau (sNdbr eq-Q fq-eq) trQ' , ref)
... | nothing | ()
▷-failures-trace-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) refusal
  | mix _ _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-failures-trace-go P Q' _ big-step refusal of λ where
      (inj₁ pFail)               → inj₁ pFail
      (inj₂ (tend , trQ' , ref)) → inj₂ (tend , bTau (sNdbr eq-Q fq-eq) trQ' , ref)
... | nothing | ()
-- (b) P distributes — P is ndbr, Q is not.
▷-failures-trace-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) refusal
  | ndbr fP _ _ _ | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sNdbr eq-P fp-eq) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | nothing | ()
▷-failures-trace-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) refusal
  | ndbr fP _ _ _ | sil _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sNdbr eq-P fp-eq) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | nothing | ()
▷-failures-trace-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) refusal
  | ndbr fP _ _ _ | vis _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sNdbr eq-P fp-eq) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | nothing | ()
▷-failures-trace-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) refusal
  | ndbr fP _ _ _ | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sNdbr eq-P fp-eq) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | nothing | ()
-- Absurd: force(P ▷ Q) is not ndbr in the remaining shapes.
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | ret _ | ret _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | ret _ | sil _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | ret _ | vis _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | ret _ | mix _ _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | sil _ | ret _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | sil _ | sil _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | sil _ | vis _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | sil _ | mix _ _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | vis _ | ret _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | vis _ | sil _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | vis _ | vis _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | vis _ | mix _ _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | mix _ _ | ret _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | mix _ _ | sil _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | mix _ _ | vis _ | ()
▷-failures-trace-go P Q _ (bTau (sNdbr eq eq-j) big-step) refusal | mix _ _ | mix _ _ | ()

-- 3. sVis: under new ▷, force(P ▷ Q) is never `vis _`.  All absurd.
▷-failures-trace-go P Q _ (bStep (sVis eq eq-j) big-step) refusal
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | vis _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | mix _ _ | ()

-- 4. sRet: productive only when force P ≡ ret r and Q is not ndbr.
▷-failures-trace-go P Q T (bStep (sRet eq) big-step) refusal
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret r | ndbr _ _ _ _ | ()
... | ret r | ret _ | refl =
    inj₁ (T , bStep (sRet eq-P) big-step , refusal)
... | ret r | sil _ | refl =
    inj₁ (T , bStep (sRet eq-P) big-step , refusal)
... | ret r | vis _ | refl =
    inj₁ (T , bStep (sRet eq-P) big-step , refusal)
... | ret r | mix _ _ | refl =
    inj₁ (T , bStep (sRet eq-P) big-step , refusal)
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | vis _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | mix _ _ | ()

-- 5. sMixSlide:
--    P=vis fP, Q≠ndbr → force = mix fP Q.  Slide goes to Q → in-Q.
--    P=mix fP P', Q≠ndbr → force = mix fP (P' ▷ Q).  Slide goes to
--    (P' ▷ Q); recurse.
▷-failures-trace-go P Q T (bTau (sMixSlide eq) big-step) refusal
  with P .force in eq-P | Q .force in eq-Q | eq
... | vis _ | ret _   | refl = inj₂ (T , big-step , refusal)
... | vis _ | sil _   | refl = inj₂ (T , big-step , refusal)
... | vis _ | vis _   | refl = inj₂ (T , big-step , refusal)
... | vis _ | mix _ _ | refl = inj₂ (T , big-step , refusal)
... | vis _ | ndbr _ _ _ _ | ()
... | mix _ P' | ret _   | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sMixSlide eq-P) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | mix _ P' | sil _   | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sMixSlide eq-P) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | mix _ P' | vis _   | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sMixSlide eq-P) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | mix _ P' | mix _ _ | refl =
    case ▷-failures-trace-go P' Q _ big-step refusal of λ where
      (inj₁ (tend , trP' , ref)) → inj₁ (tend , bTau (sMixSlide eq-P) trP' , ref)
      (inj₂ qFail)               → inj₂ qFail
... | mix _ _  | ndbr _ _ _ _ | ()
-- Absurd shapes: force isn't mix.
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()

-- 6. sMixVis: P=vis/mix fires a visible event via the mix node.
▷-failures-trace-go P Q T (bStep (sMixVis {at = at} {a = a} eq eq-j) big-step) refusal
  with P .force in eq-P | Q .force in eq-Q | eq
... | vis _ | ret _   | refl = inj₁ (T , bStep (sVis eq-P eq-j) big-step , refusal)
... | vis _ | sil _   | refl = inj₁ (T , bStep (sVis eq-P eq-j) big-step , refusal)
... | vis _ | vis _   | refl = inj₁ (T , bStep (sVis eq-P eq-j) big-step , refusal)
... | vis _ | mix _ _ | refl = inj₁ (T , bStep (sVis eq-P eq-j) big-step , refusal)
... | vis _ | ndbr _ _ _ _ | ()
... | mix _ _ | ret _   | refl = inj₁ (T , bStep (sMixVis eq-P eq-j) big-step , refusal)
... | mix _ _ | sil _   | refl = inj₁ (T , bStep (sMixVis eq-P eq-j) big-step , refusal)
... | mix _ _ | vis _   | refl = inj₁ (T , bStep (sMixVis eq-P eq-j) big-step , refusal)
... | mix _ _ | mix _ _ | refl = inj₁ (T , bStep (sMixVis eq-P eq-j) big-step , refusal)
... | mix _ _ | ndbr _ _ _ _ | ()
-- Absurd shapes: force isn't mix.
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()

-- Main decomposition lemma: thin wrapper around `▷-failures-trace-go`.
-- Renamed from `▷-failures-trace` for binary-operator `-elim` convention
-- (cf. `⊓-failures-elim`, `□-failures-elim`).
▷-failures-elim :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → failures (P ▷ Q) s B
  → failures P s B ⊎ failures Q s B
▷-failures-elim {P = P} {Q = Q} (T , bigstep , refusal) =
  ▷-failures-trace-go P Q T bigstep refusal

-----------------------------------------------------------------------------
-- Intro lemmas: lift a failure of P or a failure of Q into a failure of
-- `(P ▷ Q)`.
--
-- These are *partial* introductions, paired with operational step
-- witnesses, mirroring the structural form of `▷-step-*`.  The full
-- unconditional intros do not hold for plain `failures`: e.g. a stable
-- vis-shaped residual of P, lifted naively to `T ▷ Q`, becomes
-- non-stable (mix-shaped) and thus cannot satisfy `ref-stable`.  The
-- full sum `failures (P ▷ Q) = failures P ∪ failures Q` is recovered in
-- the divergence-closed model `failures⊥` (task A8).
--
-- For practical use downstream, we expose the most useful intros:
--
--   * `▷-failures-introP-vis`   : P fires a visible event via the mix
--                                  node → P-failure with vis-prefix
--                                  transfers verbatim.
--   * `▷-failures-introP-sRet`  : P fires √ r → P-failure starting with
--                                  √ r transfers (the post-√ residual
--                                  is `deadlock` in both).
--   * `▷-failures-introQ-slide` : when force P ≡ vis fP and Q ≠ ndbr,
--                                  the slide gives a τ-step to Q,
--                                  through which any Q-failure lifts.
-----------------------------------------------------------------------------

-- Intro-P via P-side visible firing.  When `force P ≡ vis fP` and
-- `Q-not-ndbr Q`, any failure of P' (the post-step residual) gives a
-- failure of `P ▷ Q` whose trace is prefixed by the visible event of
-- (at, a).
▷-failures-introP-vis :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P P' Q : ITree E (ExtI I) R}
    {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
    {at : AnyTypes E} {a : proj₁ at}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → ITree.force P ≡ vis fP
  → Q-not-ndbr Q
  → fP at a ≡ just P'
  → failures P' s B
  → failures (P ▷ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s) B
▷-failures-introP-vis eqP nndbr eq-j (T , trP' , ref) =
  T , bStep (sMixVis (force-▷-vis eqP nndbr) eq-j) trP' , ref

-- Intro-P via P-side √-firing.  When `force P ≡ ret r` and
-- `Q-not-ndbr Q`, any failure of `deadlock` with trace `s` lifts to a
-- failure of `P ▷ Q` with trace `√ r ∷ s`.
▷-failures-introP-sRet :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R} {r : R}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → ITree.force P ≡ ret r
  → Q-not-ndbr Q
  → failures (deadlock {E = E} {I = ExtI I} {R = R}) s B
  → failures (P ▷ Q) (√ r ∷ s) B
▷-failures-introP-sRet eqP nndbr (T , tail , ref) =
  T , bStep (sRet (force-▷-ret eqP nndbr)) tail , ref

-- Intro-Q via τ-slide.  When `force P ≡ vis fP` and `Q-not-ndbr Q`,
-- the slide step `(P ▷ Q) ─[τ]─► Q` lifts any failure of Q to a
-- failure of `P ▷ Q` with the same trace and refusal.
▷-failures-introQ-slide :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R}
    {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → ITree.force P ≡ vis fP
  → Q-not-ndbr Q
  → failures Q s B
  → failures (P ▷ Q) s B
▷-failures-introQ-slide eqP nndbr (T , trQ , ref) =
  T , bTau (▷-step-vis-τ-R eqP nndbr) trQ , ref

-----------------------------------------------------------------------------
-- A7: König-step postulate for `_▷_` divergence projection.
--
-- This is the SOLE postulate in this module (the six original `▷-step-*`
-- postulates from A1/A2 have all been restated as proven lemmas; what
-- remains here is genuinely non-constructive).
--
-- Extracting a side-divergence from `Divergent (P ▷ Q)` is fundamentally
-- non-constructive — it requires deciding whether an infinite τ-chain in
-- `(P ▷ Q)` commits to P-side actions or Q-side actions infinitely often.
-- The chain's individual steps can be P-walking (sSil/sNdbr-L of P,
-- sMixSlide off a `mix _ P'` mix-node coming from P, distributed
-- mergeNdbr▷-L branches) or Q-side-introducing (sMixSlide off a
-- `mix fP Q` mix-node sliding to Q, mergeNdbr▷-R branches when Q is
-- ndbr).  An infinite chain must consistently advance one side
-- infinitely often, but **deciding which is fundamentally non-constructive
-- over an infinite chain**.
--
-- This is exactly the König step for `_▷_`, matching
-- `divergent-□-asymm-project-LR` for `_□_` in `ExternalChoice_FD.agda`.
-- See that file's banner comment (lines ~2608–2633) for the enumerated
-- failed constructive workarounds:
--   1. "Follow LEFT, fall back to RIGHT" — fails on all-RIGHT chains.
--   2. "Decide on first step" — one step doesn't ensure infinitely many.
--   3. `{-# TERMINATING #-}` + LEFT-walking — accepted syntactically but
--      unsound (loops on RIGHT-dominated chains).
--   4. Coinductive Sum — Sum is inductive, no natural lazy form.
-- The same obstacle applies here verbatim because (P ▷ Q)'s τ-step set
-- is at least as expressive as (P □ Q)'s (both include sSil, sNdbr, and
-- sMixSlide on shared mix-node structure).
-----------------------------------------------------------------------------

postulate
  divergent-▷-asymm-project :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
      {P Q : ITree E (ExtI I) R}
    → Divergent (P ▷ Q) → Divergent P ⊎ Divergent Q

-----------------------------------------------------------------------------
-- A7: divergences decomposition for `_▷_`.
--
-- A divergence of `(P ▷ Q)` decomposes into a divergence of `P` or `Q`.
-- The proof mirrors `▷-failures-trace-go`'s case structure on the bigstep
-- reaching the divergent witness.  The only König-step is in the `bNil`
-- base case (witness ≡ `P ▷ Q`), discharged by
-- `divergent-▷-asymm-project`.  All non-base cases recurse on a smaller
-- bigstep and repackage.
-----------------------------------------------------------------------------

-- Recursive helper for ▷-divergences-elim: takes P, Q, the bigstep, and
-- the divergent witness as explicit arguments so the termination checker
-- sees the bigstep shrink.  Mirrors `▷-failures-trace-go`.  The trace is
-- split as `prefix ++ suffix`: the bigstep covers `prefix` and reaches `T`,
-- which is divergent; `suffix` is the post-divergence tail that the
-- IsDivergence record carries forward verbatim.
▷-divergences-elim-go :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    (P Q : ITree E (ExtI I) R) (T : ITree E (ExtI I) R)
    {pre suf : List (Event√ E R)}
  → (P ▷ Q) ═⟨ pre ⟩═► T → Divergent T
  → divergences P (pre ++ suf) ⊎ divergences Q (pre ++ suf)

-- Base case.  T = (P ▷ Q); use the postulate to split the divergence.
-- prefix = [], so the result trace is `[] ++ suf ≡ suf`.
▷-divergences-elim-go P Q _ {suf = suf} bNil dw
  with divergent-▷-asymm-project dw
... | inj₁ dP =
    inj₁ (record { prefix = [] ; suffix = suf ; split = refl
                 ; witness = P ; reach = bNil ; divwit = dP })
... | inj₂ dQ =
    inj₂ (record { prefix = [] ; suffix = suf ; split = refl
                 ; witness = Q ; reach = bNil ; divwit = dQ })

-- 1. sSil: only productive when force P ≡ sil P' and force Q ≠ ndbr.
▷-divergences-elim-go P Q _ (bTau (sSil eq) big-step) dw
  with P .force in eq-P | Q .force in eq-Q | eq
... | sil P' | ret _ | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sSil eq-P) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | sil P' | sil _ | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sSil eq-P) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | sil P' | vis _ | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sSil eq-P) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | sil P' | mix _ _ | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sSil eq-P) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | sil _ | ndbr _ _ _ _ | ()
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | mix _ _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | mix _ _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | mix _ _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()

-- 2. sNdbr: productive when force(P ▷ Q) is ndbr.
-- (a) Q distributes — five P-shapes × ndbr Q.
▷-divergences-elim-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) dw
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-divergences-elim-go P Q' _ big-step dw of λ where
      (inj₁ dP)                  → inj₁ dP
      (inj₂ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₂ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sNdbr eq-Q fq-eq) r
                     ; divwit = d })
... | nothing | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) dw
  | sil _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-divergences-elim-go P Q' _ big-step dw of λ where
      (inj₁ dP)                  → inj₁ dP
      (inj₂ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₂ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sNdbr eq-Q fq-eq) r
                     ; divwit = d })
... | nothing | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) dw
  | vis _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-divergences-elim-go P Q' _ big-step dw of λ where
      (inj₁ dP)                  → inj₁ dP
      (inj₂ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₂ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sNdbr eq-Q fq-eq) r
                     ; divwit = d })
... | nothing | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) dw
  | ndbr _ _ _ _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-divergences-elim-go P Q' _ big-step dw of λ where
      (inj₁ dP)                  → inj₁ dP
      (inj₂ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₂ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sNdbr eq-Q fq-eq) r
                     ; divwit = d })
... | nothing | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) dw
  | mix _ _ | ndbr fQ _ _ _ | refl with fQ i a in fq-eq | eq-j
... | just Q' | refl =
    case ▷-divergences-elim-go P Q' _ big-step dw of λ where
      (inj₁ dP)                  → inj₁ dP
      (inj₂ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₂ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sNdbr eq-Q fq-eq) r
                     ; divwit = d })
... | nothing | ()
-- (b) P distributes — P is ndbr, Q is not.
▷-divergences-elim-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) dw
  | ndbr fP _ _ _ | ret _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sNdbr eq-P fp-eq) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | nothing | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) dw
  | ndbr fP _ _ _ | sil _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sNdbr eq-P fp-eq) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | nothing | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) dw
  | ndbr fP _ _ _ | vis _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sNdbr eq-P fp-eq) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | nothing | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr {i = i} {a = a} eq eq-j) big-step) dw
  | ndbr fP _ _ _ | mix _ _ | refl with fP i a in fp-eq | eq-j
... | just P' | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sNdbr eq-P fp-eq) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | nothing | ()
-- Absurd: force(P ▷ Q) is not ndbr in the remaining shapes.
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | ret _ | ret _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | ret _ | sil _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | ret _ | vis _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | ret _ | mix _ _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | sil _ | ret _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | sil _ | sil _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | sil _ | vis _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | sil _ | mix _ _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | vis _ | ret _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | vis _ | sil _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | vis _ | vis _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | vis _ | mix _ _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | mix _ _ | ret _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | mix _ _ | sil _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | mix _ _ | vis _ | ()
▷-divergences-elim-go P Q _ (bTau (sNdbr eq eq-j) big-step) dw | mix _ _ | mix _ _ | ()

-- 3. sVis: under new ▷, force(P ▷ Q) is never `vis _`.  All absurd.
▷-divergences-elim-go P Q _ (bStep (sVis eq eq-j) big-step) dw
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | vis _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | mix _ _ | ()

-- 4. sRet: productive only when force P ≡ ret r and Q is not ndbr.  T is
-- `deadlock`, so `Divergent T` is impossible.
▷-divergences-elim-go P Q T (bStep (sRet eq) big-step) dw
  with P .force in eq-P | Q .force in eq-Q | eq
... | ret r | ndbr _ _ _ _ | ()
... | ret r | ret _ | refl =
        ⊥-elim (no-τ-from-deadlock-bigstep big-step (dw .Divergent.step))
... | ret r | sil _ | refl =
        ⊥-elim (no-τ-from-deadlock-bigstep big-step (dw .Divergent.step))
... | ret r | vis _ | refl =
        ⊥-elim (no-τ-from-deadlock-bigstep big-step (dw .Divergent.step))
... | ret r | mix _ _ | refl =
        ⊥-elim (no-τ-from-deadlock-bigstep big-step (dw .Divergent.step))
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | vis _ | ret _ | ()
... | vis _ | sil _ | ()
... | vis _ | vis _ | ()
... | vis _ | ndbr _ _ _ _ | ()
... | vis _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()
... | mix _ _ | ret _ | ()
... | mix _ _ | sil _ | ()
... | mix _ _ | vis _ | ()
... | mix _ _ | ndbr _ _ _ _ | ()
... | mix _ _ | mix _ _ | ()

-- 5. sMixSlide:
--    P=vis fP, Q≠ndbr → force = mix fP Q.  Slide goes to Q → inj₂.
--    P=mix fP P', Q≠ndbr → force = mix fP (P' ▷ Q).  Slide goes to
--    (P' ▷ Q); recurse.
▷-divergences-elim-go P Q T (bTau (sMixSlide eq) big-step) dw
  with P .force in eq-P | Q .force in eq-Q | eq
... | vis _ | ret _   | refl =
    inj₂ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = big-step ; divwit = dw })
... | vis _ | sil _   | refl =
    inj₂ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = big-step ; divwit = dw })
... | vis _ | vis _   | refl =
    inj₂ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = big-step ; divwit = dw })
... | vis _ | mix _ _ | refl =
    inj₂ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = big-step ; divwit = dw })
... | vis _ | ndbr _ _ _ _ | ()
... | mix _ P' | ret _   | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sMixSlide eq-P) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | mix _ P' | sil _   | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sMixSlide eq-P) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | mix _ P' | vis _   | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sMixSlide eq-P) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | mix _ P' | mix _ _ | refl =
    case ▷-divergences-elim-go P' Q _ big-step dw of λ where
      (inj₁ record { prefix = pre ; suffix = suf ; split = sp
                   ; witness = w ; reach = r ; divwit = d }) →
        inj₁ (record { prefix = pre ; suffix = suf ; split = sp
                     ; witness = w ; reach = bTau (sMixSlide eq-P) r
                     ; divwit = d })
      (inj₂ dQ)                  → inj₂ dQ
... | mix _ _  | ndbr _ _ _ _ | ()
-- Absurd shapes: force isn't mix.
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()

-- 6. sMixVis: P=vis/mix fires a visible event via the mix node.  Build
-- a P-divergence by anchoring the trace at P's corresponding visible
-- transition.
▷-divergences-elim-go P Q T (bStep (sMixVis {at = at} {a = a} eq eq-j) big-step) dw
  with P .force in eq-P | Q .force in eq-Q | eq
... | vis _ | ret _   | refl =
    inj₁ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = bStep (sVis eq-P eq-j) big-step
                 ; divwit = dw })
... | vis _ | sil _   | refl =
    inj₁ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = bStep (sVis eq-P eq-j) big-step
                 ; divwit = dw })
... | vis _ | vis _   | refl =
    inj₁ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = bStep (sVis eq-P eq-j) big-step
                 ; divwit = dw })
... | vis _ | mix _ _ | refl =
    inj₁ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = bStep (sVis eq-P eq-j) big-step
                 ; divwit = dw })
... | vis _ | ndbr _ _ _ _ | ()
... | mix _ _ | ret _   | refl =
    inj₁ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = bStep (sMixVis eq-P eq-j) big-step
                 ; divwit = dw })
... | mix _ _ | sil _   | refl =
    inj₁ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = bStep (sMixVis eq-P eq-j) big-step
                 ; divwit = dw })
... | mix _ _ | vis _   | refl =
    inj₁ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = bStep (sMixVis eq-P eq-j) big-step
                 ; divwit = dw })
... | mix _ _ | mix _ _ | refl =
    inj₁ (record { prefix = _ ; suffix = _ ; split = refl
                 ; witness = T ; reach = bStep (sMixVis eq-P eq-j) big-step
                 ; divwit = dw })
... | mix _ _ | ndbr _ _ _ _ | ()
-- Absurd shapes: force isn't mix.
... | ret _ | ret _ | ()
... | ret _ | sil _ | ()
... | ret _ | vis _ | ()
... | ret _ | ndbr _ _ _ _ | ()
... | ret _ | mix _ _ | ()
... | sil _ | ret _ | ()
... | sil _ | sil _ | ()
... | sil _ | vis _ | ()
... | sil _ | ndbr _ _ _ _ | ()
... | sil _ | mix _ _ | ()
... | ndbr _ _ _ _ | ret _ | ()
... | ndbr _ _ _ _ | sil _ | ()
... | ndbr _ _ _ _ | vis _ | ()
... | ndbr _ _ _ _ | ndbr _ _ _ _ | ()
... | ndbr _ _ _ _ | mix _ _ | ()

-- Main divergences decomposition lemma: thin wrapper around
-- `▷-divergences-elim-go`.
▷-divergences-elim :
    ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R}
    {s : List (Event√ E R)}
  → divergences (P ▷ Q) s
  → divergences P s ⊎ divergences Q s
▷-divergences-elim {P = P} {Q = Q}
    record { prefix = pre ; suffix = suf ; split = refl
           ; witness = T ; reach = bigstep ; divwit = dw } =
  ▷-divergences-elim-go P Q T {pre = pre} {suf = suf} bigstep dw

-----------------------------------------------------------------------------
-- Intro lemmas: lift a divergence of P or Q into a divergence of `P ▷ Q`.
--
--   * `▷-divergences-introP` : `Q-not-ndbr Q → Divergent P → Divergent (P ▷ Q)`.
--     Precondition `Q-not-ndbr Q`: when Q is ndbr, force(P ▷ Q) is itself
--     an ndbr that always takes Q-side branches via mergeNdbr▷-R, so P's
--     τ-step does not propagate.  Under Q-not-ndbr, each of P's possible
--     τ-step shapes (sSil/sNdbr/sMixSlide) lifts to a corresponding τ-step
--     of (P ▷ Q) that lands on (P.next ▷ Q), preserving the divergence.
--
--   * `▷-divergences-introQ-slide` :
--     `force P ≡ vis fP → Q-not-ndbr Q → Divergent Q → Divergent (P ▷ Q)`.
--     A single τ-slide step `(P ▷ Q) ─[τ]─► Q` (via `▷-step-vis-τ-R`)
--     then chains Q's divergence.  Other P-shapes give different
--     operational paths to Q and are not covered by this intro; the
--     vis-shape is the canonical CSP "P stable, slide to Q" form.
-----------------------------------------------------------------------------

▷-divergences-introP : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                         ⦃ _ : DecEq R ⦄
                         {P Q : ITree E (ExtI I) R}
                       → Q-not-ndbr Q
                       → Divergent P → Divergent (P ▷ Q)
▷-divergences-introP {P = P} {Q = Q} nndbr dP .Divergent.next =
  dP .Divergent.next ▷ Q
▷-divergences-introP {P = P} {Q = Q} nndbr dP .Divergent.step
  with dP .Divergent.step
... | sSil eqP        = sSil (force-▷-sil eqP nndbr)
... | sNdbr eqP eqJ   = ▷-step-ndbr-τ-L eqP nndbr eqJ
... | sMixSlide eqP   = sMixSlide (force-▷-mix eqP nndbr)
▷-divergences-introP {P = P} {Q = Q} nndbr dP .Divergent.diverge =
  ▷-divergences-introP nndbr (dP .Divergent.diverge)

▷-divergences-introQ-slide : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                               ⦃ _ : DecEq R ⦄
                               {P Q : ITree E (ExtI I) R}
                               {fP : (at : AnyTypes E)
                                   → ContinueType at
                                       (Maybe (ITree E (ExtI I) R))}
                             → ITree.force P ≡ vis fP
                             → Q-not-ndbr Q
                             → Divergent Q → Divergent (P ▷ Q)
▷-divergences-introQ-slide {Q = Q} eqP nndbr dQ =
  record { next    = Q
         ; step    = ▷-step-vis-τ-R eqP nndbr
         ; diverge = dQ }

-----------------------------------------------------------------------------
-- A8: `failures⊥` decomposition for `_▷_`.
--
-- Combines `▷-failures-elim` (A6) and `▷-divergences-elim` (A7) into the
-- divergence-strict failures⊥ model.  Since
-- `failures⊥ P s B ≡ failures P s B ⊎ divergences P s`, the decomposition
-- is mechanical: case-split on the input ⊎, dispatch to the appropriate
-- elimination lemma, and repackage.
-----------------------------------------------------------------------------

▷-failures⊥-elim :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → failures⊥ (P ▷ Q) s B
  → failures⊥ P s B ⊎ failures⊥ Q s B
▷-failures⊥-elim (inj₁ failure) with ▷-failures-elim failure
... | inj₁ fP = inj₁ (inj₁ fP)
... | inj₂ fQ = inj₂ (inj₁ fQ)
▷-failures⊥-elim (inj₂ divergence) with ▷-divergences-elim divergence
... | inj₁ dP = inj₁ (inj₂ dP)
... | inj₂ dQ = inj₂ (inj₂ dQ)

-----------------------------------------------------------------------------
-- A8 intros: lift a `failures⊥` of P or Q into a `failures⊥` of (P ▷ Q).
--
-- Unconditional intros (`failures⊥ P s B → failures⊥ (P ▷ Q) s B`) are
-- NOT cleanly provable in the current scaffolding:
--   * The failure-side input `inj₁ (failure P s B)` runs into the same
--     blocker as A6's plain-`failures` intros — a stable P-residual at the
--     end of a trace cannot be carried verbatim under `_▷_` because
--     `force (P ▷ Q)` is `mix`-shaped (non-stable) when `force P ≡ vis _`
--     (see the banner above `▷-failures-introP-vis` for the full story).
--   * The divergence-side input `inj₂ (divergences P s)` needs a
--     bigstep-lift from `P ═⟨ pre ⟩═► W` to `(P ▷ Q) ═⟨ pre ⟩═► (W ▷ Q)`
--     to relocate the divergent witness; no such helper exists yet.
--
-- The intros below restrict to operationally explicit cases, mirroring
-- the A6 intro layout.  Each variant pairs a P-side or Q-side operational
-- step witness with a `failures⊥` premise.
--
--   * `▷-failures⊥-introP-vis`     : P fires a visible event via the mix
--                                     node → failure of P' transfers, with
--                                     vis-prefix.  Lifts A6 to `inj₁`.
--   * `▷-failures⊥-introP-sRet`    : P fires √ r → P-failure starting with
--                                     √ r transfers.  Lifts A6 to `inj₁`.
--   * `▷-failures⊥-introQ-slide`   : `force P ≡ vis fP` + `Q-not-ndbr Q`
--                                     enable τ-slide; any failures⊥ of Q
--                                     (both failure and divergence sides)
--                                     transfers verbatim.  Both sides
--                                     lift through the same one-τ-step
--                                     prefix.
--   * `▷-failures⊥-introP-Divergent` :
--       `Q-not-ndbr Q → Divergent P → failures⊥ (P ▷ Q) s B`
--       for ANY trace `s` and ANY refusal `B`.  Divergence on the left
--       lifts to a divergence at the empty trace of (P ▷ Q), which then
--       extends to every trace by `div-extension-closed`.
--   * `▷-failures⊥-introQ-Divergent-slide` :
--       `force P ≡ vis fP → Q-not-ndbr Q → Divergent Q → failures⊥ (P ▷ Q) s B`
--       for ANY trace `s`.  Same divergence-closure trick but routed
--       through `▷-divergences-introQ-slide`.
-----------------------------------------------------------------------------

-- Failure-side intros (thin `inj₁`-wrappers around A6).

▷-failures⊥-introP-vis :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P P' Q : ITree E (ExtI I) R}
    {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
    {at : AnyTypes E} {a : proj₁ at}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → ITree.force P ≡ vis fP
  → Q-not-ndbr Q
  → fP at a ≡ just P'
  → failures P' s B
  → failures⊥ (P ▷ Q) (evl (evLabel (proj₁ at) (proj₂ at) a) ∷ s) B
▷-failures⊥-introP-vis eqP nndbr eq-j fP' =
  inj₁ (▷-failures-introP-vis eqP nndbr eq-j fP')

▷-failures⊥-introP-sRet :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R} {r : R}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → ITree.force P ≡ ret r
  → Q-not-ndbr Q
  → failures (deadlock {E = E} {I = ExtI I} {R = R}) s B
  → failures⊥ (P ▷ Q) (√ r ∷ s) B
▷-failures⊥-introP-sRet eqP nndbr fail =
  inj₁ (▷-failures-introP-sRet eqP nndbr fail)

-- Q-slide intro: handles BOTH the failure side (via A6) AND the
-- divergence side (via A7), since the τ-slide step extends a bigstep
-- by exactly one τ on the left.
▷-failures⊥-introQ-slide :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R}
    {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → ITree.force P ≡ vis fP
  → Q-not-ndbr Q
  → failures⊥ Q s B
  → failures⊥ (P ▷ Q) s B
▷-failures⊥-introQ-slide eqP nndbr (inj₁ failQ) =
  inj₁ (▷-failures-introQ-slide eqP nndbr failQ)
▷-failures⊥-introQ-slide {Q = Q} {s = s} eqP nndbr
    (inj₂ record { prefix = pre ; suffix = suf ; split = sp
                 ; witness = W ; reach = r ; divwit = dw }) =
  inj₂ (record { prefix = pre ; suffix = suf ; split = sp
               ; witness = W
               ; reach = bTau (▷-step-vis-τ-R eqP nndbr) r
               ; divwit = dw })

-- Divergence-side total intro: `Divergent P` lifts to a divergence at
-- EVERY trace of (P ▷ Q), via `▷-divergences-introP` and
-- `div-extension-closed`.
▷-failures⊥-introP-Divergent :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → Q-not-ndbr Q
  → Divergent P
  → failures⊥ (P ▷ Q) s B
▷-failures⊥-introP-Divergent {s = s} nndbr dP =
  inj₂ (div-extension-closed {t = s}
         (empty-div-iff (▷-divergences-introP nndbr dP)))

-- Divergence-side total intro for Q via τ-slide: `force P ≡ vis fP` and
-- `Q-not-ndbr Q` enable the τ-slide to Q, so `Divergent Q` lifts to a
-- divergence at EVERY trace of (P ▷ Q).
▷-failures⊥-introQ-Divergent-slide :
    ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
    {P Q : ITree E (ExtI I) R}
    {fP : (at : AnyTypes E) → ContinueType at (Maybe (ITree E (ExtI I) R))}
    {s : List (Event√ E R)} {B : Event√ E R → Set ℓB}
  → ITree.force P ≡ vis fP
  → Q-not-ndbr Q
  → Divergent Q
  → failures⊥ (P ▷ Q) s B
▷-failures⊥-introQ-Divergent-slide {s = s} eqP nndbr dQ =
  inj₂ (div-extension-closed {t = s}
         (empty-div-iff (▷-divergences-introQ-slide eqP nndbr dQ)))

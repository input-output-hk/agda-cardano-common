{-# OPTIONS --guardedness #-}

-- THE FD CONGRUENCE SUITE — index module and the `≈FD` congruence row.
--
-- Part 1 lifts the `≈DR` operator congruences of `CSP.Laws.Bisim.DRCongruence{,Rep}`
-- to `≈FD` (and, for interrupt, also to `FSim`/`⊑FD`) through
-- `Semantics.DRImpliesFD.drbisim→≈FD` / `.drbisim→fsim`.  Every big refinement in this
-- repo already performs this composition by hand at each use site; these give the
-- results names.
--
-- Part 2 re-exports the complete FD congruence / monotonicity suite so downstream
-- users need one import — including the premise types (`SepDR`, `Sep△`, `SepPar`,
-- `Alpha`, `Disj`, `OffersOnly`, `CongCell`, `FCell`) that those statements mention, so
-- hypotheses can be named through the index too, and the statement vocabulary
-- (`DRbisim`, `FSim`, `fsim→⊑FD`, `_≈FD_`, `_⊑FD_`) they are phrased in.
--
-- ===================================================================================
-- THREE SHAPES OF "MONOTONICITY" TRAVEL THROUGH THIS INDEX.  They are NOT equally
-- useful, and knowing which shape a name has tells you where it can be used:
--
--   1. `FSim → FSim` — the CONGRUENCE (`⊓-fsim`, `□-fsim`, `Par-fsim`, `Hide-fsim`,
--      `⦀Fin-fsim`, `Θ-fsim`, …).  ESSENTIAL: the only thing that composes an FSim
--      tower, and the only thing that crosses a hide (see "WHY HIDING IS THE CRUX").
--   2. `⊑FD → ⊑FD` — the TRUE PRECONGRUENCE (`Par-mono-⊑FD`, `∥`/`⦀`/`⦀Fin`/`⦀⋆`/`∥⁺`/
--      `∥Fin` variants, `⊓-mono-⊑FD` + `⨅⁺`/`⨅Fin`, `□-mono-⊑FD` + `□Fin`/`□⋆`,
--      `Θ-mono-⊑FD`, `⟶₀-mono-⊑FD`, `Output-mono-⊑FD`, `＆-mono-⊑FD`, `◁▷-mono-⊑FD`,
--      the LOOP family `iter-mono-⊑FD` / `loop-mono-⊑FD` / `while-mono-⊑FD` /
--      `loopc-mono-⊑FD` + `loop0-mono-⊑FD`, the RENAMING pair `renameInv-mono-⊑FD` /
--      `renameMap-mono-⊑FD`, and the BIND family `>>=-mono-⊑FD` / `bindNoτ` / `bindκ` /
--      `>>-mono-⊑FD` + `⨾⋆`/`⨾Fin`).  THE VALUABLE SHAPE:
--      a `⊑FD` premise can come from ANYWHERE — a hand-built bisimulation, a
--      denotational argument, an earlier refinement step, or a cashed-out `FSim` — and
--      chains of these compose freely.
--   3. `FSim → ⊑FD` — a CASH-OUT wrapper, body literally `fsim→⊑FD (X-fsim …)`.  Adds a
--      name, not power: the caller can write that line, and because `⊑FD → FSim`
--      completeness is out of scope (`CSP/Laws_status.md:1104`) such a wrapper can never
--      consume a `⊑FD` FACT, so it cannot appear in a `⊑FD`-only chain.
--
-- POLICY: where a shape-2 law exists, it OWNS the `-mono-⊑FD` name and the shape-3
-- wrapper is deleted, not renamed.  FIFTEEN wrappers have been retired on that basis:
-- `⊓-mono-⊑FD` + `prefix-mono-⊑FD` (`CSP.Laws.FSim.IChoiceCong`),
-- `⦀Fin-mono-⊑FD` + `⦀⋆-mono-⊑FD` (`CSP.Laws.FSim.ParCongRep`),
-- `Θ-mono-⊑FD` (`CSP.Laws.FSim.ThrowCong`, superseded by
-- `CSP.Laws.FD.ThrowMonoFD`), `□-mono-⊑FD` (`CSP.Laws.FSim.ExtChoiceCong`, superseded
-- by `CSP.Laws.FD.ExtChoiceMonoFD`), and THE WHOLE OF `CSP.Laws.FD.LoopMonoFD`, which
-- has consequently been DELETED as a module: its bind half (`Bind-mono-⊑FD` /
-- `bindNoτ-mono-⊑FD` / `bindκ-mono-⊑FD` / `>>-mono-⊑FD`, superseded by
-- `CSP.Laws.FD.BindMonoFD`, the general one renamed `>>=-mono-⊑FD` after the operator to
-- match `CSP.Laws.Traces`'s `>>=-mono-L` / `>>=-mono-k`), its `loop0-mono-⊑FD-fsim`
-- (whose `-fsim` suffix existed only to dodge the clash with the fact-shaped
-- `IterateMonoFD.loop0-mono-⊑FD`), and finally its loop half — `iter-mono-⊑FD` /
-- `loop-mono-⊑FD` / `loopc-mono-⊑FD` / `while-mono-⊑FD`, superseded by
-- `CSP.Laws.FD.IterMonoFD`.  Do not re-add them; write `fsim→⊑FD (X-fsim …)` at
-- the call site, or feed that term to the shape-2 law.  Surviving shape-3 names are kept
-- ONLY because no shape-2 counterpart exists yet: `△-mono-⊑FD-dr`,
-- `▷-mono-R-⊑FD-fsim` (two-sided is FALSE), and `αpar-mono-⊑FD-fsim-df` / `Hide-mono-⊑FD-df`
-- (both provably must stay conditional).  Note the naming split: `-dr`/`-fsim` name the
-- WITNESS shape of the premise (never mint a bare `-mono-⊑FD` for one of these — that
-- name is reserved for a fact-shaped, `⊑FD`-premised law), whereas `-df` names a SIDE
-- CONDITION on an otherwise fact-shaped (`Hide-mono-⊑FD-df`) or witness-shaped
-- (`αpar-mono-⊑FD-fsim-df`) law — the two suffix kinds are independent and can co-occur.
-- ===================================================================================
--
-- THE "ONE IMPORT" CLAIM IS NOW BUILD-TESTED, not asserted.  `CSP.Examples.FSimTower`
-- routes every FSim-suite name it uses (`⊓-refine-fsim`, `⦀Fin-fsim`, `Hide-fsim`,
-- `FSim`, `fsim→⊑FD`, `_⊑FD_`, `Alpha`, `Disj`, `OffersOnly`, `OffersOnly-Prefix₀`,
-- `OffersOnly-Skip`) through THIS module, so a regression in the index breaks that
-- module's typecheck.  What it still imports directly, and why: `Process_Trees` and
-- `CSP.Operators` (the tree type and the OPERATOR definitions — process syntax, not
-- congruence results; the index opens `CSP.Operators` non-publicly on purpose, since
-- flooding a law index with the whole operator vocabulary would make its namespace
-- unpredictable) and the stdlib.
--
-- The MENU congruence `pchoice-cong-FD` IS now in the index (Part 2).  Correction to
-- earlier drafts of this header: it never needed "lifting out" of the anonymous
-- `module _ {ℓr} {R-set}` block of `CSP.Laws.FD.RenameStepRel` (:93, declaration :166) —
-- an anonymous `module _` is auto-opened into its parent, so the name was ALREADY a
-- general export of `RenameStepRel`, with `{ℓr} {R-set}` prepended as implicits.  Its
-- displayed type mentions that block's `private Menu` abbreviation, but `private` hides
-- only the NAME: the definition still unfolds, so an outside caller can spell the type
-- out (`(at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R-set))`) and apply
-- it.  Both facts were machine-checked before this re-export was added.  So `RenameStepRel`
-- is untouched and the promotion is a pure indexing change.  There is no `pchoice-fsim`.
--
-- ===================================================================================
-- THE TWO `Sep` RECORDS ARE DIFFERENT.
--
-- `CSP.Laws.Bisim.DRCongruence.Sep` is `⊤`-carrier-only (both operands return `⊤ {ℓr}`,
-- the shape `_∥⇘_⇙_`/`_⦀_`/`⦀Fin`/`⦀⋆` all use).  It drives Part 1's `Par-cong-FD` /
-- `⦀-cong-FD` / `⦀Fin-cong-FD` / `⦀⋆-cong-FD` below and is imported here (renamed) as
-- `SepDR`, and re-exported under that name.
--
-- `CSP.Laws.FSim.ParCong.Sep` is a DIFFERENT, two-carrier `{R₁ R₂}` record (only the
-- IMPL pair needs it, since only the impl composite is inverted in an `FSim` proof).
-- It is re-exported in Part 2 (renamed) as `SepPar`.
--
-- The two are NOT interchangeable — a `SepDR A P Q : Set _` at `R = ⊤` and a
-- `SepPar A P Q : Set _` at arbitrary `{R₁ R₂}` are different types even when
-- instantiated at the same `P Q : PTree E (ExtI E) (⊤ {ℓr})`, because their `stepL`/
-- `stepR` closure fields quantify over different label sets (`Label R₁`/`Label R₂` vs
-- a shared `Label (⊤ {ℓr})`).  Do not unify them; this distinction is exactly what
-- Task 6 (`CSP.Laws.FSim.ParCongRep`) needs kept clear.
-- ===================================================================================
--
-- POSTULATE PROVENANCE.  No postulate is declared here.  Inherited, per lemma
-- (verified against source, not transcribed from the plan header — see corrections
-- below):
--
--   hide-cong-FD, Par-cong-FD, ⦀-cong-FD, ⦀Fin-cong-FD, ⦀⋆-cong-FD,
--   rename-cong-FD, renameMap-cong-FD, △-cong-FD, △-fsim, △-mono-⊑FD-dr
--                            ← ¬-divergent→normal (Semantics/DRImpliesFD.agda:67).
--     This holds even for `rename-cong-FD`/`renameMap-cong-FD`, whose underlying ≈DR
--     congruence (`cong-renameInv`/`cong-renameMap`) is ITSELF postulate-free (see
--     DRCongruence.agda's own "ZERO postulates" banner ~line 1233) — the postulate is
--     injected unconditionally by `drbisim→fsim`'s `.stab` field
--     (DRImpliesFD.agda:143), for ANY `DRbisim` argument, so every wrapper that routes
--     through `drbisim→≈FD`/`drbisim→fsim` picks it up regardless of the underlying
--     congruence's own cost.
--   Par-mono-⊑FD, ∥-mono-⊑FD, ⦀-mono-⊑FD, ⦀Fin-mono-⊑FD, ⦀⋆-mono-⊑FD,
--   ∥⁺-mono-⊑FD, ∥Fin-mono-⊑FD (CSP.Laws.FD.ParallelMonoFD, re-exported)
--                            ← offer-LEM (ParallelRefusals.agda:162),
--                              Par-Diverges→ (ParallelDivergence.agda:56),
--                              Diverges-LEM (FDTransfer).
--     ALL THREE are reached TRANSITIVELY, on equal footing: none of the three names
--     occurs anywhere in ParallelMonoFD.agda outside its own header comment, and that
--     comment names all three on ONE line (currently :27; an earlier draft also cited a
--     line that in fact mentions `Par-reach-div` — an ordinary definition, not a
--     postulate).  The route is ParallelMonoFD's single
--     `CSP.Laws.FD.ParallelDivergence` import (currently :65), which brings in only
--     `Par-reach-div`/`Par-div-intro`.
--     The FOUR replicated folds add NOTHING: `⦀Fin`/`⦀⋆` are inductions over
--     `⦀-mono-⊑FD` with `⊑FD-refl Skip` at the base, and `∥⁺`/`∥Fin` (Layer 9) are
--     inductions over `∥-mono-⊑FD` whose bases are OPERAND hypotheses (`[|A|]` has no
--     unit, so both are non-empty folds); their provenance is exactly this one.
--   ⊓-mono-⊑FD, ⊓-mono-⊇F⊥, ⊓-mono-⊇D, ⨅⁺-mono-⊑FD, ⨅Fin-mono-⊑FD
--   (CSP.Laws.FD.IChoiceMonoFD, re-exported)
--                            ← NONE.  Its whole proof is a union transfer over
--                              `FDLawsIChoiceAssoc`'s constructive `⊓-failures⊥→`/`←l`/
--                              `←r` and `⊓-div→`/`←l`/`←r`; no classical ingredient.
--     The two replicated folds add NOTHING: inductions over `⊓-mono-⊑FD`.  Both are
--     NON-EMPTY (`⨅⁺ P [] = P`, `⨅Fin zero f = f fzero`), so — unlike the `⦀`/`□` folds —
--     they do not even use `⊑FD-refl`; the base case IS an operand hypothesis.
--   ＆-mono-⊑FD, ◁▷-mono-⊑FD, Output-mono-⊑FD (CSP.Laws.FD.DerivedMonoFD, re-exported)
--                            ← NONE, and this one is CERTIFIED, not argued:
--                              `agda --safe CSP/Laws/FD/DerivedMonoFD.agda` exits 0, so the
--                              whole import closure is postulate-free.  `Output`'s
--                              decomposition is built directly over the LTS (it cannot
--                              reuse `⟶₀-mono-⊑FD`: `Output-cont` fires on the single
--                              carried value, `Prefix-cont` on all of them), and the two
--                              `Bool` splits ride on `force-≡→⊑FD`, now hoisted into
--                              `Semantics.FailuresDivergences` and proved directly over
--                              the LTS (the `CSP.Laws.FD.BindFD` dependency went with it).
--   loop0-mono-⊑FD (CSP.Laws.FD.IterateMonoFD, re-exported), hence also
--   loopc-mono-⊑FD (which IS it — `loopc` and `loop0` are the same definition)
--                            ← loop-Diverges→ (IterateFD), a `loop0`-SPECIFIC postulate.
--   iter-mono-⊑FD / loop-mono-⊑FD / while-mono-⊑FD (CSP.Laws.FD.IterMonoFD, re-exported)
--                            ← `iter-div-split` (CSP.Laws.FSim.LoopCong), i.e. the SAME
--                              two classical facts as the LoopCong family below and NOT
--                              `loop-Diverges→`: `iter-div-split` is a DERIVED lemma
--                              covering every `k`, so the general `iter` law assumes
--                              strictly less than the `loop0` specialisation above.
--                              `loop`/`while` add only `bindκ-mono-⊑FD`'s inheritance
--                              (`Diverges-LEM`); the `⊇F⊥` half needs no classical
--                              ingredient of its own — the body-side reconstruction goes
--                              through the `√` tick, which is structural.
--   renameInv-mono-⊇D / -⊇F⊥ / -⊑FD and the renameMap trio
--   (CSP.Laws.FD.RenameMonoFD, re-exported)
--                            ← NONE.  Not "argued postulate-free" but STRUCTURALLY so:
--                              `renameInv` relabels step-for-step, so `Diverges` transfers
--                              by a plain corecursive projection in BOTH directions
--                              (`ren-Diverges→`/`←`) with no König step, and the failure
--                              half's reconstruction is `ren-fail-intro`, structural.  The
--                              only hypothesis anywhere is `RenTight`, and that is a LEVEL
--                              artefact (see the re-export comment), discharged for
--                              `renameMap`.
--   The `CSP.Laws.FSim.LoopCong` family (iter-fsim/loop-fsim/loop0-fsim/loopc-fsim/
--   while-fsim)
--                            ← TWO classical facts, both verified by direct import in
--                              LoopCong.agda: `Diverges-LEM` (CSP.Laws.FD.FDTransfer)
--                              and `¬DivModA→MAcc` (CSP.Laws.FD.HideDivergence),
--                              composed inside `iter-div-split`
--                              (LoopCong.agda:378-383).  (CORRECTION: the plan header's
--                              "sole classical dependency is Diverges-LEM" is incomplete
--                              — `¬DivModA→MAcc` is imported and used too: imports at
--                              LoopCong.agda:143 (`¬DivModA→MAcc`) and :144
--                              (`Diverges-LEM`); uses at :383 and :379 respectively.)
--   Bind-fsim / bindNoτ-fsim / bindκ-fsim (CSP.Laws.FSim.BindCong, re-exported)
--                            ← NONE.  Postulate-free: the König split is a
--                              caller-supplied EXPLICIT hypothesis (`BindDivSplit` /
--                              `NoTauRoot`), not an inherited axiom
--                              (BindCong.agda:93, confirmed by grep — no `postulate`
--                              keyword anywhere in the file).
--   >>-fsim (CSP.Laws.FSim.BindCong, re-exported)
--                            ← >>-Diverges→ (CSP.Laws.FD.SeqDistR.agda:325-326,
--                              genuinely a direct dependency — confirmed used at
--                              BindCong.agda:599 inside `>>-split`).
--   >>=-mono-⊑FD, bindNoτ-mono-⊑FD, bindκ-mono-⊑FD (CSP.Laws.FD.BindMonoFD, re-exported)
--                            ← Diverges-LEM (FDTransfer), and nothing else.
--     Used ONCE, in `BindMonoFD`'s `term-transfer`: `⊑FD` observes TERMINATION only
--     through the `√` tick (a `ret` state is not stable, so it is no failure of its own),
--     and settling the spec's `√`-extended empty-ban failure at a τ-normal form is the
--     classical step.  The BIND KÖNIG STEP is NOT inherited here: it is the explicit
--     `BindDivSplit k₂` hypothesis for the general bind, and constructively discharged
--     (`bind-noτ-split` / `pure→NoTauRoot`) for the other two.
--   >>-mono-⊑FD, ⨾⋆-mono-⊑FD, ⨾Fin-mono-⊑FD (CSP.Laws.FD.BindMonoFD, re-exported)
--                            ← Diverges-LEM (as above) AND >>-Diverges→ (SeqDistR),
--                              the latter via `>>-split`, exactly as `>>-fsim`.
--     The two folds add NOTHING: both are EMPTY-BASED inductions over `>>-mono-⊑FD` with
--     `⊑FD-refl Skip` at the base (`⨾⋆ [] = Skip`, `Skip` being the unit of `;`), like
--     `⦀Fin`/`⦀⋆`/`□Fin`/`□⋆` and unlike `⨅⁺`/`⨅Fin`/`∥⁺`/`∥Fin`.
--   Hide-fsim (CSP.Laws.FSim.HideCong, re-exported)
--                            ← Diverges-LEM (FDTransfer), ¬DivModA→MAcc
--                              (HideDivergence) — both directly imported, at
--                              HideCong.agda:124 and :122 respectively.
--   ⊓-fsim, prefix-fsim, ⊓-refine-fsim, ⊓-refine-⊑FD
--   (CSP.Laws.FSim.IChoiceCong, re-exported; its `⊓-mono-⊑FD`/`prefix-mono-⊑FD`
--   cash-out wrappers were RETIRED — the fact-shaped laws are
--   `CSP.Laws.FD.IChoiceMonoFD.⊓-mono-⊑FD` and `CSP.Laws.FD.ChoiceRefine.⟶₀-mono-⊑FD`)
--                            ← NONE (direct builds; module's own banner: "POSTULATES:
--                              none, local or inherited").  It is among the FSim-layer
--                              modules transitively CLEAN of `Semantics.DRImpliesFD`;
--                              re-measured over all ELEVEN current `CSP/Laws/FSim/`
--                              modules, the clean set is `IChoiceCong`, `SlideCong`,
--                              `ExtChoiceLift`, `ExtChoiceCong`, `HideCounterexample`
--                              and `SlideCounterexample` (the last two refutations, not
--                              congruences); `BindCong`, `HideCong`, `LoopCong`,
--                              `ParCong`, `ParCongRep` do reach it.  (Machine-checked
--                              transitive import closure.  An earlier draft of this
--                              header said `IChoiceCong` was the ONLY clean congruence
--                              module and spoke of "seven" FSim modules — both went
--                              stale when `SlideCong`/`ExtChoiceLift`/`ExtChoiceCong`
--                              landed.  Reaching `DRImpliesFD` is not the same as USING
--                              its postulate; see each module's own banner.)
--   ⦀Fin-fsim, ⦀⋆-fsim, sep-from-OffersOnlyᶠ
--   (CSP.Laws.FSim.ParCongRep, re-exported)
--                            ← Par-Diverges→ (ParallelDivergence), entering through
--                              `Par-fsim`'s `div→` field at each fold step; nothing local.
--     (`ParCongRep`'s `⦀Fin-mono-⊑FD`/`⦀⋆-mono-⊑FD` cash-out wrappers were RETIRED; the
--     fact-shaped folds now carrying those names are in `CSP.Laws.FD.ParallelMonoFD` and
--     share `Par-mono-⊑FD`'s provenance below, NOT this one.)
--   ▷-fsim-R, ▷-mono-R-⊑FD-fsim, ▷-τ*-L, ▷-wτ-L, ▷-wev-L, ▷-Diverges-R
--   (CSP.Laws.FSim.SlideCong, re-exported)
--                            ← ▷-Diverges→ (CSP.Laws.FD.ExtChoiceDivergence), used by
--                              the `div→` field only (module banner: "Exactly ONE is
--                              inherited"); `fwd`/`stab` constructive.
--   □-τ*-L/-R, □-τ*-L-live/-R-live, □-τ*-settle, □-wev-L/-R, □-wev-LR, □-w√-L/-R,
--   □-offer-mono (CSP.Laws.FSim.ExtChoiceLift, re-exported)
--                            ← NONE USED.  Neither `□-Diverges→` nor `▷-Diverges→`
--                              occurs as a term in the module; both are nevertheless
--                              REACHABLE in its closure (via `ExtChoiceFD` and via
--                              `SlideCong`), so it is not `--safe`-clean.
--   □-fsim, □Fin-fsim, □⋆-fsim
--   (CSP.Laws.FSim.ExtChoiceCong, re-exported)
--                            ← □-Diverges→ and ▷-Diverges→ (both
--                              CSP.Laws.FD.ExtChoiceDivergence), both in `div→` fields
--                              only.  Its closure carries exactly those two — no other
--                              postulate-bearing module is reachable from it.
--   pchoice-cong-FD (CSP.Laws.FD.RenameStepRel, re-exported)
--                            ← NONE USED.  It is built FD-direct over `pchoice`'s own
--                              decomposition; no postulate occurs as a term in it or in
--                              its six local helpers (`cell-just-nothing`, `cell-just→`,
--                              `pchoice-refuses-cong`, `prepend-ev⊥`, `pchoice-⊇F⊥-dir`,
--                              `pchoice-⊇D-dir`).  Its HOME MODULE's closure does
--                              carry two postulate-bearing modules —
--                              `Semantics.DRImpliesFD` (`¬-divergent→normal`, :66-67,
--                              pulled in for the SIBLING `step-i-FD`'s `drbisim→≈FD`) and
--                              `CSP.Laws.FD.ExtChoiceDivergence` — so this re-export is
--                              not `--safe`-clean either.
--   ¬▷-fsim, ▷-fsim-claim (CSP.Laws.FSim.SlideCounterexample, re-exported)
--                            ← NONE.  `--safe`-clean, zero postulates.
--   αpar-fsim-df, αpar-mono-⊑FD-fsim-df (CSP.Laws.FSim.AlphaParCong, re-exported)
--                            ← αpar-Diverges→ (CSP.Laws.FD.AlphaParallelDivergence,
--                              the module's ONE postulate), used only in the `div→`
--                              field (`AlphaParCong.agda:414-416`).  Certified sound
--                              from the single `dne` in `CSP.Laws.ClassicalFromLEM`,
--                              Derivation 11 (`αpar-no-inf`).  `fwd`/`stab` are fully
--                              constructive — the drain they run on (`αdrain`) is a
--                              well-founded `τ-Acc` induction, not a König step.
--   ¬αpar-fsim, αpar-fsim-claim, ¬αpar-fsim-R, αpar-fsim-R-claim
--   (CSP.Laws.FSim.AlphaParCounterexample, re-exported)
--                            ← NONE.  `--safe`-clean, zero postulates.
--   Θ-fsim (CSP.Laws.FSim.ThrowCong, re-exported), 2026-08-04
--                            ← NONE.  `agda --safe CSP.Laws.FSim.ThrowCong` exits 0 —
--                              the whole import closure is postulate-free.  `Θ-Diverges→`
--                              (the `div→` field's only classical-shaped ingredient) is
--                              STRUCTURAL, not a postulated König step: `force (P ⟦A▷Q)`
--                              inspects only the BODY `P`, so the composite's τ-space IS
--                              the body's and the divergence projects/re-lifts in two
--                              lines, no search.  Joins `IChoiceCong` as the second
--                              `--safe`-clean FSim congruence, and — unlike `IChoiceCong`
--                              (`⊓`/prefix, which never inspect an operand's `force` at
--                              all, their composite a fixed `react` node) — the first
--                              `--safe`-clean congruence for an operator that DOES
--                              deconstruct a live operand.  (The "transitively clean of
--                              `DRImpliesFD`" six-module count earlier in this header
--                              predates this module AND `AlphaParCong`/
--                              `AlphaParCounterexample`; it is pre-existing staleness
--                              this note flags but does not otherwise correct.)
--
-- All inherited postulates are certified from a single `dne` in
-- `CSP.Laws.ClassicalFromLEM`.
--
-- CORRECTIONS TO THE PLAN HEADER (verified against source, not transcribed):
--   1. `Par-Diverges→` is claimed as a `LoopCong` dependency in the plan text —
--      grepped, NO occurrence in `CSP/Laws/FSim/LoopCong.agda`.  Spurious; dropped
--      above.
--   2. `Bind-fsim`/`bindNoτ-fsim`/`bindκ-fsim` are postulate-free (see above), not
--      inheritors of some unnamed axiom.
--   3. The loop family's classical dependency is `Diverges-LEM` AND `¬DivModA→MAcc`
--      (not `Diverges-LEM` alone — see above).
--   4. `>>-fsim` genuinely inherits `>>-Diverges→` (SeqDistR.agda:325) — confirmed,
--      not a correction, just re-verified.
--   5. `LoopCong` pins its interrupt-shaped `⊤` at the MODULE's own level `ℓ`
--      (`⊤ {ℓ}`, e.g. LoopCong.agda:581-582), not a fresh `ℓr` — confirmed by direct
--      read of the module.
--
-- ⚠ KNOWN-FALSE — DO NOT ATTEMPT:
--   1. Unconditional `P ⊑FD Q → (P ∖ A) ⊑FD (Q ∖ A)` is FALSE.  Counterexample in
--      `CSP.Laws.FD.HideMonoFD`'s header (`Q = μX. h→X` vs `P = ⊓ₙ hⁿ;STOP`).  Only
--      `Hide-mono-⊑FD-df` (divergence-freedom side condition) and the unconditional
--      failures half `Hide-mono-fail` exist.  No dne-certified postulate can rescue a
--      false ∀-E statement.
--   2. The `FinBr` repair is ALSO false — `CSP.Laws.FD.HideMonoFinBrFail` constructs
--      `finBr-Pinf : FinBr Pinf`.  `FinBr` bounds visible channel support, never
--      τ-fan-out.  Generalised lesson: `FinBr` cannot rescue a König obstruction.
--   3. Unconditional `Par` / `△` `≈DR` congruences are false — hence `Sep` / `Sep△`
--      (here `SepDR` / `Sep△`).
--   4. The TWO-SIDED sliding-choice congruence
--      `▷-fsim : FSim R P₁ P₂ → FSim R Q₁ Q₂ → FSim R (P₁ ▷ Q₁) (P₂ ▷ Q₂)`
--      is FALSE, and formally refuted (not argued in prose) by
--      `CSP.Laws.FSim.SlideCounterexample.¬▷-fsim`, whose statement is `▷-fsim-claim`.
--      Both names are re-exported in Part 2 so the refutation is reachable through the
--      index; the refutation lives at that module's OWN concrete alphabet `Ev`, so those
--      two names do NOT depend on this module's `E`/`E-≟`.  What survives is the
--      one-sided `▷-fsim-R` (`CSP.Laws.FSim.SlideCong`, unconditional, shared left
--      operand) and its `▷-mono-R-⊑FD-fsim` corollary.  Contrast `□`, where the two-sided
--      unconditional `□-fsim` DOES hold (`CSP.Laws.FSim.ExtChoiceCong`).
--   5. The UNCONDITIONAL two-sided BINARY ALPHABETISED-PARALLEL `_⟦_∥_⟧_` `FSim`
--      congruence is FALSE, and — sharper than the `▷` case above — so is the
--      ONE-SIDED variant that fixes one operand, in BOTH orientations.  Formally
--      refuted by `CSP.Laws.FSim.AlphaParCounterexample.¬αpar-fsim` /
--      `¬αpar-fsim-R` (witness `P₁ = P₂ = ea ⟶₀ Stop`, `Q₁ = div ⊓ div`, `Q₂ = div`,
--      `A = all`, `B = ∅ES`; failing field `fwd.on-ev`).  Unlike `▷-fsim-R`'s dodge
--      (the shared operand's `force` never changes, so it can stand still), `αpar`
--      inspects BOTH operand heads via its sil-priority `force` clause, so sharing
--      one operand does not help.  What survives is `αpar-fsim-df` /
--      `αpar-mono-⊑FD-fsim-df` (`CSP.Laws.FSim.AlphaParCong`), under a `τ-AccReach`
--      divergence-freedom side condition on the two SPEC operands only (the impl
--      operands are unconstrained).  Honest scope note: in the refuting witness
--      BOTH composites diverge, so `⊑FD` holds trivially between them — the
--      counterexample refutes the `FSim` congruence, not the `⊑FD`/FD law.
--
-- ⚠ WHY HIDING IS THE CRUX. Hiding is where a refinement built from bare `⊑FD` FACTS
-- breaks down: unconditional `Hide-mono-⊑FD` is FALSE (`CSP.Laws.FD.HideMonoFD` carries
-- the counterexample), so from `P ⊑FD Q` alone one cannot conclude
-- `(P ∖ A) ⊑FD (Q ∖ A)`; only `Hide-mono-⊑FD-df` survives, under a divergence-freedom
-- side condition.
--
-- What carries an FD-strength refinement through hiding unconditionally is a WITNESS,
-- and there are two independent routes here — neither recoverable from a bare `⊑FD` fact:
--   • one-way: `Hide-fsim` (unconditional), then `fsim→⊑FD`. `⊑FD → FSim`
--     completeness is out of scope.
--   • two-way: `cong-∖` (unconditional, `CSP.Laws.Bisim.DRCongruence`), then
--     `drbisim→≈FD` — i.e. `hide-cong-FD` above, in this very module. Needs the
--     strictly stronger `DRbisim` fact.
--
-- So a composite refinement must carry a witness through the hide rather than a
-- `⊑FD` fact, and cash out once at the top. FSim is the cheaper witness when only
-- refinement (not equivalence) is wanted: three obligations (`fwd`/`stab`/`div→`)
-- instead of `DRbisim`'s four, and `Par-fsim` needs `Sep` on the impl operand pair
-- only.
--
-- WHAT THE WEAKER ORDERS ACTUALLY GIVE — read the two types; earlier drafts of this
-- header got this wrong four times in a row, so it is spelled out.
--
--   • `⊑T` DOES compose through hiding unconditionally:
--         Hide-mono-⊑ᵀ : (A : EventSet) {P Q} → P ⊑T Q → (P ∖ A) ⊑T (Q ∖ A)
--     (`CSP.Laws.Traces.TraceLawsHide`, :314-315).  No side condition.
--
--   • `⊇F⊥` does NOT.  `Hide-mono-fail` (`CSP.Laws.FD.HideMonoFD`, :225-227, re-exported
--     below) is the unconditional STABLE-FAILURE TRANSFER, not `⊇F⊥` monotonicity:
--         Hide-mono-fail : (A : EventSet) {P Q} → P ⊇F⊥ Q
--                        → ∀ {s} {X} → failures (Q ∖ A) s X → failures⊥ (P ∖ A) s X
--     Its INPUT is `failures`, not `failures⊥`, so it is NOT `(P ∖ A) ⊇F⊥ (Q ∖ A)`: since
--     `failures⊥ P s B = failures P s B ⊎ divergences P s`
--     (`Semantics/FailuresDivergences.agda:73`), it discharges only the `failures`
--     disjunct of the hypothesis and says nothing about the `divergences` one.
--     Unconditional `⊇F⊥` monotonicity through hiding FAILS as well, by the same
--     divergence-chaos mechanism that kills `⊑FD` — stated in `HideMonoFD`'s own header
--     (:24): "via divergence-chaos at `[]` even `(P′ ∖ {h}) ⊇F⊥ (Q ∖ {h})` fails for a
--     `b`-offering variant `P′`".  Corroborated by the proof of `Hide-mono-⊑FD-df`
--     itself, which handles the `failures` input by `Hide-mono-fail` but refutes the
--     `divergences` input from its SIDE CONDITION rather than by proof
--     (`fF⊥ (inj₂ dv) = ⊥-elim (hdf dv)`, HideMonoFD.agda:256) — a line that would be
--     unnecessary if `⊇F⊥` were unconditionally monotone here.
--
-- SO WHICH COMPONENT BREAKS?  BOTH, and it is worth being precise about which
-- counterexample hits which:
--   • `⊇D` — the CANONICAL pair (`Q = μX. h→X`, `P = ⊓ₙ hⁿ;STOP`) breaks exactly this:
--     `Q ∖ {h}` diverges, `P ∖ {h}` has no infinite τ-path (infinite branching defeats
--     König), so `(P ∖ {h}) ⊇D (Q ∖ {h})` FAILS (HideMonoFD's header, :24).  This is the
--     `⊑FD` failure, and `Hide-mono-⊑FD-df` refutes the obligation from its side condition
--     in BOTH components (`fF⊥ (inj₂ dv)` at :256 and `fD dv` at :258).
--   • `⊇F⊥` — needs the `b`-offering VARIANT `P′` of the same pair, and breaks via
--     divergence-chaos at `[]`, i.e. on `failures⊥`'s `divergences` disjunct.
-- Both mechanisms are the same divergence-chaos phenomenon, which is why the failure takes
-- down `⊇F⊥` and `⊑FD` together, and why carrying a WITNESS (`FSim` or `DRbisim`) rather
-- than a refinement FACT is what gets a composite through a hide.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Maybe using (Maybe; just)
open import Data.Fin using (Fin)
open import Data.List using (List; map)
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.Product using (Σ; Σ-syntax; _,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_)

open import Process_Trees

module CSP.Laws.FD.Congruences {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
-- the STATEMENT VOCABULARY of the suite, re-exported PUBLICLY: every result below is a
-- `DRbisim` / `FSim` / `_≈FD_` / `_⊑FD_` sentence, and `fsim→⊑FD` is how an `FSim` tower
-- is cashed out, so a downstream consumer cannot state or use the suite without these.
-- Making them travel with the index is what lets a consumer such as
-- `CSP.Examples.FSimTower` drop its own `Semantics.*` imports (Part 2's "one import").
open import Semantics.DRBisim {E = E} {I = ExtI E} public using (DRbisim)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} public
  using (_≈FD_; _⊑FD_)
open import Semantics.FailureSim {E = E} {I = ExtI E} public using (FSim; fsim→⊑FD)
-- kept as a QUALIFIED import (not `open`): both a source-alphabet (`E`) and a
-- target-alphabet (`E₂`, in the renaming section below) instance of
-- `drbisim→≈FD`/`drbisim→fsim` are needed, and their implicit `{E}{I}` are inferred
-- from each call site's argument, so qualification sidesteps any shadowing question.
import Semantics.DRImpliesFD as DRIFD
-- these two are re-exported PUBLICLY: Part 1's statements below mention `SepDR`, `Sep△`,
-- `Alpha`, `Disj`, `OffersOnly` and `CongCell` in their own premises, so a user of
-- `Par-cong-FD` / `⦀-cong-FD` / `⦀Fin-cong-FD` / `⦀⋆-cong-FD` / `△-cong-FD` must be able
-- to NAME its hypotheses through this index (Part 2's "one import" promise).  The
-- `Sep → SepDR` rename is what keeps DRCongruence's ⊤-only record distinguishable from
-- `ParCong`'s two-carrier one, re-exported as `SepPar` in Part 2 — do NOT collapse them.
open import CSP.Laws.Bisim.DRCongruence E-≟ public
  using (cong-∖; cong-Par⊤; cong-⦀; cong-△; cong-renameInv; cong-renameMap; Sep△)
  renaming (Sep to SepDR)
-- `OffersOnly-Prefix₀`/`OffersOnly-Skip` travel too: they are the two INTRODUCTION forms
-- a consumer needs to actually BUILD the `OffersOnly` premise for a prefix-shaped leaf, so
-- without them "hypotheses can be named through the index" would still force a direct
-- `DRCongruenceRep` import (`CSP.Examples.FSimTower` is the witness).
open import CSP.Laws.Bisim.DRCongruenceRep E-≟ public
  using (cong-⦀Fin; cong-⦀⋆; Alpha; Disj; OffersOnly; CongCell;
         OffersOnly-Prefix₀; OffersOnly-Skip)

-------------------------------------------------------------------------------------
-- PART 1: the `≈FD` congruence row.
-------------------------------------------------------------------------------------

-- hiding is an ≈FD congruence, unconditionally
hide-cong-FD : ∀ {ℓr} {R : Set ℓr} (A : EventSet) {P Q : PTree E (ExtI E) R}
             → DRbisim R P Q → (P ∖ A) ≈FD (Q ∖ A)
hide-cong-FD A pq = DRIFD.drbisim→≈FD (cong-∖ A pq)

-- the general synchronised-alphabet parallel `_∥⇘_⇙_` is an ≈FD congruence, under
-- THREE `SepDR` witnesses (impl pair / mixed pair / spec pair, exactly as
-- `cong-Par⊤` itself demands — NOT one, contrary to a naive reading of the brief)
Par-cong-FD : ∀ {ℓr} (A : EventSet) {P P′ Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
            → SepDR A P Q → SepDR A P′ Q → SepDR A P′ Q′
            → DRbisim (⊤ {ℓr}) P P′ → DRbisim (⊤ {ℓr}) Q Q′
            → (P ∥⇘ A ⇙ Q) ≈FD (P′ ∥⇘ A ⇙ Q′)
Par-cong-FD A sPQ sP′Q sP′Q′ pp′ qq′ =
  DRIFD.drbisim→≈FD (cong-Par⊤ A sPQ sP′Q sP′Q′ pp′ qq′)

-- interleaving (`⦀ = Par⊤ ∅ES`) is an ≈FD congruence, under three `SepDR` witnesses
⦀-cong-FD : ∀ {ℓr} {P P′ Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
          → SepDR ∅ES P Q → SepDR ∅ES P′ Q → SepDR ∅ES P′ Q′
          → DRbisim (⊤ {ℓr}) P P′ → DRbisim (⊤ {ℓr}) Q Q′
          → (P ⦀ Q) ≈FD (P′ ⦀ Q′)
⦀-cong-FD sPQ sP′Q sP′Q′ pp′ qq′ = DRIFD.drbisim→≈FD (cong-⦀ sPQ sP′Q sP′Q′ pp′ qq′)

-- the finite replicated-interleaving fold `⦀Fin` is an ≈FD congruence, under
-- pairwise-disjoint per-index alphabets and both sides confining to them
⦀Fin-cong-FD : ∀ {ℓr} {n} (αs : Fin n → Alpha) {f g : Fin n → PTree E (ExtI E) (⊤ {ℓr})}
             → (∀ i j → i ≢ j → Disj (αs i) (αs j))
             → (∀ i → OffersOnly (αs i) (f i))
             → (∀ i → OffersOnly (αs i) (g i))
             → (∀ i → DRbisim (⊤ {ℓr}) (f i) (g i))
             → ⦀Fin n f ≈FD ⦀Fin n g
⦀Fin-cong-FD αs disj oof oog eq = DRIFD.drbisim→≈FD (cong-⦀Fin αs disj oof oog eq)

-- the LIST replicated-interleaving fold `⦀⋆` is an ≈FD congruence, under a pairwise
-- disjoint list of `CongCell`s (each packaging one operand pair + its alphabet
-- confinement + its own `≈DR`)
⦀⋆-cong-FD : ∀ {ℓr} (cs : List (CongCell ℓr))
           → AllPairs (λ c c′ → Disj (CongCell.alph c) (CongCell.alph c′)) cs
           → ⦀⋆ (map CongCell.P cs) ≈FD ⦀⋆ (map CongCell.Q cs)
⦀⋆-cong-FD cs aps = DRIFD.drbisim→≈FD (cong-⦀⋆ cs aps)

-- interrupt `_△_` is an ≈FD congruence, under three `Sep△` witnesses (P₁Q₁ / P₂Q₁ /
-- P₂Q₂ — mirroring `cong-△`'s own argument shape)
△-cong-FD : ∀ {ℓr} {R : Set ℓr} {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
          → Sep△ P₁ Q₁ → Sep△ P₂ Q₁ → Sep△ P₂ Q₂
          → DRbisim R P₁ P₂ → DRbisim R Q₁ Q₂
          → (P₁ △ Q₁) ≈FD (P₂ △ Q₂)
△-cong-FD s1 s2 s3 pp qq = DRIFD.drbisim→≈FD (cong-△ s1 s2 s3 pp qq)

-- interrupt is also an FSim congruence (same underlying ≈DR congruence, transported
-- the other way — needed so a `△` composite can sit inside an FSim tower)
△-fsim : ∀ {ℓr} {R : Set ℓr} {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
       → Sep△ P₁ Q₁ → Sep△ P₂ Q₁ → Sep△ P₂ Q₂
       → DRbisim R P₁ P₂ → DRbisim R Q₁ Q₂
       → FSim R (P₁ △ Q₁) (P₂ △ Q₂)
△-fsim s1 s2 s3 pp qq = DRIFD.drbisim→fsim (cong-△ s1 s2 s3 pp qq)

-- ... hence the ⊑FD monotonicity corollary, via `fsim→⊑FD : FSim R Q P → P ⊑FD Q`
-- (Q := P₁△Q₁ the FSim's "t₁"/impl, P := P₂△Q₂ the FSim's "t₂"/spec).  The premise is a
-- `DRbisim` (NOT an `FSim`, despite routing through `△-fsim`) — hence the `-dr` suffix,
-- not `-fsim`.
△-mono-⊑FD-dr : ∀ {ℓr} {R : Set ℓr} {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
           → Sep△ P₁ Q₁ → Sep△ P₂ Q₁ → Sep△ P₂ Q₂
           → DRbisim R P₁ P₂ → DRbisim R Q₁ Q₂
           → (P₂ △ Q₂) ⊑FD (P₁ △ Q₁)
△-mono-⊑FD-dr s1 s2 s3 pp qq = fsim→⊑FD (△-fsim s1 s2 s3 pp qq)

-------------------------------------------------------------------------------------
-- The renaming pair.  Parametric in the TARGET alphabet `E₂` and the event injection,
-- exactly like the inner module of `CSP.Laws.Bisim.DRCongruence` that supplies
-- `cong-renameInv`/`cong-renameMap` — those two names, once the module telescope
-- below is applied, take `ι ι⁻¹ ι-linv` as their first three (explicit) arguments.
-------------------------------------------------------------------------------------

module _ {ℓe₂} {E₂ : Set ℓ → Set ℓe₂}
  (ι      : ∀ {A} → E A → E₂ A)
  (ι⁻¹    : ∀ {A} → E₂ A → Maybe (E A))
  (ι-linv : ∀ {A} (e : E A) → ι⁻¹ (ι e) ≡ just e)
  where

  open import CSP.Rename {E₁ = E} {E₂ = E₂} ι ι⁻¹ ι-linv
    using (renameInv; renameMap; ConcEvent₁)
  -- target-alphabet `≈FD`, renamed on import so it never collides with the
  -- source-alphabet `_≈FD_` already open at the top of the file
  open import Semantics.FailuresDivergences {E = E₂} {I = ExtI E₂}
    using () renaming (_≈FD_ to _≈FD₂_)

  -- renaming (the functional/at-most-one-preimage wrapper `renameInv`) is an ≈FD
  -- congruence, UNCONDITIONALLY — no `Sep`-style side condition (contrast Par/△)
  rename-cong-FD : ∀ {ℓr} {R : Set ℓr}
                     (inv : (bt : AnyTypes E₂) → proj₁ bt → Maybe ConcEvent₁)
                     {P Q : PTree E (ExtI E) R}
                 → DRbisim R P Q → renameInv P inv ≈FD₂ renameInv Q inv
  rename-cong-FD inv pq = DRIFD.drbisim→≈FD (cong-renameInv ι ι⁻¹ ι-linv {inv = inv} pq)

  -- the injective same-shape specialisation (`renameMap = renameInv · ι-vis-inv`) is
  -- an ≈FD congruence too
  renameMap-cong-FD : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E (ExtI E) R}
                     → DRbisim R P Q → renameMap P ≈FD₂ renameMap Q
  renameMap-cong-FD pq = DRIFD.drbisim→≈FD (cong-renameMap ι ι⁻¹ ι-linv pq)

-------------------------------------------------------------------------------------
-- PART 2: the suite index.  One import for every FD congruence / monotonicity result.
-------------------------------------------------------------------------------------

open import CSP.Laws.FD.FDCong E-≟ public
  using (prefix-cong-DR; prefix-cong-FD; ⊓-cong-DR; ⊓-cong-FD)
open import CSP.Laws.FD.FDLawsIChoiceRep E-≟ public using (⊓-cong-FD≈)
open import CSP.Laws.FD.ChoiceRefine E-≟ public using (⟶₀-mono-⊑FD)
-- FACT-SHAPED (`⊑FD → ⊑FD`) internal-choice precongruence.  This is THE `⊓-mono-⊑FD`;
-- the former `FSim → ⊑FD` wrapper of the same name in `CSP.Laws.FSim.IChoiceCong` was
-- retired (see that module's note and `IChoiceMonoFD`'s header).
-- `⨅⁺-mono-⊑FD` / `⨅Fin-mono-⊑FD` are the replicated (NON-EMPTY: head+list resp.
-- `Fin (suc n)`) folds of the same law — no side condition, no `⊑FD-refl` at the base.
open import CSP.Laws.FD.IChoiceMonoFD E-≟ public
  using (⊓-mono-⊑FD; ⊓-mono-⊇F⊥; ⊓-mono-⊇D; ⨅⁺-mono-⊑FD; ⨅Fin-mono-⊑FD)
-- FACT-SHAPED parallel precongruence + the replicated-interleaving folds.  The folds
-- take the canonical `⦀Fin-mono-⊑FD` / `⦀⋆-mono-⊑FD` names (the retired `ParCongRep`
-- wrappers held them before) and need NO `Disj`/`OffersOnly` side condition.
-- `∥⁺-mono-⊑FD` / `∥Fin-mono-⊑FD` (Layer 9) are the replicated INTERFACE-parallel folds:
-- one shared synchronisation `EventSet` at every step, and non-empty (`[|A|]` has no unit).
open import CSP.Laws.FD.ParallelMonoFD E-≟ public
  using (Par-mono-⊑FD; ∥-mono-⊑FD; ⦀-mono-⊑FD; ⦀Fin-mono-⊑FD; ⦀⋆-mono-⊑FD;
         ∥⁺-mono-⊑FD; ∥Fin-mono-⊑FD)
-- FACT-SHAPED precongruences of the three DERIVED operators: the guard `b ＆ P`, the
-- conditional `P ◁ b ▷ Q` and the OUTPUT prefix `e ! v ⟶ P`.  Selective `using`: the
-- module also holds `Output`'s failures/divergences decomposition, which is its proof
-- scaffolding, not suite surface.  (The generic `force-≡→⊑FD` bridge the two `Bool`
-- splits ride on used to live there too; it is now in `Semantics.FailuresDivergences`
-- beside `⊑FD-refl`/`⊑FD-trans`, proved directly over the LTS.)
-- `agda --safe`-clean end to end (zero postulates, local or inherited).
open import CSP.Laws.FD.DerivedMonoFD E-≟ public
  using (＆-mono-⊑FD; ◁▷-mono-⊑FD; Output-mono-⊑FD)
open import CSP.Laws.FD.HideMonoFD E-≟ public using (Hide-mono-fail; Hide-mono-⊑FD-df)
open import CSP.Laws.FD.IterateMonoFD E-≟ public using (loop0-mono-⊑FD)
-- FACT-SHAPED precongruence of the BIND / SEQUENTIAL family.  These four take the
-- canonical `-mono-⊑FD` names; the shape-3 `Bind`/`bindNoτ`/`bindκ`/`>>` wrappers that
-- held them in `LoopMonoFD` are DELETED.  `>>=-mono-⊑FD` still needs a `BindDivSplit`,
-- now on the REFINED continuation `k₂` (the one being decomposed); the other three
-- discharge it.  All four pin a SHARED result level (`R S : Set ℓr`) — a ban set must be
-- retagged across the bind's carrier change, and `_⊇F⊥_` pins the ban level to the
-- carrier's (same reason `IterateMonoFD` pins `ℓr ≡ ℓ`).  Selective `using`: the module's
-- retag / handover / elim machinery is proof scaffolding, not suite surface.
-- `⨾⋆`/`⨾Fin` are the List-/Fin-indexed sequential folds; both are EMPTY-BASED
-- (`⨾⋆ [] = Skip`, `Skip` being the unit of `;`), so they induct over `>>-mono-⊑FD` with
-- `⊑FD-refl Skip` at the base, exactly like `⦀⋆`/`⦀Fin`/`□⋆`/`□Fin` and UNLIKE
-- `⨅⁺`/`⨅Fin`/`∥⁺`/`∥Fin`, whose base case is an operand hypothesis.
open import CSP.Laws.FD.BindMonoFD E-≟ public
  using (>>=-mono-⊑FD; bindNoτ-mono-⊑FD; bindκ-mono-⊑FD; >>-mono-⊑FD;
         ⨾⋆-mono-⊑FD; ⨾Fin-mono-⊑FD)
-- FACT-SHAPED precongruence of the LOOP family.  These four take the canonical
-- `-mono-⊑FD` names; the shape-3 `iter`/`loop`/`loopc`/`while` wrappers that held them in
-- `LoopMonoFD` are DELETED — and with them the module, which held nothing else.  The
-- general `iter-mono-⊑FD` is proved FD-directly (well-founded recursion on `runLen`, the
-- same measure `loop0-mono-⊑FD` uses) and `loop`/`while` fall out of it because both are
-- DEFINITIONALLY `iter` over a PURE-continuation bind step (`loop-unfoldᴬ` /
-- `while-unfoldᴬ`, both `refl`), whose `⊑FD`-monotonicity is `bindκ-mono-⊑FD` above.
-- `loopc-mono-⊑FD` IS `loop0-mono-⊑FD`: `loopc` and `loop0` are the same definition.
-- All pin `A R : Set ℓ` for the ban-set retag, exactly as `IterateMonoFD` does.
-- Selective `using`: the module's retag / reconstruction / spin-transfer machinery is
-- proof scaffolding, not suite surface.
open import CSP.Laws.FD.IterMonoFD E-≟ public
  using (iter-mono-⊑FD; iter-mono-⊇F⊥; iter-mono-⊇D;
         loop-mono-⊑FD; while-mono-⊑FD; loopc-mono-⊑FD)
-- FACT-SHAPED precongruence of RENAMING — the first monotonicity law renaming has had at
-- ANY shape (previously: `renameInv-mono-⊑ᵀ` at `⊑T` and the unconditional `≈DR`
-- `cong-renameInv`/`cong-renameMap`, whose `≈FD` cash-outs are `rename-cong-FD` /
-- `renameMap-cong-FD` in Part 1 above).  Stated at the SAME alphabet, so — unlike Part 1's
-- pair — it needs NO `ι`/`ι⁻¹`/`ι-linv` telescope and no `E-≟`; it follows
-- `CSP.Laws.Traces.TraceLawsRename`, which instantiates `CSP.Rename` at `ι = id`.
-- The `⊇D` half is UNCONDITIONAL and CONSTRUCTIVE (rename's τ-space corresponds one-for-one,
-- so there is no König step at all — the cheapest divergence transfer in the repo).  The
-- `⊇F⊥` half takes `RenTight inv`: the ban set has to be pulled back along `inv`, and the
-- honest pullback quantifies over target events, which lands ABOVE the carrier level
-- `_⊇F⊥_` pins its ban sets to.  `RenTight` (a forward section + no visible fan-out) makes
-- the pullback POINTWISE and hence level-`ℓr`; it is a LEVEL artefact, not a mathematical
-- side condition, and it DISCHARGES for `renameMap` (`ι-vis-inv` is the identity inverse at
-- the same alphabet), so `renameMap-mono-⊑FD` is unconditional.
open import CSP.Laws.FD.RenameMonoFD {E = E} public
  using (RenTight; renameInv-mono-⊑FD; renameInv-mono-⊇F⊥; renameInv-mono-⊇D;
         renameMap-mono-⊑FD; renameMap-mono-⊇F⊥; renameMap-mono-⊇D)
open import CSP.Laws.FSim.IChoiceCong E-≟ public
open import CSP.Laws.FSim.HideCong E-≟ public using (Hide-fsim)
-- `ParCong`'s `Sep` is the TWO-CARRIER record documented above; re-exported renamed
-- to `SepPar` so it never collides with `SepDR` (DRCongruence's ⊤-only `Sep`, which
-- Part 1 uses in its premises and which is re-exported under that name at the top)
open import CSP.Laws.FSim.ParCong E-≟ public
  using (Par-fsim; ∥-fsim; ⦀-fsim)
  renaming (Sep to SepPar)
-- the replicated-interleaving FSim layer: `⦀Fin-fsim`, `⦀⋆-fsim`, plus the `FCell` cell
-- record, `unionAlphaF`, `OffersOnly-⦀⋆-fu` and the `sep-from-OffersOnlyᶠ` discharge.
-- CONGRUENCES ONLY — the `⊑FD` folds come from `ParallelMonoFD` above (fact-shaped); the
-- `FSim → ⊑FD` wrappers `ParCongRep` used to export under those names were retired.
-- Re-exported wholesale (`ParCongRep` imports nothing publicly, so only its own
-- definitions travel).  No cycle: `ParCongRep` does not import this module.
open import CSP.Laws.FSim.ParCongRep E-≟ public
open import CSP.Laws.FSim.LoopCong E-≟ public
open import CSP.Laws.FSim.BindCong E-≟ public
-- SLIDING CHOICE `_▷_`, RIGHT operand only (the two-sided law is false — KNOWN-FALSE 4
-- above).  Selective `using` rather than wholesale: `SlideCong` also exports the internal
-- `▷-fsim-R-div→` / `f-sim-▷-R` scaffolding, which is implementation detail of the
-- congruence and not part of the suite's surface.
open import CSP.Laws.FSim.SlideCong E-≟ public
  using (▷-fsim-R; ▷-mono-R-⊑FD-fsim; ▷-τ*-L; ▷-wτ-L; ▷-wev-L; ▷-Diverges-R)
-- EXTERNAL CHOICE, weak-lifting layer.  Selective `using`: `ExtChoiceLift` also exports
-- generically-named LTS helpers (`τ-live`, `ev-live`, `stable-live`, `τ*-ev-live`,
-- `τ*-stable-live`, `□-ev-weak-L/-R`, `□-ev-LR`) whose names are too generic to belong in
-- a suite-wide namespace — that is the one namespace hazard found while wiring these three
-- modules in; no actual clash with an existing index export arose.
open import CSP.Laws.FSim.ExtChoiceLift E-≟ public
  using (□-τ*-L; □-τ*-R; □-τ*-L-live; □-τ*-R-live; □-τ*-settle;
         □-wev-L; □-wev-R; □-wev-LR; □-w√-L; □-w√-R; □-offer-mono)
-- EXTERNAL CHOICE, the congruence itself: two-sided and unconditional (no `Sep`), plus
-- the `⊑FD` corollary and the two replicated folds.  Selective `using` for the same
-- reason as `ExtChoiceLift` (`ret-fsim`, `⊓-fsim-join`, `□-fsim-run`, `▷□-fsim-L/-R`, …
-- are the S1-S4 scaffolding of its proof).
open import CSP.Laws.FSim.ExtChoiceCong E-≟ public
  using (□-fsim; □Fin-fsim; □⋆-fsim)
-- EXTERNAL CHOICE, the FACT-SHAPED (`⊑FD → ⊑FD`) precongruence — shape 2, and the one
-- that owns the `-mono-⊑FD` names (the shape-3 cash-out formerly in `ExtChoiceCong` was
-- retired; see the POLICY note in this header).  Two-sided, unconditional, plus the two
-- replicated folds.  Zero LOCAL postulates; inherits `□-Diverges→`/`▷-Diverges→`
-- (`CSP.Laws.FD.ExtChoiceDivergence`) through `□-div-elim`/`□-div-intro-L/R`, which is
-- unavoidable for any `□` law that touches divergences.
open import CSP.Laws.FD.ExtChoiceMonoFD E-≟ public
  using (□-mono-⊑FD; □-mono-⊇F⊥; □-mono-⊇D; □Fin-mono-⊑FD; □⋆-mono-⊑FD)
-- THE NEGATIVE RESULT, deliberately NOT re-exported wholesale.  `SlideCounterexample` is
-- an alphabet-CONCRETE development (its own `Ev`, `Ev-≟`, `P₁`/`P₂`/`Q₁`/`Q₂`, `Rt`, …);
-- dumping that into a suite index parameterised by `E-≟` would put a dozen
-- fixed-alphabet names beside the generic ones, inviting exactly the confusion the two
-- `Sep` records already caused.  Only the headline refutation and the statement it refutes
-- travel, so `▷-fsim`'s falsity is reachable from the index without the witness data.
open import CSP.Laws.FSim.SlideCounterexample public using (▷-fsim-claim; ¬▷-fsim)
-- THE MENU CONGRUENCE, promoted here (design §A3).  `RenameStepRel` itself is UNCHANGED:
-- the name was already a general export (see the header note), so promotion is purely a
-- matter of indexing it.  `MaybeFD` travels because `pchoice-cong-FD`'s premise is stated
-- with it and could otherwise not be named through the index.
open import CSP.Laws.FD.RenameStepRel E-≟ public using (pchoice-cong-FD; MaybeFD)
-- BINARY ALPHABETISED PARALLEL `_⟦_∥_⟧_`.  The congruence itself, conditional on
-- `τ-AccReach` divergence-freedom of the two SPEC operands (KNOWN-FALSE 5 above shows
-- the unconditional form, and even the one-sided form, cannot be had).  `τ-Acc`/`acc`/
-- `τ-AccReach` (`Semantics.DivergenceFree`) and the `NoSil` vocabulary (`CSP.Laws.
-- AlphaParallelLift`) travel too, so a caller can NAME its own side-condition
-- hypotheses through the index rather than importing those modules directly.
open import Semantics.DivergenceFree {E = E} {I = ExtI E} public
  using (τ-Acc; acc; τ-AccReach)
open import CSP.Laws.AlphaParallelLift E-≟ public
  using (NoSil; noSil-ret; noSil-react; noSil-stable)
open import CSP.Laws.FSim.AlphaParCong E-≟ public
  using (αpar-fsim-df; αpar-mono-⊑FD-fsim-df)
-- THE NEGATIVE RESULT, deliberately NOT re-exported wholesale — same rationale as
-- `SlideCounterexample` above: only the headline refutations (both orientations)
-- travel, not the fixed-alphabet witness data (`Ev`, `Ev-≟`, `Pℓ`, `divR`, …).
open import CSP.Laws.FSim.AlphaParCounterexample public
  using (¬αpar-fsim; αpar-fsim-claim; ¬αpar-fsim-R; αpar-fsim-R-claim)
-- THROW `_⟦_▷_`.  TWO-SIDED and UNCONDITIONAL — no `Sep`-style side condition, no
-- divergence-freedom hypothesis — and `--safe`-clean end to end (see the header
-- provenance note above). The weak lifts travel too, since a caller building its own
-- throw-shaped `FSim` proof needs them; the composite↔body stability/offer plumbing
-- (`Θ-stable-elim`/`Θ-stable-intro`/`Θ-offer-mono`) stays internal, the same
-- discipline `ExtChoiceCong`'s S1-S4 scaffolding does not travel either.
open import CSP.Laws.FSim.ThrowCong E-≟ public
  using (Θ-fsim; Θ-τ*-L; Θ-wτ; Θ-wev-fire; Θ-wev-pass; Θ-wev-√)
-- THROW, the FACT-SHAPED (`⊑FD → ⊑FD`) precongruence — shape 2, and the one that owns the
-- `-mono-⊑FD` name (the shape-3 cash-out formerly in `ThrowCong` was retired; see the
-- POLICY note in this header).  Two-sided and unconditional.  Zero LOCAL postulates, but
-- NOT `--safe`-clean: its `θFire` arm pushes the body's run-up-to-the-fire through
-- `CSP.Laws.FD.FDTransfer`'s `FD→trace⊥`, inheriting `Diverges-LEM` +
-- `¬-divergent→normal` — exactly as `Par-mono-⊑FD` does, and NOT a König step (throw's
-- `Θ-Diverges→` is structural).  The run decomposition `Θ-reach-split` and the `A`-free
-- trace vocabulary travel too, since a caller stating its own throw-shaped
-- decomposition needs them.
open import CSP.Laws.FD.ThrowMonoFD E-≟ public
  using (Θ-mono-⊑FD; Θ-mono-⊇F⊥; Θ-mono-⊇D; ΘReach; θNo; θFire; θDone;
         Θ-reach-split; ΘFree; []ᶠ; _∷ᶠ_)

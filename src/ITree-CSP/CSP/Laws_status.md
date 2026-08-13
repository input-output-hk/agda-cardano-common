# CSP Algebraic Laws — Validation Status

Tracks the mechanisation of the CSP algebraic laws from
`../../../CSP_Algebraic_Laws/csp_laws.tex` (a digest of Roscoe's *Theory and Practice of
Concurrency* [TPC] and *Understanding CSP* [UCS]) against the **`spike/extc-fd-laws`**
branch — the witness-free fused-`react`-node process-tree model. Layout: the core type
`Process_Trees.agda`; the generic behavioural theory in `Semantics/` (LTS, the
bisimulations, refusals/failures/divergences, the `∼⟹≈DR`/`≈DR⟹≈FD` bridges); and the
CSP layer in `CSP/` (`Operators`, `Rename`, `Laws/{Traces,Bisim,FD}`, `Examples`).

- **Goal:** raise confidence in the spike's CSP operator definitions by proving each law,
  primarily at **`≈FD`** (failures–divergences equivalence, the model `𝒩`).
- **Method:** prove on strong/weak/DR-bisim and lift via the bridge `≈DR ⟹ ≈FD`
  (`drbisim→≈FD`) where possible; otherwise FD-direct via the operator's
  failures/divergences decomposition.
- **Law tags:** `Tn.m` = TPC, `Un.m` = UCS. `^*` = not valid in every model. `Div` = ⊥
  of `𝒩`.

**Legend:** ✅ done & typechecks · 🟡 partial · ❌ not started · ➖ N/A / degenerate /
definitional.

**Branch note (2026-07-31):** the header above names **`spike/extc-fd-laws`**, which is
still the branch this document was written against and still the reference point for
§1–§14. §15 and §16 (and the §6 additions cross-referencing §15) record work landed on a
DIFFERENT branch, **`semantics/failure-sim`**; the branch name above has deliberately
NOT been rewritten.

_Last updated: 2026-08-04._

---

## Summary

| Section | Operator | Status |
|---|---|---|
| §1 | Internal choice `⊓` | ✅ **complete** |
| §2 | External choice `□` | ✅ **complete** |
| §3 | Prefix / prefix-choice | ✅ **complete** |
| §4 | Conditional `◁b▷` | ✅ **complete** |
| §5 | Parallel `∥` (interface) | ✅ **complete** (comm, dist, zero, assoc, unit, step) |
| §6 | Hiding `∖` | 🟡 dist + null + zero + combine + sym + step (all 3 cases incl. full T3.6) done at FD; hide-∥ open |
| §7 | Renaming `⟦R⟧` | ✅ **FD law list complete** for injective `_⟦inv⟧ⁱ` (zero T11.8, dist-⊓ T3.13, dist-□ T3.14, step T3.15, combine T3.16-17, rename-slide U13.6, +aux rename-▷-dist). 🟡 **RELATIONAL `_⟦R¿preimg⟧` begun**: rename-zero + rename-⊓-dist (`RenameRel`); fan-in bridge `fanNode ≈FD ⨅⁺` (`RenameFanIn`); ✅ **rename-step relational** (the fan-in `⨅` law, `RenameStepRel.rename-step-rel-FD`, via `pchoice-cong-FD` + `rnFan-list-FD`) + ✅ **rename-slide relational** (`RenameSlideRel.rename-slide-rel-FD` — `node-pw2`, fan-in symmetric so `vis-pw=refl`; crux `tau-pw` via `extBwd-just`). Relational dist-□/combine remain |
| §8 | Piping `≫` / enslavement | ❌ not started (UCS treats as derived) |
| §9 | Sequential `;`, `SKIP` | ✅ **core complete** (T6.1–6.7); cross-op SKIP-term laws open |
| §10 | Interrupt `△` / Throw `⟦A▷` | ✅ **complete** (Fig 13.6 + throw suite); ✅ throw `FSim` congruence `Θ-fsim`/`Θ-mono-⊑FD` (2026-08-04, two-sided, unconditional, `--safe`-clean — `FSim/ThrowCong`) |
| §11 | Sliding choice `▷` | ✅ **core + ⊓/seq slide-dist + failures-char** (▷-id, ▷-assoc(cond), □-slide, ▷-⊓-ext, seq-slide, ▷-failures-char U13.26, □-SKIP-resolve, □-div, Div-slide, Div-SKIP-red, div-strict zeros); ✅ **COMPLETE** (every slide law incl. per-op hide-slide U13.3 + rename-slide U13.6); U13.14 SKIP-slide ✖ correctly (eager-`ret`) |
| §13 | Zero / divergence-strictness | 🟡 `⊓`/`□`/`∥`/`;` zeros done; hide/rename zeros open |
| §14 | Recursion | ❌ not started |
| §15 | One-way failure simulation `FSim` (the `⊑FD` order) | ✅ **record + `⊑T`/`⊑D`/`⊑F⊥`/`⊑FD` bridges + preorder**, `FSimFromRel` coinduction principle, `drbisim→fsim` refactor, four operator congruences (`Par`/`>>=`/`∖`/`iter`), the FD-hide counterexample refuted at the simulation level, one worked smoke test; **2026-08-04:** throw `Θ-fsim`/`Θ-mono-⊑FD` (`FSim/ThrowCong`), the second `agda --safe`-clean FSim congruence overall and the first for an operand-deconstructing operator — see the §17 addendum's full sweep (2 of 7 clean) |
| §16 | Divergence-freedom (`τ-Acc`) + stability calculi | ✅ **generic `Semantics/DivergenceFree` + 19 per-operator `τ-Acc` closures + the gathered stability layer** (both new modules postulate-free); ⚠️ measured payoff at the EXISTING proof sites is nil — those sites need τ-FREENESS, which `τ-Acc` is strictly weaker than |
| §17 | Consolidated FD/DR/FSim congruence & monotonicity coverage (2026-08-03 campaign, + same-day addendum, + 2026-08-04 αpar addendum, + 2026-08-04 later throw addendum, + 2026-08-04 loop/rename fact-shaped addendum) | ✅ **`⊓`/prefix FSim congruences** (`FSim/IChoiceCong`, postulate-free), **9 `⊑FD`-mono loop/bind wrappers** (`FD/LoopMonoFD` — ALL NINE since RETIRED 2026-08-04 and the module DELETED: the 4 BIND ones + `loop0-mono-⊑FD-fsim` in favour of the fact-shaped `FD/BindMonoFD` / `FD/IterateMonoFD`, then the 4 LOOP ones in favour of `FD/IterMonoFD`), **fact-shaped bind/sequential precongruence `>>=`/`bindNoτ`/`bindκ`/`>>` + folds `⨾⋆`/`⨾Fin`** (`FD/BindMonoFD`, 2026-08-04) and the `force-≡→⊑FD` hoist into `Semantics/FailuresDivergences`, **fact-shaped LOOP precongruence `iter`/`loop`/`while`/`loopc`** (`FD/IterMonoFD`, 2026-08-04) and **fact-shaped RENAMING precongruence `renameInv`/`renameMap`** (`FD/RenameMonoFD`, 2026-08-04 — renaming's first monotonicity law at any shape), **`≈FD` congruence row + suite index** (`FD/Congruences`), **`⦀Fin`/`⦀⋆` FSim congruences** (`FSim/ParCongRep`), **assembled two-leaf `FSim` tower** (`CSP.Examples.FSimTower`); full operator × relation matrix + the two-regimes finding below; **addendum:** `□-fsim`/`□-mono-⊑FD` (`FSim/ExtChoiceCong`, two-sided, no `Sep`), one-sided `▷-fsim-R`/`▷-mono-R-⊑FD-fsim` (`FSim/SlideCong`) plus the two-sided `▷`-congruence proved FALSE (`FSim/SlideCounterexample`), the `fsim-τ*-prepend`/`div-prepend-τ*` linchpin (`Semantics/FailureSim`); **2026-08-04 addendum:** binary alphabetised parallel `αpar-fsim-df`/`αpar-mono-⊑FD-fsim-df` (`FSim/AlphaParCong`, conditional on `τ-AccReach` divergence-freedom of the SPEC operands, `CSP/Laws/AlphaParallelLift` support layer, no `Sep`/`DecEq R` needed), the two-sided congruence proved FALSE **and the one-sided form FALSE in both orientations** (`FSim/AlphaParCounterexample`, sharper than `▷`'s one-sided-true case), `fsim-sil-factor` (`Semantics/FailureSim`); **2026-08-04 later addendum:** throw `Θ-fsim`/`Θ-mono-⊑FD` (`FSim/ThrowCong`, two-sided, unconditional, `agda --safe`-clean — the second clean FSim congruence overall, the first for an operand-deconstructing operator), the `ThrowFD`→`TraceLawsThrowInterrupt` hoist, and a full `--safe` sweep of the 7 top-level FSim operator congruences (2 clean); **2026-08-05 addendum:** the **STABLE-FAILURES (`⊑F`) layer** — `Par-mono-⊑F` + six folds (`FD/ParallelMonoFD` Layer 10) pairing with `Hide-mono-⊑F` (`FD/HideMonoFD`:255), both **UNCONDITIONAL**, giving the first compositional route that crosses a hide with a bare refinement FACT at refusal strength; needs **no divergence layer at all** (`_⊑F_` has no `divergences` disjunct) and inherits `offer-LEM` only |

**Bottom line:** the four core "untimed" operator algebras (`⊓`, `□`, prefix,
conditional), sequential composition, interrupt/throw, **and parallel** are all fully
validated at `≈FD`. Every FD-layer postulate is certified from a single `dne`. The next
frontier is **hiding (§6) and renaming (§7)**: both have trace-level laws but no FD laws
yet (each needs an FD decomposition, the larger lift). Alongside the two-way bridge
`≈DR ⟹ ≈FD` there is now a **one-way refinement order** (§15): `FSim`, a three-field
coinductive relation with no `bwd`/`div←`, giving `⊑FD` directly and carrying its own
congruences for parallel, bind, hiding, external choice (two-sided, no side condition)
and the loops — plus a one-sided sliding-choice congruence, its two-sided form proved
false rather than merely unattempted.

---

## §1 — Internal choice `⊓`  ✅

`P ⊓ Q ≜ extc ∅v (br2 P Q)`.

| Tag | Law | Status | Module |
|---|---|---|---|
| T1.2 | `P ⊓ P = P` (idem) | ✅ | `FDLawsIChoice` |
| T1.4 | `P ⊓ Q = Q ⊓ P` (comm, strong) | ✅ | `FDLawsIChoice` |
| T1.6 | `(P⊓Q)⊓R = P⊓(Q⊓R)` (assoc, FD-direct) | ✅ | `FDLawsIChoiceAssoc` |
| T11.2 / U13.23 | `Div ⊓ P = Div` (zero) | ✅ | `FDLawsIChoiceZero` |
| U13.20 | replicated `⨅⁺` + flatten | ✅ | `FDLawsIChoiceRep` |
| — | `⊓-cong-FD≈` (≈FD-premised congruence, reusable) | ✅ | `FDLawsIChoiceRep` (§17 table: FSim-layer `⊓-fsim` counterpart; the fact-shaped `⊓-mono-⊑FD` is `FD/IChoiceMonoFD`) |
| T11.14 / U13.24 | `P ⊓ Div = P` (div-ignoring unit) | ➖ | correctly **does not hold** (`𝒩` is divergence-strict) |

Reusable `⊓` failures/divergence decomposition (`⊓-failures→/←l/←r`, `⊓-div→/←l/←r`,
`⊓-⟹-peel/-inl/-inr`, `⊓-failures⊥…`) lives in `FDLawsIChoiceAssoc` — the workhorse for
every distribution law.

## §2 — External choice `□`  ✅

| Tag | Law | Status | Module |
|---|---|---|---|
| T1.1 | `P □ P = P` (idem) | ✅ | `ExtChoiceIdem` |
| T1.3 | `P □ Q = Q □ P` (comm; FD-direct **and** strong) | ✅ | `ExtChoiceComm` |
| T1.5 | `(P□Q)□R = P□(Q□R)` (assoc) | ✅ | `ExtChoiceAssoc` |
| T1.16 | `P □ Stop = P` (unit) | ✅ | `ExtChoiceComm` |
| T1.7 | `P □ (Q⊓R) = (P□Q)⊓(P□R)` (binary dist) | ✅ | `ExtChoiceFD` |
| T1.8 / U2.8 | `P □ ⨅⁺ = ⨅⁺ (P □ ·)` (replicated dist) | ✅ | `ExtChoiceDistRep` |
| T1.13 / U2.13 | `P ⊓ (Q□S) = (P⊓Q)□(P⊓S)` ^* | ✅ | `IChoiceEChoiceDist` |
| T1.14 / U2.14 | `(?x:A→P)□(?x:B→Q) = ?x:A∪B→…` (step) | ✅ | `ExtChoiceStep` |
| — | `(P⊓Q) ⊑FD (P□Q)` (□ refines ⊓; strict refinement, not an equation) | ✅ | `ChoiceRefine` |
| — | `□-fsim` (FSim congruence, TWO-sided, unconditional — **no `Sep`-style side condition**, unlike `Par-fsim`) + `□Fin-fsim`/`□⋆-fsim` (replicated folds) | ✅ | `FSim/ExtChoiceCong` (see §17 table + 2026-08-03 addendum) |
| — | `□-mono-⊑FD` **FACT-SHAPED** (`⊑FD → ⊑FD`, the true precongruence — both operands, unconditional) + fact-shaped replicated folds `□Fin-mono-⊑FD`/`□⋆-mono-⊑FD` | ✅ | `FD/ExtChoiceMonoFD` (2026-08-04; the shape-3 `FSim → ⊑FD` cash-out that held this name in `FSim/ExtChoiceCong` was RETIRED — write `fsim→⊑FD (□-fsim …)`) |

`□` decomposition (`□-failures-elim`, `□-div-elim/intro`, `□-fail-nil-→/←`,
`□-fail-intro-cons-L/R`, `□-⟹`/`▷`-bridges) in `ExtChoiceFD`. König step `□-Diverges→`
(postulate, certified — see below) in `ExtChoiceDivergence`.

## §3 — Prefix / prefix-choice  ✅

Spike `Prefix e P` = **single-channel** input `e?x:A→P(x)` (one event constructor `e`). The
general prefix-**choice** menu `?x:A→P` (A = a *set* of events, multi-channel) is `pchoice v`
(the `react v ∅t` node, `v` = the offer map). T1.9/T1.10 are single-EVENT laws (the
single-channel proofs subsume them); T1.11/T1.12 are proved both single-channel and at the
full menu (`InputDistMenu`, FD-direct over `pchoice (menuOf dom K)`).

| Tag | Law | Status | Module |
|---|---|---|---|
| T1.9 | `a→(P⊓Q) = (a→P)⊓(a→Q)` (dist) | ✅ | `FDLawsPrefixDist` |
| T1.10 / U2.10 | `a→⨅⁺ = ⨅⁺ (a→·)` (replicated dist) | ✅ | `PrefixDistRep` |
| T1.11 / U2.11 | input dist `?x:A→(P⊓Q)=(?x:A→P)⊓(?x:A→Q)` | ✅ | single-channel `InputDist`; **MENU** (A=event set, multi-channel) `InputDistMenu.input-dist-menu` |
| T1.12 / U2.12 | input-Dist `?x:A→⨅S = ⨅{?x:A→Q}` | ✅ | single-channel `PrefixDistRep`; **MENU** `InputDistMenu.input-Dist-menu` |
| T1.15 | `STOP = ?x:∅→P` (step) | ➖ | definitional (degenerate) |
| — | `P⊑FD Q ⇒ (a→₀P) ⊑FD (a→₀Q)` (prefix FD-monotone) | ✅ | `ChoiceRefine` (`⟶₀-mono-⊑FD`; see §17 table for the FSim-layer `prefix-fsim`) |
| T11.1 | input α-conversion | ➖ | N/A (prefix is a map, not a binder) |

## §4 — Conditional `P ◁ b ▷ Q`  ✅

New operator `P ◁ b ▷ Q = if b then P else Q` (`b : Bool`). All laws in `CondLaws`.

| Tag | Law | Status |
|---|---|---|
| T1.17 | `P ◁ b ▷ P = P` (idem) | ✅ |
| T1.18 / T1.19 | dist-l / dist-r over `⊓` | ✅ |
| T1.20 / T1.21 | `◁true` / `◁false` identities | ✅ |
| T1.22 | `P □ (Q◁b▷S) = (P□Q)◁b▷(P□S)` | ✅ |

## §5 — Parallel `∥` (interface / generalised)  ✅

The spike's single `Par cs dec merge` covers interface parallel `∥[X]` (and the
alphabetised/synchronous/interleaving variants reduce to it). `Par⊤` = ⊤-merge, `⦀` =
interleaving (cs = ∅).

| Tag | Law | Status | Module / note |
|---|---|---|---|
| T2.11 / U3.11 | `P ∥ Q = Q ∥ P` (comm/sym, strong) | ✅ | `ParallelComm` |
| T2.12 / U3.12 | `P ∥ (Q⊓R) = (P∥Q)⊓(P∥R)` (dist) | ✅ | `ParallelIChoiceDist` |
| T11.4/5/6 | `Div ∥ P = Div` (zero) | ✅ | `ParallelZero` |
| T2.13 / U3.13 | `(P∥Q)∥R = P∥(Q∥R)` (assoc) | ✅ | `ParallelAssoc` (failures + div), via `ParallelAssocFail`/`ParallelAssocDiv` |
| T2.10 / U3.10 | `(?x:A→P)∥(?x:B→Q) = …` (step) | ✅ | `ParallelStep` — strong bisim; `par-pVis` realises the C-merge, τ vacuous |
| T6.16 | `SKIP ⦀ P = P` (interleaving unit) | ✅ | `ParallelUnit` — strong bisim `Par Skip P ∼ P` (dead-left runs P solo) |
| — | `cong-⦀Fin` (finite-indexed `⦀Fin`-congruence: pairwise-disjoint alphabet-confined families, pointwise `≈DR` ⇒ folds `≈DR`) | ✅ | `DRCongruenceRep` (§17 table: FSim-layer `⦀Fin-fsim`, `FSim/ParCongRep`; the fact-shaped `⦀Fin-mono-⊑FD` is `FD/ParallelMonoFD`) |
| — | `cong-⦀⋆` (list-indexed `⦀⋆`-congruence, `AllPairs`-disjoint `CongCell` list ⇒ folds `≈DR`) | ✅ | `DRCongruenceRep` (§17 table: FSim-layer `⦀⋆-fsim`, `FSim/ParCongRep`; the fact-shaped `⦀⋆-mono-⊑FD` is `FD/ParallelMonoFD`) |
| — | `sep-from-OffersOnly` + `OffersOnly` confinement closure family (`-mono`/`-Ret`/`-Skip`/`-pchoice`/`-Prefix`/`-Output`/`->>=`/`-iter-bind`/`-loop0`/`-Par`/`-∖`/`-⦀`/`-⦀Fin`/`-⦀⋆-u`) — reusable alphabet-confinement invariant discharging `cong-⦀`'s `Sep` obligations from disjointness alone | ✅ | `DRCongruenceRep` (the two-carrier `SepPar` analogue is `FSim/ParCongRep.sep-from-OffersOnlyᶠ` — see §17's `Sep` duality note) |
| — | `P₁ ⊑FD P₂ ∧ Q₁ ⊑FD Q₂ ⇒ Par A m P₁ Q₁ ⊑FD Par A m P₂ Q₂` (parallel ⊑FD-monotone, generalised `Par`; corollaries `∥-mono-⊑FD` / `⦀-mono-⊑FD`) | ✅ | `ParallelMonoFD` (`Par-mono-⊑FD` = `Par-mono-⊑F⊥` × `Par-mono-⊑D`) — classical via `FDTransfer.FD→trace⊥`; no new postulates (inherits `offer-LEM`/`Par-Diverges→`/`Diverges-LEM`, all dne-certified) — **leaf-level only when composing through hiding, see §17 two-regimes note** |
| — | `P₁ ⊑F P₂ ∧ Q₁ ⊑F Q₂ ⇒ Par A m P₁ Q₁ ⊑F Par A m P₂ Q₂` (parallel **STABLE-FAILURES**-monotone; folds `∥-mono-⊑F` / `⦀-mono-⊑F` / `⦀Fin-mono-⊑F` / `⦀⋆-mono-⊑F` / `∥⁺-mono-⊑F` / `∥Fin-mono-⊑F`) | ✅ | `ParallelMonoFD` **Layer 10** (`Par-mono-⊑F`, 2026-08-05) — **UNCONDITIONAL** and, unlike `Par-mono-⊑FD`, needing **NO divergence layer at all**: `_⊑F_` (`Semantics/Failures`:42) has no `divergences` disjunct in hypothesis or conclusion, so the `⊎`-branching that forces the `⊑FD` proof through `Par-div-out-L/R/2` / `ParInter-truncL/R/2` / `div-extension-closed` / `FD→trace⊥` simply does not arise, and there is **no `Par-mono-⊑D` counterpart** — `Par-mono-⊑F` IS the headline. Reuses the divergence-free core VERBATIM (`Par-failures-elim`/`-intro`, `Par-stable-normal`, the `routeL`/`routeR` ban-set carving); only two Layer-4 twins (`op-transfer-stable-F`/`op-transfer-ret-F`) and one Layer-6 twin (`Par-mono-fail-F`) are new. Same classical provenance as `Par-mono-⊑FD` and **no more**: `offer-LEM` only (via `Par-stable`), dne-certified in `ClassicalFromLEM`; it needs neither `Par-Diverges→` nor `Diverges-LEM`. Composes with the equally unconditional `HideMonoFD.Hide-mono-⊑F` — see §17's two-regimes note, "the stable-failures regime" |

**Decomposition machinery (complete, reusable):** `ParallelDivergence`
(`Par-div-elim/intro`, `Par-Diverges-L/R`), `ParallelFailures`
(`Par-failures-elim/intro-top`), `ParallelRefusals` (`ParRef`, refusal cs-split,
stability classify), `TraceLawsParallelInterAssoc` (`ParInter-assoc`). König step
`Par-Diverges→` + `offer-LEM` are postulates (certified from `dne` in `ClassicalFromLEM`).

## §6 — Hiding `∖`  🟡 (FD laws begun)

Trace-level machinery in `Laws/Traces/{TraceLawsHide,TraceLawsHideAlg,HideRegression}`
(`Hide-τ`/`Hide-keep`/`Hide-hidden`/`Hide-√` constructors, `Hide-τ-elim`/`hide-hVis-inv`
inversions, `∅es`, `_∪es_`). FD laws now started:

| Tag | Law | Status |
|---|---|---|
| T3.1 / U5.1 | `(P⊓Q)∖X = (P∖X)⊓(Q∖X)` (dist) | ✅ `HideDist` (strong bisim) |
| T3.4 / U5.4 | `P ∖ ∅ = P` (null hiding) | ✅ `HideUnit` (strong bisim) |
| T11.7 / U13.2 | `Div ∖ X = Div` (zero) | ✅ `HideZero` (div-strict) |
| T3.3 / U5.3 | `(P∖Y)∖X = P∖(X∪Y)` (combine) | ✅ `HideCombine` (nested-hide coind bisim + `_∪es_`) |
| T3.2 / U5.2 | `(P∖Y)∖X = (P∖X)∖Y` (sym) | ✅ `HideSym` (via combine + `hide-mem-cong` + `∪es`-comm) |
| T3.6 (A∩X=∅) | `(?x:A→P)∖X = ?x:A→(P∖X)` (step, no hide) | ✅ `HideStep` `hide-prefix-out-FD` (strong bisim) |
| T3.5 (a∈X) | `(a→P)∖X = P∖X` (step, hidden) | ✅ `HideStep` `hide-prefix-hidden-FD` (hand-built ≈DR, τ-slide) |
| T3.6 (A∩X≠∅) | `(?x:A→P)∖X = (?x:A\X→(P∖X)) ▷ ⨅{P a∖X : a∈A∩X}` (MENU, multi-channel) | ✅ `HideStepFull` `hide-step-full-FD` (FD-direct over `pchoice v`; ops `RPrefix`/`GChoice` + reusable `slide-fuse-FD`; force-eq bridge, no connecting bisim) |
| U13.3 | hide-slide `((?x:A→P)▷Q)∖X = (?x:A\X→(P∖X)) ▷ ⨅({Q∖X}∪{P[a/x]∖X : a∈X∩A})` (MENU) | ✅ `HideSlide` `hide-slide-FD` — `((pchoice v)▷Q)∖X ≈FD RPrefix v X ▷ GChoiceS v Q X`, general `R`, **no `DecEq`, no side-condition**. Near-clone of `HideStepFull`: `force((pchoice v ▷ Q)∖X)` IS the fused node with τ-map `hide-hTau X (force of the slide)` (tag0 timeout → `Q∖X`, tag1 hidden events → `P[a]∖X`). Hop1 `(S∖X)∼fused` strong bisim (visible offers agree pointwise via `hVis-eq` — NOT definitionally, `hide-hVis` guards on `dec` before `viewV`; τ-maps identical); hop2 `slide-fuse-FD`. The slide's timeout always gives `GChoiceS ─τ→ Q∖X` ⇒ unstable witness FREE, no `mem₀` side-condition (unlike T3.6 full). No postulates |
| T3.7 / T3.8 | hide–parallel dist `(P∥Q)∖Z = (P∖Z)∥(Q∖Z)` (Z∩cs=∅) | 🚧 IN PROGRESS (FD-direct, not a bisim) — foundation `HideFD` failures **+** divergence decomposition ✅ (`Hide-failures-elim/intro`, `Hide-div-elim/intro`); TODO: `Hide-Diverges→` König (certify from dne) + combine with `ParallelFailures`/`ParallelDivergence` |
| — | `P ⊑FD Q ⇒ (P∖A) ⊑FD (Q∖A)` (hide ⊑FD-monotone) | ⚠️ **CONDITIONAL** `HideMonoFD` — the UNCONDITIONAL law is **FALSE** in this model.<br><br>Delivered: (i) `Hide-mono-fail` — the UNCONDITIONAL stable-failure transfer `P ⊑F⊥ Q ⇒ failures (Q∖A) s X ⇒ failures⊥ (P∖A) s X`; (ii) `Hide-mono-⊑FD-df` — the full law `(P∖A) ⊑FD (Q∖A)` **under a divergence-freedom side condition** `∀ {s} → ¬ divergences (Q∖A) s`, i.e. on the **REFINED / RIGHT (implementation) operand's hide `Q∖A`**, NOT on the spec's (`HideMonoFD.agda:243`, :268-270); (iii) **`Hide-mono-⊑F` — the STABLE-FAILURES analogue, UNCONDITIONALLY** (`HideMonoFD.agda:255`, 4 lines, added 2026-08-04): `P ⊑F Q ⇒ (P∖A) ⊑F (Q∖A)`, no side condition of any kind. It is the `inj₁` branch of `Hide-mono-fail` verbatim: `_⊑F_` (`Semantics/Failures`:42) is a plain failures-to-failures map with **no `divergences` disjunct in either its hypothesis or its conclusion**, so the `inj₂ dP` branch — and everything it drags in (`HideTr-split`, `div-extension-closed`, `Hide-div-intro`, `hide-Diverges-lift`) — has no counterpart. This is the ONE hiding law that is both FD-flavoured (refusals, not just traces) and unconditional; the parallel half that composes with it is `ParallelMonoFD.Par-mono-⊑F` (Layer 10).<br><br>WHY unconditional fails: hiding can *create* divergence (an infinite hidden-event τ-path), which `⊑FD` does not constrain; under unbounded nondeterminism `P ⊑FD Q` does not give `(P∖A) ⊑D (Q∖A)` — counterexample (`Q = μX.h→X`, `P = ⊓ₙ hⁿ;STOP`) in the `HideMonoFD` header (Roscoe's known N-model hiding unsoundness). `modA-transfer` needs `≈DR` not `⊑FD`; no dne-certified postulate can rescue a false ∀-`E` statement.<br><br>**ZERO postulates** (built on `HideFD`/`TraceLawsHide` only). For trace-only refinement `Hide-mono-⊑ᵀ` stays unconditional.<br><br>**(2026-07-31 additions, see §15.)** (a) At the SIMULATION level the congruence IS unconditional: `CSP/Laws/FSim/HideCong.agda`'s `Hide-fsim : FSim R P₁ P₂ → FSim R (P₁ ∖ A) (P₂ ∖ A)` has NO side condition. That is consistent, because `FSim` is strictly STRONGER than `⊑FD`: `CSP/Laws/FSim/HideCounterexample.agda`'s `¬fsim-Pinf-Qh : ¬ (FSim Rt Qh Pinf)` proves the very counterexample pair is not an `FSim`, so it can never be fed to `Hide-fsim`. The trade is real — you must supply a simulation WITNESS, not a `⊑FD` fact, and completeness (`⊑FD → FSim`) does **not** hold in general.<br><br>(b) **`Hide-mono-⊑FD-finBr` is FALSE too** — `CSP/Laws/FD/HideMonoFinBrFail.agda` constructs `finBr-Pinf : FinBr Pinf` for the very `P = ⊓ₙ(hⁿ;STOP)` of the counterexample, so a `FinBr` hypothesis on the refining side excludes NOTHING. Reason: `FinBr` bounds only the VISIBLE channel support (`chan-supp`, here `[]` — `Pinf` offers `∅v`) and never τ-fan-out, which it records merely as a `Dec (isStable ·)`; the counterexample's unbounded branching is entirely on τ. **Generalise the lesson: `FinBr` cannot rescue any law whose obstruction is König.**<br><br>(c) Still UNFORMALISED, stated plainly: that the counterexample pair genuinely satisfies `Pinf ⊑FD Qh` *denotationally* remains prose in `HideMonoFD`'s header — nothing in the repo proves it. Neither negative result needs it (refuting `Hide-fsim` would require exhibiting an `FSim`; refuting the `FinBr` repair only requires the certificate), but the denotational half of the classic counterexample is a genuine gap.<br><br>**See §17 for the consolidated cross-relation table and the "why hiding is the crux" finding** (unconditional `Hide-mono-⊑FD` is FALSE, so carrying an FD-strength refinement through hiding needs a WITNESS — `Hide-fsim`/`fsim→⊑FD` one-way, or `cong-∖`/`hide-cong-FD` two-way — not a bare `⊑FD` fact).<br><br>**On the weaker orders, stated so this cell no longer contradicts itself:** `⊑T` *does* compose through hiding unconditionally (`Hide-mono-⊑ᵀ`). `⊑F⊥` does **not** — `Hide-mono-fail`, described at the top of this cell, has `failures` as its INPUT and `failures⊥` as its output, so it is the stable-failure transfer and **not** `(P∖A) ⊑F⊥ (Q∖A)`; unconditional `⊑F⊥` monotonicity through hiding fails by the same divergence-chaos mechanism that kills `⊑FD`, since what breaks is `failures⊥`'s `divergences` disjunct, which both orders contain. Full argument and line references in §17. |

## §7 — Renaming `⟦R⟧`  🟡 (FD layer begun)

Relational renaming + general fan-in trace laws done: `TraceLawsRename`,
`TraceLawsRenameGen` (intro/elim/mono). **FD layer now begun** for the **injective**
single-E renaming `_⟦inv⟧ⁱ` (`renameInv`, clean non-weak inversions `ren-τ-inv`/`ren-ev-inv`/
`ren-trace-elim`). Renaming preserves `ret` and passes τ's through 1-1 ⇒ **no König step**
(divergence lifts directly — strictly simpler than hiding).

| Tag | Law | Status |
|---|---|---|
| T11.8 / U13.5 | `Div⟦R⟧ = Div` (zero) | ✅ `RenameZero.rename-zero-FD` (div-strict, `HideZero` clone; trivial) |
| T3.13 | `(P⊓Q)⟦R⟧ = (P⟦R⟧)⊓(Q⟦R⟧)` (dist over `⊓`) | ✅ `RenameIChoiceDist.rename-⊓-dist-FD` — **STRONG bisim**, port of `HideDist` (`ren-τ-inv`+`⊓-τ-inv`↦`⊓-stepL/R`, on-ev vacuous via `rename-⊓-no-ev`+`⊓-no-ev`); injective `_⟦inv⟧ⁱ` |
| T3.14 | `(P□Q)⟦R⟧ = (P⟦R⟧)□(Q⟦R⟧)` (dist over `□`) | ✅ `RenameEChoiceDist.rename-□-dist-FD` — **coinductive STRONG bisim** (injective `_⟦inv⟧ⁱ`, ⦃DecEq R⦄). Mutual `∼`/`∼R` (reversed, for guarded bwd); `□`-τ residuals (`chP`/`chQ`) recurse; overlap event (`evPQ`→`P₁⊓Q₁`) bridged by the imported `rename-⊓-dist-∼`; `□`-slide cases (`sPQ`/`sQP`, fire only when one side `ret`) bridged by an auxiliary `rename-▷-dist-∼` (rename over `▷`, general operands, also mutual/reversed). 782 lines. No postulates |
| T3.15 | `⟦R⟧`-step `(?x:A→P)⟦R⟧ = ?y:R(A)→⨅{P[a/x]⟦R⟧:a R y}` | ✅ `RenameStep.rename-step-FD` — `(pchoice v)⟦inv⟧ⁱ ≈FD pchoice (renMenu inv v)` (injective `_⟦inv⟧ⁱ`; `⨅` collapses, `renMenu inv v bt b = map (_⟦inv⟧ⁱ) (v (inv⁻¹ bt b))`). STRONG bisim via the reused `SeqSlide.node-pw2` (pointwise-both-maps): `vis-pw` (the operator's `rnFan∘rnCollect∘invPreimg` collapses to `renMenu` on the singleton preimage — `refl` per case) + `tau-pw` (`extBranch … ∅t = ∅t` via `rnMc … nothing`). No postulates |
| T3.16 / T3.17 | combine `P⟦R⟧⟦S⟧ = P⟦S∘R⟧` | ✅ `RenameCombine.rename-combine-FD` — `(P⟦inv₁⟧ⁱ)⟦inv₂⟧ⁱ ≈FD P⟦invComp inv₁ inv₂⟧ⁱ`, `invComp inv₁ inv₂ = inv₂ >>= inv₁` (Kleisli, outer-first). Coinductive mutual STRONG bisim `∼`/`∼R` (step-inversion: invert both rename layers via `ren-*-inv`, rebuild via `ren-*-fwd` with the composed witness `invComp-just`/`invComp-split`); recurses on `P`. No `DecEq` (no merge case). No postulates |
| U13.6 | rename-slide `((?x:A→P)▷Q)⟦R⟧ = (?y:R(A)→⨅{…})▷(Q⟦R⟧)` | ✅ `RenameSlide.rename-slide-FD` — `((pchoice v)▷Q)⟦inv⟧ⁱ ≈FD ((pchoice v)⟦inv⟧ⁱ)▷(Q⟦inv⟧ⁱ)`, injective `_⟦inv⟧ⁱ` (the `⨅` collapses; `R(A)`=renamed prefix). **NON-recursive STRONG bisim** (renaming relabels events, never hides ⇒ no fusion, unlike hide-slide; prefix τ-free ⇒ no coinduction): step-matched via `ren-*-inv`/`ren-*-fwd` + `▷-ev-L`/`▷-timeout`/`▷-{τ,ev}-elim`, `sbisim-refl` conts; impossible prefix-τ / `√`-from-ret discharged by `pchoice-no-τ`/`ren-pchoice-no-τ`. No postulates |

**Note:** laws are for the injective `_⟦inv⟧ⁱ`; the relational/fan-in generalisation (weak
steps via `TraceLawsRenameGen`) is future work (single-case-first, cf. single-channel→menu).

## §8 — Piping `≫` / enslavement  ❌

Not started (UCS treats piping as derived from parallel+rename+hide; no spike operator).

## §9 — Sequential composition `;`, `SKIP`  ✅ (core)

`P >> Q = P >>= λ_→Q`; `SKIP = Ret tt`.

| Tag | Law | Status | Module |
|---|---|---|---|
| T6.1 | `(P⊓Q);R = (P;R)⊓(Q;R)` (dist-l, strong) | ✅ | `FDLawsSeqDist` |
| T6.2 | `P;(Q⊓R) = (P;Q)⊓(P;R)` (dist-r, FD-direct) | ✅ | `SeqDistR` |
| T6.3 | `(P;j);k = P;(j;k)` (assoc) | ✅ | `SeqAssoc` |
| T6.4 / U7.2 | `SKIP;P = P` (unit-l) | ✅ | `SeqLaws` |
| T6.5 / U7.1 | `P;SKIP = P` (unit-r) | ✅ | `SeqLaws` |
| T6.7 / U7.4 | `(?x:A→P);Q = ?x:A→(P;Q)` (step) | ✅ | `SeqLaws`: single-channel `prefix-step-FD`; **MENU** (A=event set, multi-channel) `seq-step-menu-FD` |
| T6.6 / T6.8 | extc-SKIP-resolve / SKIP-;-step | ❌ | slide/extc (→ §11) |
| T6.9–6.16 | SKIP-termination (cross-operator) | ❌ | belong to hide/rename/parallel/interrupt |

König step `>>-Diverges→` (postulate, certified) in `SeqDistR`.

`⊑FD` MONOTONICITY of `;` is `>>-mono-⊑FD` (`FD/BindMonoFD`, 2026-08-04): FACT-SHAPED
(`⊑FD → ⊑FD`), two-sided, unconditional, inheriting only `>>-Diverges→` (via `>>-split`)
and `Diverges-LEM` (via `FDTransfer`). The replicated fold `⨾⋆`/`⨾Fin` follows by
induction (`⨾⋆-mono-⊑FD` / `⨾Fin-mono-⊑FD`, same module — EMPTY-based, `⊑FD-refl Skip`
at the base). See §17.

## §10 — Interrupt `△` / Throw `⟦A▷`  ✅

| Group | Law | Status | Module |
|---|---|---|---|
| U7.5 | interrupt step `(?x:A→P)△(?x:B→Q) = (?x:A→(P△(?x:B→Q)))□(?x:B→Q)` | ✅ | `InterruptFD`: single-channel `△-step-FD`; **MENU** (A,B=event sets) `△-step-menu-FD` |
| Fig 13.6 | interrupt-over-slide `((?x:A→P)▷P′)△Q = (?x:A→(P△Q))▷(P′△Q)` | ✅ | `InterruptFD`: single-channel `△-slide-dist-FD`; **MENU** `△-slide-dist-menu-FD` |
| Fig 13.6 | interrupt: `△-Pret-⊓`, `△-div-row`, `△-⊓L/R-dist`, `△-step` | ✅ | `InterruptFD` |
| U7.6 | throw step `(?x:A→P)⟦B▷Q = ?x:A→(P⟦B▷Q ◁ x∉B ▷ Q)` | ✅ | `ThrowFD`: single-channel `Θ-prefix-step`; **MENU** (A=event set) `Θ-step-menu-FD` |
| — | throw: `Θ-Pret`, `Θ-div`, `Θ-⊓L/R-dist` | ✅ | `ThrowFD` |
| — | `Θ-fsim` (FSim congruence, **TWO-SIDED, UNCONDITIONAL**, no `Sep`-style side condition, no divergence-freedom hypothesis, `--safe`-clean) | ✅ | `FSim/ThrowCong` (see §17 table + 2026-08-04 addendum) |
| — | `Θ-mono-⊑FD` **FACT-SHAPED** (`⊑FD → ⊑FD`, the true precongruence — body AND handler, unconditional).  Rests on the new run decomposition `Θ-reach-split` (`θNo`/`θFire`/`θDone`) over `A`-free traces; 0 local postulates, inherits only `FD→trace⊥`'s `Diverges-LEM`/`¬-divergent→normal` (fire arm only), NOT a König step | ✅ | `FD/ThrowMonoFD` (2026-08-04; the shape-3 cash-out that held this name in `FSim/ThrowCong` was RETIRED — write `fsim→⊑FD (Θ-fsim …)`) |

König step `△-Diverges→` (postulate, certified) in `InterruptDivergence`. Throw is
postulate-free, and its own divergence bridge `Θ-Diverges→` (`FSim/ThrowCong`'s `div→`
field) is **structural** — no König step, no postulate at all (see the 2026-08-04 §17
addendum for why).

## §11 — Sliding choice `▷` (UCS Ch.13)  🟡

`▷` is used pervasively as the timeout/slide inside `□` and interrupt laws (slide-dist,
√-slide bridges). First standalone `▷` laws (divergence-strict):

| Tag | Law | Status | Module |
|---|---|---|---|
| — | `Div ▷ Q ≈FD Div` (slide left-zero) | ✅ | `SlideZero.slide-Div-L-FD` |
| — | `P ▷ Div ≈FD Div` (slide right-zero, P non-ret) | ✅ | `SlideZero.slide-Div-R-FD` |
| U13.13 | `Div ▷ Q = Div ⊓ Q` (Div-slide) | ✅ | `SlideZero.slide-Div-FD` (via ⊓-zero) |
| U13.16 | `P □ Div = P ▷ Div` (□-div, P non-ret) | ✅ | `SlideZero.□-div-FD` (both = Div; via □-comm+□-zero) |
| U13.12 | ▷-assoc `P▷(Q▷R)=(P▷Q)▷R` (Q non-ret) | 🟡 | `SlideAssoc.slide-assoc-FD` — holds **conditionally** (`NonRet (force Q)`); the *unconditional* law is ✖ (counterexample P=a→STOP, Q=SKIP, R=b→STOP: RHS has trace ⟨b⟩, LHS does not, same eager-`ret` `▷` cause as U13.14). Coinductive DR-bisim (mutual `sa→`/`sa←`, no `drbisim-sym`); divergence transfers `build→`/`build←` via copattern-guarded corecursion + non-corecursive `decompose→`/`decompose←` (sidesteps the guardedness-through-`with` issue) |
| U13.14 | SKIP-slide `SKIP▷Q=SKIP⊓Q` | ✖ | does NOT hold — spike `▷` resolves `ret` eagerly (`SKIP▷Q=SKIP`, drops Q) |
| T6.6/U13.17 | □-SKIP-resolve `P□SKIP = P▷SKIP` | ✅ | `SlideSkipResolve.□-SKIP-resolve-FD` — **STRONG bisim, NO side-condition** (at `R=⊤`): `□-slide-PR nP Skip` and `▷-slide nP Skip` are clause-for-clause identical ⇒ same offers + identical successors. Generic `node-pw` (same `v`, pointwise-equal τc, `sbisim-refl` successors) for live `force P`; `sbisim-force-eq` for the `ret` case. The general `P□Ret r` is ✖ (eager-`ret` mismatch when `force P=ret r₀≠r`); `⊤` rules that out |
| U13.19 | extc-Div-SKIP-red `Div□SKIP = Div⊓SKIP` | ✅ | `SlideZero.□-Div-SKIP-red-FD` — both reduce to `Div` (div-strict): `≈FD-trans (□-zero-FD Skip) (≈FD-sym (⊓-zero-FD Skip))` |
| U13.8 | seq-slide `((?x:A→P)▷P′);Q = (?x:A→(P;Q))▷(P′;Q)` | ✅ | `SeqSlide.seq-slide-FD` — single-channel prefix h.n.f. (`>>`, x∉fv(Q) automatic), general `R`/`S`, no `DecEq`. **STRONG bisim** (not FD-direct): the bind `>>Q` pushes uniformly through the prefix offer *and* the timeout, so both sides force to a `react` node with pointwise-equal visible/τ maps and identical successors. Generalised `SlideSkipResolve.node-pw` → `node-pw2` (pointwise-equal *visible* map too); force eqns via `fBind-react ∘ force-▷-react`; every pointwise case `refl`; lifted `drbisim→≈FD ∘ sbisim→drbisim`. **MENU** (A=event set, multi-channel): `SeqSlideMenu.seq-slide-menu-FD` `((pchoice v)▷P′)>>Q ≈FD (pchoice (mapBind (λ_→Q) v))▷(P′>>Q)` — reuses `node-pw2` + `SeqLaws.mapBind`; visible pointwise even simpler (no `E-≟`, `bindV K (react v _) = mapBind K v` by a `v at a` split) |
| U13.22 | ▷-⊓-ext `((?x:A→P)▷P′)⊓Q = (?x:A→P)▷(P′⊓Q)` | ✅ | `SlideIChoiceExt.▷-⊓-ext-FD` — single-channel prefix h.n.f., general `R`, NO side-condition, no `DecEq`. FD-direct (internal-choice analogue of U13.15 □-slide; same time-0 ⊓-resolution mismatch ⇒ not a bisim). `⊓` is simpler than `□`: `⊓-failures⊥→`/`⊓-div→` split `S⊓Q` directly (Q behind a τ, no offer-merge). Workers `S→RHS-fail`/`-div` (recurse on S's big-step, prefix event kept explicit, `P′⊑P′⊓Q` via `⊓-…←l`) + `RHS→LHS-fail` (recurse on RHS big-step, timeout splits `P′⊓Q`). No new postulates |
| U13.21 | ▷-combine `((?x:A→P)▷(?x:B→Q))▷R = (?x:A∪B→((P⊓Q)◁x∈A∩B▷(P◁x∈A▷Q)))▷R` | ✅ | `SlideCombine.slide-combine-FD` — **MENU form** `((pchoice vP)▷(pchoice vQ))▷T ≈FD (pchoice (mergeVis vP vQ))▷T`, general `R`, **no `DecEq`**. The `A∪B`-merge-with-conditionals IS `mergeVis vP vQ` (same as `□-step`). Outer `▷T` essential (else the cross-domain ⟨⟩-refusals differ). FD-direct, NOT a bisim. Built new general `pchoice v` decomposition (`pchoice-⟹-inv`/`-failures→`/`-div→`, arbitrary `v` — the existing `menu-*`/`pfx-*` only cover `menuOf`/single-channel); recurses manually on the slides (DecEq-free, avoids `▷-failures-elim`/`□-step`). Crux routing: an LHS `vP`-event → RHS event with cont `P₁` (A-only) or `P₁⊓Q₁` (overlap, `⊓-…←l`); an LHS inner-timeout `vQ`-event → cont `Q₁` (B-only) or `P₁⊓Q₁` (`⊓-…←r`), via `mergeVis-L/R/LQ-eq`. No new postulates |
| U13.25 ^* | ▷-nohist `(?x:A→P)▷(?x:A→Q) = ?x:A→(P⊓Q)` | ✅ | `SlideNoHist.nohist-FD` — single-channel value-dependent `(e⟶P)▷(e⟶Q) ≈FD e⟶(λx→P x⊓Q x)`, general `R`, **no `DecEq`, no side-condition** (single-channel = same domain automatically). FD-direct (LHS unstable via timeout, RHS stable — not a bisim). Reuses `InputDist`'s value-dep prefix decomposition (`pfx-failures⊥→`/`pfx-refuses`/`pfx-failures⊥-nil/-cons`) for the RHS prefix + both LHS prefixes; the `⊓` of continuations routes via `⊓-stepL/R` / `⊓-failures⊥←l/r`. RHS→LHS recurses manually on the slide big-step (DecEq-free, avoids `▷-failures-elim`); LHS→RHS via `▷-reach-div`. No new postulates |
| U13.26 ^* | ▷-failures-char `P▷Q = (P□Q)⊓Q` | ✅ | `SlideFailuresChar.▷-failures-char-FD` — **general `P`/`Q`, side-condition `NonRet (force P)`** (eager-`ret` breaks it unconditionally), `DecEq R`. The model-characterising law (`*` = FD-model-specific). **FD-direct**, NOT a DR-bisim (the `P□Q` intermediate offers `init P∪init Q` which `P▷Q` never offers stably). EASY side (`RHS⊑·LHS`): `▷-failures-elim`/`▷-reach-div` (P▷Q never stable ⇒ `▷-unstable` kills the empty-trace base, no bare-P-refusal case). HARD side (`LHS⊑·RHS`): worker `□→▷-fail` recurses on `(Pc□Qc)⟹⟨s⟩W` carrying `P▷Q─τ*→Pc▷Q` and `Q─τ*→Qc` — P-events replay via `▷-ev-L`, Q-events/τ's + the joint stable refusal route through the root timeout (`route-Q`, via new Q-side mirror `□-refl-fail-R`); Qc-terminated slide residual handled by `▷→▷-fail`. No new postulates |
| U13.18 | ▷-id `P▷P = P` | ✅ | `SlideId.▷-id-FD` — **general `P`, general `R`, NO side-condition, no `DecEq`**. **FD-direct** (NOT a bisim — intermediate `t▷P ≉ t`). `ret`-`P` case: identical `force` ⇒ `sbisim-force-eq`. Live-`P` case: both operands are `P`, so the eliminators `▷-reach-div P P` (⊑D) and a local DecEq-free `▷-fail-elim P P` (⊑F⊥) collapse to the `P`-side; the intro directions just prepend the single timeout τ (`P▷P ─[τ]─► P`, via `▷-timeout`) with `div-τ-prepend`/`fail-τ-prepend`. No new postulates |
| U13.15 | □-slide `(P▷P′)□Q = P▷(P′□Q)` | ✅ | `ExtChoiceSlide.□-slide-FD` — single-channel prefix h.n.f. `((e⟶P)▷P′)□Q ≈FD (e⟶P)▷(P′□Q)`, **general `R`, NO side-condition**. **FD-direct, NOT a DR-bisim**: LHS can advance `Q` by an internal τ while *keeping the choice + timeout open*, but RHS can only progress `Q` *after* firing the timeout (committing, losing the prefix offer) — so that LHS τ has no DR-match; ≈FD abstracts the gap. The prefix gives ▷ a non-terminating left operand (no eager-`ret`); the slide-on `P′▷Q` *can* eager-`ret` but both sides expose the *same √-value set*, so FD survives. Structure mirrors `InterruptFD.△-slide-dist` (⊑D/⊒D/⊑F⊥/⊒F⊥), key asymmetry: prefix continuation `P` is **unchanged** on the RHS (a visible event resolves the choice, discards Q). ⊒F⊥ worker `□-slide-fail-elim` recurses on the LHS big-step carrying `Q ─τ*→ Qc`; reuses `▷-failures-elim`/`▷-reach-div`/`□-failures⊥-elim`/`□-div-elim`/`□→▷-term`/`slide-term-fail` + new R-mirror bridges. No new postulates |
| — | `▷-fsim-R` (FSim congruence, **ONE-SIDED ONLY**: left operand `P` SHARED, right operand varies — `FSim R Q₁ Q₂ → FSim R (P▷Q₁) (P▷Q₂)`) + `▷-mono-R-⊑FD-fsim`, unconditional given that one-sided shape | ⚠️ one-sided | `FSim/SlideCong` (see §17 table + 2026-08-03 addendum) |
| — | the TWO-sided `▷`-congruence (`FSim R P₁ P₂ → FSim R Q₁ Q₂ → FSim R (P₁▷Q₁) (P₂▷Q₂)`, both operands varying) is **PROVED FALSE** — `--safe`-clean, 0 postulates transitively | ✖ | `FSim/SlideCounterexample.¬▷-fsim` (see the 2026-08-03 addendum below §17 for the witnesses and mechanism; a proved negative result, not an unattempted gap — joins §6's `Hide-mono-⊑FD`/`Hide-mono-⊑FD-finBr` FALSE results as a further, independent point where a naive two-sided congruence fails; no uniqueness claim made about any one operator) |

**SPIKE NOTE (§11):** the spike's `▷` has a *different termination semantics* from CSP's sliding choice — it resolves a terminated (`ret`) operand eagerly (P wins, the timeout/Q is dropped), whereas CSP's `▷` makes termination-vs-timeout an internal choice (`SKIP▷Q=SKIP⊓Q`).  So the CSP laws that depend on `▷`'s `ret`-handling FAIL *unconditionally* here (U13.14 SKIP-slide; U13.12 ▷-assoc when Q may terminate).  ▷-assoc is nevertheless recovered in the `NonRet Q` regime (where the eager-`ret` obstruction is absent) — see `SlideAssoc`.  The laws independent of `▷`'s `ret`-handling (the divergence-strict ones above) transfer unconditionally.

## §13 — Zero / divergence-strictness (`Div = ⊥`)  🟡

| Tag | Law | Status |
|---|---|---|
| T11.2 | `Div ⊓ P = Div` | ✅ `FDLawsIChoiceZero` |
| T11.3 | `Div □ P = Div` | ✅ `ExtChoiceZero` |
| T11.4/5/6 | `Div ∥ P = Div` | ✅ `ParallelZero` |
| T11.9 / U13.7 | `Div ; P = Div` | ✅ `SeqZero` |
| T11.7 / T11.8 | hide-zero / rename-zero | ✅ `HideZero` / `RenameZero` (both div-strict) |
| T11.10–11.13 | SKIP/√-head-normal-form, `∥`-timeout splits | ❌ |

All zeros share one trivial pattern: `Op-Diverges`-lift + `div-extension-closed` ⇒ both
sides ⊥ at every trace.

## §12 — Bind / Iterate (FD characterisation)  🟡

Foundational FD characterisation for `>>=` / `iter` / `loop`, towards loop-level
refinement (VM §5.3b/§5.3c). Decomposition: **A** bind → **B** iterate
characterisation → **C** iterate refinement-monotonicity → **D** VM rewire.

| Piece | Status | Module |
|---|---|---|
| Bind FD characterisation: force (ret/sil/react) + continuation lemmas, `lift-bind-bigstep`, `BindSplit`/`bind-bigstep-inv`, bind divergence + failures⊥ elim/intro (**sub-project A**) | ✅ | `CSP.Laws.FD.BindFD` |
| Iterate FD characterisation: iter-bind force/cont, `lift-iter-bigstep`, `IterSplit`/`iter-bind-inv`, `LoopSplit`/`loop-trace`/`-intro`, `loop0-failures⊥-elim`/`-intro`, loop0 divergence + silent-spin (**sub-project B**) | ✅ | `CSP.Laws.FD.IterateFD` |
| Iterate refinement-monotonicity `loop0-mono-⊑FD` — **sub-project C** | ✅ | `CSP.Laws.FD.IterateMonoFD` (FD-direct, FACT-SHAPED, and the only `loop0` monotonicity law — the FSim-routed `loop0-mono-⊑FD-fsim` wrapper was retired 2026-08-04.  The rest of the family is now fact-shaped too, in `CSP.Laws.FD.IterMonoFD` (`iter`/`loop`/`while`/`loopc`, 2026-08-04), which generalises THIS proof to a state-indexed step; `loopc-mono-⊑FD` IS this law, `loopc` and `loop0` being the same definition) |
| Bind refinement-monotonicity `>>=-mono-⊑FD` / `bindNoτ` / `bindκ` / `>>-mono-⊑FD` + the sequential folds `⨾⋆`/`⨾Fin` (2026-08-04) | ✅ | `CSP.Laws.FD.BindMonoFD` (FD-direct, FACT-SHAPED; the FSim-routed `Bind-`/`bindNoτ-`/`bindκ-`/`>>-mono-⊑FD` wrappers in `FD/LoopMonoFD` were RETIRED (that module is now deleted outright).  Built on **A**'s elim/intro suite plus a `bind-div-elim⁺` variant that RETAINS the `force Pᵣ ≡ ret r` handover witness `bind-div-elim` discards — re-introducing a handover divergence needs exactly that equation, which is why `bind-div-elim` alone is not enough here) |
| VM loop-level FD rewire: `VM_spec⊑FD-VM_impl` (§5.3b, via `loop0-mono-⊑FD`) + `loop-lesson-✗` strictness (§5.3c, via `loop0-failures⊥-elim`/`-intro` + the refusal-transport helpers) — **sub-project D** | ✅ | `CSP.Examples.VendingMachine.VendingMachine` |

Note (sub-project A): `bind-div-elim` keeps the in-`P` divergence witness inside
`P′ >>= k` (reflecting it to `P` alone is a König/LEM obstruction); `bind-failures⊥-elim`'s
in-`P` branch carries a `failures⊥ (P′ >>= k)` to subsume that case. No postulates / no
`NON_TERMINATING`.

Note (sub-project C): `loop0-mono-⊑F⊥` is direct via B — **postulate-free**, by
well-founded recursion on a run-step measure (`runLen`); `loop0-mono-⊑D` is via the
documented iterate König postulate `loop-Diverges→` (the single classical input; the
body-internal `>>= loop-k` peel `bind-loopk-Diverges→` and the silent-spin transfer
`loopD-transfer` are constructive). `loop-Diverges→` is **certified sound from `dne`**
(Derivation 6, `iter-no-inf`, in `CSP.Laws.ClassicalFromLEM`).

Note (sub-project D): the VM module adds **no** postulate / hole / pragma. §5.3b is a
one-liner `loop0-mono-⊑FD VM_body_spec VM_body_impl canonical-lesson-✓`. §5.3c lifts the
body counterexample one `loop0` layer: the spec witness is built with
`loop0-failures⊥-intro-failures` + the exported refusal-intro helpers
(`refuses-bind-intro`/`refuses-iter-intro`); the impl refutation decomposes with
`loop0-failures⊥-elim` — the divergence arm is refuted via `loop-Diverges→` (the body
never diverges and the stable `coin`-react never loops back on the single-`coin` trace),
the failure arm peels back through `>>= loop-k`/`iter-bind` to the body's `(tea □ coffee)`
state, which offers `tea`. No new helpers were added to `IterateFD`/`IterateMonoFD`; the
VM module only widened its `using` lists to import existing definitions
(`refuses-*`, `body-terminates`, `ret-stuck`, `⟹-then-τ*`, `map-evl-inj`).

## §14 — Recursion  ❌

Not started.

## §15 — One-way failure simulation `FSim` (the `⊑FD` refinement order)  ✅

**What it is, and why it exists.** Until now `⊑FD` had exactly ONE route: `drbisim→⊑FD`,
which consumes all four `DRbisim` fields (`fwd`, `bwd`, `div→`, `div←`). For a
*refinement* the `bwd` and `div←` halves are dead weight — and worse than dead weight,
because supplying them forces the abstract (spec) side of every proof to be reflected
back through the whole operator stack. `FSim` is the one-way alternative: a coinductive
record with **three** fields and no `bwd` / `div←`.

**Orientation — state it explicitly, it is easy to get backwards.** In `FSim R t₁ t₂`
the FIRST argument is the **IMPLEMENTATION** and the SECOND the **SPECIFICATION**
(mirroring `Semantics.WeakSim`'s `WSim`), so the headline theorem reads

```
fsim→⊑FD : FSim R Q P → P ⊑FD Q
```

The three fields (`Semantics/FailureSim.agda`):

| Field | Type | Reading |
|---|---|---|
| `fwd` | `WSimF (FSim R) t₁ t₂` | every impl step matched by a WEAK spec step — the `bwd`-free half of the existing DR congruences |
| `stab` | `isStable t₁ → Σ[ t₂′ ] (t₂ ─[τ*]─► t₂′ × isStable t₂′ × (∀ e → Offers t₂′ e → Offers t₁ e))` | a stable impl lets the spec silently SETTLE into a stable state offering **no more** than the impl (the inclusion runs spec-offers ⊆ impl-offers, which is what lets a refusal travel impl→spec) |
| `div→` | `Diverges t₁ → Diverges t₂` | the only divergence direction `⊑D` consumes |

| Result | Module |
|---|---|
| `FSim` record; `fsim-trace-sim` (big-step replay), `fsim→wsim`, `fsim→⊑T`, `fsim→⊑D`, `fsim→⊑F⊥`, `fsim→⊑FD`; preorder `fsim-refl` / `fsim-trans` (with the `FSim`-specific weak-step lifts `fsim-τ*-sim` / `fsim-wev-sim`, since `WeakBisim`'s are hard-coded to `Wbisim`) | ✅ `Semantics/FailureSim.agda` — **postulate-free**, and deliberately imports nothing supplying `dne` |
| `FSimFromRel` coinduction principle: `fwdE` / `fwdT` (the two FORWARD obligations of `DRFromRel`, reusable verbatim) + `stabR` (the `stab` field with `Rel p q` in front) + `ndivL`; `bwdE`, `bwdT`, `ndivR` are NOT required | ✅ `Semantics/BisimFromRel.agda` — postulate-free |
| `drbisim→fsim` (a `DRbisim` is an `FSim` in the SAME orientation: keep `fwd`/`div→`, drop `bwd`, derive `stab` from `div←` + `¬-divergent→normal`); `drbisim→⊑D` / `⊑F⊥` / `⊑FD` rewired as ONE-LINERS through `FSim` — **all names and types preserved, all 58 consumers green** | ✅ `Semantics/DRImpliesFD.agda` |
| postulate-free STABILITY helpers (`stable-not-sil` / `-not-ret` / `-react-τc`, `stable-no-τ`, `stable→¬div`, `stable→τ*-refl`, `nothing≢just`) hoisted OUT of the postulate-bearing bridge and re-exported from it, so postulate-free clients need not import `¬-divergent→normal` | ✅ `Semantics/Stability.agda` — postulate-free (`⟹-then-τ*` similarly moved to `Semantics/Failures.agda`) |
| `Par-fsim` (generalised `Par A merge`) + corollaries `∥-fsim`, `⦀-fsim` | ✅ `CSP/Laws/FSim/ParCong.agda` |
| `Bind-fsim` (`>>=`) + corollaries `bindNoτ-fsim`, `bindκ-fsim` (pure continuation), `>>-fsim` | ✅ `CSP/Laws/FSim/BindCong.agda` |
| `Hide-fsim` (`∖`) | ✅ `CSP/Laws/FSim/HideCong.agda` |
| `Iter-bind-fsim` + corollaries `iter-fsim`, `loop-fsim`, `loop0-fsim`, `loopc-fsim`, `while-fsim` | ✅ `CSP/Laws/FSim/LoopCong.agda` |
| `¬fsim-Pinf-Qh : ¬ (FSim Rt Qh Pinf)` — the FD hiding counterexample pair is provably **not** an `FSim`, so it cannot refute the unconditional `Hide-fsim` | ✅ `CSP/Laws/FSim/HideCounterexample.agda` — postulate-free |
| `fsim-sil-factor` (a `sil`-headed spec's simulation factors through its unique τ-successor — the converse of `fsim-τ*-prepend`) + generic inversions `sil-no-ev`, `sil-τ*-split`, `sil-div-factor` (2026-08-04, added for the αpar congruence's `αdrain`; see §17 addendum) | ✅ `Semantics/FailureSim.agda` — postulate-free |
| `Θ-fsim` (throw, `⟦A▷`) + `Θ-mono-⊑FD` — **two-sided, unconditional, `agda --safe`-clean** (2026-08-04; see §17 addendum for the mechanism and the sweep) | ✅ `CSP/Laws/FSim/ThrowCong.agda` — 0 local postulates |
| worked smoke test: `copy⊑FD-buff1 : COPY ⊑FD BUFFN1` via `FSimFromRel`, reusing `Buffers`' `BRel` / `fwdE` / `fwdT` / `ndivL` verbatim and adding one stability obligation; `orientation-check` pins the direction against `proj₂ copy-is-buff1` | ✅ `CSP/Examples/UCS/Ch6/BuffersFSim.agda` — postulate-free |

**Side conditions — the interesting part, reported honestly:**

- **`Par-fsim` needs `Sep A P₁ Q₁` on the IMPL operand pair ONLY** — HALF of what the
  two-way `≈DR` congruence needs (being two-way, that one needs `Sep` on both operand
  pairs). It is consumed in exactly ONE place: `fwd`'s `evBoth` overlap case, where
  `Par-ev-elim` would otherwise put the impl composite into the inline overlap node
  `(Par P′ Q₁) ⊓ (Par P₁ Q′)`. **`stab` needs no side condition at all.**
- **`Bind-fsim` takes a `BindDivSplit k₁` hypothesis, for `div→` ONLY** (the bind König
  step: an infinite τ-chain of `P >>= k` either stays inside `P` or crosses the
  handover). It is DISCHARGED for τ-less continuation roots (`NoTauRoot` ⇒
  `bind-noτ-split`, giving the side-condition-free `bindNoτ-fsim` and `bindκ-fsim`) and
  for `_>>_` (via `>>-split`, off the pre-existing certified `>>-Diverges→`). It is
  undischarged only when the continuation may itself begin with a τ. `fwd` and `stab`
  need nothing.
- **`Hide-fsim` is UNCONDITIONAL**, and so are **all five loop corollaries**
  (`iter-fsim`, `loop-fsim`, `loop0-fsim`, `loopc-fsim`, `while-fsim` — `iter-div-split`
  discharges the iterate König hypothesis for EVERY continuation and every state type).
  See §6 for why unconditional `Hide-fsim` does not contradict the FALSITY of
  unconditional `Hide-mono-⊑FD`.
- **`□-fsim` (2026-08-03 addendum below) needs NO `Sep`-style side condition at all** —
  unlike `Par-fsim`, which needs half of one. `□` never synchronises, so an offer
  overlap is legal and simply resolves into a real `⊓` (the `evPQ` case), whose
  branches are the ordinary `⊓-stepL`/`⊓-stepR`, not a premise the caller must supply.
  `▷-fsim-R`, by contrast, IS one-sided — not by a side condition but because the
  two-sided form is outright false (`FSim/SlideCounterexample`).
- **`Θ-fsim` (throw, `⟦A▷`, 2026-08-04 addendum) needs NO side condition of any kind** —
  not even the `Sep`-freedom `□-fsim` already didn't need one of — and, uniquely among
  the operand-deconstructing congruences, its `div→` field is fully STRUCTURAL rather
  than resting on a postulated `Diverges→` inversion, which is what lets the whole
  module pass `agda --safe`. See the §17 addendum for the mechanism and a full
  `--safe`-sweep table across the FSim congruence suite (2 of 7 top-level operator
  congruences clean: `IChoiceCong` and `ThrowCong`).
- **Across the whole suite, `fwd` and `stab` are classical-ingredient-free; the only
  classical dependency is ever `div→`** (and even that is empty for `Θ-fsim`).

**Generic-layer housekeeping landed with this work:** `FinBr` was hoisted OUT of the
priority layer into `Semantics/FinBr.agda`, where it belongs — it mentions only
`Process_Trees` + `Semantics.LTS` — and is now generic in the τ-index type `I` exactly
like `Semantics.LTS`. `CSP/Priority/Base.agda` re-exports it at `I = ExtI E`, so the ~22
modules that get `FinBr` from there needed **zero** downstream edits.

**Cost of the one-way route vs. the two-way one** (measured on the real-scale
`Liveness/PipePairFlipBFs` BF-server peer refinement; the FSim re-proof is
`CSP/Examples/Cardano_network/NetworkVerification/Liveness/PipePairFlipBFsFSim.agda`,
which reuses `bfsFwdE` / `bfsFwdT` / `bfsNdivL` verbatim and replaces
`bfsBwdE` / `bfsBwdT` / `bfsNdivR` by one `bfsStab`):

| Metric | Route A (`≈DR`) | Route B (`FSim`) | Δ |
|---|---|---|---|
| backward half → `stabR` | 1590 lines / 1294 clauses | 1168 / 941 | **−27 %** |
| whole proof | 3875 lines | 3458 lines | **−10.8 %** |
| wall clock | 52.69 s | 46.39 s | **−12.0 %** |
| peak RSS | 6.38 GB | 5.82 GB | **−8.8 %** |
| `--profile=modules` self time | 46.9 s | 42.6 s | **−9.2 %** |

⚠ **Two caveats, and they matter.** (i) The two routes do not deliver the same thing:
Route A yields a full `≈DR` (hence `≈FD`, both directions), Route B yields ONE `⊑FD`.
Route B is therefore doing strictly less work, and the table is not a like-for-like
speed-up. (ii) The saving is far BELOW the 41–45 % line share that `bwd` / `div←`
occupy, because `stabR` cannot avoid the alphabet enumeration that makes `bwdE` large in
the first place — the offer-reflection lemmas still case-split over the whole event
alphabet. The structural win (three obligations instead of six, no residual relation and
no τ*-padded weak matching on the backward side) is real; the line-count win is modest.

---

## §16 — Divergence-freedom and stability calculi  ✅ built · ⚠️ payoff LIMITED

Five commits on `semantics/failure-sim`: `732afee` + `33ce925` (the divergence-freedom
calculus) and `e1260da` + `ab8cff3` + `db17141` (the stability consolidation). This
section records **infrastructure**, not new laws — and the honest headline is that the
divergence-freedom half did **not** pay off at the existing proof sites; see *Measured
payoff* below, which also says exactly where it would.

### The modules

| Module | What it holds |
|---|---|
| `Semantics/DivergenceFree.agda` — generic in `E`/`I`, **postulate-free**, `--safe`-clean | ONE home for the three strengths of "does not diverge" (`τ-Acc` ⇒ `¬ Diverges` ⇒ the reachability-closed `DivergenceFree`). **Moved in:** `τ-Acc` / `acc` / `accSub` / `τ-Acc→¬Div` (from `Semantics/TauAcc.agda`) and `DivergenceFree` (from `Semantics/DeadlockDR.agda`, the √-free-reachability definition **unchanged**). **Re-exported, NOT moved:** `stable→¬div` (+ `stable-no-τ`, `stable→τ*-refl`) — owner stays `Semantics/Stability.agda`, which is postulate-free by design — and `deadlock-converges` (+ `div-diverges`, `deadlock-no-τ`) — owner stays `Semantics/DRBisim.agda`, next to the pathology they refute. **New leaf certificates:** `stable→τ-Acc`, `ret→τ-Acc` (+ `ret→no-τ`), `sil→τ-Acc`, `τ-step-transport`, `τ-AccReach` and its bridge `τ-AccReach→DivergenceFree` (+ `divergenceFree→¬Div`) |
| `CSP/Laws/DivFree/Closure.agda` — **postulate-free**, typechecks green | **19** structural `τ-Acc` closures — leaves `Stop`, `deadlock`, `Ret`/`Skip`, `Tau`; prefixes `pchoice`, `⟶`, `⟶₀`, `Output` (`e ! v ⟶ P`); `⊓` and `⨅Fin`; `▷`; `□`; `Par` with `∥⇘⇙` / `⦀` / `⦀Fin`; `>>=` and `>>`. **10** of the 19 carry a `*-no-Diverges` corollary (`Stop`, `Skip`, `pchoice`, `prefix`, `⊓`, `▷`, `□`, `Par`, `>>=`, `>>`) — the shapes `DRFromRel`/`FSimFromRel` actually consume; the other nine are `τ-Acc`-only. Bind needed a τ-inversion the trace laws did not have (`BindτR` / `bind-τ-elim`, derived in the module). Also folds away the two remaining `prefix-no-Diverges` duplicates (`InterruptFD`, `ExtChoiceSlide`) |
| `Semantics/Stability.agda` (extended) | now single-sources the **five** generic `isStable` lemmas: `mk-stable` (intro from an everywhere-`nothing` τ-map), `stable→react` (Σ-form elim), `isStable-force-eq` (forward transport along an equal force), `stable-force-eq` (the same, backward), `react-no-τ→stable` (intro from the LTS side). `mk-stable` alone had **four** identical copies (`ThrowFD`, `InterruptFD`, `ParallelRefusals`, `ExtChoiceFD`) |
| `CSP/Laws/Stability/Closure.agda` — postulate-free, typechecks green, **not `--safe`** | one import for "is this state τ-free?". §1–§8 **re-export** the per-operator lemmas that already existed (nothing re-proved): generic core, leaves (`Stop`, `deadlock`, `deadlock ∖ Z`), the prefix/`pchoice`/menu family, the NEVER-stable operators (`⊓`, `▷`, the `ret`-shaped `□`s), `□`, the parallel group (intro, `ParNormal` elim, `StableClass` classifier, reassociation), hide, and bind/seq/iterate. §9 adds the four gap lemmas below (three of which now live in `Stability/ExtChoice.agda` and are re-exported from here) |
| `CSP/Laws/Stability/ExtChoice.agda` — postulate-free, typechecks green, **not `--safe`** | the `□` half of §9, split out of the survey so it can be imported CHEAPLY: `□-force-nn`, `stable-□`, `□-stable-elim`, moved **verbatim** (nothing re-proved, nothing duplicated — `Closure.agda` re-exports them `public`, so its existing clients are unchanged). Its closure has **one** postulate-bearing module (`ExtChoiceDivergence`, via `ExtChoiceFD`'s `□-Lret-unstable`/`□-Rret-unstable`) against the survey's **ten**. Measured effect on the only client, `CSP/Laws/FSim/ExtChoiceCong.agda`: 67 → 27 modules in closure, 10 → 1 postulate-bearing, and the surviving one holds exactly the two postulates that module actually uses |

### Design findings — the durable part

1. **State the calculus on `τ-Acc`, not on `¬ Diverges`.** The negative form is *not*
   constructively closed under these operators: turning `Diverges (P □ Q)` into
   `Diverges P ⊎ Diverges Q` requires deciding WHICH operand contributes infinitely many
   of the τ's — a König-style classical step. `τ-Acc` is inductive, so every closure is
   plain structural recursion on the operands' certificates, with no classical input,
   and `τ-Acc→¬Div` then delivers exactly what `DRFromRel`'s `ndivL`/`ndivR` and
   `FSimFromRel`'s `ndivL` ask for. **`⊓` is the one operator that also closes in the
   negative form** (its τ-successors are literally the operands), and it is proved both
   ways.
2. **`τ-Acc-▷` is a PREREQUISITE for `τ-Acc-□`**, not an independent nicety:
   `□-τ-elim`'s `sPQ` / `sQP` cases put the composite into genuine slide states, so the
   `□` closure calls the `▷` one. (The `□` recursion is lexicographic: `chQ` keeps the
   left certificate and shrinks the right.)
3. **Divergence-freedom is NOT Agda productivity — same word, different guard.**
   `div = sil div` is perfectly productive *and* maximally divergent. Agda's guardedness
   asks for the corecursive call under **any** constructor; CSP's "guarded recursion"
   asks for the loop-back under a **visible** action. So the productivity checker cannot
   supply the loop hypothesis, and `loop`/`iterate` is deliberately OUT of the closure
   module. Intended shape for a later commit, recorded in its header:
   `Guarded B → τ-Acc B → τ-Acc (loop0 B)`, with `Guarded` ruling out a `ret` reachable
   by τ's alone.
4. **The four gap lemmas** (§9 of `CSP/Laws/Stability/Closure.agda`; the three `□` ones
   were later moved verbatim to `CSP/Laws/Stability/ExtChoice.agda` and are re-exported
   from the survey) — what the survey showed was genuinely missing rather than merely
   scattered:

   | Lemma | Statement | Why it was a gap |
   |---|---|---|
   | `□-force-nn` | force equation for a `react`\|`react` external choice | `ExtChoiceIdem` had only the DIAGONAL `double-force-eq` |
   | `stable-□` | `isStable P → isStable Q → isStable (P □ Q)` | only the diagonal `stable-double : isStable P → isStable (P □ P)` existed |
   | `□-stable-elim` | `isStable (P □ Q) → isStable P × isStable Q` | the converse, completing the iff; all nine force shapes, the eight non-`react`\|`react` ones refuted |
   | `Par-stable?` | `Dec (isStable P) → Dec (isStable Q) → Dec (isStable (Par As merge P Q))` | intro (`Par-stable`/`-termL`/`-termR`) and elim (`Par-stable-normal`) lived in two separate files and had never been packaged as a DECISION; the `ret`/`sil` shapes need no input at all |

5. **Structural blocker on deduplication, verified empirically.** An
   `open … public` re-export of the SAME definition through two applications of a
   parameterised module still yields `[AmbiguousName]` at a client that imports both.
   One canonical name therefore **cannot** be achieved by re-export: every historic name
   must survive as a locally-defined alias, and deduplication can only remove the
   *body*, never the signature. This caps the achievable dedup saving repo-wide, and it
   is why `CSP/Laws/Stability/Closure.agda` carries a usage note telling clients to
   `hiding (…)` on one of the two imports rather than drop the re-export.

### Measured payoff — recorded honestly

⚠️ **The operator closures do NOT pay off against the existing `ndivL`/`ndivR` sites,
and the reason generalises.** Every such site already needs strict **τ-freeness**
(`isStable`) for its `fwdT`/`bwdT` obligation; once you have τ-freeness, `ndiv*` is
`stable→¬div`, a one-liner. `τ-Acc` is strictly WEAKER than τ-freeness, so it cannot
discharge `fwdT`/`bwdT`, and it buys nothing where τ-freeness was needed anyway. The
closures pay only where a composite genuinely HAS τ's whose well-foundedness is
non-trivial — the **hide** and **loop** cases, both currently out of scope. That is also
why the follow-up commits pivoted to gathering STABILITY, which is the load-bearing
notion in this tree.

- **Hide is not redone.** `MAcc A P → ¬ Diverges (P ∖ A)` already exists as
  `Hide-noDiv-from-MAcc` at `CSP/Laws/FD/HideDivergence.agda:78`.
- **Sites.** `CSP/Examples/UCS/Ch6/AbpFT.agda` converted: the hand-rolled
  `par-pTau-nothing` (an 11-line case split over the `ExtI` index shapes) deleted in
  favour of `Par-stable` + `stable-no-τ`; **28 proof lines → 12**, file 460 → 450,
  behaviour unchanged.
- **Deliberately NOT converted, measured:** `Ch6/Buffers.agda` and
  `Ch7/SeqBuffers.agda` — their τ-free states are plain `react … ∅t` leaves, **not**
  operator composites, so the existing `sSil ()` / `sTau refl ()` refutations are already
  minimal; converting would trade 2 lines of proof for an import plus a layer of
  indirection. `Cardano_network/Terminable/NetworkTRefinement.agda` would go 18 → 8 lines
  (`spec0-noτ` / `S1-noτ`, two 8-shape `sTau` case splits) but is a WIP experiment and
  was left untouched.
- **The consolidation itself was roughly a wash on line count** (`e1260da`: +127 / −88).
  Its value is single-sourcing, not brevity.
- **Deduplication NON-findings, worth recording so nobody re-opens them.**
  `stable-react` was **two different lemmas under one name** — an alias of `mk-stable`
  (intro) in `IterateMonoFD`, an alias of `stable→react` (Σ-elim) in `ExtChoiceIdem`.
  The three prefix-stability copies have three DIFFERENT signatures (`prefix-stable` in
  `FDCong`, implicit arguments; `pfx-stable` in `InputDist`, explicit; `prefix₀-stable`
  in `FDLawsPrefixDist`, over `Prefix₀`) and each proof is the single clause
  `_ _ = refl`, so deleting copies would save nothing. Several other apparent duplicates
  take their arguments in the opposite order. All correctly left alone.

### Postulate and `--safe` status

All three new modules (`Semantics/DivergenceFree.agda`, `CSP/Laws/DivFree/Closure.agda`,
`CSP/Laws/Stability/Closure.agda`) are **postulate-free**, with no `NON_TERMINATING` and
no sized types.

- `Semantics/DivergenceFree.agda` passes `agda --safe Semantics/DivergenceFree.agda`
  (exit 0 — the invocation puts the whole dependency cone under `--safe` too). Its own
  pragma says only `--guardedness`, because `--safe` is CO-infective and
  `Process_Trees` / `Semantics.LTS` / `Semantics.DRBisim` do not carry it.
- `CSP/Laws/Stability/Closure.agda` **does not** pass `--safe`, and the failure is
  genuine rather than cosmetic: it gathers from modules above `Semantics/DRImpliesFD`,
  so `agda --safe` stops at `[SafeFlagPostulate] Cannot postulate ¬-divergent→normal`
  (`DRImpliesFD.agda:67`). Under a plain `agda` it typechecks green.
- Incidental repair: `Semantics/TauAcc.agda` did **not** typecheck under a plain `agda`
  before this work — it declared `{-# OPTIONS --safe #-}` while `Process_Trees` does not,
  giving `[CoInfectiveImport]`. The pragma was dropped; the content is still
  `--safe`-clean, and `agda --safe Semantics/TauAcc.agda` still exits 0.

---

## Postulate inventory (`spike/extc-fd-laws`)

### (a) FD-layer postulates — all certified from the single `dne`

**Twelve** postulated names, spread over **eleven** modules. Each is kept small and direct, and
**each is certified derivable from a single classical axiom `dne` (¬¬A→A)** in
`CSP/Laws/ClassicalFromLEM.agda` (a standalone soundness witness, imported by nothing; `dne`
itself lives in `src/Classical.agda` and is the development's only axiom):

| Postulate | Used in | Certified |
|---|---|---|
| `¬-divergent→normal` | `Semantics/DRImpliesFD` | ✅ Derivation 1 |
| `□-Diverges→` | `CSP/Laws/FD/ExtChoiceDivergence` | ✅ Derivation 2 |
| `▷-Diverges→` | `CSP/Laws/FD/ExtChoiceDivergence` | ✅ Derivation 2 (the "▷ analogue", same `DAcc` engine) |
| `△-Diverges→` | `CSP/Laws/FD/InterruptDivergence` | ✅ "Postulate 3" of the certifier — the "△ analogue", certified inside the Derivation-2 block; there is **no banner literally reading "Derivation 3"** in `ClassicalFromLEM.agda` |
| `>>-Diverges→` | `CSP/Laws/FD/SeqDistR` | ✅ Derivation 4 |
| `Par-Diverges→` | `CSP/Laws/FD/ParallelDivergence` | ✅ Derivation 5 |
| `loop-Diverges→` | `CSP/Laws/FD/IterateFD` | ✅ Derivation 6 |
| `offer-LEM` | `CSP/Laws/FD/ParallelRefusals` | ✅ Derivation 7 (plain LEM) |
| `modA-transfer` | `CSP/Laws/Bisim/DRCongruence` | ✅ Derivation 8 (certifier name `modA-transfer-cert`) |
| `¬DivModA→MAcc` | `CSP/Laws/FD/HideDivergence` | ✅ Derivation 9 (headed `Hide-Diverges→` in the certifier; the certified statement is `¬DivModAC→MAccC`, over the certifier's local copies `DivModAC`/`ModAStepC` of DRCongruence's `DivModA`/`ModAStep`) |
| `Diverges-LEM` | `CSP/Laws/FD/FDTransfer` | ✅ Derivation 10 (plain LEM; certifier name `Diverges-LEM-cert`) |
| `αpar-Diverges→` | `CSP/Laws/FD/AlphaParallelDivergence` | ✅ Derivation 11 (certifier name `αpar-no-inf` — a `τ-Acc`/`DAcc` well-founded recursion, strictly simpler than Derivation 2/5's since `αpar` has no both-offer overlap node) |

Caveats on the numbering, so the table can be checked against the file: `ClassicalFromLEM.agda`
lists "Postulate 1 … Postulate 10" in its header but carries banners only for Derivations
1, 2, 4, 5, 6, 7, 8, 9, 10 — Postulate 3 (`△-Diverges→`) and the unnumbered `▷-Diverges→`
are both certified within the Derivation-2 section. Every postulated name above does exist
under that name in its home module, and every certifier derivation does correspond to a live
postulate: there are **no orphaned derivations**.

**Every postulate in the FD layer derives from the one `dne` axiom.** No module uses
`NON_TERMINATING`. The bridge `≈DR ⟹ ≈FD` and `∼ ⟹ ≈DR` lift bisim laws to FD.

### (b) Postulates outside the FD layer

These are **not** part of the `dne`-certified FD family and must not be counted with it.

| Postulate(s) | Module | Status |
|---|---|---|
| `dne` | `src/Classical.agda` | the single classical axiom itself — deliberate, the thing everything in (a) reduces to |
| `⟦G⟧⇒⟦G⟧⁺`, `¬G⇒F¬` | `Semantics/LTL/Traces_Based` | ✅ certified from one `dne` in the **separate** certifier `Semantics/LTL/ClassicalFromLEM.agda` |
| `¬¬F⇒F` | `Semantics/LTL/ClassicalDescent` | ✅ certified in the same LTL certifier (`¬¬F⇒F-fromLEM`) |

**Scope.** This inventory covers the core layers only — `Semantics/`, `CSP/Operators`,
`CSP/Rename`, `CSP/Laws/` and `CSP/Priority/` (plus `src/Classical.agda`); experimental,
work-in-progress and spike modules under `CSP/Examples/` are out of its scope and may carry
postulates of their own, documented in their own module headers.

Within that scope this is the **complete** list:
`grep -rn '^[[:space:]]*postulate' --include='*.agda'` over those layers turns up no other
`postulate` block. In particular `CSP/Priority/Adequacy.agda` is postulate-free (as is the
whole `CSP/Priority/` tree).

### (c) Additions from §15 (`FSim`), 2026-07-31

The `FSim` layer declares **no new postulate**. What it consumes, all of it pre-existing
and `dne`-certified:

| §15 module | Classical input (all in `div→`; `fwd` and `stab` are constructive throughout) |
|---|---|
| `CSP/Laws/FSim/ParCong.agda` (`Par-fsim`) | `Par-Diverges→` (`CSP.Laws.FD.ParallelDivergence`) |
| `CSP/Laws/FSim/BindCong.agda` (`>>-fsim` only) | `>>-Diverges→` (`CSP.Laws.FD.SeqDistR`), via `>>-split`; `Bind-fsim` itself takes the König step as the explicit `BindDivSplit` hypothesis, and `bindNoτ-fsim` / `bindκ-fsim` discharge it constructively |
| `CSP/Laws/FSim/HideCong.agda` (`Hide-fsim`) | `Diverges-LEM` (`CSP.Laws.FD.FDTransfer`) **+** `¬DivModA→MAcc` (`CSP.Laws.FD.HideDivergence`) |
| `CSP/Laws/FSim/LoopCong.agda` (all corollaries, via `iter-div-split`) | the same two: `Diverges-LEM` **+** `¬DivModA→MAcc` |
| `Semantics/DRImpliesFD.agda` (`drbisim→fsim`) | `¬-divergent→normal` — unchanged, and now the SINGLE place the bridge consumes it |

`Semantics/FailureSim.agda`, `Semantics/Stability.agda` and `Semantics/FinBr.agda` are
themselves **postulate-free** (as are `CSP/Laws/FSim/HideCounterexample.agda`,
`CSP/Laws/FD/HideMonoFinBrFail.agda` and both smoke tests). `FailureSim` and
`BisimFromRel` in particular do NOT import `Semantics.DRImpliesFD`, keeping the one-way
route free of `¬-divergent→normal`.

Both classical inputs consumed here, `Diverges-LEM` and `¬DivModA→MAcc`, are rows of table
(a) above (Derivations 10 and 9).

### (d) Additions from §16 (divergence-freedom / stability), 2026-08-01

The §16 layer declares **no new postulate** and consumes **no classical input at all**:
`Semantics/DivergenceFree.agda` and `CSP/Laws/DivFree/Closure.agda` are postulate-free
and `dne`-free (that is the point of stating the calculus on the inductive `τ-Acc` — see
§16, finding 1), and `CSP/Laws/Stability/Closure.agda` adds no postulate of its own. The
one `--safe` caveat is inherited, not new: `Stability/Closure` gathers from modules above
`Semantics/DRImpliesFD`, so it sits under row 1 of table (a), `¬-divergent→normal`.

### (e) Additions from the `αpar` `FSim` congruence, 2026-08-04

The `αpar` congruence work (§17 addendum above) declares exactly **one** NEW postulate,
`αpar-Diverges→` (table (a), Derivation 11), and it is the only classical input the new
modules consume: `Semantics/FailureSim.agda`'s `fsim-sil-factor` (+ its three
inversions), `CSP/Laws/AlphaParallelLift.agda` (925 lines) and
`CSP/Laws/FSim/AlphaParCounterexample.agda` (291 lines) are all postulate-free;
`CSP/Laws/FSim/AlphaParCong.agda` inherits `αpar-Diverges→` through exactly one field,
`div→` (`AlphaParCong.agda:414-416`) — `fwd` and `stab` are fully constructive.

### (f) Additions from the throw (`⟦A▷`) `FSim` congruence, 2026-08-04

The throw congruence work (§17 addendum above) declares **no new postulate** — it is
the first FSim-congruence addition in this campaign that adds a row to the postulate
inventory only to say "none". `CSP/Laws/FSim/ThrowCong.agda` (298 lines) is
postulate-free end to end (`agda --safe` exits 0 on it directly), and so is its hoisted
support, the new "Part 4" of `CSP/Laws/Traces/TraceLawsThrowInterrupt.agda`
(`Θ-τ-lift-P`/`Θ-Diverges-L`/`Θ-div-step`/`Θ-Diverges→`/`Θ-throw-step`/`Θ-pass-step`,
hoisted verbatim from `CSP/Laws/FD/ThrowFD.agda`, which itself keeps re-exporting all
six `public` so its own consumers are unaffected). In particular `Θ-Diverges→` — the
one field (`div→`) where every other operand-deconstructing congruence in this
inventory (§17's `□`/`▷`/`Par`/αpar rows, table (a)'s Derivations 2/5/11) pays a
postulated König step — is STRUCTURAL here, for the reason given in the addendum: the
composite's τ-space is literally the body's τ-space, so the divergence bridge is a
two-line projection, not a search.

### (g) Additions from the replicated folds and derived operators, 2026-08-04

**None.** The seven laws of the §17 "cheap fact-shaped remainder" addendum
(`⨅⁺`/`⨅Fin`/`∥⁺`/`∥Fin`/`＆`/`◁▷`/`Output` `-mono-⊑FD`) declare no postulate and add no
inherited one. The four replicated folds are inductions over binary laws already listed
here, so they inherit exactly those rows (`⊓-mono-⊑FD`: none; `∥-mono-⊑FD`:
`Par-mono-⊑FD`'s three). The new module `CSP/Laws/FD/DerivedMonoFD.agda` is
`--safe`-clean end to end — its whole import closure is `Process_Trees` +
`CSP/Operators` + seven `Semantics/*` modules (as of the 2026-08-04 hoist recorded in (h);
before it, six plus `CSP/Laws/FD/BindFD`, itself postulate-free). Two deliberate choices
keep it that way: `stable-no-τ` is taken from
`Semantics/Stability` rather than from `Semantics/DRImpliesFD` (which re-exports it but
carries `¬-divergent→normal`), and the `Bool` splits cross the missing coinductive η via
the constructive `force-≡→⊑FD` rather than via
`∼ → ≈DR → ≈FD` (which would inject `¬-divergent→normal` through `drbisim→≈FD`, exactly
as table (a) records for every other bridge user).

### (h) Additions from the bind/sequential fact-shaped precongruence, 2026-08-04

**None.** `CSP/Laws/FD/BindMonoFD.agda` declares no postulate. Inherited, per lemma:

* `>>=-mono-⊑FD` / `bindNoτ-mono-⊑FD` / `bindκ-mono-⊑FD` ← **`Diverges-LEM`**
  (`FD/FDTransfer`, table (a)) and nothing else. It is used exactly once, in
  `term-transfer`: `⊑FD` can observe TERMINATION only through the `√` tick (a `ret` state
  is not stable, so it is no failure of its own), and settling the spec's `√`-extended
  empty-ban failure at a τ-normal form is the classical step. The BIND KÖNIG STEP is NOT
  inherited: for the general bind it is the caller's explicit `BindDivSplit k₂`, and for
  the two restricted forms it is discharged constructively (`bind-noτ-split`,
  `pure→NoTauRoot`).
* `>>-mono-⊑FD` and the folds `⨾⋆`/`⨾Fin` ← `Diverges-LEM` **plus `>>-Diverges→`**
  (`FD/SeqDistR`, table (a)) through `>>-split` — precisely the inheritance the FSim
  analogue `>>-fsim` already had. The two folds add nothing of their own.

Also in this campaign: `force-≡→⊑FD` was hoisted from `FD/DerivedMonoFD` into
`Semantics/FailuresDivergences`. It stays postulate-free — the new home's closure is
`Semantics/{LTS,Failures,Refusals,WeakBisim,DRBisim,Stability}` only, in particular NOT
`Semantics/DRImpliesFD` — so `agda --safe CSP/Laws/FD/DerivedMonoFD.agda` still exits 0
and subsection (g)'s `--safe` claim still holds (with `CSP/Laws/FD/BindFD` dropped from
that closure and `Semantics/FailuresDivergences`'s two new imports added to it).

---

## TPC/UCS chapter-1 examples (`Examples/TPC/Ch1/`)

Chapter-1 processes from Roscoe's TPC (`chapter1.csp`) and UCS (`ucs1.csp`) ported to the
process-tree model, with **every in-scope FDR `assert` discharged as an Agda theorem** —
a sanity check of the operator definitions. Holding asserts are proved as `≈DR` (lifted to
`[T=`/`[F=`/`[FD=` via `drbisim→≈FD` and `traces-respects-≈`) or directly as `⊑T`;
intended-to-fail asserts are proved as **negations with an explicit witness trace**. All
processes are operator-native (`loop`/`loop0` + prefix/`□`/`⊓`/`◁▷`); no postulates, no
`NON_TERMINATING`, no `mutual`. Supporting lemma: `Semantics/WeakSim.agda` (one-way weak
simulation `WSim` ⟹ trace inclusion `wsim→⊑T`).

| Module | Processes | FDR asserts discharged | Status |
|---|---|---|---|
| `UpDown` | `P0 P1 P2 Pu`, `COUNT LCOUNT AROUND` | `P1 [T=/[F=/[FD= P2` (via `P1 ≈DR P2`), `P2 [T= Pu`, `Pu [T= P1` (via `P1 ≈DR Pu`), `P1 [T= P0`; `¬(P0 [T= P1)` | ✅ |
| `DayRoutine` | `Day Groundhog_Day`, `Asleep/InBed/Up` (14-event alphabet, `Fin 14`-retract DecEq) | `Groundhog_Day [T= Day`, `InBed [T= Groundhog_Day`; `¬(Day [T= Groundhog_Day)`, `¬(Up [T= Groundhog_Day)` | ✅ |
| `BProcesses` | `B0 B1 BX` | `¬(B0 [T= BX)` (witness `⟨b,a,b,a,b,a,a,b,b,b⟩`) | ✅ |
| `Copy` | `COPY BN Binf` (Bool payload), `Abs1 Abs2` (ℤ payload) | `COPY ≈DR BN 1 []`, `Binf [T= BN N`, `Abs1 [T=/=]T Abs2` (via `Abs1 ≈DR Abs2`) | ✅ |
| `ATM` | `ATM1 ATM2` (value-carrying channels + `⊓`) | `ATM2 [T= ATM1`; `¬(ATM1 [T= ATM2)` (witness ends in `refuse`) | ✅ |

The shared proof machinery is now consolidated: `Semantics.BisimFromRel` provides the
`DRFromRel`/`WSimFromRel` coinduction principles (relation → `≈DR`/`WSim`), and
`CSP.Laws.Traces.PrefixInversion` provides the prefix/loop firing-and-inversion lemmas, the
`TEmpty`/`□-mt-empty` nested-`□` stability chain, and the `sil` helpers. `PrefixInversion`
is imported by all five example modules; `BisimFromRel` by the four that prove a
bisimulation/simulation (`UpDown`, `DayRoutine`, `Copy`, `ATM`) — `BProcesses` proves only
the negative refinement `¬(B0 [T= BX)` and needs neither principle. `COUNT [T= LCOUNT` (no
FDR assert in the source) deferred.

---

## TPC/UCS chapter-2 examples (`Examples/TPC/Ch2/`)

Chapter-2 parallel-operator processes from TPC (`chapter2.csp`) and UCS, with the in-scope
FDR `[T=` asserts discharged as `⊑T` theorems in **both directions** — exercising
interleaving `_⦀_` and interface parallel `_∥⇘_⇙_` (alphabetised `[A‖B]` is modelled as
interface parallel on the shared alphabet). All refinements are proved directly at the
trace level via the parallel trace laws of `CSP.Laws.Traces.TraceLawsParallelTrace`
(`Par-trace-elim` / `Par-trace-intro` and the `ParInter` interleaving relation with
`psync`/`psoloL`/`psoloR`/`p√`). No postulates, no `NON_TERMINATING`, no `mutual`.
Deadlock-freedom asserts, the infinite-state examples, dining philosophers, and `ucs2`
are out of scope.

| Module | Parallel operator | FDR asserts discharged | Status |
|---|---|---|---|
| `Interleaving` | `_⦀_` (N interleaved up/down loops `L'(N) = ⦀ⁿ L1`, vs the bounded counter `LCOUNT`) | `LCOUNT N 0 ⊑T L'(N)` **and** `L'(N) ⊑T LCOUNT N 0` for all `N` (`count⊑interleave-safe` / `interleave⊑count`); book corollaries `L'9⊑count9 : nCopies 9 ⊑T LCOUNT 9 0`, `count10⊑L10 : LCOUNT 10 0 ⊑T nCopies 10` | ✅ |
| `ATMParallel` | `_∥⇘_⇙_` over all events (value-passing) | `SeqATMC c1 ⊑T ATM1andCUST1 c1` (`seq⊑par1`) and reverse (`par⊑seq1`) — card 1 | ✅ |
| `Horse` | `_∥⇘_⇙_` on `{forward, backward}` (pantomime horse) | `RUNnw ⊑T Horse` (`run⊑horse`) and `Horse ⊑T RUNnw` (`horse⊑run`) | ✅ |
| `ChainedBuffers` | `_∥⇘_⇙_` on `{bb}` (chained `COPY` buffers) | `CC0 ⊑T CC0'` (`cc0⊑cc0'`) and `CC0' ⊑T CC0` (`cc0'⊑cc0`) | ✅ |

---

## TPC/UCS chapter-3 examples (`Examples/TPC/Ch3/`)

Chapter-3 processes from TPC — hiding, renaming, and the semantic models — verified at the
**failures–divergences** level (`≈FD`/`⊑FD`), most via the `≈DR → ≈FD` bridge
(`drbisim→≈FD`); the bridge's single certified postulate is inherited transitively (the
example modules themselves are postulate-free). New supporting module:
`Semantics/Determinism.agda` (the `Deterministic` predicate). No `NON_TERMINATING`, no
`mutual`.

| Module | Operator / topic | FDR asserts discharged | Status |
|---|---|---|---|
| `HidingBuffer` | hiding `∖` | `HCHAIN N ≈FD BN N` for **all** `N` (`hchain≈FD-buffer` — hidden N-cell interface-parallel `COPY` chain ≈FD the N-place buffer), via a `Vec`-configuration `≈DR` plus a strictly-decreasing τ-measure for divergence-freedom; `N = 5` corollary `hchain5≈FD-buffer5`. (ATM refinement out of scope.) | ✅ |
| `Renaming` | renaming `⟦ ⟧` | injective: `renameInv COPY inv ≈FD COPY'` (`copyRen≈FD-copy'`); non-injective: `RenSPLIT ≈FD SPLIT'` (`renSplit≈FD-split'` — deterministic → nondeterministic, the fan-in becoming `⊓`); plus `Deterministic SPLIT` (`split-det`) and `¬ Deterministic SPLIT'` (`split'-nondet`) via `Semantics.Determinism` | ✅ |
| `FailuresDivergences` | semantic models (`𝒩`) | stable-failures refinements `Q3 ⊑F⊥ Q2`, `Q2 ⊑F⊥ Q1` (div-free, so `⊑F⊥` = `⊑F` here); `DIV ≈FD div` (hiding an unguarded recursion = livelock); `Q3 ⊓ DIV ≈FD DIV` (`⊓` FD-strictness); Q4 quartet: `Q2 ⊑F Q4` / `¬(Q4 ⊑F Q2)` (stable failures), `¬(Q2 ⊑FD Q4)` / `Q4 ⊑FD Q2` (FD), plus the divergence-strict flip `¬(Q2 ⊑F⊥ Q4)` / `Q4 ⊑F⊥ Q2` | ✅ |

**Caveat (which "failures" is FDR's `[F=`):** FDR's `[F=` is the *stable-failures* model =
the repo's `_⊑F_`; the divergence-strict `_⊑F⊥_` (failures-with-chaos, the failures
component of FD) *flips* on divergent processes (Q4) — hence the Q4 F-pair uses `_⊑F_`,
while for the divergence-free Q1–Q3 the `_⊑F⊥_` statements coincide with `_⊑F_`. Also,
the repo's `_⊑F_` is failures-only (omits the trace conjunct of the full FDR SF model),
but for these examples the trace sets coincide, so the verdicts match FDR.

---

## UCS chapter-2 examples (`Examples/UCS/Ch2/`)

First module of the book-pure UCS track (UCS's numbering; ch1 is already covered
by the combined `Examples/TPC/Ch1`). Source: `fdr-examples/ucs/chapter02/ucs2.csp`.

- `Collatz` — the Collatz `(3n+1)/2` recursion as a productive silent recursion
  (`P n = Tau (P (next n))`, `P 1 = a→P 1`). Proves `P(45) [T= a→STOP` as a finite
  12-step τ-chain halting witness (`p45-refines-aStop`), and the reduced-domain
  `Bd [T= d?n:{2,3,4,5}→Pd(n)` (`bd-refines-rest`) via a weak simulation of the
  feeder inside the `RUN`-buffer `Bd` (`WSimFromRel` + `wsim→⊑T`). The book's full
  `{2..100}` does **not** port: the trajectory from n=27 exceeds NN=4000 (peaks at
  4616), so `Pd(27)` would emit `b` (which `Bd` never offers), falsifying the
  refinement — documented in-module; the retained starts `{2,3,4,5}` keep the whole
  reachable set at `{1,2,3,4,5,8}`, well under the bound. No `postulate`, no
  `NON_TERMINATING`, no `mutual` (`Pd`/`Aω` hand-inline their `react` nodes for
  guardedness).

---

## UCS chapter-3 examples (`Examples/UCS/Ch3/`)

Synchronisation-and-deadlock examples from UCS ch3 (`ucs3.csp`), at the trace +
deadlock level — fully constructive, inheriting NO postulate (unlike the FD
chapters). Excluded: ncopy (buffer chain, covered by TPC), phils (in
Examples/DiningPhilosophers), robots (infinite-state, no asserts).

- `SyncIdentity` — `AS =T (a→REPEAT)[|Events|]REPEAT` (full synchronisation
  collapses the loop to infinite a's); both `[T=` directions proved by weak
  simulation (`as⊑aRR`, `aRR⊑as`). Events reduced to {a,b,c}.
- `PeterMaggie` — full-synchronisation `Peter[|Events|]Maggie` has a genuine
  deadlock: `peterMaggie-deadlocks : HasDeadlock (…)` (stuck after
  ⟨getup,breakfast⟩ — Peter must jog, Maggie must swim, neither shared under
  full sync), hence `¬pm-deadlockFree`. The source-faithful Peter/Maggie use an
  external choice `□` and a looping `Up`. A finite `Up→Skip` variant
  `PeterDF`/`MaggieDF` (keeping the `□`) carries the deadlock-vs-deadlock-free
  CONTRAST proved on ONE family: `peterMaggieDF-deadlocks` (full-sync, still
  deadlocks) and `pm-deadlockFree : DeadlockFree (PeterDF ⟦AP∥AM⟧ MaggieDF)`
  (alphabetised parallel — AP = ∖{swim}, AM = ∖{jog} — is deadlock-free, via
  `progress⇒deadlockFree` over a finite 9-state reachability DAG). Illustrates
  why alphabetised parallel avoids the full-sync deadlock.
- `Bargaining` — Customer/Merchant haggling with real price functions
  (`pval x = (7x+1)%8`, `mval x = (5x+3)%7`) and a stock-DEPLETING merchant
  (`Merchant(diff(X,{x}))`, faithful to the source), reduced to Item = {1,2},
  stock {1,2,3,4}, money 30. `bargaining-deadlocks : HasDeadlock (…)` +
  `¬barg-deadlockFree`: the customer's internal choice of item 1 stucks at the
  empty trace (pval 1 = 0 < mval 1 = 1, no price agreement; item 1 in stock, so
  no outofstock). Trace specs on this reduced model: `buy-spec : Buy 2 ⊑T sys`
  holds (only item 2 is tradeable and depletes after one buy, so ≤1 buy), while
  `NEvs(10) [T= sys` is FALSE — proved as `nevs-fails : ¬ (NEvs 10 ⊑T sys)`
  (after item 2 depletes, outofstock.2 synchronises forever ⇒ unbounded traces),
  matching the source assert's failure. No postulate/NON_TERMINATING/mutual.

_Last updated 2026-07-06._

---

## UCS chapter-4 examples — routing networks (`Examples/UCS/Ch4/`)

First UCS-ch4 subsystem (case studies): §4.2 ring routing, trace + deadlock
level, fully constructive (no inherited postulate). Later routing sub-specs:
trees, general networks, token ring, divergence-freedom, the TBuff buffer
refinement. Other ch4 subsystems (ABP/SWP protocols, sudoku) are separate specs.

- `RoutingRingNaive` (N=4) — the naive one-packet store-and-forward ring
  (`dring`) DEADLOCKS: `naiveRing-deadlocks : HasDeadlock naiveRing` (reachable
  full-ring jam — every node holds a remote-destined packet and waits to forward
  to a neighbour that is itself waiting), hence `¬naiveRing-deadlockFree`. The
  FDR `Ring :[deadlock free]` assert fails; this is its proved negation. Modelled
  with a value-generalised forward offer — sound for this existential
  (`HasDeadlock`) claim (an over-approximation still yields a genuine jam; the
  block is receiver-side, refusing the forward at every packet value).
- `RoutingRingNonBlocking` (N=2, spec-sanctioned reduction) — the non-blocking
  two-packet-buffer ring (`nonblock`) is deadlock-free:
  `nonBlockingRing-deadlockFree : DeadlockFree nonBlockingRing` via
  `progress⇒deadlockFree` over a joint reachability invariant `RSys` (8 configs,
  occupancy ≤ 2N−1 = 3 = the source's `capacity`; the deadlocking full-full
  config is unreachable). Forwards are PINNED to the held packet (required for
  soundness of this universal claim). N=4 packet-pinned enumeration is
  intractable, so N is reduced to 2 (the contrast holds for any N≥2). Proved on
  the composed (unhidden) ring; hiding of `ring` + divergence-freedom deferred.
- `RoutingTreeNaive` (N=5, full source tree) — the naive tree (`tree1`)
  DEADLOCKS via STRONG CONFLICT: `naiveTree-deadlocks : HasDeadlock naiveTree`
  (a tree has no cycles, so a global stuck state needs every node blocked — all
  five nodes are filled: one adjacent strong-conflict pair (nodes 0,1) plus
  every other node passing into a full neighbour), hence
  `¬naiveTree-deadlockFree`. Value-generalised forward (sound for this
  existential claim; the block is receiver-side).
- `RoutingTreeSwap` (N=2, 2-node edge — sanctioned reduction) — the swap tree
  (`tree2`) is deadlock-free: `swapTree-deadlockFree : DeadlockFree swapTree`
  via `progress⇒deadlockFree` + a reachability invariant (indexed by data tags
  decoded to processes via `⟦_⟧`, to avoid a non-injective-defined-term
  unification wall). The `swap` exchange breaks strong conflict — the config
  that deadlocks in the naive tree is un-stuck here by a `swap` between the
  adjacent nodes. Forwards PINNED to the held packet (required for the universal
  claim). N=5 swap enumeration is intractable (the swap handshake is harder than
  the non-blocking ring, which only reached N=2), so N is reduced to 2. Proved
  on the composed (unhidden) tree; hiding + `tree3` negotiation/livelock deferred.
- `GeneralNetworkLivelock` (minimal 3-cycle) — the FIRST livelock in the port,
  porting UCS `general4a`'s FAILING `HNetwork :[divergence free]` assert: a
  `pass`-forwarding network with a cyclic `next` circulates a packet forever;
  hiding the internal `pass` channel turns each hop into a τ, so
  `generalNet-livelocks : Σ s t′. (HNetwork ⟹∖√⟨s⟩ t′ × Diverges t′)` and hence
  `¬generalNet-divergenceFree : ¬ DivergenceFree HNetwork`. The `Diverges`
  witness is a productive 3-state τ-loop (each hidden `pass` hand-off becomes a
  τ, the ch3 `DIV = (a→AS)∖{a}` mechanism at network scale). Isolates the
  message-circulation core (the full general4a node's swap/negotiation is
  deadlock-freedom machinery orthogonal to the livelock); existential witness.
  general4's deadlock-freedom/divergence-freedom deferred.
- `General4DivFree` (minimal cyclic triangle) — general4's HOLDING
  `HNetwork :[divergence free]`: `general4-divergenceFree : DivergenceFree
  HNetwork`, via the Cardano acyclic-τ-DAG `¬Diverges` technique (well-founded
  recursion on a measure = number of nodes holding an undelivered packet; every
  hidden `pass` is a single-hop delivery that strictly decreases it). The
  careful, delivering `next` never circulates — the divergence-free counterpart
  to the general4a livelock (same shape, good `next`). Pinned offers (sound for
  the universal claim). Proved on the good-routing pass core (sanctioned
  reduction); the full swap+negotiation general4 node is also defined and
  exported. general4's `Network :[deadlock free]` is DEFERRED — the full
  swap+negotiation node over the cyclic triangle is a ~2500–3500-line config
  enumeration (no faithful topology reduction exists below the triangle: the
  swap strong-conflict pair and the yes/no negotiation need distinct edges), a
  proof-volume wall (not a soundness/feasibility issue) left as its own future
  effort.
- `TokenRing` (N=2, 1 token) — tokring's FAILING `RingH :[divergence free]`:
  empty tokens circulate forever with no message in flight, so hiding `{|ring|}`
  gives a livelock — `tokenRing-livelocks : Σ s t′. (RingH ⟹∖√⟨s⟩ t′ ×
  Diverges t′)` (at the INITIAL empty state, `s = []`) and
  `¬tokenRing-divergenceFree`. A DIFFERENT divergence source from general4a's
  message circulation — here the token infrastructure itself circles. Productive
  2-state `Diverges` under hiding (the `GeneralNetworkLivelock` mechanism). Pinned
  offers; `NodeR` send restricted to non-self destinations (source fidelity).
- `TokenRingDeadlockFree` (N=2, 1 token) — tokring's HOLDING `Ring :[deadlock
  free]`: `tokenRing-deadlockFree : DeadlockFree Ring` via `progress⇒deadlockFree`
  + a reachability invariant (4 config classes indexed by the real node
  processes) — the single circulating token means the token-holder can always
  act (send / pass / deliver / forward) and the token never duplicates or
  vanishes, so no reachable config is stuck. Pinned offers; unhidden `Ring`.
  Reduced from source N=4/tokens=2. `TBuff` refinement deferred.
- `RoutingRingNonBlockingDivFree` (N=2) — nonblock's HOLDING `RingH :[divergence
  free]`: the non-blocking ring with its internal `ring` channel hidden is
  divergence-free — `nonBlockingRing-divergenceFree : DivergenceFree RingH`
  (`RingH = nonBlockingRing ∖ ringES`), via the Cardano acyclic-τ-DAG `¬Diverges`
  technique (well-founded measure = total remaining forward-hops of in-flight
  packets; every hidden `ring`-forward strictly decreases it, delivery is a
  visible `receive`). Unlike tokring (empty tokens circulate) and general4a
  (messages circulate), the non-blocking ring has NO internal circulation —
  forwards make progress. Reuses the committed N=2 non-blocking-ring model
  (imported, pinned offers). No postulate in the transitive closure.
- `NonBlockingRingTBuff` (N=2, T=Bool, capacity 2N-1=3) — nonblock's
  `TBuff(<>) [T= RingH∖diff(…)`: the non-blocking ring observed only on its
  N1→N2 (0→1) port trace-refines a bounded in-order FIFO —
  `nonblock-TBuff : TBuff [] ⊑T RingObs` (`RingObs = Ring ∖ obsES`, hiding
  `{ring}` + all non-0→1 send/receive), via `wsim→⊑T` + a contents-`List Bool`
  weak simulation (observed send appends; observed receive delivers the oldest;
  internal `ring` hops and the hidden reverse flow are τ). Data-flow correctness
  (bounded, in-order delivery) at full T=Bool. Bool-payload PINNED model
  (re-derived; the committed T=⊤ model carries no payload).
- `TokenRingTBuff` (N=2, 1 token, T=Bool, capacity = tokens = 2) — tokring's
  analogous `TBuff(<>) [T= RingH∖diff(…)`: `tokring-TBuff : TBuff [] ⊑T
  TokRingObs`, same weak-simulation technique but with a reachability-restricted
  6-shape relation (an all-pairs over-approximation would be unsound — the
  single-token invariant makes two-token configs unreachable). The empty-token
  circulation is hidden τ. Full T=Bool, PINNED.
- `RoutingTreeNegotiation` (N=2) — tree3's FAILING `Tree∖diff(Events,{send,
  receive}) :[divergence free]`: two adjacent busy nodes exchange `no` forever
  (never delivering), so hiding the internal negotiation (`pass`/`yes`/`no`)
  gives a livelock — `tree3-livelocks : Σ s t′. (TreeH ⟹∖√⟨s⟩ t′ × Diverges t′)`
  and `¬tree3-divergenceFree`. A THIRD distinct livelock source (negotiation
  stalemate) after tokring's empty tokens and general4a's message circulation.
  Productive 1-state `no`-self-loop `Diverges` under hiding. (`yes`/`no` events
  named `yesc`/`noc` to avoid the `Dec`-constructor clash.)
- `RoutingTreeNegotiationDeadlockFree` (N=2) — tree3's HOLDING `Tree :[deadlock
  free]`: `tree3-deadlockFree : DeadlockFree Tree` via `progress⇒deadlockFree` +
  a data-tag reachability invariant (6 config classes, refl-bridged to the real
  `∥ₐ⁺` composite). A node can always act — the both-busy config's move is the
  very `no.0.1` self-loop that diverges when hidden, so the tree is DEADLOCK-FREE
  THOUGH NOT DIVERGENCE-FREE (the source's "deadlock free but may make no
  progress"). Pinned offers; unhidden `Tree`. Completes the tree trilogy (tree1
  deadlock / tree2 deadlock-free / tree3 deadlock-free + livelock).
- `ABP` — the ALTERNATING BIT PROTOCOL (`abp.csp`), reduced model `DATA = TAG =
  Bool`, bounded-loss channels `BE` at `L = 2`, divergence-free receiver `REC2`.
  Sender `SEND`/`SND`, receiver `REC2`/`RCV2`, channels `BE`/`BE′`,
  `SystemBE2 = SND ⟦{a,d}∥…⟧ ((BE ⦀ BE′) ⟦…∥{b,c}⟧ RCV2)`, `SysH = SystemBE2 ∖
  {a,b,c,d}`, spec `COPY`. Reachable-config datatype `Cfg` + decode `⟦_⟧` + refl
  bridge `SystemBE2 ≡ ⟦ cfg₀ ⟧`. Model COMPLETE, faithful, PINNED, postulate-free.
- `ABPRefinement` — the headline assert `COPY [FD= SysH` is **DEFERRED**. Both
  routes stall at the SAME wall: the hidden system has **594 reachable
  configurations** (≈150 phase/value symmetry classes, 1452 three-layer nested-`Par`
  step-inversion obligations — ~25× the largest completed template
  `TokenRingTBuff`), an intractable-by-hand reachability closure. The FD route
  (`≈DR → ≈FD`) needs it for the bisimulation; the sanctioned trace-safety fallback
  `Spec [T= SystemBE2` (`Spec = COPY ||| CHAOS({a,b,c,d})`, unhidden, `a`/`b`/`c`/`d`
  CHAOS-absorbed) needs the identical closure for its weak simulation. An exhaustive
  external BFS of the exact Agda semantics CONFIRMS the refinement is TRUE (0
  buffer-discipline violations), so this is a proof-scale wall, not a soundness gap.
  The committed module lands the verified FOUNDATION — the inlined `Spec` (PINNED
  `right!x`) + its 12 forward-step lemmas — hole-free, warning-free, postulate-free;
  the `RR` relation + `fwdE`/`fwdT` closure are documented-deferred (as with the
  general4 deadlock-free volume wall). A future attempt would need machine-assisted
  reachability enumeration.
- `SlidingWindow` — the SLIDING WINDOW PROTOCOL (`swp.csp`), reduced `W = 2`,
  `SEQ = Fin 3`, `DATA = Bool`, bounded-loss channels `BE`/`BE′` at `L = 2`.
  Window-2 sender `SEND`/`SND` (constructor window `w0`/`w1`/`w2`, PINNED
  (re)transmit + cumulative ack-slide), receiver `REC`/`RCV` (in-order by
  expected seq, PINNED `right`/`c`), `SystemW = SND ⟦{a,d}∥…⟧ ((BE ⦀ BE′)
  ⟦…∥{b,c}⟧ RCV)`, `SWPH = SystemW ∖ {a,b,c,d}`, spec `COPY`. Two EXISTENTIAL
  pipelining witnesses, postulate-free: `swp-delivers2 : traces SWPH
  [left·true, left·false, right·true, right·false]` (accepts TWO messages before
  delivering either, then delivers both IN ORDER — the sliding window's defining
  feature) and `swp-beats-copy : ¬ (COPY ⊑T SWPH)` (SWP is strictly more than a
  one-place buffer — `[left, left] ∈ traces SWPH ∖ traces COPY`). Built as single
  finite forward `⟹` derivations (`Par-sync`/`Par-soloL/R`/`Par-τ-L/R` +
  `Hide-keep`/`Hide-hidden`/`Hide-τ`) — no reachability closure, so the >594-state
  ABP-refinement wall never arises. The full buffer refinement `BUFF W [FD= SWPH`
  is documented-DEFERRED (ABP-style). Second protocols sub-spec after ABP.
- `Sudoku` — the SUDOKU constraint network (`sudoku.csp`), reduced to 4×4 shidoku
  (rows, columns, 2×2 boxes; values `Fin 4`). Modelled as a single FUSED-CONSTRAINT
  board process `Board : Grid → SProc` (`Grid = List (Fin 4 × Fin 4 × Fin 4)`) whose
  `sel.r.c.v` offer is guarded by the conjunction of the row/column/box all-different
  constraints — the PRODUCT of the region-constraint processes, trace-equivalent to
  their literal `∥`. Two EXISTENTIAL witnesses, postulate-free: `sudoku-solvable`
  (the empty board reaches a full valid grid via a 16-`sel` forward `⟹` trace — the
  CSP network solving a sudoku from scratch, validity guaranteed by construction) and
  `sudoku-deadlocks : HasDeadlock BadPuzzle` (an over-constrained board — cell (3,3)'s
  row holds {1,2,3} and its column a 0, so no value is legal there — is immediately
  `IsStuck`). The literal 12-fold parallel constraint network, and universal
  deadlock-freedom / unique-solution / full-unsolvability, are documented-DEFERRED.
  Last (sudoku) subsystem of UCS ch4.

---

## UCS chapter-5 examples — hiding / renaming / link parallel (`Examples/UCS/Ch5/`)

First UCS-ch5 subsystem: the `ncopyh.csp` hidden-chain COPY-buffer refinement,
trace level, postulate-free. Later ch5 sub-specs (renaming, apples/link
parallel) are separate specs.

- `NCopy` — `ncopyh.csp`: a chain of two `COPY` cells over channels `c.0/c.1/c.2`
  (`Bool`), alphabetised-parallel synchronising on the shared `c.1` which is
  HIDDEN (`CCH = (COPY₀ ⟦∥⟧ COPY₁) ∖ {c.1}`), is a 2-PLACE BUFFER. Trace
  equivalence `Spec =T CCH` proved both directions: `ncopy-safe : Spec ⊑T CCH`
  (the chain is a safe buffer) and `ncopy-live : CCH ⊑T Spec` (it realises every
  buffer trace), each via `wsim→⊑T` + `WSimFromRel` over a shared buffer-contents
  relation (4 reachable cell-pair configs; the hidden `c.1` handoff is a τ that
  preserves contents). Reuses the ch4 `TBuff` weak-simulation technique, run in
  BOTH directions. Postulate-free. Reduced `N = 2`, `T = Bool`; the `[FD=`
  refinements (ch6) and the `ncopyl` link-parallel variant are deferred. First of
  the UCS-ch5 sub-specs (ncopy / renaming / apples).

- `Renaming` — `renaming.csp`: (§A) the INJECTIVE renaming of `COPY` is a pure
  relabelling — `RenCOPY = renameInv COPY inv` (left↦aa, right↦bb) with
  `rename-safe : COPY' ⊑T RenCOPY` and `rename-live : RenCOPY ⊑T COPY'` (together
  `RenCOPY =T COPY'`), via two weak simulations (`wsim→⊑T` + `WSimFromRel`) over the
  2-state ready/holding relation (no τ introduced). (§B) the DETERMINISM contrast:
  `split'-nondet : ¬ Deterministic SPLIT'` (the internal choice `⊓` after `inp'`
  refuses `out2'` in a stable state while `[inp',out2']` is a trace — a `failures`
  witness) and `split-det : Deterministic SPLIT` PROVED IN FULL (SPLIT is τ-free
  with functional offers, so its reached state is unique and cannot refuse an
  offered event — proved via a reached-state determinacy lemma). Postulate-free,
  `T = Bool`. DEFERRED non-goals: the non-injective `RenSPLIT =T SPLIT'` (general
  fan-in rename trace laws unbuilt) and the `[FD=` asserts (ch6). Second of the
  UCS-ch5 sub-specs (ncopy done; apples remains).

- `Apples` — `apples.csp`: many-way, CONTEXT-DEPENDENT renaming (`apple` renamed to
  BOTH `braeburn` and `cox`, a regulator `Reg` picking which by whether `adam`/`eve`
  happened last; `braeburn` before `eve`, `cox` after). `RelP` modelled DIRECTLY as
  its regulated observable behaviour (phased `braeburn`+`adam` → `eve` → `cox`) —
  trace-faithful to `P[[apple<-cox/braeburn]] [|…|] Reg`, the literal fan-out-rename
  + parallel deferred (general relational rename trace laws unbuilt). The `Before(A,B)`
  ordering contrast, postulate-free: `apples-holds : Before({braeburn},{cox}) ⊑T RelP`
  (HOLDS — all `braeburn` precede all `cox`, via `wsim→⊑T` + `WSimFromRel` over a
  4-class relation) and `apples-fails : ¬ (Before({cox},{braeburn}) ⊑T RelP)` (FAILS —
  the `RelP` trace `[braeburn,adam,eve,cox]` has `cox` after `braeburn`, refuted by a
  `BeforeCB` trace-inversion). All events valueless; `apple` renamed away. Completes
  the UCS-ch5 group (ncopy / renaming / apples).

## UCS chapter-6 examples — failures & divergences (`Examples/UCS/Ch6/`)

- `faildiv` (UCS §6.1, `faildiv.csp`) — **already covered** by
  `CSP.Examples.TPC.Ch3.FailuresDivergences` (TPC §3.3 `section3-3.csp` uses the
  identical `Q1`–`Q4`/`DIV` processes UCS §6.1 reuses). That module proves,
  postulate-free, the F-refinement chain `Q3 ⊑F⊥ Q2 ⊑F⊥ Q1`, `DIV ≈FD div`, the
  ⊓-strictness `Q3 ⊓ DIV ≈FD DIV`, and the full F-vs-FD reversal quartet on `Q4`
  (`Q2 ⊑F Q4`, `¬(Q4 ⊑F Q2)`, `¬(Q2 ⊑FD Q4)`, `Q4 ⊑FD Q2`) plus the `⊑F⊥` flip.
  No separate `UCS/Ch6/FailDiv.agda` (pointer, not a re-port — cf.
  phils→DiningPhilosophers).
- `Buffers` (UCS ch6, `buffers.csp`) — the FD buffer hierarchy, reduced `T = Bool`,
  `N ∈ {1,2}`. Most-nondeterministic bounded buffer `BUFN : ℕ → List Bool → BProc`
  (the `right!head □ (#s<N & STOP ⊓ left?x)` nondeterminism as a FUSED sliding node:
  visible `right` + τ-branches to a deadlock-on-accept `Bstop` and an accept
  `Baccept`), and `COPY`. `copy-is-buff1 : BUFFN1 ≈FD COPY` (COPY is the one-place
  buffer — `BUFN 1` has no room to nondeterminise); proved via the `drbisim→≈FD`
  bridge, so it inherits the certified `¬-divergent→normal` (not postulate-free).
  `¬buff1⊑buff2 : ¬ (BUFFN1 ⊑FD BUFFN2)` (buffer size is FD-observable — `BUFFN2`
  traces `[left,left]`, holding two, which `BUFFN1` cannot). `buff2⊑buff1 : BUFFN2
  ⊑FD BUFFN1` — the universal size hierarchy, PROVED IN FULL (a smaller buffer
  refines a bigger, matching `BUFFN1`'s refuse-`left` refusal via `BUFFN2`'s `STOP`
  branch; direct trace-simulation). Both `¬buff1⊑buff2` and `buff2⊑buff1` are
  direct `failures⊥`/`divergences` reasoning, postulate-free and bridge-free (no
  `drbisim`/FD bridge). Deferred non-goals: `WBUFF` (weak buffer + `DIV`), chaining
  (link-parallel), `N>2`. First genuinely-new ch6 sub-spec (faildiv covered by
  TPC/Ch3/FailuresDivergences).
- `AbpFT` (UCS ch6 §6.5, `abp-ft.csp`) — fault tolerance via LAZY ABSTRACTION,
  single-channel level, `T = Bool`. Controlled-error channel `CE` (may `lose` an
  input / `dup`licate an output, 4 states `CE`/`CEmid`/`CE'`/`CEdup`), reliable
  `COPY`, lossy/dup medium `C`, and the built `CHAOSE` (= `CHAOS({lose,dup}) =
  STOP ⊓ (lose □ dup)`) + `LAbsE P = (Par⊤ Errors P CHAOSE) ∖ Errors` (=
  `LAbs(Errors)`; `normal` omitted). `copy-ce-reliable : COPY ⊑FD (Par⊤ Errors CE
  STOP)` (errors DISABLED by `STOP` ⇒ the error channel is a reliable one-place
  buffer — the fault-tolerance baseline); proved via the `drbisim→⊑FD` bridge, so
  it inherits the certified `¬-divergent→normal` (not postulate-free). The
  lazy-abstraction equivalence `C ≈F LAbsE CE` DEFERRED (genuine wall — not a
  forward simulation + unbuilt general Par-∖ failures de-interleaving; the
  `LAbsE CE` step/τ characterisation lemmas landed, postulate-free/hole-free).
  DEFERRED non-goals: the full `SYSTEME`/`SYSTEMA` refinements (`COPY [F=
  SYSTEMA`, `NoError [F= SYSTEMA` — the plain-ABP 594-state closure wall +
  abstraction); `normal` compression; larger `DATA`/`TAG`. Second ch6 sub-spec
  (buffers done).
- `CommSec` (UCS ch6 §6.5, `commsec.csp`) — INFORMATION-FLOW SECURITY via
  noninterference (security = determinism of the High-abstracted system), `data =
  Bool`, Low channel `lois→leah` observed, High abstracted. Each system's
  abstracted Low view modelled DIRECTLY (the observable behaviour of
  `LAbs(H)(System_i)`; literal composites deferred). `commsec-insecure : ¬
  Deterministic LowView1` (System1's naive shared medium LEAKS — hidden High
  occupies the medium, so `sendL` is both accepted and refused after the empty Low
  trace; a root `⊓` of accept vs `Stop`; the `split'-nondet` technique).
  `commsec-secure : Deterministic LowView2` (System2's Low-prioritising medium is
  SECURE — the Low view is a τ-free functional 1-place buffer, so its reached
  state is unique and cannot refuse an offered event; the `split-det`
  reached-state-determinacy technique). Postulate-free (failures-determinism, no
  bridge). Reuses the `renaming` determinism contrast (`SPLIT'`/`SPLIT`). DEFERRED
  non-goals: the literal `LAbs(H)(System1–4)` composites (`∥`+`∖{in,out}`+`CHAOS`);
  Systems 3 & 4; the `BN` buffer refinements + High-view checks; the `[FD]`
  determinism variants. Third and last ch6 sub-spec.

## UCS chapter-7 examples — termination & sequential composition (`Examples/UCS/Ch7/`)

- `Termination` + `SeqBuffers` + `Counter` (UCS ch7 §7.1, `section7-1.csp`) —
  TERMINATION & SEQUENTIAL COMPOSITION. **Termination semantics:** `te-≈FD : TE
  ≈FD TE′` for `TE = (up ⟶₀ Stop) □ Skip`, `TE′ = TE >> Skip` (= `TE;SKIP`) — our
  model is **tick-as-signal** (√ under `□` is realised as an UNSTABLE τ-slide via
  `□-slide-PR`, so √ is never in a stable refusal), so `TE` and `TE;SKIP` are
  equal — in contrast to Hoare's tick-as-refusable, where Roscoe notes they
  differ. Proved via `te∼ = sbisim-sym (seq-unit-r-∼ TE)` — reusing the
  certified `;`-right-unit strong-bisim law from `CSP.Laws.FD.SeqLaws` — then
  `drbisim→≈FD (sbisim→drbisim te∼)`. **Sequential composition / iteration**
  (`Iter(P) = loop0 P`, `T = Bool`): `copy-iter : COPY ≈FD IterCOPY` (=
  `Iter(left?x→right!x→SKIP)`; iteration = tail recursion, the `loop0` loop-back
  τ ⇒ `≈DR` not strong) AND `iterbuff2-bn2 : IterBuff2 ≈FD BN2` (= `IterBuff2 =
  loop0 TB`, the deterministic 2-place buffer `BN2 = BN 2 []`) — BOTH PROVED (no
  defer-fallback needed), each via a hand-built `DRFromRel` divergence-respecting
  weak bisimulation → `drbisim→≈FD`. **Counter:** the `ZERO`/`POS` up/down
  counter [G4], model-only (no FDR assertion in `section7-1.csp`). Agda's
  `--guardedness` checker rejects the literal `ZERO = up ⟶₀ (POS >> ZERO)` /
  `POS = (up ⟶₀ (POS >> POS)) □ (down ⟶₀ Skip)` (corecursion through the
  already-elaborated `>>`/`□` is not guarded), so it was reformulated as two
  directly-self-recursive ℕ-indexed families `Zn n` (= `POS^n;ZERO`) and `Pn n`
  (= `POS^n;SKIP`), with `ZERO = Zn 0`, `POS = Pn 1` — faithful state-for-state
  to the counter (up pushes/increments, down pops/decrements to termination),
  verified by three `sVis` transition sanity lemmas (`zero-up`/`pos-up`/
  `pos-down`). G1–G3 route through the certified `drbisim→≈FD`, inheriting the
  certified `¬-divergent→normal` (no new postulate); G4 postulate-free. All
  modules hole-free, no `NON_TERMINATING`/`mutual`/Sized. Deferred non-goals:
  `BN(N)` for N>2, `T` beyond `Bool`, any FD claim about `ZERO`/`POS`,
  `section7-2.csp` (interrupt/throw — separate track). First UCS-ch7 sub-spec.

_Last updated 2026-07-09._
## Cardano network example — link-indexed network vs. `CopySpec` (`Examples/Cardano_network/`)

`NetworkLink` (`NetworkLink.agda`) re-renders the monolithic `Network` mux
(`Network.agda`) per TCP link, as `⦀Fin numLinks NetOneLink` — the same shape
`CopySpec` already has (`⦀Fin numLinks linkCopy`). `NetworkLinkEquiv.agda`
assembles the headline equivalence out of the reusable generic congruence
machinery above:

| Result | Status | Module |
|---|---|---|
| `perLink : (l : Link) → linkConfig l ≢ [] → Unique (linkConfig l) → NetOneLink l ≈DR linkCopy l` (per-link general-config mux-vs-copy) | ✅ **PROVED, postulate-free** (Milestone 2b: the `PerLink.Leaf` → `PerLink.Fold` → `PerLink.Exp` `⦀⋆`-fold expansion walk; hypotheses honest per the 2026-07-10 spike: `≢ []` = empty-config soundness fix, `Unique` = instance-disjoint fold step-elimination) | `PerLink.Exp` |
| `netLink≈DR : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l)) → NetworkLink ≈DR CopySpec` | ✅ (`cong-⦀Fin` applied to `linkAlpha`/`linkAlpha-disj` + `oo-NetOneLink`/`oo-linkCopy`, fed by the PROVED `perLink`; `Data →` dropped) | `NetworkLinkEquiv` |
| `netLink≈FD : (∀ l → linkConfig l ≢ [] × Unique (linkConfig l)) → NetworkLink ≈FD CopySpec` | ✅ **PROVED** (`drbisim→≈FD (netLink≈DR hyp)`) — modulo ONLY the module-level certified König/classical axioms (Par-Diverges→, DRImpliesFD), as elsewhere in the FD layer | `NetworkLinkEquiv` |
| `netLink⊑FD` / `spec⊑FD-Link` (the two `≈FD` refinement directions, same hypothesis) | ✅ proved via `proj₁`/`proj₂`, same König caveat | `NetworkLinkEquiv` |
| `perLink-single : (l : Link)(dc : Dir)(idc : IDs) → linkConfig l ≡ (dc , idc) ∷ [] → NetOneLink l ≈DR linkCopy l` (per-link singleton-config corollary) | ✅ **corollary** of the general `perLink` (a singleton config is manifestly `≢ []` and trivially `Unique`) | `NetworkLinkEquiv` |
| `netLink≈DR-single : (∀ l → Σ[ c ] linkConfig l ≡ c ∷ []) → NetworkLink ≈DR CopySpec` (all-singleton network) | ✅ **corollary** — routes each singleton witness into `netLink≈DR`'s `≢ [] × Unique` hypothesis; König caveat as above | `NetworkLinkEquiv` |
| `netLink≈FD-single : (∀ l → Σ[ c ] linkConfig l ≡ c ∷ []) → NetworkLink ≈FD CopySpec` (all-singleton network) | ✅ **corollary** — `drbisim→≈FD (netLink≈DR-single sing)`; König caveat as above | `NetworkLinkEquiv` |

Confinement side: `linkAlpha`/`linkAlpha-disj` (per-link value-level alphabets,
pairwise disjoint) and `oo-NetOneLink`/`oo-linkCopy` (both families `OffersOnly`
their own link's alphabet, closed structurally through the `MenuConf` leaves and
the generic `OffersOnly-⦀`/`-Par`/`-∖` lemmas) are proved with **no postulates,
holes, or `NON_TERMINATING`** in `NetworkLinkOffers.agda`.

Milestone 2b closes this subsystem: the general per-link `perLink` (previously
the one remaining axiom in `NetworkLinkEquiv`) is now PROVED in `PerLink.Exp`
(the `Leaf` → `Fold` → `Exp` `⦀⋆`-fold expansion), `NetworkLinkEquiv` declares
zero axioms, and the four headline theorems drop their `Data →` witness. The
all-singleton results are now corollaries of the general path. The subsystem is
axiom-free modulo ONLY the FD layer's certified König/classical inputs
(`Par-Diverges→`, `DRImpliesFD`), as everywhere else.

**Repair note (2026-07-31), `NetworkVerification/Liveness/PipePair.agda`:** a
pre-existing RED module, unrelated to §15 but blocking work on it, is green again. It
carried **12 stale `OffersOnly` witnesses**: `e ! v ⟶ P` is `Output e v P` — a SINGLE
`react` node — so four sites needed `OffersOnly-Output refl OffersOnly-Ret` where they
had a bare `OffersOnly-Ret`, and eight had an extra `OffersOnly-Prefix₀` layer that the
single node does not have. The fix unblocks **6 of the module's 23 importers**; the other
17 have their own independent errors and remain red.

### Four-node diamond block-liveness — CSP failures-divergences refinement statement (`FourNode/Liveness/CSP_Refinement/Spec.lagda.md`, 2026-08-05)

`CSP/Examples/Cardano_network/FourNode/Liveness/CSP_Refinement/Spec` states, as a
CSP refinement, the block-liveness property of the broken four-node diamond
`systemBroken` (`FourNode/FourNodeDiamondBroken.lagda.md`):

```
LivenessSpec = ∀ (b : Block₃) → LSpec b true true ⊑FD (systemBrokenOf b ∖ hidden b)
```

**Status: stated — deliberately NOT proved and NOT postulated.**
`LivenessSpec` is a `Set`, exactly like `BlockLiveness`/`BlockLiveness⁺` in the
sibling LTL module (`FourNode/Liveness/LTL/Spec.lagda.md`) — no term of
this type is constructed anywhere, and there is no postulate standing in for
one. It is the CSP-refinement counterpart to the trace-LTL `BlockLiveness⁺`:
both express "if at least one A→B→D/A→C→D path stays whole, NodeD receives
NodeA's block", but `BlockLiveness⁺` uses **global** confinement (one path
group never breaks, checked via an implication over the whole run) whereas
`LivenessSpec` tracks path-wholeness **per state** by observing `break`
events directly, so it needs no implication primitive and is strictly weaker
as a hypothesis.

The obligation the Spec actually imposes is **per path and conjunctive**: *if A
produced `b` on path X's entry link **and** path X is whole, then D's receive of
`b` on X's exit link is not refused.* The produce conjunct is load-bearing —
gating on path-wholeness alone refuted the statement at trace length 1
(`t = ⟨send@AB⟩`, `X = {recv@CD}`: the implementation has a stable state there
refusing `recv@CD`, since C never got the block, while every branch of the old
`Prod b true true` offered it). `Prod`/`delivMenu` therefore carry four flags,
`b p1 g1 p2 g2`; see Decision 12 of the design doc.

The module ships **45 computable `refl` sanity tests** (11 hide-set incl. a
near-miss battery and two `EventSet.dec` probes, 9 delivery-menu, 6
must-offer/may-event, 18 real-τ-map coverage over every flag-updating branch of
`prodτ`/`idleτ`, 1 block-generic continuity) and is otherwise
**postulate-free**; the statement quantifies over the block-generic
`systemBrokenOf b` (not the `b1`-fixed shipped `systemBroken`), so `∀ b` is
non-vacuous for every block in `Block₃`. Full truth analysis
(divergence-freedom on both sides of the refinement, the produce-gating of the
obligation, the must-offer/may-offer `Prod`-branch fix, the CHAOS `Done`
requirement, the causal justification for the idle state offering no receive,
boundary cases, and the future proof route) is in the module's own "Truth
analysis" section; design rationale is
`docs/superpowers/specs/2026-08-04-fournode-liveness-csp-refinement-design.md`.

---

## §17 — FD/DR/FSim congruence & monotonicity: consolidated coverage (2026-08-03 campaign)

Eight tasks (`docs/superpowers/plans/2026-08-03-fd-congruence-campaign.md`) extended the
congruence suite so that compositional refinement — proving leaves, then folding via
operator monotonicity, rather than one monolithic bisim — is actually assemblable. This
section is a single-page index over the scattered rows above (§1–§16); it adds no new
result not already stated there, it only collects them. **Read the two-regimes note
below before using any `⊑FD`-mono row in a composite proof** — several of them are
leaf-level only.

### Consolidated table

Columns: `≈FD` cong = congruence at failures-divergences equivalence; `≈DR` cong =
congruence at divergence-respecting weak bisimulation; `FSim` cong = congruence at the
one-way failure-simulation order (§15); `⊑FD` mono = monotonicity of the `⊑FD` refinement
order itself. ✅ = done & typechecks · ⚠️ = side-condition / conditional · ✖ = the
UNCONDITIONAL form is proved FALSE · ❌ = not attempted.

**THE `⊑FD` MONO COLUMN HOLDS TWO DIFFERENT SHAPES — check which before using a row.**

| shape | statement | worth |
|---|---|---|
| **fact-shaped** | `⊑FD → ⊑FD` | **the valuable one.** A true precongruence. Its premise can come from ANYWHERE — a hand-built bisimulation, a denotational argument, an earlier refinement step, or a cashed-out `FSim` — and chains of these compose freely. |
| cash-out | `FSim → ⊑FD` | mostly ceremony. The body is literally `fsim→⊑FD (X-fsim …)`, a one-liner the caller can write; it adds a NAME, not power. Since `⊑FD → FSim` completeness is out of scope (§15, line ~1104) it can never consume a `⊑FD` fact, so it cannot appear in a `⊑FD`-only chain. |

(The `FSim` cong column is the third shape, `FSim → FSim` — essential, and the only thing
that composes an FSim tower or crosses a hide.)

**Policy, adopted 2026-08-04:** where a fact-shaped law exists it OWNS the `-mono-⊑FD`
name, and the cash-out wrapper is DELETED rather than renamed. **Fifteen** have been
retired on that basis: `⊓-mono-⊑FD` + `prefix-mono-⊑FD` (`FSim/IChoiceCong`),
`⦀Fin-mono-⊑FD` + `⦀⋆-mono-⊑FD` (`FSim/ParCongRep`), `Θ-mono-⊑FD` (`FSim/ThrowCong`),
`□-mono-⊑FD` (`FSim/ExtChoiceCong`), and — 2026-08-04, this campaign — **the entire
`FD/LoopMonoFD` module, which is consequently DELETED**, in three waves:
its bind half (`Bind-mono-⊑FD` / `bindNoτ-mono-⊑FD` / `bindκ-mono-⊑FD` / `>>-mono-⊑FD`,
superseded by `FD/BindMonoFD`, the general one renamed `>>=-mono-⊑FD` after the operator to
match `Traces`'s `>>=-mono-L`/`>>=-mono-k`); `loop0-mono-⊑FD-fsim` (whose `-fsim` suffix
existed only to dodge the clash with the fact-shaped `IterateMonoFD.loop0-mono-⊑FD`); and
finally its loop half `iter-mono-⊑FD` / `loop-mono-⊑FD` / `loopc-mono-⊑FD` /
`while-mono-⊑FD`, superseded by **`FD/IterMonoFD`**.
Callers holding a witness write `fsim→⊑FD (X-fsim …)` and,
if they want, feed it to the fact-shaped law. Surviving cash-out rows are kept ONLY because
no fact-shaped counterpart exists yet (`△` — now the ONLY such row)
or because the law provably must stay conditional/one-sided (`▷-mono-R-⊑FD-fsim`,
`αpar-mono-⊑FD-fsim-df`, `Hide-mono-⊑FD-df`). Do not mint new cash-out names for an operator
that already has a fact-shaped law.

**Naming amendment, adopted 2026-08-04 (closing a gap in the policy above).** The policy
above says what happens when a fact-shaped law SUPERSEDES a cash-out (fact-shaped keeps
the bare name, cash-out is deleted); it does not say what a SURVIVING cash-out — one with
no fact-shaped counterpart, and provably never able to get one, since `⊑FD → FSim`
completeness is out of scope — must be called. Left unnamed, three of them (`△`, `▷`,
`αpar`) were still sitting on the bare `-mono-⊑FD` name, which misleads a reader into
thinking they can feed it a `⊑FD` FACT when the definition can only ever consume a
simulation WITNESS. Closing that gap:

* the bare `‹op›-mono-⊑FD` name is reserved for a FACT-SHAPED law (premise itself a
  `⊑FD`/`⊑F⊥`/`⊑D`, or a `Pointwise` of one), always — never a cash-out, even a surviving
  one with no fact-shaped rival;
* a witness-premised law MUST carry a suffix naming the premise's WITNESS SHAPE: `-fsim`
  for an `FSim` premise, `-dr` for a `DRbisim` premise (the shape actually discharged —
  not whatever shape the proof happens to route through internally: `△`'s witness is a
  `DRbisim`, even though its body is `fsim→⊑FD (△-fsim …)`, hence `-dr` and not `-fsim`);
* a PREMISE-SHAPE suffix (`-fsim`/`-dr`) is a different axis from a SIDE-CONDITION suffix
  (`-df`, "divergence-free"), and the two compose independently rather than being
  interchangeable spellings of "conditional": `Hide-mono-⊑FD-df` is FACT-SHAPED (its
  premise is a bare `P ⊑FD Q`) WITH a side condition, so it carries `-df` alone; `▷-mono-
  R-⊑FD-fsim` is WITNESS-shaped with no side condition, so it carries `-fsim` alone;
  `αpar-mono-⊑FD-fsim-df` is WITNESS-shaped AND side-conditioned, so it carries both, in
  that order (premise shape before side condition). A reader must be able to tell the two
  suffix kinds apart from the name alone, without opening the module.

Applied 2026-08-04: `△-mono-⊑FD` → **`△-mono-⊑FD-dr`**, `▷-mono-R-⊑FD` →
**`▷-mono-R-⊑FD-fsim`**, `αpar-mono-⊑FD-df` → **`αpar-mono-⊑FD-fsim-df`** (all in
`FD/Congruences`'s re-export list; the first two are DEFINED in `FD/Congruences` and
`FSim/SlideCong` respectively, `αpar-mono-⊑FD-fsim-df` in `FSim/AlphaParCong`).
`Hide-mono-⊑FD-df` (`FD/HideMonoFD`) is UNCHANGED — its premise genuinely is `P ⊑FD Q`,
so it was already correctly named under this policy; `-df` there is a side condition, not
a premise-shape marker, and renaming it would be wrong.

| Operator | `≈FD` cong | `≈DR` cong | `FSim` cong | `⊑FD` mono |
|---|---|---|---|---|
| Internal choice `⊓` | ✅ `⊓-cong-FD` / `⊓-cong-FD≈` — `FDCong` / `FDLawsIChoiceRep` | ✅ `⊓-cong-DR` — `FDCong` | ✅ `⊓-fsim` — `FSim/IChoiceCong` | ✅ **`⊓-mono-⊑FD` — `FD/IChoiceMonoFD`, FACT-SHAPED (`⊑FD`→`⊑FD`), unconditional, 0 postulates** (+ `⊓-refine-⊑FD : (P⊓Q)⊑FD P`, the ⊓/□ strict refinement `FSim/IChoiceCong`/`ChoiceRefine`).  The former `FSim`→`⊑FD` wrapper of this name in `FSim/IChoiceCong` was RETIRED 2026-08-04 |
| Replicated internal choice `⨅⁺` / `⨅Fin` | ❌ | ❌ | ❌ | ✅ **`⨅⁺-mono-⊑FD` / `⨅Fin-mono-⊑FD` — `FD/IChoiceMonoFD`, FACT-SHAPED, unconditional, 0 postulates** (inductions over `⊓-mono-⊑FD`).  ⚠️ BOTH FOLDS ARE **NON-EMPTY** — `⨅⁺ P [] = P` (head+list) and `⨅Fin zero f = f fzero` (`Fin (suc n)`-indexed) — so unlike the `⦀`/`□` folds the base case hands back an OPERAND and `⊑FD-refl` is never used; `⨅⁺`'s recursion RE-HEADS on the list's head |
| Prefix `⟶₀` | ✅ `prefix-cong-FD` — `FDCong` | ✅ `prefix-cong-DR` — `FDCong` | ✅ `prefix-fsim` — `FSim/IChoiceCong` | ✅ **`⟶₀-mono-⊑FD` — `ChoiceRefine`, FACT-SHAPED**.  The `FSim`→`⊑FD` duplicate `prefix-mono-⊑FD` (`FSim/IChoiceCong`) was RETIRED 2026-08-04 |
| Output prefix `e ! v ⟶` | ❌ | ❌ | ❌ | ✅ **`Output-mono-⊑FD` — `FD/DerivedMonoFD`, FACT-SHAPED, unconditional, `--safe`-clean**.  NOT a corollary of `⟶₀-mono-⊑FD`: `Output` shares `Prefix₀`'s event index `(A , e)` but has a DIFFERENT offer map — `Output-cont` fires only on the single carried value `v` (extra `x ≟ v` decision, hence `⦃ DecEq A ⦄`) — so the whole `⟹`-inversion / offers / refusals / failures / divergences decomposition of `FDLawsPrefixDist` had to be redone |
| External choice `□` | ❌ | ❌ | ✅ `□-fsim` — `FSim/ExtChoiceCong`, **two-sided, unconditional, NO `Sep`-style side condition** (contrast `Par-fsim`) | ✅ `□-mono-⊑FD` — **FACT-SHAPED** (`⊑FD → ⊑FD`), `FD/ExtChoiceMonoFD` (+ the fact-shaped replicated folds `□Fin-mono-⊑FD`/`□⋆-mono-⊑FD`, one line each — no side condition to thread through the fold; the shape-3 cash-out formerly in `FSim/ExtChoiceCong` is retired; + the pre-existing cross-operator strict refinement `(P⊓Q)⊑FD(P□Q)`, `ChoiceRefine`) |
| Sliding `▷` | ❌ | ❌ | ⚠️/✖ `▷-fsim-R` — `FSim/SlideCong`, **ONE-SIDED ONLY** (left operand shared); the TWO-sided form is **proved FALSE** (`FSim/SlideCounterexample.¬▷-fsim`) | ⚠️ `▷-mono-R-⊑FD-fsim` — `FSim/SlideCong`, one-sided by necessity given the counterexample; `-fsim` names its `FSim` WITNESS premise (2026-08-04 rename, was `▷-mono-R-⊑FD`) |
| Interrupt `△` | ✅ `△-cong-FD` — `FD/Congruences` | ⚠️ `cong-△` — `Bisim/DRCongruence`, conditioned on `Sep△` (unconditional false) | ✅ `△-fsim` — `FD/Congruences` | ✅ `△-mono-⊑FD-dr` — `FD/Congruences`; `-dr` names its `DRbisim` WITNESS premise (2026-08-04 rename, was `△-mono-⊑FD` — NOT `-fsim`, despite routing through `△-fsim`, because the premise actually discharged is `DRbisim`) |
| Throw `⟦A▷` (`_⟦_▷_` — DISTINCT operator from `△` above; **verify before reusing the row title**, see the note below the table) | ❌ | ❌ | ✅ `Θ-fsim` — `FSim/ThrowCong`, **two-sided, unconditional, `--safe`-clean**, no `Sep`-style condition, no divergence-freedom hypothesis | ✅ `Θ-mono-⊑FD` — **FACT-SHAPED** (`⊑FD → ⊑FD`), `FD/ThrowMonoFD` (the shape-3 cash-out formerly in `FSim/ThrowCong` is retired) |
| Parallel `Par`/`∥`/`⦀` (pairwise) | ⚠️ `Par-cong-FD` / `⦀-cong-FD` — `FD/Congruences`, conditioned on `SepDR` (unconditional false) | ⚠️ `cong-Par⊤` / `cong-⦀` — `Bisim/DRCongruence`, conditioned on `Sep` (unconditional false) | ⚠️ `Par-fsim` / `⦀-fsim` — `FSim/ParCong`, conditioned on `Sep` **on the impl pair only** (half of what `≈DR`/`≈FD` need) | ✅ `Par-mono-⊑FD` / `∥-mono-⊑FD` / `⦀-mono-⊑FD` — `FD/ParallelMonoFD`.  ✅ **Also at STABLE FAILURES: `Par-mono-⊑F` / `∥-mono-⊑F` / `⦀-mono-⊑F` — `FD/ParallelMonoFD` (Layer 10, 2026-08-05), FACT-SHAPED, UNCONDITIONAL, and needing NO divergence layer** (`_⊑F_` has no `divergences` disjunct, so the `⊎`-branching of the `⊑FD` proof and its whole Layer-5 truncation machinery do not arise; no `⊑D` counterpart exists or is needed).  Classical provenance is `offer-LEM` ALONE (via `Par-stable`) — strictly less than `Par-mono-⊑FD`'s, which also inherits `Par-Diverges→`/`Diverges-LEM` |
| Replicated interleaving `⦀Fin` / `⦀⋆` | ✅ `⦀Fin-cong-FD` / `⦀⋆-cong-FD` — `FD/Congruences` | ✅ `cong-⦀Fin` / `cong-⦀⋆` — `Bisim/DRCongruenceRep` (disjoint-alphabet `Sep` discharged from `OffersOnly` alone) | ✅ `⦀Fin-fsim` / `⦀⋆-fsim` — `FSim/ParCongRep` (`Sep` per fold step, from `sep-from-OffersOnlyᶠ`) | ✅ **`⦀Fin-mono-⊑FD` / `⦀⋆-mono-⊑FD` — `FD/ParallelMonoFD` (Layer 8), FACT-SHAPED and needing NO `Disj`/`OffersOnly`** (inductions over the unconditional `⦀-mono-⊑FD`; the `Disj`/`OffersOnly` of the FSim folds exist only to discharge `Par-fsim`'s `Sep`, which `Par-mono-⊑FD` has not).  The `FSim`→`⊑FD` wrappers of these names in `FSim/ParCongRep` were RETIRED 2026-08-04.  ✅ **Stable-failures twins `⦀Fin-mono-⊑F` / `⦀⋆-mono-⊑F` — `FD/ParallelMonoFD` (Layer 10), same inductions over the unconditional `⦀-mono-⊑F` with `⊑F-refl Skip` at the base, equally free of `Disj`/`OffersOnly`** |
| Non-empty replicated interleaving `⦀⁺` / `⦀Fin⁺` (no trailing `Skip`, unlike `⦀⋆`/`⦀Fin` — `CSP/Operators.agda:646,653`) | ❌ | ✅ `OffersOnly-⦀Fin⁺` (alphabet-confinement of the non-empty fold) + `cong-⦀Fin⁺` — `Bisim/DRCongruenceRep.agda:546,571` (disjoint-alphabet `Sep` discharged from `OffersOnly` alone, same shape as `cong-⦀Fin`).  ⚠️ **`cong-⦀Fin⁺` is currently UNUSED** — a sunk cost of a mid-campaign route change (2026-08-12): the N-node assembly was first aimed at `≈DR`, which needs this congruence's pairwise per-node alphabet disjointness, but that disjointness was REFUTED for nodes (they share link alphabets with their neighbours), so the campaign re-routed to assemble at `⊑FD` instead | ❌ | ✅ **`⦀Fin⁺-mono-⊑FD` / `⦀⁺-mono-⊑FD` — `FD/ParallelMonoFD.agda:748,755`, FACT-SHAPED and needing NO `Disj`/`OffersOnly`** (inductions over the unconditional `⦀-mono-⊑FD` — this fold, unlike the `≈DR`/`FSim` fold above, carries **no side condition at all**).  ⚠️ NON-EMPTY like `∥⁺`/`∥Fin` and NOT like `⦀Fin`/`⦀⋆`: `⦀⁺ P [] = P`, `⦀Fin⁺ zero f = f fzero`, so the base case hands back an OPERAND, not `⊑FD-refl Skip` |
| Replicated interface parallel `∥⁺` / `∥Fin` | ❌ | ❌ | ❌ | ✅ **`∥⁺-mono-⊑FD` / `∥Fin-mono-⊑FD` — `FD/ParallelMonoFD` (Layer 9), FACT-SHAPED, NO side condition** (inductions over the unconditional `∥-mono-⊑FD`; each carries the one shared synchronisation `EventSet` as an explicit first argument).  ⚠️ Both are **NON-EMPTY** like `⨅⁺`/`⨅Fin` and unlike the `⦀` folds, because interface parallel has no unit: `∥⁺ A P [] = P`, `∥Fin A zero f = f fzero`.  ✅ **Stable-failures twins `∥⁺-mono-⊑F` / `∥Fin-mono-⊑F` — `FD/ParallelMonoFD` (Layer 10), same shape, same non-emptiness, over the unconditional `∥-mono-⊑F`** |
| Hiding `∖` | ✅ `hide-cong-FD` — `FD/Congruences`, **unconditional** | ✅ `cong-∖` — `Bisim/DRCongruence`, **unconditional** | ✅ `Hide-fsim` — `FSim/HideCong`, **unconditional** | ✖ unconditional `Hide-mono-⊑FD` is **FALSE** (`FD/HideMonoFD`); only `Hide-mono-⊑FD-df`, conditional on divergence-freedom of the **REFINED / RIGHT (implementation) operand's hide `Q∖A`** — `∀ {s} → ¬ divergences (Q∖A) s`, NOT of the spec's hide `P∖A` (`HideMonoFD.agda:243` calls it "the refined side's hide"; signature at :268-270) — and the unconditional failures-only half `Hide-mono-fail`.  ✅ **BUT at STABLE FAILURES the law IS unconditional: `Hide-mono-⊑F` — `FD/HideMonoFD`:255 (2026-08-04), `P ⊑F Q ⇒ (P∖A) ⊑F (Q∖A)`, NO side condition**, because `_⊑F_` has no `divergences` disjunct for hiding's τ-introduction to break; pairs with `Par-mono-⊑F` (Layer 10 of `FD/ParallelMonoFD`) to give a hide-crossing compositional route at refusal strength |
| Renaming `⟦R⟧` / `renameMap` | ✅ `rename-cong-FD` / `renameMap-cong-FD` — `FD/Congruences`, **unconditional** | ✅ `cong-renameInv` / `cong-renameMap` — `Bisim/DRCongruence`, **unconditional** | ❌ (no `rename-fsim` built) | ✅ **FACT-SHAPED** (`⊑FD → ⊑FD`), `FD/RenameMonoFD` (2026-08-04) — renaming's FIRST monotonicity law at any shape.  ✅ `renameInv-mono-⊑D` **UNCONDITIONAL and CONSTRUCTIVE** — `renameInv` relabels step-for-step, so `ren-τ-fwd`/`ren-τ-inv` are mutually inverse on steps and `Diverges (P⟦inv⟧ⁱ) ↔ Diverges P` is a plain corecursive projection: **no König step anywhere, zero postulates local or inherited** (the cheapest divergence transfer in the repo, and the reason rename is the cheap congruence).  ⚠️ `renameInv-mono-⊑F⊥` / `renameInv-mono-⊑FD` take `RenTight inv` (a forward section `fwd` with `inv (fwd ce) ≡ just ce`, plus `inv ce ≡ just ce′ → ce ≡ fwd ce′`, i.e. no visible fan-OUT).  That is a **LEVEL artefact, not mathematics**: transferring a reached refusal needs the target ban set pulled back along `inv`, and the honest pullback `Σ[b] (inv b ≡ just e × B (evl b))` lives at `lsuc ℓ ⊔ ℓe ⊔ ℓr` because it quantifies over `AnyTypes E`, whereas `_⊑F⊥_ {R = Rr}` pins ban sets to `Set ℓr`; `RenTight` makes the pullback POINTWISE (`banSrc B e = B (fwd e)`) and hence level-`ℓr`.  Same family of obstruction as `BindMonoFD`'s shared result level and `IterateMonoFD`'s `ℓr ≡ ℓ`.  ✅ It **DISCHARGES for `renameMap`** (`ι-vis-inv-tight`: at the same alphabet `ι = id`/`ι⁻¹ = just` makes `ι-vis-inv` the identity inverse), so `renameMap-mono-⊑D` / `-⊑F⊥` / `-⊑FD` are all UNCONDITIONAL.  ⚠️ Stated at the SAME alphabet, following the `⊑T` precedent `TraceLawsRename.renameInv-mono-⊑ᵀ` — so, unlike the `≈DR`/`≈FD` rename congruences, it needs NO `ι`/`ι⁻¹`/`ι-linv` telescope and no `E-≟`.  Scope: the GENERAL relational `_⟦R¿preimg⟧` (with fan-in) is NOT covered, same scope limit as `cong-renameInv` |
| Bind `>>=` / `>>` | ❌ (not built directly at `≈FD`/`≈DR`) | ❌ | ⚠️ `Bind-fsim` (needs `BindDivSplit`) / `bindNoτ-fsim` / `bindκ-fsim` (both unconditional) / `>>-fsim` (unconditional, bakes in `>>-split`) — `FSim/BindCong` | ✅ **FACT-SHAPED** (`⊑FD → ⊑FD`), `FD/BindMonoFD` (2026-08-04): ⚠️ `>>=-mono-⊑FD` (needs `BindDivSplit k₂` — the König split, on the REFINED continuation, for the `⊑D` half ONLY) · ✅ `bindNoτ-mono-⊑FD` / `bindκ-mono-⊑FD` / **`>>-mono-⊑FD`** all UNCONDITIONAL (split discharged by `bind-noτ-split` / `pure→NoTauRoot` / `>>-split`).  All four pin a SHARED result level `R S : Set ℓr` — a LEVEL constraint, not a mathematical one: `_⊑F⊥_` ties a carrier's ban set to `Event√ R → Set ℓr`, and transferring a still-in-prefix failure needs the composite's `Event√ S` ban set RETAGGED over `Event√ R` (`banP`); `Lift` only raises levels.  Same reason `IterateMonoFD` pins `ℓr ≡ ℓ`, but weaker (any shared level).  These four SUPERSEDE and REPLACE the retired `FD/LoopMonoFD` cash-outs, and unlike them they are NOT leaf-level — a `⊑FD` fact from anywhere composes.  `bindκ-mono-⊑FD` is also what carries `loop`/`while` in `FD/IterMonoFD` (their `iter` steps are pure-continuation binds) |
| Replicated sequential `⨾⋆` / `⨾Fin` | ❌ | ❌ | ❌ | ✅ **`⨾⋆-mono-⊑FD` / `⨾Fin-mono-⊑FD` — `FD/BindMonoFD`, FACT-SHAPED, unconditional** (inductions over `>>-mono-⊑FD`).  ⚠️ BOTH FOLDS ARE **EMPTY-BASED** — `⨾⋆ [] = Skip` and `⨾Fin zero f = Skip`, `Skip` being the unit of `;` (`Operators`:358-364) — so the base case is `⊑FD-refl Skip`, exactly like `⦀Fin`/`⦀⋆`/`□Fin`/`□⋆` and NOT like `⨅⁺`/`⨅Fin`/`∥⁺`/`∥Fin`, whose base hands back an operand.  Both fold with `_>>_`, never the general `_>>=_`, so no side condition is threaded through the fold |
| Iterate / loop family (`iter`/`loop`/`loop0`/`loopc`/`while`) | ❌ (not built directly at `≈FD`/`≈DR`) | ❌ | ✅ `Iter-bind-fsim` + 5 corollaries — `FSim/LoopCong`, all **unconditional** (`iter-div-split` discharges the König step generically) | ✅ **FACT-SHAPED throughout** (`⊑FD → ⊑FD`), `FD/IterMonoFD` (2026-08-04): `iter-mono-⊑FD` / `loop-mono-⊑FD` / `while-mono-⊑FD` / `loopc-mono-⊑FD`, plus the pre-existing `loop0-mono-⊑FD` (`FD/IterateMonoFD`, §12).  These four SUPERSEDE and REPLACE the shape-3 cash-outs of the same names in `FD/LoopMonoFD`, whose deletion emptied and therefore DELETED that module.  **DEFINITIONAL RELATIONSHIPS (all `refl`, `Operators`:1017-1063), and they are what make this cheap:** `loop body a = iter (body a >>= Ret ∘ inj₁) a` and `while c body a = iter (body a >>= Ret ∘ tag c) a`, so `loop`/`while` fall out of the general `iter` law composed with the UNCONDITIONAL `bindκ-mono-⊑FD` (the step's continuation is pure); and `loopc body = loop (λ _ → body) tt = loop0 body` **TEXTUALLY**, not merely up to equivalence, so `loopc-mono-⊑FD` IS `loop0-mono-⊑FD` — `loopc` follows from `loop0`, not only from `loop`.  `iter-mono-⊑F⊥`/`-⊑D` generalise `IterateMonoFD`'s `loop0` proof from a `PTree ⊤` body to a state-indexed step: the `Acc _<_`-on-`runLen` recursion carries over UNCHANGED (`IterSplitN`/`iter-bind-invN` were already `iter`-generic), the loop state threads through as a pointwise premise, the loop-back states are forced to agree on the next state `a′` by the `√` tick CARRYING the returned value, and the `in-done` arm — vacuous for `loop0` — is new and constructive.  Side condition: `A R : Set ℓ`, the same ban-set level pin `IterateMonoFD` imposes.  ⚠️ Inheritance is STRICTLY WEAKER than the `loop0` specialisation's: the general laws use `FSim/LoopCong.iter-div-split` (a DERIVED lemma over `Diverges-LEM` + `¬DivModA→MAcc`) and **not** the `loop0`-specific postulate `IterateFD.loop-Diverges→` that `loop0-mono-⊑FD` leans on; the `⊑F⊥` half needs no classical ingredient of its own |
| Guard `＆` (`b ＆ P = guard b >> P`) | ❌ | ❌ | ❌ | ✅ **`＆-mono-⊑FD` — `FD/DerivedMonoFD`, FACT-SHAPED, unconditional, `--safe`-clean**.  Not quite free: `PTree` is a COINDUCTIVE record, so there is no η and `Skip >> P` is a *different tree* from `P` with the same `force`.  The law goes through `force-≡→⊑FD` (force-equal trees are ⊑FD-interchangeable — the FD analogue of `Traces/TraceLawsGuard.force-≡→traces-⊆`, which proves the same law at `⊑T` as `＆-mono-⊑ᵀ`, and of `FD/SeqLaws.sbisim-force-eq` at `∼`).  That bridge was HOISTED 2026-08-04 out of `DerivedMonoFD` into `Semantics/FailuresDivergences` (beside `⊑FD-refl`/`⊑FD-trans`), where it is proved DIRECTLY over the LTS from a new generic `step-force-≡` — the statement is "every LTS rule reads its source only through `force`", generic in `E`/`I` and CSP-free; `DerivedMonoFD`'s `CSP.Laws.FD.BindFD` dependency went away with it.  The `false` branch is force-equal on both sides at once: `Stop >> P` deadlocks independently of `P` |
| Conditional `P ◁ b ▷ Q` (§4) | ❌ | ❌ | ❌ | ✅ **`◁▷-mono-⊑FD` — `FD/DerivedMonoFD`, FACT-SHAPED, two-sided, unconditional**.  It IS `if_then_else_`, so each `b` selects the matching hypothesis; genuinely a one-liner (contrast `＆`, whose `guard b >> P` shape has no η) |
| Menu / `pchoice` (multi-channel offer map) | ✅ `pchoice-cong-FD` — proved in `FD/RenameStepRel.agda:166`, **now re-exported from `FD/Congruences`** (with its premise type `MaybeFD`); see the promotion note below | ❌ | ❌ (no `pchoice-fsim` was built) | ❌ |
| Alphabetised parallel `_⟦_∥_⟧_` (= `αpar A B _,_`) | ❌ | ❌ | ⚠️ `αpar-fsim-df` — `FSim/AlphaParCong`, conditioned on `τ-AccReach` divergence-freedom of the **SPEC operands only** (impl operands unconstrained); the UNCONDITIONAL two-sided form, and the ONE-SIDED form in BOTH orientations, are **proved FALSE** (`FSim/AlphaParCounterexample.¬αpar-fsim`/`¬αpar-fsim-R`) | ⚠️ `αpar-mono-⊑FD-fsim-df` — `FSim/AlphaParCong`, same `τ-AccReach` side condition; `-fsim` names the `FSim` WITNESS premise, `-df` the side condition — both suffixes, in that order (2026-08-04 rename, was `αpar-mono-⊑FD-df`) |

**Addendum: FACT-SHAPED `⊑FD` precongruences for the LOOP family and for RENAMING
(2026-08-04, later still).** Two new modules, and the *end* of `FD/LoopMonoFD`.

* `FD/IterMonoFD` — `iter-mono-⊑FD` / `loop-mono-⊑FD` / `while-mono-⊑FD` /
  `loopc-mono-⊑FD`, all shape 2. The four shape-3 wrappers of the same names were the
  last things in `FD/LoopMonoFD`, so deleting them **deleted the module**; its re-export in
  `FD/Congruences` is gone. The definitional findings are what made this cheap and are
  worth remembering: `loop` and `while` are *literally* `iter` over a pure-continuation
  bind step, and **`loopc` is `loop0` — the same definition text, so `loopc` follows from
  `loop0`, not only from `loop`.** Only the general `iter` case needed real work, and it is
  the `loop0` proof (`Acc _<_` on `runLen`) generalised to a state-indexed body, with the
  next-state agreement supplied for free by the `√` tick carrying the returned value.
* `FD/RenameMonoFD` — renaming's **first monotonicity law at any shape**. The `⊑D` half is
  unconditional and needs no König step at all (rename's τ-space corresponds one-for-one).
  The `⊑F⊥` half takes `RenTight inv`, and that hypothesis is a **level artefact of how
  `_⊑F⊥_` is stated**, not a mathematical side condition: the honest ban-set pullback
  quantifies over target events and so lands above the carrier level that `_⊑F⊥_` pins its
  ban sets to. It discharges for `renameMap`. See the Renaming row for the full statement.
* Both are stated with a level restriction of the same family as `BindMonoFD`'s shared
  result level: `A R : Set ℓ` for the loop laws, `RenTight` for rename's failure half.
  Neither is a mathematical weakening.

**Addendum: FACT-SHAPED `⊑FD` precongruences for `□` and throw (2026-08-04, later).**
`□-mono-⊑FD` (+ the folds `□Fin-mono-⊑FD`/`□⋆-mono-⊑FD`) now live in
`FD/ExtChoiceMonoFD`, and `Θ-mono-⊑FD` in `FD/ThrowMonoFD`, both in the FACT shape
`⊑FD → ⊑FD` (a true precongruence, consuming a `⊑FD` premise from ANY source).  The
shape-3 `FSim → ⊑FD` cash-out wrappers that formerly held those two names in
`FSim/ExtChoiceCong` and `FSim/ThrowCong` were RETIRED — write `fsim→⊑FD (□-fsim …)` /
`fsim→⊑FD (Θ-fsim …)` at the call site, or feed that term to the fact-shaped law.  That
brings the retired-wrapper count to SEVEN; `FD/Congruences`'s header POLICY note is the
authoritative list, and the four matrix/registry rows above have been corrected in place.
NARRATIVE STALENESS FLAG: the §10/§15/§17 campaign-record entries earlier in this file
still describe `Θ-mono-⊑FD`/`□-mono-⊑FD` as living in the `FSim/*` modules; those are
historical records of the FSim campaigns and were deliberately not rewritten — trust the
rows and the `FD/Congruences` POLICY note over them.  Both new modules have ZERO local
postulates.  `FD/ThrowMonoFD` inherits ONLY `FD→trace⊥`'s `Diverges-LEM` +
`¬-divergent→normal`, and only in its `θFire` arm — there is NO König-style
`Θ-Diverges→` (throw's divergence inversion is structural), so its `θNo`/`θDone` arms are
fully constructive; `agda --safe` fails on `¬-divergent→normal` alone.
`FD/ExtChoiceMonoFD` inherits `□-Diverges→`/`▷-Diverges→` (unavoidable for any `□` law
touching divergences) and is pure routing through the existing `ExtChoiceFD`/
`ExtChoiceAssoc` decompositions — nothing new is proved there.  STILL MISSING (checked,
not attempted): a fact-shaped `△-mono-⊑FD` — `FD/InterruptFD` has only the Fig 13.6
`ret`/`div` rows plus step lifts, so there is no `△-reach-div`/`△-failures-elim`/
`△-div-intro-*` to route through, and interrupt's refusal is a CONJUNCTION of the two
operands at EVERY trace (not just at `[]`, as for `□`), so the `⊑F⊥` half needs new
`Par`-style two-operand failure decomposition machinery.

**Addendum: the CHEAP fact-shaped remainder — replicated folds and derived operators
(2026-08-04, later still).** Seven more fact-shaped (`⊑FD → ⊑FD`) laws, in three commits,
adding **five new matrix rows** above. All unconditional; none needed a side condition,
and none is a cash-out.

* **`FD/IChoiceMonoFD`** gained `⨅⁺-mono-⊑FD` / `⨅Fin-mono-⊑FD`; **`FD/ParallelMonoFD`**
  gained a Layer 9 with `∥⁺-mono-⊑FD` / `∥Fin-mono-⊑FD`. Three lines each, over the
  existing binary laws. **Correction to the campaign brief, which claimed these folds
  mirror `⦀Fin`/`⦀⋆`:** all FOUR are **non-empty** folds, so the base case is an OPERAND
  hypothesis and `⊑FD-refl` never appears — `⨅⁺ P [] = P`, `⨅Fin zero f = f fzero`,
  `∥⁺ A P [] = P`, `∥Fin A zero f = f fzero` (`CSP/Operators.agda:137,143,651,656`).
  `⨅⁺`/`∥⁺` additionally RE-HEAD on the list's head at each step, so the induction
  consumes a `Pointwise` cell and passes it on as the new head hypothesis rather than
  keeping a fixed head. `∥⁺`/`∥Fin` are the *interface*-parallel forms (one shared
  synchronisation `EventSet` at every step), so each takes that `EventSet` explicitly;
  `∥-mono-⊑FD` being unconditional, nothing accumulates along the fold — confirming the
  brief's expectation that no side condition would be needed.
* **New module `FD/DerivedMonoFD.agda`** (`agda --safe` exits 0 — zero postulates, local
  or inherited — its whole closure is `Process_Trees` + `CSP/Operators` + six `Semantics/*`
  modules + `FD/BindFD`): `＆-mono-⊑FD`, `◁▷-mono-⊑FD`, `Output-mono-⊑FD`. `Output` is the substantive
  one (~90 of the module's lines) for the offer-map reason in its row above. The two
  `Bool` splits are *not* both trivial: `◁▷` is `if_then_else_` and reduces, but
  `b ＆ P = guard b >> P` needs `force-≡→⊑FD` because coinductive records have no η —
  see its row. Homed together rather than in `ChoiceRefine` (60 lines about `⊓`-vs-`□`
  refinement, which the `Output` plumbing would swamp) or `FDLawsPrefixDist` (whose
  subject is `⊓`-distribution over prefix).
* All seven are re-exported from the `FD/Congruences` index (selective `using`; the
  `Output` decomposition and `force-≡→⊑FD` stay internal as scaffolding), and its
  postulate-provenance block records the two new entries.

**Addendum: the STABLE-FAILURES (`⊑F`) layer — `Par-mono-⊑F` + folds, and why it is
cheaper than its `⊑FD` twin (2026-08-05).** `FD/ParallelMonoFD` gained a **Layer 10**:
`Par-mono-⊑F` plus all six folds `∥-mono-⊑F` / `⦀-mono-⊑F` / `⦀Fin-mono-⊑F` /
`⦀⋆-mono-⊑F` / `∥⁺-mono-⊑F` / `∥Fin-mono-⊑F`, all fact-shaped (`⊑F → ⊑F`) and all
**unconditional**. Together with the already-committed `HideMonoFD.Hide-mono-⊑F` this closes
the compositional route at stable-failures strength: build a refinement up an operator tree,
then push it through the hide.

* **The divergence layer disappears entirely, and that is a type-level fact, not a
  simplification.** `_⊑F_` (`Semantics/Failures.agda:42-43`) is `∀ s X → failures Q s X →
  failures P s X`: no `divergences` disjunct in either the hypothesis or the conclusion.
  Layer 4's `op-transfer-stable` / `op-transfer-ret` already fed only `inj₁` (failures)
  arguments *into* their `⊑F⊥` hypotheses — what forced `Par-mono-fail` to branch four ways
  per `ParNormal` case was purely their `⊎`-valued **result**. Their `⊑F` twins
  (`op-transfer-stable-F` / `op-transfer-ret-F`) return a bare failure, so each of the three
  `ParNormal` cases collapses to its single `Par-failures-intro` recombination. Nothing ever
  produces a composite divergence, so **Layers 1 and 5 in their entirety** —
  `ParInter-truncL/R/2`, `Par-div-transfer-L/R/2`, `Par-div-out-L/R/2`, `div-extend`,
  `div-extension-closed`, `Par-div-intro`, `FD→trace⊥` — are unused here, and there is
  **no `Par-mono-⊑D` counterpart** to prove or to pair with: `Par-mono-⊑F` *is* the
  headline, not a half of one.
* **The failures core was reused verbatim, as predicted.** `Par-failures-elim` /
  `Par-failures-intro` (`FD/ParallelFailures`), Layer 2's `Par-stable-normal`, and Layer 3's
  whole `routeL`/`routeR` ban-set carving (`routeL-covers`/`routeR-covers`/`route-rebuild`/
  `ret-routeL-cover`/`ret-routeR-cover`) are all divergence-free already, so they took the
  `⊑F` hypotheses unchanged. Net cost: **four new definitions** (two Layer-4 twins, one
  Layer-6 twin, the headline) plus six one- or two-line folds. Typechecked first try.
* **One real signature difference to watch when calling these:** `_⊑F_` takes its trace `s`
  and ban set `X` **EXPLICITLY**, whereas `_⊑F⊥_` takes them implicitly. So the `⊑F` laws
  are applied as `hP sP BP ⟨failure⟩`, not `hP ⟨failure⟩`, and the headline's clause head is
  `Par-mono-⊑F A merge hP hQ s X f` rather than `… hP hQ {s} {X} f`. The ban-set level pin is
  the same as everywhere else in this module (`X : Event√ R → Set ℓr`, all carriers at one
  `ℓr`), which is what lets `routeL`/`routeR` be handed straight to a `⊑F` hypothesis.
* **Classical cost is strictly LOWER than the `⊑FD` twin's**: `offer-LEM` alone (via
  `Par-stable`/`Par-stable-termL/R`), *not* `Par-Diverges→` and *not* `Diverges-LEM` — see
  the provenance block below for the dependency-cone argument. `offer-LEM` is pre-existing,
  dne-certified in `ClassicalFromLEM`, and already incurred by `Par-mono-⊑FD`; **no new
  postulate, no hole**.
* **Why this matters (the motivating obstruction).** The FD route to a large hidden
  composite is blocked twice over: unconditional `Hide-mono-⊑FD` is FALSE, and
  `Hide-mono-⊑FD-df` needs divergence-freedom of the **implementation** composite's hide —
  an intractable `MAcc` termination argument at ~150 leaves. The `⊑F` pair dodges both while
  keeping the refusal content that a liveness property actually needs.

**Correction: the "Interrupt / throw △" row's title was misleading (2026-08-04).** Its
title used to read "Interrupt / throw `△`", but every entry in that row —
`△-cong-FD`/`cong-△`/`△-fsim`/`△-mono-⊑FD-dr` — is built on `Bisim/DRCongruence`'s `cong-△`,
which is about `_△_` (interrupt) alone; grepped, none of those names ever mentions
`_⟦_▷_` (throw). So a row for throw did **not** already exist, despite the title
suggesting otherwise — the same "assumed present, actually absent" trap the `αpar` row
fell into earlier in this campaign (a prior task assumed that row was present when it
was not). The title above is now corrected to "Interrupt `△`" alone, and a genuine new
row, "Throw `⟦A▷`", is added directly below it for `Θ-fsim`/`Θ-mono-⊑FD`
(`FSim/ThrowCong`, 2026-08-04) — see the addendum below for the full result. No cell
content was deleted, only the row's own title corrected and a new row added.

**Promotion, and a correction to the premise this note used to carry (the design's §A3
item).** The campaign design (`docs/specs/2026-08-03-fd-congruence-campaign-design.md`,
§A1 line 126 and §A3 line 156) offered two alternatives for the menu congruence: build
`pchoice-fsim` if it fell out of `prefix-fsim`'s shape, **or else** promote the existing
`pchoice-cong-FD` into `FD/Congruences` "by lifting it out of its local `module _` in
`RenameStepRel.agda:166`". The second alternative is now **done**, and it needed no lifting
at all — the premise that it was *not* a general export was **false**:

* An anonymous `module _ {ℓr} {R-set : Set ℓr} where` block (opens at
  `RenameStepRel.agda:93`) is **auto-opened into its parent**, so `pchoice-cong-FD` was
  already exported by `CSP.Laws.FD.RenameStepRel`, with `{ℓr} {R-set}` prepended as
  implicits. Machine-checked by importing it into a throw-away module.
* The block's `Menu` abbreviation (`:95-97`) is `private`, but `private` in Agda hides only
  the **name**: the definition still unfolds, so an outside caller can spell the type out
  (`(at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R-set))`) and apply the
  lemma. Also machine-checked, by discharging that hand-written signature with
  `pchoice-cong-FD` directly.

So the promotion is a **pure indexing change**: `FD/Congruences` re-exports
`pchoice-cong-FD` and `MaybeFD`, and **`RenameStepRel.agda` is untouched** — no risk was
taken with a working proof module. Verified against source: repo-wide there is still **no**
`pchoice-fsim`; `pchoice-cong-FD` is declared at `RenameStepRel.agda:166`, used once
in-module at `:241`, mentioned in that module's header at `:19`, and now also named in
`FD/Congruences`. **Remaining follow-up:** build `pchoice-fsim` if a menu-shaped composite
ever needs an `FSim`/`⊑FD` entry in that row. Nothing about `pchoice-cong-FD` itself is
deferred any more.

Not in this matrix: pre-existing congruences at plain (non-divergence-respecting) weak
bisimulation `≈` — `prefix-cong` (`Bisim/Congruence`) and `iter-cong` (`Bisim/IterCong`)
— predate the FD/FSim layers and answer a different, coarser question.

**The `Sep` duality, stated once so it is never conflated:** `CSP.Laws.Bisim.DRCongruence.Sep`
is a **⊤-carrier-only** record (both operands return `⊤`; drives `cong-Par⊤`/`cong-⦀` and,
via `drbisim→≈FD`, `Par-cong-FD`/`⦀-cong-FD` — re-exported from `FD/Congruences` as
`SepDR`). `CSP.Laws.FSim.ParCong.Sep` is a **different, two-carrier** `{R₁ R₂}` record —
only the IMPL operand pair needs it, since an `FSim` proof only ever inverts the impl
composite — re-exported from `FD/Congruences` as `SepPar`. They are not interchangeable
even when both are instantiated at `R = ⊤`: their `stepL`/`stepR` fields quantify over
different label sets. `CSP.Laws.FSim.ParCongRep.sep-from-OffersOnlyᶠ` re-proves, for
`SepPar`, the same alphabet-confinement discharge that `Bisim.DRCongruenceRep`'s
`sep-from-OffersOnly` gives for `SepDR`.

**The one-import index.** `FD/Congruences` re-exports the whole suite above, `FSim/ParCongRep`
included (`⦀Fin-fsim`, `⦀⋆-fsim`, `sep-from-OffersOnlyᶠ`,
`FCell`, `unionAlphaF`, `OffersOnly-⦀⋆-fu`; the `⊑FD` folds `⦀Fin-mono-⊑FD`/`⦀⋆-mono-⊑FD` now
come from `FD/ParallelMonoFD` instead — fact-shaped), **and** the premise types the statements mention
— `SepDR`, `Sep△`, `SepPar`, `Alpha`, `Disj`, `OffersOnly`, `CongCell` — so a caller can name
its own hypotheses through the index rather than importing `Bisim/DRCongruence{,Rep}` and
`FSim/ParCong` separately. `SepDR` keeps its rename; the two `Sep` records stay distinct.

**Completed 2026-08-04 — the index is now build-tested, and covers the addendum work.**
Added to the re-export list: `FSim/SlideCong` (`▷-fsim-R`, `▷-mono-R-⊑FD-fsim`, `▷-τ*-L`,
`▷-wτ-L`, `▷-wev-L`, `▷-Diverges-R`), `FSim/ExtChoiceLift` (`□-τ*-L/-R`,
`□-τ*-L-live/-R-live`, `□-τ*-settle`, `□-wev-L/-R`, `□-wev-LR`, `□-w√-L/-R`,
`□-offer-mono`), `FSim/ExtChoiceCong` (`□-fsim`, `□-mono-⊑FD`, `□Fin-fsim`, `□⋆-fsim`),
`FD/RenameStepRel` (`pchoice-cong-FD`, `MaybeFD` — see the promotion note above), the two
headline names of `FSim/SlideCounterexample` (`¬▷-fsim`, `▷-fsim-claim`, so the negative
result is reachable from the index without its fixed-alphabet witness data), the statement
vocabulary (`DRbisim`, `FSim`, `fsim→⊑FD`, `_≈FD_`, `_⊑FD_`) and the two `OffersOnly`
introduction forms a consumer needs to BUILD the premise (`OffersOnly-Prefix₀`,
`OffersOnly-Skip`). The three FSim modules are re-exported through explicit `using` lists,
not wholesale: each also exports proof scaffolding (`f-sim-▷-R`, `▷-fsim-R-div→`, `ret-fsim`,
`□-fsim-run`, `▷□-fsim-L/-R`, …) and, in `ExtChoiceLift`, LTS helpers with names too generic
for a suite-wide namespace (`τ-live`, `ev-live`, `stable-live`, `τ*-ev-live`,
`τ*-stable-live`). **No name clash arose** and no entry had to be dropped or renamed. There
are no import cycles: none of the newly-indexed modules imports `FD/Congruences`.
`CSP.Examples.FSimTower` now routes every suite name it uses through the index instead of
importing `FSim/IChoiceCong`, `FSim/HideCong`, `FSim/ParCongRep`, `Bisim/DRCongruenceRep`,
`Semantics/FailureSim` and `Semantics/FailuresDivergences` directly — its proof bodies are
unchanged, so the "one import" claim is now something the build checks rather than an
assertion. It still imports `Process_Trees` and `CSP.Operators` directly (process SYNTAX,
not congruence results; the index opens `CSP.Operators` non-publicly on purpose).

### Addendum (2026-08-03, later the same day) — `□`/`▷` FSim congruences

Landed after the consolidated table above was first written, closing two of its ❌
cells; recorded here as an addendum rather than folded into the numbered task list,
since it postdates that list.

- **`Semantics/FailureSim.agda`** gained two lemmas that `□-fsim` (below) is built on:
  `div-prepend-τ*` (a finite τ-chain in front of a divergence is still a divergence) and
  `fsim-τ*-prepend : t₂ ─[τ*]─► t₂′ → FSim R t₁ t₂′ → FSim R t₁ t₂` — "the spec may be
  lazy": an `FSim` survives PREPENDING τ's to the SPEC side. Both `--safe`-clean.
  **`fsim-τ*-prepend`/`div-prepend-τ*` are the LINCHPIN that lets `□-fsim` avoid ever
  invoking the refuted two-sided `▷` congruence**: `□-fsim`'s proof carries the spec's
  owed τ*-runs as debt and discharges them only through these two lemmas, so the spec
  is never itself forced into a `▷`-shaped residual at a point where the (false)
  two-sided `▷`-congruence would be needed.
  - Two hand-rolled copies of the same lemma **predate this hoist and were NOT removed
    by it** — verified against source, so this corrects rather than merely repeats the
    original hoist claim: `CSP.Laws.FSim.BindCong.div-prepend-τ*`
    (`BindCong.agda:203`, same name) and `CSP.Laws.FD.InterruptFD.τ*-Diverges`
    (`InterruptFD.agda:1391`, **different name**, identical definition — its own
    header comment even calls out `BindCong`'s copy by name and explains why it is not
    imported instead: pulling in 1400 lines of interrupt-specific FD theory for four
    lines would cost more typechecking time than it saves). `BindCong.agda` already
    imports `Semantics.FailureSim` for `FSim` itself, so its local copy is a genuine,
    if small, residual duplication; `InterruptFD.agda` does not import the FSim layer
    at all. Neither file was touched here (this change is comment/prose-only).
- **`CSP/Laws/FSim/SlideCounterexample.agda`** proves the TWO-sided `▷`-congruence
  (`FSim R P₁ P₂ → FSim R Q₁ Q₂ → FSim R (P₁▷Q₁) (P₂▷Q₂)`) is **FALSE** — `¬▷-fsim`,
  `--safe`-clean, 0 postulates transitively. Witnesses `P₁ = Tau (Ret tt)`,
  `P₂ = Ret tt`, `Q₁ = Q₂ = a ⟶₀ Stop`. Mechanism: `FSim` legally relates a `sil` node
  to a `ret` node (the spec may already "be there"), and `▷` branches on exactly that
  distinction (timeout vs. live), so a live impl timeout has no matching spec timeout.
  A proved NEGATIVE result, not an unattempted gap — joining §6's `Hide-mono-⊑FD` /
  `Hide-mono-⊑FD-finBr` as a further, independent place where a naive two-sided
  congruence fails. (No uniqueness claim: this is not being called the only place, or
  the only regime, where such a congruence breaks — only that it breaks here too, for
  its own, different reason.)
- **`CSP/Laws/FSim/SlideCong.agda`** — `▷-fsim-R : FSim R Q₁ Q₂ → FSim R (P▷Q₁) (P▷Q₂)`
  (left operand `P` SHARED, right operand varies), unconditional — one-sided **by
  necessity** given the refutation above, not by choice. Plus `▷-τ*-L`, `▷-wτ-L`,
  `▷-wev-L`, `▷-Diverges-R`, `▷-mono-R-⊑FD-fsim`.
- **`CSP/Laws/FSim/ExtChoiceLift.agda`** — weak-lifting machinery for `□` in the
  `FSim` layer's own currency (τ*-runs, weak steps, `Offers` inclusions). The naive
  UNCONDITIONAL τ*-lift is FALSE when the other operand is terminated (`□` resolves
  EAGERLY into a `▷`, Roscoe's R3), so the lift is stated as a disjunction (lands in
  `P′□Q` or in `P′▷Q`) except where a `NonRet` witness is free (the `stab` field, whose
  settle target is stable hence never a `ret`). **Not `--safe`-clean**: `agda --safe
  CSP/Laws/FSim/ExtChoiceLift.agda` fails with two `SafeFlagPostulate` errors
  (`□-Diverges→` and `▷-Diverges→`, both from `CSP.Laws.FD.ExtChoiceDivergence`),
  because that module is reachable — TWICE over — via `CSP.Laws.FD.ExtChoiceFD`
  (imported directly, for `□-offers-L`) and again via `CSP.Laws.FSim.SlideCong`
  (imported for `▷-τ*-L`); neither postulated name is actually USED by this module's
  own proofs (grepped: neither occurs outside its own header comment).
- **`CSP/Laws/FSim/ExtChoiceCong.agda`** — the headline, `□-fsim : FSim R P₁ P₂ →
  FSim R Q₁ Q₂ → FSim R (P₁□Q₁) (P₂□Q₂)`, **two-sided, unconditional, and — unlike
  `Par-fsim` — with NO `Sep`-style side condition at all**: `□` never synchronises, so
  an offer overlap is legal and simply resolves into a real `⊓` (the `evPQ` case of the
  proof), whose branches are the ordinary `⊓-stepL`/`⊓-stepR`, not a side-condition
  premise. Plus `□-mono-⊑FD`, `□Fin-fsim`, `□⋆-fsim` (replicated folds, one line each —
  unlike `⦀Fin-fsim`, no side condition to thread through the fold). USES exactly TWO
  postulates, both from `CSP.Laws.FD.ExtChoiceDivergence`, both only in `div→`:
  `□-Diverges→` (one site, `□-run-div→`) and `▷-Diverges→` (two sites, the S2/S3
  mirrors `▷□-L-div→`/`▷□-R-div→`). Its transitive import closure is now **TIGHT**: one
  postulate-bearing module, `CSP.Laws.FD.ExtChoiceDivergence`, which declares exactly
  those two postulates and nothing else — so every postulate reachable from this module
  is one it genuinely uses. It formerly carried TEN, the other nine pulled in by a single
  `CSP.Laws.Stability.Closure` edge, borrowed there for the two constructive facts
  `stable-□`/`□-stable-elim`; those moved to `CSP/Laws/Stability/ExtChoice.agda` (see the
  stability section above). It is still not `--safe` — `agda --safe` reports two
  `SafeFlagPostulate` errors, one per genuinely-used name — and that residue is
  irreducible short of discharging the two classical `Diverges→` inversions themselves.

### Addendum (2026-08-04) — binary alphabetised parallel `_⟦_∥_⟧_` `FSim` congruence

Closes the `αpar` cells of the consolidated table above. Four modules landed:

- **`Semantics/FailureSim.agda`** gained `fsim-sil-factor : PTree.force t₂ ≡ sil t₂′ →
  FSim R t₁ t₂ → FSim R t₁ t₂′` — "a `sil`-headed spec's simulation factors through its
  unique τ-successor", the converse direction to `fsim-τ*-prepend` (2026-08-03 addendum
  above): together the two say a spec's leading `sil` chain is `FSim`-invisible. Built on
  three small generic inversions also added there: `sil-no-ev` (a `sil` node performs no
  visible step), `sil-τ*-split` (a τ*-run out of a `sil` node either stands still or
  factors through the successor), `sil-div-factor` (an infinite τ-run out of a `sil` node
  continues out of the successor). All four are `--safe`-clean, 0 postulates.
- **`CSP/Laws/AlphaParallelLift.agda`** (925 lines, 0 postulates) — the αpar analogue of
  `FSim/ParCong`'s τ*/weak lifts plus the stability/offer layer of `FD/ParallelRefusals`/
  `FD/ParallelMonoFD`: `NoSil` (`t.force ≢ sil u`) with intros `noSil-ret`/`-react`/
  `-stable`/`-of-ev`, the one-sided lifts `αpar-τ*-L`/`-R`, the two-operand flush
  `αpar-flush` (+ `-stable`/`-retL`/`-retR`/`-retLR` endpoint corollaries), weak lifts
  `αpar-wsolo-L`/`-R`/`αpar-wsync`/`αpar-w√`, stability classification
  (`αpar-stable-normal`) and offer monotonicity (`αpar-offer-mono`). **No `Sep`-style
  overlap-alphabet side condition is needed**: `αpar` routes every visible event
  determinately by alphabet membership, so its inversion datatype `αVisR` has no
  `evBoth` analogue (contrast `Par-fsim`'s `Sep`). **No `DecEq R`** is needed either.
- **`CSP/Laws/FD/AlphaParallelDivergence.agda`** — `αpar-Diverges-L`/`-R` (constructive,
  `NoSil`-gated coinductive lifts of an operand's livelock) plus the module's ONE
  postulate, the König step `αpar-Diverges→ : Diverges (P ⟦A∥B⟧ Q) → Diverges P ⊎
  Diverges Q`, certified sound from the single `dne` of `CSP.Laws.ClassicalFromLEM` as
  **Derivation 11** (`αpar-no-inf`, a `τ-Acc`/`DAcc` well-founded recursion — STRICTLY
  simpler than `Par`'s Derivation 2/5 argument, since `αpar-τ-step-inv` gives only P's τ
  or Q's τ: no both-offer overlap node, no third τ-shape to dispatch).
- **`CSP/Laws/FSim/AlphaParCounterexample.agda`** (`--safe`-clean, 0 postulates) proves
  the UNCONDITIONAL two-sided `αpar` `FSim` congruence FALSE (`¬αpar-fsim`), **and the
  one-sided variant FALSE in BOTH orientations** (`¬αpar-fsim-R`) — a SHARPER result
  than `▷`'s (where the one-sided form `▷-fsim-R` genuinely holds, unconditionally).
  Witnesses `P₁ = P₂ = ea ⟶₀ Stop`, `Q₁ = div ⊓ div`, `Q₂ = div`, `A = all`, `B = ∅ES`;
  failing field `fwd.on-ev` (the impl's solo `ea` step has no spec match). Mechanism:
  `αpar`'s `force` gives a `sil`-headed operand ABSOLUTE priority, masking the other
  operand's visible offers; finitely many masking τ's are absorbed by weak matching, but
  the masking becomes PERMANENT when the spec operand's leading `sil` chain is infinite
  (spec = `div`), and `FSim` legitimately relates a `react`-headed divergence (`div ⊓
  div`) to `div`. Since `P₁ = P₂` literally in the witness, the SAME pair refutes the
  one-sided law with the shared operand on the left, and the mirror witness refutes it
  with the shared operand on the right — **`▷-fsim-R`'s dodge (the shared operand's
  `force` never changes, so it can legally stand still) is unavailable for `αpar`,
  because `αpar` inspects BOTH operand heads**, not just one. A bare `NoSil` invariant
  cannot repair this either: `NoSil` is not preserved by τ-stepping, so it collapses
  into divergence-freedom rather than surviving as a separate, weaker fix.
- **`CSP/Laws/FSim/AlphaParCong.agda`** (0 local postulates) — the positive result:
  ```agda
  αpar-fsim-df : ∀ {ℓr ℓs} {R : Set ℓr} {S : Set ℓs} (A B : EventSet)
                 {P₁ P₂ : PTree E (ExtI E) R} {Q₁ Q₂ : PTree E (ExtI E) S}
               → τ-AccReach P₂ → τ-AccReach Q₂
               → FSim R P₁ P₂ → FSim S Q₁ Q₂
               → FSim (R × S) (P₁ ⟦ A ∥ B ⟧ Q₁) (P₂ ⟦ A ∥ B ⟧ Q₂)
  ```
  plus `αpar-mono-⊑FD-fsim-df`. The side condition is **`τ-AccReach`, not `τ-Acc`** — the
  proof drains both spec operands' leading `sil`s at EVERY matched step (not just at the
  two roots), via the well-founded induction `αdrain` (bounded by `τ-Acc`, carried across
  each `sil` node by `fsim-sil-factor` above), so accessibility is needed after visible
  steps too, which `τ-Acc` alone does not give. The condition constrains the SPEC
  operands ONLY: `fwd` and `stab` are fully constructive; `div→` inherits exactly one
  postulate, `αpar-Diverges→`, entering nowhere else. `_⟦_∥_⟧_` fixes `merge = _,_` — it
  takes no `merge` argument, and the two operand carriers may sit at different universe
  levels, unlike `Par-fsim`'s single-carrier `Par-stable-normal`.
- **Honest scope caveat.** In the refuting witness above, BOTH composites diverge
  (`impl-div`, `spec-div`): both are `⊥` in the failures-divergences model, so `⊑FD`
  holds trivially between them. What the counterexample refutes is the **`FSim`
  step-wise congruence**, not the `⊑FD`/FD-level law — `FSim`'s `fwd` obligation is not
  weakened by a diverging specification the way `⊑FD` is. This is the same
  divergence-freedom-as-necessary-condition pattern as `HideMonoFD`/`Hide-mono-⊑FD-df`,
  applied at a different operator (no uniqueness claim: this is not the only place, or
  the only regime, where a naive two-sided congruence needs such a side condition).
- **Re-exported from `FD/Congruences`**: `αpar-fsim-df`, `αpar-mono-⊑FD-fsim-df`, the `NoSil`
  vocabulary, `τ-Acc`/`acc`/`τ-AccReach` (`Semantics.DivergenceFree`, now re-exported for
  the first time so a caller can name this side condition through the index), and the
  two headline refutations `¬αpar-fsim`/`¬αpar-fsim-R` (+ their statement types). No
  import cycle, no name clash.

### Addendum (2026-08-04, later the same day) — throw `⟦A▷` (`_⟦_▷_`) `FSim` congruence

Closes the ❌/❌ cells left in the throw row above. **The pre-existing "Interrupt /
throw △" row was misleading**, not a real throw entry — see the correction note above
the table; this addendum supplies the genuine one. Two commits: `77c81a7` (hoist),
`a4ad5b9` (congruence).

- **Hoist (`77c81a7`).** Six lemmas — `Θ-τ-lift-P`, `Θ-Diverges-L`, `Θ-div-step`,
  `Θ-Diverges→`, `Θ-throw-step`, `Θ-pass-step` — moved BYTE-IDENTICAL out of the
  (872-line, pre-hoist) FD law-suite `CSP/Laws/FD/ThrowFD.agda` into a new "Part 4" of
  `CSP/Laws/Traces/TraceLawsThrowInterrupt.agda` (verified at source:
  `TraceLawsThrowInterrupt.agda:193-295`). `ThrowFD.agda` re-exports all six `public`
  (`ThrowFD.agda:57-61`), so its own API is unchanged and no consumer needed edits. The
  point is the IMPORT CLOSURE: `ThrowFD` pulls in the classical `Semantics.DRImpliesFD`,
  whereas `TraceLawsThrowInterrupt` does not and is itself `agda --safe`-clean (verified
  directly) — which is what lets the FSim-layer congruence below stay `--safe` too.
  Mirrors the earlier `stable-□` hoist into `CSP/Laws/Stability/ExtChoice.agda` (§16
  table above) in spirit: move the constructive kernel somewhere with a smaller import
  closure, re-export from the original home so nothing downstream breaks.
- **`CSP/Laws/FSim/ThrowCong.agda`** (298 lines, 0 local postulates; commit `a4ad5b9`) —
  the headline result:
  ```agda
  Θ-fsim : (A : EventSet) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
         → FSim R P₁ P₂ → FSim R Q₁ Q₂ → FSim R (P₁ ⟦ A ▷ Q₁) (P₂ ⟦ A ▷ Q₂)
  Θ-mono-⊑FD : (A : EventSet) {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
             → FSim R P₁ P₂ → FSim R Q₁ Q₂ → (P₂ ⟦ A ▷ Q₂) ⊑FD (P₁ ⟦ A ▷ Q₁)
  ```
  **TWO-SIDED and UNCONDITIONAL** — no divergence-freedom hypothesis, no `Sep`-style
  separation condition, no side condition of any kind, and no `DecEq R`. Also
  `Θ-τ*-L`, the weak lifts (`Θ-wev-fire`/`Θ-wev-pass`/`Θ-wτ`/`Θ-wev-√`), and the
  composite↔body `Offers`/`isStable` elimination+introduction pair
  (`Θ-stable-elim(-at)`/`Θ-stable-intro`/`Θ-offer-mono`) that the `stab` field needs.
- **Why throw is unconditional where `▷`/`αpar` are not.** `force (P ⟦ A ▷ Q)` inspects
  ONLY the body `P` (verified, `CSP/Operators.agda:388-392`: `_⟦_▷_` cases on
  `PTree.force P` alone), so the composite's whole LTS is a function of the body's LTS:
  the composite's τ-space IS the body's τ-space (no extra slide-τ ⇒ no `sil`-masking,
  the mechanism that kills the two-sided `▷`/`αpar` congruences), and the composite's
  visible offers are exactly the body's offers with only the TARGET decided by `A .dec`
  (fire → `Q`, pass → continue under the throw) — so no both-offer overlap can arise
  and no `Sep` hypothesis is ever needed. The handler is dormant until a visible
  `A`-event fires the throw, the trigger event is consumed, and the handler starts at
  once — so a spec body weakly matching the SAME label is forced into the SAME `A .dec`
  branch and lands on `Q₂`, discharged by the `FSim R Q₁ Q₂` hypothesis directly, with
  no invariant extension and no corecursion in that arm.
- **`Θ-Diverges→` is STRUCTURAL — no König step, no postulate.** `ThrowCong.agda`'s
  `div→` field (`Θ-fsim-div→`) is two lines: project the composite's infinite τ-path to
  the body's (`Θ-Diverges→`), transfer with the body's own `div→`, re-lift
  (`Θ-Diverges-L`) — no search, no bar induction. Contrast the FOUR postulated
  `*-Diverges→` siblings that gate the other operand-deconstructing FSim congruences:
  `△-Diverges→` (`FD/InterruptDivergence`, gates `FD/Congruences`'s `△-fsim` — the
  DIFFERENT `_△_` operator, not throw), `□-Diverges→`/`▷-Diverges→`
  (`FD/ExtChoiceDivergence`, gate `ExtChoiceCong`/`SlideCong`), `Par-Diverges→`
  (`FD/ParallelDivergence`, gates `ParCong`, and reached — though not necessarily used —
  by `HideCong`), `αpar-Diverges→` (`FD/AlphaParallelDivergence`, gates `AlphaParCong`).
  Throw needs none of them and adds **no new postulate to the inventory** — see
  postulate-inventory item (f) below.
- **`--safe` sweep across the FSim operator-congruence suite (verified by direct
  `agda --safe` invocation on each module, 2026-08-04).** Of the seven modules that
  state a top-level operator's FSim congruence (as opposed to a weak-lift/helper module
  such as `ExtChoiceLift`, or a counterexample module), exactly **two** pass
  `agda --safe` cleanly:

  | Module (operator) | `agda --safe` | First-reported blocking postulate |
  |---|---|---|
  | `FSim/IChoiceCong` (`⊓`, prefix) | ✅ pass | — |
  | `FSim/ThrowCong` (`⟦A▷`) | ✅ pass | — |
  | `FSim/ExtChoiceCong` (`□`) | ❌ fail | `□-Diverges→` **and** `▷-Diverges→` (`FD/ExtChoiceDivergence`) |
  | `FSim/SlideCong` (`▷`) | ❌ fail | `□-Diverges→` **and** `▷-Diverges→` (`FD/ExtChoiceDivergence`) |
  | `FSim/ParCong` (`Par`/`∥`/`⦀`) | ❌ fail | `offer-LEM` (`FD/ParallelRefusals`) |
  | `FSim/HideCong` (`∖`) | ❌ fail | `Par-Diverges→` (`FD/ParallelDivergence`, reached transitively — `HideCong`'s own direct classical inputs, per §15(c) above, are `Diverges-LEM`/`¬DivModA→MAcc`) |
  | `FSim/AlphaParCong` (αpar) | ❌ fail | `αpar-Diverges→` (`FD/AlphaParallelDivergence`) |

  The common thread matches each module's own header: `⊓`/prefix never inspect an
  operand's `force` at all (their composite is a fixed `react` node), and throw
  inspects only the BODY's `force` with a structural divergence bridge; every other
  operator DECONSTRUCTS a live operand and pays for it with a postulated `Diverges→`
  inversion (a König-style step) somewhere in its closure. **This is not a uniqueness
  claim** ("throw is the only/first ... " phrasing has been wrong four times already in
  this campaign, see the postulate-provenance section above) — it states the measured
  set, dated, and nothing stronger: throw is the first `--safe`-clean congruence for an
  operator that DECONSTRUCTS a live operand, since `⊓`/prefix (the other clean case)
  never do.
- **No consumer needs `⊑FD`.** The only user of `_⟦_▷_` repo-wide is
  `CSP/Examples/ThrowInterruptSanity.agda` (verified by grep across `src/`), and it is
  purely `≡`-level `force`-reduction sanity checks
  (`check-throw-fires`/`check-throw-passes`/`check-throw-skip`), not an `FSim`/`⊑FD`
  consumer. So this result's value is recorded honestly as CLOSING a ❌ cell of the
  coverage matrix (completeness of the FSim congruence suite), not as unblocking any
  existing proof.
- **Re-exported from `FD/Congruences`**: `Θ-fsim`, `Θ-mono-⊑FD`, and the weak lifts
  `Θ-τ*-L`/`Θ-wτ`/`Θ-wev-fire`/`Θ-wev-pass`/`Θ-wev-√` (explicit `using`, following the
  index's existing selective-export discipline — the composite↔body stability/offer
  scaffolding stays internal, the same treatment `ExtChoiceCong`'s own S1-S4 helpers
  get). No name clash arose and none had to be resolved by renaming. No import cycle:
  `ThrowCong` does not import `FD/Congruences`. `agda CSP/Laws/FD/Congruences.agda` and
  `agda CSP/Examples/FSimTower.agda` both exit 0 after the addition.

### The two regimes — `⊑FD` facts and `FSim` witnesses do not mix

`⊑FD` and `FSim` are **separate regimes**, joined **one-way only** by
`fsim→⊑FD : FSim R Q P → P ⊑FD Q`. There is no route back: `FSim` completeness
(`⊑FD → FSim`) is classical and deliberately **out of scope** (see "Suggested next
steps" item 5 below) — it would need finite-branching and convergence hypotheses that
`FSim` was built precisely to avoid assuming. Consequently a `⊑FD` fact can never be fed
into an `FSim`-shaped proof obligation.

**Why hiding is the crux.** Hiding is where a refinement built from bare `⊑FD` FACTS
breaks down: unconditional `Hide-mono-⊑FD` is FALSE (§6, `HideMonoFD` carries the
counterexample — Roscoe's known N-model hiding unsoundness under unbounded
nondeterminism), so from `P ⊑FD Q` alone one cannot conclude `(P∖A) ⊑FD (Q∖A)`; only
`Hide-mono-⊑FD-df` survives, under a divergence-freedom side condition **on the REFINED /
RIGHT (implementation) operand's hide** — `∀ {s} → ¬ divergences (Q∖A) s`, where `Q` is the
right-hand operand of `P ⊑FD Q` (`FD/HideMonoFD.agda:268-270`; the module's own comment at
`:243` calls it "the refined side's hide"). **It is NOT a hypothesis about the spec `P`** —
earlier revisions of this note and of the §17 coverage table said "the hidden spec", which
was wrong: the spec side is unconstrained, and the side condition bites precisely because
it is the *implementation* composite (the ~150-leaf mux) whose hide one must show
divergence-free. And **every top-level refinement statement in this repo hides
internal/message events** — the mux shape is always `(⦀Fin n leaf) ∖ msgs` or similar.

What carries an FD-strength refinement through hiding unconditionally is a **witness**, and there are two
independent routes here — neither recoverable from a bare `⊑FD` fact:

- **one-way:** `Hide-fsim` (unconditional — its `Diverges` correspondence only needs
  the FORWARD direction, which hiding's τ-introduction always preserves), then
  `fsim→⊑FD`. `⊑FD → FSim` completeness is out of scope (see "Suggested next steps"
  item 5 below), so a `⊑FD` fact can never be substituted for an `FSim` witness.
- **two-way:** `cong-∖` (unconditional, `Bisim/DRCongruence`), then `drbisim→≈FD` —
  i.e. `hide-cong-FD` (`FD/Congruences`). Needs the strictly stronger `DRbisim` fact.

So a composite refinement must carry a witness through the hide rather than a `⊑FD`
fact, and cash out once at the top. FSim is the cheaper witness when only refinement
(not equivalence) is wanted: three obligations (`fwd`/`stab`/`div→`) instead of
`DRbisim`'s four, and `Par-fsim` needs `Sep` on the impl operand pair only.

**What the weaker orders actually give — read the two types.** Four earlier revisions of
this paragraph asserted that `⊑F⊥` composes through hiding unconditionally "via
`Hide-mono-fail`". **That was false**, and the corrected statement is *stronger*:

- **`⊑T` does compose through hiding unconditionally.**
  `Hide-mono-⊑ᵀ : (A : EventSet) {P Q} → P ⊑T Q → (P∖A) ⊑T (Q∖A)`
  (`Traces/TraceLawsHide.agda:314-315`), no side condition.
- **`⊑F⊥` does not.** `Hide-mono-fail` (`FD/HideMonoFD.agda:225-227`) is the unconditional
  stable-**failure transfer**, *not* `⊑F⊥` monotonicity:
  `P ⊑F⊥ Q → failures (Q∖A) s X → failures⊥ (P∖A) s X`. Its **input** is `failures`, not
  `failures⊥`. Since `failures⊥ P s B = failures P s B ⊎ divergences P s`
  (`Semantics/FailuresDivergences.agda:73`), it discharges only the `failures` disjunct and
  says nothing about the `divergences` one — so it is not `(P∖A) ⊑F⊥ (Q∖A)`. Unconditional
  `⊑F⊥` monotonicity through hiding **also fails**, by the same divergence-chaos mechanism
  that kills `⊑FD`: `HideMonoFD`'s header states it at :24 ("via divergence-chaos at `[]`
  even `(P′∖{h}) ⊑F⊥ (Q∖{h})` fails for a `b`-offering variant `P′`"), and the proof of
  `Hide-mono-⊑FD-df` corroborates it — it handles the `failures` input via
  `Hide-mono-fail` but refutes the `divergences` input **from its side condition**
  (`fF⊥ (inj₂ dv) = ⊥-elim (hdf dv)`, `HideMonoFD.agda:256` — `:255` is the neighbouring
  `inj₁` clause, which *is* discharged by proof), a line that would be unnecessary if `⊑F⊥`
  were unconditionally hide-monotone.
- **`⊑F` — Roscoe's *stable-failures* order — DOES compose through hiding
  unconditionally.** `Hide-mono-⊑F : (A : EventSet) {P Q} → P ⊑F Q → (P∖A) ⊑F (Q∖A)`
  (`FD/HideMonoFD.agda:255`, four lines, no side condition). Read the type to see why this
  does not contradict the `⊑F⊥` bullet above: `_⊑F_` (`Semantics/Failures.agda:42-43`) is
  `∀ s X → failures Q s X → failures P s X` — *both* ends are bare `failures`, whereas
  `_⊑F⊥_`'s ends are `failures⊥ = failures ⊎ divergences`
  (`Semantics/FailuresDivergences.agda:73`). The divergence-chaos mechanism that kills
  `⊑F⊥` and `⊑FD` through a hide needs that `divergences` disjunct to break; `⊑F` has none
  to break. The trade is honest and is exactly the standard one: `⊑F` says nothing about
  divergence, so a divergent implementation refines everything at `⊑F` — but if the
  property being proved is about *stable refusals* (as liveness properties are), `⊑F`
  carries its full content.

**The stable-failures regime — a third route, and the only one that crosses a hide with a
bare FACT.** As of 2026-08-05 the `⊑F` order has both halves needed to assemble a composite
refinement and then push it through a hide, both **unconditional** and both fact-shaped:

- `ParallelMonoFD.Par-mono-⊑F` + `∥`/`⦀`/`⦀Fin`/`⦀⋆`/`∥⁺`/`∥Fin` folds (Layer 10) — build
  the composite;
- `HideMonoFD.Hide-mono-⊑F` — cross the hide;
- `⊑F-trans` / `⊑F-refl` (`Semantics/Failures.agda:51-54`) — chain and terminate.

This does **not** weaken the "carry a witness, not a fact" discipline for `⊑FD`: the two
regimes above are about FD-strength refinement, and nothing here recovers `⊑FD` through a
hide. What it does is give a *third* regime whose strength (traces + stable refusals) sits
strictly between `⊑T` and `⊑FD`, and which — unlike `⊑FD` — needs neither an `FSim`/`DRbisim`
witness nor a divergence-freedom certificate on a ~150-leaf composite. Use it when the
property is a stable-refusal (liveness) property and divergence-freedom of the
implementation is not itself part of the claim; use `FSim` when divergence must be tracked.
Classical cost: `offer-LEM` only (via `Par-stable`), already incurred by `Par-mono-⊑FD` and
dne-certified in `ClassicalFromLEM` — no new postulate.

**Which component breaks — both, and by different witnesses.** An earlier revision said
only "the component that breaks is `failures⊥`'s `divergences` disjunct". That is right for
the `⊑F⊥` failure but it under-reports the `⊑FD` one, and a reader could wrongly infer that
`⊑D` is fine. Attributing each precisely:

- **`⊑D` breaks**, and the **canonical** counterexample pair breaks exactly it: with
  `Q = μX.h→X` and `P = ⊓ₙ hⁿ;STOP`, `Q∖{h}` diverges while `P∖{h}` has no infinite τ-path
  (infinite branching defeats König), so `(P∖{h}) ⊑D (Q∖{h})` **FAILS**
  (`HideMonoFD.agda:24`). This is the `⊑FD` failure. Correspondingly
  `Hide-mono-⊑FD-df` refutes the divergence obligation from its side condition in **both**
  components — `fF⊥ (inj₂ dv)` at `:256` *and* `fD dv` at `:258`.
- **`⊑F⊥` breaks** on `failures⊥`'s `divergences` disjunct, and needs the `b`-offering
  **variant** `P′` of that same pair, via divergence-chaos at `[]`.

Both are the one divergence-chaos phenomenon, which is why the failure takes down `⊑F⊥` and
`⊑FD` together, and why carrying a **witness** (`FSim` or `DRbisim`) rather than a
refinement **fact** is what gets a composite through a hide.

**Consequence for this campaign's own deliverables:** the FOUR surviving `⊑FD`-mono
wrappers that `FD/LoopMonoFD` used to hold (`iter`/`loop`/`loopc`/`while`) were therefore
**leaf-level results only** — which is why they were replaced 2026-08-04 by the fact-shaped
`FD/IterMonoFD`, emptying and deleting that module. (Its bind half — four more wrappers,
plus `loop0-mono-⊑FD-fsim` — had already been
retired 2026-08-04 in favour of FACT-SHAPED laws in `FD/BindMonoFD` /
`FD/IterateMonoFD`, and those are NOT leaf-level: a fact-shaped law consumes a `⊑FD`
premise from any source, so it composes freely with other `⊑FD` facts. The hide
obstruction below is unchanged — no `⊑FD` chain, fact-shaped or not, crosses a hide.)
They are correct and directly usable when the loop or bind operator IS the entire
refinement being stated, but they must not be used partway up a composite: `Par-fsim`,
`Hide-fsim` and `⦀Fin-fsim`/`⦀⋆-fsim` all consume `FSim` **witnesses**, not `⊑FD`
**facts**. The discipline is: build the composite entirely at `FSim`, and cash out
**once**, at the very top, via `fsim→⊑FD`. `CSP.Examples.FSimTower` demonstrates exactly
this route — an assembled `⊑FD` refinement of a two-leaf `(⦀Fin 2 ·) ∖ msgs` tower,
`per-leaf ⊓-refine-fsim → ⦀Fin-fsim → Hide-fsim → fsim→⊑FD` (one cash-out, at the top).
**Note on what is and is not certified there:** the assembled `⊑FD` refinement itself
IS certified (typechecks, no postulate, no hole). Its **strictness** — that the
refinement is proper, not a disguised equivalence — is argued informally in the module
(the `⟨out i, out i⟩` trace-separation argument) and is **not** formalised as an Agda
`¬ (impl ⊑FD spec)` proof; treat that half as prose, the same status as the
`Pinf ⊑FD Qh` half of `HideMonoFD`'s classic counterexample.

### Postulate provenance across the FSim/FD congruence suite

Verified against source (not transcribed from any plan draft — two errors in the
original campaign plan's provenance text were caught and corrected during Task 4/5):

- **Loop family** (`iter-fsim`/`loop-fsim`/`loop0-fsim`/`loopc-fsim`/`while-fsim`, and —
  since 2026-08-04 — the fact-shaped `FD/IterMonoFD` laws too, which route through the
  same `iter-div-split`): classical dependency is **both**
  `Diverges-LEM` (`FD/FDTransfer`) **and** `¬DivModA→MAcc` (`FD/HideDivergence`),
  composed inside `iter-div-split` (`FSim/LoopCong.agda:378-383`; imports at `:143`
  (`¬DivModA→MAcc`) and `:144` (`Diverges-LEM`), uses at `:383` and `:379`). (`Par-Diverges→`
  is **not** a dependency of this family — an earlier plan draft claimed it was; grepped,
  no occurrence in `LoopCong.agda`.)
- **`Bind-fsim` / `bindNoτ-fsim` / `bindκ-fsim`** (`FSim/BindCong`): **postulate-free**.
  The bind König split is a **caller-supplied explicit hypothesis** (`BindDivSplit` /
  `NoTauRoot` / the pure-continuation witness), not an inherited axiom
  (`BindCong.agda:93`; no `postulate` keyword anywhere in the file).
- **`>>-fsim`** (`FSim/BindCong`): genuinely inherits `>>-Diverges→`
  (`FD/SeqDistR.agda:325`), used inside `>>-split` at `BindCong.agda:599`.
- **`>>=-mono-⊑FD` / `bindNoτ-mono-⊑FD` / `bindκ-mono-⊑FD`** (`FD/BindMonoFD`,
  2026-08-04): `Diverges-LEM` (`FD/FDTransfer`) and **nothing else**, used exactly once,
  in `term-transfer` — `⊑FD` sees TERMINATION only through the `√` tick (a `ret` state is
  not stable, hence no failure of its own), and settling the spec's `√`-extended empty-ban
  failure at a τ-normal form is the classical step. The bind König step is **not**
  inherited: explicit `BindDivSplit k₂` for the general bind, constructively discharged
  (`bind-noτ-split` / `pure→NoTauRoot`) for the two restricted forms.
- **`>>-mono-⊑FD`** and the folds **`⨾⋆-mono-⊑FD` / `⨾Fin-mono-⊑FD`** (`FD/BindMonoFD`):
  `Diverges-LEM` **plus** `>>-Diverges→` via `>>-split` — exactly `>>-fsim`'s debt. The
  two folds add nothing of their own (empty-based inductions over `>>-mono-⊑FD`).
- **`iter-mono-⊑FD` / `loop-mono-⊑FD` / `while-mono-⊑FD`** (`FD/IterMonoFD`, 2026-08-04):
  `iter-div-split` (`FSim/LoopCong`), i.e. `Diverges-LEM` + `¬DivModA→MAcc` — the loop
  family's usual pair — for the `⊑D` half only, plus `bindκ-mono-⊑FD`'s `Diverges-LEM` for
  `loop`/`while`. It does **NOT** inherit `IterateFD.loop-Diverges→`: that postulate is
  `loop0`-specific, so the GENERAL `iter` law assumes strictly LESS than the `loop0`
  specialisation `loop0-mono-⊑FD` that predates it (`loopc-mono-⊑FD`, being definitionally
  the same law, does inherit it). The `⊑F⊥` half needs no classical ingredient of its own —
  the body-side reconstruction goes through the `√` tick, which is structural.
- **`renameInv-mono-⊑D` / `-⊑F⊥` / `-⊑FD` and the `renameMap` trio** (`FD/RenameMonoFD`,
  2026-08-04): **NONE**, and structurally so rather than by argument — the τ-spaces of
  `P` and `P ⟦inv⟧ⁱ` correspond one-for-one, so both divergence directions are plain
  corecursive projections and the failure reconstruction is structural. The only
  hypothesis anywhere is `RenTight`, a level artefact, discharged for `renameMap`.
- **`Par-fsim` / `⦀-fsim` / `⦀Fin-fsim` / `⦀⋆-fsim`**: the FSim regime's real classical
  debt here is `Par-Diverges→` (`FD/ParallelDivergence.agda:56`, dne-certified), entering
  through `Par-fsim`'s `div→` field.
- **`Par-mono-⊑FD`** (and `∥`/`⦀`/`⦀Fin`/`⦀⋆` corollaries, `FD/ParallelMonoFD`): `offer-LEM` (`FD/ParallelRefusals.agda:162`),
  `Par-Diverges→` (`FD/ParallelDivergence.agda:56`) and `Diverges-LEM` (`FD/FDTransfer`) —
  **all three reached transitively, on equal footing**: none of the three names occurs
  anywhere in `ParallelMonoFD.agda` outside its own header comment, and that comment
  mentions all three on **one line alone** (`:27` as of 2026-08-04) (`-- (offer-LEM, Par-Diverges→, Diverges-LEM — each
  certified in ClassicalFromLEM).`) — an earlier revision also cited `:7`, which in fact
  names `Par-reach-div`, an ordinary definition and not one of the three postulates; the
  route is `ParallelMonoFD`'s single `FD/ParallelDivergence` import (`:65` as of
  2026-08-04), which brings in only `Par-reach-div`/`Par-div-intro`. The FOUR replicated
  folds add nothing to this provenance: `⦀Fin-mono-⊑FD`/`⦀⋆-mono-⊑FD` are inductions over
  `⦀-mono-⊑FD` with `⊑FD-refl Skip` at the base, and `∥⁺-mono-⊑FD`/`∥Fin-mono-⊑FD`
  (Layer 9) are inductions over `∥-mono-⊑FD` whose (non-empty) bases are operand
  hypotheses. (An
  earlier revision attached the "reached transitively" qualifier to `Par-Diverges→` alone,
  implying the other two were direct. They are not.)
- **`Par-mono-⊑F`** (and its six folds, `FD/ParallelMonoFD` Layer 10, 2026-08-05):
  `offer-LEM` (`FD/ParallelRefusals.agda:162`) **and nothing else** — strictly LESS than
  `Par-mono-⊑FD` above, which is the point of the layer. `Par-Diverges→` and `Diverges-LEM`
  are *not* reached: the `⊑F` proof touches only `Par-failures-elim`/`Par-failures-intro`
  (`FD/ParallelFailures`, which imports neither `FD/ParallelDivergence` nor
  `FD/FDTransfer`), `Par-stable`/`Par-stable-termL/R` (`FD/ParallelRefusals`, where
  `offer-LEM` lives), and the two purely structural `FDTransfer` helpers
  `term→√failure` / `√-run-split-gen` used by `op-transfer-ret-F` (neither uses
  `Diverges-LEM`). `FD/FDTransfer` and `FD/ParallelDivergence` remain imported by the
  module as a whole, for Layers 1-9 — the claim here is about the `⊑F` laws' own
  dependency cone, not the file's import list. Same for `Hide-mono-⊑F`
  (`FD/HideMonoFD.agda:255`): **ZERO postulates**, as for the rest of that module.
- **`Hide-fsim`** (`FSim/HideCong`): `Diverges-LEM` (`FDTransfer`) and `¬DivModA→MAcc`
  (`HideDivergence`), both directly imported, at `HideCong.agda:124` and `:122`
  respectively.
- **`⊓-fsim` / `prefix-fsim` / `⊓-refine-fsim` / `⊓-refine-⊑FD`**
  (`FSim/IChoiceCong`; its `⊓-mono-⊑FD`/`prefix-mono-⊑FD` wrappers were retired 2026-08-04): **none** — direct builds, deliberately not routed through
  `drbisim→fsim` to avoid its postulate. It is **among** the FSim-layer modules that are
  transitively clean of `Semantics.DRImpliesFD`. (Re-measured by computing the transitive
  import closure of all **eleven** current `CSP/Laws/FSim/` modules: the clean set is
  `IChoiceCong`, `SlideCong`, `ExtChoiceLift`, `ExtChoiceCong`, `HideCounterexample` and
  `SlideCounterexample` — the last two **refutations** (`¬fsim-Pinf-Qh`, `¬▷-fsim`), not
  congruences; `BindCong`, `HideCong`, `LoopCong`, `ParCong`, `ParCongRep` do reach it.
  Successive earlier revisions of this line said "the only FSim-layer module" and then "the
  only FSim-layer **congruence** module"; **both are now false** — the second went stale the
  moment `SlideCong`/`ExtChoiceLift`/`ExtChoiceCong` landed, which is a standing warning
  against phrasing this cell as a uniqueness claim at all. Note also that *reaching*
  `DRImpliesFD` is not the same as *using* its postulate; see each module's own banner.)
- **`＆-mono-⊑FD` / `◁▷-mono-⊑FD` / `Output-mono-⊑FD`** (`FD/DerivedMonoFD`, 2026-08-04):
  **none, certified** — `agda --safe` exits 0 on the module, so its whole closure is
  postulate-free. See inventory row (g) for the two choices that keep it so
  (`stable-no-τ` from `Semantics/Stability`, not `Semantics/DRImpliesFD`; force-equality
  crossed via `FD/BindFD`'s `cross-*-force-eq`, not via `drbisim→≈FD`).
- **`⨅⁺-mono-⊑FD` / `⨅Fin-mono-⊑FD`** (`FD/IChoiceMonoFD`, 2026-08-04): **none** —
  inductions over `⊓-mono-⊑FD`, which is itself postulate-free (a union transfer over
  `FDLawsIChoiceAssoc`'s constructive decompositions).
- **`¬-divergent→normal`** (`Semantics.DRImpliesFD`'s one postulate, declared and used
  in its home module) has exactly **one** consumer beyond that home module, repo-wide:
  `FD/FDTransfer.agda:42-43` (imported), used at line 210.
- All of the above are certified sound from the single `dne` in
  `CSP.Laws.ClassicalFromLEM`.

### The `DRImpliesFD` transitive-reach erratum

The original campaign constraint — "modules under `CSP/Laws/FSim/` must not import
`Semantics.DRImpliesFD`" — holds literally (no FSim module imports it directly) but is
**unsatisfiable under a transitive reading**, discovered during Task 6:

- `FSim/ParCong` → `FD/ParallelMonoFD` → `FD/FDTransfer` → `Semantics.DRImpliesFD`
  (`ParCong.agda:112`)
- `FSim/HideCong` → `FD/HideMonoFD` → `Semantics.DRImpliesFD` (`HideCong.agda:123`)
- `Bisim/DRCongruence` → `FD/InterruptFD` → `Semantics.DRImpliesFD`
  (`DRCongruence.agda:79`)

So `ParCong`, `HideCong` (hence `ParCongRep`, hence `FSimTower`), `LoopCong`, `BindCong`
and `DRCongruence` all reach `DRImpliesFD` transitively, while `IChoiceCong`, `SlideCong`,
`ExtChoiceLift`, `ExtChoiceCong`, `HideCounterexample` and `SlideCounterexample` do not.
**Do not restate this as "only X is clean".** An earlier revision said only
`FSim/IChoiceCong` was the clean congruence module; that became false as soon as the `▷`/`□`
FSim modules landed, and this is the fourth time in this campaign that a "the only …"
phrasing about hiding or `□` turned out to be wrong. State the measured set, dated, or
state nothing.
**The useful reformulation, which the reach above still satisfies:** the property that
actually matters is "does this module **USE** `¬-divergent→normal` or `drbisim→≈FD`",
not "does it **import** `DRImpliesFD`" — a module can import `DRImpliesFD` purely for
its postulate-free `Semantics.Stability` re-exports (which is what `HideMonoFD` does)
and add zero classical content. Under that reformulation the intent is satisfied:
`¬-divergent→normal` has the single external consumer noted above, and the FSim
regime's actual classical debt is `Par-Diverges→` via `Par-fsim`'s `div→`, not
`¬-divergent→normal`. **Caveat, disclosed honestly:** this rests on manual name-level
import/use tracing across the relevant modules, not a machine axiom tracer — none
exists in this Agda setup, and `--safe` is not usable here since real postulates exist
upstream of the whole FD layer.

### Correction to a stale progress note

An earlier project note (predating this campaign) recorded "Task 4 congruences
(Par/Bind/Hide/loop0) remain" against the `FSim` layer. **Resolved** — verified against
source, not transcribed: all four landed on `semantics/failure-sim` in PR #60
(`0a4a9be` Par, `56ee517` Bind, `cb5f63e` Hide, `da5ea98` loop/iterate), and are the
`Par-fsim`/`Bind-fsim`/`Hide-fsim`/`Iter-bind-fsim` rows of §15 and the table above —
already recorded there as ✅ before this campaign started. The note was stale, not a gap.

The genuinely-remaining item with a similar shape lives in a different document:
`docs/specs/compositional-refinement-plan.md` Tasks 1–2 (`Par-mono-⊑FD`,
`Hide-mono-⊑FD`) are marked done in that file (with the correction that unconditional
`Hide-mono-⊑FD` is false — see §6 above); **Tasks 3–4 of that plan — restructuring a
flat spec into leaf-decomposed form, and assembling the compositional Cardano mux
refinement from it — have no "done" annotation in that file and genuinely remain.**
(Verified by reading the file: only Task 2 carries an "UPDATE (done…)" note.)

---

## Suggested next steps

1. **New operator layer:** lift Hiding (§6) and Renaming (§7) from trace laws to FD laws
   (needs each operator's FD decomposition, the larger lift). Their zero laws
   (`Div ∖ X`, `Div⟦R⟧` — T11.7/T11.8) come for free once the FD layer exists.
2. **Sliding choice (§11)** and the remaining cross-operator SKIP-termination laws.
3. **A `FinHide A` certificate — the repair that would actually fix hide monotonicity;
   SCOPED BUT DELIBERATELY NOT BUILT.** §6(b) shows `FinBr` is the wrong certificate
   (it bounds visible channels, whereas the obstruction is τ-fan-out). The right one
   enumerates, at each reachable state, the τ-successor **TREES** together with the
   hidden-event successors for channels in `A` — i.e. finite branching of exactly the
   step relation that hiding turns into τ. A **label-generic** version is FALSE:
   `c?x → cont x` with an infinite value carrier has infinitely many `ev`-successors, so
   the certificate must be indexed by the hidden set `A` and must enumerate SUCCESSORS,
   not labels. Estimated cost: a **~700-line closure module** (the `FinHide` analogue of
   `CSP.Priority.Closure`, one lemma per operator) plus **~300 lines of König**, plus a
   **new `dne`-certified pigeonhole postulate**. Scoped during the §15 work and
   deliberately not attempted.
4. **Formalise `Pinf ⊑FD Qh`** — the denotational half of the classic hiding
   counterexample, currently only prose in `HideMonoFD`'s header (§6(c)).
5. **`FSim` completeness (`⊑FD → FSim`)** — OUT OF SCOPE. It is classical and would need
   finite branching plus convergence hypotheses; §15 uses `FSim` purely as a SUFFICIENT
   condition for `⊑FD`.
6. **§16 follow-ons, with the honest read on each.** Further site-hunting for
   `AbpFT`-shaped conversions is expected to be **thin**: the pattern that pays is a
   *composite with stable operands*, and that is rarer in this tree than a name survey
   over `noτ-*` / `ndiv*` suggests — most such states are plain `react … ∅t` leaves,
   where the existing refutations are already minimal. The remaining HIGH-VALUE target is
   the **hide** case via `MAcc` (`τ-Acc`-style closure for `P ∖ A`), which is precisely
   where the only postulated non-divergence obligation lives (`¬DivModA→MAcc`, table (a)
   Derivation 9). The **loop** case needs the `Guarded B → τ-Acc B → τ-Acc (loop0 B)`
   hypothesis of §16 finding 3 first.

_Last updated 2026-08-04._

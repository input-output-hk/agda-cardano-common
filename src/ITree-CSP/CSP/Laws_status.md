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

_Last updated: 2026-07-06._

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
| §10 | Interrupt `△` / Throw `⟦A▷` | ✅ **complete** (Fig 13.6 + throw suite) |
| §11 | Sliding choice `▷` | ✅ **core + ⊓/seq slide-dist + failures-char** (▷-id, ▷-assoc(cond), □-slide, ▷-⊓-ext, seq-slide, ▷-failures-char U13.26, □-SKIP-resolve, □-div, Div-slide, Div-SKIP-red, div-strict zeros); ✅ **COMPLETE** (every slide law incl. per-op hide-slide U13.3 + rename-slide U13.6); U13.14 SKIP-slide ✖ correctly (eager-`ret`) |
| §13 | Zero / divergence-strictness | 🟡 `⊓`/`□`/`∥`/`;` zeros done; hide/rename zeros open |
| §14 | Recursion | ❌ not started |

**Bottom line:** the four core "untimed" operator algebras (`⊓`, `□`, prefix,
conditional), sequential composition, interrupt/throw, **and parallel** are all fully
validated at `≈FD`. Every FD-layer postulate is certified from a single `dne`. The next
frontier is **hiding (§6) and renaming (§7)**: both have trace-level laws but no FD laws
yet (each needs an FD decomposition, the larger lift).

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
| — | `⊓-cong-FD≈` (≈FD-premised congruence, reusable) | ✅ | `FDLawsIChoiceRep` |
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
| — | `P⊑FD Q ⇒ (a→₀P) ⊑FD (a→₀Q)` (prefix FD-monotone) | ✅ | `ChoiceRefine` (`⟶₀-mono-⊑FD`) |
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
| — | `cong-⦀Fin` (finite-indexed `⦀Fin`-congruence: pairwise-disjoint alphabet-confined families, pointwise `≈DR` ⇒ folds `≈DR`) | ✅ | `DRCongruenceRep` |
| — | `cong-⦀⋆` (list-indexed `⦀⋆`-congruence, `AllPairs`-disjoint `CongCell` list ⇒ folds `≈DR`) | ✅ | `DRCongruenceRep` |
| — | `sep-from-OffersOnly` + `OffersOnly` confinement closure family (`-mono`/`-Ret`/`-Skip`/`-pchoice`/`-Prefix`/`-Output`/`->>=`/`-iter-bind`/`-loop0`/`-Par`/`-∖`/`-⦀`/`-⦀Fin`/`-⦀⋆-u`) — reusable alphabet-confinement invariant discharging `cong-⦀`'s `Sep` obligations from disjointness alone | ✅ | `DRCongruenceRep` |
| — | `P₁ ⊑FD P₂ ∧ Q₁ ⊑FD Q₂ ⇒ Par A m P₁ Q₁ ⊑FD Par A m P₂ Q₂` (parallel ⊑FD-monotone, generalised `Par`; corollaries `∥-mono-⊑FD` / `⦀-mono-⊑FD`) | ✅ | `ParallelMonoFD` (`Par-mono-⊑FD` = `Par-mono-⊑F⊥` × `Par-mono-⊑D`) — classical via `FDTransfer.FD→trace⊥`; no new postulates (inherits `offer-LEM`/`Par-Diverges→`/`Diverges-LEM`, all dne-certified) |

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
| — | `P ⊑FD Q ⇒ (P∖A) ⊑FD (Q∖A)` (hide ⊑FD-monotone) | ⚠️ **CONDITIONAL** `HideMonoFD` — the UNCONDITIONAL law is **FALSE** in this model. Delivered: (i) `Hide-mono-fail` — the UNCONDITIONAL stable-failure transfer `P ⊑F⊥ Q ⇒ failures (Q∖A) s X ⇒ failures⊥ (P∖A) s X`; (ii) `Hide-mono-⊑FD-df` — the full law `(P∖A) ⊑FD (Q∖A)` **under a divergence-freedom side condition** `∀ s → ¬ divergences (Q∖A) s`. WHY unconditional fails: hiding can *create* divergence (an infinite hidden-event τ-path), which `⊑FD` does not constrain; under unbounded nondeterminism `P ⊑FD Q` does not give `(P∖A) ⊑D (Q∖A)` — counterexample (`Q = μX.h→X`, `P = ⊓ₙ hⁿ;STOP`) in the `HideMonoFD` header (Roscoe's known N-model hiding unsoundness). `modA-transfer` needs `≈DR` not `⊑FD`; no dne-certified postulate can rescue a false ∀-`E` statement. **ZERO postulates** (built on `HideFD`/`TraceLawsHide` only). For trace-only refinement `Hide-mono-⊑ᵀ` stays unconditional. |

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

## §10 — Interrupt `△` / Throw `⟦A▷`  ✅

| Group | Law | Status | Module |
|---|---|---|---|
| U7.5 | interrupt step `(?x:A→P)△(?x:B→Q) = (?x:A→(P△(?x:B→Q)))□(?x:B→Q)` | ✅ | `InterruptFD`: single-channel `△-step-FD`; **MENU** (A,B=event sets) `△-step-menu-FD` |
| Fig 13.6 | interrupt-over-slide `((?x:A→P)▷P′)△Q = (?x:A→(P△Q))▷(P′△Q)` | ✅ | `InterruptFD`: single-channel `△-slide-dist-FD`; **MENU** `△-slide-dist-menu-FD` |
| Fig 13.6 | interrupt: `△-Pret-⊓`, `△-div-row`, `△-⊓L/R-dist`, `△-step` | ✅ | `InterruptFD` |
| U7.6 | throw step `(?x:A→P)⟦B▷Q = ?x:A→(P⟦B▷Q ◁ x∉B ▷ Q)` | ✅ | `ThrowFD`: single-channel `Θ-prefix-step`; **MENU** (A=event set) `Θ-step-menu-FD` |
| — | throw: `Θ-Pret`, `Θ-div`, `Θ-⊓L/R-dist` | ✅ | `ThrowFD` |

König step `△-Diverges→` (postulate, certified) in `InterruptDivergence`. Throw is
postulate-free.

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
| Iterate refinement-monotonicity `loop0-mono-⊑FD` — **sub-project C** | ✅ | `CSP.Laws.FD.IterateMonoFD` |
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

---

## Postulate inventory (`spike/extc-fd-laws`)

All six postulates are kept small and direct, and **each is certified derivable from a
single classical axiom `dne` (¬¬A→A)** in `ClassicalFromLEM.agda` (a standalone soundness
witness, imported by nothing):

| Postulate | Used in | Certified |
|---|---|---|
| `¬-divergent→normal` | `DRImpliesFD` | ✅ Derivation 1 |
| `□-Diverges→` | `ExtChoiceDivergence` | ✅ Derivation 2 |
| `△-Diverges→` | `InterruptDivergence` | ✅ Derivation 3 |
| `>>-Diverges→` | `SeqDistR` | ✅ Derivation 4 |
| `Par-Diverges→` | `ParallelDivergence` | ✅ Derivation 5 |
| `offer-LEM` | `ParallelRefusals` | ✅ Derivation 6 (plain LEM) |

**Every postulate in the FD layer now derives from the one `dne` axiom.** No module uses
`NON_TERMINATING`. The bridge `≈DR ⟹ ≈FD` and `∼ ⟹ ≈DR` lift bisim laws to FD.

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

---

## Suggested next steps

1. **New operator layer:** lift Hiding (§6) and Renaming (§7) from trace laws to FD laws
   (needs each operator's FD decomposition, the larger lift). Their zero laws
   (`Div ∖ X`, `Div⟦R⟧` — T11.7/T11.8) come for free once the FD layer exists.
2. **Sliding choice (§11)** and the remaining cross-operator SKIP-termination laws.

_Last updated 2026-07-12._

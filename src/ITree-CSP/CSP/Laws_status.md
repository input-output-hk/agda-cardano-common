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

_Last updated: 2026-06-15._

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

## Suggested next steps

1. **New operator layer:** lift Hiding (§6) and Renaming (§7) from trace laws to FD laws
   (needs each operator's FD decomposition, the larger lift). Their zero laws
   (`Div ∖ X`, `Div⟦R⟧` — T11.7/T11.8) come for free once the FD layer exists.
2. **Sliding choice (§11)** and the remaining cross-operator SKIP-termination laws.

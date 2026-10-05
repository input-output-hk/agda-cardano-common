# `FourNode/Liveness/` — layout

Block-liveness for the four-node breakable-links diamond, in **two independent
routes** over the *same* model and the *same* R2 bisimulation.

The model itself lives one level up and is **not** part of this directory:

| module | role |
|---|---|
| `FourNode.FourNodeDiamond` | the four-node diamond system (`Params`, `Block₃`, node logic, `system`) |
| `FourNode.FourNodeDiamondBreakable` | the breakable-links variant (`breakableSystem`) — the subject of both routes |
| `FourNode.FourNodeDiamondCfg` | an unused clone of the config, kept for reference only |

## Directory map

```
Liveness/
  R2_Bisim/            25   SHARED by both routes — the divergence-respecting bisimulation
                            `breakableSystem blkA ≈DR abstractSystem` and its supporting
                            oracle/step/route/medium layers
                            (Sys*, AbstractSystem, NodeSpecs)

  LTL/                        ROUTE 1 — LTL satisfaction (`⊨`), the headline theorem
    Spec.lagda.md             the LTL spec: atoms `producedA`/`arrivedD`/`brkG1`/`brkG2`,
                              `confined`, `respondsAtoD`, `BlockLiveness⁺At`, `BlockLiveness⁺`
    BlockLivenessProof.agda   the per-`blkA` proof
    BlockLiveness.agda        the ∀-closure ENDPOINT: `blockLiveness⁺ : BlockLiveness⁺`
    BLOCKLIVENESS_STATUS.md   campaign status + audit

    Walk/            36       R3 abstract-side liveness: the walk/μ-descent engine
                              (`AbstractLive`, `Walk*`, `RealAbs`, `TProg`)
    Value/           37       the payload chain that makes `arrivedD` payload-EXACT
                              (`Pipe*` — invariant, preservation, fire/routing, τ-io mirrors)
    Evidence/         3       live FINDINGS, imported by nothing but kept green:
                              `PipeCellFalse`  machine-checked refutation of the false
                                               `Coupled` cell clauses of the old `pcone`
                              `PipeValGate`    the positive value gate (all nine edges)
                              `PipeValArrived` the `arrivedD-BS` pre-flight
    Archive/         23       superseded modules + the two harvest spikes
                              (`ChoiceMatchSpike`, `Route2Spike`).  Kept because they still
                              typecheck and record dead ends.  **Outside the endpoint
                              closure** — the two spikes carry `--allow-unsolved-metas`
                              and `postulate`s, which is why they must stay outside it.

  CSP_Refinement/             ROUTE 2 — the CSP failures-divergences refinement statement
    Spec.lagda.md             the ⊑FD-shaped statement of the same liveness property
    FrozenPeersDemo.agda      discharges `FrozenKAclient`'s two open hypotheses concretely
    LeafSpecs/        2       τ-free component specs for the KeepAlive client peer
                              (`KAclient`, `FrozenKAclient`)
    LiveSpecCouple.agda       couples reachable abstract configurations to spec states —
                              `SpecPos`/`specPos`/`SpecOf` plus five flag-update lemmas and
                              spec-side weak transitions
    LiveNoDivH.agda           divergence-freedom of the hidden abstraction
                              (`abstractSystem ∖ hidden`) by lexicographic `(μTot , μτ)` descent —
                              no `MAcc` calculus, no `¬DivModA→MAcc` postulate
    LiveLegInv.agda           the POSITIVE per-leg token-location invariant `LegInv` —
                              `LegPos` (10 positions) / `AtPos` / `legInv-init` /
                              `legInv⇒pipeInv` (the coarse image onto `PipeInv`'s five
                              `PLvl`s) + the `TokenSomewhere` and `CellReaderAligned`
                              readers.  Where `PipeInv⁺` is a one-way UPSTREAM coupling
                              that goes vacuous on the all-empty configuration, every
                              `AtPos` clause asserts POSITIVE occupancy of one slot —
                              `legInv-excludes-phantom` is the machine-checked record that
                              this rules out the gate verdict's phantom-token state `s✗`.
                              State predicate only; preservation is Task 3.
                              **In the HEAVY closure**, not the cheap prefix: its required
                              export `legInv⇒pipeInv` names `PipeInv`, and `PipeInv` →
                              `WalkPr` → `WalkDExpose` → `SysRoute`/`SysOracle_*`.
    STABR_STATUS.md           campaign status: the CSP route is COMPLETE and
                              UNCONDITIONAL — `LivenessProof.At.Premises` is an EMPTY
                              record since the cellCp3 window, so `livenessSpec-un` and
                              `livenessDivFree` both hold outright.  (This read
                              "`stabR-final` premised on `cellCp3` + 12 `InFlightOpen`
                              facts", true until the InFlightOpen close.)
```

## Dependency flow

```
FourNodeDiamond / FourNodeDiamondBreakable            (the model)
        │
        ├──► R2_Bisim                              (≈DR, shared)
        │       │
        │       ├──► LTL/Walk  ──┐
        │       └──► LTL/Value ──┴──► LTL/BlockLivenessProof ──► LTL/BlockLiveness
        │                                   ▲                       (endpoint)
        │                            LTL/Spec (atoms + statement)
        │
        └──► CSP_Refinement/Spec  ◄── CSP_Refinement/LeafSpecs
                │
                └──► R2_Bisim (cheap prefix) ──► CSP_Refinement/{LiveSpecCouple,LiveNoDivH}
                                                          ──► (Phase 2: LiveLegInv,
                                                               LiveLegStep, LiveStableOffer,
                                                               LiveFSim, then the two heavy
                                                               LiveHeavyFacts, LivenessProof)
```

`LTL/Evidence` and `LTL/Archive` hang off the same lower layers but are imported by
nothing; they are built on their own.

**Module weight.** `LiveSpecCouple` and `LiveNoDivH` import only the **cheap prefix** of
`R2_Bisim` — `NodeSpecs → AbstractSystem → SysDecode/SysMedium/SysNode → SysStep/SysReach`
— never the heavy suffix (`SysBisim`, `SysOracle*`, `SysIoLink*`, `LTL/Walk`'s `Walk*`);
heavy facts are module parameters instead (`LiveNoDivH`'s `Descent` block). Iteration stays
in the seconds range. Phase 2 confines the heavy closure to **two** files —
`LiveHeavyFacts` (the parameter discharges) and `LivenessProof` (assembly) — one closure
and one shared `.agdai`, split only so each is reviewable alone. They cannot be merged into
one cheap module: `WalkConvNoDiv` already imports `SysBisim`.

**Outside this tree.** `Semantics/FDFromF.agda`'s `⊑F→⊑FD-df` upgrades a stable-failures
refinement to failures-divergences once the right-hand side is known divergence-free — a
new module, so `Semantics/FailuresDivergences.agda`'s existing consumers stay untouched.

**Phase status.** Phase 1 stopped at a deliberate re-plan gate. Two docs under
`docs/superpowers/specs/` carry it: `2026-08-06-liveness-via-abstractSystem-design.md`
(the route-2 strategy; per-step status in §9(f)) and
`2026-08-11-stable-offer-falsification.md` (the falsify-first verdict — the stable-offer
obligation is true of the model, but the banked pipeline invariant is too weak to close it).
Phase 2 opens by strengthening that invariant and adds six modules — `LiveLegInv`,
`LiveLegStep`, `LiveStableOffer`, `LiveFSim`, `LiveHeavyFacts`, `LivenessProof` — plus one
throwaway pricing spike, in
`docs/superpowers/plans/2026-08-11-liveness-csp-refinement-phase2.md`.

## Endpoints and audit, in one line each

**There are THREE endpoints (two liveness, one safety), and all are unconditional.**

- LTL endpoint: `CSP.Examples.Cardano_network.FourNode.Liveness.LTL.BlockLiveness` —
  `blockLiveness⁺ : BlockLiveness⁺`, premise-free, payload-exact.
- SAFETY endpoint (S1, provenance at D):
  `CSP.Examples.Cardano_network.FourNode.Liveness.LTL.ProvenanceD` —
  `provenance⁺ : Provenance⁺` (`∀ blkA tr → □ᵗ (atom (provD blkA)) tr`, with
  `provD blkA fr = arrivedD⁻ fr → arrivedD blkA fr`): every block D receives IS the
  block A produced.  A SAFETY result that reuses the liveness route's machinery
  (`PipeVal` + `pipeVal-fold` at `φ := arrivedD⁻`, then the `≈DR` transport), hence
  the path.  Premise-free; closure **135 modules**.  Classical footprint: ONE axiom
  (`Classical.dne`); exactly ONE use-site on this endpoint's term path
  (`LTL/Walk/TProg.agda:46`), and two further use-sites in the closure
  (`LTL/Walk/Walk.agda:262` `getProd`, `LTL/Walk/Walk.agda:269` `conf⊎`) that feed
  only the `AbstractLive` path this endpoint does not traverse.  The two
  `Traces_Based` classical postulates sit in the closure UNUSED (the per-position
  transport never routes through `⟦ G φ ⟧`) and `ClassicalDescent` is not imported.
  Used-versus-merely-present was established by import and name analysis, not by a
  machine check — Agda offers no term-level axiom tracer.
  **Not closed here: antecedent reachability.**  `provD` is an implication, so it is
  vacuously true at any frame that is not a D-delivery, and nothing in the repo
  proves such a frame is ever REACHABLE on a trace of `breakableSystem`.  The missing
  artefact is a `Trace` witness over `breakableSystem`, or a lemma of shape
  `∃ tr n → arrivedD⁻ (frameOf (drop n tr))`; `FourNodeDiamondBreakable.lagda.md`
  (§"Reading the witness") records why none is given — one composed step costs
  ≈2.5 min and ≈20 GB.  The gap is INHERITED from the LTL liveness endpoint, not
  introduced here (`BlockLiveness⁺At` also takes its trace, confinement disjunct and
  `producedA` frame as hypotheses, so discharging non-vacuity from liveness would be
  circular), and is strictly SMALLER for provenance: `provenance⁺` needs no
  confinement hypothesis, so it holds even when both routes are broken.  Not a defect
  in the proof — it never discharges by refuting the antecedent (the value chain is
  positive throughout), and the in-module checks show `provD b1` refutable on a
  wrong-payload frame and satisfiable on a right-payload one.
- CSP-refinement endpoint:
  `CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LivenessProof` —
  `livenessSpec-un : LivenessSpec` (`∀ b → LSpec b true true ⊑FD (breakableSystemOf b ∖
  hidden b)`) and `livenessDivFree : ∀ b → DivergenceFree (breakableSystemOf b ∖ hidden b)`.
  **Both premise-free since the cellCp3 window** — `LivenessProof.At.Premises` is an EMPTY
  record, so the conditional form `livenessSpec` (kept, type unmoved) discharges outright.
  Unlike the LTL route this one is NOT postulate-free: two sanctioned seams on the term
  path (`DRCongruence.modA-transfer`, `DRImpliesFD.¬-divergent→normal`), both certified
  `dne`-derivable in `CSP.Laws.ClassicalFromLEM`.  Detail in
  `CSP_Refinement/STABR_STATUS.md`.
- Transitive import closure: **149 modules**; classical base exactly
  {`Classical.dne`, `Semantics.LTL.ClassicalDescent.¬¬F⇒F`,
  `Semantics.LTL.Traces_Based.⟦G⟧⇒⟦G⟧⁺`, `Semantics.LTL.Traces_Based.¬G⇒F¬`};
  zero postulates, holes, unsolved metas, `NON_TERMINATING` or `Sized` in the closure.
- Full detail in `LTL/BLOCKLIVENESS_STATUS.md`.

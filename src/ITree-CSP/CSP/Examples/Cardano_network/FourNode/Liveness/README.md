# `FourNode/Liveness/` — layout

Block-liveness for the four-node breakable-links diamond, in **two independent
routes** over the *same* model and the *same* R2 bisimulation.

The model itself lives one level up and is **not** part of this directory:

| module | role |
|---|---|
| `FourNode.FourNodeDiamond` | the four-node diamond system (`Params`, `Block₃`, node logic, `system`) |
| `FourNode.FourNodeDiamondBroken` | the breakable-links variant (`systemBroken`) — the subject of both routes |
| `FourNode.FourNodeDiamondCfg` | an unused clone of the config, kept for reference only |

## Directory map

```
Liveness/
  R2_Bisim/            25   SHARED by both routes — the divergence-respecting bisimulation
                            `systemBroken blkA ≈DR abstractSystem` and its supporting
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
```

## Dependency flow

```
FourNodeDiamond / FourNodeDiamondBroken            (the model)
        │
        ├──► R2_Bisim                              (≈DR, shared)
        │       │
        │       ├──► LTL/Walk  ──┐
        │       └──► LTL/Value ──┴──► LTL/BlockLivenessProof ──► LTL/BlockLiveness
        │                                   ▲                       (endpoint)
        │                            LTL/Spec (atoms + statement)
        │
        └──► CSP_Refinement/Spec  ◄── CSP_Refinement/LeafSpecs
```

`LTL/Evidence` and `LTL/Archive` hang off the same lower layers but are imported by
nothing; they are built on their own.

## Endpoint and audit, in one line each

- Endpoint: `CSP.Examples.Cardano_network.FourNode.Liveness.LTL.BlockLiveness` —
  `blockLiveness⁺ : BlockLiveness⁺`, premise-free, payload-exact.
- Transitive import closure: **149 modules**; classical base exactly
  {`Classical.dne`, `Semantics.LTL.ClassicalDescent.¬¬F⇒F`,
  `Semantics.LTL.Traces_Based.⟦G⟧⇒⟦G⟧⁺`, `Semantics.LTL.Traces_Based.¬G⇒F¬`};
  zero postulates, holes, unsolved metas, `NON_TERMINATING` or `Sized` in the closure.
- Full detail in `LTL/BLOCKLIVENESS_STATUS.md`.

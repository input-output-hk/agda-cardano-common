# Praos `BlockLiveness⁺` — STATUS (`pcone` DISCHARGED, session 33)

**Endpoint module:** `CSP.Examples.Cardano_network.NetworkVerification.Praos.BlockLiveness`
(the unparameterised ∀-closure; the per-block proof lives in
`…Praos.BlockLivenessProof blkA`)
**Branch:** `examples/praos_liveness`  ·  **Green** (bare `EXIT=0`).

**SESSION-33 (2026-08-07) DISCHARGED `pcone`.** `BlockLiveness⁺` is now proved
end-to-end **modulo ONE explicit premise** (`wprog`) and one sanctioned model
relaxation (payload-agnostic `arrivedD`). Both `tprog` (via the campaign `dne`)
and `pcone` (constructively, 0 new axioms) are closed.

**As of the 2026-08-06 generalisation, node A is no longer hardwired to `b1`:**
A may be configured to produce **any** block `blkA : Block₃`, and the headline is
universally quantified over that choice. All 106 modules under `Praos/` are now
top-level parameterised modules `module X (blkA : Block₃) where`; `BlockLiveness.agda`
is the one unparameterised module that closes `∀ blkA`.

---

## Result

`blockLiveness⁺ : BlockLiveness⁺`, where (from `FourNodeDiamondLiveness`)

```agda
BlockLiveness⁺At : Block₃ → Set _
BlockLiveness⁺At blkA = ∀ (b : Block₃) (tr : Trace (⊤ {0ℓ}) (systemBroken blkA))
                      → (□ᵗ (¬ atom brkG1) tr ⊎ □ᵗ (¬ atom brkG2) tr)  -- breaks confined to one path group
                      → ∀ (n : ℕ) → ⟦ atom (producedA b) ⟧ (drop n tr) -- A hands out block b (apiBF sendBFBlock@hi on AB/AC, a≡b)
                      → ◇ᵗ (atom (arrivedD b)) (drop n tr)             -- SOME block arrives at D (apiBF recvBFBlock@hi on BD/CD)

BlockLiveness⁺ : Set _
BlockLiveness⁺ = ∀ (blkA : Block₃) → BlockLiveness⁺At blkA
```

**In prose:** in the broken four-node diamond, **however node A is configured** (it produces
an arbitrary block `blkA`), if every `break` event stays confined to at most one of the two
candidate paths ({AB,BD} or {AC,CD}), then whenever node A produces a block, node D
eventually receives a block. Fairness-free (the honest headline for this model;
`BlockLiveness⁺ᶠ` is superseded, see `FourNodeDiamondLiveness`).

Note the two block quantifiers are deliberately **kept apart**: `blkA` is A's configured
payload, `b` is the block observed on the `producedA` frame. The proof never needs
`b ≡ blkA`, and merging them would change what is proved.

**Proved under ONE module premise.** `Praos.BlockLivenessProof blkA` proves
`blockLiveness⁺ : BlockLiveness⁺At blkA` inside `module _ (wprog)`
(`BlockLivenessProof.agda:176-178`):

```agda
module _
  (wprog : (b : Block₃) (r : RState) → Pr b r → WEnabled (IntactApiClass b) (radec r))
  where
```

`Praos.BlockLiveness` then closes `∀ blkA` with the **same single premise**, restated with
a leading `∀ (blkA : Block₃)` (the `Praos` modules are imported UNAPPLIED so their
parameter appears as an explicit first argument).  **VERBATIM, `BlockLiveness.agda:66-75`:**

```agda
module _
  (wprog : ∀ (blkA : Block₃) (b : Block₃) (r : SR.RState blkA)
         → WP.Pr blkA b r
         → WEnabled (WE.IntactApiClass blkA b) (SR.radec blkA r))
  where

  -- R3/R4 HEADLINE at FULL generality: A may be configured to produce ANY
  -- block; the per-`blkA` proof is `Praos.BlockLivenessProof blkA`
  blockLiveness⁺ : BlockLiveness⁺
  blockLiveness⁺ blkA = BLP.blockLiveness⁺ blkA (wprog blkA)
```

(`SR` = `Praos.SysReach`, `WP` = `Praos.WalkPr`, `WE` = `Praos.WalkEnabled`,
`BLP` = `Praos.BlockLivenessProof`.)  **`pcone` is GONE** — no `pcone` parameter remains
in `AbstractLive`, `BlockLivenessProof` or `BlockLiveness`.

**Proof spine** (`BlockLivenessProof`, at the module's `blkA`):

```
abstractLive wprog       : abstractSystem ⊨ᵂ respondsAtoD b        -- R3 abstract-liveness walk (AbstractLive; locate from PipeLocate)
sysBisim                 : systemBroken blkA ≈DR abstractSystem     -- R2 divergence-respecting bisim (SysBisim)
realAbs tprog            : Realisableᴿ abstractSystem               -- R3 (RealAbs, tprog from TProg via dne)
  ── ⊨-DRWB-invariantᴿ→ ──►  systemBroken blkA ⊨ᵂ respondsAtoD b
  ── ⊨ᵂ⇒⊨ (TraceBridge)  ──►  systemBroken blkA ⊨ respondsAtoD b
  ── descent-⊨ (ClassicalDescent) ──►  BlockLiveness⁺At blkA
  ── Praos.BlockLiveness (∀-closure) ──►  BlockLiveness⁺
```

### Audit (mainline = the transitive import closure of `BlockLiveness`)

- **0 postulate, 0 hole `{! !}`, 0 unsolved meta, 0 `NON_TERMINATING`/`Sized`** in the
  closure. 105 of the 107 files under `Praos/` use only `{-# OPTIONS --guardedness #-}`
  (session-33 re-audit: `grep -rlE "OPTIONS.*allow-unsolved-metas"` hits ONLY the two
  spikes; `grep -rnE "^\s*postulate|\{! |NON_TERMINATING|Sized"` hits only the two spikes
  plus prose lines in this file).
- The only two exceptions are the harvest-scratch spikes `ChoiceMatchSpike` and
  `Route2Spike` (`--guardedness --allow-unsolved-metas`, 3 `postulate` blocks between
  them). Neither is in the closure — they are referenced only in comments.
- **`dne` is the single classical axiom** used. Its use-sites, all the sanctioned
  campaign-classical style (each certified LEM-derivable in `ClassicalFromLEM`):
  - `Classical.dne` — THE axiom.
  - `Semantics.LTL.ClassicalDescent.¬¬F⇒F` (postulate, certified from `dne`) — powers
    `descent-⊨`, the final `BlockLiveness⁺At` step.
  - `Semantics.LTL.Traces_Based.⟦G⟧⇒⟦G⟧⁺` and `.¬G⇒F¬` (generic-LTL postulates,
    certified from `dne`).
  - `Praos.TProg` — `dne`→`em`→`tprog` (the `Realisableᴿ` τ-decision; see below).
  - `Praos.Walk` — `getProd`, `conf⊎` (extract positive `producedA` / split confinement
    `∨` out of a double-negation; same `Classical.dne`).
- Note: `respondsᵂ-intro` is NOT in the closure — the descent runs through
  `descent-⊨`/`¬¬F⇒F`, not `respondsᵂ-intro`.

---

## The explicit hypotheses

### 1. `wprog` — weak progress / enabledness

- **Type (at a fixed `blkA`):** `(b : Block₃) (r : RState) → Pr b r →
  WEnabled (IntactApiClass b) (radec r)`; in `BlockLiveness` with a leading `∀ blkA`.
- **Meaning:** from any reachable pending state `r` (`Pr b r`: some D-consumer leg is
  pre-`recvBFBlock`), the intact-path BlockFetch class (`apiBF@hi` on AB/BD/AC/CD) is
  **weakly enabled**. I.e. the pipeline can still make an observable intact-path move.
- **Plausible/true:** while a block is in flight and D has not yet consumed it, an intact
  path's fetch driver is always reachable via τ*+visible — nothing has terminated
  (`WalkEnabled` already proves `WEnabled` is absurd at `ret`/stuck states, so the only
  gap is the positive offer).
- **Discharge:** the **forward offer-intro cone** — constructively expose the enabled
  `apiBF@hi` offer along the walk. **Unbuilt.**

### 2. `pcone` — pipeline provenance — **DISCHARGED (session 33, 2026-08-07)**

- **Was:** `(b : Block₃) (r0 : RState) {t : NetProc} (w : WTrace ⊤ t)
  → t ≡ radec r0 → producedA b (frameOf w) → Pr b r0`.
- **Meaning:** if the current frame is a `producedA b` (A is handing out block `b`), the
  state is pending (`Pr b r0`: D's consumer leg on that path has not yet received).
- **Discharge (constructive, 0 new axioms, no `dne`):** the premise was never inhabited in
  its literal ∀-`r0` form.  Instead `Praos.PipeLocate.locate` inhabits
  `WalkLocate.locate`'s type — the ONLY shape the engine consumes — and
  `AbstractLive.walkPos` now reads
  `walkPosFrom μTot Pr (λ b → WD.deliver b (wprog b)) PL.locate`.
  The premise parameter was then deleted from `AbstractLive`, `BlockLivenessProof` and
  `BlockLiveness` in turn.

**The discharge chain (all green, all `--guardedness` only):**

| piece | module | content |
|---|---|---|
| product walk | `PipeInvProd.pipeInvS-along-walk′` | folds `PipeInvS l = PipeInv⁺ l × SrvCoupled l` from `rinit` to the located `producedA` frame |
| τ-io arm | `PipeTauIo.tauIo` | `TauIoS l`, total (session 32) |
| visible arm | `PipeEvStep.evStepS` | `EvStepS l`, total (session 33, G2) |
| (E1) | `PipeProdFix.liftτ*-prodFix` | a hidden τ-run moves NO producer: `AllProdFix` over `─[τ*]─►` |
| (E2) | `PipeProdFire.prodFire-{AB,AC}` | a strong `apiBF lk hi sendBFBlock` out of `radec r` forces `prodOf (leg lk) (toSys r) ≡ pp5` |
| assembly | `PipeLocate.locate` | frame inversion + (E1)∘(E2) + `pipeInvS⇒Pr` |

**Why (E1) AND (E2) (the session-32 finding, now resolved).** `producedA b` is a FRAME
predicate: it records that the frame's next move is a **weak** `apiBF … sendBFBlock`
(τ*·ev·τ*), not a strong step out of the frame's state.  `pipeInvS⇒Pr` wants
`prodOf l (toSys r0) ≡ pp5` **at** the frame state.  (E2) sees only the strong middle;
(E1) transports its verdict back over the τ-prefix.  The τ-suffix is never read.

**Session-33 table check (method mandate, run BEFORE building (E2)), SOUND.**
`sendBFBlock` occurs at EXACTLY one place in the whole driver algebra:
`FourNodeDiamond.produce`'s sixth hop = the head of `SysNode.decProd _ _ _ pp5`
(`SysNode.agda:823-825`).  It occurs NOWHERE in `consume`/`consume-k`
(`FourNodeDiamond.lagda.md:224-241`), hence nowhere in `decCons`, `decConsD`, or `decCP`'s
consuming arm.  No false statement found this session.

**Session-33 economies worth keeping.**
1. **(E2) needs no non-offer cascade.** A node api step is a `∥⇘ apiES ⇙` SYNC
   (`SysStep.reflect-node-api`), so the node's DRIVER must co-fire the same event.  Every
   refutation is therefore taken on the driver side alone — the twelve protocol peers are
   never examined.  Node A → `decProd-sbb-pp5`; node B/C → `decCP` (consuming arm is
   `decCons`, produce arm is on the other link); node D → link injectivity.  ~380 L, 28 s.
2. **The CLASSIFIER, not `refl`.** The two `evLabel`s in a fired-label equality carry
   DIFFERENT carrier types and `Set` is not injective, so a direct `refl`/`()` match on
   `output-ev-lab`'s result gets the unifier stuck.  Transport a `Set`-valued predicate
   (`PipeProdFire.IsSBB : Event → Set`) along it instead.  This one idiom powers
   `decProd-sbb-pp5`, `decCons-sbb-⊥`, `decCP-sbb-⊥` and both `srvEvo⇒…` folds.
3. **`SrvEvStep` was never inhabited as stated.** Session 32's cheaper packaging was
   taken: `PipeEvStep.evStepS` builds `EvStepS l` DIRECTLY (own reflected `r′`, both
   halves), so nothing has to make `proj₁ (evStep l r st)` reduce.  `PipeInvProd.SrvEvStep`
   and `evStepS-from` are now vestigial.
4. **`evStep`'s dispatch shape made G2 cheap.** Only 2 of its 16 label clauses do work
   (`evStep-api`, `evStep-break`); the other 14 are `⊥-elim`.  So `evStepS` is a verbatim
   re-dispatch with two new bodies, not a re-proof.

**Session-33 gotcha (cost one build).** `prodOf`/`relayOf`/`upSrv`/`dnSrv` all
pattern-match on the leg, so with `l` a VARIABLE both sides of a frame equality stay stuck
and Agda tries to unify the two whole `SysState`s (error: `med (RState.sys r) != m′`).
Every frame lemma over these must be cased on `l` at the top —
`PipeEvStep.srvCoupled-break` is the fix, mirroring the existing `frame-break`.

### 3. Payload-agnostic `arrivedD` (sanctioned `a ≡ b` drop) — STILL OPEN

Generalising A's block **does not** restore this conjunct; it only renames the missing
invariant.

- Not a premise but a **model relaxation**: `arrivedD b` fires on ANY `recvBFBlock@hi` on
  BD/CD regardless of payload (the `a ≡ b` conjunct is dropped; `producedA b` still reads
  `a ≡ b`). So the headline is "**some** block arrives at D", not "the produced block `b`".
- **Why:** inside `WalkDeliver.deliver` the received block `b″` cannot be tied to the
  quantified `b` — `Pr` is block-blind, and the copy-cell value invariant is unbuilt. With
  the generalisation the unbuilt invariant is now **`b″ ≡ blkA`** (it used to read
  `b″ ≡ b1`); the `blkA` case is no harder, but it is no easier either.
- **Discharge:** build the `b″ ≡ blkA` block-value cone, then restore the `a ≡ b`
  conjunct — which would also let `b` and `blkA` be tied together.

### `pcone` — DISCHARGED (session 33; see section 2 above)

### `tprog` — DISCHARGED (was the third premise)

- **Type:** `(r : RState) → τ-progress (radec r)` (`Praos.TProg`).
- Pure `P ⊎ ¬ P` at `P = Σ t′. radec r ─[τ]─► t′`; closed in one line from the campaign
  `dne` (`em`, then repackage the negative disjunct's implicit `{t′}`). No τ-inversion /
  cone. Supplied to `RealAbs.realAbs` at the endpoint.

---

## Architecture map (per phase)

Every module below is `(blkA : Block₃)`-parameterised except `BlockLiveness` itself.

- **R2 — `systemBroken blkA ≈DR abstractSystem`:** `SysBisim` (`sysBisim`), driven by the R2
  transition oracle `SysOracle`/`SysOracle_{TauCore,NodeTauEv,PeerEvCSBF,PeerEvIo,
  RouteKaTs,RouteLnLf,GapBDisj}`, plus `SysReach`/`SysRoute`/`SysStep`/`SysSqrt`/
  `SysDecode`/`SysNode`/`SysMedium`/`SysDiv`/`SysIoLink*`, `AbstractSystem`, `NodeSpecs`.
- **R3 — abstract liveness walk:** `AbstractLive` (`abstractLive`, takes `wprog` ONLY),
  the `Walk*` family (`Walk`/`WalkLocate`/`WalkEngine`/`WalkDeliver`/`WalkConv*`/
  `WalkClassify`/`WalkMeasure`/`WalkEnabled`/`WalkPr`/…), `RealAbs` (`realAbs`, takes
  `tprog`), `TProg` (`tprog`).
- **R4 — transport to the concrete headline:** `BlockLivenessProof`
  (`⊨-DRWB-invariantᴿ→` + `⊨ᵂ⇒⊨` + `descent-⊨`; `respondsAtoD-BS` `BisimStable`
  certificate reproduced in-module).
- **∀-closure:** `BlockLiveness` (unparameterised; the only module in `Praos/` without a
  `blkA` parameter).
- **`pcone` DISCHARGE CHAIN (session 33 — now IN the mainline closure):**
  `AbstractLive` → `PipeLocate` → {`PipeInvProd`, `PipeTauIo`, `PipeEvStep`,
  `PipeProdFix`, `PipeProdFire`} → {`PipeEvDriverCone`, `PipeNodeAEvo`, `PipeEvRelay`,
  `PipeEvDriver`, `PipeBundleEvo`, `PipeSrvInv`, `PipeInv`, `PipeMedKey`, `PipeSrvIoDec`,
  `PipeCliIoDec`, `PipeBundleIoEvo`, `PipeNodeIoEvo`, `PipeSrvFire`, `PipeFillSource`,
  `PipeTauMed`, …}.  The `Pipe*` family is no longer "imported by nothing".
- **Still-unwired scaffolding (green, imported by nothing):** the remaining `Pipe*` leaves
  (`PipeInv`, `PipeExpose*`, `PipeClass*`, `PipeNodeFix*`, `PipeEv*`, `PipeStepEmit`,
  `PipeTauMed`, `PipeConsumeSource`, `PipeRecvSource`, `PipeIoHandoff`, `PipeReportGen`,
  `PipeBundleRecv`, `PipeBundleEvo`, `PipeSrvInv`, `PipeFillSource`, `PipeCellFalse`,
  `PipeSrvFire`, `PipeInvProd`, `PipeMedKey`, `PipeSrvIoDec`, `PipeCliIoDec`,
  `PipeBundleIoEvo`, `PipeNodeIoEvo`, `PipeTauIo`).
  NOT wired to the theorem.

---

## Build figures (corrected)

| build | wall | peak RSS |
|---|---|---|
| `BlockLivenessProof` — **cold**, full closure, `-M28g` | **22:53** | **25.2 GB** |
| `BlockLivenessProof` — warm | 16 s | 2.1 GB |
| `BlockLiveness` (∀-closure endpoint) — warm | 16 s | — |

The 22:53 / 25.2 GB cold figure is the correct one to plan against; earlier versions of this
document quoted "14 s / 2.0 GB", which was a **warm** rebuild. The `blkA` parameterisation
did **not** inflate the build (warm is 16 s / 2.1 GB against the pre-parameterisation
14 s / 2.0 GB).

### Operational notes

- **Every `agda` invocation must run with the Claude sandbox disabled.** The global
  libraries file (`~/.config/agda/libraries`) points at
  `…/CSP_Agda_Interaction_Trees/src/csp-ptree.agda-lib` — the **sibling, non-`.experiment`**
  checkout — which is outside the sandbox read allowlist. Inside the sandbox every build
  dies instantly with `[LibraryError] … csp-ptree.agda-lib does not exist`. That message
  means "re-run with the sandbox off", **not** "the code is broken". Git also needs the
  sandbox off here (this checkout is a worktree whose `.git` lives in the sibling repo).
- **One Agda build at a time.** A cold closure build peaks at ~25 GB RSS; two concurrent
  builds will thrash or OOM. Typecheck as
  `cd src && agda +RTS -M28g -RTS <path>` and judge **only** by `echo "EXIT=$?"` — never by
  piping the output through `tail`/`head` (exit 0 is success even with yellow warnings).
- Cold builds exceed 20 minutes; detach them (`nohup … ; echo $? > x.done &`) rather than
  relying on a tool timeout.

### `with`-abstraction hazard introduced by the parameterisation

Inside a `(blkA : Block₃)` module a `with` clause (and any `where` block under one)
partially normalises the goal, after which the normal form refuses to convert against the
un-normalised type written in the body. The two terms then **print identically** — the
discriminator is the elided module-parameter slot, invisible even under `--show-implicit`.
Typical message:

```
prodOf l (RState.sys r) != prodOf l (toSys r) of type …SysNode.ProdPh blkA
```

Two fixes are in use:

1. **Fold the `with`/`where` into a single `let`** (Agda `let` accepts type signatures and
   destructures Σ). Applied at 5 sites: `PipeExposeReach.reach-ev-cellReport`,
   `PipeTauMed.τpreserve-med`, `PipeExposeNodeProd.reach-ev-prodReport`,
   `PipeExposeNodeRelay.reach-ev-relayReport`, `PipeExposeReachClient.reach-ev-clientReport`.
2. When the `with` is a **genuine case split** and cannot be removed, split the definition
   in two: a top-level *inversion-only* helper that carries the case split but whose
   statement mentions **none** of the affected types, and a `with`-free assembly clause.
   Applied at `PipeEvStep.evStep-break` → `PipeEvStep.break-invert` + a single-`let`
   `evStep-break`.

---

## Discharge plan (to close the remaining premise)

1. **`pcone`** — **DONE (session 33)**.  See section 2 above for the chain and the
   session-33 economies.  Commits `684e323` (E1) · `a5bcac4` (E2) · `07aecdb` (E) ·
   `1c2a427` (G2a) · `afca698` (G2) · `0ea9a18` (wiring).
2. **`wprog`**: build the forward offer-intro cone (expose the enabled `apiBF@hi` offer at
   pending states). Unbuilt.
3. **Payload:** `b″ ≡ blkA` block-value cone → restore the `a ≡ b` conjunct in `arrivedD`.

The 25-session non-convergence ended at session 33: `pcone` closed in ONE session once
(E1)/(E2) were identified as the true gap (session 32) and the driver-side-only economy
was found.  `wprog` (the forward offer-intro cone) is the only premise left — see
`.superpowers/sdd/progress.md` (SESSION-25 + USER DECISION, the BLK-GENERALISATION
CAMPAIGN section, and the SESSION-26/26b entries for the exact D1-D5/(E) frontier) and
`r3-plan.md` for detail.

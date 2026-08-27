# Praos `BlockLiveness⁺` — STATUS (**UNCONDITIONAL** and **PAYLOAD-EXACT**, session 51)

**Endpoint module:** `CSP.Examples.Cardano_network.FourNode.Liveness.LTL.BlockLiveness`
(the unparameterised ∀-closure; the per-block proof lives in
`…FourNode.Liveness.LTL.BlockLivenessProof blkA`)
**Branch:** `examples/praos_liveness`  ·  **Green** (bare `EXIT=0`).

> **Layout note (restructure, 2026-08-10).**  This development used to live in a flat
> `NetworkVerification/Praos/` directory; it now sits under
> `FourNode/Liveness/` — `R2_Bisim/` (the shared `≈DR` layer), `LTL/` (this route:
> `Spec`, `BlockLivenessProof`, `BlockLiveness`, plus `Walk/`, `Value/`, `Evidence/`,
> `Archive/`) and `CSP_Refinement/` (the sibling ⊑FD route).  See
> `FourNode/Liveness/README.md` for the map.  **Nothing else changed** — same theorem,
> same proofs, same audit.  In the session log below, the historical short names
> `Praos.Sys*` / `Praos.Walk*` / `Praos.Pipe*` now denote
> `FourNode.Liveness.R2_Bisim.Sys*` / `…LTL.Walk.Walk*` / `…LTL.Value.Pipe*`
> respectively (with `PipeCellFalse`, `PipeValGate`, `PipeValArrived` in
> `…LTL.Evidence/`), and `FourNodeDiamondLiveness{,CSP}` are now
> `…Liveness.LTL.Spec` and `…Liveness.CSP_Refinement.Spec`.

**SESSION-51 (2026-08-10) RESTORED THE PAYLOAD CONJUNCT — the campaign is COMPLETE.**
`BlockLiveness⁺` is proved end-to-end with **NO premise module** and **no model
relaxation left**: `arrivedD b` again requires the delivered value to BE `b`, so the
headline reads "the block A produced is the block D receives".  All three scaffold
premises were closed earlier — `tprog` (via the campaign `dne`), `pcone` (session 33,
constructive), `wprog` (session 34, constructive) — and the last deviation, the
payload-agnostic `arrivedD`, is now closed too (sessions 35–51, constructive, no new
axiom, no `dne` in the value chain).  Endpoint `EXIT=0`.

---

## Result

`blockLiveness⁺ : BlockLiveness⁺`, where (from `LTL.Spec`)

```agda
BlockLiveness⁺At : Block₃ → Set _
BlockLiveness⁺At blkA = ∀ (b : Block₃) (tr : Trace (⊤ {0ℓ}) (breakableSystem blkA))
                      → (□ᵗ (¬ atom brkG1) tr ⊎ □ᵗ (¬ atom brkG2) tr)  -- breaks confined to one path group
                      → ∀ (n : ℕ) → ⟦ atom (producedA b) ⟧ (drop n tr) -- A hands out block b (apiBF sendBFBlock@hi on AB/AC, a≡b)
                      → ◇ᵗ (atom (arrivedD b)) (drop n tr)             -- THAT block arrives at D (apiBF recvBFBlock@hi on BD/CD, a≡b)

BlockLiveness⁺ : Set _
BlockLiveness⁺ = ∀ (blkA : Block₃) → BlockLiveness⁺At blkA
```

**In prose:** in the broken four-node diamond, **however node A is configured** (it produces
an arbitrary block `blkA`), if every `break` event stays confined to at most one of the two
candidate paths ({AB,BD} or {AC,CD}), then whenever node A hands out a block `b`, node D
eventually receives **that same block `b`**. Fairness-free.

**VERBATIM, the final `arrivedD` and its payload-agnostic companion**
(`LTL.Spec`):

```agda
arrivedD : Block₃ → FramePred 0ℓ (⊤ {0ℓ})
arrivedD b (step _ (evl (evLabel _ (apiBF l d recvBFBlock) a))) =
  ((l ≡ linkBD) ⊎ (l ≡ linkCD)) × (d ≡ hi) × (a ≡ b)
arrivedD _ _ = ⊥

arrivedD⁻ : FramePred 0ℓ (⊤ {0ℓ})
arrivedD⁻ (step _ (evl (evLabel _ (apiBF l d recvBFBlock) a))) =
  ((l ≡ linkBD) ⊎ (l ≡ linkCD)) × (d ≡ hi)
arrivedD⁻ _ = ⊥
```

**UNCONDITIONAL.  VERBATIM, the whole theorem block of `BlockLiveness.agda`:**

```agda
-- R3/R4 HEADLINE at FULL generality: A may be configured to produce ANY
-- block; the per-`blkA` proof is `LTL.BlockLivenessProof blkA`
blockLiveness⁺ : BlockLiveness⁺
blockLiveness⁺ blkA = BLP.blockLiveness⁺ blkA
```

No `module _ (wprog : …)` — the premise module is GONE from `AbstractLive`,
`BlockLivenessProof` and `BlockLiveness`.

**Proof spine** (`BlockLivenessProof`, at the module's `blkA`):

```
abstractLive             : abstractSystem ⊨ᵂ respondsAtoD b        -- R3 walk (AbstractLive → WalkEngineB, premise-free)
sysBisim                 : breakableSystem blkA ≈DR abstractSystem     -- R2 divergence-respecting bisim (SysBisim)
realAbs tprog            : Realisableᴿ abstractSystem               -- R3 (RealAbs, tprog from TProg via dne)
  ── ⊨-DRWB-invariantᴿ→ ──►  breakableSystem blkA ⊨ᵂ respondsAtoD b
  ── ⊨ᵂ⇒⊨ (TraceBridge)  ──►  breakableSystem blkA ⊨ respondsAtoD b
  ── descent-⊨ (ClassicalDescent) ──►  BlockLiveness⁺At blkA
  ── LTL.BlockLiveness (∀-closure) ──►  BlockLiveness⁺
```

### Audit (mainline = the transitive import closure of `BlockLiveness`)

*(Audit re-run fresh at the END of session 51, i.e. WITH the strengthened `arrivedD` —  `grep -rnE "^[[:space:]]*postulate[[:space:]]*$"`
over `FourNode/Liveness/` hits ONLY `LTL/Archive/ChoiceMatchSpike.agda:222` and
`LTL/Archive/Route2Spike.agda:137`; `{! `,
`NON_TERMINATING` and `Sized` hit NOTHING; `--allow-unsolved-metas` appears only in those two
spikes' pragmas and in prose.  Neither spike is imported.  `AbstractLive`, `BlockLivenessProof`
and `BlockLiveness` contain **zero** `module _ (…)` premise modules.  Endpoint `EXIT=0` at 20 s.)*

- **0 postulate, 0 hole, 0 unsolved meta, 0 `NON_TERMINATING`/`Sized`** in the closure.
  `grep -rnE "^\s*postulate|\{! |NON_TERMINATING|Sized"` over `FourNode/Liveness/` hits ONLY the two
  harvest spikes `LTL/Archive/ChoiceMatchSpike`/`LTL/Archive/Route2Spike` (which also carry the only
  `--allow-unsolved-metas` pragmas) plus prose lines in this file; neither spike is imported.
- **`dne` is the single classical axiom.**  The closure's classical base is EXACTLY
  {`Classical.dne`, `ClassicalDescent.¬¬F⇒F`, `Traces_Based.⟦G⟧⇒⟦G⟧⁺`,
  `Traces_Based.¬G⇒F¬`} (the latter three certified LEM-derivable in
  `ClassicalFromLEM`).  Use-sites: `TProg` (tprog), `Walk` (`getProd`, `conf⊎`),
  `descent-⊨`.  **The session-34 `wprog`-discharge chain uses NONE of it.**

---

## How `wprog` fell (session 34)

### The premise was FALSE as stated — and never needed

- **Was:** `(b : Block₃) (r : RState) → Pr b r → WEnabled (IntactApiClass b) (radec r)`
  — from any reachable pending state, some intact-path `apiBF@hi` is weakly enabled.
- **Consumer read (the pcone lesson, again decisive):** `wprog` was consumed ONLY by
  `WalkEnabled`'s three TERMINAL refutations inside `WalkDeliver` — never for progress
  (the trace supplies the steps; the μ-descent comes from `liftReach-ev-expose`).  The
  true demand: *a pending reachable state is never a `ret`/stuck τ*-descendant.*
- **Falsity (prose, machine-checkable but bypassed — the pcone pattern):** node A runs
  TWO independent produce drivers (`produce linkAB ⦀ produce linkAC`).  On a run confined
  to G2 breaks, the AB→BD leg can deliver fully, then the AC producer fires
  `sendBFBlock` (an api sync needing no medium) with link AC already broken
  mid-handshake.  The resulting reachable pending state offers NO `apiBF` at all —
  the intact leg has TERMINATED, the pending leg is wire-wedged; only `break` events
  (excluded from `IntactApiClass`) remain enabled.  No enabledness cone can exist.
- **The saving model fact:** an unbroken link's decode is
  `renameMap (copy fold) △ (break l ⟶₀ Skip)`, and the fold's force is a `react` at ANY
  cell phases (`fold-react`) — so **`break l` is offered at every unbroken-link state**,
  visible through the whole stack (`break ∉ ioES`, medium solo).  On a confined trace the
  protected group's two links never break, so a `break` offer exists FOREVER — terminal
  frames are impossible, pending or not.  `WEnabled`/`IntactApiClass` are bypassed
  entirely.

### The discharge chain (all green, no `dne`)

| piece | module | content |
|---|---|---|
| break-offer intro | `WalkBrkFire.sys-break-fire` | `broken (med s) l ≡ false ⇒ absDec s ─[ev break l]─► M` (`△-fire-Q` + explicit `⦀Fin` nest + `lift-med-whole-ev`) |
| inversion | `WalkBrkFire.sys-break-unbroken` | the converse (frozen `link-break-chan` + `link-broken-false`) |
| **decode transport** | `WalkBrkFire.unb-transport` | `radec r ≡ radec r′` carries unbrokenness — **dodges the radec-not-injective trap semantically** (the offer is readable off the tree) |
| terminal refutations | `WalkBrkFire.unb-{stuck,ret}-⊥` | an unbroken link refutes stuck/`ret` (the `wprog` replacement) |
| flag lifts | `WalkBrkLift` | `liftτ*-brk` (flags fixed), `liftReach-ev-brk` (nodes-solo), `liftReach-break-brk` (the `i ≡ l` pin `medium-break-drop` erases, + `bupd-miss`) |
| Unb fold + locate | `WalkUnbLocate` | `unbAlong` from `rinit` along the confined trace; `locateU` = `PipeLocate.locate` + `unbAlong`, glued by `unb-transport` |
| premise-free deliver | `WalkDeliverB` | `PrU = Pr × Unb gs`; terminals by `Unb` alone; positive steps run BOTH lifts on the same weak step + transport |
| side-fixed engine | `WalkEngineB` | `Cfᵂ gs` descent + `walkPosB` (the literal `Walk.walkPos` slot; ⊎ cased once) |

Commits: `8472bac` (fire) · `21f8cd0` (lifts) · `6780599` (fold+locate) · `0c372b9`
(deliver) · `97eaa79` (engine) · `d5cda78`/`b9f3e9a`/`94bbfa3` (wiring/premise deletion).

### Session-34 gotchas worth keeping

1. **`with` of a big application can exhaust the heap.**  `with locateU g1 b tr g n prod`
   blew the 28 GB heap; the applicative `let`-destructuring of the Σ (plus hoisting the
   per-side body to a top-level `walkSide`) checks in 19 s / 2.9 GB.
2. **No-eta coinductive projections are not invertible:** `force-renameMap-react`'s `{P}`
   must be passed explicitly (`{P = ⦀⋆ (map …)}`), exactly as `SysRoute` does.
3. **`⦀`/`decMed` are defined functions**, so meta-laden unification stalls — build steps
   at the EXPLICIT nest with all operands spelled out and a `refl` home-equality.
4. **Prefix offers stick on the link's `Fin` self-test** — `with i FinP.≟ i`, not
   `Net_Api-≟` at the event pair.
5. **`linkAB` etc. are definitions, not constructors** — clause patterns must be `Fin`
   literals (mirror `WalkBreakDrop.budget-drop`).

---

## The former deviation — **CLOSED in session 51** (history retained below)

### Payload-agnostic `arrivedD` (the `a ≡ b` drop) — **CLOSED**; was gated TRUE in session 35

- Not a premise but a **model relaxation**: `arrivedD b` fires on ANY `recvBFBlock@hi` on
  BD/CD regardless of payload.  So the headline is "**some** block arrives at D".
- **Discharge:** build the `b″ ≡ blkA` block-value cone through the copy cell, then
  restore the `a ≡ b` conjunct.

**SESSION-35 PHASE-1 GATE: the value invariant is TRUE** — the first *positive* gate
verdict of the campaign (the previous four gates each refuted their target).
`Praos.PipeValGate` (green, imported by nothing) machine-checks all nine edges of the
single value chain

```
nodeA driver `! blkA`  ⇒  A's BF server `bsWblk blkA`  ⇒  cell(AB,hi,BF) = `MsgBlock blkA`
  ⇒  relay's BF client `bcAblk blkA`  ⇒  relay driver `consuming/producing blkA`
  ⇒  relay's BF server  ⇒  cell(BD,hi,BF)  ⇒  D's BF client  ⇒  D's `recvBFBlock` value
```

each edge a table `refl` on `NodeSpecs.bfSnxt`/`bfCnxt` or an `Output` **`!`-pin**
(`prod-pp5-output` + `output-pins`; `srv-wblk-pins`; `cli-ablk-pins`).  The gate also
clears the three explicit worries: `Base.IDs` **discriminates** `N2N_ChainSync` from
`N2N_BlockFetch` and cells are keyed `(link, dir, IDs)`, so a CS payload never shares a BF
cell; **stale/second blocks are harmless** because *every* `MsgBlock` value on any leg is
`blkA` (so even a `draining` leftover carries it); the decoder placeholders
`consD blkA cp0` / `consuming blkA cp0` are **discarded** by the decode
(`cons-cp0-blind`/`cons-cp1-blind`) and cannot leak.

**Phase-2 statement layer built:** `Praos.PipeValInv` (green) — the eight-clause per-leg
`PipeVal l s`, base `pipeVal-init`, frame `pipeVal-frame`, and two cash-outs
(`pipeVal⇒client`, `pipeVal⇒recorded`).

- **Economy (kills the obvious plan):** value-refining `PipeInv` *in place* does NOT work.
  `MsgIsBlk`/`BFcHasBlk`/`BFsHasBlk` sit in **negative** position inside
  `Coupled`/`SrvCoupled` (they are the antecedents), so strengthening them *weakens* those
  invariants instead of delivering the value fact.  The value clauses must be positive,
  hence new — a parallel leaf, blast radius zero.
- **Economy:** `ConsValAt`/`RelayValOK` are vacuous before `cp4`, which keeps the whole
  ChainSync chain out of the invariant; sound because the delivered value is rebound at the
  `cp3 → cp4` hop from the BF client's held block (`cons-cp3-rebind` + `cli-ablk-pins`).

**SESSION-36: the anchor is BUILT and merged into the live chain.**  `WalkDExpose.DReport`'s
`dBD`/`dCD` and `WalkPr.DeliverSig` now carry the delivered block's tie-point:

```agda
DeliverSig r r′ e a =
  Σ[ c ∈ TwoLegs ]
    ( phOf c (toSys r) ≡ cp3 × phOf c (toSys r′) ≡ cp4
    × Σ[ b″ ∈ Block₃ ]
        (evLabel X e a ≡ evLabel Block₃ (apiBF (linkOf c) hi recvBFBlock) b″)
      × (cblkOf c (toSys r′) ≡ b″) )                    -- ← the SESSION-36 anchor
```

Since `DeliverSig` already pins `phOf c (toSys r′) ≡ cp4`, `PipeValInv.pipeVal⇒recorded` at
the delivering **successor** now discharges `b″ ≡ blkA`.  The last *structural* obstacle is
gone; what remains is the preservation build alone.

- Source: `Praos.WalkDAnchor` — `consD-c34-anchor` (the `cp3` hop's label value IS the slot
  value) and `consDAdv-of⁺` (the anchored classifier).  `WalkClassify` stayed READ-ONLY.
- **Design finding:** the anchor had to go *through* the classifier, not beside it — the
  peels `with consDAdv-of …` **before** they know the phase, so composing a conditional
  anchor afterwards would need injectivity of `decConsD l ∘ consD`, and decodes are not
  injective.
- **Same constructor arity throughout** (the conjunct went *inside* the existing `Σ`), which
  held the blast radius to 7 modules: `WalkDAnchor`, `WalkApiDrop`, `PipeNodeFixApi`,
  `WalkDExpose`, `WalkReachExpose`, `WalkPr`, `WalkDeliver{,B}`.
- **Rebuild cost measured: 8:52 wall, not a cold closure** — the expensive R2 layer
  (`SysIoLink*`/`SysOracle*`/`SysRoute`) sits *below* every edited module and stayed cached.

**Preservation engine scaffolded:** `Praos.PipeValStep` mirrors `PipeInvProd`'s per-step
engine at `PipeVal` and **discharges the medium-τ arm** (`pipeVal-drain`, `τpreserveV-med`,
`tauStepV-from`) plus the τ-run/weak-move folds (`stepEmitFromV`, `stepEmitV`).  A drain
empties a cell and moves no node, and `CellValOK empty = ⊤`, so a drain can only *discharge*
a value clause — `drain-preserve`'s distinct-links case analysis is not even needed.

**`arrivedD-BS` pre-flighted — NO AMBUSH** (`Praos.PipeValArrived`, checked against a
verbatim local copy so no rebuild was spent): `bs-atom stab` goes through at the strengthened
predicate with the *same* proof term, because `FrameSim`'s head `refl` identifies the whole
observation `evLabel X e a` — value included.

**Exact remaining obligations** (explicit combinator arguments in `PipeValStep`; no
postulate, no premise in any chain module):

```agda
TauIoV  l = (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M₁ N₁ M : NetProc}
          → ioES .mem (X , e) a
          → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁
          → absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁
          → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
          → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (PipeVal l (toSys r) → PipeVal l (toSys r′))

EvStepV l = (r : RState) {e : Event} {M : NetProc} → radec r ─[ ev (evl e) ]─► M
          → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (PipeVal l (toSys r) → PipeVal l (toSys r′))
```

Inputs already in hand for `TauIoV`: fill = `PipeValGate.srv-wblk-pins` ∘ `PipeVal` clause
(1)/(5); drain-into-client = `PipeValGate.cli-stream-reads` ∘ clause (2)/(6); the
peer-identification plumbing is `PipeSrvFire.fill-{up,dn}-nodes` / `PipeRecvSource`, already
built for `PipeInvS`.

**The client io arm now carries the block value too** (`94021ab`): `PipeCliIoDec.BfcIoSucc`
said only "the read payload *was* a block", never *which* block the reader ended up holding,
so no value invariant could cross a wire READ.  The link was free at the single construction
site (`bcStream --output … MsgBlock b--> bcAblk b` is the only block-gaining client row), and
is now carried as `CliBlkVal`, threaded through `BlkReadAt` (which gained a successor index)
and `CliIoCls`.  `CliBlkVal` is vacuous off the `MsgBlock` shape and *paired* with the
existing `PlIsBlk`, so every existing consumer keeps working by projection —
`PipeTauIo.cliOut-decode` needed one character of change.

> **Pattern, now seen three times** — `DReport`'s `b″`, `BfcIoSucc`'s payload block, and
> `arrivedD`'s own `a ≡ b`: the value identification existed *for free* at the producing
> site and was simply not carried into the interface, and each time it looked like a hard
> obligation from the consumer's side.  When a value fact seems unreachable, first check
> whether the producer had it and dropped it.

**Step (iv) is not a drop-in — recorded before it can ambush anyone.**  `WalkDeliverB` takes
its successor `r′` from `liftReach-ev-expose` (which also supplies the `DReport`), whereas a
`StepEmitV` fold builds its *own* successor with only `radec` equality relating them — and
`PipeVal` is a fact about the state, which a decode equality does not transport (the
`radec`-not-injective obstacle session 34 hit for `Unb`).  **Recommendation: fuse, don't
transport** — strengthen `WalkReachExpose.liftReach-ev-expose` to return the `PipeVal`
preservation map alongside the `DReport`, so there is only one successor.  The fallback is a
semantic transport in the `unb-transport` style, but only clause (7) is plainly tree-readable
(`dnClient l s ≡ bcBlk1 b` ⟺ the tree offers `recvBFBlock ! b`, `!`-pinned), so that route
would need `PipeVal` split into a tree-readable delivery half and a private half.

**Session 37: `TauIoV`'s four clause cores are built** (`Praos.PipeValFill`, green) —
`blockFill-srv-pins` (a BF server at `bsBlk1 b` fires the cell fill *only* with payload
`MsgBlock b`; one clause, because the other ten positions are already refuted by the frozen
`blockFill-forces-srv`), `hasBlk⇒isBlk1`, the three one-liner arms, and `cliRead⇒CliValOK`
(the drain-into-client arm — what session 36's `CliBlkVal` was for).

> ### The transferable rule — read it before starting any new value obligation
>
> **A decision procedure's output carries no evidence about the step that motivated it.
> If you need the step's content, take it from the step.**
>
> `PipeSrvFire.bundle-blkfill-srv′` is the cleanest instance: it returns `BFsHasBlk bfs`
> taken straight from the *decision* `bfsHasBlk? bfs`, never from the step, so the
> payload↔position match is short-circuited away before it can ever be observed — and from
> the consumer's side that looks like a hard proof obligation rather than a dropped field.
>
> Four-for-four so far: `WalkDExpose.DReport`'s `b″` (existential, tied to nothing),
> `PipeCliIoDec.BfcIoSucc`'s payload block (payload classified, position not),
> `arrivedD`'s own `a ≡ b` (dropped at the spec), and this one.  In every case the fact was
> **free at the producing site**.  So: **reading the producing site is the opening move, not
> the retrospective.**  Two corollaries that have each saved a session here: put the new
> conjunct *inside* an existing `Σ`/tuple arm so constructor arity does not change (binding
> sites stay untouched); and when a helper is already parametric over a predicate — as
> `bundleG-io-no-BF` is over its two peer no-offers, and `PipeBundleIoEvo.BFcDecodeP` is over
> `Cf` — you can often get the stronger fact with *no edit to the base module at all*.

**The fill arm's one remaining structural obstacle, diagnosed.**  `blockFill-srv-pins` needs
the *server's own* step, and `PipeSrvFire` never extracts one — its whole design is "no
cascade re-mirror; prove the bundle fact **by contradiction** against a 12-peer `⦀-noOffer`".
So `nodes-blockfill-hi` yields `upSrv l s ≡ bsBlk1 b` and hence `b ≡ blkA`, but not `b₀ ≡ b`
for the payload's block.

**Session 38 — SOLVED, and with no `PipeSrvFire` edit at all.**  The plan was to parametrise
its cascade over the peer no-offer; reading it first showed **the parametrisation already
exists as exported API**.  `bundleG-io-no-BF` takes both peer no-offers as explicit
arguments and `blockFill-forces-cli` is exported, so feeding it a server no-offer built from
`blockFill-srv-pins` refutes any fill whose payload is not the server's own block:

```agda
bundle-blkfill-val : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos)
     (bfc : BFcPos) (b : Block) (ip : InertPos) {l′ d′ pl Bd′}
  → absBundleG l cl sv csc css bfc (bsBlk1 b) ip
      ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) pl)) ]─► Bd′
  → PlIsBlk pl → pl ≡ blkPayload b

blkfill-cellValOK : … → PlIsBlk pl → SrvValOK (bsBlk1 b) → CellValOK (full pl)
```

Two clauses instead of an in-place refactor of a 477-line base module, and zero rebuild risk
for the live chain.  *Generalise: before editing a base module to add parametricity, check
whether it is already parametric — this module family repeatedly is.*

Also already over-provisioned in our favour: `PipeNodeIoEvo.top-nodes-io-evo`'s `edBD`/`edCD`
are **full `ConsDPh` equalities** (`legCons` only ever took `cong cph` of them), so `PipeVal`
clause (8) rides across an io for free.

### Session 39 — **`TauIoV` is CLOSED**

`Praos.PipeValTauIo` gives `tauIoV : (l : TwoLegs) → TauIoV l`, total and unconditional: the
io-sync arm of the `PipeVal` preservation is done.  Two leaves, both green first try:

- `Praos.PipeValFire` — the node routing mirror.  `SrvHitVal` (the value twin of
  `PipeSrvFire.SrvHit`, same four-way nesting), `nodes-blockfill-val`, the four per-node
  lemmas, and `srvHitVal-{up,dn}`.  The one `subst` that rewrites the server slot inside
  `absBundleG` is factored into a single `bundleVal` helper so it appears once, not four
  times.  `PipeSrvFire` stays byte-for-byte untouched.
- `Praos.PipeValTauIo` — the `tauIo-{in,out}` mirror.  All eight clauses discharged:
  (1)(5) `srvIoV`; (2)(6) INPUT via `PipeValFire`'s routing + clause (1)/(5), OUTPUT via
  `cellValOK-full⇒draining`; (3)(7) INPUT vacuous, OUTPUT via `cliValOutC` /
  `cliRead⇒CliValOK` / `CliBlkVal`; (4) `legRelay`; (8) free via `legConsD`.

> **Cost of flipping a clause from negative to positive position.**  Two small pieces were
> needed that `PipeTauIo` did not need — `plBlk?` and a repeated `cliValOut-decode` — both
> because `CellValOK` is *unconditional* where `PipeInv`'s `CellHasBlk` is its own
> antecedent.  Generalise: **turning a negative-position clause into a positive-position one
> costs exactly one decision procedure per payload-shaped antecedent that used to come for
> free.**

> **The producer-site check paid a fifth time — positively, for the first time.**  Opening
> `EvStepV` by reading its producing site found `PipeBundleEvo.BfsSucc` *already* carries
> `(bfs′ ≡ bsBlk1 b″)` together with the label pin, so `EvStepV`'s server arm is already
> served.  Read the producing site even when you expect bad news.

### Session 40 — `EvStepV`'s two value pins are built

- **`ldCons` anchored** (`a0dd5a6`).  `LegDriverStep.ldCons`'s label field now carries
  `(cblkOf l s′ ≡ b″)` inside the existing `Σ`, so **arity is unchanged and `PipeEvStep`
  needed no edit at all** — all four of its consumers bind the label as `_`.  Construction
  reuses `WalkDAnchor.consDAdv-of⁺`, so the conjunct is `refl` and two `where` blocks are
  deleted.  Third use of the arity-preserving move; it has never cost more than the module
  defining the field.
- **The client api value pin** (`a5d2968`), the eighth dropped-value instance:
  `recvBFBlock-src-val : absBFc l d (bcBlk1 b) ─[ … recvBFBlock … a … ]─► M → a ≡ b`.
  `PipeRecvSource.recvBFBlock-forces-src`'s one inhabited clause returns `tt` without
  inspecting the step, yet the table gates `recvBFBlock` at `bcAblk b` on `x ≟ b`.  One
  clause; the other ten positions are already refuted by the frozen lemma.

**The three remaining threadings, each pinpointed to a named field.**  All four api
obligations are understood; what is left is carrying the pins up through interfaces that
currently project them away.

1. ~~client → `wUp`/`wDn`~~ — **DONE (session 41, `08b7fa4`).**  `ldCons`'s label field gained
   a third conjunct `(dnClient l s ≡ bcBlk1 b″)`, inside the existing `Σ`, so `PipeEvStep` is
   still byte-for-byte untouched — the **fourth** consecutive arity-preserving strengthening.
   Clause (7) now hands clause (8) its value: `dnClient l s ≡ bcBlk1 b″` + `CliValOK` gives
   `b″ ≡ blkA`, and `cblkOf l s′ ≡ b″` carries it to the recorded block.  `wDn` itself was
   left alone.  Witness: `PipeValFill.bundle-recv-cliPos`, built on the already-parametric
   `bundleBF-ev-forces`, so `PipeBundleRecv` was not edited either.
2. **relay** — clause (4).  **Anchor built** (session 42, `904b811`):
   `WalkDAnchor.consCP-c34-anchor`, which is `consD-c34-anchor`'s proof verbatim with
   `produce l₂ hi` for the `>> Skip` continuation — `cpStepKindL-of` drops the tie exactly as
   `consDAdv-of` did.  Ninth instance of the pattern; third time the fix was the previous fix
   with one substitution.  Remaining wiring, all shapes fixed:
   (a) `cpStepKindL-of⁺` — 13 clauses, widening the label component inside the existing `Σ`
       to `… × (relayBlk x′ ≡ b″)`; the `consuming b cp3` clause is the anchor and the other
       twelve are *vacuous* (the component's hypothesis is `RelayPre x → RelayHas x′`, and
       only the `c34` hop crosses `RelayPre` to `RelayHas` — confirmed against `PipeInv`:
       `RelayPre` is `⊤` exactly on `consuming _ cp0..cp3`, `RelayHas` exactly on
       `consuming _ cp4..cp6`).  `relayBlk : CPPh → Block₃` belongs in `PipeValInv`.

       **DONE (session 44, `fa9607f`) — `Praos.PipeValRelay.cpStepKindL-of⁺`, all 13
       clauses, green.**  The component is stated as `x′ ≡ consuming b″ cp4` (the
       successor's *shape*) rather than `relayBlk x′ ≡ b″`, for the ICE reason below.
       Added with it: `WalkDAnchor.cons-c34-anchor` (the bare `decCons` anchor, no bind
       wrapper) and `PipeValInv.relayBlk`.

       > ### SYMPTOM: Agda 2.8.0 dies with `__IMPOSSIBLE__` at `Substitute.hs:139`
       >
       > **What you see.**  Not a type error — an *internal error*:
       > `__IMPOSSIBLE__, called at src/full/Agda/TypeChecking/Substitute.hs:139:33`.
       > It is a de Bruijn fault during **with-abstraction**, and because it arrives with no
       > goal and no location in your own code it reads like a proof problem.  It is not.
       >
       > **Trigger.**  Applying a **function** to a `with`-abstracted variable inside the
       > result type — here `relayBlk x′ ≡ b″`, with `x′` the `with`-bound successor.
       >
       > **Workaround.**  Equate the variable to a **constructor form** instead:
       > `x′ ≡ consuming b″ cp4`.  Typechecks immediately.
       >
       > **Rule: never apply a function to a `with`-abstracted variable inside the result
       > type.**  Fourth distinct `with` hazard in this catalogue — after the
       > module-parameter slot, the leg-matching projections, and heap exhaustion on big
       > applications — and **the only one that manifests as an ICE rather than a stuck
       > goal**, which is exactly why it needs to be findable by symptom.
       >
       > The constructor form is also the **better interface on the merits**, not merely a
       > workaround: the consumer reads `relayBlk` off the equation.  Good outcome, bad cause.
       >
       > **Related gotcha, same session:** `IsSBB`, `decCons-sbb-⊥` and `decProd-sbb-pp5`
       > live in **`PipeProdFire`**, not `PipeEvRelay` where their callers sit.  Run the
       > helper-export pre-flight before writing an import block.

       > **Cost correction — this is a full MIRROR, not a delegation.**  The vacuous clauses
       > cannot delegate to `cpStepKindL-of`, because it returns `x′` *abstractly* and
       > `RelayHas x′` then does not reduce; and the `cp3` clause cannot mix the anchor's
       > `x′` with `cpStepKindL-of`'s, since that would need injectivity of `decCP l₁ l₂`.
       > So all 13 clauses must be re-derived over `bind-ev-inv`/`consAdv-of`/`consAdv→rk`/
       > `decCons-sbb-⊥`/`prodAdv-of`/`prodAdv→rk` (`consAdv→rk`/`prodAdv→rk` are exported;
       > check the rest before starting).  **This is the general shape of the whole remaining
       > tail:** the base cones classify by PHASE and existentialise VALUES, so a
       > value-carrying variant never composes with its phase-only original — it is always a
       > fresh per-clause mirror.  Budget the tail by clause count, not by "copy with
       > substitutions".
   (b)+(c) **DONE (session 45, `ae2dead`).**  `wUp` widened to
       `BFcHasBlk (upClient l s) × (Σ[ bc ] (upClient l s ≡ bcBlk1 bc) × (relayOf l s′ ≡ consuming bc cp4))`;
       the two produce-leg peels needed nothing (their `wUp` is already a total refutation,
       and `⊥-elim` inhabits the widened pair).  `PipeEvStep` came in at **one** site, not two
       — `legStep→pmono`/`legStep→rmono` bind `wUp` as `_`.  First and only `PipeEvStep` edit
       in six consecutive strengthenings.

**Threading 2 is COMPLETE**: clause (3) now hands clause (4) its value, exactly as clause (7)
hands clause (8) its value.

### Session 46 — every leaf pin is now built

`PipeValFill.decProd-sbb-val` / `decProd-sbb-blkA` (the producer's `!`-pin at LTS level) is
the **tenth** dropped-value instance: `PipeProdFire.decProd-sbb-pp5` returns only the phase.
One clause, green first try.

> ### The rhythm of this arc — budget by it
>
> Ten instances in, the work is completely regular, two parts per obligation:
>
> 1. a **leaf pin** (`!`-pin or position-pin) — one clause, always green first try, because
>    the fact is definitionally present at the table or the `Output` node;
> 2. a **cone threading** carrying that pin up through a peel that classifies by *phase* and
>    existentialises *values* — always a fresh per-clause mirror, never a wrapper.
>
> Part (1) takes minutes; part (2) takes the session.  **All the leaf pins are now built**
> (`blockFill-srv-pins`, `recvBFBlock-src-val`, `cliRecv-pos`/`bundle-recv-cliPos`,
> `cons-c34-anchor`/`consCP-c34-anchor`/`consD-c34-anchor`, `decProd-sbb-val`); what remains
> is threading.  At the observed rate that is 2–4 sessions of volume, with **no design
> questions left open**.

### Session 48 — step (v) DONE, and the costing was pessimistic

`Praos.PipeValProd` (green) gives
```agda
prodFire-blkA-AB : (r : RState) {b : Block₃} {M}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkAB hi sendBFBlock) b)) ]─► M → b ≡ blkA
prodFire-blkA-AC : the AC mirror
```
plus `nodeA-sbb-blkA-{AB,AC}` and `nodes-sbb-blkA-{AB,AC}` over the same dispatch.

> **A PARALLEL LEAF beats a widening when the two facts are independent.**  The phase fact
> (`prodOf l ≡ pp5`) and the value fact (`b ≡ blkA`) are read off the *same* step but neither
> needs the other — so instead of giving `nodes-sbb-{AB,AC}` a product conclusion (a type
> change with no `Σ` to widen, costed at ~4 consumer sites) the value cone is built *beside*
> it.  **`PipeProdFire` untouched, zero consumers moved: costed 4 sites, delivered 0.**
> Add this to the decision procedure: existing `Σ` ⇒ widen inside it; no `Σ` ⇒ **ask whether
> the new fact is independent of the old one, and if so build a parallel leaf** before
> paying for a type change.

The ICE-dodging interface worked as designed: `SbbVal l e a = (b : Block₃) → evLabel X e a ≡
evLabel Block₃ (apiBF l hi sendBFBlock) b → b ≡ blkA`, so the *caller* supplies the label
equation (`refl` at `prodFire-blkA-{AB,AC}`), and inside the cone the driver step is
transported first to the pinned phase then to the pinned label.  No projection off a
`with`-abstracted variable.  *Universe gotcha:* `evLabel` lands in `Set₁`, so `SbbVal`
returns `Set₁`.

> **Threading 3 — BOTH ROUTES MEASURED; it collapses to a parallel leaf and NO
> `driverExpose` change.**
>
> *Upstream server (clause (1)) — free.*  `BfsSucc`'s block arm already carries the label pin
> `evLabel X e a ≡ evLabel Block₃ (apiBF l d sendBFBlock) b″`, and in `evStepV` the
> whole-system step is in hand; substituting along the pin and applying the already-built
> `prodFire-blkA-{AB,AC}` gives `b″ ≡ blkA`.  **No tuple append.**
>
> *Downstream server (clause (5)) — the measurement.*  Both candidate routes need a dispatch
> that reaches the relay's produce-leg driver step on BD/CD, because the value is pinned by
> `decProd`'s `!` and neither `DnSrvEvo` nor `ldRelay`'s `RelayStepKind` exposes that step:
> - *route A* — a `prodFire`-style parallel leaf on BD/CD: **just the dispatch** (branch 2,
>   0 consumer lines);
> - *route B* — driver-side via clause (4): **the same dispatch, plus** the `driverExpose`
>   tuple append, plus two `_`s in `PipeEvStep`.
>
> **Route A is strictly cheaper** — route B is route A plus overhead — so threading 3 reduces
> to building `prodFire-relayVal-{BD,CD}` beside `prodFire-blkA-{AB,AC}`.  Note its
> conclusion is *conditional*: the relay's produce driver is `decProd (dnLink l) hi b pp` with
> `b` its recorded block, so the lemma reads
> `… → RelayValOK (relayOf l (toSys r)) → b′ ≡ blkA`, taking `PipeVal` clause (4) as a
> hypothesis (available at every `evStepV` call site).  The `Set₁` gotcha applies here too —
> `evLabel` quantifies over `Set`.
>
> **PRE-FLIGHT RESULT — one prerequisite is MISSING, and it is the reason to budget ~200 L
> rather than ~120 L.**  A BD/CD dispatch has to refute **node A**, and there is no
> `nodeA-link`: `PipeProdFire` exports `nodeB-link`/`nodeC-link`/`nodeD-link` but *not* the
> node-A analogue (it never needed one, because its two productive lemmas are exactly node A's
> own links).  Build it first — a ~20-line mirror of `nodeB-link` over `decProd-ev-link` on
> both produce arms.  Everything else the dispatch needs *is* exported:
> `decCP-sbb-⊥` (`PipeProdFire:194`, already the right shape — a `sendBFBlock` on a link ≠ `l₂`
> out of `decCP` is refuted), `decCons-sbb-⊥`, `sbb-along`, `pp0≢pp5`, `decProd-ev-link`,
> and `PipeValInv.RelayValOK`.
>
> Revised inventory for threading 3's downstream half: `nodeA-link` (~20 L, NEW prerequisite)
> · `decCP-sbb-val` (8 clauses, ~30 L) · `nodeB-sbb-blkA-BD` / `nodeC-sbb-blkA-CD` (~30 L each)
> · `nodes-sbb-relayVal-{BD,CD}` (~35 L each) · `prodFire-relayVal-{BD,CD}` (~10 L each)
> ≈ **200 L**.
>
> **BOTH PREREQUISITES NOW BUILT** (session 49, `ba80539` + `894b94d`, in `PipeValProd`):
> `nodeA-link`, and — a **second** prerequisite the first pre-flight MISSED —
> `decConsD-sbb-⊥` / `nodeD-sbb-⊥`.
>
> ### Rule extracted from that miss
>
> The first pre-flight checked which `node*-link` lemmas existed but **not which per-node
> `sendBFBlock` refutations existed**.  `PipeProdFire`'s dispatch only ever targets node A's
> links (AB/AC), so it refutes every *other* node by **link disequality alone** and never needs
> a per-node sbb-refutation — its header says of node D simply "both links differ".  A BD/CD
> dispatch cannot use that argument for node D, which **owns** both those links.
>
> **A dispatch on link `l` needs an sbb-refutation exactly for the nodes that OWN `l` but do
> not produce on it.**  For BD and CD that is node D in both cases, so the one lemma family
> serves both links, and nodes A/B/C stay refutable by link disequality.  When pre-flighting a
> dispatch on a *new* link, enumerate the link's owners first, not just the helper names.
>
> **THREADING 3 IS COMPLETE** (session 49, `6b10c91` + `0c7092a`).  Downstream half built as
> `decCP-sbb-val` · `nodeB-sbb-blkA-BD` / `nodeC-sbb-blkA-CD` · `nodes-sbb-relayVal-{BD,CD}` ·
> `prodFire-relayVal-{BD,CD}`, all in `PipeValProd`:
> ```agda
> prodFire-relayVal-BD : (r : RState) {b : Block₃} {M}
>   → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkBD hi sendBFBlock) b)) ]─► M
>   → RelayValOK (SN.NodeStateB.cp-B (nB (toSys r))) → b ≡ blkA
> ```
> conditional on `PipeVal` clause (4), available at every `evStepV` call site.  Route A held
> as measured for this half — no `PipeEvStep` edit, and `PipeProdFire` still byte-for-byte
> untouched.
>
> ### CORRECTION (session 50) — the tuple append IS needed after all
>
> Session 49 reported "no `driverExpose` tuple append" for threading 3.  That was **wrong**,
> and checking it before assembling `evStepV` is what caught it.  The claim conflated two
> things: `prodFire-blkA-{AB,AC}` / `prodFire-relayVal-{BD,CD}` do supply
> `b″ ≡ blkA` **for free**, but they supply it *about a `b″` you must already have* — and the
> only thing that ties the successor server position to a fired value is
> `PipeBundleEvo.BfsSucc`'s block arm
> `Σ[ b″ ] (label pin) × (bfs′ ≡ bsBlk1 b″)`, which `srvEvo⇒fwd` **projects away** into
> `UpSrvEvo`/`DnSrvEvo`:
> ```agda
> UpSrvEvo l s s′ = (upSrv l s ≡ upSrv l s′)
>                 ⊎ ((BFsHasBlk (upSrv l s′) → ⊥) ⊎ ProdSent (prodOf l s′))
> ```
> — the third arm carries no position and no value, so `SrvValOK (upSrv l s′)` is
> **unreachable** from `driverExpose` as it stands.  This affects **both** halves, upstream and
> downstream alike; the downstream lemma being conditional on clause (4) was never the issue.
>
> **So threading 3 still needs the append**: carry `BfsSucc`'s block-arm witness for each of
> the four server slots, appended at the **end** of `driverExpose`'s returned tuple so its one
> destructuring site (`PipeEvStep:249`) gains only `_`s and `srvEvo⇒fwd`'s existing callers
> are untouched.  Once appended, `prodFire-blkA-{AB,AC}` and `prodFire-relayVal-{BD,CD}` close
> clauses (1) and (5) immediately — those parts really are built.
>
> *Lesson:* "fact F is free" and "the object F is about is in scope" are different claims.
> When a value fact is supplied by a lemma keyed on an existential, check that something still
> in the interface **binds** that existential.
>
> ### Append pre-flight (session 50) — THREE modules, and an upstream/downstream asymmetry
>
> Enumerating where each of the four server slots' `BfsSucc` witness survives:
>
> | slot | where the value is projected away | append is |
> |---|---|---|
> | B's `bfS-BD`, C's `bfS-CD` (downstream) | `PipeEvDriverCone`'s own `srvEvo⇒fwd` calls (`:417`, `:532`) — the **raw** `srvEvo` is still in scope there | **local & cheap** |
> | A's `bfS-AB`, `bfS-AC` (upstream) | **one level lower**, in `PipeNodeAEvo`: `naEBaev1`/`naEBaev2`'s server field is already the projected `(fixed) ⊎ ((¬holding) ⊎ ProdSent (prod-AB na′))` (`PipeNodeAEvo:139-141`) | needs `PipeNodeAEvo` widened **too** |
>
> So the append touches **three** modules, not one: `PipeNodeAEvo` (widen the two peel fields —
> branch 1, the ⊎ arm already exists), `PipeEvDriverCone` (append the four witnesses at the end
> of `driverExpose`'s tuple; B/C's are the raw `srvEvo` already in scope, A's come from the
> widened peel), and `PipeEvStep` (its single `driverExpose` destructuring site, `:249`, gains
> `_`s).  `UpSrvEvo`/`DnSrvEvo` themselves stay untouched, so `srvEvo⇒fwd` and
> `srvCoupled-pres` are unaffected.
>
> *This is the second time the projection turned out to happen a level lower than the interface
> suggested* (the first was `srvEvo⇒fwd` itself).  When tracing a dropped value, follow it to
> the **producing peel**, not just to the last consumer that mentions it.
>
> ### The append is SMALLER than costed — no new fold is needed
>
> Reading `PipeNodeAEvo` to the bottom rather than stopping at its record: the fold is
> `srvEvo⇒up` (`:113`), whose block-arm clause already destructures
> `(inj₂ (inj₂ (b″ , lbl , _)))` — **and that `_` is exactly the `bfs′ ≡ bsBlk1 b″` link the
> value clause needs.**  It is discarded one line later.
>
> Consequently the thing to append is literally the peel's own input,
> `(bfs ≡ bfs′) ⊎ BfsSucc l hi bfs′ e a`, which is already in scope at every construction
> site (`PipeNodeAEvo:179` binds it as `srvEvo`; `PipeEvDriverCone:417`/`:532` likewise).
> **`SrvValEvo` *is* that type — so there is no new fold to write, only a value to carry.**
>
> Final append inventory:
> - `PipeNodeAEvo` — pair the existing server field with the raw `srvEvo` (both already in
>   scope at `:179` and its `naEBaev2` twin); ~6 lines, two construction sites.
> - `PipeEvDriverCone` — append the four raw witnesses at the end of `driverExpose`'s tuple
>   (A's from the paired peel field, B/C's are the `srvEvo` already bound at `:417`/`:532`).
> - `PipeEvStep` — `:249` gains `_`s.
>
> Then clauses (1) and (5) close immediately: `prodFire-blkA-{AB,AC}` for the upstream server,
> `prodFire-relayVal-{BD,CD}` (given clause (4)) for the downstream one.
>
> **Design note worth respecting:** `PipeNodeAEvo`'s header (`:22-25`) explains that resolving
> the pin *inside* the peel was deliberate — "the caller never has to relate a second peel of
> the same step to the first (`absNodesOf` is not known injective; the session-30 negative
> result)".  Carrying the raw witness **alongside** the resolved one preserves that property:
> nothing re-peels, so the session-30 obstacle stays avoided.
>
> The owner-enumeration rule predicted the dispatch shape exactly and found every
> prerequisite up front: node A via `nodeA-link`, node C via `nodeC-link` (BD dispatch) /
> node B via `nodeB-link` (CD dispatch), node D via `nodeD-sbb-⊥` in **both**.  A
> `sendBFBlock` out of `decCP` can only be the produce arm's `pp5` hop; the `cp6` hand-off is
> refuted by **phase** (`pp0 ≢ pp5`) rather than by link, because here the fired link *is*
> `l₂` — the one place this dispatch differs from `PipeProdFire.decCP-sbb-⊥`.

### Session 51 — **`StepEmitV` is UNCONDITIONAL**, and step (iv) has a CHEAPER ROUTE

Three green commits (`c89baaf`, `5b123d3`, then the walk layer), endpoint re-verified
`EXIT=0` at 20 s after each.

**(1) The append — FOUR facts, not one.**  The session-50 pre-flight costed the append
as carrying `BfsSucc`'s dropped block for the four server slots.  That was right but
*incomplete*: `RelayStepKind` and `ConsAdv` are **phase-only too**, so `PipeVal`
clauses (4) and (8) were equally unreachable from `LegDriverStep`.  All four are now
carried, in a record appended BESIDE the phase data (never inside it, so
`legStep→pres`/`→pmono`/`→rmono` are untouched):

```agda
record LegValStep (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ}
                  (e : Net_Api Payload X) (a : X) : Set₁ where
  constructor lvStep
  field
    lvUpSrv : SrvValEvo (upLinkOf l) (upSrv l s) (upSrv l s′) e a
    lvDnSrv : SrvValEvo (linkOf   l) (dnSrv l s) (dnSrv l s′) e a
    lvRelay : (RelayPre (relayOf l s) → ⊥)
            → RelayValOK (relayOf l s) → RelayValOK (relayOf l s′)
    lvCons  : ConsHeld (phOf l s) → cblkOf l s′ ≡ cblkOf l s
```

Feeders widened, all green first try:
- `WalkDAnchor.consDAdv-of⁺` `+ (ConsHeld (cph cd) → b′ ≡ cblk cd)`;
- `PipeValRelay.cpStepKindL-of⁺` `+ ((RelayPre x → ⊥) → RelayValOK x → RelayValOK x′)`;
- `PipeNodeAEvo`'s two peel server fields **paired** with the raw `srvEvo` (arity
  unchanged; the resolved arm stays resolved, so session 30's no-re-peel property holds).

> **`consAdv-of` returns exactly `b` at cp0/cp2/cp4/cp5 — and existentialises it.**
> The eleventh and twelfth instances of the dropped-value pattern were *inside a
> function that already computes the right answer*.  The fix is not a new pin but
> **not going through the existential**: the two post-receive clauses are re-derived
> directly off `output-ev-inv` / `⟶₀-ev-inv`, which name the tail concretely.  Generalise:
> **when a helper's clause body already produces the value you need, check whether its
> TYPE hides it — the cheapest fix may be to bypass the helper, not to widen it.**

> **`ConsHeld` is a local restatement of `PipeInv.ConsRecv`, and it has to be.**
> `WalkDAnchor` sits BELOW `PipeInv` (`PipeInv → WalkPr → WalkDExpose → WalkApiDrop →
> WalkDAnchor`), so importing `ConsRecv` is a **[CyclicModuleDependency]**.  Check the
> import direction before reaching for a predicate that "obviously" already exists.

> **The Substitute.hs:139 ICE did NOT fire** on `(RelayPre x → ⊥) → RelayValOK x →
> RelayValOK x′`, even though `x′` is the same Σ-bound successor that ICEd as
> `relayBlk x′ ≡ b″`.  Refinement of the session-44 rule: the hazard is an **equation**
> whose side applies a function to the abstracted variable; a **`Set`-valued** application
> in a function type is fine (the pre-existing `RelayHas x′` is the precedent).

**(2) `evStepV` — DONE, green first try** (`Praos.PipeValEvStep`, 1:33).  Label dispatch
verbatim `PipeEvStep.evStep`'s.  Consequently

```agda
evStepV    : (l : TwoLegs) → EvStepV l
stepEmitVᶠ : (l : TwoLegs) → StepEmitV l
stepEmitVᶠ l = stepEmitV l (tauIoV l) (evStepV l)
```

— **both** of `PipeValStep.stepEmitV`'s explicit combinator arguments are inhabited
(`tauIoV` session 39, `evStepV` here), so the weak-move preservation of `PipeVal` is
premise-free.  Style note that made it cheap: every function mentioning the imported
`PipeVal` is `with`-FREE, all case analysis living in **state-abstract** helpers over
plain `CPPh`/`ConsDPh`/`BFcPos`/`BFsPos`.  Two leg-level wrappers
(`consValStepFix`/`consValStepAdv`) exist only so `phOf l s` and `cph (consOf l s)`
become the same term — with `l` a variable both stay stuck.

**(3) The walk layer** (`Praos.PipeValWalk`, green first try, 30 s):

```agda
pipeVal-along-walk : (tr : WTrace ⊤ abstractSystem) (n : ℕ)
                   → producedA b (frameOf (drop n tr))
                   → Σ[ r′ ∈ RState ] (dropIdx n tr ≡ radec r′) × PipeVal l (toSys r′)
prodBlkA : (b : Block₃) (tr : WTrace ⊤ abstractSystem) (n : ℕ)
         → ⟦ atom (producedA b) ⟧ᵂ (drop n tr) → b ≡ blkA
```

`prodBlkA` is **half of the `arrivedD` repair, and unconditional**: whatever block node A
is *observed* to hand out is `blkA`.  Route: `PipeLocate.prodFrame-inv` (a `producedA`
frame IS a weak `sendBFBlock ! b`) + `PipeLocate.locate` (a reachable state at that frame)
+ `liftτ*-expose` + `PipeValProd.prodFire-blkA-{AB,AC}`.

---

### Step (iv) — the recorded FUSION plan is NOT the cheapest route.  Use the UPGRADE route.

Session 36 recommended fusing `WalkReachExpose.liftReach-ev-expose` so that one successor
carries both the `DReport` and the `PipeVal` map.  **Measured against the code, that is the
expensive route**: `liftReach-ev-expose` is three successors deep
(`liftτ*-expose` → `reach-ev-expose` → `liftτ*-expose`), and while the medium-τ arm fuses
for free (`WalkTauExpose.τreflect-med-expose`'s `s′` is literally
`PipeTauMed.drainSucc`'s), the **io arm does not**: `τreflect-io-expose` builds its
successor from `top-nodes-io-abs-fix`, whereas `PipeValTauIo` builds its own from
`top-nodes-io-evo` — two different cones, so the two `SysState`s are not convertible and
the whole `WalkTauExpose`/`WalkReachExpose` family would have to be re-mirrored.

**The UPGRADE route avoids threading `PipeVal` through the descent entirely.**  Keep the
existing chain proving the payload-AGNOSTIC delivery, and upgrade its *witness* at the top:

1. `LTL.Spec`: strengthen `arrivedD` with `(a ≡ b)` and add the current
   payload-agnostic definition beside it as `arrivedD⁻`.
2. Rename `arrivedD` → `arrivedD⁻` in the delivery chain only — `WalkDeliverB`,
   `WalkEngineB.descend*`/`walkSide` (+ the unimported `WalkDeliver`/`WalkEnabled`).
   Their content does not change at all.
3. New leaf: the **frame upgrade**

   ```agda
   arrUpgrade : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem) (m : ℕ)
              → b ≡ blkA
              → ⟦ atom (arrivedD⁻) ⟧ᵂ (drop m tr)
              → ⟦ atom (arrivedD b) ⟧ᵂ (drop m tr)
   ```

   `arrivedD⁻` pins the frame to `apiBF l hi recvBFBlock ! a` with `l ∈ {BD,CD}`; case that
   ⊎ FIRST, then run `pipeVal-along-walk` at the matching leg (the fold's `emit` is
   leg-indexed, so the leg must be known before the fold is run — this is why the ⊎ is
   cased first) to get `PipeVal l` at the frame's own reachable state, and read `a ≡ blkA`
   off clause (7).  With `b ≡ blkA` from `prodBlkA`, that is `a ≡ b`.
4. `WalkEngineB.walkPosB` applies the upgrade pointwise under the `F` witness
   (`⟦ F φ ⟧ᵂ` = index + frame witness), so `Walk`'s module-parameter type — which
   mentions the strengthened `arrivedD` — is met unchanged.

**Exact remaining obligations, with types.**  Only two are genuinely new:

```agda
-- (i) the terminal refutation for the new stopping predicate (7-line mirror of
--     WalkCausal.term-no-prod; `arrivedD⁻` is ⊥ on done/stuck/div frames)
term-no-arr : {t : NetProc} (w : WTrace (⊤ {0ℓ}) t) → IsTermᵂ w → (m : ℕ)
            → arrivedD⁻ (frameOf (drop m w)) → ⊥

-- (ii) the RECEIVE-frame value cone: the mirror of `PipeValProd.prodFire-blkA-AB`
--      on the delivering side
recvFire-blkA-BD : (r : RState) {a : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkBD hi recvBFBlock) a)) ]─► M
  → CliValOK (dnClient legBD (toSys r)) → a ≡ blkA
recvFire-blkA-CD : the CD mirror
```

`pipeVal-along-walk′` also needs generalising from `producedA b` to an arbitrary stopping
predicate + its terminal refutation (its `producedA` argument is used ONLY in the `√`
clause, via `term-no-prod`) — mechanical.

**Inventory for (ii), with the owner-enumeration rule applied.**  The peer and bundle
halves are BUILT: `PipeValFill.recvBFBlock-src-val`/`-blkA` (the client's `!`-pin) and
`PipeValFill.bundle-recv-cliPos` (bundle level, via the already-parametric
`PipeBundleRecv.bundleBF-ev-forces`).  What is missing:
- the NODE level — a verbatim mirror of `PipeEvCone.nodeD-{BD,CD}-recv-forces` with
  `bundle-recv-cliPos` in place of `bundle-recvBFBlock-forces-src` (~25 L each);
- the whole-NODES dispatch on link BD / CD.  **Owners of BD are nodes B and D**, so nodes
  A and C are refuted by link disequality (`PipeValProd.nodeA-link`,
  `PipeProdFire.nodeC-link`) but **node B needs its own `recvBFBlock` refutation** —
  node B's BD bundle is `absBundleG linkBD lo hi …`, so the client sits on `lo` while the
  fired event is at `hi`, and its BD server can never fire a client api
  (`recvBFBlock-server-absurd`).  `absBundleG-api-no` refutes on LINK mismatch only, so a
  **DIR-mismatch refutation is the one prerequisite to check for before starting** (the
  session-49 lesson, one link over).

### Session 51 (continued) — **THE UPGRADE ROUTE IS BUILT; the relaxation is CLOSED**

| step | content | state |
|---|---|---|
| (iii) `evStepV` | mirror of `PipeEvStep.evStep`'s label dispatch | **DONE** |
| walk layer | `pipeVal-along-walk`, `prodBlkA` (`b ≡ blkA`) | **DONE** |
| (ii) receive cone | `recvFire-blkA-{BD,CD}` (`Praos.PipeValRecv`) | **DONE**, green first try, 39.5 s |
| (i) + (iv′) | `term-no-arr`, generic stopping predicate, `arrUpgrade`/`arrUpgradeAt` (`Praos.PipeValArrive`) | **DONE**, 2:07 |
| (vi) | `arrivedD` strengthened, `arrivedD⁻` added, chain renamed, `walkSide` upgrades | **DONE**, endpoint `EXIT=0` 5:13 |

**`recvFire-blkA-{BD,CD}` — the owner-enumeration rule with a DIR twist.**  The
delivering mirror of `prodFire-blkA-{AB,AC}`:

```agda
recvFire-blkA-BD : (r : RState) {a : Block₃} {M : NetProc}
  → radec r ─[ ev (evl (evLabel Block₃ (apiBF linkBD hi recvBFBlock) a)) ]─► M
  → CliValOK (dnClient legBD (toSys r)) → a ≡ blkA
```

Owners of BD are nodes B and D, so A and C fall to link disequality — but node B's
refutation **cannot be a link argument**: its BD bundle is `absBundleG linkBD lo hi …`,
so the BF *client* sits on `lo` while the delivering event is at `hi`, and
`absBundleG-api-no` refutes on link mismatch ONLY.  Two new leaves close it —
`recvBFBlock-cli-dir` (one clause; the other ten client positions are already refuted
by the frozen `recvBFBlock-forces-src`) and `bundle-recv-dir` (on the
already-parametric `bundleBF-ev-forces`).  Because only the BUNDLE half of
`reflect-node-api` is inspected, the relay DRIVER never appears — **no `decCP`/`decProd`
tag classifier was needed**, which is what kept this at ~250 lines.

> **Refinement of the owner-enumeration rule.**  "A dispatch on link `l` needs a
> refutation for the nodes that OWN `l` but do not act on it" is right, but the
> refutation's *kind* depends on the api's POLARITY: a send-side dispatch refutes
> co-owners by link, a receive-side dispatch refutes them by **direction**, because
> the two ends of a link decode their client and server on opposite `Dir`s.  Pre-flight
> the disequality's *kind*, not just its existence.

**The upgrade, and why `PipeVal` never enters the descent.**  `WalkEngineB.walkSide`
runs the descent at `arrivedD⁻`, then upgrades the `F` witness:

```agda
walkSide gs b tr g n prod =
  let (r0 , eq0 , pr0 , unb0) = locateU gs b tr g n prod
      (k , ar , rest) = F-transport (atom arrivedD⁻) eq0 (drop n tr) (descend …)
  in  k , arrUpgradeAt b tr n prod k ar , rest
```

`arrUpgradeAt` runs `PipeValWalk.pipeVal-fold` **twice**, composing at the fold's own
successors:

```
rinit ──(n steps, stop at `producedA b`)──► rₚ ──(k steps, stop at `arrivedD⁻`)──► r_d
```

The second call's start equality is *literally* the first's output
(`dropIdx n tr ≡ radec rₚ`) and its trace is `drop n tr`, so `drop k (drop n tr)` never
has to be related to `drop (n + k) tr`.

> **THE DECISIVE OBSERVATION — index composition beats index arithmetic.**  `drop`'s
> type is indexed by `dropIdx`, so `drop k (drop n w) ≡ drop (n + k) w` is a
> **heterogeneous** equation and cannot be proved by a `cong`-style lemma.  Threading
> the fold's own start-equality (which `pipeVal-fold` already generalises over,
> `t ≡ radec r`) sidesteps the arithmetic completely.  Generalise: **when a fold is
> already generalised over its start, compose two runs instead of adding their
> indices.**

> **The `⊎` must be cased BEFORE the folds run.**  `pipeVal-fold` is leg-indexed and
> the two legs' folds build DIFFERENT successors — the same non-convertibility that
> killed the fusion route, one level up.  So `arrUpgrade` takes both legs' data and
> splits on `arrivedD⁻`'s `l ≡ linkBD ⊎ l ≡ linkCD` itself.

`arrivedD-BS` went through **unchanged**, exactly as session 36 pre-flighted: the
`FrameSim` head `refl` identifies the whole observation, value included.  Three
`LTL.Spec` sanity proofs moved to the 3-tuple, and the wrong-payload
frame is now **rejected** (`λ { (_ , _ , ()) }`).

Off-chain modules re-verified green after the spec change: `WalkEnabled`, `WalkDeliver`,
`WalkEngine`, `WalkLocate`, `PipeValArrived`, `PipeValGate`, `LivenessSpike`,
`LTL.Spec` / `CSP_Refinement.Spec` — all `EXIT=0`.

### What is left

**Nothing.**  `blockLiveness⁺ : BlockLiveness⁺` is unconditional, premise-free and
payload-exact.  Remaining optional cleanups only: the dead-code list below, and the
`PipeVal`-value modules that are now all on the mainline
(`PipeValInv`/`Step`/`Fill`/`Fire`/`TauIo`/`Relay`/`Prod`/`EvStep`/`Walk`/`Recv`/`Arrive`).

> ### HOW TO BUDGET A NEW VALUE FACT — the three-branch procedure
>
> Nine strengthenings measured.  Decide which branch you are in *before* costing:
>
> | branch | test | what you do | **measured cost** |
> |---|---|---|---|
> | **1** | the carrier has an **existing `Σ`/⊎ arm** | put the new conjunct *inside* it — arity unchanged, so sites that merely bind the field never move | **0–1 consumer lines** (six cases; `PipeEvStep`'s whole-arc delta is 3 insertions / 1 deletion) |
> | **2** | no `Σ`, but the new fact is **independent** of the old one (both read off the same step, neither needs the other) | build a **parallel leaf** beside the existing cone, duplicating only its refutation branches | **0 consumer lines** (`PipeValProd`: budgeted 4, delivered 0) |
> | **3** | no `Σ` **and** the facts are **entangled** (the new one must be produced where the old one is consumed) | pay for the type change | **1–4 consumer lines** |
>
> The two branch-3 cases were entangled, not merely `Σ`-less — that reclassification is what
> makes the procedure predictive rather than a happy path with exceptions:
> - `ldRelay` (threading 2) — no label field, and `RelayStepKind` is phase-only, so widening
>   it would break `cpadv-step`/`rk-fwd-mono`/`pres-relay-rk`.  Cost: widen `wUp` to a pair,
>   **1** site.
> - `nodes-sbb-{AB,AC}` (step (v), *as originally planned*) — bare `prodOf l ≡ pp5`
>   conclusion.  Costed at **4**; on inspection the facts turned out **independent**, so it
>   moved to branch 2 and cost **0**.  Check independence before assuming branch 3.
>
> Design note for step (v), to stay clear of the ICE rule: state the value half as
> `(b : Block₃) → evLabel X e a ≡ evLabel Block₃ (apiBF linkAB hi sendBFBlock) b → b ≡ blkA`
> — the caller supplies the label equation (it is `refl` at `prodFire-{AB,AC}`, where the
> carrier is already `Block₃`).  That keeps the generic cone from having to *project* a value
> out of a `with`-abstracted phase, which is the documented `__IMPOSSIBLE__` trigger.

> **Ordering finding — do step (v) BEFORE threading 3.**  Appending `BfsSucc`'s value to
> `driverExpose`'s tuple is mechanical but not sufficient: `BfsSucc` gives
> `Σ[ b″ ] (label) × (bfs′ ≡ bsBlk1 b″)`, and `b″ ≡ blkA` must still come from the co-firing
> driver.  For the relay's `dnSrv` that is now free from clause (4).  For node A's `upSrv` it
> is the structural `decProd … blkA pp5` pin — **whose node dispatch is exactly step (v)**.
> So threading 3 and step (v) are one unit, and the recorded (iii)→(iv)→(v) order has them
> backwards for this dependency.
3. **server** (`PipeEvDriverCone.srvEvo⇒fwd`).  `PipeBundleEvo.BfsSucc` *already* carries
   `Σ[ b″ ] (label pin) × (bfs′ ≡ bsBlk1 b″)`; `srvEvo⇒fwd` projects it away into
   `UpSrvEvo`/`DnSrvEvo`.  Recover by **appending** a value component to `driverExpose`'s
   returned tuple — appending at the end costs two `_`s in `PipeEvStep` and no constructor
   change.  Completes clauses (1)/(5).

Then assemble `evStepV : (l : TwoLegs) → EvStepV l` mirroring `PipeEvStep.evStep`'s label
dispatch (break: every node fixed and `phase` preserved ⇒ all eight clauses `subst`; io:
hidden; inert api and wire messages: refuted).  Clauses (2)/(6)/(3)/(7) need nothing new on
the api side: an api never touches a medium cell, and a client never *enters* `bcBlk1` on an
api, so `PipeBundleEvo.BFcDecode`'s `(BFcHasBlk bfc′ → ⊥)` is exactly right.

**Remaining order:** (iii) `EvStepV`; (iv) the fused `liftReach-ev-expose` per the finding
above; (v) `b ≡ blkA` at the produce frame — the `!`-pin *is* certified (`PipeValGate.prod-pp5-output` +
`output-pins`); what is missing is only that `PipeProdFire.nodes-sbb-{AB,AC}` returns a
phase rather than a product, so its cascade must be re-run with a product conclusion (a
`PipeProdFire` edit, not a leaf); (vi) *then* edit `arrivedD`, once.

### Dead code (green, unimported from the mainline — keep or delete on the user's call)

`WalkEnabled` (§3), `WalkDeliver`, `WalkLocate`, `WalkEngine.walkPosFrom`,
`PipeInvProd.SrvEvStep`/`evStepS-from`.  (`WalkDeliver.refute-weak`/`isRecvBF` and
`WalkEngine`'s generic `G⁺`/`F` plumbing ARE still imported by the new chain.)

---

## Build figures

| build | wall | peak RSS |
|---|---|---|
| `BlockLiveness` (endpoint) — warm | 15.8 s | 2.5 GB |
| `WalkEngineB` — warm | 19 s | 2.9 GB |
| full closure — cold (session-33 figure) | ~23 min | ~25 GB |

### Operational notes

- **Every `agda`/`git` invocation must run with the Claude sandbox disabled** (the
  libraries file and this worktree's `.git` resolve into the sibling checkout).
  `[LibraryError] … csp-ptree.agda-lib does not exist` means "sandbox off", not broken code.
- **One Agda build at a time**; judge only by `echo "EXIT=$?"`; detach cold builds.
- **The FALSE GREEN — same family as the phantom red below, opposite direction, and worse
  because it invents success.**  A chained `cd src` fails when cwd is *already* `src`; the
  `&&` short-circuits so the *edit never runs*; a trailing `agda` then re-checks the
  **unmodified** file and reports `EXIT=0`.  **Verify the edit applied — `git status` /
  `git diff`, or grep for the new name — before trusting any green.**  (Environmental, not
  operator error: it has caught more than one person on this campaign.)
- **The FALSE RED completes the set.**  `cwd` is **not stable** between shell invocations in
  this environment, so a *relative* `agda CSP/…/BlockLiveness.agda` fails with
  `openBinaryFile: does not exist` and `EXIT=42` whenever cwd happens to be the repo root
  rather than `src` — a **path** error that looks exactly like a typecheck failure.  Always
  give `agda` an **absolute** path (and keep `--include`/`.agda-lib` resolution in mind by
  running from `src`).
- **Shared root cause of all three:** `cwd` instability plus `&&` chains that mix `cd`, edits
  and builds turn a failed step into a misleading exit code *in either direction*.  **Rules:
  keep `cd`, edits, commits and verification builds as separate commands; use absolute paths
  in edit scripts AND in `agda` invocations; and confirm what actually changed (`git status`)
  before believing any exit code.**  Three distinct false signals have now come from this one
  cause: false green (edit skipped, stale build passes), phantom red (commit's exit read as
  the build's), false red (relative path unresolved).
- **Never chain a verification build behind `&&` after a `git commit`, and never read `$?`
  off the end of a mixed chain.**  A `git commit` with nothing staged exits **1**, which
  short-circuits the rest of the `&&` chain — the `agda` invocation never runs — and the
  trailing `echo "EXIT=$?"` then reports the *commit's* status as if it were the build's.
  That manufactures a phantom red in exactly the signal this campaign relies on.  Run
  commits and verification builds as separate commands.
- `.superpowers/` is **git-ignored** (`.gitignore:5`, `.git/info/exclude:41`), so
  `progress.md` is a working scratch log only — it is never committed.  **This file is the
  tracked record.**  Do not claim `progress.md` was committed, and do not force-add it.
- The `with`-abstraction hazards (module-parameter slot, leg-matching projections, and
  now the heap-exhaustion of clause-`with` on big applications) are catalogued in
  `.superpowers/sdd/progress.md` SESSION-32/33/34.

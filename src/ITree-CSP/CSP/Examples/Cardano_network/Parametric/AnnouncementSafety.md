# Announcement safety — what is proved, and where

*Paths below are relative to this directory
(`src/CSP/Examples/Cardano_network/Parametric/`) unless prefixed with `src/`.*

**Status:** complete, 2026-09-09, on branch `examples/n_node_parametric`.
Every module listed here typechecks with zero postulates, zero holes and no
`TERMINATING`/`NON_TERMINATING` pragmas of its own; §0 records the one classical
seam the transitive closure inherits.

---

## 0. Assumptions

What the theorem rests on, in decreasing order of how much a reader should care.

### 0.1 The scope assumption — safety is a property of the NETWORK

**Every node runs `nodeLogic`. There is no Byzantine or compromised node.**

This is not a technicality; it is the substance of what is and is not claimed.
The theorem says *a network of honest relays never announces an unminted
block*. It does **not** say a node is safe against a dishonest peer, and that
is not an oversight in the proof — it is false. `storeStep`'s `putEv` clause is
unguarded, so a node handed an arbitrary block over the wire will store it and
go on to announce it. §6 makes this concrete: a lone *good* node has exactly
the bad trace its broken twin does, reached by a different route.

Safety holds because every sender is itself well-behaved, which is why the
proof is assume-guarantee (§3b) rather than node-local.

### 0.2 The one open premise

`LinkCfgWf p` — each link's mini-protocol configuration is non-empty and
duplicate-free. It is the only hypothesis of `announceSafeT`, and it is
*decided* rather than assumed at each shipped topology, so `lineAnnounceSafeT`,
`starAnnounceSafeT` and `diamondAnnounceSafeT` carry no premises at all.

### 0.3 Premises that look open but are discharged

Listed so they are not mistaken for holes:

- `AnnSync apiES` and `BFSync apiES`, the two parameters of the `Assembly`
  module in `AnnounceSafeCopy.agda`, are discharged for the shipped alphabet by
  `annSync-apiES` and `bfSync-apiES`.
- `StoreInv ms held`, the store invariant of `wf-nodeLogic`, is discharged at
  the empty store.

### 0.4 Modelling assumptions

True by construction of the model rather than proved, and each one bounds what
the theorem means:

- **Every node starts with an empty store** — the theorem is about
  `nodeLogic n []`. A network whose nodes are pre-loaded with blocks is *not*
  covered, and the distinction bites: `RelayLive` runs from a non-empty initial
  store whose block is ill-announced at the empty minted set, so that
  configuration does not satisfy the store invariant and cannot be reused for a
  positive result.
- **Minting is an environment event.** Hashes enter the minted set only through
  `env _ _ envMint`. The environment may mint anything at all, including
  ill-announced blocks; those are *refused by the guard*, not prevented from
  being offered.
- **The medium is the concrete per-link multiplexer** carrying the configured
  mini-protocols, and `apiES` is the api alphabet. The proof is assembled over
  a copy medium and transported (§3d), so both media are in play, but the
  theorem is stated over the concrete one.

### 0.5 The classical seam

The modules listed in §4 introduce no postulates. Their transitive closure
inherits exactly one, through the medium transport:
`src/Semantics/DRImpliesFD.agda:70` postulates `¬-divergent→normal` — a
non-divergent tree reaches a τ-normal form — and `drbisim→fsim` uses it to
supply `FSim`'s `stab` field (`:145-146`). The transport step `drbisim→⊑F` is
defined in terms of it, so `AnnounceSafeConcrete` depends on it.

It is a certified seam, not an open assumption:
`src/CSP/Laws/ClassicalFromLEM.agda:128-131` derives `¬-divergent→normal` from
a single instance of double-negation elimination. So the theorem is classical,
not unsound — it holds in Agda extended with excluded middle.

This audit covers the seam reached by the transport, which is the one the
`⊑T` chain needs. It is not a mechanised audit of the entire import closure;
if an exhaustive one is ever wanted, the way to get it is to typecheck an
endpoint under `--safe` and read off what fails.

## 1. The property

A node may only announce, over LeiosNotify, a ranking block whose announced
endorser-block hash was actually produced by a mint. Nothing may announce a
block it invented, or one that arrived carrying a hash no mint ever created.

The specification is `AnnounceSafe.Generic.AnnounceSpecT`: a loop over the set
of hashes minted so far, whose offer map gates
`apiLN _ _ sendLNBlockAnnouncement` on membership in that set and passes every
other event through freely. Mints (`env _ _ envMint`) grow the set. It is a
*safety* specification — it constrains which announcements are possible, and
imposes no obligation to offer anything.

## 2. The theorem

`AnnounceSafeConcrete.agda` (commit `e390665a`):

```agda
LinkCfgWf p = ∀ l → linkConfig p l ≢ [] × Unique (linkConfig p l)

announceSafeT : ∀ (p : Params) (t : Topology p) → LinkCfgWf p
              → AnnounceSpecT ⊑T systemOf (λ n → nodeLogic n [])
```

For **every** `Params` and **every** `Topology`, over the **concrete** per-link
multiplexer rather than an idealised medium. `LinkCfgWf` — each link's
mini-protocol configuration is non-empty and duplicate-free — is the only
premise, and it is *decided*, not assumed, at each shipped instance:
`lineAnnounceSafeT`, `starAnnounceSafeT` and `diamondAnnounceSafeT`
(`AnnounceSafeInstances.agda`, commit `f86ec63b`) are premise-free,
via `from-yes (unique? cfg)`.

### Why `⊑T`

Announcement safety is a trace property: it constrains which sequences of
events are possible, and says nothing about refusals or divergence. `⊑T` is
therefore the order that states exactly the property.

The two neighbouring orders are not interchangeable here, and in opposite ways.
`⊑F` is strictly stronger — `⊑F→⊑T = proj₁` (`src/Semantics/Failures.agda:88`) —
so proving the property at `⊑F` would additionally oblige the implementation's
refusals to be justified, for no gain in what is asserted about announcements.
`⊑FD`, by contrast, would **not** give the property at all: it has no `⊇T`
conjunct, so it does not imply `⊑T`
(`src/Semantics/FailuresDivergences.agda:88-92`, counterexample in
`CSP.Examples.RefinementOrderCounterexamples`). Reaching for the
failures-divergences order because it "sounds stronger" would leave the
announcement constraint unstated.

## 3. How it is proved

The obstacle is that safety is **not** a node-local property. `storeStep`'s
`putEv` clause is unguarded (`NodeLogic.agda`), so a node in isolation will
happily store a block handed to it over the wire and then announce it. Safety
holds for a *network-wide* reason: every sender is itself well-behaved. The
proof is therefore assume-guarantee, and the four layers are:

**(a) A coinductive, shape-agnostic carrier.** `AnnounceSafeCarrier.Safe` is a
five-field coinductive record (`gate`, `onτ`, `onMint`, `onOther`, `noTick`)
indexed by the minted set. It is *shape-agnostic* by necessity: a
configuration-indexed family of states was tried and **refuted** — the
`sys-step` property is false for `⦀Fin⁺`. `safe→wsim` builds a weak simulation
from it and `wsim→⊑T` spends that as the refinement, so `Safe [] system` *is*
the theorem.

**(b) An assume-guarantee payload invariant.** `BlockProvenance.Wf` carries the
rely as an **argument** to its `stepW` field rather than as a global
hypothesis — which is what keeps it non-vacuous. Each component is `Wf` on its
own guarantee alphabet, with the events it cannot control left as its rely. The
circularity collapses without any well-founded measure, because `Minted` is the
*global* specification state, not a per-node one.

**(c) The seed.** `acceptMint`'s guard turns out to be *exactly*
`WellAnnounced (mintedAfter mb ms) b`. That single guard is what makes the
store's contents well-announced, and §6 below shows it is load-bearing.

**(d) Composition, then transport.** The alphabets union to cover everything,
`wf→safe` bridges to `Safe` (its `Covers` premise is what makes a single leaf's
partial-alphabet `Wf` fact *not* bridgeable), and the result is transported
from the copy medium to the concrete multiplexer along
`netLinkBreakable≈DR`, in the direction
`CopySpecBreakableA ⊑T NetworkLinkBreakableA` via
`proj₁ (drbisim→⊑F (drbisim-sym …))`.

## 4. File map

### The property and its proof

| File | Lines | Role |
|---|---:|---|
| `AnnounceSafe.agda` | 509 | states the property at `⊑T`; `AnnounceSpecT`, `AnnounceSafeT`, `AnnounceSafeTWith`, and the reduction to per-node obligations |
| `AnnounceInvariant.agda` | 318 | the residual obligations stated as types — `WellAnnounced`, `mintedAfter`, `Reach`, `Gated`, `MediumConfined` |
| `AnnounceSafeCarrier.agda` | 453 | the coinductive `Safe` carrier, its monotonicity, the composition lemmas (`safe-Par`, `safe-⦀`, `safe-⦀Fin⁺`, `safe-Hide`), and `safe→wsim` / `safe→announceSafeT` |
| `AnnounceSafeLeaves.agda` | 380 | the announcement-free thread leaves (`quiet→Safe`), `Env`, and the one-sided congruence `safe-ParE` |
| `AnnounceSafeCopy.agda` | 255 | the assembly: the whole N-node network over the copy medium, `AnnounceSafeTWith CopySpecBreakableA`; also `wf-node` |
| `AnnounceSafeConcrete.agda` | 117 | **the theorem** — transport to the concrete multiplexer |
| `AnnounceSafeInstances.agda` | 90 | premise-free line, star and diamond instances |

### The payload invariant (assume-guarantee layer)

| File | Lines | Role |
|---|---:|---|
| `BlockProvenance.agda` | 659 | the carrier `Wf`, `Carries`, `BlockOK`, and the congruences `wf-Par` / `wf-△` / `wf-⦀Fin` |
| `BlockProvenanceWfR.agda` | 434 | the returning-tree carrier `WfR` and its sequential/iteration closure — generic, split out so it elaborates on its own |
| `BlockProvenanceNode.agda` | 336 | the store and the four relay threads are `Wf` |
| `BlockProvenanceBF.agda` | 381 | the two BlockFetch peers, over their own alphabet `BFEv` |
| `BlockProvenancePeers.agda` | 297 | every configured peer, hence `nodeBundle`, on `peersG` |
| `BlockProvenanceCopy.agda` | 175 | the copy medium over its own alphabet |
| `BlockProvenanceMedium.agda` | 169 | the copy medium on `medG` — everything but its one rely, `input` |
| `BlockProvenanceSafe.agda` | 199 | **the bridge** `wf→safe`, gated by `Covers` |

### Non-vacuity controls

| File | Lines | Role |
|---|---:|---|
| `AnnounceContent.agda` | 146 | the spec forbids something — `badTraceRefused`, `goodTraceAllowed` |
| `RelayLive.agda` | 272 | the announcement is reachable — `announce-fires` (node level) |
| `AnnounceBadLogic.agda` | 90 | the deliberate break: `acceptMintBad`, one guard deleted |
| `AnnounceBadTrace.agda` | 246 | the bad trace of the broken node |
| `AnnounceSafeNegative.agda` | 189 | the refutation — `announceSafeT-node-FAILS` |
| `AnnounceControlNode.agda` | 191 | the level-matched control at `Wf` — `wf-goodNode`, `gated-goodNode`, `¬wf-badNode` |

### Supporting infrastructure (not specific to this property)

`Node.agda` (`systemOf`, `node`, `nodeWith`, `nodeBundle`),
`NodeLogic.agda` (the relay logic under test),
`Topology.agda`, `Assembly.agda`,
`FoldGate.agda`, `LeiosInstance.agda`, and the three
topology instances `LineInstance` / `StarInstance` / `DiamondInstance`.

## 5. Typechecking

From `src/`, endpoints only — imports are checked transitively:

```
cd src
agda +RTS -M16G -RTS CSP/Examples/Cardano_network/Parametric/AnnounceSafeInstances.agda
agda +RTS -M16G -RTS CSP/Examples/Cardano_network/Parametric/AnnounceControlNode.agda
```

Two cautions learned the hard way. Agda exiting 0 does **not** mean the module
was rechecked — demand the literal `Checking …` line for the endpoint, and if
it is absent delete only that endpoint's own `.agdai` under `src/_build/`. And
a long-running check here has always meant a type error, never mere size: the
whole chain is seconds to tens of seconds, so kill anything that runs long and
diagnose it rather than waiting.

## 6. Non-vacuity

A safety theorem is worthless if the guarded event cannot occur, and this
development had already shipped that failure mode twice before it was caught
(a `RUN`-shaped specification that imposed an offer obligation instead of a
constraint; and server threads driving the wrong direction over a medium with
no LeiosNotify cell, so no announcement was reachable at all). Three
machine-checked artefacts now close it:

| Risk | Closed by |
|---|---|
| the specification forbids nothing | `AnnounceContent` |
| the announcement is unreachable | `RelayLive.announce-fires` |
| the guard does no work | `AnnounceSafeNegative` and `AnnounceControlNode` |

The third deletes exactly one guard — `acceptMintBad (_ , b) hs = b ∷ hs` — and
proves the property **fails**:

```agda
announceSafeT-node-FAILS : ¬ (AnnounceSpecT ⊑T node nA (nodeLogicBad nA []))
```

`AnnounceControlNode` then removes the level mismatch by restating both sides
at node level over one shared alphabet `nodeG = peersG ∪α logicG`, all
premise-free and all at `ms = []`:

```agda
wf-goodNode    : ∀ n → Wf nodeG [] (node n (nodeLogic n []))
gated-goodNode : ∀ n → Gated [] (node n (nodeLogic n []))
¬wf-badNode    : ¬ Wf nodeG [] badNode
```

`Wf nodeG []` being inhabited for the good node and refuted for the broken one,
at one predicate and one alphabet, is what rules out the refutation holding
merely because `Wf` is unsatisfiable there.

### Why that control is at `Wf` and not at `⊑T`

The natural-looking alternative,
`RelyOK → AnnounceSpecT ⊑T node n (nodeLogic n [])`, is a **vacuity trap**. A
hypothesis of the form "this node performs no bad `output`" is false for the
*good* node too — its BlockFetch client peer accepts an arbitrary `MsgBlock b`
off the wire. A false premise makes the implication vacuously true, and equally
provable for the broken node, destroying the control it was meant to build.
`Wf` escapes this because its rely is an argument to `stepW`, never a global
hypothesis.

Reaching a genuine `⊑T` headline would mean moving the rely *into* the
specification — a wire-delivered block granting announcement permission the way
a mint does. That was scoped at 600–900 lines across two or three modules, and
rejected on more than cost: it forks the specification, so the node-level and
system-level theorems would then be about *different* specs, reintroducing
exactly the level mismatch the exercise set out to remove.

## 7. What is not proved

- **A system-level refutation.** Both negative controls are node level, as
  their module headers state. Building a system-level bad trace means driving
  the far node's `lnClientLoop` through the multiplexer's hidden
  `input`/`tx`/`ack`/`output` cells; there is no precedent for it in the
  repository, and `RelayLive` declined the analogous positive version for the
  same reason.
- **`gated-goodNode` at a general minted set.** It is stated at `ms = []`;
  `wf-node` is `∀ {ms}`, so a general version is available if wanted.
- **Liveness.** Nothing here says an announcement ever *must* happen.
  `RelayLive` witnesses one reachable announcement; that is all.

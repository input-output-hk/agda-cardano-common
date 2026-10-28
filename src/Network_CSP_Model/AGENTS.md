# Working in Network_CSP_Model

## Scope and purpose

This guidance applies to this directory and its descendants. This is the standalone
Agda library `cardano-network-csp`, nested inside `agda-cardano-common` but independent
of the enclosing `cardano-common` library. Its library root is this directory;
module names start with `Cardano_network` or `GovernorWedge`.

The project models Cardano node-to-node networking as coinductive process trees
(`PTree`) and proves properties using traces, stable failures, failures-divergences,
divergence-respecting weak bisimulation (`≈DR`), and LTL. Generic process-tree
semantics, CSP operators, and proof laws belong to the external `csp-ptree-agda`
library. Look there for existing laws before duplicating them locally; changes to
that dependency are separate from changes to these models.

## Read first

- For project goals, status, continuation, and handover, read
  [PROJECT_STATE.md](PROJECT_STATE.md) and apply
  [project-continuity](skills/project-continuity/SKILL.md). Inspect the current
  worktree before resuming its active milestone; update the state after meaningful
  progress or a change of direction. Keep the overall objective and completion
  criteria visible alongside the next task.
- [README.md](README.md): library setup and overview.
- [Cardano_network/README.md](Cardano_network/README.md): module map and reading order.
- [mini-protocols.md](Cardano_network/mini-protocols.md): protocol scope and claims.
- Read the relevant area's README and the comments on the actual theorem before
  changing it. Historical status documents contain snapshots; current types and
  imports determine what a theorem establishes. Do not repeat old line counts,
  proof-completion claims, or axiom audits without checking them.

Suggested source reading order: `Params`, `Base`, `Data`, `Net`, `Network`, a peer
such as `ChainSync`, `NetCommon`, `NetworkPar`, then a scenario or proof endpoint.

## Architecture

| Area | Responsibility |
| --- | --- |
| `Params`, `Base`, `Data`, `Net` | Abstract domains and equality instances; protocol IDs and directions; messages and payloads; wire, API, store, environment, and break events. |
| `Network`, `NetworkLink` | Multiplexer and its per-link rendering; `Network` also defines the copy-buffer specification `CopySpec`. |
| `NetCommon`, `NetworkPar` | Rename media and peers into `Net_Api`; compose and hide wire events; assemble uniform or configuration-driven peer bundles. |
| `BundleBridge`, `ApiAlphabet`, `MediumEquivA` | Bundle relations, shared API event sets, and equivalence of breakable media. |
| `KeepAlive`, `ChainSync`, `BlockFetch`, `TxSubmission`, `LeiosNotify`, `LeiosFetch` | API-driven mini-protocol client/server processes. `BlockFetch` is literate Agda. `LeiosNotifyP` and `LeiosFetchP` are prototype variants. |
| `NetworkVerification/` | Medium refinement, equivalence, deadlock/divergence freedom, and sanity probes. `PerLink/` develops the per-link equivalence. |
| `FourNode/` | Diamond A–B, A–C, B–D, C–D; uniform, configured, and breakable variants. |
| `FourNode/Liveness/` | Shared abstraction/bisimulation in `R2_Bisim/`; separate LTL and CSP-refinement routes in `LTL/` and `CSP_Refinement/`. |
| `Parametric/` | Topology-generic node assembly, concrete line/star/diamond instances, announcement safety, and block provenance. |
| `Parametric/Leios/` | Prototype peers, node stores and logic, safety properties and negative controls, concrete systems, and `NoLivelock/` proofs. |
| `Priority/` | BlockFetch priority over LeiosFetch at the send arbiter. Full-system construction alone is not a behavioural theorem. |
| `Terminable/` | Experimental graceful shutdown. |
| `GovernorWedge/` | Independent inbound-governor connection-management model, reachable wedge witnesses, invariants, and proposed fixes. |

## Semantic constraints

- Network instances are indexed by `(l : Link, d : Dir, id : IDs)` with
  `Link = Fin numLinks`. `linkConfig l` lists the active `(Dir × IDs)` pairs;
  unconfigured instances are absent and an empty interleaving returns `Skip`.
  Do not reintroduce the old per-protocol `Conn` model into current network code.
- Preserve distinctions between the faithful medium, `CopySpec`, renamed media,
  breakable media, and the fully composed system. A property of one does not
  automatically establish the corresponding property of another.
- Preserve explicit premises such as nonempty and unique link configurations,
  alphabet separation, and divergence freedom when applying congruence laws.
- Objects and identities are separate: `Block`/`RbHash`, `EB`/`EBHash`, and
  `Tx`/`TxHash`. Use `TxHash` in new code; `Txid` is a compatibility alias.
  Hash injectivity is not automatically a theorem, and slots are not object IDs.
- Definitional equality matters. Some faithfulness and sanity checks use `refl`
  on exact process terms. For example, the diamond deliberately retains its own
  `apiES`. Check these consumers before deduplicating definitions or reordering
  process compositions.
- Distinguish safety, deadlock freedom, divergence freedom, no livelock, delivery
  liveness, and existence of a finite trace. `NoLivelockL` concerns the concrete
  three-node Leios system after hiding; `LiveL` supplies a possible delivery trace,
  not a universal delivery theorem. Keep finite-carrier assumptions explicit.
- GovernorWedge models overlapping incarnations of one connection ID. Its release
  is atomic and its timeout untimed. Preserve the source pin, policy distinctions,
  reachability witnesses, and stated limitations in its README when changing claims.

## Agda conventions and proof integrity

- Use Agda 2.8.0 and preserve `{-# OPTIONS --guardedness #-}`. Match module names to
  paths; retain executable code fences in `.lagda.md` files.
- Follow local Unicode notation, explicit `using` lists, module parameters, and
  `Class.DecEq` instance conventions. Preserve universe levels where polymorphic.
- Keep coinductive definitions productive using the existing `iter`/`loop0` and
  `ptree`/`.force` patterns. Do not bypass termination with `NON_TERMINATING`,
  `TERMINATING`, or sized-type workarounds.
- Prefer forward type declarations for mutually recursive functions over new
  old-style `mutual` blocks. Add a short explanatory comment above new definitions.
- Do not close proof gaps by adding postulates, holes, or
  `--allow-unsolved-metas` to maintained proofs, or by weakening the requested
  statement. Keep experimental spikes outside theorem import closures.
- Distinguish local postulate freedom from assumptions in external dependencies.
  The four-node routes have different classical footprints; consult
  `LTL/BLOCKLIVENESS_STATUS.md` and `CSP_Refinement/STABR_STATUS.md` before making
  claims about them. An import audit is not a term-level axiom audit.
- Preserve small, cheap proof layers. In particular, do not introduce the heavy
  `SysBisim`/`SysOracle*` closure into modules deliberately parameterised over those
  facts. Use component lemmas and existing trace lifts instead of normalising a
  full composed-system step when that causes elaboration blowups.

## Validation

Run commands **from this directory**. `cardano-network-csp.agda-lib` declares
`standard-library`, `standard-library-classes`, and `csp-ptree`; register their
library files in the Agda libraries configuration (`~/.config/agda/libraries` or
`$AGDA_DIR/libraries`). Do not substitute the enclosing project's build setup.

There is no single all-modules test entry point here. Typecheck the changed module,
then the relevant downstream endpoint and existing sanity/negative-control modules.
Imports are checked transitively. Select commands appropriate to the change:

```sh
agda Cardano_network/ChainSync.agda
agda Cardano_network/NetworkVerification/NetworkLinkSanity.agda
agda Cardano_network/NetworkVerification/NetworkADeadlockFreeThm.agda
agda Cardano_network/NetworkVerification/NetworkADivergenceFreeThm.agda
agda Cardano_network/FourNode/FourNodeDiamond.lagda.md
agda GovernorWedge/Release.agda
```

Other important endpoints, to check when affected:

- `FourNode/Liveness/LTL/BlockLiveness.agda` and `ProvenanceD.agda`.
- `FourNode/Liveness/CSP_Refinement/LivenessProof.agda`.
- `Parametric/Leios/{Announce,Blob,Body,Vote,Cert,CertRb,Tx}SystemL.agda`.
- `Parametric/Leios/NoLivelock/{NoLivelockL,LiveL}.agda`.

These paths are relative to `Cardano_network/`. For GovernorWedge coverage, its
README lists `Timeout`, `Wedged`, `Invariant`, `FullFix`, `CMFix`, and `Release`;
run those six endpoints when changing the shared model.

Run **one Agda process at a time**. Heavy proofs need memory limits; the documented
Linux command is:

```sh
systemd-run --user --scope -p MemoryMax=25G -p MemorySwapMax=0 -- \
  agda Cardano_network/FourNode/Liveness/LTL/BlockLiveness.agda +RTS -M20G -RTS
```

Keep the RTS heap limit below the cgroup limit to allow RSS overhead. Do not add
an explicit `-c`; the Leios README records substantial slowdown. A cold four-node
build has been measured at about 45 minutes and 22 GB peak; these are historical
measurements, not runtime guarantees. Check resource availability before starting.

Generated interfaces live under `_build/2.8.0/agda/`. For an explicitly fresh
endpoint check, invalidate only its own `.agdai` and confirm its `Checking …` line
as well as a successful exit. Do not purge the whole cache routinely or describe
a cached success as a fresh check. Report commands, warnings, failures, and any
unperformed checks accurately. Documentation-only edits need no heavy proof rebuild.

## Legacy and experimental areas

Do not expect a blind sweep of every source file to pass:

- `BlockFetchRefinement/`, `EvBothProbe.agda`, and `NetModel.agda` are documented
  as awaiting migration from the old connection model.
- The Leios README records pre-existing failures in
  `Parametric/Spike/HideDiverge.agda`, `EvBothProbe.agda`, and the
  `NetworkVerification/Liveness/PipePair*` chain. Recheck status if working there;
  these reports are not permission to ignore a new regression.
- `FourNode/Liveness/LTL/Archive/` includes proof spikes with postulates and
  unsolved metas. `Terminable/NetworkTRefinement.agda` also has postulates.
  Keep these dependencies out of maintained endpoints.
- Files named `*Bad`, `*Negative`, or under `Negative/` can be intentional,
  typechecking counterexamples. Preserve the property they refute rather than
  treating their names as evidence of broken code.

## Workspace hygiene

Keep changes focused and preserve existing user edits and configuration symlinks.
Do not modify their external targets as part of a model change. Keep temporary
logs and scratch files outside the source tree; do not commit `_build/` or
`.agdai` files. Update nearby documentation when theorem scope or assumptions
change. Respect the existing contributor preference against AI co-author trailers
or assistant-session text in commit messages.

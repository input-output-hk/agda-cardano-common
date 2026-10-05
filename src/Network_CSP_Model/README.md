# Network_CSP_Model

CSP models of the Cardano node-to-node networking layer, mechanised in Agda.
Processes are written as process trees (`PTree`) and reasoned about through the
CSP semantic models (traces, failures, failures-divergences, divergence-respecting
weak bisimulation) and LTL, all provided by the
[csp-ptree-agda](https://github.com/input-output-hk/csp-ptree-agda) library.

This folder is its own Agda library, `cardano-network-csp`
(`cardano-network-csp.agda-lib`), separate from the enclosing `cardano-common`
library. It does not depend on `cardano-common`.

## Contents

| Folder | What it is |
|---|---|
| [`Cardano_network/`](Cardano_network/README.md) | The Ouroboros N2N mini-protocols (KeepAlive, ChainSync, BlockFetch, TxSubmission2, LeiosNotify, LeiosFetch) as client/server peer processes, the network multiplexer and its copy-buffer specification, whole-network systems built from them, and the proofs about them. |
| [`GovernorWedge/`](GovernorWedge/README.md) | A small standalone model of the `ouroboros-network` inbound governor's connection-management path, checking which interleavings wedge the governor and what each proposed fix does. |

### Inside `Cardano_network/`

| Subfolder | Topic |
|---|---|
| top level | Parameters, data and message types, the shared `Net`/`Net_Api` alphabet, the medium (`Network`, `NetworkLink`, `CopySpec`), the six mini-protocol peers, and the bundling of peers into nodes. |
| `FourNode/` | The four-node diamond scenario (A–B, A–C, B–D, C–D), its configurable and breakable-link variants, and the block-liveness proofs (`Liveness/`, with its own [README](Cardano_network/FourNode/Liveness/README.md)). |
| `NetworkVerification/` | Deadlock freedom, divergence freedom and refinement/equivalence of the medium against its specification ([README](Cardano_network/NetworkVerification/README.md)). |
| `BlockFetchRefinement/` | BlockFetch client/server and network refinements against abstract specifications. Written against the earlier per-protocol `Conn` model and not yet ported. |
| `Parametric/` | The topology-generic N-node layer: arbitrary topologies, announcement safety and block provenance, plus the Leios prototype (`Leios/`, with its own [README](Cardano_network/Parametric/Leios/README.md)). |
| `Priority/` | BlockFetch (Praos) prioritised over LeiosFetch (Leios) at each link's send arbiter ([README](Cardano_network/Priority/README.md)). |
| `Terminable/` | Experimental: a medium with graceful shutdown. |

See [`Cardano_network/README.md`](Cardano_network/README.md) for a reading order
and per-module descriptions, and
[`Cardano_network/mini-protocols.md`](Cardano_network/mini-protocols.md) for what
is modelled and proved for each mini-protocol.

## Setup

The models need Agda 2.8.0 and these libraries:

- [csp-ptree-agda](https://github.com/input-output-hk/csp-ptree-agda), which
  provides `csp-ptree`
- `standard-library`
- `standard-library-classes`

Clone csp-ptree-agda and register its `.agda-lib` file, together with the two
standard libraries, in your Agda libraries file (`~/.config/agda/libraries`, or
`$AGDA_DIR/libraries`):

```
git clone https://github.com/input-output-hk/csp-ptree-agda
echo "$PWD/csp-ptree-agda/csp-ptree.agda-lib" >> ~/.config/agda/libraries
```

## Typechecking

Run Agda from this directory. Module names are relative to it, for example:

```
cd src/Network_CSP_Model
agda Cardano_network/ChainSync.agda
agda GovernorWedge/Release.agda
```

Imports are checked transitively, and build artefacts go to `_build/` here.
Some of the larger proofs need a lot of memory. The subfolder READMEs give the
exact commands and memory limits for their endpoint modules.

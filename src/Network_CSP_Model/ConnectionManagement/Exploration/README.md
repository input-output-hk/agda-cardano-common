# Bounded supervised exploration

This is G5 stage 1. `Bounded` enumerates all successful dispatcher edges over an
explicit finite event alphabet, then all trace/endpoint pairs through depth `n`
whose visited states satisfy allocation cutoff `b`. No scheduler, dependency
reduction, equality-based merging, or ordering restriction prunes the search.
Duplicates in the input alphabet give duplicate branches. Nothing requires
decidable equality on the full supervised runtime or action type.

`Supervised.Search candidates` uses the actual `ServerPeersRelays` outer runtime
and G4's `label`/`decode` through `Alphabet.decodeAlphabet`. Thus the event carrier
is exactly the finite decoded list, including its nested payloads. Completeness
is **relative to that list**, not every constructor/payload combination formed
from small IDs. A new search must explicitly declare its alphabet; extending an
ID range does not implicitly add events. Finite input alphabets and finite depth
make this enumeration finite even though the underlying model has natural-valued
clock/delay inputs and allocation supplies.

For allocation cutoff `b`, `workerCarrier b`, `peerCarrier b`, `socketCarrier b`
and `promiseCarrier b` are separate typed finite sets of serials `[0,b)`.
`allocated` takes the maximum of the listed worker/peer capture/key serial bounds,
socket/promise serial bounds, entry/promise and peer/job supplies, selected retained
store sizes, and one reserved supervisor slot. See `Supervised.footprint` for the
exact fields; the four `*-bounded` lemmas certify every ID in the respective
`workers`/`peers`/`sockets`/`promises` projections. This is a capacity/identity
cutoff, not a byte-memory bound, total historical allocation count, or assertion
that every nested metadata field is traversed. Other identities and payloads are
restricted by the finite event list. Allocation pruning checks the initializer,
each intermediate state and the endpoint; it never changes `outerStep`.

The main statements in `Bounded` are:

- `enabled-sound` / `enabled-complete`: exact successful edges and endpoints for
  every action in the declared alphabet, at every state, before cutoff pruning.
- `events-sound` / `events-complete`: the same result for the raw bridge's event
  labels/offers. `absent-refusal` reuses the bridge's singleton-refusal theorem.
- `reach-sound`: every listed trace has length at most `n` and a `BoundedRun`;
  `real-run` erases its bound/coverage evidence to the real dispatcher execution.
  The existing `Raw.trace-intro` then gives a genuine CSP trace.
- `reach-complete`: every real carrier run whose states meet `b` and length is at
  most `n` is in the computed list. `BoundedRun` records precisely these premises.
- `frontiers` retains trace/state/report triples. `allocation-cutoff`,
  `depth-cutoff`, and `exhausted` are distinct. `exhausted` means no enabled event
  **in the declared alphabet**, not global deadlock or unreachability. The prefix
  of an allocation frontier includes the real enabled edge entering an over-budget
  state; that state is excluded from `reach`.

`Controls` computes the exact enabled list and depth-one result at the real
outbound initializer for all seven relays actions. It also computes both cutoff
reports, the disabled finish edge, and tick rejection/label decoding.

The six separate witness modules prove `initialized-witness-found`, retaining the
exact initialized endpoint, using the committed native run and the enumeration
completeness theorem. They do **not** normalize or materialize the whole search:

| Module | Ordinary witness | Depth | Alphabet list length, including duplicates |
| --- | --- | ---: | ---: |
| `HandshakeFailure` | G2 handshake failure / physical cleanup | 40 | 47 |
| `Inbound` | G2 clean inbound | 109 | 116 |
| `TimeoutCooling` | G2 production timeout cooling | 145 | 152 |
| `Outbound` | G2 clean outbound | 156 | 163 |
| `TwoPeer` | G3 two executing peers | 294 | 301 |
| `Overlap` | G3 overlapping same-key incarnations | 303 | 310 |

Each alphabet is the corresponding native schedule mapped to outer `innerAct`,
plus **all seven** outer relays actions. Schedule order is forgotten: `reach`
explores every enabled ordering/repetition over that alphabet. Each explicit
allocation cutoff is the closed executable term
`allocation-bound = W.Find.budgetFor W.start W.actions`: the maximum `allocated`
value along that schedule, including both endpoints. These six natural numbers
are deliberately **not normalized to numeral constants**. `run-with-budget`
proves the cutoff sufficient without replay normalization or a new assumption;
`within-length` substitutes the committed numeric step-count proof. This meets
the proved-membership alternative, not a claim of six completed exhaustive
searches. The small relays computation uses numeric allocation/depth bounds 1/1.

Run from the Agda library root, one process at a time, after confirming no Agda
process and at least 14 GB available:

```sh
agda ConnectionManagement/Exploration/Controls.agda +RTS -M20G -A128m -RTS
agda ConnectionManagement/Exploration/HandshakeFailure.agda +RTS -M20G -A128m -RTS
agda ConnectionManagement/Exploration/Inbound.agda +RTS -M20G -A128m -RTS
agda ConnectionManagement/Exploration/TimeoutCooling.agda +RTS -M20G -A128m -RTS
agda ConnectionManagement/Exploration/Outbound.agda +RTS -M20G -A128m -RTS
agda ConnectionManagement/Exploration/TwoPeer.agda +RTS -M20G -A128m -RTS
agda ConnectionManagement/Exploration/Overlap.agda +RTS -M20G -A128m -RTS
```

[Supervision increment 97](../Supervision.md#ninety-seventh-increment-g5-bounded-enumeration-and-witness-membership)
records actual checks and the commit list. [GateAudit](../GateAudit.md#ordered-gap-closing-plan)
retains export/reimport, targeted race searches, minimization and reduced-candidate
source replay as the remaining step 9/10 obligations. No exporter, FDR run,
minimizer or new source replay is supplied here.

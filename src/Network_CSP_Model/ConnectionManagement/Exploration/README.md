# Bounded supervised exploration

Stage 1 supplies the enumerator below. Stage 2 adds the dictionary-relative
text importer/exporter and targeted race certificates described at the end. `Bounded` enumerates all successful dispatcher edges over an
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
records completed step 9 at the declared scopes; minimization and reduced-candidate
source replay remain step 10 obligations. That stage supplied no FDR run, minimizer or new source replay; stage 3 below adds checked shrinking and selected source-operation tests.
Stage-2 acceptance evidence is recorded below.


## Checked text format (stage 2)

`Text` is parameterized by the actual dispatcher and a finite typed action
**dictionary**. Each event line is a zero-based dictionary offset, followed by
`.` and LF: `+` skips one entry and `:` skips ten. For example `.`, `+.`, `:.`
name entries 0, 1 and 10. The six retained dictionaries are exactly
`Exploration.<Name>.W.candidates` (equal to the decoded bridge carrier by
`encoded-alphabet`), including the seven relays actions.
Files must be interpreted with their named dictionary at the same source revision;
they are not self-describing logs or a general Haskell/action-constructor syntax.
Offsets preserve the full G4 `Raw.label` payload, including nested identities,
results and environment inputs. They introduce no API projection or hiding.
Duplicate dictionary entries are aliases for the same label.

`printLabel` accepts evidence that a label's action belongs to the dictionary;
`print` accepts coverage of a whole trace. `parse-print-label` recovers the action
and unread suffix, and `bridge-label-round-trip` states the scalar result in
G4's actual event carrier. `round-trip` recovers the complete action list.
`check` parses and dispatches each action from the supplied initializer;
`check-sound` proves every accepted trace is a real `Raw.Executes` with the exact
returned endpoint. `Raw.trace-intro` consequently yields its actual CSP trace.
`check-complete` proves printed covered real runs are accepted. `Imported`
retains a parser equality and the exact execution; `certified-acceptance` proves
that such a checked certificate is sufficient for executable checker acceptance. `ResultTrace`'s
existing deterministic-record theorem explains why fixed initialization and full
actions recover result snapshots; text files do not serialize runtime snapshots.

The parser takes an explicit maximum-event fuel. The exported files use their
witness event count; byte length is also a conservative usable input bound.
Empty input is the empty run. Empty/malformed/truncated lines, offsets outside
the dictionary and fuel exhaustion reject. A syntactically valid disabled action
also rejects. There is no ignored suffix or recovery that skips unknown input.
`TextControls` supplies malformed, truncated, out-of-range, alias, no-fuel,
accepted-run, disabled-label and disabled-suffix controls.

| Retained artifact | Events | Bytes | Agda certificate |
| --- | ---: | ---: | --- |
| [HandshakeFailure.trace](traces/HandshakeFailure.trace) | 40 | 320 | `ExportHandshakeFailure` |
| [Inbound.trace](traces/Inbound.trace) | 109 | 1244 | `ExportInbound` |
| [TimeoutCooling.trace](traces/TimeoutCooling.trace) | 145 | 1910 | `ExportTimeoutCooling` |
| [Outbound.trace](traces/Outbound.trace) | 156 | 2142 | `ExportOutbound` |
| [TwoPeer.trace](traces/TwoPeer.trace) | 294 | 6075 | `ExportTwoPeer` |
| [Overlap.trace](traces/Overlap.trace) | 303 | 6399 | `ExportOverlap` |

Run `python3 ConnectionManagement/Exploration/trace_files.py` to verify the exact
retained bytes against each Agda certificate's literal. Then typecheck the six
`Export<Name>.agda` modules. The script is a byte-transport check; Agda proves
`file-is-print`, `imported-labels` and `imported-run` for those same literals,
with the original initialized endpoints. `imported-run` is an `Imported`
certificate; `certified-acceptance` supplies executable checker acceptance from
its fields. The proof follows the native witness and generic round-trip theorems; it does not normalize six giant
replay terms or search trees. The script does not replace an Agda check.

## Targeted race searches (stage 2)

These use the unchanged stage-1 `Bounded` engine and explicit event lists, with
all enabled permutations and repetitions. Positive results are **proved
membership**, not materialized exhaustive searches. Invariant-based negatives quantify over
every member of the corresponding bounded search using soundness and actual
design invariants. The combined late-registry negative additionally computes
the complete filtered search result. Negatives do not only reject the original schedule. The finite
alphabets retain the concrete IDs and inputs; the diagnostic capacity measures
below are not the stage-1 full supervised identity footprint.

- `RaceLate`: the ten-event increment-73 shutdown/admission window, starting at
  the reached `ServerAdmission.atAfterIG igJoined` state, through CM closure,
  Server return, then the five late-admission events. Depth/capacity bounds
  **10/8**. Capacity is the maximum of retained workers/sockets/handlers and
  entry/promise supplies. The source search is at the Server layer. The same
  labels embed into the actual shared `ServerOwnedWorkers.step′` variant with
  both unjoined handles retained. No join action is in this window alphabet;
  its invariant excludes every returned Server endpoint. The combined
  handler-registry/OwnedCallers search also computes an empty returned-endpoint
  filter at the same bounds. This is a local
  boundary comparison, not a new composed late-admission run or progress claim.
- `RaceSelfPurge`: the eight-event increment-78 pre-close-to-finished window
  `s77` to `s85`, reached after the initialized witness's first 77 edges.
  Depth/physical-handler-capacity bounds **16/8**. The source-compatible phase-B
  dispatcher admits closed CM/finished relays with a self-purged physical
  handler lacking its result. The registry search starts at the corresponding
  reached `SelfPurge.v77`; its alphabet includes all original window labels
  and the existing repaired progress schedule, including sweep/counter/result
  operations. The gate/coverage invariant excludes any closed-CM physical
  handler with unavailable result, for every enumerated ordering. Depth 16
  also accommodates the repair's fifteen-event continuation. Existing
  initialized registry progress and physical-result controls are retained.
- `RaceForeign`: the full initialized increment-75 foreign-frame run with
  **1000 events**, with allocation pruning disabled. The alphabet is exactly its
  inner schedule plus the six relays-close labels. The owned-callers search
  uses the same labels, initializer and bounds; `no-frames` excludes every
  acquisition or release residue at every enumerated finished-relays endpoint.
  Concrete worker 900 and the request's other IDs remain explicit payloads in
  that alphabet. The zero metric/budget retains all states: finite depth and
  the exact finite event list bound the search without a separate ID cutoff.

These are model safety results at their declared layers/windows. They do not
strengthen the historical source replay classifications: late include remains
a combined candidate, and the self-purge replay remains a direct-CM observation
with synthetic inputs and a gated cleanup tracer. No native replay is rerun.

Validation status and exact commands are recorded in
[Supervision increment 98](../Supervision.md#ninety-eighth-increment-g5-checked-text-and-targeted-race-searches).
G5 remains partly met; minimization and reduced-candidate source replay are
separate plan-step-10 obligations at that checkpoint; stage 3 below records their completion.

## Trace shrinking (stage 3)

[Minimise](Minimise.agda) deletes dictionary offsets without changing identities
or supplying endpoint states. `valid` runs the existing stage-2 `Text.check`
from the fixed initializer and then tests the fixed endpoint violation.
`valid-sound` produces `Accepted`: successful checker equality, a real
`Raw.Executes` and that same violation. `pick-preserves`, `preserves` and
`reduction-sound` prove the single-event reducer retains acceptance;
`coarse-preserves` and `coarse-sound` do the same for bounded chunk deletion.
These statements quantify over the dispatcher, dictionary, initializer and
predicate. They introduce no local axiom or extra semantic assumption.

[MinimiseControls](MinimiseControls.agda) computes a three-to-one deletion on a
small dispatcher, checks both preservation lemmas and rejects a missing
violation, a disabled repeated action and an out-of-dictionary offset.
[MinimiseCandidates](MinimiseCandidates.agda) fixes the three actual dispatchers,
full initialized schedules and endpoint predicates. The candidates use the
committed initialized traces underlying increment 98, rather than treating its
reached local windows as initial states. Their dictionaries are exactly each
case's `actions`, including repeated actions as separate offset aliases.

Concrete reduction is driven by an external Python script in the task scratch
area. Starting from offsets `0 .. length(actions)-1`, it tries contiguous chunks
of width `floor(length/2)`, in order. An accepted deletion is retained and the
same position is tried again; rejected proposals advance by that width. Width
is halved through one, followed by repeated single-event scans until one full
scan accepts no deletion. Every oracle answer evaluates `Case.M.valid` in Agda,
including the original and final trace. The script never generates Agda backend
code. The completed Python search found no accepted single deletion in its final
scan; this is an observed search result, not an Agda minimality theorem. No
global minimum is claimed.

The concrete `Shrunk*` certificates independently typecheck the literal original
and retained offset lists: `original-valid` / `shrunk-valid` are `refl`, and
`original-accepted` / `shrunk-accepted` apply `valid-sound`. Thus the Python search
is outside the trusted proof boundary. Export equalities tie each literal to the
canonical stage-2 bytes. Dictionary offsets and payloads are retained verbatim;
the initial state is identical in each pair. `strictly-shorter` checks an actual
length decrease. A finite accepted violating trace establishes no universal
liveness or failure of every possible cleanup schedule.

[Increment 99](../Supervision.md#ninety-ninth-increment-g5-trace-shrinking-and-conformance-tests)
records the concrete lengths, byte checks, typechecking and source classifications.
The [source tests](../SourceReplay/README.md#reduced-cleanup-candidates-increment-99)
replay selected operations with controls. The foreign actor is deliberately
outside library ownership, and the combined late Server race remains unconfirmed.

| Dictionary / certificate | Original → shrunk events | Original → shrunk bytes | Fixed endpoint predicate |
| --- | ---: | ---: | --- |
| `LateCase` / [ShrunkLate](ShrunkLate.agda) | 50 → 46 | 425 → 400 | Server returned, CM closed with empty snapshot/collected lists, physical `child₁` present |
| `PurgeCase` / [ShrunkPurge](ShrunkPurge.agda) | 85 → 82 | 860 → 828 | CM closed, relays finished, physical `child₀` present with unavailable result |
| `ForeignCase` / [ShrunkForeign](ShrunkForeign.agda) | 192 → 183 | 2988 → 2876 | Relays finished with worker 900's acquisition frame retained |

Retained pairs are `traces/{Late,Purge,Foreign}.{original,shrunk}.trace`.
Run `python3 ConnectionManagement/Exploration/trace_files.py` to verify all twelve
artifacts against their Agda literals. Then check `MinimiseControls.agda` and
`Shrunk{Late,Purge,Foreign}.agda` serially with
`+RTS -M20G -A128m -RTS`, under the resource guard above. The concrete certificates
include both original and shrunk initialized acceptance and strict length decrease.

# LeiosNotifyPipeLookahead source model

The native producer is
[`Cardano_network.LeiosNotifyPipeLookahead`](../LeiosNotifyPipeLookahead.agda).
Its operational models, executable transitions, PTree constructors and protocol
properties live in this directory. Replay bridges and validation witnesses live
in [`Replay/LeiosNotifyPipeLookahead`](../Replay/LeiosNotifyPipeLookahead/README.md).

## Dependency structure

```text
Cardano_network/
  LeiosNotifyPipeLookahead.agda          native entry point
  LeiosNotifyPipeLookahead/              protocol models, trees and properties
  Replay/LeiosNotifyPipeLookahead/       replay bridges and validation witnesses
```

The native entry point and replay bridges import the protocol modules.
Protocol modules and their PTree constructors have no dependency on `Replay`.
The source-operation compiler and transition certificates belong to the model
layer because they define and justify its executable semantics; their use by
replay does not make them replay-specific definitions.

The directory refactor preserved the then-existing 27 Agda source files modulo
namespace changes. The [T4.3.2 dependency scan](../Replay/LeiosNotifyPipeLookahead/tools/results-t432-20261104.json)
recorded 75 local dependencies and no Replay dependency; the earlier T4.3.1
scan recorded 70. These are dated module-boundary checks; protocol properties
retain the scopes documented below.

The later [DriverSearchOrder](DriverSearchOrder.agda) and its
[tests](DriverSearchOrderTests.agda) provide complete input-dependent enumeration
of the existing hidden driver moves. They introduce no protocol policy or Replay
dependency: stable sorting retains every source alternative. The replay layer
uses those all-state soundness/completeness facts in the generic ordered search;
the [comparison guide](../Replay/LeiosNotifyPipeLookahead/tools/search-order/README.md)
records practical improvements for the retained full shutdown histories and
the limits of those measurements.

The [lookahead replay design](../../../docs/specs/leiosnotify-lookahead-replay-design.md)
records the source model and remaining checker work. The model follows the
server control flow in consensus
[`2416493`](https://github.com/IntersectMBO/ouroboros-consensus/blob/2416493bfdbe93b761b3a4bb1ccf2b4a913e5e4b/ouroboros-consensus/src/ouroboros-consensus/LeiosDemoOnlyTestNotify.hs#L636-L723)
and the sender/reader scheduling in its pinned
[typed-protocols driver `9b46272`](https://github.com/IntersectMBO/typed-protocols/blob/9b4627221ae5d649f2303c6926a8dba3f9934658/typed-protocols/src/Network/TypedProtocol/Driver.hs#L427-L555).
It is an explicit Agda transcription under callback contracts, not a formal
refinement theorem for compiled Haskell.

The T2 operational extension adds the pipelined client, a paired driver-record
product with hidden channel commits, the node server's credit/queue transactions,
and the node client's fixed-depth/cancellation policy. T3.1 now adds productive
source-operation client/product PTrees with two-sided finite-trace bridges.
The server now also has a general two-sided bridge over existing native `LNPEv`
events and a canonical realization of every exact source action. The generic
client now also has a native `LNPEv` tree and two-sided finite trace bridge with
explicit callback erasure. A native endpoint-tagged paired driver product and
projection to both local native endpoints are now checked. `NodeDriverModel` now
binds the production client/server policies in that product; its projections,
resource/failure invariants and one-way native realization are checked. Eight
controlled pinned Haskell peer/driver schedules now pass, with all 80 captured
histories matched to checked Agda witnesses. T4.1.1 additionally proves universal
server accounting and exact FIFO conservation, including pending hooks, with
node-policy and native paired endpoints. Wider differential coverage, full
node-callback validation and certified raw-log search remain outstanding. Immutable
source URLs and inspected byte checksums are in [`sources.json`](sources.json).

The next stages are numbered in the
[T1 to T8 task plan](../../../docs/specs/leiosnotify-pipe-lookahead-plan.md).

## Source correspondence

| Source operation | Model operation |
| --- | --- |
| First ordinary Await | Reader `first`; no reply job exists yet |
| `incr` succeeds | `admitted`, from `admit` to `register` |
| `incr` returns ExcessiveRequests | `excessive`, then exception/cancellation phase `raising` and `abort` |
| AwaitLookahead registers a sender | `registered`: increment waiting before the next receive |
| Sender thread claims a registered job | `claim` |
| `next` returns a normal or generic cancellation reply | Explicit `nextReply` action, storing that exact payload |
| True `quitVar` wins the responder transaction | Hidden `cancel`, selecting Canceled |
| Reader receives MsgQuit | `receiveQuit`: reader enters `signalQuit`, flag unchanged |
| Reader writes `quitVar` | Separate `setQuit` step |
| Sender yields the selected reply | `send`, preserving the selected payload |
| Sender finishes and increments doneVar | Separate `retire` step |
| FlushSender consumes a completion | `flush` |
| Last completion has been flushed | `drained`, enabling responder Done |

The reader and sender have independent state. A selected or sending reply does
not remove the reader's receive offers. If the reader observes Quit between
reply selection and sending, the selected normal reply is retained. Multiple
normal sends can follow the Quit record when the reader has not yet published
the flag. Once the flag is true, new responder selections choose Canceled.

`genericNext` allows Canceled as a result of `next`, as permitted by the peer
function's type. `nodeNext` restricts that callback to the four normal reply
kinds, matching the pinned node queue's message kinds. These contracts do not
model application stores, actual message availability, offer validation or the
production `credits` counter. `NodeModel` separately binds the server to
`CreditModel`'s actual credit/queue transactions under eligible-input contracts.
For the generic server the environment supplies callback results. An
unavailable callback is blocked, not a hidden polling loop.

Admission failure is preserved. The native tree returns `excessiveRequests`
after exception cancellation, distinct from its `success` return following
wire Done. During the raising/cancellation interval an already active sender
can still progress. Other callback exceptions and codec/channel faults are
outside this first model.

## Observation and arithmetic scope

The model's operational actions include application reply readiness. These
are not raw log rows; `wireActions` erases only those readiness actions. The
native tree maps readiness to existing application API channels and preserves
native payloads, endpoint identity and message agency.

Native wire labels denote local driver observations. They are not a proof of
channel-commit timing. The pinned network driver writes to the channel before
recording Send; its pipelined client registers receivers before the sending
call. The current producer must therefore not be connected to the old
TraceSend-as-enqueue paired checker and described as a complete raw-log model.
`DriverModel` now provides those explicit channel-commit and pending-record
relations, but native correspondence and certified search remain required for
that claim. Existing CLI modes and bridge targets
are unchanged; no new log-verifier CLI mode is installed by this stage.

Counters in Agda are mathematical naturals. The pinned driver uses Natural for
its waiting/completion counters, but
[`Nat` is backed by `Int`](https://github.com/IntersectMBO/typed-protocols/blob/9b4627221ae5d649f2303c6926a8dba3f9934658/typed-protocols/src/Network/TypedProtocol/Core.hs#L545-L570)
for the peer's deferred-sender count. Source correspondence of count arithmetic
therefore requires a no-overflow range. The unbounded Agda family is not a
claim that the machine representation is unbounded. Strictness, allocation,
integer boundaries and elapsed time require runtime evidence beyond these
step-count results.

## Implemented results

- `Model.agda` specifies independent `Step` and `Tau` relations, payload-retaining
  states, finite operational runs, callback contracts and proof-carrying lookup.
  `next-complete` proves lookup implements every independent visible rule.
- `Enumeration.agda` proves soundness and completeness of the hidden successor
  list, including admission failure and concurrent reader/sender choices.
- `Rank.agda` proves every hidden step strictly decreases a natural-number
  measure and all model states are hidden-step accessible. This does not prove
  that a blocked callback or network operation eventually completes.
- `Properties.agda` proves shutdown-state persistence, no new requests or
  repeated Quit after reader shutdown, exact selected-payload preservation,
  the node callback's normal-only selection, and Done's drained-state guard.
- `Tests.agda` supplies inhabited full operational schedules for ordinary
  replies across Quit, multiple normal replies after the Quit record,
  cancellation drain and admission failure, plus negative controls.
- `NativeTests.agda` exhibits actual PTree receive/Quit, flag publication and
  post-Quit normal-send steps, and distinguishes failure from successful return.
- `NativeReachability.agda` constructs arbitrarily long finite executions of
  the actual native PTree reaching completed-bookkeeping states with zero owed.
- `ClientModel.agda` separates sender control, receiver jobs, completed results,
  signed `arrived`, the stop flag and the retained return value. `ClientTests`
  covers the Zero branch, full-pipe termination, publication/collection races,
  handler completion after Quit and draining without decrementing `arrived`.
- `DriverModel.agda` couples the generic client/server with exact directional
  FIFOs and four pending trace records. `DriverTests.delayed-send-records`
  witnesses a fresh execution whose record order is server Recv Request,
  client Recv reply, client Send Request, server Send reply. It preserves every
  record and each endpoint's order; it does not sort or repair a capture.
- `CreditModel.agda` models admission, enqueue/drop and FIFO dequeue separately.
  `NodeModel.agda` binds server admission and selection to these transactions.
  `NodeProperties` proves the free-credit invariant and constructs the conditional
  pending-work counterexample below. It leaves eligibility/store policy external.
- `NodeClientModel.agda` fixes depth 1000 and represents the node handler's
  `LeiosNotifyUnexpectedMsgCancel` exception when it handles Canceled. A receiver
  that observes draining skips this handler. `NodeTests` covers both paths,
  the server credit limit and exact/empty queue negative controls.
- `ClientExecution.agda` certifies executable visible lookup and a sound/complete
  finite hidden menu against every independent client `Step`/`Tau` constructor.
- `DriverExecution.agda` certifies visible record lookup and complete executable
  hidden selectors for endpoint scheduling, callbacks, channel writes and decode.
  Selectors contain operation data, never supplied transition evidence.
- `OperationalTree.agda` builds productive PTrees from these certified operations.
  `visible-intro`/`visible-elim` and `hidden-intro`/`hidden-elim` prove both step
  directions; `run-intro`/`run-elim` prove both finite trace directions, retaining
  an explicit continuation equality without assuming coinductive tree injectivity.
- `ClientTree`/`ClientBridge` and `DriverTree`/`DriverBridge` instantiate those
  proofs for the existing independent run relations. The client returns the exact
  `checkDone` result after Done. The paired tree models finite prefixes and has
  no global return rule, matching `DriverModel.Run`; endpoint results stay in state.
- `ClientNativeTests` realizes the reply-before-Send and handler-after-Quit source
  schedules as actual PTree runs. `DriverNativeTests` realizes the delayed-Send
  paired schedule and rejects an uncommitted record, changed pending payload,
  second commit of a pending call and decode from empty transport.
- `ServerEvents.agda` supplies canonical `LNPEv` representatives of every exact
  source server action. `ServerEventsBridge.decode-encode` proves roundtrip
  decoding for every Params/contract/link/direction, and `encode-injective`
  proves that distinct source actions or payloads cannot collapse.
- `ServerBridge` proves both visible/hidden step directions for the existing
  native server, both finite trace directions, and success/failure return
  classification. Its `realize` theorem constructs native events for every source
  run; its `sound` theorem reconstructs an operational run and exact continuation
  from every finite native run. `Matches` preserves each native event alongside
  its decoded action, including readiness APIs.
- `ServerBridgeTests` gives exact-field native executions for all four notification
  kinds, a selected normal reply across Quit, cancellation drain, and abstract
  admission failure. Negative controls cover changed slot/size, reordered votes,
  wrong agency/direction and an invented Done API. The bridge also transports
  selected-payload, no-new-request and drained-Done guards to canonical native
  events, with impossibility proofs for early Done and requests after Quit.
- `Notifications.agda` shares native payload equality between client and server;
  the entry point retains its existing public equality names and definitions.
- `ClientEvents.agda` maps wire records and successful normal handler deliveries
  to existing `LNPEv` channels. Its `Hidden` classifier singles out `checkDone`
  decisions and successful generic Canceled handling. `ClientEventsBridge.view`
  proves this observation partition; `decode-observe` and `observe-injective`
  prove exact retained-action/payload realization.
- `ClientNetwork.agda` constructs the native client with data-only internal
  callback choices. The main entry point exports `NetworkClient` and
  `client Return link direction`. `ClientNetworkBridge` proves both visible and
  hidden step directions and both finite trace directions against the original
  client rules, retaining erased decisions in an explicit `Matches` witness.
- `ClientNetworkTests` gives native witnesses for replies before Send records,
  handler completion after Quit and Canceled draining with return value 73.
  It preserves the residual `arrived = 1` at shutdown, tests negative-depth Zero
  behavior and termination at capacity, and rejects hiding wire/normal delivery
  events, changed handler payloads and an invented unit checkDone API.
- `DriverNetwork.agda` exposes the original paired driver state over endpoint-tagged
  native channels, retaining hidden commits/decode and all four pending records.
  Canonical full-packet decoding carries equality evidence for the entire native
  envelope. The main module exports this product as `NetworkDriver`.
- `DriverEventsBridge` proves native record roundtrip realization and injectivity;
  `DriverNetworkBridge` proves both visible/hidden step directions and both finite
  record-trace directions against the original independent paired rules.
- `DriverProjections` extracts exact local client/server source runs from every
  paired execution. `DriverEndpointBridge` lifts those runs to the existing native
  client/server trees and proves that filtering their local wire rows yields
  precisely each endpoint's ordered records from the product trace.
- `DriverNetworkTests` supplies fresh native paired and native-endpoint witnesses
  for both receives preceding delayed Sends, Canceled shutdown and a preselected
  normal reply sent after Quit/flag publication. The closed case retains client
  result 73 and arrived one with empty FIFOs/pending records. Negative controls
  cover absent/duplicate records, changed pending payloads, wrong coordinates,
  hidden-record callbacks and skipping a FIFO head.

The test and bridge modules listed above are in `Replay/LeiosNotifyPipeLookahead/`;
the models, executable transitions, trees and protocol properties are here.

These are properties of the new source model. The complete wire quotient,
exact-field replay bridge and paired raw-driver checker remain later stages.
The source-operation client exposes `ClientModel.Action`, including callback
decisions; the paired tree exposes `DriverModel.Event`, including endpoint tags.
These channels are distinct from the existing network `LNPEv` alphabet. The
main module exports them as `PipelinedClient` and `PairedDriver` module instances
over native notification payloads. `NetworkClient` separately supplies the local
client over existing native network/API channels; `NetworkDriver` supplies the
paired driver product below. Network node assembly remains separate from these entry points.
`DriverModel` uses the generic successful
client callback contract and generic admission outcomes: the two node-policy
models are component targets, not yet one certified paired-node product.

The paired hidden selector contains arbitrary callback depths, return values
and notification values. A complete selector interpretation therefore does
not establish a finite successor list for raw replay. T7 still needs its
input-relative finite basis and search proof. The finite-run bridges exclude
the separate CSP termination tick and establish no infinite liveness property.

## Native server bridge scope

`ServerBridge.For contract link direction` connects the unchanged operational
server to the existing `LeiosNotifyPipeLookahead.Machine.tree` over `LNPEv`:

```text
source Run --realize--> native network/API execution
native execution --sound--> matching actions + source Run + exact continuation
```

`complete` accepts supplied native events that decode to the source actions;
`realize` uses `ServerEvents` to discharge that representability condition for
every source run. The theorem retains exact selected notification values and
allows arbitrary internal interleavings. It requires no equality/injectivity
assumption on coinductive trees. Finite-trace transport excludes the CSP
termination tick; `return-elim` separately distinguishes success and excessive
request failure.

Readiness APIs are retained in this bridge. The standalone server wire checker
below now erases them through a proved observation. `nodeNext` restricts callback reply kinds, while admission
outcomes remain abstract in this server model. The actual credit/queue binding
in `NodeModel` is a separate target; the initial admission-failure witness does
not claim that the pinned node rejects its first request. These results do not
establish Haskell refinement, store validity, codec behavior or infinite liveness.

### Exact server wire checker

[Wire/Server.agda](Wire/Server.agda) implements an exact unbounded standalone
server quotient with complete lookup and certified decision for both contracts.
It tracks requests still owed and the Open/QuitSeen/CancelOnly/Closed phases.
Protocol code imports no Replay modules. The
[replay proof and native bridge](../Replay/LeiosNotifyPipeLookahead/README.md#exact-server-wire-replay)
prove both detailed source/wire inclusions and decide the native wire prefix
language. Thus server checking need not enumerate internal interleavings.
This is the abstract-callback baseline; credits, node queue policy, client/paired
logs, raw fields and optional wire-cap policies need their own support.

### Generic client source wire checker

[Wire/Client.agda](Wire/Client.agda) adds a distinct unbounded generic client
quotient. Its `Lead` state permits one extra received reply before the delayed
RequestNext Send record, without permitting another reply or Quit first.
The [source-language proofs](../Replay/LeiosNotifyPipeLookahead/README.md#generic-client-source-replay)
preserve arbitrary schedules and exact payloads; completeness explicitly takes
a return-value inhabitant. Native wire transport is now checked through
`Replay/LeiosNotifyPipeLookahead/WireClientNative`; fixed node policy remains
separate, and the paired checker below supplies its own composition result.

## Native client observation and callback scope

`ClientNetwork` retains the original `ClientModel` control state. RequestNext,
Quit, reply and Done records use the existing send/receive channels; successful
normal handlers use `lnpRecvBlockAnnouncement`, `lnpRecvBlockOffer`,
`lnpRecvBlockTxsOffer` or `lnpRecvVotes`, preserving exact values.

The Haskell `checkDone` result carries a dynamic signed depth or an exact return
value. The existing unit request/quit APIs cannot represent that result. Native
internal choices therefore retain `continue k` and `terminate value`, with the
source lookup enforcing the original guards. A successful generic Canceled
handler also becomes an internal callback step because this API has no receive
Canceled delivery tag. **The received Canceled wire record remains visible.**
Normal deliveries and all wire actions are excluded from the hidden classifier.

`ClientNetworkBridge.complete` and `sound` relate native finite executions to
original source runs using `Matches`: visible native events retain their decoded
actions, while the declared callback actions are explicitly recorded as erased.
`realize` supplies a projected native trace for every source run. `return-elim`
preserves the original exact termination value. These bridges exclude the
separate termination tick from finite trace transport and classify it separately.

This client uses the generic successful-callback contract. `NodeDriverModel`
restricts its client control to depth 1000, the forecast/termination decision and
the unexpected-Canceled failure policy; see the combined policy below. The dedicated internal scheduler family
can carry arbitrary callback values. The paired product below now supplies a
joint wire-observation target and endpoint projection certificates, including
channel commits before delayed Send records. These local driver-observation trees do
not by themselves justify the old Send-record-as-enqueue medium. Infinite
callback domains are handled by the now-checked finite target/basis proofs at
the explicit unit-return paired-checker profile. The standalone native wire
bridge retains generic Return with an explicit inhabitant for decision.

## Native paired driver product

`NetworkDriver.At contract clientLink serverLink clientDir serverDir` exposes
the existing `DriverModel.State` as a PTree over `atClient`/`atServer` wrappers of
the existing `LNPEv` channels. The wire-only profile retains every driver record
and hides application callbacks. Committing a packet appends it to the directional
FIFO and creates a pending Send; recording that Send advances the endpoint without
enqueuing again. Decode consumes the exact head before its Receive record.

`DriverNetworkBridge.realize` constructs a native paired trace for every source
run; `sound` reconstructs the source rows and exact product continuation from every
native trace. `DriverEndpointBridge.native-endpoints` additionally supplies actual
native client and server executions with matching start/end states and the same
local wire-record order. Their local API events remain present where appropriate,
then are removed by the declared wire projection.

This is the explicit driver product with endpoint projection theorems. Equivalence
to an ordinary CSP `Par` or the legacy `AsyncPair.compose` medium has not been
proved. The legacy medium's Send-as-enqueue boundary does not describe these raw
driver schedules. The packet profile uses shared canonical time/length metadata
and exact selected message fields; arbitrary raw envelopes and codec bytes still
need their capture/normalization correspondence. The product preserves finite
prefixes and keeps endpoint return values in state without a global return tick.
Generic successful client callbacks and abstract admission remain this generic
tree's contracts. The node model below supplies a checked restriction of its runs.

### Replay prefix bounds and finite callbacks

[DriverPrefixBounds](DriverPrefixBounds.agda) proves exact physical-operation
versus visible-hook tallies on arbitrary driver runs. From a fresh state, each
directional commit count is at most its Send-row count plus one pending Send.
[DriverPrefixBoundsQueues](DriverPrefixBoundsQueues.agda) adds exact commit/
decode/FIFO accounting and bounds pending Receive plus queued packets by those
Send rows plus one. Reachable prefixes require the additive one; no queue cap
is guessed and delayed Send hooks remain permitted.

[ClientCallbackBasis](ClientCallbackBasis.agda) gives a finite exact successor
menu for erased successful client callbacks at unit return. Arbitrary signed
depths reduce to their tested comparison cases without changing the target
state; exact handler payloads and concurrent alternatives remain. This covers
one hidden rule family per state, not all payload choices or a finite overall
state graph. The
[design](../../../docs/specs/leiosnotify-lookahead-replay-design.md#checked-prefix-bounds-and-callback-targets)
states the theorems, regressions and remaining packet/state/search obligations.

### Input-relative paired replay model

[DriverBasis](DriverBasis.agda) restricts only new normal callback selections
to a declared finite list. [DriverBasisExecution](DriverBasisExecution.agda)
enumerates all eight hidden rule families completely for that relation;
[DriverBasisExecutionReplay](DriverBasisExecutionReplay.agda) exports its Replay
interface and inherited hidden accessibility. [DriverPayloadMap](DriverPayloadMap.agda)
preserves every generic source rule under payload renaming. Exact endpoint
alphabets and order-preserving merges live in [DriverRows](DriverRows.agda).
All protocol modules remain independent of Cardano-network Replay modules.

The [paired checker](../Replay/LeiosNotifyPipeLookahead/README.md#typed-paired-driver-replay)
uses whole-input adequacy to turn those finite menus into a decision about the
unrestricted original driver model, then transports it to native paired trees.
The checker has unit return and successful generic client callbacks; it does
not invert the fixed node-policy restriction or validate raw capture fields.

## Combined production node policy

[`NodeDriverModel`](NodeDriverModel.agda) combines the driver state with the
production credit/notification queue, local client failure state, forecast
readiness and governor termination inputs. It uses unit as the client return
type, matching `Left ()` in the pinned node wiring.

The model permits the following operations:

- Continue at depth 1000 only when the forecast is ready and termination is not
  requested. Termination bypasses forecast readiness and selects the Quit path.
- Admit requests through the actual credit callback and select normal replies
  from the exact queued head. Generic admission/next callbacks cannot bypass
  this policy through the transport scheduler.
- Supply eligible notifications and successful normal-handler outcomes as
  explicit environment inputs. Ledger, relay and validation correctness are
  outside this control model.
- Record an unexpected-Canceled handler exit locally. The failed client stops;
  remote server work may continue at the successful-channel prefix abstraction.
  This is not a model of precise exception propagation or channel cleanup.

[`NodeDriverProperties`](NodeDriverProperties.agda) proves that every combined
run projects to both existing node-policy components, embeds into a generic
driver run with exactly its wire rows, preserves free credits at most 1000 from
the initial state, and keeps an exited client's exact control state frozen.
Client records require a live local driver.

[`NodeDriverBridge`](../Replay/LeiosNotifyPipeLookahead/NodeDriverBridge.agda)
turns such a witness into a native paired trace and both native endpoint runs:

```text
Node.Run (policy inputs + wire rows)
  -> generic Driver.Run (same wire rows)
  -> native paired trace + native endpoint traces
```

This is a **one-way inclusion**. An arbitrary generic native trace is not a
certificate of the production node policy. Policy inputs and the abnormal-exit
tag remain in `Node.Run`; the wire-only generic tree erases them and does not
classify the node's exception outcome. An exact policy PTree/inversion theorem
and certified search for a node-policy witness remain future work.

`NodeDriverTests` supplies fresh witnesses for forecast-blocked termination,
delayed Send records with real queue accounting, Canceled shutdown, and a normal
reply selected before Quit but sent after its flag becomes true. It also checks
successful normal handling and the local fault transition from a stated partial
state. Fresh honest-pair reachability of that unexpected-Canceled fault is not
claimed. Cancellation can leave an unused admission credit after Done; that
counter is distinct from drained protocol work.

## Credit admission does not alone bound pending work

The production counter is consumed at enqueue, before `next` removes a message
or a sender transmits it. The following finite cycle is therefore possible at
the component abstraction, for a nonzero admission limit:

```text
receive Request -> free = 1
register the deferred sender; delay its execution
eligible notification is enqueued -> free = 0, queued += 1
repeat
```

`NodeProperties.initial-free-bounded` proves free
credits remain at most the limit. `admission-bound-counterexample` proves that
for any proposed pending-work bound there is a finite run with more deferred
sender jobs and queue entries, all at free credits zero. `NodeTests.two-reserved`
instantiates two pending jobs at limit one. Without an intervening enqueue, the
second request instead follows the excessive-request path.

This is a counterexample to a bound justified **only** by the admission counter.
It assumes enough eligible application inputs and external requests, and permits
finite sender delay. The pinned honest depth-1000 client supplies another policy
that must be analyzed in the paired model. No runtime exploit, resource cost or
whole-node reachability beyond that policy is established here.

## Potential issue established in the model

Completed sender jobs accumulate during normal operation and are collected by
FlushSender only after Quit. Consider sequential exchanges, with each response
sent before another request is issued:

```text
request -> reply -> completed = 1, unanswered = 0
request -> reply -> completed = 2, unanswered = 0
request -> reply -> completed = 3, unanswered = 0
...
Quit -> flush every accumulated completion -> Done
```

`completion-bound-counterexample` proves that for every proposed bound and an
inhabited notification carrier there is a finite operational execution ending
with zero unanswered requests and more completed tokens than that bound. Its
witness issues one request at a time. `completed-native` independently gives
inhabited executions of the actual PTree. `shutdown-count` proves that the
constructed shutdown from a state with n completed tokens performs exactly n
flush transitions before Done.

This identifies a potential shutdown-cost problem: bookkeeping work can depend
on the connection's completed request history, not just its outstanding work.
It is not a proof of a memory leak, measured latency, or failure of finite
shutdown. The runtime Int representation also prevents inferring a unary
counter allocation cost merely from the type-indexed Nat interface.

A candidate improvement is to collect finished sender jobs periodically in
the busy loop using nonblocking FlushSender operations, maintaining the
source's type indices and Quit responsiveness. Before changing the Haskell
code, verify preservation of wire behavior, account for simultaneously pending
and completed jobs, establish a bound under explicit client/admission policies,
and compare shutdown work and allocation with a pinned runtime experiment.
The current model retains the original behavior for that comparison.

## Request/reply and FIFO conservation

`ServerConservation` proves `owed(start) + requests = replies + owed(end)` for
every finite server run under either callback contract. Normal and Canceled
replies each count once; Quit, Done and callback readiness do not count as
request/reply exchanges. Completion tokens stay separate from owed work.
Fresh sessions cannot emit extra replies; the exact drained closed state has
equal request and reply counts. Failure prefixes retain unanswered obligations.

`DriverConservation` proves exact packet-list equations for both directions:
recorded Sends plus a pending Send equal recorded Receives plus a pending
Receive and the remaining FIFO. Payload, order and multiplicity are preserved.
The theorem covers Receive-before-Send prefixes. Equality of just the recorded
histories follows when the direction's FIFO and both hooks are clear.
`NodeConservation` applies these properties to all fresh production-policy runs
and retains actual server source/wire accounting. The separate replay
`ConservationBridge` lifts them to all actual native paired finite traces via
the existing inverse bridge. Its generic native target keeps its existing scope.

The [conservation note](../../../docs/notes/leiosnotify-pipe-lookahead-conservation.md)
gives exact statements, reachable controls and remaining T4 tasks. These are
finite model safety properties; progress, machine arithmetic and client
marker/completion resource bounds remain separate obligations.

## Shutdown and Done work guarantees

T4.1.2 adds `ClientShutdown` for persistent shutdown from termination acceptance
onward, and `ServerShutdown` for persistent flag publication and Canceled-only
new selections afterward. A previously selected normal remains sendable.
`ClientAccounting` proves the exact inventory equation, correcting `inFlight`
for registration before Send; zero counter alone does not imply empty work.

`DoneOrigin` links every physical Done packet in the FIFO or hooks to the actual
drained responder. `DriverShutdown` proves no new client request records or
commits during shutdown. A fresh client Receive-Done certifies closed client
control, zero count, a stored return value, empty jobs/results, idle receiver and
a drained server (`doneReady` or closed). A delayed server Send-Done hook can
remain. Server Send-Done alone can precede client draining and packet delivery.
Fresh paired runs witness both distinctions. `NodeShutdown` and the separate
native `ShutdownBridge` retain the exact guarantees under their existing scopes.

The [shutdown note](../../../docs/notes/leiosnotify-pipe-lookahead-shutdown.md)
contains precise statements and counterexamples. All nine new modules pass safe
checking through the two shutdown roots with strict zero-finding audits.
Eventual progress, trace-hook scheduling and shutdown latency remain separate
obligations; finite scheduling and operation bounds are now checked below.

## Hidden scheduling and shutdown step budget

`SchedulingArithmetic` supplies shared safely checked polynomial identities;
`SchedulingCost` assigns potential to queues, source control and pending hooks.
`SchedulingRank` proves strict decrease for every hidden paired operation,
including callback choices, channel commits and decodes, and constructs
accessibility at every state. The original local server rank is preserved.
Infinite callback data domains do not require a finite-branching assumption for
this theorem.

`ShutdownWork` additionally proves that remaining wire operations decrease once
both role-specific shutdown paths hold. Every finite continuation then has at
most the starting potential's number of internal-plus-wire operations.
`NodeScheduling` supplies production hidden accessibility and a bound on
projected driver work; stuttering environment records are not counted as driver
operations. `SchedulingBridge` proves native hidden accessibility/divergence
exclusion and bounds actual native shutdown steps through existing inversion.

The computed work view separates owed replies, completion tokens and unretired
sends. Reachable controls distinguish these quantities and show that potential
is a conservative budget, not exact work or elapsed time. See the
[scheduling note](../../../docs/notes/leiosnotify-pipe-lookahead-scheduling.md).
Conditional completion and its remaining structural premise are described below.

## Conditional shutdown progress

`ShutdownProgress` separates a preserved structural local-progress invariant
from the decreasing potential. It constructs bounded source completion and
proves completion of finite maximal runs under that explicit invariant.
`RuntimeProgress` additionally represents waiting, successful operations,
failure and terminal observations. Its theorem proves eventual completion of
the given execution from finite responsiveness, no failure and no premature
halt, retaining the actual source path and operation bound.

`ServerProgress` supplies constructive local progress after an actual Quit
without needing a new application `next` result. `DoneProgress` discharges the
paired structural premise for all seven final Done packet/hook states.
The replay `ProgressBridge` realizes actual native completion paths; pure and
native examples construct inhabited runtime premises at fresh reachable handoffs.
Starvation, exceptions and premature EOF violate separate required conditions.

General fresh paired progress through the earlier reply/marker drain is now
proved by `PairedDrain` below. The theorem does not infer enabled progress from finite rank alone or
deduce runtime liveness from a finite accepted log. It preserves the existing
Haskell, production-policy, native-prefix and CSP-composition boundaries. See
the [progress note](../../../docs/notes/leiosnotify-pipe-lookahead-progress.md).

The next component results now prove general fresh paired server progress.
`ServerPhase` retains exact reader/flag shape; `ServerSendSlot` retains pending
Send payload/control consistency under every interleaving. `ServerDrain` obtains
both from fresh reachability and constructs bounded server closure, with runtime
and native endpoints under explicit responsiveness/failure assumptions. No
structural server-progress premise remains for the caller to discharge.

`ClientPhase` retains fresh return/flag/count guards and proves Await-Done and
closed client work empty. `ClientReplyAccounting` tracks exact outstanding wire
replies separately from Quit-marker work and received-but-unpublished results.
The T4.2.2.3.3 results below connect those facts to actual FIFO/pending-Receive
packets and final Done order. The earlier fresh twenty-two-operation complete
example remains distinct from the new universal theorem. See the
[server-drain note](../../../docs/notes/leiosnotify-pipe-lookahead-server-drain.md).

`CommandFlow` proves physical Quit seals the initiator direction; `ResponseFlow`
proves unique final Done and exact packet/hook delivery phases. `ReplyLedger`
connects outstanding client responses to actual server/transport obligations,
including pending-Send corrections. `ClientDrain` uses these facts to prove
actual local/packet progress throughout the client reply, handler, marker and
Done drain. `PairedDrain` supplies the full fresh local-progress contract and
derives bounded model completion, completion of finite maximal runs and
given-runtime liveness under the explicit external response/failure/terminal
premises. No unproved structural-progress parameter remains for fresh states.

The replay `PairedDrainBridge` retains actual native paths and native step
bounds. Fresh delayed-Quit and held-handler examples instantiate the general
theorem; missing-Done, dropped-reply and duplicate-Done targets are proved
unreachable. A full production-policy delayed-Quit schedule has actual native
and inhabited runtime witnesses. These results retain the previous successful-IO,
entry-to-shutdown, production-policy and Haskell/CSP-refinement boundaries. See
the [paired-drain note](../../../docs/notes/leiosnotify-pipe-lookahead-paired-drain.md).

## Completed bookkeeping and exact flush cost

`CompletionAccounting` proves universal completed/retirement/flush accounting
and total owed-plus-unretired-plus-completed work conservation. Every successful
close flushes initial work plus newly received requests. After Quit, every
successful schedule flushes exactly the initial work. Existing completion history
lower-bounds any later successful closing operation count, even before Quit.
The older constructed `flushCount` is preserved and proved equal to the new count.

`CompletionDriver` retains these results at the physical commit/decode/trace-hook
boundary. The replay `CompletionBridge` independently counts actual native
hidden flushes and proves source-count agreement, exact closure counts and
operation lower bounds. A fresh modeled native prefix containing server Send-Done
flushes every decoded historical RequestNext exactly once, without assuming tree
injectivity or inferring completion from EOF.

`SequentialCompletion` constructs an arbitrary-length family in the combined
production-policy model, with the actual depth 1000 and explicit eligible inputs
and normal handlers. Eight natural resource bounds of one hold at every state
of its normal prefix and shutdown. After n sequential rounds the empty/idle
client and zero-owed server coexist with n completed tokens. The selected full
shutdown uses n flushes and exactly n+12 paired/native operations. Source/native
families and unretired/mixed-work/EOF controls are checked. These are counter and
model-step results, not measured heap/time or machine-range guarantees. See the
[completion-cost note](../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md).

## Validation

Agda 2.8.0; run from `src/`:

```sh
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NativeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NativeReachability.agda
agda --safe Cardano_network/LeiosNotifyPipeLookahead/Rank.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ClientTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NodeTests.agda
```

All six commands completed with exit zero on 3 November 2026. Their logs and
exit-code manifest are in `/tmp/leios-notify-pipe-lookahead-t2-20261103/`.

T3.1 validation additionally uses:

```sh
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ClientNativeTests.agda
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverNativeTests.agda
```

These roots include both executable interpreters, productive trees and two-sided
bridges. They and the downstream `NativeTests`/`NativeReachability` roots completed
with exit zero; logs are in `/tmp/leios-notify-pipe-lookahead-t3-20261103/`.

After the directory refactor, the native entry point and all eight validation
roots above passed command-line `--safe` checks. The eight-root exit-code manifest,
logs, normalized source hashes and dependency-scan results are in
`/tmp/leiosnotify-lookahead-layering-20261103/`.

The native server bridge adds this safe root:

```sh
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ServerBridgeTests.agda
```

It and the downstream ClientNativeTests, DriverNativeTests, NativeTests and
NativeReachability roots passed. Logs and the exit-code manifest are under
`/tmp/leiosnotify-lookahead-server-bridge-20261103/`.

The native client adds this safe root:

```sh
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/ClientNetworkTests.agda
```

It and five relevant server/source-tree downstream roots passed after introducing
the native client and shared payload leaf. Logs and the exit-code manifest are
under `/tmp/leiosnotify-lookahead-client-network-20261103/`.

The native paired driver adds this safe root:

```sh
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/DriverNetworkTests.agda
```

It and five relevant client/server/source-tree downstream roots passed. Logs,
exit-code manifest and the dependency scan are under
`/tmp/leiosnotify-lookahead-driver-network-20261103/`.

The combined node policy adds this safe root:

```sh
agda --safe Cardano_network/Replay/LeiosNotifyPipeLookahead/NodeDriverTests.agda
```

It and the relevant `DriverNetworkTests`, `NodeTests` and native entry-point
checks passed. Logs, the exit-code manifest, audit and dependency scan are under
`/tmp/leiosnotify-lookahead-node-policy-20261103/`.

T3.2 now has an isolated build of the unchanged pinned peers and drivers in
[`src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools`](../Replay/LeiosNotifyPipeLookahead/tools/README.md).
Eight STM-controlled schedules pass five times each at GHC -N1 and -N2. Four
wire histories are compared to `NodeDriverTests` witnesses by evaluating the
pure `ExportFixtures.rendered` with Agda's DefaultCompute normalizer; all 40
comparisons and 30 missing-record/payload/order negative controls pass.
The export module also passes `agda --safe`. Its original witness theorem types
are unchanged. Full artifacts and the normalization/check logs are under
`/tmp/leiosnotify-haskell-final-20261103/`.

T3.3's follow-up now matches the other 40 captured histories through 22 checked
supplied-schedule certificates: two normals between Recv Quit and flag publication,
server-only excessive requests, termination at depth 1000 and the
arrived-before-result-publication Collect boundary. Each paired certificate
starts from the initial node-policy state and realizes the exact original rows
in the native paired tree. The synthetic writer's request-1001 fault has a
server-only node/native certificate. The publication cases also prove reachable
held-result checkpoints. Combined with the first four cases, all 80 captured
histories match (70 paired, including interrupted prefixes; 10 server-only).
The [T3.3 record](../Replay/LeiosNotifyPipeLookahead/tools/results-t33-20261103.json)
includes hashes and memory measurements. Its artifacts are under
`/var/tmp/leiosnotify-t33-20261103/verified/`. The
fixture callbacks, observer Effects and identity-codec transport are documented;
these runs do not execute all production node callbacks or certify CBOR/socket
behavior. Publication held after arrived increments can hold an already selected
Collect, delaying Quit until release; completion after release is observed.
No permanent-deadlock or measured-latency claim follows.

The guarded PTree roots use the established command-line safe checking mode.
The pure model, enumeration, rank and property modules declare `--safe`.
The targeted audit covers 105 Agda files across the protocol directory, native
entry point and replay directory. Its two `possible-hole` findings
are the question marks in the standard integer comparison operator `Int.<?`
in `ClientModel.below` and `positive`; inspection confirms they are operator
applications, not holes. There are no actual holes, postulates, trust primitives
or disabled checks in the new files. The four runtime certificate helpers and
all 1003 generated Agda files also pass strict scans with zero findings.
Safe typechecking is the compiler check;
the static scan does not audit all external dependencies. No Haskell source, deployed
node configuration, existing replay rule, or historical log verdict is changed.

The two new conservation roots safely check all six new property/bridge/test
modules and have strict zero-finding audits. They can be checked serially with
the persistent bounded wrapper from the repository root:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/check_agda.py \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/ConservationTests.agda \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/ConservationNativeTests.agda \
  --out /var/tmp/leiosnotify-conservation-checks
```

Final logs and resource records are under
`/var/tmp/leiosnotify-t4-conservation-20261103/final/`; the
[compact result](../Replay/LeiosNotifyPipeLookahead/tools/results-t41-20261103.json)
records exact source hashes and checking budgets.

The nine T4.1.2 modules are checked with the same bounded wrapper:

```sh
python3 -I -B src/Cardano_network/Replay/LeiosNotifyPipeLookahead/tools/check_agda.py \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/ShutdownTests.agda \
  Cardano_network/Replay/LeiosNotifyPipeLookahead/ShutdownNativeTests.agda \
  --out /var/tmp/leiosnotify-shutdown-checks
```

Logs and resources are under `/var/tmp/leiosnotify-t412-20261103/final/`; the
[T4.1.2 record](../Replay/LeiosNotifyPipeLookahead/tools/results-t412-20261103.json)
ties them to the exact source hashes and theorem scopes.

The eight T4.2.1 modules pass safe checking through `SchedulingTests.agda` and
`SchedulingNativeTests.agda` using the same bounded wrapper. Their strict scans
have zero findings. Final artifacts are under
`/var/tmp/leiosnotify-t421-20261103/final/`; the
[result record](../Replay/LeiosNotifyPipeLookahead/tools/results-t421-20261103.json)
includes exact source and resource hashes.

The seven T4.2.2 modules pass safe checking through `ProgressTests.agda` and
`ProgressNativeTests.agda`, with strict zero-finding audits and the same bounded
wrapper. Final artifacts are under `/var/tmp/leiosnotify-t422-20261103/final-v2/`;
the [result record](../Replay/LeiosNotifyPipeLookahead/tools/results-t422-20261103.json)
records the conditional scope and remaining general structural invariant.

The eight T4.2.2.3 component modules pass safe checking through
`ServerDrainTests.agda` and `ServerDrainNativeTests.agda`, with strict zero-finding
audits and the same bounded wrapper. The
[result record](../Replay/LeiosNotifyPipeLookahead/tools/results-t4223-20261104.json)
records exact sources, successful root checks and the remaining client/packet
connection. Existing imported `ShutdownTests` variable-name warnings are retained.

The nine T4.2.2.3.3 modules pass safe checking through `PairedDrainTests.agda`
and `PairedDrainNativeTests.agda`, with strict zero-finding audits and the same
bounded wrapper. The [result record](../Replay/LeiosNotifyPipeLookahead/tools/results-t42233-20261104.json)
records exact sources, successful checks, the completed structural theorem and
retained external runtime/implementation assumptions. T4.3 resource results are recorded below.

T4.3.1's six modules pass safe checking through `CompletionTests.agda` and
`CompletionNativeTests.agda` with strict zero-finding audits and the same bounded
wrapper. The [result record](../Replay/LeiosNotifyPipeLookahead/tools/results-t431-20261104.json)
records exact sources, successful checks, universal counts and all-state
occupancy certificates. T4.3.2 resource and representation results follow below.

T4.3.2 adds `ClientBounds`, `ResourceBounds`, `QueueBudget`, `NodeQueueBounds`
and `Representation` in the protocol layer, with `ResourceFixtures` and
`ResourceNativeTests` under Replay. The seven modules pass safe checking and
strict audits. Every fresh fixed-depth policy run has conservative live-resource
envelopes; the full-pipe Quit witness needs one extra marker slot. Historical
server deferred jobs remain unbounded, so depth cannot discharge their finite
Int-range premise. Signed arrival-counter range remains a separate obligation.
See the [resource-bounds note](../../../docs/notes/leiosnotify-pipe-lookahead-resource-bounds.md)
and [result record](../Replay/LeiosNotifyPipeLookahead/tools/results-t432-20261104.json).

## Runtime investigation

The [completion-cost topic](../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md)
maintains T5.1.1 history counts, T5.1.2 quiet baseline profiles and T5.2.1 Nat
heap/arithmetic diagnostics. T5.2.2's [runtime profiles](../../../docs/notes/leiosnotify-pipe-lookahead-progress.md#pinned-haskell-blocking-and-failure-experiments)
cover blocking, injected failures and credit/queue accounting. The topics link
committed records, reproduction commands and source pins, keeping runtime
outcomes distinct from model guarantees. These finite fixtures do not establish a verified repair, full
Haskell refinement or production-node severity.

The [source audit](../../../docs/notes/leiosnotify-pipe-lookahead-source-audit.md#remaining-implementation-and-replay-obligations)
collects the remaining runtime, representation and replay obligations. The
[numbered plan](../../../docs/specs/leiosnotify-pipe-lookahead-plan.md#t5-investigate-potential-implementation-problems)
tracks raw observation/capture evidence and stronger node-profile work.
The source audit also holds the T5.3 classification and resource-candidate
decision. The typed paired checker now completes its generic search scope;
Normalized profile/CLI delivery is implemented in the
[replay guide](../Replay/LeiosNotifyPipeLookahead/README.md#normalized-input-and-cli-delivery);
raw fidelity and complete captures remain open.

The separate [CollectOne candidate design](../../../docs/specs/leiosnotify-collect-one-design.md)
has compiled type/constructor feasibility and separate safe reference
[Model/Contract](../../../docs/specs/leiosnotify-collect-one-design.md#t612-behavior-and-observation-contract)
definitions. Their witness/guard root is
[CollectOne/ContractTests.agda](../Replay/LeiosNotifyPipeLookahead/CollectOne/ContractTests.agda).
[T6.2.1 preservation](../../../docs/specs/leiosnotify-collect-one-design.md#t621-finite-source-and-wire-preservation)
now proves both finite local source-action and exact wire inclusions without
extra premises. [T6.2.2 conditional resources/progress](../../../docs/specs/leiosnotify-collect-one-design.md#t622-conditional-resources-and-local-progress)
now prove B+1 registered inventory, exact early/final collection accounting,
shutdown safety, internal accessibility and finite local completion/operation
bounds. [T6.2.2.3 paired-policy bounds](../../../docs/specs/leiosnotify-collect-one-design.md#t6223-paired-policy-resource-bounds)
now discharge that premise for independent candidate driver/node rules. Every
fresh candidate policy history has an exact baseline policy history, yielding
≤1005 retained jobs/completions with no extra resource premise. Candidate native,
converse paired and Haskell correspondence remain open.
[T6.3.1 actual-driver comparison](../../../docs/notes/leiosnotify-pipe-lookahead-completion-cost.md#collectone-actual-driver-comparison)
now passes 1224 fresh fixture processes, with matching behavior and lower
retention/shutdown cost plus a small allocation increase. The
[T6.3.2 review bundle](../Replay/LeiosNotifyPipeLookahead/tools/patches/collect-one/README.md)
is now source/apply checked; these are controlled measurements and a proposal,
not a deployed-node result.

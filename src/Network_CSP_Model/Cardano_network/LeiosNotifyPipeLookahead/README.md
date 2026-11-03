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
namespace changes. The latest transitive scan of the native entry point and
protocol modules found 39 local dependencies and no Replay dependency. This is a module-boundary check;
the protocol properties retain the scopes documented below.

This is the first implementation stage for the
[lookahead replay design](../../../docs/specs/leiosnotify-lookahead-replay-design.md).
It models the server control flow in consensus
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
controlled pinned Haskell peer/driver schedules now pass, with four wire
histories matched to checked Agda witnesses. Wider differential coverage, full
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

Readiness APIs are retained in this bridge. Erasing them to obtain a wire-only
checker remains T7. `nodeNext` restricts callback reply kinds, while admission
outcomes remain abstract in this server model. The actual credit/queue binding
in `NodeModel` is a separate target; the initial admission-failure witness does
not claim that the pinned node rejects its first request. These results do not
establish Haskell refinement, store validity, codec behavior or infinite liveness.

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
callback domains also require T7's finite-basis proof before exhaustive replay.

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
[`tools/leiosnotify-lookahead`](../../../tools/leiosnotify-lookahead/README.md).
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
The [T3.3 record](../../../tools/leiosnotify-lookahead/results-t33-20261103.json)
includes hashes and memory measurements. Its artifacts are under
`/var/tmp/leiosnotify-t33-20261103/verified/`. The
fixture callbacks, observer Effects and identity-codec transport are documented;
these runs do not execute all production node callbacks or certify CBOR/socket
behavior. Publication held after arrived increments can hold an already selected
Collect, delaying Quit until release; completion after release is observed.
No permanent-deadlock or measured-latency claim follows.

The guarded PTree roots use the established command-line safe checking mode.
The pure model, enumeration, rank and property modules declare `--safe`.
The targeted audit covers 52 Agda files across the protocol directory, native
entry point and replay directory. Its two `possible-hole` findings
are the question marks in the standard integer comparison operator `Int.<?`
in `ClientModel.below` and `positive`; inspection confirms they are operator
applications, not holes. There are no actual holes, postulates, trust primitives
or disabled checks in the new files. The four runtime certificate helpers and
all 1003 generated Agda files also pass strict scans with zero findings.
Safe typechecking is the compiler check;
the static scan does not audit all external dependencies. No Haskell source, deployed
node configuration, existing replay rule, or historical log verdict is changed.

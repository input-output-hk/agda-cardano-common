# Hot→warm demotion: design (stage 3)

Status: draft for review. Facts and citations are in [`RESEARCH.md`](RESEARCH.md)
(ouroboros-network `4b3ab76`, ouroboros-consensus `27fa649ff`).

## 1. Question

When the outbound peer governor demotes a hot peer, does the peer end **Warm** (all hot
mini-protocols returned within the deactivate timeout) or **Cold** (timeout or error, so
`Mux.stop` and the connection is closed)? Specifically, in the scenario "Praos blocks keep
arriving, no Leios load":

- before ouroboros-consensus PR 2344 (LeiosNotify has no MsgQuit/MsgCanceled), and
- after it (LeiosNotify can quit with requests outstanding).

## 2. Scope

A standalone model in the style of `GovernorWedge/`: stdlib, `Process_Trees`, `CSP.Operators`,
`Semantics.{LTS,Failures,LTL.*}` only. It does not import `Cardano_network`. Each hot
mini-protocol is abstracted to its **termination behaviour after `Terminate`**. The
LeiosNotify abstractions are justified in comments by the existing results (`blk-stall`
for pre-PR; `LeiosNotifyPipelinedProps.pblk-afterQuit` for post-PR); a formal refinement
link to those modules is out of scope (see §8).

Not modelled: data content, the inbound governor (covered by `GovernorWedge/`), the
established protocols beyond "they keep running" (`LeiosNotifyIsolation` covers that),
churn, backoff, peer-sharing.

## 3. Events

- Governor: `demote` (start of `deactivatePeerConnection`, writes `Terminate`), `warm`
  (all hot returned, `PSA:1007-1014`), `tmo` (deactivate timeout fired, `PSA:1025-1033`),
  `cold` (after `Mux.stop`, peer ends Cold, `AP:988-1017`).
- Per hot protocol `p`: `ret p` (its initiator returned; the governor's `awaitAllResults`
  synchronises on all of them).
- Environment (what the hot initiators wait for while in a server-agency state):
  - `block` — a Praos header arrives (ChainSync `StMustReply` answer);
  - `txReq` — the remote TxSubmission2 inbound sends a blocking `MsgRequestTxIds`;
  - `lnReply` — a LeiosNotify reply (announcement/offer/votes) arrives (Leios load).
- Protocol-internal (not offered by `Env`): `quit` and `lnQuitDone` — post-PR only, the
  client sends MsgQuit and the remote LeiosNotify server answers it (MsgCanceled for each
  outstanding request, then MsgDone) without involving the server's application.

## 4. Processes

Each hot protocol, from the moment `demote` writes `Terminate`:

| Protocol | Abstract behaviour after `Terminate` | Source |
|---|---|---|
| ChainSync | waiting in `StMustReply`: `block → ret CS` | §3 ChainSync, `CSC:1265-1268` |
| BlockFetch | `ret BF` after finitely many internal steps (in-flight batches) | `BFC:122-130,183-190` |
| TxSubmission2 | waiting in `StIdle`: `txReq → ret TX` | `TxOut:131-145`, `TxCodec:84` |
| LeiosFetch | `ret LF` (nothing in flight in the scenario) | `LDL:726-734` |
| LeiosNotify, pre-PR | requests outstanding: `lnReply → (… → ret LN)`; no other way out | `LN:525-533`, `LN:214` |
| LeiosNotify, post-PR | `quit → lnQuitDone → ret LN` (no environment event needed) | PR 2344; `LeiosNotifyPipelined*` |

`Hot v = ChainSync ⦀ BlockFetch ⦀ TxSub ⦀ LeiosFetch ⦀ LeiosNotify v`, for `v ∈ {pre, post}`.

Governor (one demotion):
`Gov = demote → ( (awaitAll → warm → Skip) □ (tmo → cold → Skip) )`,
where `awaitAll` synchronises with every `ret p` (last-to-finish), and `tmo` is a visible
event that may fire at any time before `warm` (untimed model; same device as
`GovernorWedge/Timeout.agda`).

`Sys v = (Gov ∥_{ret, demote} Hot v) ∥_{env} Env`, where `Env` is the environment process
(which of `block`, `txReq`, `lnReply` it offers). "No Leios load" = `Env` never offers
`lnReply`.

## 5. Properties

Notation: runs are the LTL library's maximal runs (`Trace`), as in `LeiosNotifyQuitLive`.

- **(D1) Pre-PR, no Leios load: Warm is unreachable.** For `Sys pre` with `Env` never
  offering `lnReply`: no trace contains `warm`. Every maximal run that does not deadlock
  after `demote` contains `tmo` and then `cold`. (The model's form of "hot → 300 s → Cold".)
- **(D2) Post-PR, no Leios load: Warm is always still reachable, and fairness makes it
  happen.**
  - (D2a) In every reachable state of `Sys post` before `tmo`, a trace leading to `warm`
    exists, using only `block`, `txReq` and protocol-internal events.
  - (D2b) Every maximal run of `Sys post` that is fair for `block` and `txReq` (weak
    fairness, using `PFair` from `LeiosNotifyQuitLive`) and in which `tmo` does not fire
    reaches `warm`.
- **(D3) The remaining blockers (finding).** Post-PR, Warm is still unreachable if
  - `Env` never offers `txReq` (the remote TxSubmission2 never sends a blocking request), or
  - `Env` never offers `block` (no Praos block during the wait).
  Both shown by witness runs; each blocker forces the `tmo → cold` path on its own.
- **(D4) Contrast.** The pair (D1, D2b) as a single statement: in the same environment,
  `Sys pre` cannot reach `warm` while `Sys post` reaches it on every fair `tmo`-free run.

The model is untimed, so "within 300 s" is not expressed. D2b's "`tmo` does not fire"
stands for "every awaited event arrives before the timeout"; D1 and D3 say Warm is
impossible regardless of timing.

## 6. Layout (new folder `HotDemotion/`, one Agda module per concern)

- `HotDemotion/Model.agda` — events, the five protocol abstractions (pre/post variant for
  LeiosNotify), `Gov`, `Env` variants, `Sys`.
- `HotDemotion/PrePR.agda` — D1.
- `HotDemotion/PostPR.agda` — D2a, D2b.
- `HotDemotion/Blockers.agda` — D3, D4.
- `HotDemotion/README.md` — what is modelled, assumed, proved; citation key (shared with
  `RESEARCH.md`).

Conventions as in `CLAUDE.md` (`--guardedness`, one-line comment per definition, no
postulates/pragmas/sized types, forward declarations, `iter` for loops).

## 7. Verification

Each module typechecks from the project folder with `+RTS -M20G -RTS`; grep for
postulate/TERMINATING/mutual/Sized; report axioms used (LTL library `Traces_Based` carries
two postulates; D2b may import it).

## 8. Open points / later

- Formal refinement link from the abstract LeiosNotify processes to the real peer models
  (`LeiosNotifyQuit.blk-stall`, `LeiosNotifyPipelinedProps.pblk-afterQuit`).
- TxSubmission2 inbound policy: whether the remote can withhold `txReq` indefinitely is
  not traced (RESEARCH.md §5); D3 only shows the consequence if it does.
- ChainSync's `StMustReply` limit (601–911 s) exceeds `deactivateTimeout` (300 s); the
  `Pol:27-28` comment ("269 s") is stale. Worth reporting upstream independently.
- PR 2344's exact diff (time limits, depth, `CN2N:504-515`) was not available locally.

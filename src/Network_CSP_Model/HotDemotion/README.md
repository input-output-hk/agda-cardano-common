# Hot→warm demotion: what is modelled, assumed, and proved

Design: [`DESIGN.md`](DESIGN.md). Citations (ouroboros-network `4b3ab7664f609a1aee0f0c24dcfcfd0ab899fc42`,
ouroboros-consensus `27fa649ff`): [`RESEARCH.md`](RESEARCH.md). Plan: [`PLAN.md`](PLAN.md).

## 1. What this is

A small, standalone CSP model of one outbound hot→warm demotion (`deactivatePeerConnection`), checked
against the leios-prototype pins. It machine-checks when the demotion ends **Warm** and when it ends
**Cold** (the 300 s `deactivateTimeout` fires), before and after ouroboros-consensus PR 2344 (LeiosNotify
sends `MsgQuit` instead of draining its pipe). The five hot protocols are ChainSync, BlockFetch,
TxSubmission2, LeiosFetch, LeiosNotify; the governor writes Terminate, awaits all five, then goes Warm,
or times out and goes Cold.

Each protocol is reduced to its behaviour after Terminate (DESIGN.md §4 table).
The whole system is one synchronous step function `sstep` over a state (governor phase, phase per
protocol); `Sys m` is the process it generates, `Steps m` the pure multi-step relation, and `Lift.agda`
proves the two agree on traces.

## 2. Assumptions

- **Untimed.** `tmo` (the deactivate timeout) is a free choice of the governor while awaiting, not a clock.
  Mode flag `timer = false` removes it.
- **Environment flags** (`Mode`): `blocks` (a Praos header arrives for ChainSync), `txReqs` (the remote
  sends a blocking `MsgRequestTxIds`), `lnLoad` (a Leios reply arrives). The theorems fix them as stated.
- **LeiosNotify is abstracted.** Pre-PR it waits for a Leios reply (`waitEnv`); post-PR it sends
  `MsgQuit`, the remote answers, it returns, all without environment help. These abstractions are
  justified only by the peer models in `Cardano_network/Parametric/Leios/LeiosNotifyQuit.agda`
  (`blk-stall`) and `LeiosNotifyPipelinedProps.agda` (`pblk-afterQuit`); this library imports nothing
  from `Cardano_network`, so the link is a comment, not a proof.
- **Post-PR LeiosNotify assumptions** (`Model.agda`:119-124). The post-PR abstraction
  (`afterTerm post ln = needInt`) assumes
  (i) on Terminate the client sends `MsgQuit` even with a full pipeline: the real client pipelines to
  depth 100 and then blocks in `Collect Nothing`, which does not read the control var (RESEARCH.md §3,
  §5), and whether PR 2344 makes the client send `MsgQuit` from there (`CN2N:504-515`) is unverified; and
  (ii) both ends run PR 2344: a pre-PR server does not understand `MsgQuit` (protocol error, hence Cold).
  `pblk-afterQuit` holds only once the quit has been sent, and that model has pipelining depth 1.
  Every post-PR Warm result (D2, the post-PR half of D4) holds under these assumptions.
- **Worst-case phase at Terminate.** ChainSync is in `StMustReply` (needs a header) and TxSubmission2 in
  `StIdle` (needs a blocking `MsgRequestTxIds`). A TxSubmission2 already in a blocking `StTxIds` would
  return at once; D3 depends on this choice.
- **Not modelled:** the mini-protocol error path (an erroring hot protocol sends the peer to Cooling, then
  Cold; RESEARCH.md §2); the failure of `c_PEER_DEMOTION_TIMEOUT` itself (`AP:1010-1014`): in the model
  `cold` always follows `tmo`; and the BlockFetch registry bracket, which waits for the same peer's
  ChainSync (RESEARCH.md §3, `BFReg:160-163`), so in the model BlockFetch can return while ChainSync has
  not (as in `post-noBlock-nearlyWarm`), which is not realistic.
- One demotion of one peer; KeepAlive and PeerSharing (established, not hot) are not modelled.

## 3. Theorem index

Line numbers are of the definition's type signature. `Pre b t c` and `Post b t c` are the pre-/post-PR
modes with `blocks = b`, `txReqs = t`, `timer = c`, no Leios load.

| Claim | Name | File:line |
|---|---|---|
| Model (channels, `Steps`, `Sys`, `sstep`) | `Ev`, `Steps`, `SysAt`, `sstep` | `Model.agda`:44, 233, 199, 176 |
| `block` refused before demote | `block-only-when-waiting` | `Model.agda`:238 |
| Leios reply refused with no load | `lnReply-off` | `Model.agda`:242 |
| `Steps` and traces correspond | `Steps⇒traces`, `Sys-traces⇒Steps`, `Sys-anyTrace` | `Lift.agda`:106, 111, 124 |
| D1 pre-PR: LeiosNotify stuck | `pre-ln-stuck` | `PrePR.agda`:150 |
| D1 pre-PR: never Warm (states) | `pre-neverWarm` | `PrePR.agda`:156 |
| D1 pre-PR: no trace has `warm` | `pre-noWarm` | `PrePR.agda`:182 |
| D1 vacuity: all but LeiosNotify returned | `pre-nearlyWarm` | `PrePR.agda`:190 |
| D1 pre-PR: `tmo` always enabled (timer on) | `tmo-enabled` | `PrePR.agda`:160 |
| D1 run form: progress, deadlock free (timer on) | `pre-progress`, `pre-deadlockFree` | `PrePR.agda`:221, 252 |
| D1 run form: at most 11 events | `pre-bounded` | `PrePR.agda`:420 |
| D1 run form: √-ended traces are `t₁ ++ tmo ∷ t₂`, cold in `t₂` | `pre-endsCold` | `PrePR.agda`:516 |
| Run-form tools (any mode): timer ⇒ deadlock free; Steps bound ⇒ trace bound; invariant ⇒ `tmo` then `cold` | `timer-deadlockFree`, `steps⇒traceBound`, `endsCold` | `PrePR.agda`:247, 410, 507 |
| D2 post-PR: LeiosNotify returns without env | `post-ln-noEnv` | `PostPR.agda`:50 |
| D2a: Warm reachable from every *reachable* awaiting state | `post-warmReachable` | `PostPR.agda`:392 |
| D2b: deadlock / divergence free, at most 13 events | `post-bounded` (`post-deadlockFree` 408, `post-divergenceFree` 413, `post-traceBound` 422) | `PostPR.agda`:427 |
| bound is tight | `post-tight` | `PostPR.agda`:451 |
| D2b LTL: every run eventually fires `warm` | `post-warmLTL` | `PostPR.agda`:551 |
| D3 no blocking txReq: never Warm | `post-noTxReq-noWarm` | `Blockers.agda`:131 |
| D3 no blocking txReq, timer on: deadlock free, ≤ 14 events, √-ended traces have `tmo` then `cold` | `post-noTxReq-endsCold` (`RunCold` 40) | `Blockers.agda`:136 |
| D3 vacuity: only TxSubmission2 outstanding | `post-noTxReq-nearlyWarm` | `Blockers.agda`:140 |
| D3 no Praos block: never Warm | `post-noBlock-noWarm` | `Blockers.agda`:230 |
| D3 no Praos block, timer on: deadlock free, ≤ 14 events, √-ended traces have `tmo` then `cold` | `post-noBlock-endsCold` | `Blockers.agda`:235 |
| D3 vacuity: only ChainSync outstanding (in the model) | `post-noBlock-nearlyWarm` | `Blockers.agda`:241 |
| D4 contrast (modes differ only in the LeiosNotify variant) | `contrast` | `Blockers.agda`:254 |

D1 headline (`pre-neverWarm`, `pre-endsCold`): before the PR, with no Leios load, a demotion never
ends Warm; with the timer on every run goes `tmo` then `cold`. D2 headline (`post-warmLTL`, under the
post-PR LeiosNotify assumptions of §2): after the PR, with blocks and tx requests offered and no
timeout, every run reaches Warm, in at most 12 moves (`post-bounded`: 13 events counting √;
`post-traceBound`). D3 headline (`post-noTxReq-endsCold`, `post-noBlock-endsCold`): after the PR, with
the timer on, no blocking `txReq`, or no Praos block, on its own makes every run end `tmo` then `cold`.

The run forms combine three facts: deadlock freedom (a run never stops short of √), a trace bound (runs
are finite) and the system's lack of τ (`Sys-no-τ`, so no divergence); hence every maximal run is a
√-run, and the √-ended statement applies to it.

## 4. Reproduction

Run from `src/Network_CSP_Model` (the nested `.agda-lib`):

```
agda HotDemotion/Blockers.agda +RTS -M20G -RTS     # imports Model, Lift, PrePR, PostPR
grep -nE 'postulate|TERMINATING|mutual|Sized' HotDemotion/*.agda   # only comment hits in PostPR.agda, Blockers.agda
```

## 5. Axioms

None used: no `postulate`, no `TERMINATING`/`NON_TERMINATING`, no sized types, no `mutual`.
`PostPR` (`PostPR.agda`:36) and `Blockers` (`Blockers.agda`:32) import definitions from
`Semantics.LTL.Traces_Based`, which contains two library postulates (`⟦G⟧⇒⟦G⟧⁺`, `¬G⇒F¬`); neither
is imported or used.

## 6. Deviations from DESIGN.md

- One monolithic product step function instead of a parallel composition of per-protocol processes
  (§4's ∥), giving far cheaper proofs (the `GovernorWedge` pattern). The traces differ from §4's
  `(Gov ∥ Hot) ∥ Env`: there, hot protocols can still act after `tmo`, whereas `sstep` freezes them;
  and §4's `(awaitAll → warm) □ (tmo → cold)` would resolve the choice at the first return, whereas
  `sstep` keeps `tmo` enabled throughout awaiting. The product model is the faithful one for the
  Warm/Cold outcome (on timeout `Mux.stop` kills the hot protocols, so nothing they do afterwards
  matters), not a trace-equivalent rendering of §4.
- D2b needs no fairness assumption: every move strictly lowers a rank, and with `blocks = txReqs = true`
  the environment offers `block` and `txReq` whenever ChainSync / TxSubmission2 awaits them
  (`PostPR.agda`:456-460), so no run can avoid `warm`.
- D1 is stated as a run form (progress, bound, √-ended traces contain `tmo` then `cold`) rather than a
  single failures statement; D3 likewise (`RunCold`). `Pre` is parameterised by the timer;
  the D1 safety results hold for both settings, the run-form progress needs the timer on.
- Trace bounds 11 (pre), 13 (post, no timer) and 14 (post, timer on; D3) count the final √: 10, 12 and
  13 moves. The D3 bound reuses PostPR's rank and is not tight for the blockers.
- D2a is stated for awaiting states; a hot state reaches awaiting by one `demote`.
- D4 compares `Pre true true false` and `Post true true false`, which differ only in the LeiosNotify
  variant (both without the timer).

## 7. Findings

- **Pre-PR LeiosNotify always forces Cold** when there is no Leios load (`pre-neverWarm`,
  `pre-endsCold`; RESEARCH.md §5): the demotion takes the full 300 s timeout every time.
- **After PR 2344, TxSubmission2 and a long Praos block gap still can** (`post-noTxReq-noWarm`,
  `post-noBlock-noWarm`; with the timer on, `post-noTxReq-endsCold` and `post-noBlock-endsCold`
  prove each forces `tmo` then `cold` on its own): Warm needs a blocking `MsgRequestTxIds` from the
  remote and a block header for ChainSync, given the worst-case phases of §2. Whether a remote can
  withhold the request is not established (RESEARCH.md §5, DESIGN.md §8). In the model the other hot
  protocols can all return (vacuity guards); in practice BlockFetch also waits for ChainSync (§2).
- **ChainSync `StMustReply` limit (601–911 s) exceeds `deactivateTimeout` (300 s)**
  (`CSCodec:53-60`); the "269 s" comment at `Pol:25-31` (and `CSTL:78-79`) is stale (RESEARCH.md §3, §5).
  Worth reporting upstream independently.
- Not covered: PR 2344's exact diff (time limits, depth) was unavailable locally (DESIGN.md §8).

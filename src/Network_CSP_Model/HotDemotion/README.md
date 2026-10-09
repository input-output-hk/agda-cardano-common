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
- One demotion of one peer; KeepAlive and PeerSharing (established, not hot) are not modelled.

## 3. Theorem index

Line numbers are of the definition's type signature.

| Claim | Name | File:line |
|---|---|---|
| Model (channels, `Steps`, `Sys`, `sstep`) | `Ev`, `Steps`, `SysAt`, `sstep` | `Model.agda`:45, 229, 195, 172 |
| `block` refused before demote | `block-only-when-waiting` | `Model.agda`:234 |
| Leios reply refused with no load | `lnReply-off` | `Model.agda`:238 |
| `Steps` and traces correspond | `Steps⇒traces`, `Sys-traces⇒Steps`, `Sys-anyTrace` | `Lift.agda`:108, 113, 126 |
| D1 pre-PR: LeiosNotify stuck | `pre-ln-stuck` | `PrePR.agda`:148 |
| D1 pre-PR: never Warm (states) | `pre-neverWarm` | `PrePR.agda`:154 |
| D1 pre-PR: no trace has `warm` | `pre-noWarm` | `PrePR.agda`:180 |
| D1 vacuity: all but LeiosNotify returned | `pre-nearlyWarm` | `PrePR.agda`:188 |
| D1 pre-PR: `tmo` always enabled | `tmo-enabled` | `PrePR.agda`:158 |
| D1 run form: progress, deadlock free | `pre-progress`, `pre-deadlockFree` | `PrePR.agda`:218, 240 |
| D1 run form: at most 11 events | `pre-bounded` | `PrePR.agda`:399 |
| D1 run form: √-ended traces are `t₁ ++ tmo ∷ t₂`, cold in `t₂` | `pre-endsCold` | `PrePR.agda`:483 |
| D2 post-PR: LeiosNotify returns without env | `post-ln-noEnv` | `PostPR.agda`:50 |
| D2a: Warm reachable from every awaiting state | `post-warmReachable` | `PostPR.agda`:391 |
| D2b: deadlock / divergence free, at most 13 events | `post-bounded` (`post-deadlockFree` 407, `post-divergenceFree` 412, `post-traceBound` 421) | `PostPR.agda`:430 |
| bound is tight | `post-tight` | `PostPR.agda`:454 |
| D2b LTL: every run eventually fires `warm` | `post-warmLTL` | `PostPR.agda`:554 |
| D3 no blocking txReq: never Warm | `post-noTxReq-noWarm` | `Blockers.agda`:110 |
| D3 vacuity: only TxSubmission2 outstanding | `post-noTxReq-nearlyWarm` | `Blockers.agda`:114 |
| D3 no Praos block: never Warm | `post-noBlock-noWarm` | `Blockers.agda`:204 |
| D3 vacuity: only ChainSync outstanding | `post-noBlock-nearlyWarm` | `Blockers.agda`:208 |
| D4 contrast (same env, before vs after) | `contrast` | `Blockers.agda`:219 |

D1 headline (`pre-neverWarm`, `pre-endsCold`): before the PR, with no Leios load, a demotion never ends
Warm; every run goes `tmo` then `cold`. D2 headline (`post-warmLTL`): after the PR, with blocks and
tx requests offered and no timeout, every run reaches Warm in at most 12 moves.

## 4. Reproduction

Run from `src/Network_CSP_Model` (the nested `.agda-lib`):

```
agda HotDemotion/Blockers.agda +RTS -M20G -RTS     # imports Model, Lift, PrePR, PostPR
grep -nE 'postulate|TERMINATING|mutual|Sized' HotDemotion/*.agda   # only a comment hit in PostPR.agda
```

## 5. Axioms

None used: no `postulate`, no `TERMINATING`/`NON_TERMINATING`, no sized types, no `mutual`.
`PostPR` imports definitions from `Semantics.LTL.Traces_Based`, which contains two library
postulates (`⟦G⟧⇒⟦G⟧⁺`, `¬G⇒F¬`); neither is imported or used.

## 6. Deviations from DESIGN.md

- One monolithic product step function instead of a parallel composition of per-protocol processes
  (§4's ∥). Same traces by construction, far cheaper proofs (the `GovernorWedge` pattern). Consequently D2b's
  fairness assumption is vacuous: the process has no fairness-sensitive scheduling.
- D1 is stated as a run form (progress, bound, √-ended traces contain `tmo` then `cold`) rather than a
  single failures statement.
- Trace bounds 11 (pre) and 13 (post) count the final √: 10 and 12 moves.
- D2a is stated for awaiting states; a hot state reaches awaiting by one `demote`.
- D3 is stated over `Steps` (states), not traces; `post-noTxReq-nearlyWarm` and `post-noBlock-nearlyWarm`
  show the blocker is the named protocol alone (LeiosNotify returns without env post-PR).

## 7. Findings

- **Pre-PR LeiosNotify always forces Cold** when there is no Leios load (`pre-neverWarm`,
  `pre-endsCold`; RESEARCH.md §5): the demotion takes the full 300 s timeout every time.
- **After PR 2344, TxSubmission2 and a long Praos block gap still can** (`post-noTxReq-noWarm`,
  `post-noBlock-noWarm`): Warm needs a blocking `MsgRequestTxIds` from the remote and a block header
  for ChainSync. Whether a remote can withhold the request is not established (RESEARCH.md §5, DESIGN.md §8).
- **ChainSync `StMustReply` limit (601–911 s) exceeds `deactivateTimeout` (300 s)**
  (`CSCodec:53-60`); the "269 s" comment at `Pol:25-31` (and `CSTL:78-79`) is stale (RESEARCH.md §3, §5).
  Worth reporting upstream independently.
- Not covered: PR 2344's exact diff (time limits, depth) was unavailable locally (DESIGN.md §8).

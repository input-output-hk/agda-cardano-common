# Praos-over-Leios priority

BlockFetch (**Praos**) is prioritised over LeiosFetch (**Leios**) at each link's
send arbiter in the Cardano `NetworkLink` mux. Under contention *on the same
link*, a pending BlockFetch `sndmsg` prunes a concurrently-offered LeiosFetch
`sndmsg` — but only while BlockFetch is actually competing, so LeiosFetch is
**delayed, not lost** (it reappears once the BlockFetch contention clears).

This folder collects the Cardano-specific priority work. The generic priority
machinery it builds on lives in the model-agnostic layer `CSP/Priority/`
(the operator `Priᶜ`, the finite-branching certificate `FinBr`, and the
`FinBr` closure lemmas — including `CSP/Priority/ClosureLoop.agda`'s
`finBr-loop0menu`/`finBr-⦀⋆` for the medium's `loop0 (pchoice …)` leaves).

## The idea

The channel-level priority operator `Priᶜ` (`CSP.Priority.Channel`) prunes an
offer whenever a *dominating* channel is present in the same node's finite offer
support. Two ingredients make it model praos-over-leios:

- **The order.** `bfOverLf` makes, per link, `sndmsg … N2N_BlockFetch` dominate
  `sndmsg … N2N_LeiosFetch` (and nothing else) — protocol identity is the `IDs`
  tag carried on every wire channel, so the order keys on a finite channel tag,
  never on payload.
- **The placement.** `Priᶜ` overlays the per-link **send queue** `Inputsₗ l`
  (not the `Transmitterₗ` leaf). An `Input` cell offers its `sndmsg` only after
  it has buffered a message, so `Inputsₗ`'s offer support is *readiness-sensitive*:
  `Priᶜ` prunes LeiosFetch's `sndmsg` exactly when a BlockFetch message is
  genuinely queued. Overlaying the transmitter instead — whose menu offers every
  protocol unconditionally — would starve LeiosFetch outright.

## Modules

| Module | Lines | Purpose |
|---|--:|---|
| `BfOverLf.agda` | 163 | The channel-level priority **order** `bfOverLf : PriOrderC` over `Net Payload`: per link, BlockFetch's `sndmsg` dominates that link's LeiosFetch `sndmsg`; every other channel pair is unordered. All order laws (irreflexivity/transitivity/soundness/completeness/inhabitation) proved by exhaustive case analysis. Consumed by `NetworkLinkPri`. |
| `NetworkLinkPri.agda` | 201 | The **prioritised medium**. Overlays `Priᶜ bfOverLf` onto each link's `Inputsₗ` send queue: `fbInputsₗ` assembles the required `FinBr` certificate (per-cell `finBr-loop0menu`, folded by `finBr-⦀⋆`), `TxSideₗ-pri` is the priority-overlaid Tx side, and `NetworkLinkPri`/`NetworkLinkPriA` (renamed into `Net_Api Payload`) are the drop-in replacements for `NetworkLink`/`NetworkA`. Construction only. |
| `FourNodeDiamondPri.lagda.md` | 47 | `systemPri` — the four-node diamond over the prioritised medium `NetworkLinkPriA`, reusing the existing `nodeA`/`nodeB`/`nodeC`/`nodeD` and `ioES` verbatim. A construction-only deliverable (it typechecks; no behavioural property is proved over the full system). |
| `TxSidePriOneLink.agda` | 233 | The **priority properties**, on a minimal fully-concrete `Params` (one link running exactly BlockFetch + LeiosFetch) so the priority decision computes by reduction: P1 (prune-under-contention), P2 (delayed-not-lost), P3 (priority introduces no deadlock). |

## Properties (`TxSidePriOneLink.agda`)

All three are proved by direct reduction on a fully-concrete `Params p₀`, over a
representative send-buffered state `bothBuffered = Pbf ⦀ Plf` (the two `Input`
cells' post-`input` continuations, competing for the wire):

- **P1 — prune-under-contention.** `pri-keeps-bf`: with both a BlockFetch and a
  LeiosFetch `sndmsg` offered, `Priᶜ bfOverLf` still offers BlockFetch's; and
  `pri-prunes-lf`: it does **not** offer LeiosFetch's (its dominator is present).
- **P2 — delayed-not-lost.** `pri-lf-reappears`: once BlockFetch's `sndmsg` fires
  and its cell moves on, LeiosFetch's `sndmsg` is offered again (its dominator
  has gone). `bf-fires` witnesses the connecting `─[ ev sBF ]─►` step.
- **P3 — no deadlock.** `pri-no-deadlock-contended`/`-drained` (something is
  always offered at the prioritised contention states) and `head-offers-input`
  (the fresh head of the *real* `Inputsₗ`/`fbInputsₗ` still offers `input`, since
  `bfOverLf` leaves incomparable channels untouched) — so priority pruning never
  empties the menu.

## Scope & follow-ons

The proofs are deliberately scoped to the isolated one-link setting:

- `bothBuffered` is a hand-built **representative** of the contention state (it is
  the genuine `inputMenu` continuation), not proven reachable from
  `TxSideₗ-pri l₀`'s own transitions; the `p₀`-concreteness is what makes the
  priority decision reduce.
- `systemPri` is a construction, not a behavioural proof.

Documented follow-ons: hoist the generic `finBr-Output` helper from
`NetworkLinkPri.agda` into `CSP/Priority/Closure.agda`; a full
`DeadlockFree (TxSideₗ-pri l₀)` over the composed medium's reachable states;
behavioural properties over `systemPri`; and a general (non-concrete-`Params`)
restatement of P1/P2 (which would go through `MuxDelayed.priᶜ-mux-reappears`
plus a hand-built `ExactSupp`).

## Reading order

`BfOverLf` → `NetworkLinkPri` → `TxSidePriOneLink` (properties) →
`FourNodeDiamondPri` (whole-system construction). Prerequisites: the generic
`CSP/Priority/*` layer and the unprioritised `NetworkLink.agda` medium.

# CSP-refinement liveness — STATUS (**ROUTE COMPLETE AND UNCONDITIONAL** to `LivenessSpec`; *** `Premises = {}` — THE RECORD IS EMPTY ***; all 12 in-flight facts premise-free; campaigns 1–10 + the CROSS-NODE API CAMPAIGN + the CELLCP3 WINDOW, CLOSED)

## *** THE FINAL TRUTH (cellCp3 window, 2026-08-26) — THERE IS NOTHING LEFT ON THIS ROUTE. ***

`LivenessProof.At.Premises` has **ZERO fields**.  `cellCp3` — the last one, and the only
premised content of the whole route since T12 — is a **THEOREM**: `LiveChanJoin.cellCp3-of`
(§5e), off the CARRIED join alone.  Half one is `LiveChanInv`'s `cvBlk`/`cvStr` (an unread
block in a hop's cell puts that hop's reader inside its streaming region, `CliStrA`); half
two is `LiveDrvBFA.UpIdl` and `LiveDrvBFD.DnIdl`, the two new members landed by the window's
slices A and B (the reader sits at `bcIdle` throughout its PRE-REQUEST region, and
`CliStrA bcIdle = ⊥`); and the two regions **partition** the premise's own position
hypothesis (`UpPre ∪ RelayCp3 = RelayPre`, `DnPre ∪ ConsCp3 = InCp03` — both inclusions and
disjointness machine-checked on all seventeen / all seven shapes), so the conclusion is the
one sub-phase left: `cp3`.

`livenessSpec`'s type and TERM did not move (md5 `cbbbb200b6aea165f0a43b62c6b6f97c` over the
raw five lines of `livenessSpec-at` + `livenessSpec`, identical to the campaign base
`9de2bd0`); `Premises` is KEPT as an EMPTY record so that stays true, and
**`livenessSpec-un : LivenessSpec`** spends the now-trivial hypothesis (`record {}`).  So both
headlines of `LivenessProof` are unconditional:

- `livenessSpec-un : LivenessSpec` — `∀ b → LSpec b true true ⊑FD (breakableSystemOf b ∖ hidden b)`
- `livenessDivFree : ∀ b → DivergenceFree (breakableSystemOf b ∖ hidden b)`

**WHAT REMAINS FOR THE PROJECT ON THIS ROUTE: NOTHING.**  No premise, no residual, no parked
obligation is consumed anywhere in `LivenessProof`'s closure.  The two CLASSICAL SEAMS stay
exactly as recorded below (`modA-transfer` and `¬-divergent→normal`, both certified from one
`dne` in `CSP.Laws.ClassicalFromLEM`) — they are the route's only non-constructive content and
they were never premises of it.  `LiveTokenExcl` §1b/§3's chain alignments and
`LiveCellOpen`'s `CellRdy` are the routes NOT taken; they stay parked, type-checked and
consumer-free.  Everything below this block is HISTORY and is superseded in place where it
states a premise count.


**Date:** 2026-08-26 · **Branch:** `examples/cardano_network_refinement` at the *** CROSS-NODE API CAMPAIGN CLOSE *** (`af5d964..HEAD`, **229 commits** counting this close commit; the cross-node api campaign itself is the last **104**, `d593b31..HEAD`; `af5d964..d593b31` = **125** at the InFlightOpen close, whose own campaign was the 33 of `0d775bb..d593b31`).  *** (CORRECTED at the post-close fix round: this cited "the last 137, `0d775bb..HEAD`" — `0d775bb` is the PREDECESSOR InFlightOpen campaign's base, not this one's, so 33 of those 137 belong to it, and the sentence was self-inconsistent besides: 124+137≠229.  This campaign's base is `d593b31`, as its own plan file states.) *** · **State:** all green, LTL endpoint never red at any point.

**THE ROUTE IS CLOSED, AND (SINCE THE CELLCP3 WINDOW) THE PREMISED CONTENT IS ZERO.**  It read "down to ONE REACHABILITY ARGUMENT — `cellCp3` — AND NOTHING ELSE" at the cross-node close; that argument is now a theorem too (see the block above).  *** All NINE api co-position equations are DISCHARGED, both residual fields are RETIRED (`csRes` at T8c-iii, `bfRes` at the T12 close) and `Premises` has ZERO fields (`cellCp3` retired at the window). ***
(nine at the InFlightOpen close; **ALL NINE have been discharged** by the cross-node api campaign.
FIVE went off S1 —
`pp4` at its T1, `pp5` at its T2, `pp1` at its T5, `pp2` at its T6d and `cp5` at its T7 — the relay
DRIVER-TAIL coupling (`LiveDrvBF.DrvCp`), the first object in this development to run driver phase
⇒ peer position.  The other FOUR could NOT move into `DrvCp` and are DERIVED at `LiveRelayCS`
instead, each from a further carried object: `cp6`/`pp0` at T8c-iii from `LiveDrvCSD.DnJoint` (the
SEVENTH `LegJointU` factor) plus the bundled `CsIdleExcl`; `cp4` at T10 from `LiveDrvBFA.UpJoint`
(the EIGHTH) plus the token's own level computation; and `pp3` at T11h — the last of all nine, and
the only one whose equation is a Σ rather than a position — from `LiveDrvBFD.BFFresh` (the FIFTH
factor's THIRD half) through `areq-of⁺⁺` and §3's per-phase `Sharp`.  T1/T2 are the BlockFetch pair and T5/T6d/T7 the ChainSync triple, so a reader
reconstructing the arithmetic should count **two BF arms and three CS ones**, not two arms in total.
`cp5` (T7) is the odd one of the five: the only DISCHARGE on the CONSUME side, the only one whose
co-party is a CLIENT, and the only one that needed the coupling to carry sub-phases the residual does
not name (`cp2`/`cp3`/`cp4`, three pure carriers, because the row that establishes the position fires
three BlockFetch api hops before the sub-phase the residual names).  Two of
the five needed a second ingredient, because at those sub-phases the coupling can carry only a
REGION and not a position: `{bsWsb, bsStream}` at `pp5`, closed by `LiveSrvOpen.srvWsb-⊥` under
`isStable` — off `LiveChanInv.cvQui` STRENGTHENED at T2 from the negative `¬ RespFull` to the
positive `CellPreQ` — and `{csWar, csMust}` at `pp2`, closed by `LiveSrvOpen.csWar-⊥` off the
ChainSync CHANNEL invariant (`LiveChanCS`, T6b; joined T6c)).
`CSP_Refinement/LivenessProof.agda` delivers both ends:

- `livenessSpec : (∀ (b : Block₃) → At.Premises b) → LivenessSpec`
  — the CONDITIONAL headline, **statement unchanged by campaign 10**, with the premise
  families carried **in its type** (`At.Premises`, a record, so the conditionality
  cannot be lost by quoting the name).  *** The record now has ZERO fields *** (T8c-iii retired `csRes`; T10 shrank `bfRes` to one equation, T11h discharged that equation and T12 retired the field; the CELLCP3 WINDOW retired `cellCp3`, so the record is EMPTY and `livenessSpec-un` spends it).  It is deliberately KEPT, empty, so that `livenessSpec`'s type and term do not move.  `livenessSpec`'s DEFINITION is byte-identical across the whole campaign — **and record the RECIPE with any digest, because a bare one has now cost three separate reproduction attempts**: md5 `cbbbb200b6aea165f0a43b62c6b6f97c` is over the THREE indented `livenessSpec-at` lines PLUS the TWO top-level `livenessSpec` lines and nothing else; md5 `059315f2…` (the controller's ledger) is over `grep -A2 '^livenessSpec :'`; the two are digests of DIFFERENT extractions and are not comparable.  The claim they both support is the same one and it holds under either, plus a third recipe the final review ran; identity checked at `0d775bb`, `f68f1e4`, `558ded7`, `9de2bd0` and the close.  **The stronger check, which needs no convention at all, is whole-file identity of `LivenessProof.agda` against the campaign base** — available for every task except the window's slice D, where the file HAD to change (the field and the `lspec-fd` argument) and the definition's own lines are what is byte-identical. so every retirement made its STATEMENT strictly stronger at an unchanged term.  The gain
  is DISCHARGEABILITY, not premise strength — state it that way: `ifo-of` DERIVES the
  twelve position facts from these fields plus proved content, so the new set **implies**
  the old one (and the converse fails: twelve position refutations do not give a per-hop
  channel invariant), i.e. it is logically at least as strong.  What is better is that the
  carryable object has left the record ENTIRELY — the channel invariant with its base, its
  frame and its per-step-class preservation calculus is now THREADED (§3's join, both hops)
  — leaving the cell/reader alignment plus a CHARTED cross-node residual, where none of the
  twelve position facts ever had any route at all.

  | | field | content |
  |---|---|---|
  | (P1) | ~~`cellCp3`~~ | **RETIRED AT THE CELLCP3 WINDOW — DISCHARGED, not dropped.**  The cell/reader alignment (`LiveLegStep:967-972`'s `CellCp3`) is a THEOREM: `LiveChanJoin.cellCp3-of` (§5e) proves it off the CARRIED join — `LiveChanInv`'s `cvBlk`/`cvStr` for half one, the new `LiveDrvBFA.UpIdl` / `LiveDrvBFD.DnIdl` members for half two, the two guard regions PARTITIONING the premise's own position hypothesis so the conclusion is the one sub-phase left (`cp3`).  `LiveLegAssembly`'s io READ class carries the obligation on its preservation MAP at the arm's own `r` and `LiveChanJoin` retires it there, one site, one line.  *** So this table has NO live rows and `Premises` is an EMPTY record. *** |
  | (P3′) | ~~`csRes`~~ | **RETIRED at T8c-iii — the ChainSync half of the api residual is GONE.**  Its last two equations (`cp6`, `pp0` — the SAME equation `≡ csAreq` at two sub-phases over ONE slot, the leg's down-hop CS SERVER) are DERIVED at `LiveRelayCS` §3 from the CARRIED pair `LiveDrvCSD.DnJoint` (node D's freshness clause × its driver-tail coupling, `LiveChanJoin.LegJointU`'s **seventh** trailing factor) sharpened by the four `csIdle` exclusions `LiveSrvOpen` §6 proves from stability.  *** UNLIKE the other five discharges the equation does NOT move into `LiveDrvBF.DrvCp`: *** proving it needs `DnFresh`, `DrvCliD` AND stability, and `DrvBF`'s preservation is state-to-state — so `coAt-split-at` gained a THIRD unconditional premise (the bundled `CsIdleExcl`), which in turn fired the deletion of the two consumer-less `relayOpen-*-ws′` corollaries.  `LiveRelayCS.CSAt` is now `⊤` at all seventeen shapes and `csResidual-triv` proves the residual.  Earlier discharges of this half: `pp1` at T5, `pp2` at T6d, `cp5` at T7 (falsifications F26/F43/F47, re-run at the new arity at T8c-iii). |
  | (P3′) | ~~`bfRes`~~ | **RETIRED AT THE T12 CLOSE — the BlockFetch half is GONE too, and with it the last field beside `cellCp3`.**  `pp3`, the ninth and last of the charted equations, is DISCHARGED at T11h: `LiveRelayCS` §3's per-phase `Sharp` carries it, proved by `areq-of⁺⁺` from the CARRIED `LiveDrvBFD.BFFresh` (`LiveChanJoin.LegJointU`'s FIFTH factor's THIRD half, landed at T11h across five `mkBFJoint` arm sites).  `LiveRelayCS.BFAt` is `⊤` at all seventeen `CPPh` shapes and `bfAt-triv`/`bfResidual-triv` prove the residual outright, so the T11h review INHABITED this field's type PREMISE-FREE before the deletion — which is why deleting it STRENGTHENS the headline instead of moving work.  F91 is RETIRED with the honest record (its target was `pp3`; the F7→F48→F49→F91 terminus on the BF axis) and F108 is the successor guard, weakening `Sharp`'s new `pp3` clause to `⊤` and going RED at `LiveRelayCS:924.54-61`.  Its history, since the arithmetic is the campaign's own: **TWO** such equations since the cross-node campaign's T2 (`LiveRelayCS.BFResidual`) — `cp4`, `pp3` (THREE after T1).  The other two are **DISCHARGED**: `pp4` at T1 and `pp5` at T2, both off `LiveDrvBF.DrvCp`'s own clauses, CARRIED as `LiveChanJoin.LegJointU`'s fifth trailing factor, and `LiveRelayCS.coAt-split-at` proves `CoAt`'s clauses from them (falsifications F12/F18).  `pp5`'s clause is a REGION `{bsWsb, bsStream}` and takes one further ingredient at the consumer — the stability refutation of `bsWsb` (`LiveSrvOpen.srvWsb-⊥`), which is why the two api fields now carry the down link's unbrokenness.  `Premises` has TWO fields since T8c-iii retired `csRes`, and this is the only api field left — its TYPE shrank twice.  **(T9) STILL TWO, and `pp3` is RE-CLASSIFIED from "transcription" back to "new kind"** — the carried freshness clause is VACUOUS at `pp3` (its guard's `pp3` clause is `⊥` by construction) and one leaf of its dispatch, node D at `cp1`, needs a ChainSync-axis chain with two never-built objects; see §3's T9 postscript and `LiveRelayCS` §5b.  **(T10) ONE, `pp3` ALONE.**  `cp4` is DISCHARGED at `LiveRelayCS` §2c off the NEW carried pair `LiveDrvBFA.UpJoint = UpBd × UpCli` (`LiveChanJoin.LegJointU`'s EIGHTH trailing factor) plus the token's own level computation at the guard (`pipeInv⇒sent-cp4`: at `consuming _ cp4` the token can only be at `L2`, whose producer constraint IS `ProdSent`).  The arm cost the two relay api fields their SECOND link antecedent — `oRelayIn`/`oRelayOut` now take BOTH the up and the down link's unbrokenness, because the `cp4` refutations are moves of the UP medium — and it paid the standing per-clause refactor ruling: `coAt-split-at`'s three unconditional premises are now ONE per-phase `Sharp`.  Guards F89/F90/F91 plus the four re-runs F18/F26/F43/F47 at the refactored arity, and **F92 in the fix round — F48 re-aimed at `Sharp`'s `cp6` clause, the CS half having had NO live vacuity guard since T8c-iii** (`LiveRelayCS` §10).  **(T11) STILL ONE — `pp3`, and it is still a PREMISE, but the equation is now PROVED at `LiveRelayCS` §2d (`areq-of`) modulo ONE hypothesis (T9's `cp1` leaf) and the carry.**  The object is `LiveDrvBFD` (the BF freshness twin, guard region `consuming` ∪ `{pp0 … pp3}`); five of the sharpening's six premises are theorems, the leaf is down from five client positions to FOUR (`LiveDrvCSD` §6f), and the object is NOT yet a `LegJointU` factor — the ninth, priced at the eighth's measured 290.  Guards F93/F94 (this task's two novel families in `LiveDrvBFD`), F95 (the new reader-polarity BF ladder's landing) and F96 (the `cp2` OUTPUT-prefix offer's landing); F91 STILL STANDS at a funded target. |
| | **THE SWEEP RULE, WITH ITS COMPLEMENT (banked in T10's fix round).** T8c banked "after any retirement, grep the RETIRED NAMES — a count is found by numbers, a claim only by the thing that stopped being true".  T10's sweep obeyed that and still missed §5's paragraph, because **that line names no retired name: it states a COUNT**.  The complete rule is therefore two-sided: *after any RETIREMENT grep the retired names, and after any DISCHARGE grep the residual COUNTS too* — the number words and the digits (`TWO`/`THREE`/`FOUR`, "equations", "fields", "arms"), not only the identifiers.  A discharge and a retirement leave different fingerprints, and a sweep that looks for only one of them finds only one of them.  *** (THE CELLCP3 WINDOW PROVED THIS RULE BY BREAKING IT — record it here, where the rule lives.)  The window's own sweep grepped the RETIRED NAME (`cellCp3`) across eleven files and reported them all true.  The final review then found **11 live falsehoods in 4 of those same eleven files** — every one of them a COUNT and not a name: "FOUR parameters" (×3 in `LiveFSim`), "Three premises come from the record" (`LivenessProof`), "SEVEN-equation residual" (`LiveStableOffer`), a second "WHAT REMAINS" with a live 2,250-3,110 band (`STABR_STATUS` §1) contradicting this file's own headline.  So: **the count half is the half that matters after a DISCHARGE, and it is the half that gets skipped** — because a discharge retires no name, it only changes a number.  Grep the number WORDS (`ONE`/`TWO`/`THREE`/`FOUR`/`SEVEN`) and the nouns they count ("parameters", "premises", "fields", "equations", "arms"), and grep "WHAT REMAINS" and any live cost band, EVERY time.  A `SUPERSEDED IN PLACE` marker aimed at the wrong correction is WORSE than none: it reads as audited-and-current. ***  |

  There is **no (P2″) any more**: the leg's WHOLE channel invariant
  (`LiveChanInv.ChanLeg` = `ChanUp × ChanDn`) is CARRIED by the FSim's `Rel`
  (`LiveChanJoin`, hop-parametric arms, all five step classes, on grants #7/#8 plus the
  grant-free node-D re-mirror of task 5).

  **EIGHT of the twelve `InFlightOpen` facts are THEOREMS** — the four cell positions
  (`LiveChanInv` §7) and the four server positions (`LiveSrvOpen` §2) at both legs —
  and **ALL EIGHT are PREMISE-FREE**, off the carried invariant.  "Premise-free", not
  "unconditional": all four io fields still carry the leg's own link-unbrokenness
  antecedent, which is intrinsic to the `InFlightOpen` field type.  The remaining four
  (the two relay-driver tails at both legs) are theorems OUTRIGHT (SUPERSEDED IN PLACE: this
  read "theorems modulo (P3′)", a pre-existing T12 miss — both residual fields are retired and
  `CSAt`/`BFAt` are `⊤` at all seventeen shapes).  `LivenessProof.ifo-of` builds both records; `ifoBD`/`ifoCD`
  are gone from `Premises`.  FIVE of the original eight `LiveFSim` families are also
  THEOREMS — (P4) at the route close and (P5)–(P8) in the Tier-1 campaign (§3);
- `livenessDivFree : ∀ (b : Block₃) → DivergenceFree (breakableSystemOf b ∖ hidden b)`
  (`LivenessProof.agda:601-602`; `:408-409` was a pre-window reading) — **PREMISE-FREE**, and **UNCHANGED by the Tier-1 campaign** (it never
  depended on (P5)–(P8) and does not depend on (P1)–(P3)).
  The real broken four-node diamond, hidden, never livelocks. This is the route's
  first unconditional result about the real system; its only inputs are `sysBisim`
  and the now-discharged lexicographic descent.
  **PREMISE-FREE IS NOT POSTULATE-FREE** (say both in any publication): no premise
  family of §1/§3 enters this headline, but its term path does consume ONE of the
  two sanctioned dne-certified König seams — `DRCongruence.modA-transfer`, through
  `cong-∖`'s `div→`. The other, `DRImpliesFD.¬-divergent→normal`, is NOT on this
  path: it enters only the conditional headline, via `drbisim→⊑FD` in `abs⊑sys`.

**Goal:** `LivenessSpec = ∀ b → LSpec b true true ⊑FD (breakableSystemOf b ∖ hidden b)`
(`CSP_Refinement/Spec.lagda.md`, "THE SPECIFICATION" section) — the CSP failures–divergences
counterpart of the LTL route's completed `BlockLiveness⁺`. Route (the hybrid design,
`docs/superpowers/specs/2026-08-06-liveness-via-abstractSystem-design.md`): the banked 0-postulate
`sysBisim : breakableSystem blkA ≈DR abstractSystem blkA` replaces the real system by the τ-free
abstraction; ONE `FSim` witness (`Semantics/BisimFromRel.agda`, `FSimFromRel`: `fwdE`/`fwdT`/
`stabR`/`ndivL`) discharges the refinement against it; the transport chain
`cong-∖` → `drbisim-sym` → `drbisim→⊑FD` → `⊑FD-trans` carries it back.

---

## 0. THE CROSS-NODE API CAMPAIGN — CLOSED (T12).  `Premises = {cellCp3}` ALONE.
### (SUPERSEDED BY THE CELLCP3 WINDOW: `Premises = {}`.  See the FINAL TRUTH block at the top.)

*** THE END STATE, IN ONE RECORD. ***

```agda
record Premises : Set₁ where
  field
    -- (P1) the cell/reader alignment
    cellCp3 : (l : TwoLegs) (b : Block₃) (r : RState) → LS.CellCp3 l b r
```

That is the whole of it: `LivenessProof.At.Premises` has ONE field (ZERO since the cellCp3 window).  `csRes` was retired at
T8c-iii and `bfRes` at this close, and no third field has existed since the task-4 restructure.
`livenessSpec`'s DEFINITION never changed to get there — md5 `cbbbb200b6aea165f0a43b62c6b6f97c`
at the campaign base `0d775bb`, at `f68f1e4`, at `558ded7` and at the close, verified through
`cat -A` — so each retirement made the theorem's STATEMENT strictly stronger at an unchanged
term.  Say it that way round.

**ALL NINE API CO-POSITION EQUATIONS ARE DISCHARGED**, and `LiveRelayCS.CSAt` and `.BFAt` are
now `⊤` at all seventeen `CPPh` shapes (7 `ConsPh` + 10 `ProdPh`), with `csAt-triv`/`bfAt-triv`
and `csResidual-triv`/`bfResidual-triv` the proofs:

| arm | task | route |
|---|---|---|
| `pp4` | T1 | `LiveDrvBF.DrvCp` clause, carried as `LegJointU`'s FIFTH factor (S1) |
| `pp5` | T2 | ditto + the `bsWsb` stability refutation (`LiveSrvOpen.srvWsb-⊥`) — a REGION arm |
| `pp1` | T5 | ditto, on grant #11's server half |
| `pp2` | T6d | ditto + the `csWar` refutation (`csWar-⊥`) off the CS channel invariant — a REGION arm |
| `cp5` | T7 | ditto, the only CONSUME-side discharge and the only CLIENT co-party |
| `cp6`/`pp0` | T8c-iii | DERIVED at `LiveRelayCS` §3 from the carried `LiveDrvCSD.DnJoint` (SEVENTH factor) + the bundled `CsIdleExcl` — the first pair whose equation could NOT move into `DrvCp` |
| `cp4` | T10 | DERIVED at §2c from the carried `LiveDrvBFA.UpJoint` (EIGHTH factor) + the token's own level computation |
| `pp3` | T11h | DERIVED at §3's per-phase `Sharp` from the carried `LiveDrvBFD.BFFresh` (the FIFTH factor's THIRD half) through `areq-of⁺⁺` — the last of the nine, and the only Σ-shaped equation |

**THE OWNER GRANTS THE CAMPAIGN ASKED FOR, AND WHAT EACH COST:**

- **#10 — DECLINED**, on the campaign's own spike (T3).  The object was measured
  LAYER-INDIFFERENT (identical bodies green in either layer), the one real sync surface — the
  123-160-line bundle peel mirror — is paid identically either way, and the "LTL reuse"
  justification measured EMPTY (grant #8's LTL rows have zero LTL consumers).  Declining it
  deleted T6's io-row line item outright: net **−275 to −830**.
- **#11 — `PipeNodeIoEvo`'s fourth fact family.**  The **server half** landed at T5 for **40
  net** against a 90-125 band and unblocked four of five arms' preservation.  The **client
  half** was deliberately left unbuilt (no consumer until `cp5`), and the verified need then
  proved BROADER than the deferral had priced — the client family plus node A's and node D's
  own peel slots — so it was subsumed by #12 rather than exercised as asked.
- **#12 — the io cone's CS client family, FULL LEG** (not Dn-only): **≈297 net** against
  260-490.  It serves `pp2`, `cp5`, `cp6` and `pp0` at once, which is why it was priced once.
  Inside it, `csNoBoth` came in at ~48 against 110-230 by GENERALISING grant #7's predicates
  over `(id : IDs)` — sixteen witnesses implicitly, NO clause body changed, and `csNoBoth`
  VANISHED as a premise.  Verified STRICT at the diff level by review.

**THE MEASURED TOTAL:** **≈11,256 net non-comment lines over 104 commits** (`d593b31..HEAD`,
counting the close), against a 13,000 cap.  (T11h's wiring commit measured 30, not the 27 the
ledger's running figure assumed; item `b105c47` measured 181 exactly; T12 itself is a NET
DELETION.)  *** (CORRECTED at the post-close fix round: this read "≈11,771 net over **137
commits** (`0d775bb..HEAD`)" — a range that starts at the PREDECESSOR campaign's base and
measures **15,685** net, so the figure and the range never described the same thing.  ≈11,256 is
this campaign's own net over its own range.) ***

*** WHAT REMAINS — NOTHING.  See the FINAL TRUTH block at the top of this file, which is the
one authoritative answer; this paragraph is HISTORY. ***  (SUPERSEDED IN PLACE at the cellCp3
window: it read "`cellCp3`, and the priced route to it: the **monotone creation-only window,
2,250-3,110** (§3 item 3; templates parked).  It is the last premise … and it is the whole of
the remaining work".  BOTH the premise and the band are gone: the window was funded and closed
for **315 net** by a different route — the carried join, not the monotone one — and `cellCp3`
is a theorem, `LiveChanJoin.cellCp3-of`.  A live cost band in a "what remains" paragraph is the
worst kind of stale line, because it reads as funded work; there is exactly ONE "WHAT REMAINS"
in this file now and it is the top block's.)  `livenessDivFree` never depended on it.

---

## 1. THE HEADLINE, STATED HONESTLY

**`stabR` is a theorem**, in `CSP_Refinement/LiveStableOffer.agda`:

```
stabR-final : (r : RState)
            → LA.LegJointB legBD (toSys r)
            → InFlightOpen legBD r → InFlightOpen legCD r
            → StabOffer r
```

**Never quote this without its premises** (the module header says the same):

- **Proved outright:** the spec-side settle (`posIdle`/`posDone` with trivial containment); the
  ENTIRE offer half — parked-at-D forces the kept receive `apiBF (exit i) hi recvBFBlock · blkA`
  through both parallel operands and both hides (`delivObl-parked`, `stabOffer-parked`); the block
  pin (the `PipeVal` component joined to the fold); the ten-way position dispatch; the
  `lpUpClient` progress arm on both legs.
- **`InFlightOpen` — 8 of 12 PROVED (campaign 10).** `stabR-final` still TAKES the two records,
  but they are no longer premises: `LivenessProof.ifo-of` BUILDS them.
  - the four **cell** positions (`oUpCell`/`oDnCell`, both legs) — `LiveChanInv.cellOpen-up-chan`/
    `-dn-chan`, off the hop's `ChanInv` + the carried `NoTwoTokens`;
  - the four **server** positions (`oUpSrv`/`oDnSrv`, both legs) — `LiveSrvOpen.srvOpen-up`/`-dn`,
    off the same two objects through `chanInv⇒h19`'s three-armed dispatch;
  - the four **relay-driver** positions (`oRelayIn`/`oRelayOut`, both legs) —
    `LiveRelayCS.relayOpen-in-s′`/`-out-s′`, now **UNCONDITIONAL** theorems — the residual is
    **ZERO** equations (T11h).  All nine arms are discharged: `pp4` at T1, `pp5` at T2, `pp1` at
    T5, `pp2` at T6d, `cp5` at T7, `cp6`/`pp0` at T8c-iii, `cp4` at T10 and `pp3` at T11h — the
    last off the CARRIED `LiveDrvBFD.BFFresh` (`LiveChanJoin`'s fifth factor's third half) through
    `areq-of⁺⁺` and §3's own `Sharp`; `LiveRelayCS.BFAt` and `.CSAt` are `⊤` at all seventeen
    shapes, with `bfAt-triv`/`csAt-triv` the proofs.  (This read "**TWO**-equation residual … BOTH
    that remain are CROSS-NODE BlockFetch arms" — a PRE-EXISTING staleness of one arm, T10's `cp4`
    never having been swept here, corrected at T11h with the sweep-both-or-neither rule.)  The two
    facts still take the CARRIED `LiveDrvBF.DrvBF` beside the freshness clause. **Since T2 they also take the leg's DOWN-link unbrokenness** — `pp5`'s
    discharge closes its `bsWsb` half by exhibiting a MEDIUM move (`LiveSrvOpen.srvWsb-⊥`), so the
    two api fields are no longer antecedent-free; `parked-at` forwards `hb2` to them.  **State the
    strength of that exactly:** what is CHECKED is that both arms of the sharpening consume the
    unbrokenness hypothesis (and F21 shows the leg's OWN link is the one that licenses the move);
    what is NOT checked is a WITNESS.  **This caveat covers EVERY REGION arm's sharpening, and
    there are now two** (T6d review I-2): no stable `(pp5, bsWsb)` state at a broken link has been
    constructed, and none has been constructed for `(pp2, csWar)` either — `LiveSrvOpen.csWar-⊥`
    (`:470-484`) has `srvWsb-⊥`'s shape exactly (`broken … ≡ false → ChanCSDn → pin → isStable → ⊥`,
    discharged by exhibiting a medium move `srvSendMoveCS-at-⊥` or a medium τ-move `medτMove-⊥`
    through `chanCSDn-war`'s `CellPreQCS` split), so both antecedents rest on
    unprovability-as-unguarded, not on a refutation.  A THIRD region arm would inherit the same
    caveat; state it generically, not per-arm.
  All four io fields carry the leg's own **link-unbrokenness antecedent**, and that is mandatory,
  not stylistic: a broken link's medium is `Skip` and offers nothing, and unbrokenness is provably
  not invariant-carryable (a `break` is visible and every preserved conjunct transports across it).
  `parked-of` forwards the obligated window's `wLink1`/`wLink2` into the fields.
- **Premised: NOTHING (the cellCp3 window).**  *** This bullet's own claim is superseded, not
  merely its history: `cellCp3` is a THEOREM (`LiveChanJoin.cellCp3-of`) and
  `LivenessProof.At.Premises` is an EMPTY record. ***  What it read, kept as history:
  "**Premised: `cellCp3` ALONE** (since the TokenExcl campaign) — the cell/reader alignment in its
  conditional form `CellFull⁺ b → RelayPre → RelayCp3`, riding only the invariant transport.
  Nothing about the channel: BOTH hops' invariants are CARRIED by the FSim's `Rel`
  (`LiveChanJoin`, task 5).  Nothing about the api residual either: `csRes` was retired at
  T8c-iii and `bfRes` at the T12 close.  (SUPERSEDED IN PLACE: this bullet read "the api residual
  `bfRes` (P3′) alone since T8c-iii" and listed `cellCp3` as a second, "also premised" item.)

**And nothing else.** Everything the earlier records listed beside them ((P4) `noDivH`,
(P5) `noRetA`, (P6) `brkBits`, (P7) `prodLands`, (P8) `recvLands`) is a theorem, proved and
consumed by name; see §3 for the supplier of each.  Note the shape of the campaign-10 trade: the
twelve independent position facts became ONE invariant with a complete preservation calculus plus
the api residual's co-position equations — of which *** ZERO REMAIN *** (nine before T1's `pp4`, T2's `pp5`, T5's `pp1`, T6d's `pp2`, T7's `cp5`, T8c-iii's `cp6`/`pp0`, T10's `cp4` and T11h's `pp3`), so the trade's second half has been paid off entirely and `ifo-of` takes NO premise application at all.  <<< THIS READ "**TWO** co-position equations … TWO scoped premise applications, two fields × two legs" AND ENUMERATED THE DISCHARGES ONLY TO T8c-iii: FALSE SINCE T10 (`cp4`), and false about the field count since T8c-iii retired `csRes`.  Corrected in T10's fix round; the T10 sweep missed it because **the line names no retired name** — see the rule below. >>> — and the invariant was the kind of
object that *can* be discharged by an assembly join, which none of the twelve ever was.  Task 5
cashed that in: the join now carries the whole invariant and the trade's invariant half is PAID.

## 2. DELIVERED (eleven campaigns, 229 commits `af5d964..HEAD` counting the cross-node api close commit — **125** at the InFlightOpen close (`af5d964..d593b31`) plus the cross-node api campaign's **104** (`d593b31..HEAD`) — every instalment adversarially reviewed)

| Campaign | Modules / theorems | Budget |
|---|---|---|
| Phase 1 | gate verdict (b); `Semantics/FDFromF.agda` (`⊑F→⊑FD-df`, constructive); `LiveSpecCouple.agda` (`SpecPos`/`specPos`/`SpecOf`, flag lemmas, 15 spec-side weak transitions); `LiveNoDivH.agda` (`ndivL`: divergence-freedom of `abstractSystem ∖ hidden` by lexicographic `(μTot,μτ)` descent; 5 `Descent` parameters, all verified dischargeable) | — |
| Tasks 1–3 | `LiveLegInv.agda` (`LegPos` 10 positions; payload-pinned `AtPos`; drain-safe `CellFullBlk`; `phantom-gap` = the machine-checked two-sided contrast with `PipeInv⁺`); `LiveLegStep.agda` (all six preservation arms; hops 4+9 discharged; 9/11 leaves proved) | 4,396/4,500 |
| TokenExcl | `LiveTokenExcl.agda` — `NoTwoTokens` was machine-checked **FALSE as stated** (draining-inclusive cells), fixed by the C1 pattern, now **unconditional**; parked `UpChainCp3`/`DnChainCp3` as the window templates | 1,525/2,100 net |
| Assembly | `LiveLegApiCone.agda`/`LiveLegIoCone.agda` (the ⁺ cones; `driverExpose⁺` applied, `VisLeaves` proved not premised); `LiveLegAssembly.agda` — `legJoint-step` at `RState` for `LegJoint⁺ = (PipeInvS × LegInv × TokenExcl) × PipeVal` (*era-scoped row: since (P5), `LegJoint⁺` also carries the trailing `KAcFrz` factor — see §5*); both-legs `LegJointB` by delta-convertibility | ~950/1,030 |
| LiveStableOffer | `LiveStableOffer.agda` — `stabR-final` as in §1 | 2,278/2,500 |
| LivenessProof | `LiveNoDivH.agda` re-engined (the ANCHORED lex measure); `LiveHeavyFacts.agda` (`Descent` discharged at SIX banked walk facts — five by naming, `hidEv-μ`'s 16-clause event split mirroring `WalkDeliver:153-270`); `LivenessProof.agda` (the transport + both headlines above) | 3 commits, ≈4.5 min of agda |
| LiveFSim | `LiveFSim.agda` — the `FSim` witness ASSEMBLED: `Rel = (r , LegJointB (toSys r))` + the `specPos` coupling into `FSimFromRel`; all four obligations discharged (`fwdT` 16/16 labels; `fwdE` 23-clause dispatch, all five kept classes + the `√` arm; `stabR` = `stabR-final`; `ndivL` = `noDivH`), concluding `Sim.Assemble.lspec-fd : LSpec blkA true true ⊑FD (abstractSystem ∖ hidden blkA)`. Closed the campaign at EIGHT module parameters, with (P5)-(P8) chartered rather than funded — that charter was then funded and paid in full by the Tier-1 campaign below | 1,850/2,000 |
| **Tier-1 premise discharge** | **(P5)–(P8) ALL BECAME THEOREMS**; `Sim`'s telescope 8 → **4** parameters (`module Sim` at `LiveFSim.agda:1240`, its parameter block `:1244-1286`: `cellCp3` `:1244`, `ifoBD` `:1275`, `ifoCD` `:1276`, `noDivH` `:1286` — re-derived at the post-close fix round, the old `:1211`/`:1215-1252` having drifted ~30), `Premises` 7 → **3** fields at that close (ONE, `cellCp3`, since T12) (campaign 10 restructured them — four fields at its first close, then THREE at its final one, the channel invariant having left the record for the FSim's `Rel`, §1). (P6) `brkBits` — `PES.break-invert` widened to carry the `broken`-bit update it always built, discharged at `LiveFSim` §A4 (`:1094`) through the pointwise `LiveSpecCouple.specPos-break′` (the whole-map form needs funext, absent from `src/`). (P7) `prodLands` — the ⁺ cone now KEEPS the generic `SrvLands` and exports node A's fired-link pin, §A5 (`:1134`), no base module touched. (P8) `recvLands` — `PipeEvDriverCone.NodeDDrv` carries the firing consume-driver's own step, off which both the `cp3` gate and the fired link follow inside `LiveLegApiCone`, §A6 (`:1166`). (P5) `noRetA` — NEW modules `LiveRetFree.agda` + `LiveKAFrozen.agda` (grant #6), consumed by `sqrt-⊥` (`:1388-1391`) | ≈624 net/1,100 |

| **InFlightOpen completion** (campaign 10) | **8 of the 12 facts became PREMISE-FREE THEOREMS.** NEW modules: `LiveIoIntro.agda` (the io intro ladders + `medOfferOut`), `LiveCellOpen.agda` (the four cell facts), `LiveChanRead.agda` + `LiveChanInv.agda` (**the payload-generic per-hop CHANNEL INVARIANT** — five clauses on one hop's three abstract components, seven per-class preservation lemmas, 21 machine-checked adjacency rows with row PRODUCERS, `ChanLeg` = base + frame + preservation, and `CellRdy` discharged as a corollary), `LiveSrvOpen.agda` (the four server facts, off `chanInv⇒h19`), `LiveRelayOpen.agda` (the whole api ladder + all NINE per-sub-phase arm theorems + the two TOTAL `CPPh` dispatches), `LiveRelayCS.agda` (the residual SPLIT by protocol, proved exact at all 17 shapes). `LiveStableOffer`'s four io fields gained the link antecedent; and `LiveChanJoin.agda` — **THE JOIN**, which threads the whole `ChanLeg` along a run: hop-parametric arms (`module HopArm`, one copy of the api arm's 21-clause label dispatch and of the four row-refutation tables, instantiated at each hop) for all five step classes, carried as a TRAILING factor of `LegJoint⁺`.  `LivenessProof.Premises` = `{cellCp3, csRes, bfRes}` (it read `chanLeg`, then `chanDn`, before the join reached both hops). Machine-checked NEGATIVE results, each of which killed a cheaper plan: `CellRdy` has no invariant-carryable widening (two counter-states, one banked in `LTL/Evidence/PipeCellFalse`); the un-gated "a full cell's payload is accepted by its reader" is FALSE; `cp4`'s api arm is FALSE as a state invariant (hence the `isStable` scoping); and the BF half of the residual does NOT come out of `ChanLeg` (eight refutation lemmas — every `ChanInv` field runs server-or-cell ⇒ client, or cell ⇒ server-REGION (`cvBlk : BlkFull ph → SrvStr sa`, and `cvQui` contrapositively), so no reading yields a server POSITION at `pp3`/`pp4`/`pp5`) | **measured 4,934 added / 505 removed / net 4,429** non-comment `.agda` lines over `60f0f64~1..HEAD`; the earlier ≈4,230 was the per-task ADDED sum, within 4.5% of net. Basis from here on: MEASURED NET. Cap 7,000 (final-review M-7) |

LTL base modules touched across the whole route: **four** — `PipeValRelay` (grant #2),
`PipeNodeIoEvo` (grants #1 and #6), `PipeEvStep` (grant #4) and `PipeEvDriverCone` (grant #5) —
plus mechanical consumer threading (`PipeValEvStep`'s binder rows). Grant #3 (`PipeBundleEvo`) was
returned UNEXERCISED: the sibling-grep found an already-abstract cascade. **Campaign 10 ended up touching FOUR
more** at its close, on grants #7 and #8, both EXERCISED: `PipeBundleEvo` (#8 — the three api decodes
report the fired coarse row), `PipeCliIoDec`/`PipeSrvIoDec` (#7 — the four io decodes do) and
`PipeNodeIoEvo` again (#7 — the ownership mirrors). The route's LTL base total is therefore **seven
GRANT-TOUCHED modules**; the count of LTL *files edited* across `af5d964..HEAD` is **eight**, the
eighth being `PipeValEvStep`, whose binder rows are the mechanical consumer threading disclosed one
sentence above (final-review M-8). Grant #3 (`PipeBundleEvo`, offered earlier for a different slot) stays returned
unexercised; grant #8 later took that module for the api rows.
**T3b NOTE on #7/#8:** both were justified on a sentence later found to conflate the FINE and COARSE
levels, and were therefore **AVOIDABLE as scoped** — record-material only, with no implication for
the landed code. The full statement is in §3's grant record, under "RETROACTIVE NOTE (T3b)"; the
corrected doctrine is §5's coarse-ROW bullet (`:505`, NOT §5's first bullet, which is the relay
sub-phase coverage lesson).

**LEDGER NOTE (task-4b I-3) — grant #7 was exercised with one extension beyond "strict trailing".**
The six io-decode widenings are strictly trailing with the originals re-derived as projection
wrappers (zero forced consumer churn — `PipeBundleIoEvo`, `LiveLegInv` and `LiveLegStep` were not
edited). The extension is in `PipeNodeIoEvo`: `IoFacts.cRefl`/`sRefl`'s PREMISES were widened
**in place** (`NoCliReadAt` → `NoCliIoAt`, `NoSrvWriteAt` → `NoSrvIoAt`, each the pair with a new
transposed mirror), and the eight per-node no-fire lemmas' conclusions with them. It is grant #1's
own pattern at grant #1's own two fields, monotone-safe (weakening a record field's premise
strengthens no instance obligation; the frozen `facts₀` classifiers ignore it, which is why
`PipeTauIo`/`PipeValTauIo` saw no change) and it is LOAD-BEARING, not tidying: without the mirrors
the io arms' case "the cell filled while BOTH hop peers stayed fixed" is unrefutable, and `ChanInv`'s
`cvReq` is genuinely FALSE at such a state. Recorded here because two frozen-module field types moved
outside the grant's letter.
**OWNER SIGN-OFF, 2026-08-19 (batched decisions):** the extension is *** APPROVED RETROACTIVELY ***
and stands as exercised — recorded as grant #7's second exercise, in grant #1's own pattern
(load-bearing, monotone-safe, same module and same two fields). This line IS the repo's record of
that approval: the working decision ledger lives in untracked `.superpowers/`, so without it the
tree would show an in-place base-module widening with approval pending. The in-place surface is
**ten definitions** — the two `IoFacts` record fields `cRefl`/`sRefl` plus the eight per-node
no-fire lemmas forced to return the pair — where the campaign's summaries say "the two OWNERSHIP
MIRRORS" (a summary/detail mismatch, not a concealment: the paragraph above already names the eight).

Every exercise on the route is a
strict in-place generalisation with the original re-derived as a literal instance (grant #6 left
`top-nodes-io-evo`'s type byte-identical, and #7/#8's projection wrappers are byte-identical in type,
so their consumers were untouched) and the full LTL
endpoint `LTL/BlockLiveness.agda` verified green at EXIT=0 BEFORE each base commit landed.

## 3. THE PREMISE AUDIT — what is a theorem (ALL OF IT, since the cellCp3 window; this heading read "and WHAT REMAINS to `LivenessSpec`", and the answer is NOTHING — the one authoritative "what remains" is the FINAL TRUTH block at the top)

**`LiveFSim` is COMPLETE** (campaign 7) **and its premise block is down to THREE parameters, NONE
of which is a premise** (campaign 9 got it to four; the cellCp3 window removed (P1)).
`Sim.Assemble.lspec-fd : LSpec blkA true true ⊑FD (abstractSystem ∖ hidden blkA)` is
assembled with NO obligation left as a parameter. The audit, exactly — the **three**
parameters of `Sim` (`module Sim` at `LiveFSim.agda:1250`, parameters at `:1291`, `:1292`,
`:1302`), and there is nothing left to warn about: `ifoBD`/`ifoCD` are applications of the
CARRIED join and `noDivH` is a theorem.  *** (SUPERSEDED IN PLACE, and the previous marker on
this section corrected only the pre-T12 field count while leaving the telescope at FOUR and all
four anchors drifted: it read "down to four parameters", "the **four** parameters of `Sim`
(`module Sim` at `LiveFSim.agda:1240`, parameter block `:1244-1286`)", "(never quote the
conclusion without them)", and a `cellCp3` parameter at `:1244` that no longer exists.) ***

- **(P1)** `cellCp3` — *** GONE FROM THE TELESCOPE (the cellCp3 window). ***  Discharged inside
  `LiveChanJoin`'s own io READ arm off §5e's `cellCp3-of`, so it never reaches here.
  · **(P2)/(P3)** `InFlightOpen` at both legs (`:1291-1292`) — since
  campaign 10 these two parameters take the CARRIED `LegJointB` at the config they answer about
  (`NoTwoTokens` is a proved conjunct of it) and are SUPPLIED by `LivenessProof.ifo-of`
  which builds both records from `Premises`' ONE field plus the CARRIED channel invariant (T12: from
  the CARRIED invariant ALONE at the two api fields, `ifo-of` having lost its last `Premises`
  argument); so what reaches `livenessSpec`'s type is (P1) and nothing else, never the twelve facts.
  (SUPERSEDED IN PLACE: this read "`Premises`' three fields" and "(P1) + (P3′)".)
- **(P4)** `noDivH` (`:1286`) — a THEOREM of `LiveNoDivH.Descent` (6 parameters, discharged at
  `LiveHeavyFacts`' six banked walk facts), taken abstractly here so this module's closure stays
  off the heavy `LTL/Walk/*` suffix; `LivenessProof` passes it by name, so it is NOT a field of
  `Premises`.

**DISCHARGED IN THE TIER-1 CAMPAIGN — (P5)–(P8) are theorems, none of them a parameter anywhere:**

- **(P5)** `noRetA` — "no reachable config whose joint invariant holds forces to `ret`". The
  charted `LegPos` dispatch was machine-refuted (`lpDone ∧ cp6` survives it: the escape state was
  BUILT explicitly, with all five `LegJointB` components discharged while `force (absDec s) ≡ ret`),
  the second blocked-on-content diagnosis of the effort to survive adversarial re-derivation. The
  real refutation is peer INERTNESS: `LiveKAFrozen.agda` states the freeze `KAcAtHead ip = kac ip ≡
  kcHead KA.stClient` (`:124-125`) and the conjunct `KAcFrz s` at node B's link-AB KA client
  (`:277-278`), and transcribes `SysIoLink6`'s two-rung KA peel with the fact riding along
  (**KEEP-IN-SYNC vs `R2_Bisim/SysIoLink6:644-760`** — datatype `:644-656`, finisher bodies
  `:658-697`, the peel's first two rungs `:699-714`, and `:715-760` deliberately COLLAPSED into
  `kaTail-abs-noKA`; the marker at `LiveKAFrozen.agda:27-67` also records the transcription's two
  intended deviations, a STRENGTHENED premise (`IsKAoff`) and a WEAKENED conclusion (`KAFire`'s
  unpinned `ip′`), and a third sync surface, the hand-built `Tkac`.  The transcription exists because
  `absBundleKA-ev-prod` drops the moved peer's step and only the step refutes a frozen fire);
  `LiveRetFree.agda` then proves `absDec-noRet`/`radec-noRet` (`:166-178`) = 8 `SysSqrt` rungs +
  `tableSpec-ret-fin` + one absurdity, with `noRetA-lit` (`:184-186`) at the LITERAL premise type.
  `KAcFrz` joins `LegJoint⁺` as a TRAILING conjunct, so `LegJointB`'s type and the `Rel` are
  untouched. Consumed by `sqrt-⊥` (`LiveFSim.agda:1388-1391`, in §4 from `:1321`) — the `√` arm
  that would otherwise falsify the refinement;
- **(P6)/(P7)/(P8)** `brkBits`/`prodLands`/`recvLands` — the three KEPT-CLASS SUCCESSOR facts:
  component equations at the invariant arm's own successor which the two inversions BUILT and then
  projected away (`break-invert` kept the cell phases but dropped the `broken` update;
  `driverExpose⁺` decided which driver fired, then reported a four-arm disjunction whose `ldFix`
  arm fits every label). The recorded reason no consumer could recover them DOWNSTREAM stands
  for these two objects — the peels do not reduce for a variable step, and no FINE decode is
  injective (era-scoped at T3b: the sentence was written before coarse-position injectivity was
  derived, and it was never about a coarse row — `break-invert`'s `broken` update and
  `driverExpose⁺`'s driver disjunction are not table rows) — and is
  exactly why the fix had to be the WIDENING, which is what was done: each inversion now returns
  what it already computed, as a strict trailing field. Sites: §A4 (`:1094`), §A5 (`:1134`),
  §A6 (`:1166`).

Method notes worth keeping: `broken-upd` vs `brkSet` needs funext (absent), dodged by the
POINTWISE restatement `LiveSpecCouple.specPos-break′`; grant #5 was exercised SMALLER than granted
(the firing consume-driver's step subsumes both requested facts, and the `cp3` gate came from a new
table inversion in the NON-frozen `LiveLegApiCone`); every new slot of `driverExpose⁺` was APPENDED
so that `proj₁` stayed slot 1 and no consumer's positional access shifted, leaving a Σ chain that
grew to 21 components across grants #8 and task 5, and to **23** across T1 and T2
(`driverExpose⁺`'s signature).
*** THE RECORD-CONVERSION DEBT: PAID AT T3b. ***
The debt was booked at "17 slots × 8 destructuring sites; re-open on further widening OR the first
middle-slot consumer", and by T2 BOTH disjuncts were met (**23 slots × 12 destructuring sites**,
+6 type-level; `LiveChanJoin`'s api arm counted past FIFTEEN anonymous slots — positions 3-17 — to
reach the four row pairs, and `LiveLegAssembly`'s two `evStepB-api-at` clauses read interior slot 17). Two reviewers
called the conversion overdue (task-1 review M-6, task-2 report). **T3b converted it**:
`driverExpose⁺` now returns the record `DriverExposed⁺` with 23 NAMED fields
(`deSucc`/`deMed`/`deProc`/`deRun`, the two `deLd*`, `deSrv*`, `deVl*`, `deLv*`, `dePl*`, `deRl*`,
`deFrzB`, the four `deRows*` and T1's two `deDnDrv*`); the six clause bodies construct it with
`record { … }`, and all twelve reading sites read by name. **The mis-bind class is closed**: a
reader now has to NAME the slot it wants, so no insertion can silently shift it and no wildcard can
absorb the shift. The property given up is the one that made the mis-bind ABSORBABLE — a reader
could take a positional PREFIX without naming the tail — and it is given up deliberately.
**What the record buys, stated exactly (T3b, corrected at review).** Two things, and *not* a third:
(i) **UNCONDITIONALITY** — every wrong-field read is a type error *somewhere*, with no
type-coincidence escape and no wildcard able to absorb a shift; and (ii) a **by-NAME audit trail** at
the read site, so the intended slot is on the page. It does **NOT** buy error LOCALITY: falsification
F22, run in the RECORD form, mutated `LiveChanJoin:924` and was reported at `:941` — seventeen lines
away, inside the `_`-typed `rowsUp` selector — exactly the non-locality the `Σ` had. Locality still
fails wherever the value passes through an inferred-type helper.
**And two corrections to the debt's own wording.** The task-1 review said an insertion was
"undetectable at eleven of twelve" sites; T3b narrowed that to "silence CONDITIONAL on adjacent-slot
type coincidence, non-local always", and the review then **exhausted all 22 adjacencies of the
23-slot `Σ` and found NO convertible pair** — so silence needed not a pure shift but a
type-DUPLICATING insertion, which is precisely T4's shape (a CS `VisLeaves⁺`- or CS row-pair-typed
slot placed before its BF twin). The narrowing must therefore not be read as "the `Σ` was safe".
Second: a well-typed mis-bind of a PROOF slot could never have weakened a stated theorem (consumers'
signatures are explicit, so the mis-bound witness still had to discharge the stated goal); the only
slot whose mis-binding changes meaning at unchanged type is the DATA slot `deSucc`, which is position
1, never shifted by an append, and pinned by the §D probes. The conversion's value is auditability
and insertion safety, not closing an unsoundness.
The stated blocker did not materialise: the two `refl` tripwire probes in `LiveFSim` §D
(§4's risk 2) were **re-established against the record form unchanged** — `proj₁ (driverExpose⁺ …)`
became `deSucc (driverExpose⁺ …)`, both probes are still `refl`, and no `subst` entered any premise
site. The reason they hold is that a record projection of the same neutral application is the same
term the `Σ` projection was, so the conversion `toSys r′` ≡ the cone's own successor is still a
CONVERSION and not a theorem.
T3b also **SPLIT the file**: `LiveLegApiCone` keeps §1-§7 (the per-peer up-hop cone and the row
types, 1,489 code) and the new `LiveLegApiExpose` holds §8-§11 (node D's ⁺ re-mirror, `VisLeaves⁺`,
the two landings, `DriverExposed⁺`/`driverExpose⁺` and the three per-leg selectors, 707 code), one-
directionally, with `DnSrvDrv` left behind in the cone so `LiveDrvBF`'s import did not move. The new
module's copied import header was PRUNED at the fix round to what the assembly half actually names
(109 dead `using` entries, 18 imports removed outright), which is where the split's net cost went.

Also proved outright on the way, and reusable: the whole hidden-side flag layer (a hidden step
moves no reader of the coupling, including the produce-threshold refutation the driver layer
cannot see, taken on the SERVER layer instead), the kept-side co-leg gate (the same three-arm
server refutation with the hiddenness contradiction replaced by a LINK one, via two `Maybe
Link` label decoders), and `keptRecv⇒prod` off `LegInv`.

1. **`LivenessProof`** — ***DONE*** (campaign 8, three commits). Two corrections to the plan,
   both re-derived at source:
   - the chartered **`τreflect-lex` merge is NOT a ~40-line re-assembly** and was not built. The
     two banked halves agree on the `medτ` arm but call TWO DIFFERENT node cones on the `hidSync`
     arm (`WalkConvNodeDrop.top-nodes-io-abs-wt:1263` vs `WalkConvNodeFix.top-nodes-io-abs-fix:510`),
     each building its own successor `SysState` through its own 4×12 dispatch and projecting the
     other's payload away (the fix cone re-uses `absBundleG-io-prod-wt` and *discards its `drop`
     field*). No decode is injective, so merging needs a THIRD ~500-line cone. Instead
     `LiveNoDivH`'s descent was **ANCHORED**: `μA r rk = (μTot (toSys r) , μτ rk)` reads the trace
     measure at the anchor and the τ measure at the current config, carrying the τ-run between
     them; a τ step moves only `rk` (`τreflect`, verbatim) and a hidden visible step cashes the run
     in through `liftτ*-μ` (verbatim) — the STEP transports onto the measured config, so no state
     pairing is ever needed. `Descent`: 5 → 6 parameters, five now banked verbatim by name.
   - the build was **seconds, not minutes** (warm interfaces; one `Checking` line per new module).
2. **Tier-1 premise discharge** — ***DONE*** (campaign 9, eleven commits `101be5b..061d8e5`
   — re-derived and PINNED at the final review (M-3b): written as `101be5b..HEAD` it read 44 at the
   final close and rots by construction on every future commit
   including this close commit): (P5)–(P8) are
   theorems, `Premises` was at three fields at that close (campaign 10 then restructured it, §1).
   The former Tier-1 debt line ("`noRetA` 160–390 and
   the cone/`break-invert` widening 240–495, both outside any funded band") is **PAID** — actual
   spend ≈624 net lines against a 1,100 cap, on three owner grants (#4 `PipeEvStep`,
   #5 `PipeEvDriverCone`, #6 `PipeNodeIoEvo`).
3. **THE REMAINING ROUTE to an unconditional `livenessSpec` — ***DONE***, BOTH DEBTS PAID, THE
   HEADLINE IS UNCONDITIONAL.**  (SUPERSEDED IN PLACE: this read "after campaign 10 there are
   TWO debts (the conditional headline stays conditional until they are paid …)".)
   `livenessDivFree` never depended on either:
   - **`cellCp3` window — ***DONE*** for 315 net.**  The 2,250–3,110 monotone creation-only
     price is SUPERSEDED and the route taken was a different one: `LiveChanInv`'s `cvBlk`/`cvStr`
     for half one and two new carried members (`LiveDrvBFA.UpIdl`, `LiveDrvBFD.DnIdl`) for half
     two, composed at `LiveChanJoin` §5e.  No monotone window was ever built; the templates
     parked for it stay parked.
   - **the `ChanLeg` JOIN — ***DONE***, BOTH HOPS, NO PREMISE LEFT.**  Grants #7 and #8 made
     the io and api cones report the fired per-peer coarse ROW (the fact every decode
     computed and threw away, unrecoverable afterwards because abstract-position
     injectivity is FALSE), grant #7 also added the two OWNERSHIP MIRRORS without which
     a cell fill whose hop's peers both stayed fixed could not be refuted, and
     `LiveChanJoin` threads `ChanLeg` through all five step classes as a trailing factor
     of `LegJoint⁺` (the `KAcFrz` pattern), so the FSim's `Rel` carries it and all four
     cell/server facts are premise-free at both hops and both legs.

     *** RETROACTIVE NOTE (T3b, record-material, NO implication for the landed code). ***
     Grants #7 and #8 were justified on the sentence corrected in §5's coarse-ROW bullet (`:505`) — that the
     fired row is unrecoverable because position injectivity is FALSE. That sentence mixed the
     FINE and COARSE levels: at the coarse level the row IS recoverable post hoc, in 11 lines off
     two already-banked generic lemmas (T3's spike, machine-checked; confirmed by its adversarial
     verification, which also machine-checked that the cited `sil-collapse` evidence only ever
     supplies the diagonal instance). So **both grants were AVOIDABLE as scoped** — a row-recovery
     wrapper over the un-widened decodes would have needed no base edit at all. This is recorded,
     not acted on: the widenings are landed, sound, strictly trailing, and their consumers are
     byte-identical in type; re-doing them would buy nothing and cost the KEEP-IN-SYNC surface
     they removed. What it DOES change is the price of future asks — before requesting a decode
     widening, check coarse-position injectivity of the peer's table first (the standing
     support-distinctness review obligation on `NodeSpecs` is the cost of that route).

     *** HOW THE DOWN HOP WAS UNBLOCKED, GRANT-FREE (task 5). ***  The down hop's client is
     node D's, and node D's api peel was the frozen `PipeEvDriverCone.NodeDDrv`
     (`:203-260`), which reports only `(fixed) ⊎ (¬holding successor)` about the client it
     moves — no row, no successor identity — and a second peel cannot be tied to the frozen
     one (`absNodeD` is not injective).  The weak slot is inherited ONE LAYER DEEPER:
     `NodeDDrv`'s client field is fed verbatim from `PipeBundleEvo.BundleGEvR⁺`'s own client
     slot (`bgEB⁺` at `:940-946`, the client slot `:944` — `(bfc ≡ bfc′) ⊎ (BFcHasBlk bfc′ → ⊥)`; the
     server slot `:945` already carries `BfsSucc`.  *Anchor correction: the earlier records cited
     `:934-940`/`:938`/`:939` for these; the datatype is `:937-946` at HEAD*), and grant #8
     widened the api DECODES, not that datatype, which is matched at 28 sites across three
     modules (`PipeBundleEvo` 14, `PipeEvDriverCone` 8, `PipeNodeAEvo` 6); its SERVER slot
     already carries `BfsSucc`, so the CLIENT slot alone was the gap.  **The fix needed no
     base edit and no grant #9** (which the owner declined on the reviewer's recommendation):
     `LiveLegApiCone` §8 re-mirrors node D's api peel IN THE CSP LAYER — the same move §5-§7
     make for nodes A, B and C — calling the landed `decBFc-apiBF-succ-row⁺` through
     `absBundleG-api-evo⁺` and bypassing `BundleGEvR⁺` entirely, exactly as the api cone's
     own `bfEvRio→api` chain already did for the UP hops.  `driverExpose⁺` then gained the two
     DOWN-hop row pairs; the down hop's SERVER rows were already produced by §7's node-B/C
     peels and discarded, and the io cone's `AllSrvP`/`AllCliP` already reported all four
     peers (grant #7 stated them for the four peers at once), so only two selectors were
     missing there.

     *** AND THE DOWN JOIN WAS NOT A MIRROR. ***  The review's (iii) called `LiveChanJoin`
     §2-§5 per-LEG rather than per-HOP and priced the down hop as a ~470-line textual mirror
     (400-560) or a hop-parametric refactor (250-400).  The refactor was taken: `module HopArm`
     abstracts over the hop's link, its two peers, its cell and the cell-key bridge, and §5
     instantiates it twice, so the api arm's 21-clause label dispatch, the four
     row-refutation tables, the two key dichotomies, the payload-role split and the two
     ownership refutations exist ONCE for both hops.  A third hop would cost an instantiation
     line.  ACTUAL SPEND for the whole finish: **575 added non-comment code lines** against the
     funded band 400-660, and **net +222** after the refactor's de-duplication (353 removed).
     The de-dup delta is the headline: `LiveChanJoin` went from 540 to 591 code lines while
     going from ONE hop to TWO — the down hop cost **51 net lines there**, against the review's
     400-560 for the mirror — and `LiveLegApiCone` grew 1,605 → 1,777 for the node-D inversion
     plus the cone's two new row pairs (inside that slice's own 150-260 band).
   - **the api residual (P3′)**: NOT closable inside the relay. Three of the equations are
     CROSS-NODE — `cp4` needs node A's `MsgBatchDone` (upstream), `cp6`/`pp0` node D's CS client,
     `pp3` node D's second request — and `pp2` needs a ChainSync channel invariant (13×12 vs the
     BF one's 10×7, which cost 888 code) plus a CS-side io ladder (every banked ladder is
     `N2N_BlockFetch`-keyed). By-kind map: `pp4` is the cheap driver-tail twin, `pp5`'s two objects
     are both banked (`cvQui` + the T2c ladders + `srvOpen-dn`), `cp5`/`pp1` are one cheap
     driver-tail coupling. Owner decision: closed at the split, chartered as a future cross-node
     campaign.
   - **UPDATE (cross-node api campaign, T1, 2026-08-20)**: the by-kind map's "`pp4` is the cheap
     driver-tail twin" was RIGHT, and the arm is now a THEOREM — S1 (`LiveDrvBF`) is that
     driver-tail coupling, built and CARRIED (`LiveChanJoin`'s fifth trailing factor, all five
     step classes).  Spend: **355 net code lines** against the task's funded band 450-1,000, and
     `LiveFSim` needed NO edit at all.  Two of the same note's other claims are already known
     wrong: `pp5`'s "two objects both banked" is REFUTED on all three named objects (the campaign's
     gate + its adversarial verification), and `cp5`/`pp1` are blocked on a ChainSync ROW layer
     that no module in the tree has.  `bfRes` is a TWO-equation residual after T2 (three after T1).
     **(T10) ONE after the `cp4` discharge — `pp3` alone, and the by-kind map's `cp4` entry is now
     spent: the arm's real cost was the up-hop api cone (per-label landings reported source-AND-target)
     plus one new carried pair, not a channel-invariant field.**
   - **POSTSCRIPT (T2, 2026-08-20) — READ THIS BEFORE PRICING `cp4` OR ANY OTHER ARM FROM THE
     BY-KIND MAP ABOVE.**  `pp5` is DISCHARGED, for **264 net code lines**, and the way it closed
     re-prices two of the map's entries:
     * the "REFUTED on all three objects" verdict was right about DERIVABILITY and wrong about
       PRICE.  One of the three — `cvQui` — was **STRENGTHENED** rather than replaced: from the
       negative `SrvPre sa → RespFull ph → ⊥` to the positive `CellPreQ ph = (ph ≡ empty) ⊎ Σ x,
       ph ≡ draining x`.  Re-proving preservation at the EXISTING field cost **net −20 lines** in
       `LiveChanInv` (no `mkChan` arity change; `RespFull` + its four refutations became dead and
       were deleted), against the gate's 120-260 for a SIXTH field.  Twenty-one of the
       twenty-three producer rows were unchanged or simpler, and the two cell-FILLING rows
       discharged from the EXISTING `cvPre`.  **So "not derivable pointwise" does NOT imply
       "expensive": check whether the fact is already implicit at the rows that could break it.**
     * `ChanInv bsWsb (full (rrPayload r)) bcBusy` — the instance the gate verification
       machine-checked as INHABITED, and the state the `pp5` ladder had to exclude — is now
       **uninhabitable**, and independently machine-checked so at every pre-region server
       position (`bsBusy`, `bsAreq r`, `bsWnb` too), per the T2 review §2.3.
     * where the cost actually went: the CONE (+132, the `sendBFStartBatch` label pin, the landed
       row `SrvSbLand`, the classifier's eleventh component, `DnSbLand`/`DnSrvDrv`) and the
       sharpening (+49 in `LiveSrvOpen`, +31 in `LiveRelayCS`).  A THIRD funded arm of S1 is cheap
       (one `DrvCp` clause + one `drvCp-of` argument + two λ-halves per class producer); it is the
       cone and the ladder that are arm-specific.  **Do not re-price `cp4` at 264.**
   - **POSTSCRIPT (T7, 2026-08-23) — `cp5` IS DISCHARGED, AND THE BY-KIND MAP'S ONE REMAINING
     ChainSync CLAIM IS NOW SCORED.**  The map said "`cp5`/`pp1` are one cheap driver-tail
     coupling"; the T1 update then said both were "blocked on a ChainSync ROW layer that no module
     in the tree has".  Both halves were wrong in the same way — **the PAIRING**:
     * `pp1` (T5) needed ONE funded sub-phase and the CS-SERVER io channel (grant #11).
     * `cp5` (T7) needed **FOUR** funded sub-phases — `cp2`-`cp5`, because the row that puts the
       client at `ccIdle` fires at the relay's `cp1 → cp2` step and the residual names `cp5`,
       three BlockFetch api hops later — plus a whole api LANDING family on the CONSUME side
       (`LiveLegApiCone` §1c⁗/§2b⁗/§1d, three LOCAL `decCons` anchors, four new classifier
       components), a new `DriverExposed⁺` field pair, and a SOURCE PHASE on three of its four api
       arms that neither landed CS arm needed.  They were never one item.
     * the T1 update's "blocked on a ChainSync ROW layer" was right about the OBSTRUCTION and it
       was cleared by T4 (`LiveCSRow`, the row layer recovered post hoc from coarse-position
       injectivity — no frozen module widened).
     * **the one genuine discount was banked two tasks early and by accident of scope**: T5 built
       the per-key pin `LiveCSRow.cscRfwLands` and the two `ccIdle` io refutations for a consumer
       that did not yet exist, and they pay the whole of `cp5`'s `Header × Tip` value gate — the
       dearness item the T6d calibration priced at 45-70 came in at **zero**.  Bank the general
       form: *a per-key pin built at the natural key is reusable across the whole family, so price
       the pin once per KEY and not once per ARM.*
     * `cp5` cost NO sharpening and NO new unconditional premise on `coAt-split-at` (it is a
       POSITION), which is the first confirmation of the T6d review's §4(b) deferral ruling
       against a real arm.
   - **POSTSCRIPT (T9, 2026-08-27) — `pp3` IS RE-CLASSIFIED FROM "TRANSCRIPTION" BACK TO "NEW
     KIND", AND NOTHING WAS DISCHARGED.  READ THIS BEFORE FUNDING EITHER REMAINING ARM.**  The
     T8c BF re-gate rated `pp3` a transposition of the `cp6`/`pp0` freshness machinery and priced
     it 880-1,530.  `LiveRelayCS` §5b machine-checks FOUR negatives that put it back at a new
     kind, and `LiveDrvCSD` §6d builds the fact that decides the inventory:
     * **the carried freshness clause is VACUOUS at `pp3`** — `DnFresh` is a guarded implication
       and `RelayFresh (producing b pp3)` is `⊥` BY CONSTRUCTION, because at `pp3` the dn CS
       server is past `csAreq` and `SrvFresh` is false there.  A BF twin therefore needs its OWN
       guard region ("the relay has not yet fired `reqBFRange`" = `consuming` ∪ `{pp0 … pp3}`) and
       CANNOT reuse `DnFresh`'s ChainSync conjuncts under it.  Its PHASE conjunct is then exactly
       the token's `InCp03` — **no narrowing at all**, where `PhFresh` narrowed `{cp0 … cp3}` to
       `{cp0, cp1}`.  That lost narrowing is the whole difference between the two arms.
     * **the BF hop half of the transposition IS real and cheap**, and three of the five
       sub-cases are free or nearly so: the correlation kills `bcBusy`, `cp2` is the api sync the
       gate verification already costed cheap, and **`cp0` is already a THEOREM** off the CARRIED
       (and unguarded, hence still live at `pp3`) `DrvCliD` plus `LiveDrvCSD.cliIdle-cp0-⊥`.
     * **ONE leaf blocks it: node D's driver at `cp1`.**  Every component of the down BF hop is
       move-free at `(bsIdle, empty, bcIdle)` there — and node D's driver offers the BlockFetch
       request at `cp2` and NOWHERE else (`LiveDrvCSD.consD-brr-off`/`consD-cp1-no-brr`, §6d, the
       unoffered-label family's first BF member, F82 its guard) — so the refutation must come off
       the ChainSync axis at a relay phase where the landed freshness object says nothing.  The
       repair a driver-to-DRIVER pin would give is **FALSE, not merely unbuilt**: the relay's
       `pp2 → pp3` step is its own `sendCSRollForward` sync, at which the header has not been
       written to the wire, so node D sits at `cp0`/`cp1` for a whole stretch of `pp3` states.
     * **what the `cp1` leaf actually costs**, none of it in the re-gate's P1-P5: a `DrvCp` clause
       at `producing _ pp3` pinning the relay's own dn CS server (a REGION, not io-closed, so it
       needs a sharpening too) 150-300; **TWO** new CS io ladders, positionally distinct from the
       two `LiveIoIntroCS` §1c/§2b built — the relay's server WRITING and node D's client READING,
       the other two directions — 300-450; an exclusion of `ccArb` (the client never sees a
       rollback because `produce` never rolls one back, and nothing in the tree says so) 110-230;
       and the `cp1` api sync itself, a genuine transcription, 60-100.
     * **re-priced: 1,220-2,080** against a band of 880-1,530 and a STOP of 1,700, at a class of
       arm whose measured multiplier in this campaign is 1.2-1.8×.
     * **S-a IS NOT A `ChanInv` FIELD, and should not be priced as one** (the re-gate's 180-320 for
       a "client-antecedent `ChanInv` clause" shared with `cp4`).  The two states it was wanted for
       — `(bsIdle, empty, bcBusy)` and `(bsIdle, empty, bcStream)` — are excluded by the BF
       freshness clause's OWN client conjunct and correlation.  A hop-generic field cannot do it:
       `(bsIdle, empty, bcIdle)` is `chanInv-init` itself, so the exclusion is necessarily GUARDED
       on the relay's phase and therefore leg-level, not channel-level.
     * bank the general form: *a guarded invariant transposes only as far as its GUARD does.  Before
       pricing a transposition, check the guard region at the TARGET sub-phase first — it is one
       line, and it is what decides whether the conjuncts are reusable or have to be re-derived.*
   - **POSTSCRIPT (T11, 2026-08-25) — THE OBJECT IS BUILT AND THE ARM'S EQUATION IS PROVED MODULO
     THE LEAF; `pp3` IS STILL A PREMISE AND `Premises` STILL HAS TWO FIELDS.**  What T11 landed, and
     what of the T9 postscript above is now SUPERSEDED (the sentences are kept because they priced
     the work):
     * **`LiveDrvBFD` — the BF freshness twin**, with its own wide guard region (`consuming` ∪
       `{pp0 … pp3}`), the five-field core on four abstract positions, base/frame/lift, node D's
       JOINT BlockFetch adjacency `BFCliDrvAdj`, the six step classes, the state-level wrappers and
       the sharpening `bfFresh⇒areq`.  **Its §0 is the (T9/T10) GUARD CHECK done in writing before
       anything was built**, and it paid three times: the guard is `⊤` at `pp3` (the exact contrast
       with `DnFresh`); the region is an INITIAL SEGMENT of an acyclic advance chain containing the
       initial phase, so it is backward-closed and **has no entering step at all**; and — the
       measured POSITIVE — **the four in-region relay advances (`raCp6`, `a01`, `a12`, `a23`) cost NO
       cone work**, because they fire `apiCS` events and `SrvApiRowP`/`CliApiRowP` DEGENERATE TO THE
       FIXITY EQUATION at a non-BlockFetch label.  The ChainSync twin needed
       `LiveLegApiExpose.deRelayBD`'s third case for exactly this; the BlockFetch one needs no new
       field, no `BundleApiEvo` component and no Σ-append.
     * **two hazards were caught by the check BEFORE building, and both fixed the object's shape**:
       the client region is NOT io-closed on its own (`crNB`: `bcBusy + MsgNoBlocks → bcIdle`, so
       only the cell conjunct closes it — F93), and a phase-only conjunct would be FALSE because
       `(pp3 , cp3)` is REACHABLE, so the phase conjunct is the JOINT `PhCli` whose `cp3` clause
       constrains the client and whose `cp4`/`cp5`/`cp6` clauses are `⊥` (F94) — which is what lets
       the object supply `InCp03` itself instead of premising the token.
     * **`LiveRelayCS` §2d `areq-of` — the arm's equation, five premises of six discharged**: the
       drain τ, the server's own wire READ, node D's client's own wire WRITE (`LiveSrvOpen` §7, on
       **`LiveIoIntro` §10's TWO NEW BlockFetch io directions** — 145 net for the pair, rung 1
       already banked in the oracle, so *** a missing POLARITY on an axis that already has the other
       one costs rungs 2-4 and no new table fact ***), the `cp2` api sync (`LiveDrvCSD` §6e) and the
       `cp0` one (free, off the carried unguarded `DrvCliD`).  The sixth is the LEAF.
     * **the leaf is FOUR positions, not five** — `LiveDrvCSD` §6f refuted the `ccArf ht` member
       (T9's item (iv), "this one IS cheap", and it was: the node-D sync kits are protocol- and
       phase-generic, so a new member costs its rung 1), and `cliPost-cp1-rest` is the machine-checked
       residual: `ccWreq`, `ccAwait`, `ccMust`, `ccArb pt`.
     * **SUPERSEDED above**: "TWO new CS io ladders … 300-450" — the server-WRITE half already
       existed (T9-verify: 22) and T11 measured the same two directions on the BlockFetch axis at
       145 for BOTH, so the one remaining CS ladder (node D's client READING) prices at ~75; and
       "the `cp1` api sync itself, 60-100" is LANDED.
     * **STILL OPEN, and it is the arm's whole remaining risk**: the relay's own dn CS server region
       at `producing _ pp3` (item (i), a cone-edit-class item since `DnCsDrv`'s landing half has no
       `pp3` member), the payload/order correlation, the one remaining CS io ladder and the `ccArb`
       EXCLUSION — plus the carry (a NINTH `LegJointU` factor, priced at the eighth's measured 290)
       and the discharge.  `BFAt`'s `pp3` clause is UNCHANGED; F91 still stands at a FUNDED target,
       so this task does not owe the "nothing left to guard" statement.

## 4. RISKS

1. **The conditional headline** (main risk, narrowed to its floor at the CROSS-NODE API CLOSE):
   `LivenessSpec`, transported, rests on `cellCp3` and on NOTHING ELSE — *** it is now a ONE-premise
   theorem, and that premise is the only thing between this route and an unconditional
   `livenessSpec` *** (SUPERSEDED IN PLACE: this read "rests on `cellCp3` + the two residual halves
   (§3's (P1)/(P3′))") — all true, all REACHABILITY-shaped, all assumed. Every PEEL-shaped premise is
   gone, and the io half of the in-flight family is now a PREMISE-FREE THEOREM off the carried
   invariant, so *** THE SURVIVING PREMISES ARE NONE *** (SUPERSEDED IN PLACE: this read "the
   surviving premises are exactly ONE reachability argument (`cellCp3`) plus a cross-node
   co-position residual" — the residual went at T12 and `cellCp3` at the window).  There is no
   longer any gap between "theorem" and "the property, unconditionally": `livenessSpec-un` IS
   the property.
   **`cellCp3` was the one to read carefully** (it is a THEOREM since the cellCp3 window —
   `LiveChanJoin.cellCp3-of`): it was the last premise whose content is a
   reachability argument about the leg itself, and the only one with a priced route — whose
   2,250-3,110 monotone price was SUPERSEDED and never spent: the window closed for **315 net**
   off the carried join instead.
2. **`LiveFSim`'s G2 is RETIRED** (it was real, bounded, and has now been paid): the arms computed
   the component facts and discarded them; for the hidden classes the same-application trick
   recovered them, for the KEPT classes it could not, and the fix was to widen the two inversions
   so they return what they built — (P6)/(P7)/(P8), §A4/§A5/§A6. What REMAINS of the risk is only
   the CONVERSION no type records (`toSys r′` δ-reduces to the cone's own successor); the two
   `refl` probes in `LiveFSim` §D are the tripwire, and they still typecheck — no `subst` entered
   any premise site during the widenings. **Re-verified at T3b against the RECORD form** of
   `driverExpose⁺`: both probes are still `refl` with `proj₁` replaced by the field `deSucc`, which
   is the one thing the conversion had to preserve.
3. **The heavy assembly's dischargeability verdicts were static** (verified by reading, not
   building); surprises there cost wall-clock (23-min iterations), not soundness.
4. **Estimate calibration law of this effort:** only reviewer-re-derived bands ever held;
   ~10 recorded claims proved false pre-spend (both "unbuildable" and "banked" claims have been
   wrong in both directions). Re-derive every number and anchor at point of use.
5. **Classical seams — now REALISED, in `LivenessProof` and nowhere upstream of it:** the
   transport consumes the two sanctioned dne-certified König postulates —
   `DRImpliesFD.¬-divergent→normal` (`:69-73`, through `drbisim→⊑FD`) and
   `DRCongruence.modA-transfer` (`:278-282`, through `cong-∖`'s `div→`/`div←`). Unlike the LTL
   route, this route is not postulate-free. Note that `LiveNoDivH` deliberately avoided
   `modA-transfer` upstream (its descent uses only the postulate-free `div∖→modA`) and the hiding
   congruence re-introduces it unavoidably at the last step. Restate in any publication.
6. **Operational:** the decision ledger lives in gitignored `.superpowers/` on one machine (the
   committed record is the plans/specs + this file); the build depends on a warm `_build`
   (fresh clones pay cold heavy builds); one Phase-1 commit (`d651fcc`) carries a mislabelled
   message (contents fine — note in any PR).

(Item 7, the `ProdPh`-constructor guard, was RETIRED at the cross-node campaign's T2 — the guard is
a type error again — and its surviving guidance moved to §5's first bullet.)

## 5. Key reusable lessons (full list in the ledger and memory)

- **A NEW relay sub-phase is a coverage error at EIGHT sites — read this before adding a
  `ProdPh`/`ConsPh` constructor** (`R2_Bisim/SysNode.agda`: `ProdPh` at `:794-795`, `ConsPh` at
  `:928-930`).  The eight: `LiveRelayOpen.CoAt`, `LiveRelayCS.CSAt`/`BFAt` and its three §3 maps
  (`coAt-split-at`/`coAt⇒cs`/`coAt⇒bf`), plus `LiveDrvBF.DrvCp` and `LiveDrvBF.drvCp-of` — the last
  being the one that forces the DISCHARGE-vs-PREMISE decision to be taken rather than defaulted (a
  new funded arm has to arrive there as an argument).  *This entry was §4 RISKS item 7 until T2's
  shape switch retired the risk; it is kept HERE, as guidance, because the eight sites are worth
  knowing and a RISKS slot should not carry a non-risk.*  The drift that would be UNSOUND —
  coupling and residual disagreeing about a discharged arm — is machine-caught independently of
  totality (`LiveRelayCS` §7's F12/F18, and `LiveDrvBF` §6's F17 on the Π-bridge's phase index).
- A non-vacuity guard must be stated independently of the invariant it guards; arity-preserving
  mutations only (conjunct ↦ `⊤`).
- No FINE decode/slot injectivity exists anywhere: every cone-peeled arm must be SINGLE-PEEL; pairing
  is only by delta-convertibility of let-only leg-free arms or both-facts-from-one-peel. *(Scope
  corrected at T3b: the FINE statement stands and is what the peel discipline rests on. The COARSE
  statement — `tableSpec` position injectivity — is DERIVABLE, under a support-distinctness side
  condition; see §5's coarse-ROW bullet at `:505`. Do not read this bullet as covering the coarse
  level.)*
- The cones repeatedly already computed what was missing and discarded it (`_`-bound witnesses) —
  six recoveries during the assembly; grep the module family for fact-abstract siblings before
  asking to edit a base module (that grep returned grant #3 unexercised). When the value is
  provably unrecoverable downstream — the peel does not reduce for a variable step, and no FINE
  decode is injective — the route taken on this campaign was to widen the inversion with a strict
  TRAILING field, which is how (P6)/(P7)/(P8) were paid. *(T3b: "the ONLY route" was too strong —
  where the missing datum is a COARSE row there is a second route, recovering it post hoc off
  `tableSpec` coarse-position injectivity; §5's coarse-ROW bullet at `:505` states both and their
  respective costs.)* a grant may then be exercised SMALLER than granted (#5: one field
  subsumed both requested facts).
- Funext is absent from `src/`: an equation between two whole maps is stated POINTWISE instead
  (`specPos-break′`), which is a strictly weaker hypothesis and composes identically.
- When a frozen cone drops the very step that refutes a fire, TRANSCRIBE its peel into a new
  shared module with the fact riding along (`LiveKAFrozen`) and mark the transcription
  **KEEP-IN-SYNC** with the source span; a second peel does not correlate with the first.
- Build verification: `touch` does not force a rebuild and neither does deleting only the EDITED
  module's `.agdai` — an unchanged interface hash leaves every downstream `.agdai` valid, so the
  endpoint exits 0 having NEVER been visited (the fifth recorded false-green variant). Delete the
  ENDPOINT's own `.agdai` and require the literal `Checking …` line.
- The hide condition is BLOCK-sensitive on the kept side, ROLE-sensitive on the hidden side;
  the effective falsification is a role swap, not a link swap.
- **An invariant is worth more than the facts it proves.** Campaign 10's payoff came from trading
  twelve independent position facts for ONE per-hop invariant plus a residual: the facts had no
  proof route at all, while the invariant has a base, a frame, a per-class preservation calculus
  and — once the adjacency plumbing exists — an assembly join. Prefer replacing a family of
  premises by a single carryable object even when the immediate premise COUNT does not drop.
- **A transcribed adjacency table needs row PRODUCERS, not just care.** The producers make "every
  real step produces its row" a theorem by totality (a table row with no adjacency constructor
  leaves a `just` no clause can answer). Two blind spots survive and must be recorded wherever such
  a table lives: a SPURIOUS constructor (harmless — hypothesis position) and a row on a NEW EVENT
  FAMILY (dangerous — invisible to every producer, silently restoring vacuity).
- **The fired coarse ROW is the reusable currency of peer-position reasoning**, and every decode in
  the tree computes it and discards it (`tableSpec-ev-inv`'s `ceq` → `just-injective` → `mkMbfs`).
  **CORRECTED at T3/T3b (the T3 CS-row spike, confirmed by its adversarial verification): the
  earlier form of this bullet said the row is unrecoverable afterwards *because* abstract-position
  injectivity is FALSE, and that reasoning conflated two levels.** The doctrine, in the wording the
  verification banked:

  > the fired coarse ROW is recoverable post hoc iff the peer's table is COARSE-position injective,
  > which is single-peel provable exactly when its coarse positions have pairwise-distinct offer
  > SUPPORTS; what the sil-collapses prove is FINE non-injectivity, whose coarse witness pair is
  > diagonal — so a consumer needing an adjacency has two routes: widen the decode (KEEP-IN-SYNC,
  > no table obligation) or recover the row (no KEEP-IN-SYNC, but a standing support-distinctness
  > review obligation on `NodeSpecs`); never cite the sil-collapse against the second.

  Machine-checked scope, so the two levels stay apart: `absBF{c,s}-sil-collapse`
  (`SysStep:1156-1162`, both `refl`) are about the FINE coarsening map — `SysStep:1141-1147`'s own
  comment says so — and the collapse only ever supplies the DIAGONAL instance, verified as
  `collapse-is-diagonal = refl` beside a machine-checked `fineInj-false`. Coarse `tableSpec`
  position injectivity is DERIVABLE in 11 lines from the two banked generic lemmas
  (`tableSpec-ev-fwd` `SysOracle_NodeTauEv:979-984` fires `q₁`'s row, the table equation transports
  the step, `tableSpec-ev-inv` `:963-966` reads `q₂`'s row off it). The widening route
  ((P6)/(P7)/(P8)'s lesson, one layer lower) therefore remains CORRECT and is what the landed code
  uses; it is no longer the only route.
- Wire interfaces, don't document them: a documented-but-unwired antecedent would have made the
  progress half build a non-composing lemma.
- Agda 2.8 ICE: projection-like functions on `with`-abstracted variables in RESULT types —
  fix by a named total predicate + bridges. `with` matches the normalised goal. An index used
  only in ⊥-reducing arms must be explicit. Prefer the continuation form at menu boundaries.
- **A per-hop/per-leg arm family should be written hop-PARAMETRIC the first time.**  The
  `ChanLeg` join's five arms were first written per LEG with the up hop's four accessors
  hard-wired; the down hop then priced as a ~470-line textual mirror.  Abstracting the arms
  over the hop's accessors and its cell-key bridge (`LiveChanJoin.HopArm`, instantiated at
  `HUp`/`HDn`) landed BOTH hops for less than the mirror alone, because the expensive parts —
  a 21-clause label dispatch and four 9-clause row-refutation tables — are hop-INDEPENDENT
  once the key is a parameter.  The tell that the refactor will work: the underlying invariant
  layer is already payload-generic (here `ChanUp`/`ChanDn` were both `ChanInv` instances and
  both `-pres` lemmas one-liners off `chanInv-pres-eq`).
- **A frozen peel with a too-weak slot is not automatically a base edit.**  Node D's api peel
  reported no row about the client it moves, and the weak slot came from a bundle-level
  datatype matched at 28 sites — an expensive widening.  But the widened DECODE underneath it
  was already landed, so RE-MIRRORING the peel one layer up in the non-frozen CSP layer, calling
  that decode directly and bypassing the datatype, cost ≈190 lines and no grant.  Ask "is there
  a non-frozen re-mirror that skips the weak layer?" before asking for the widening.

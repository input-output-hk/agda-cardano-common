{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- InFlightOpen completion, Task 3b — THE E2 REDUCTION: split the api
-- residual `LiveRelayOpen.RelayCo` BY PROTOCOL.
--
-- WHY A SIBLING AND NOT AN EXTENSION OF `LiveRelayOpen`.  Two reasons, both
-- structural.  (1) The BlockFetch half of the split is meant to be discharged
-- from `LiveChanInv.ChanLeg`, and `LiveRelayOpen` does NOT import
-- `LiveChanInv` — the api family is the one family with no medium operand
-- anywhere in it (`LiveRelayOpen` §4), so pulling an 888-code-line channel
-- invariant into it would couple the api LADDER to the io INVARIANT for the
-- sake of one corollary layer.  (2) `LiveRelayOpen` §7 is a costed record of a
-- residual; this module is a re-STATEMENT of that residual.  Keeping them apart
-- keeps §7 quotable.
--
-- *** WHAT THE SPLIT IS. ***  `RelayCo l s` is `CoAt l s (relayOf l s)`, a total
-- dispatch on `CPPh` carrying ONE coarse co-position equation at each of the
-- relay driver's nine in-flight sub-phases (`LiveRelayOpen.agda:900-922`).  Four
-- of those nine equations name a BLOCKFETCH slot and five name a CHAINSYNC one:
--
--   sub-phase   co-party slot            protocol   equation
--   ---------   ----------------------   --------   -----------------------
--   cp4         up BF client             BF         `≡ bcIdle`   *** (T10) DISCHARGED ***
--   cp5         up CS client             CS         `≡ ccIdle`   *** (T7) DISCHARGED ***
--   cp6         dn CS server             CS         `≡ csAreq`
--   pp0         dn CS server             CS         `≡ csAreq`
--   pp1         dn CS server             CS         `≡ csCanAwait` *** (T5) DISCHARGED ***
--   pp2         dn CS server             CS         `≡ csMust`   *** (T6d) DISCHARGED ***
--   pp3         dn BF server             BF         `≡ bsAreq rg` (∃ rg)
--   pp4         dn BF server             BF         `≡ bsBusy`   *** (T1) DISCHARGED ***
--   pp5         dn BF server             BF         `≡ bsStream` *** (T2) DISCHARGED ***
--
-- §1 and §2 below are those two halves as separate total dispatches, `CSAt` and
-- `BFAt`, and §3 proves the split is EXACT: `coAt-split-at` recomposes `CoAt` from
-- the two, and `coAt⇒cs` / `coAt⇒bf` project it back, so no clause of `CoAt` is
-- lost by the split and none is duplicated across the halves.  Both dispatches
-- are TOTAL on `CPPh` — all seventeen shapes written out, no catch-all — which
-- is what makes a new `ConsPh`/`ProdPh` constructor a type error here rather
-- than a silently-`⊤` arm (`LiveRelayOpen` F5 is the mutation that establishes
-- that property for `CoAt`, and F7/F8 below do it for these two).
--
-- *** SCOPING: `isStable`, ALWAYS. ***  Every consumer-facing form in §4 takes
-- its residual under `isStable (radec r ∖ hidden blkA)`, exactly as
-- `LiveRelayOpen` §6e does, and for the same reason: as BARE state predicates
-- the BF half is FALSE at reachable states (`LiveRelayOpen` §7(a) gives the
-- machine-checked counter-state at `cp4`), so a bare premise would be REFUTABLE
-- and would make the campaign's headline theorem vacuously true.  The stability
-- WITNESS, not the position, is what the consumer feeds; F9 below is the
-- arity-preserving mutation that shows it.
--
-- *** WHAT THIS MODULE DOES NOT DO, AND THE HONEST REASON. ***  It does NOT
-- discharge `BFResidual` from `ChanLeg`.  §5 records the machine-checkable
-- reasons — the short version is that `ChanInv`'s five clauses all run
-- SERVER-or-CELL ⇒ CLIENT, so they constrain no server position at all (`pp3`,
-- `pp4`, `pp5`) and constrain the client only from a server/cell antecedent that
-- the relay-driver position does not supply (`cp4`).  Closing the BF half needs
-- a DRIVER-to-PEER coupling, a direction this development has never proved.  So
-- the deliverable that lands here is the SPLIT (exact, machine-checked, total)
-- and NOT the reduction to five.  *** (T12) THE LAST CLAUSE OF THIS PARAGRAPH IS
-- HISTORY, NOT STATUS. ***  It read "`BFResidual` remains a premise beside
-- `CSResidual`", and NEITHER IS A PREMISE ANY MORE.  *** Read that precisely: what was
-- retired is the two `Premises` FIELDS.  `CSResidual` and `BFResidual` THEMSELVES are
-- live definitions with live consumers *** — they are the `⊤`-valued synonyms
-- `csResidual-triv`/`bfResidual-triv` prove, and `relayCo-from` and §3 still name them.
-- `csRes` was retired at T8c-iii and
-- `bfRes` at T12, both residuals being theorems (`csResidual-triv`,
-- `bfResidual-triv`).  What is still true is everything before it — this module never
-- did discharge the BF half from `ChanLeg`, and the discharges that landed came from
-- the DRIVER-to-PEER coupling §5 named as "logically open", exactly as the paragraph
-- below says.  §5 refutes the chartered inference as theorems, and §6
-- classifies what each of the five CS equations actually needs — which is T3c's
-- gate input and is NOT one object.
--
-- *** WHAT (T1) AND (T2) CHANGED, AND WHAT THEY DID NOT. ***  The cross-node api
-- campaign BUILT that driver-to-peer coupling (`LiveDrvBF`, S1) and used it to
-- discharge TWO of the nine arms: `pp4` (T1) and `pp5` (T2).  Both clauses of `BFAt`
-- are `⊤` now and §3's `coAt-split-at` proves `CoAt`'s own clauses from the CARRIED
-- coupling — see §2's header.  §5 is untouched and still true: what it refutes is the
-- discharge from `ChanInv`/`ChanLeg` ALONE, and it names the DRIVER-antecedent
-- reading as "logically open" in as many words.  That reading is the route taken.
-- The other two BF arms (`cp4`, `pp3`) and FOUR of the five CS arms are premises
-- still — (T5) discharged `pp1`, off the same coupling and owner grant #11.
--
-- *** (T5), (T6d) AND (T7) TOOK THE CS SIDE THE SAME WAY, AND THE TALLY IS NOW FIVE OF
-- NINE. ***  All five discharged arms ride the ONE coupling `LiveDrvBF.DrvCp`: `pp4`
-- (T1) and `pp5` (T2) on the BlockFetch axis, `pp1` (T5), `pp2` (T6d) and `cp5` (T7) on
-- the ChainSync one.  *** `cp5` is the first on the CONSUME side and the first whose
-- co-party is a CLIENT rather than a server ***, and it is the first that needed the
-- coupling to carry sub-phases the residual does not name (`cp2`/`cp3`/`cp4`, its three
-- carriers).  What is premised still: `cp4` and `pp3` on the BF axis, `cp6` and `pp0` on
-- the CS one — FOUR of nine, and §6(iv) says why the CS pair is the deepest of them.
-- <<< SUPERSEDED TWICE: T8c-iii discharged `cp6`/`pp0` and T10 discharged `cp4`; the
-- current tally is the paragraph below. >>>
--
-- *** (T8c-iii) AND (T10): EIGHT OF NINE, AND ONE ARM REMAINS. ***  Discharged, in the
-- order they fell: `pp4` (T1), `pp5` (T2), `pp1` (T5), `pp2` (T6d), `cp5` (T7), `cp6`
-- and `pp0` (T8c-iii), `cp4` (T10).  *** PREMISED STILL: `pp3` ALONE *** — the down-hop
-- BF server's `∃ rg. ≡ bsAreq rg`, the one arm whose equation is a Σ rather than a
-- position, and the only equation `LivenessProof.Premises.bfRes` still carries.
-- `cp4` was the first arm on the UP hop, and the first whose refutations are moves of
-- the UP medium — which is why the two relay positions' antecedent in
-- `LiveStableOffer.InFlightOpen` widened to BOTH links in the same commit.
--
-- *** WHY `pp5` COST MORE THAN `pp4`, IN ONE SENTENCE. ***  Its position is not
-- io-closed: the api step that enters `pp5` leaves the server at `bsWsb` and only the
-- server's own WIRE-SEND carries it to `bsStream`, so the coupling can carry only the
-- REGION `{bsWsb, bsStream}` and the singleton equation needs a second ingredient —
-- the STABILITY refutation of `bsWsb` (`LiveSrvOpen.srvWsb-⊥`, off `LiveChanInv`'s
-- `cvQui` strengthened to the positive `CellPreQ`).  That is why this module now
-- imports one io-side lemma, and why the two api fields of `InFlightOpen` acquired
-- the down link's unbrokenness antecedent.
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`, no `funext`, and no
-- `with` in anything whose type mentions an imported `blkA`-parameterised
-- predicate — every dispatch is on an EXPLICIT argument, the campaign's
-- `blkA`-module rule.
------------------------------------------------------------------------

open import Data.Bool using ( false )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
-- (T9) the NON-polymorphic `⊤`, qualified: `LiveDrvBF.DrvCp`'s `⊤` clauses are stated
-- at `Data.Unit.⊤`, not at the polymorphic one this file's own dispatches use, so
-- §5b's triviality witness at `pp3` needs the other `tt` (measured: `Level.Lift _ ⊤
-- !=< Agda.Builtin.Unit.⊤`)
import Data.Unit as U
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary using ( ¬_ )
-- (T6d) `sym`/`trans`/`cong` are new here: the `csWar` refutation's pin is stated at
-- `LiveChanCS.dnCSsOf` and this module reads `LiveRelayOpen.dnCSs`, so the two-clause
-- bridge `dnCSs-is-of` has to be transported into it
open import Relation.Binary.PropositionalEquality
  -- (T8c-iii) §3's two discharged clauses transport the sharpening's conclusion across
  -- the `dnCSs`/`dnCSsOf` bridge
  using ( _≡_; refl; sym; trans; cong; subst )

open import Process_Trees using ( ExtI; isStable )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveRelayCS
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟ )
-- (T9) `Header`/`Tip`/`Point` are new here: §5b's `CliPost`-blindness witness names
-- the two PAYLOAD-CARRYING members of node D's `cp1` client region (`ccArf`, `ccArb`)
open import CSP.Examples.Cardano_network.Data p
  -- (T11, round 3) §2f's rollforward arm names the message and the payload's three
  -- lenient components
  using ( Payload; ChainRange; Header; Tip; Point; chainSync; MsgCSRollForward )
open import CSP.Examples.Cardano_network.Base using ( Mode )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Time; Length )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∖_ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial; med )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  -- (T8c-iii) `draining` joins `empty`: the bundle's drain field names it
  -- (T11, round 3) … and `full`, which §2f's two reader arms name
  using ( CopyPhase; empty; draining; full; broken )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( CPPh; consuming; producing
              ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
              ; ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9 )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( coarsenCSc; coarsenCSs; coarsenBFc; coarsenBFs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  -- (T6d) `legCD` joins `legBD`: `dnCSs-is-of` dispatches on BOTH constructors
  -- (T8c-iii) … and node D's phase and stored block, which the bundle's api-sync field
  -- and its discharge name
  -- (T9) … and the token's own D-consumer region, which §5b shows does not separate
  -- the relay's `pp3` from node D's `cp1`
  using ( TwoLegs; legBD; legCD; phOf; cblkOf; InCp03 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  -- (T9) … and the token's relay-side region at level `L2`, §5b's other half
  -- (T10) … and the token ITSELF, with its producer constraint and the two relay
  -- regions §5c's `cp4` level computation eliminates.  *** THIS IS THE ARM's PIN AND
  -- IT IS CARRIED ALREADY *** — see §5c
  -- (T11) … and node D's own DOWN-hop BF client, which §2d's `pp3` arm reads
  using ( relayOf; upClient; RelayHas; PipeInv; PLvl; L0; L1; L2; L3; L4
        ; prodOf; ProdSent; RelayPre; RelayFwd; dnClient )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( hidden )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA
  using ( lpRelayIn; lpRelayOut )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveStableOffer blkA
  using ( RefutedAt; Window; wLink2 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanInv blkA
  using ( ChanInv; mkChan; ChanUp; ChanDn; ChanLeg; chanInv-init; chanLeg-init
        ; preQ-full-⊥ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveRelayOpen blkA
  using ( upCSc; dnCSs; CoAt; RelayCo; relayOpen-in; relayOpen-out )
-- (T1) S1, the BF driver-tail coupling — CARRIED in the FSim's `Rel`
-- (`LiveChanJoin`'s fifth trailing factor), and the discharge of the `pp4` arm
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvBF blkA as LDB
-- (T8c-iii) node D's freshness clause, its coupling and the sharpening that turns them
-- into the `cp6`/`pp0` arms' own equation.  The carry is `LiveChanJoin`'s SEVENTH
-- `LegJointU` factor, so a consumer of §3 already holds it
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvCSD blkA as LDC
-- (T10) the UP hop's carried pair (`UpBd × UpCli`) and the equation it proves at the
-- `cp4` guard.  The carry is `LiveChanJoin`'s EIGHTH `LegJointU` factor, so a consumer
-- of §3 already holds it — exactly as it holds `LDB.DrvBF` and `LDC.DnJoint`
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvBFA blkA as LDBA
-- (T11) *** the DOWN hop's BlockFetch freshness clause and the sharpening that turns
-- it into the `pp3` arm's own equation. ***  Its carry is NOT yet a `LegJointU`
-- factor, so §2d takes it as an ARGUMENT — the (T10) parked-interface pattern, and
-- the acceptance probe for the object's consumer-facing shape
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveDrvBFD blkA as LBFD
-- (T2) … and the STABILITY half of the `pp5` discharge: the coupling pins the down
-- server to the region `{bsWsb, bsStream}`, and a stable configuration cannot be at
-- `bsWsb` (`LiveSrvOpen` §3).  This is the module's only io-side import and it is
-- one lemma wide.
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveSrvOpen blkA
  using ( srvWsb-⊥
        -- (T6d) … and its ChainSync twin, which is what sharpens the `pp2` REGION
        ; csWar-⊥
        -- (T8c-iii) … and §6's three `csIdle` exclusions, which are three of the
        -- bundle's four fields (the fourth is `LiveDrvCSD` §3's api sync)
        ; cellDrainCS-⊥; cellReqCS-⊥; cliWreqCS-⊥
        -- (T11) … and §7's three BLOCKFETCH twins, which are three of the `pp3`
        -- arm's six premises
        ; cellDrainBF-dn-⊥; cellRngBF-dn-⊥; cliWrrBF-dn-⊥
        -- (T11, round 2) … and §8's FOUR ChainSync arms, which are the `cp1`
        -- leaf's own: the server's pending rollforward write and the three
        -- reader-side deliveries on §2c's new ladder
        ; srvWrf-⊥; cliAwaitAr-⊥; cliAwaitRfw-⊥; cliMustRfw-⊥ )
-- (T6d) the CS twin of the `ChanDn` above: the down-hop ChainSync channel invariant
-- `csWar-⊥` runs on, plus its own down-server accessor (the SAME node fields
-- `LiveRelayOpen.dnCSs` reads, under a second name — `dnCSs-is-of` below bridges them,
-- because neither reduces at a variable leg)
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanCS blkA
  -- (T8c-iii) … and the hop's CELL, which §3's exclusion bundle names
  -- (T11, round 3) … and the client region §6h's correlations conclude in
  using ( ChanCSDn; dnCSsOf; cellCSDn; CliAwt )

------------------------------------------------------------------------
-- §1  THE CHAINSYNC HALF — *** TWO equations since (T7), `⊤` at the other fifteen
-- shapes. ***
--
-- Read against `LiveRelayOpen.CoAt` (`:900-917`): this is that dispatch with its
-- four BlockFetch-slot clauses (`consuming _ cp4`, `producing _ pp3/pp4/pp5`)
-- replaced by `⊤` and every other clause copied verbatim.  *** FOUR here counts
-- `CoAt`'s BF SLOTS, which neither T1 nor T2 changed. ***  (SUPERSEDED IN PLACE, stale
-- twice over and read as current until T12: this continued "; §2's `BFAt` is a residual
-- of TWO equations because `pp4`'s and `pp5`'s are discharged".  `BFAt`'s residual went
-- to ONE at T10 (`cp4`) and to *** ZERO *** at T11h (`pp3`) — it is `⊤` at all
-- seventeen shapes, `bfAt-triv` proves it, and `bfRes` was retired at T12.)  The TWO
-- clauses mention exactly ONE slot — the leg's down-hop CS SERVER (`cp6`, `pp0`) — at
-- ONE position of that server's state machine (`csAreq`).  So the CS half is now
-- HOMOGENEOUS in the strongest sense the E2 route ever claimed for it: one place, one
-- protocol, one leg.  (`pp1`'s `csCanAwait` left at T5, `pp2`'s `csMust` at T6d and
-- `cp5`'s `ccIdle` at T7 — with `ccIdle` went the half's only CLIENT slot, computed
-- from the clause list above and not carried over.)
--
-- *** (T5) THE `pp1` CLAUSE IS `⊤` NOW, AND THAT IS THE THIRD DISCHARGE. ***  Its
-- equation moved into `LiveDrvBF.DrvCp`'s own `pp1` clause — the SAME coupling the
-- two BF arms ride, extended rather than duplicated — and §3's `coAt-split-at` proves
-- `CoAt`'s `pp1` clause from it.  What made it the cheap CS arm: `csCanAwait` is
-- entered by exactly ONE table row (T5's per-key pin `LiveCSRow.cssReqLands`) and is
-- io-CLOSED, so the coupling's two io classes REFUTE rather than region, and its api
-- class reads the cone's already-applied landing.  Its io preservation is what OWNER
-- GRANT #11 bought: the io cone now carries a CS-SERVER fact
-- (`PipeNodeIoEvo.CssFact`, `LiveLegIoCone.CssRowP`), which it did not when this
-- module's §6 was written.
--
-- *** (T6d) AND SO IS THE `pp2` CLAUSE — THE FOURTH DISCHARGE. ***  Its equation moved
-- into `LiveDrvBF.DrvCp`'s `pp2` clause, and unlike `pp1`'s it moved as a REGION:
-- `csWar` is where the entering api step puts the server, `csMust` is one io hop
-- further on, and no invariant can say `≡ csMust` at the entering instant.  §3's
-- `csRegion⇒must` closes the gap with the STABILITY refutation of `csWar`
-- (`LiveSrvOpen.csWar-⊥`), which is the exact `pp5` shape one axis over — and the
-- reason it is available at all is the ChainSync CHANNEL invariant T6b built and T6c
-- joined (`LiveChanCS.ChanCSDn`, the FSim `Rel`'s sixth trailing factor).  So the
-- `pp2` arm is NOT the "sequential plus one io hop" premise §6(iii) priced: the io hop
-- is now proved, not assumed.
--
-- *** (T7) AND THE `cp5` CLAUSE IS `⊤` — THE FIFTH DISCHARGE, AND THE CHEAPEST OF THE
-- FIVE AT THE CONSUMER. ***  Its equation moved into `LiveDrvBF.DrvCp`'s `cp5` clause,
-- and it moved as a POSITION: `ccIdle` is entered by ONE row reachable here
-- (`ccArf ht + apiCS recvCSRollforward`, T5's per-key pin `LiveCSRow.cscRfwLands`) and
-- has NO io row in either direction (`cscIdle-in-⊥`/`cscIdle-out-⊥`), so there is
-- nothing to sharpen — no `csRegion⇒must` twin, no stability refutation, and *** NO
-- THIRD UNCONDITIONAL PREMISE ON §3's `coAt-split-at` ***.  The T6d review §4(b) ruled
-- exactly that in advance and declined a refactor on the strength of it; the ruling
-- held, and the premise count is still TWO.
--
-- What it cost instead sits one layer up: the discharge needed THREE MORE FUNDED CLAUSES
-- of `DrvCp` than it discharges here (`cp2`, `cp3`, `cp4`), because the row that
-- establishes `ccIdle` fires at the relay's `cp1 → cp2` step and the residual names
-- `cp5`, three BlockFetch api hops later.  *** So from T7 on this file's clause list and
-- `LiveDrvBF`'s are NO LONGER in bijection. ***  `LiveDrvBF` §1's own marker says the
-- same thing from the other side.
--
-- *** (T8c-iii) THE `cp6`/`pp0` ARMS ARE WIRED AND DISCHARGED — resolved history, kept
-- because it is the record of HOW. ***
--
-- *** THE SENTENCE THIS BLOCK USED TO CARRY IS FALSE AND IS QUOTED SO IT CANNOT BE
-- REINTRODUCED BY COPY: *** "What is missing is ONE step: nothing CARRIES `DnFresh ×
-- DrvCliD` yet, so §3's `coAt-split-at` has nothing to apply the sharpening to and *the
-- two clauses below stay equations*."  *** FALSE at every clause. ***  The pair IS
-- carried — `LiveChanJoin.LegJointU`'s SEVENTH trailing factor `LiveDrvCSD.DnJoint`,
-- threaded through all five arms — §3 DOES apply the sharpening, and the two clauses
-- below are `⊤`.
--
-- What actually landed, and it is the route `LiveDrvCSD` §8 wrote out: the freshness
-- clause `DnFresh`, node D's coupling `DrvCliD`, the sharpening `dnFresh⇒areq` (its
-- FOUR `⊥`-premises theorems off `LiveSrvOpen` §6 and `LiveDrvCSD` §3, on the two io
-- ladders `LiveIoIntroCS` §1c/§2b built), the total joint-adjacency producer
-- `cliDrvAdj-of` (§6c) and the twelve preservation classes (§5b/§5c) — carried as one
-- factor, and consumed at §3's two discharged clauses through the bundled `CsIdleExcl`.
-- *** THE PREMISE COUNT PREDICTION IN THE OLD TEXT WAS ALSO WRONG: *** it said the
-- one-record shape "keeps `coAt-split-at`'s unconditional-premise count at two rather
-- than seven".  It went to THREE — one record, not five, but a third all the same — and
-- that third premise fired §4's own deletion trigger, which is why the two
-- `relayOpen-*-ws′` corollaries no longer exist.
--
-- KEEP IN SYNC with `LiveRelayOpen.CoAt`: §3's `coAt-split-at` / `coAt⇒cs` /
-- `coAt⇒bf` are the machine check that this file and that one still agree, and
-- they fail to typecheck if any clause here drifts from its counterpart there.
------------------------------------------------------------------------

-- the CHAINSYNC co-position requirement, per sub-phase (total on `CPPh`)
CSAt : TwoLegs → SysState → CPPh → Set
CSAt l s (consuming _ cp0) = ⊤
CSAt l s (consuming _ cp1) = ⊤
CSAt l s (consuming _ cp2) = ⊤
CSAt l s (consuming _ cp3) = ⊤
CSAt l s (consuming _ cp4) = ⊤
-- (T7) DISCHARGED: `coarsenCSc (upCSc l s) ≡ NS.ccIdle` is now `LiveDrvBF.DrvCp`'s own
-- `cp5` clause — the LAST link of the `cp2 … cp5` chain, whose other three links are
-- funded carriers with no partner here (see §1's header) — and §3's `coAt-split-at`
-- proves `CoAt`'s `cp5` clause from it.  *** THIS IS THE FIRST DISCHARGE ON THE CONSUME
-- SIDE, AND THE FIRST WHOSE PEER IS A CLIENT. ***  F47 is the mutation that says the
-- clause is genuinely gone
CSAt l s (consuming _ cp5) = ⊤
-- *** (T8c-iii) DISCHARGED — THE FIFTH AND SIXTH, AND THE CS HALF IS NOW EMPTY. ***
-- `coarsenCSs (dnCSs l s) ≡ NS.csAreq` did not go away: it is DERIVED at §3 from the
-- CARRIED pair `LiveDrvCSD.DnJoint` (node D's freshness clause × its driver-tail
-- coupling, `LegJointU`'s seventh factor) sharpened by the four `csIdle` exclusions
-- `LiveSrvOpen` §6 proves from stability.  Unlike the other four discharges the
-- equation does NOT move into `LiveDrvBF.DrvCp`: proving it needs `DnFresh`, `DrvCliD`
-- AND stability, and `DrvBF`'s preservation is state-to-state, so the derivation has to
-- happen at the ARM.  That is why §3 gained a premise record rather than a clause.
CSAt l s (consuming _ cp6) = ⊤
CSAt l s (producing _ pp0) = ⊤
-- (T5) DISCHARGED: `coarsenCSs (dnCSs l s) ≡ NS.csCanAwait` is now `LiveDrvBF`'s
-- `DrvCp`'s own `pp1` clause, carried — see §1's header and §3's `coAt-split-at`
CSAt l s (producing _ pp1) = ⊤
-- (T6d) the `pp2` arm has LEFT the CS half too: its content is `LiveDrvBF.DrvCp`'s
-- `pp2` REGION sharpened by the stability refutation of `csWar` — F43 is the mutation
-- that says the clause is genuinely gone, not merely satisfiable
CSAt l s (producing _ pp2) = ⊤
CSAt l s (producing _ pp3) = ⊤
CSAt l s (producing _ pp4) = ⊤
CSAt l s (producing _ pp5) = ⊤
CSAt l s (producing _ pp6) = ⊤
CSAt l s (producing _ pp7) = ⊤
CSAt l s (producing _ pp8) = ⊤
CSAt l s (producing _ pp9) = ⊤

-- the CS half AT THE RELAY DRIVER'S ACTUAL PHASE — the TWO-equation residual
-- since (T7) (`cp6`, `pp0`), both at the SAME slot and the SAME position
CSResidual : TwoLegs → SysState → Set
CSResidual l s = CSAt l s (relayOf l s)

------------------------------------------------------------------------
-- §2  THE BLOCKFETCH HALF — *** TWO equations since (T2), `⊤` at the other
-- fifteen shapes. ***
--
-- The `pp3` clause is the only one of the remaining seven that is not a bare
-- equation: the server's pre-region position carries the client's `ChainRange`,
-- which no caller of the arm knows, so the arm quantifies it existentially and
-- the residual must too (`LiveRelayOpen.arm-pp3` takes `rg` as an argument, and
-- `relayOpen-out` feeds it `proj₁` of this Σ — `:965-966`).
--
-- *** (T1) THE `pp4` CLAUSE IS NOW `⊤`, AND THAT IS THE DISCHARGE. ***  Its
-- equation — `coarsenBFs (dnSrv l s) ≡ bsBusy` — did not go away: it moved into
-- `LiveDrvBF.DrvCp`'s `pp4` clause, which the FSim's `Rel` CARRIES (`LiveChanJoin`
-- §1's fifth trailing factor), and §3's `coAt-split-at` proves `CoAt`'s own `pp4`
-- clause from it instead of premising it.
--
-- *** (T2) AND SO IS THE `pp5` CLAUSE, IN TWO PIECES. ***  `coarsenBFs (dnSrv l s) ≡
-- bsStream` is NOT carryable on its own — the api step entering `pp5` lands the
-- server at `bsWsb` (`bfSnxt :604-605`) and only its wire-send goes on to `bsStream`
-- (`:610-613`) — so what the coupling carries is the REGION, `DrvCp`'s `pp5` clause
-- `(≡ bsWsb) ⊎ (≡ bsStream)`, and §3's `region⇒stream` sharpens it with the stability
-- refutation of `bsWsb`.  The refutation is `LiveSrvOpen.srvWsb-⊥`: at `bsWsb` the
-- strengthened `cvQui` says the hop's cell is empty or draining, and each gives the
-- medium an enabled move.  So this half is a residual of TWO equations, both at slots
-- a relay-local coupling cannot reach: `cp4` needs node A's `MsgBatchDone` and `pp3`
-- node D's request — both CROSS-NODE.
--
-- *** (T9) BOTH ARE STILL PREMISES, AND `pp3`'s ROUTE IS RE-CLASSIFIED — see §5b.
-- ***  The (T8c) re-gate rated `pp3` a TRANSCRIPTION of the `cp6`/`pp0` freshness
-- machinery.  §5b machine-checks four negatives that put it back at NEW KIND: the
-- carried freshness clause is VACUOUS at `pp3` (its guard's `pp3` clause is `⊥` by
-- construction), the carried relay coupling is TRIVIAL there, the carried node-D
-- coupling leaves five client positions at node D's `cp1`, and the token does not
-- separate the relay's `pp3` from node D's `cp1`.  The BF-hop half of the
-- transposition is real and cheap; ONE leaf of one dispatch — node D at `cp1` — needs
-- a ChainSync-axis chain with two objects the campaign has never built.  §5b has the
-- inventory and the re-priced band.
--
-- WHY THE CLAUSES ARE KEPT AT ALL, rather than deleted with the shape: totality on
-- `CPPh` is what makes a new `ProdPh` constructor a type error here (F7/F8), and
-- `⊤` at a DISCHARGED arm is exactly the same statement as `⊤` at a vacuous one —
-- the difference is recorded by `coAt-split-at`'s `pp4`/`pp5` clauses, which no longer
-- read their `BFAt` argument and would not typecheck without the coupling.
------------------------------------------------------------------------

-- the BLOCKFETCH co-position requirement, per sub-phase (total on `CPPh`)
BFAt : TwoLegs → SysState → CPPh → Set
BFAt l s (consuming _ cp0) = ⊤
BFAt l s (consuming _ cp1) = ⊤
BFAt l s (consuming _ cp2) = ⊤
BFAt l s (consuming _ cp3) = ⊤
-- *** (T10) DISCHARGED — THE SEVENTH ARM, AND THE FIRST ON THE UP HOP. ***
-- `coarsenBFc (upClient l s) ≡ NS.bcIdle` is now §2c's `upIdle-of`, off the carried
-- pair `LiveDrvBFA.UpJoint` (`LiveChanJoin`'s EIGHTH factor) plus the token's own
-- level computation at the guard; §3's `coAt-split-at` proves `CoAt`'s `cp4` clause
-- from it, through the per-clause `Sharp`.  F89 (§10) is the mutation that says the
-- clause is genuinely gone
BFAt l s (consuming _ cp4) = ⊤
BFAt l s (consuming _ cp5) = ⊤
BFAt l s (consuming _ cp6) = ⊤
BFAt l s (producing _ pp0) = ⊤
BFAt l s (producing _ pp1) = ⊤
BFAt l s (producing _ pp2) = ⊤
-- *** (T11h) DISCHARGED — THE EIGHTH ARM, THE LAST OF THE HALF, AND THE HALF IS NOW
-- EMPTY. ***  `Σ rg, coarsenBFs (dnSrv l s) ≡ NS.bsAreq rg` is `areq-of⁺⁺` off the
-- CARRIED `LiveDrvBFD.BFFresh` (`LiveChanJoin`'s fifth factor's third half since T11h)
-- plus node D's coupling and §6h's record — all three read off the join — with the
-- link fact and `isStable` the two api consumers already hold.  §3's `Sharp` carries
-- the requirement now, exactly as `cp4`'s does; the clause below is `⊤`.
-- *** F91 HAS NO FUNDED `BFAt` CLAUSE LEFT TO GUARD — the honest record the
-- third re-aiming owed (§10). ***
BFAt l s (producing _ pp3) = ⊤
-- (T1) DISCHARGED: `coarsenBFs (dnSrv l s) ≡ NS.bsBusy` is now `LiveDrvBF`'s
-- `DrvCp`'s own `pp4` clause, carried; see §2's header and §3's `coAt-split-at`
BFAt l s (producing _ pp4) = ⊤
-- (T2) DISCHARGED: `coarsenBFs (dnSrv l s) ≡ NS.bsStream` is now the carried REGION
-- `LiveDrvBF.DrvCp`'s `pp5` clause plus `LiveSrvOpen.srvWsb-⊥`; see §2's header
BFAt l s (producing _ pp5) = ⊤
BFAt l s (producing _ pp6) = ⊤
BFAt l s (producing _ pp7) = ⊤
BFAt l s (producing _ pp8) = ⊤
BFAt l s (producing _ pp9) = ⊤

-- the BF half AT THE RELAY DRIVER'S ACTUAL PHASE — *** ONE equation since (T10)
-- (`pp3` alone; `cp4` was the other, and §2c discharged it) ***
BFResidual : TwoLegs → SysState → Set
BFResidual l s = BFAt l s (relayOf l s)

------------------------------------------------------------------------
-- §2c  *** (T10) THE `cp4` ARM's OWN EQUATION, OFF THE CARRIED PAIR. ***
--
-- §5c's guard check is what licenses this section: at `consuming _ cp4` the token can
-- only be at `L2` (`L0`/`L1` need `RelayPre`, `L3`/`L4` need `RelayFwd`, all `⊥`
-- there), and `L2`'s producer constraint IS `ProdSent` — so "node A has already fired
-- `sendBFBlock` on the leg's up link" is CARRIED, not owed.  That is
-- `pipeInv⇒sent-cp4`, relocated here from §5c so §3 can consume it.
--
-- `upIdle-of` is then the whole arm: the guard, the up link's unbrokenness, the up-hop
-- channel invariant, the carried pair and stability give `≡ bcIdle`.  Everything but
-- the guard is held by BOTH stability-scoped consumers below, and every carried piece
-- comes off the joint invariant `LivenessProof.ifo-of` already destructures — so this
-- is a DISCHARGE and not a new premise.
------------------------------------------------------------------------

-- the token's level computation at the guard (relocated from §5c; F85 is its mutation)
pipeInv⇒sent-cp4 : (l : TwoLegs) (s : SysState) (b : Block₃)
                 → relayOf l s ≡ consuming b cp4
                 → PipeInv l s → ProdSent (prodOf l s)
pipeInv⇒sent-cp4 l s b eq (L0 , _  , hr , _) = ⊥-elim (subst RelayPre eq hr)
pipeInv⇒sent-cp4 l s b eq (L1 , _  , hr , _) = ⊥-elim (subst RelayPre eq hr)
pipeInv⇒sent-cp4 l s b eq (L2 , hp , _  , _) = hp
pipeInv⇒sent-cp4 l s b eq (L3 , _  , hr , _) = ⊥-elim (subst RelayFwd eq hr)
pipeInv⇒sent-cp4 l s b eq (L4 , _  , hr , _) = ⊥-elim (subst RelayFwd eq hr)

-- *** (T10) THE `cp4` SHARPENING, AS ONE NAMED STEP — `region⇒stream`'s analogue on
-- the UP hop. ***  Unlike that one it is not a region narrowing: the carried
-- `UpCli` region is `{bcIdle, bcStream}` and `LiveUpOpen.upStream-⊥` kills `bcStream`
-- from stability, which `LiveDrvBFA.upCli⇒bcIdle` does internally.  Named (not
-- inlined) for `region⇒stream`'s reason and because both consumers below call it
upIdle-of : (l : TwoLegs) (r : RState)
          → broken (med (toSys r)) (upLink l) ≡ false
          → ChanUp l (toSys r) → LDBA.UpJoint l (toSys r) → PipeInv l (toSys r)
          → isStable (radec r ∖ hidden blkA)
          → (b : Block₃) → relayOf l (toSys r) ≡ consuming b cp4
          → coarsenBFc (upClient l (toSys r)) ≡ NS.bcIdle
upIdle-of l r hbUp ivU upj pinv sta b eq =
  LDBA.upCli⇒bcIdle l r b eq hbUp ivU
    (LDBA.upJoint⇒bd  l (toSys r) upj)
    (LDBA.upJoint⇒cli l (toSys r) upj)
    (pipeInv⇒sent-cp4 l (toSys r) b eq pinv) sta

------------------------------------------------------------------------
-- §2d  (T11) *** THE `pp3` ARM's OWN EQUATION, ASSEMBLED — five of its six
-- premises discharged, and the sixth is T9's LEAF. ***
--
-- §5b is the record of why this arm needs an object of its own; `LiveDrvBFD` is
-- that object, and this section is its consumer.  The shape is §2c's
-- (`upIdle-of`) at the other hop: the guard is free at the arm's sub-phase
-- (`LBFD.relayFreshBF-at`, and §0 of that module is the guard check that says so),
-- the freshness clause is applied, and the caller's stability refutations are
-- fed in as the five `⊥`-premises they are.
--
-- WHERE EACH PREMISE COMES FROM — the inventory, at the point of use:
--   (1) `LiveSrvOpen.cellDrainBF-dn-⊥`  the medium's own drain τ;
--   (2) `LiveSrvOpen.cellRngBF-dn-⊥`    the down BF server's own wire READ, on
--       `LiveIoIntro` §10's new reader-polarity ladder;
--   (3) `LiveSrvOpen.cliWrrBF-dn-⊥`     node D's client's own wire WRITE, on §10's
--       other new ladder;
--   (4) `LiveDrvCSD.bfIdle-cp2-⊥`       the api sync at node D's `cp2` (§6e);
--   (5) `LiveDrvCSD.cliIdle-cp0-⊥`      the api sync at `cp0`, on the CHAINSYNC
--       axis, off the carried and UNGUARDED `DrvCliD` — free, and T9 said so;
--   (6) *** THE LEAF: node D at `cp1`, still a premise. ***
--
-- *** WHY THE OBJECT IS AN ARGUMENT AND NOT A CARRIED FACT (yet). ***  `BFFresh`
-- is not a `LegJointU` factor: adding it is the NINTH factor, priced at the
-- EIGHTH's measured 290 (the T10 review's I-3).  Until then this lemma is the
-- parked interface — `LiveTokenExcl` §1b's precedent and T10's own R1 — and it is
-- also the ACCEPTANCE PROBE: it typechecks exactly when the object's
-- consumer-facing shape is the one the arm needs, which is the check that catches
-- an interface built against the wrong hypothesis before the carry pays for it.
------------------------------------------------------------------------

-- the `pp3` arm's equation, modulo the leaf.  `BFAt`'s `pp3` clause VERBATIM as
-- the conclusion, so a discharge is a matter of supplying the two arguments
areq-of : (l : TwoLegs) (r : RState)
        → broken (med (toSys r)) (dnLink l) ≡ false
        → LBFD.BFFresh l (toSys r) → LDC.DrvCliD l (toSys r)
        → isStable (radec r ∖ hidden blkA)
        -- (6) the leaf: node D's driver at `cp1` with its BF client at `bcIdle`
        → (coarsenBFc (dnClient l (toSys r)) ≡ NS.bcIdle → phOf l (toSys r) ≡ cp1 → ⊥)
        → (b : Block₃) → relayOf l (toSys r) ≡ producing b pp3
        → Σ[ rg ∈ ChainRange ] (coarsenBFs (dnSrv l (toSys r)) ≡ NS.bsAreq rg)
areq-of l r hb fresh cpl sta noleaf b eq =
  LBFD.bfFresh⇒areq l (toSys r) (LBFD.relayFreshBF-at l (toSys r) b eq) fresh
    (λ dr → cellDrainBF-dn-⊥ l r (proj₁ dr) hb (proj₂ dr) sta)
    -- the cell's four lenient components and its equation, in `RngOnly`'s own order
    (λ hidl rq → cellRngBF-dn-⊥ l r (proj₁ rq) (proj₁ (proj₂ rq))
                   (proj₁ (proj₂ (proj₂ rq))) (proj₁ (proj₂ (proj₂ (proj₂ rq))))
                   hb hidl (proj₂ (proj₂ (proj₂ (proj₂ rq)))) sta)
    (λ he hcw → cliWrrBF-dn-⊥ l r (proj₁ hcw) hb he (proj₂ hcw) sta)
    (λ hci h2 → LDC.bfIdle-cp2-⊥ l r (cblkOf l (toSys r)) hci h2 refl sta)
    -- (5) is the ChainSync-axis sync, and the coupling's `cp0` clause is what
    -- supplies its client pin — T9's "already a THEOREM", spent here
    (λ hci h0 → LDC.cliIdle-cp0-⊥ l r (cblkOf l (toSys r))
                  (LDC.drvCliD-to0 l (toSys r) cpl h0) h0 refl sta)
    noleaf

------------------------------------------------------------------------
-- §2e  (T11, round 2) *** DELETED IN THE (T11) FIX ROUND — the ruling, kept in
-- the tree's DELIBERATE-KEEP form so the decision is recorded rather than
-- implicit (`LiveCellOpen:262`'s convention, one polarity over). ***
--
-- This section held `leaf⇒⊥` (the `cp1` leaf closed modulo THREE LOOSE premises)
-- and `areq-of⁺` (the arm against them).  §2f's `dnRfw⇒leaf` supersedes both: it
-- closes the SAME seven configurations from ONE object, and its `cell-arms`
-- dispatch duplicated `leaf⇒⊥`'s arm for arm.  `areq-of⁺` had no consumer and
-- `leaf⇒⊥` only `areq-of⁺`, so ≈137 lines were live-but-dead.
--
-- *** THE RULING (T11 review's I-4, ponytail): DELETE, not keep. ***  The
-- loose-premise form was a defensible fallback while §6h's record was only a
-- design; once the record has a type and an acceptance probe, the fallback is a
-- second statement of the same proof that a successor must keep in sync by hand.
-- What §2e recorded and §2f now carries: the inventory of the leaf's seven
-- refutations, and the fact that T9's item (iii) (the `ccArb` exclusion) is
-- RETIRED rather than deferred, because the cell region excludes a rollback
-- payload outright.
--
-- Recoverable at `b6470db` if a successor ever wants the loose-premise shape.

------------------------------------------------------------------------
-- §2f  (T11, round 3) *** THE LEAF OFF THE RECORD — and this is the ACCEPTANCE
-- PROBE for `LiveDrvCSD` §6h's nine fields. ***
--
-- §2e closed the leaf modulo three LOOSE premises; §6h's postscript then showed
-- those three are not hop-local clauses but fields of a `{pp2, pp3}`-guarded
-- record whose entering step is already carried.  This section consumes THAT — so
-- the leaf's whole obligation is now ONE object, and the arm's residual is the
-- record's preservation calculus plus the one `pp3` cone landing (`rwSrv`'s only
-- unbuilt ingredient) plus the carry.
--
-- *** IT TYPECHECKS, WHICH IS THE PROBE: *** the nine fields are exactly what the
-- seven refutations need, in the shapes they need them.  Two of them earn their
-- keep here visibly — `rwEmp`'s DELIBERATELY WIDE conclusion (`ccWdone`/`ccTerm`
-- are killed for free by the carried `CliPost`, which is why widening it to make it
-- preservable costs the consumer nothing) and `cliAwt-post⇒await`, the one-line
-- bridge from the correlations' `CliAwt` conclusion to the position the io ladders
-- want.
------------------------------------------------------------------------

-- *** §2f's FALSIFICATION (T11 fix round), arity-preserving, RED, reverted by
-- string inversion with `git status` verified clean. ***
--
-- (F99  *** THE TWO READER ARMS ARE SEPARATED BY THE CLIENT's POSITION, NOT BY THE
--      PAYLOAD. ***)  `rfw-arms`'s `ccMust` arm closed by `cliAwaitRfw-⊥` — the
--      AWAITING lemma — instead of `cliMustRfw-⊥`.  Both take the same eleven
--      arguments at the same payload, so nothing but the position distinguishes
--      them, and this is the mutation a transcriber reading the two side by side
--      would make.
--      *** RED ***: `LiveRelayCS.agda:735.75-78: [UnequalTerms] NS.ccMust !=
--      NS.ccAwait of type NS.CScPos … when checking that the expression hmu has
--      type coarsenCSc (…dnCScOf _ l (toSys r)) ≡ …`, EXIT=42.  What it
--      establishes: `rwRfw`'s disjunction is load-bearing — an unread rollforward
--      admits TWO client positions and each has its OWN row (`ceqCSc04` from
--      `ccAwait`, `ceqCSc07` from `ccMust`), so collapsing the two arms is a type
--      error rather than a silently-weaker proof.  Re-aiming note: F99 dies if
--      `LiveSrvOpen` §8's two rollforward arms are ever merged into one
--      position-generic lemma — in which case the merged lemma is a new family and
--      wants its own guard.

-- the leaf, from the record alone
dnRfw⇒leaf : (l : TwoLegs) (r : RState) (b : Block₃)
           → relayOf l (toSys r) ≡ producing b pp3
           → broken (med (toSys r)) (dnLink l) ≡ false
           → LDC.DnRfwC (coarsenCSs (dnCSsOf l (toSys r))) (cellCSDn l (toSys r))
                        (LDC.dnCScC l (toSys r)) (phOf l (toSys r))
                        (relayOf l (toSys r))
           → LDC.DrvCliD l (toSys r) → phOf l (toSys r) ≡ cp1
           → isStable (radec r ∖ hidden blkA) → ⊥
dnRfw⇒leaf l r b eq hb rw cpl hph sta = cell-arms (LDC.rwCell rw)
  where
  post : LDC.CliPost (LDC.dnCScC l (toSys r))
  post = cpl cp1 hph
  -- the server's region, with the relay's phase reduced to the arm's own
  srv : LDC.SrvRfw (coarsenCSs (dnCSsOf l (toSys r)))
  srv = subst (λ z → LDC.SrvAtRfw z (coarsenCSs (dnCSsOf l (toSys r)))) eq (LDC.rwSrv rw)
  -- the `empty` cell at `csIdle`: `rwEmp`'s TWO answers, one refuted by a move and
  -- one by the carried region.
  --
  -- *** (T11b) TWO ARMS DELETED, and the record is why. ***  `rwEmp` used to
  -- conclude four positions; §6i narrowed it to two, because with the carried
  -- token's `InCp03` refuting node D's `cdDone` hop the client can never reach
  -- `ccWdone` (nor `ccTerm` behind it) inside the guard.  The two deleted arms were
  -- `subst LDC.CliPost` one-liners — killed for free by the carried `CliPost`, which
  -- is exactly why the round-3 map could afford the width in the first place
  consumed-arms : (Σ[ ht ∈ Header × Tip ] (LDC.dnCScC l (toSys r) ≡ NS.ccArf ht))
                  ⊎ (LDC.dnCScC l (toSys r) ≡ NS.ccIdle) → ⊥
  consumed-arms (inj₁ (ht , hcf)) =
    LDC.cliArf-cp1-⊥ l r (cblkOf l (toSys r)) (proj₁ ht) (proj₂ ht) hcf hph refl sta
  consumed-arms (inj₂ hci) = subst LDC.CliPost hci post
  -- … and over the server's two positions
  empty-arms : cellCSDn l (toSys r) ≡ empty
             → (coarsenCSs (dnCSsOf l (toSys r)) ≡ NS.csIdle)
               ⊎ (Σ[ ht ∈ Header × Tip ]
                    (coarsenCSs (dnCSsOf l (toSys r)) ≡ NS.csWrf ht))
             → ⊥
  -- (T11b) `rwEmp`'s antecedent is `CellPreQ` since §6i (the drain class needs it),
  -- so the `empty` equation is injected rather than passed
  empty-arms he (inj₁ hidl)      = consumed-arms (LDC.rwEmp rw (inj₁ he) hidl)
  empty-arms he (inj₂ (ht , hw)) =
    srvWrf-⊥ l r (proj₁ ht) (proj₂ ht) hb hw he sta
  -- the unread rollforward, over the two client positions its correlation leaves
  rfw-arms : (t : Time) (md : Mode) (ln : Length) (h : Header) (tp : Tip)
           → cellCSDn l (toSys r) ≡ full (t , md , ln , chainSync (MsgCSRollForward h tp))
           → CliAwt (LDC.dnCScC l (toSys r)) ⊎ (LDC.dnCScC l (toSys r) ≡ NS.ccMust) → ⊥
  rfw-arms t md ln h tp hf (inj₁ haw) =
    cliAwaitRfw-⊥ l r t md ln h tp hb
      (LDC.cliAwt-post⇒await (LDC.dnCScC l (toSys r)) haw post) hf sta
  rfw-arms t md ln h tp hf (inj₂ hmu) = cliMustRfw-⊥ l r t md ln h tp hb hmu hf sta
  -- the four cell arms
  cell-arms : LDC.CellRfw (cellCSDn l (toSys r)) → ⊥
  cell-arms (inj₁ he) =
    empty-arms he (LDC.srvRfw-cases (coarsenCSs (dnCSsOf l (toSys r))) srv)
  cell-arms (inj₂ (inj₁ (x , hd))) = cellDrainCS-⊥ l r x hb hd sta
  cell-arms (inj₂ (inj₂ (inj₁ har))) =
    cliAwaitAr-⊥ l r (proj₁ har) (proj₁ (proj₂ har)) (proj₁ (proj₂ (proj₂ har))) hb
      (LDC.cliAwt-post⇒await (LDC.dnCScC l (toSys r)) (LDC.rwAr rw har) post)
      (proj₂ (proj₂ (proj₂ har))) sta
  cell-arms (inj₂ (inj₂ (inj₂ hrf))) =
    rfw-arms (proj₁ (proj₂ (proj₂ hrf))) (proj₁ (proj₂ (proj₂ (proj₂ hrf))))
      (proj₁ (proj₂ (proj₂ (proj₂ (proj₂ hrf))))) (proj₁ hrf) (proj₁ (proj₂ hrf))
      (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ hrf))))) (LDC.rwRfw rw hrf)

-- *** THE ARM's EQUATION AGAINST THE RECORD — the statement a discharge supplies.
-- ***  TWO NEW carried objects — `LiveDrvBFD.BFFresh` and §6h's `DnRfwC`, the pair
-- the ninth `LegJointU` factor is to carry — BESIDE the already-carried
-- `LDC.DrvCliD` (`LegJointU`'s seventh factor, `DnJoint = DnFresh × DrvCliD`), the
-- down link's unbrokenness and `isStable`.  (T11 review's M-2: the earlier
-- "two carried objects and nothing else" omitted `DrvCliD`, whose plumbing already
-- exists — the substance is "two NEW objects", not "two premises")
areq-of⁺⁺ : (l : TwoLegs) (r : RState)
          → broken (med (toSys r)) (dnLink l) ≡ false
          → LBFD.BFFresh l (toSys r) → LDC.DrvCliD l (toSys r)
          → isStable (radec r ∖ hidden blkA)
          → (b : Block₃) → relayOf l (toSys r) ≡ producing b pp3
          → LDC.DnRfwC (coarsenCSs (dnCSsOf l (toSys r))) (cellCSDn l (toSys r))
                       (LDC.dnCScC l (toSys r)) (phOf l (toSys r))
                       (relayOf l (toSys r))
          → Σ[ rg ∈ ChainRange ] (coarsenBFs (dnSrv l (toSys r)) ≡ NS.bsAreq rg)
areq-of⁺⁺ l r hb fresh cpl sta b eq rw =
  areq-of l r hb fresh cpl sta
    (λ _ h1 → dnRfw⇒leaf l r b eq hb rw cpl h1 sta) b eq

------------------------------------------------------------------------
-- §3  *** THE SPLIT IS EXACT. ***  Recomposition AND both projections.
--
-- `coAt-split-at` alone would only show the two halves are SUFFICIENT for `CoAt`;
-- a `CSAt` that said `⊤` everywhere would satisfy it just as well.  The two
-- projections are what make the split faithful in the other direction: together
-- the three say `CoAt l s x` and `CSAt l s x × BFAt l s x` are interderivable at
-- every one of the seventeen shapes, so the split moves no obligation and
-- invents none.  That is the property a T3c-style follow-on needs, because it is
-- what licenses discharging the two halves INDEPENDENTLY.
------------------------------------------------------------------------

-- *** (T2) THE `pp5` SHARPENING, AS ONE NAMED STEP. ***  The carried coupling pins
-- the down server to `{bsWsb, bsStream}`; the residual's clause is the singleton
-- `≡ bsStream`; and what closes the gap is the refutation of `bsWsb`, which is a
-- STABILITY fact (`LiveSrvOpen.srvWsb-⊥`) and therefore travels as a premise of the
-- recomposition rather than as part of the invariant.  Named rather than inlined
-- because a `with` on the region would abstract a type mentioning an imported
-- `blkA`-parameterised predicate (the module rule).
region⇒stream : (l : TwoLegs) (s : SysState)
              → ¬ (coarsenBFs (dnSrv l s) ≡ NS.bsWsb)
              → (coarsenBFs (dnSrv l s) ≡ NS.bsWsb)
                ⊎ (coarsenBFs (dnSrv l s) ≡ NS.bsStream)
              → coarsenBFs (dnSrv l s) ≡ NS.bsStream
region⇒stream l s nw (inj₁ w)  = ⊥-elim (nw w)
region⇒stream l s nw (inj₂ st) = st

-- (T6d) the leg's down-hop CS server is the SAME node field under two names: the
-- accessor this module reads (`LiveRelayOpen.dnCSs`) and the one the ChainSync channel
-- invariant states its facts at (`LiveChanCS.dnCSsOf`).  Both dispatch on the leg, so
-- at a VARIABLE leg neither reduces and the two forms are not convertible — this is
-- the two-clause bridge, and it is why `csWar-⊥`'s pin is `subst`ed rather than passed
dnCSs-is-of : (l : TwoLegs) (s : SysState) → dnCSs l s ≡ dnCSsOf l s
dnCSs-is-of legBD s = refl
dnCSs-is-of legCD s = refl

-- *** (T6d) THE `pp2` SHARPENING, AS ONE NAMED STEP — `region⇒stream`'s exact twin on
-- the ChainSync axis. ***  The carried coupling pins the down CS server to
-- `{csWar, csMust}`; the residual's clause is the singleton `≡ csMust`; and what
-- closes the gap is the refutation of `csWar`, a STABILITY fact
-- (`LiveSrvOpen.csWar-⊥`) which therefore travels as a premise of the recomposition
-- rather than as part of the invariant.  Named for `region⇒stream`'s reason (a `with`
-- on the region would abstract a type mentioning an imported `blkA`-parameterised
-- predicate).
csRegion⇒must : (l : TwoLegs) (s : SysState)
              → ¬ (coarsenCSs (dnCSs l s) ≡ NS.csWar)
              → (coarsenCSs (dnCSs l s) ≡ NS.csWar)
                ⊎ (coarsenCSs (dnCSs l s) ≡ NS.csMust)
              → coarsenCSs (dnCSs l s) ≡ NS.csMust
csRegion⇒must l s ncw (inj₁ w)  = ⊥-elim (ncw w)
csRegion⇒must l s ncw (inj₂ mu) = mu

-- *** (T8c-iii) THE `csIdle` EXCLUSION BUNDLE — ONE premise, not five (the banked
-- option (3)). ***  §1's re-review trigger fires here: this IS a third unconditional
-- premise on the recomposition.  It is bundled into a single record so the signature
-- grows by ONE argument, and the trigger's own consequence is paid in the same commit
-- (the two consumer-less `-ws′` corollaries below are DELETED, as their note required).
--
-- Every field is a SysState-level fact and every consumer already holds what proves it:
-- the carried pair off `LiveChanJoin.dnJoint-of`, and the four refutations from
-- `LiveSrvOpen` §6 (`cellDrainCS-⊥`, `cellReqCS-⊥`, `cliWreqCS-⊥`) plus `LiveDrvCSD`
-- §3's `cliIdle-cp0-⊥`, each of which wants only the leg's dn-link unbrokenness and
-- `isStable` — exactly what the two `bsWsb`/`csWar` refutations already want.
record CsIdleExcl (l : TwoLegs) (s : SysState) : Set where
  constructor mkCsIdleExcl
  field
    ceJoint : LDC.DnJoint l s
    ceDrain : Σ[ x ∈ Payload ] (cellCSDn l s ≡ draining x) → ⊥
    ceRead  : coarsenCSs (dnCSsOf l s) ≡ NS.csIdle
            → LDC.ReqOnly (cellCSDn l s) → ⊥
    ceWrite : cellCSDn l s ≡ empty → LDC.dnCScC l s ≡ NS.ccWreq → ⊥
    ceSync  : LDC.dnCScC l s ≡ NS.ccIdle → phOf l s ≡ cp0 → ⊥
open CsIdleExcl public

-- *** (T8c-iii) THE CS HALF IS INHABITED BY CONSTRUCTION. ***  Every one of `CSAt`'s
-- seventeen clauses is `⊤` now, so the residual is a theorem rather than an obligation
-- — this is the object `csRes` used to be, and its retirement is exactly this lemma
-- existing.  The seventeen clauses are kept (rather than collapsing `CSAt` to `⊤`)
-- because they are the record of WHICH arm left WHEN, and because a new `CPPh`
-- constructor must stay a coverage error here
csAt-triv : (l : TwoLegs) (s : SysState) (x : CPPh) → CSAt l s x
csAt-triv l s (consuming _ cp0) = tt
csAt-triv l s (consuming _ cp1) = tt
csAt-triv l s (consuming _ cp2) = tt
csAt-triv l s (consuming _ cp3) = tt
csAt-triv l s (consuming _ cp4) = tt
csAt-triv l s (consuming _ cp5) = tt
csAt-triv l s (consuming _ cp6) = tt
csAt-triv l s (producing _ pp0) = tt
csAt-triv l s (producing _ pp1) = tt
csAt-triv l s (producing _ pp2) = tt
csAt-triv l s (producing _ pp3) = tt
csAt-triv l s (producing _ pp4) = tt
csAt-triv l s (producing _ pp5) = tt
csAt-triv l s (producing _ pp6) = tt
csAt-triv l s (producing _ pp7) = tt
csAt-triv l s (producing _ pp8) = tt
csAt-triv l s (producing _ pp9) = tt

-- … at the driver's own phase
csResidual-triv : (l : TwoLegs) (s : SysState) → CSResidual l s
csResidual-triv l s = csAt-triv l s (relayOf l s)

-- *** (T11h) … AND THE BF HALF's OWN, now that its last funded clause is discharged.
-- ***  `csAt-triv`'s exact twin, and it exists for the same reason: this is the object
-- `bfRes` used to be, and its retirement is this lemma existing.  The seventeen clauses
-- are kept for `csAt-triv`'s two reasons (the record of which arm left when, and a new
-- `CPPh` constructor staying a coverage error)
bfAt-triv : (l : TwoLegs) (s : SysState) (x : CPPh) → BFAt l s x
bfAt-triv l s (consuming _ cp0) = tt
bfAt-triv l s (consuming _ cp1) = tt
bfAt-triv l s (consuming _ cp2) = tt
bfAt-triv l s (consuming _ cp3) = tt
bfAt-triv l s (consuming _ cp4) = tt
bfAt-triv l s (consuming _ cp5) = tt
bfAt-triv l s (consuming _ cp6) = tt
bfAt-triv l s (producing _ pp0) = tt
bfAt-triv l s (producing _ pp1) = tt
bfAt-triv l s (producing _ pp2) = tt
bfAt-triv l s (producing _ pp3) = tt
bfAt-triv l s (producing _ pp4) = tt
bfAt-triv l s (producing _ pp5) = tt
bfAt-triv l s (producing _ pp6) = tt
bfAt-triv l s (producing _ pp7) = tt
bfAt-triv l s (producing _ pp8) = tt
bfAt-triv l s (producing _ pp9) = tt

-- … at the driver's own phase
bfResidual-triv : (l : TwoLegs) (s : SysState) → BFResidual l s
bfResidual-triv l s = bfAt-triv l s (relayOf l s)

-- the two halves RECOMPOSE the co-position requirement — *** (T1) PLUS THE CARRIED
-- COUPLING, and at the driver's OWN phase. ***
--
-- The two new premises are exactly what the `pp4` discharge costs: `LiveDrvBF`'s
-- field is an IMPLICATION off `relayOf l s`, so filling `CoAt`'s `pp4` clause needs
-- the phase equation that fires it.  `relayCo-from` below supplies it by `refl`,
-- which is why no consumer ever sees the extra argument as an obligation.  Note the
-- `pp4` clause now IGNORES its `BFAt` argument — the arm is a theorem, and a
-- coupling-free version of this lemma does not typecheck (F12).
--
-- *** (T2) THE `bsWsb` REFUTATION IS AN UNCONDITIONAL PREMISE, AND ONLY `pp5` READS
-- IT. ***  All seventeen clauses take it; sixteen ignore it.  That is harmless at
-- every consumer this module has (all four hold the witness off the window and the
-- carried `ChanDn`), and it keeps the signature uniform — but it makes the
-- recomposition unusable at a CS-ONLY call site that has no down-server fact at all.
-- If T3/T4 wants CS-only recomposition, the premise wants to move INSIDE the `pp5`
-- clause (as a Π over the region there); that is a three-line change now and a wider
-- one later.  A simplification candidate, not a defect (review M-3).
-- *** (T6d) AND THE `csWar` REFUTATION IS A SECOND UNCONDITIONAL PREMISE. ***  It
-- compounds the note above exactly: all seventeen clauses take it and sixteen ignore
-- it, and it is harmless at every consumer this module has (all four now hold the
-- CARRIED `ChanCSDn` beside the carried `ChanDn`).  If a CS-only or a BF-only
-- recomposition is ever wanted, BOTH premises want to move inside their own clause as
-- a Π over the region there — one three-line change each, and the shapes are already
-- named (`region⇒stream`, `csRegion⇒must`).
-- *** (T7) THE COUNT IS STILL TWO, AND IT IS NOW STABLE FOR THE REST OF THE CAMPAIGN.
-- *** The T6d review §4(b) DEFERRED the refactor on the ground that no remaining
-- residual arm is a region — `cp5` is a POSITION (`≡ ccIdle`), `cp6`/`pp0` are positions
-- (`≡ csAreq`), `cp4` is a position (`≡ bcIdle`) and `pp3` is a Σ over `ChainRange` — so
-- no third sharpening refutation could arrive.  `cp5` landed at T7 and added NONE, which
-- is the first confirmation of that ruling against a real arm.  *** RE-REVIEW TRIGGER,
-- recorded here as the ruling asked: pay the refactor at the FIRST of (a) a genuine
-- CS-only or BF-only recomposition call site, or (b) a THIRD unconditional premise being
-- proposed. *** Until one of those, this signature stays uniform.
-- *** (T10) THE RE-REVIEW TRIGGER FIRES A SECOND TIME, AND IS PAID. ***  §1's ruling
-- said: pay the refactor at the FIRST of (a) a CS-only or BF-only recomposition call
-- site, or (b) a THIRD unconditional premise being proposed.  (b) fired at T8c-iii and
-- was paid by BUNDLING; the `cp4` arm proposes a FOURTH, and the ruled payment is the
-- per-clause Π shape instead — so the three unconditional premises become ONE
-- PER-PHASE requirement, `Sharp`, which is `⊤` at the twelve clauses that need
-- nothing and exactly the needed fact at the five that do.
--
-- WHAT THIS BUYS, concretely: a CS-only or BF-only caller now supplies only its own
-- phase's requirement, and a new arm's sharpening lands in ONE clause instead of on
-- all seventeen.  WHAT IT COSTS: a uniform caller has to dispatch, which is
-- `sharp-all` below — one 17-clause builder, written once.
Sharp : TwoLegs → SysState → CPPh → Set
Sharp l s (consuming _ cp0) = ⊤
Sharp l s (consuming _ cp1) = ⊤
Sharp l s (consuming _ cp2) = ⊤
Sharp l s (consuming _ cp3) = ⊤
-- (T10) the `cp4` arm's own requirement IS its equation, proved by §2c's `upIdle-of`
-- at the two stability-scoped consumers (§4) and nowhere else
Sharp l s (consuming _ cp4) = coarsenBFc (upClient l s) ≡ NS.bcIdle
Sharp l s (consuming _ cp5) = ⊤
-- (T8c-iii) the `csIdle` exclusion bundle, now at the TWO clauses that read it
Sharp l s (consuming _ cp6) = CsIdleExcl l s
Sharp l s (producing _ pp0) = CsIdleExcl l s
Sharp l s (producing _ pp1) = ⊤
-- (T6d) the CS region's stability refutation, at the ONE clause that reads it
Sharp l s (producing _ pp2) = ¬ (coarsenCSs (dnCSs l s) ≡ NS.csWar)
-- (T11h) the `pp3` arm's own requirement IS its equation — `cp4`'s shape exactly,
-- proved by `areq-of⁺⁺` at the two stability-scoped consumers (§4) and nowhere else
Sharp l s (producing _ pp3) = Σ[ rg ∈ ChainRange ] (coarsenBFs (dnSrv l s) ≡ NS.bsAreq rg)
Sharp l s (producing _ pp4) = ⊤
-- (T2) … and the BF region's, likewise
Sharp l s (producing _ pp5) = ¬ (coarsenBFs (dnSrv l s) ≡ NS.bsWsb)
Sharp l s (producing _ pp6) = ⊤
Sharp l s (producing _ pp7) = ⊤
Sharp l s (producing _ pp8) = ⊤
Sharp l s (producing _ pp9) = ⊤

-- … and the uniform builder, for a caller that holds all four facts and does not know
-- the phase (both of §4's consumers are of that kind).  The `relayOf l s ≡ x` argument
-- is what lets the `cp4` clause instantiate its guard
sharp-all : (l : TwoLegs) (s : SysState) (x : CPPh) → relayOf l s ≡ x
          → ¬ (coarsenBFs (dnSrv l s) ≡ NS.bsWsb)
          → ¬ (coarsenCSs (dnCSs l s) ≡ NS.csWar)
          → CsIdleExcl l s
          → ((b : Block₃) → relayOf l s ≡ consuming b cp4
             → coarsenBFc (upClient l s) ≡ NS.bcIdle)
          -- (T11h) … and the `pp3` arm's, as a Π over its own guard for the `cp4`
          -- argument's reason exactly
          → ((b : Block₃) → relayOf l s ≡ producing b pp3
             → Σ[ rg ∈ ChainRange ] (coarsenBFs (dnSrv l s) ≡ NS.bsAreq rg))
          → Sharp l s x
sharp-all l s (consuming _ cp0) _  _  _   _  _  _  = tt
sharp-all l s (consuming _ cp1) _  _  _   _  _  _  = tt
sharp-all l s (consuming _ cp2) _  _  _   _  _  _  = tt
sharp-all l s (consuming _ cp3) _  _  _   _  _  _  = tt
sharp-all l s (consuming b cp4) eq _  _   _  ui _  = ui b eq
sharp-all l s (consuming _ cp5) _  _  _   _  _  _  = tt
sharp-all l s (consuming _ cp6) _  _  _   ex _  _  = ex
sharp-all l s (producing _ pp0) _  _  _   ex _  _  = ex
sharp-all l s (producing _ pp1) _  _  _   _  _  _  = tt
sharp-all l s (producing _ pp2) _  _  ncw _  _  _  = ncw
sharp-all l s (producing b pp3) eq _  _   _  _  ai = ai b eq
sharp-all l s (producing _ pp4) _  _  _   _  _  _  = tt
sharp-all l s (producing _ pp5) _  nw _   _  _  _  = nw
sharp-all l s (producing _ pp6) _  _  _   _  _  _  = tt
sharp-all l s (producing _ pp7) _  _  _   _  _  _  = tt
sharp-all l s (producing _ pp8) _  _  _   _  _  _  = tt
sharp-all l s (producing _ pp9) _  _  _   _  _  _  = tt

coAt-split-at : (l : TwoLegs) (s : SysState) (x : CPPh) → relayOf l s ≡ x
              → LDB.DrvBF l s
              -- *** (T10) THE THREE UNCONDITIONAL PREMISES ARE GONE — this is the
              -- ruled payment. ***  Each clause reads its OWN requirement, and the
              -- twelve that need none read `tt`
              → Sharp l s x
              → CSAt l s x → BFAt l s x → CoAt l s x
coAt-split-at l s (consuming _ cp0) _ _ _  _ _ = tt
coAt-split-at l s (consuming _ cp1) _ _ _  _ _ = tt
coAt-split-at l s (consuming _ cp2) _ _ _  _ _ = tt
coAt-split-at l s (consuming _ cp3) _ _ _  _ _ = tt
-- *** (T10) THE SEVENTH DISCHARGED ARM, and the first on the UP hop: `CoAt`'s `cp4`
-- clause off §2c's equation, delivered through this clause's OWN `Sharp`.  Like the
-- other six it no longer reads its `BFAt` argument — F89 (§10) says so
coAt-split-at l s (consuming _ cp4) _ _ sh _ _ = sh
-- (T7) THE FIFTH DISCHARGED ARM, and the first on the CONSUME side: `CoAt`'s `cp5`
-- clause off the carried coupling, with NO sharpening — `ccIdle` is a position, so this
-- clause is `pp1`'s shape and not `pp2`'s.  Like the other four it no longer reads its
-- `CSAt` argument — F47 is the mutation that says so
coAt-split-at l s (consuming b cp5) eq db _  _ _ = LDB.drvCS-at-cp5 l s b eq db
-- *** (T8c-iii) THE FIFTH AND SIXTH DISCHARGED ARMS — and the only two of the six
-- whose equation is DERIVED here rather than read off `DrvCp`. ***  The carried pair
-- gives the freshness clause and node D's coupling; the guard is free at each arm's own
-- sub-phase (`relayFresh-cp6`/`-pp0`); the four exclusions come off the bundle; and
-- `dnFresh⇒areq` is the sharpening.  The `subst` is the `dnCSs`/`dnCSsOf` bridge §3's
-- own `dnCSs-is-of` exists for.  Like the other four, these clauses no longer read
-- their `CSAt` argument — F80/F81 are the mutations that say so
coAt-split-at l s (consuming b cp6) eq _  ex _ _ =
  subst (λ z → coarsenCSs z ≡ NS.csAreq) (sym (dnCSs-is-of l s))
    (LDC.dnFresh⇒areq l s (LDC.relayFresh-cp6 l s b eq)
      (LDC.dnJoint⇒fresh l s (ceJoint ex)) (LDC.dnJoint⇒cpl l s (ceJoint ex))
      (ceDrain ex) (ceRead ex) (ceWrite ex) (ceSync ex))
coAt-split-at l s (producing b pp0) eq _  ex _ _ =
  subst (λ z → coarsenCSs z ≡ NS.csAreq) (sym (dnCSs-is-of l s))
    (LDC.dnFresh⇒areq l s (LDC.relayFresh-pp0 l s b eq)
      (LDC.dnJoint⇒fresh l s (ceJoint ex)) (LDC.dnJoint⇒cpl l s (ceJoint ex))
      (ceDrain ex) (ceRead ex) (ceWrite ex) (ceSync ex))
-- (T5) THE THIRD DISCHARGED ARM, and the first on the ChainSync axis: `CoAt`'s `pp1`
-- clause off the carried coupling.  Like `pp4`'s and `pp5`'s it no longer reads its
-- `CSAt` argument — F26 is the mutation that says so
coAt-split-at l s (producing b pp1) eq db _  _ _ = LDB.drvCS-at-pp1 l s b eq db
-- (T6d) THE FOURTH DISCHARGED ARM, and the second on the ChainSync axis: `CoAt`'s
-- `pp2` clause off the carried REGION sharpened by the stability refutation of
-- `csWar`.  Like the other three it no longer reads its `CSAt` argument — F43 says so
coAt-split-at l s (producing b pp2) eq db ncw _ _ =
  csRegion⇒must l s ncw (LDB.drvCS-at-pp2 l s b eq db)
-- *** (T11h) THE EIGHTH DISCHARGED ARM, and the LAST: `CoAt`'s `pp3` clause off
-- `areq-of⁺⁺`, delivered through this clause's OWN `Sharp`.  Like the other seven it no
-- longer reads its `BFAt` argument — and with it the BF half is EMPTY ***
coAt-split-at l s (producing _ pp3) _ _ sh _ _ = sh
-- (T1) THE FIRST DISCHARGED ARM: `CoAt`'s `pp4` clause, off the carried coupling
coAt-split-at l s (producing b pp4) eq db _  _ _ = LDB.drvBF-at-pp4 l s b eq db
-- (T2) THE SECOND: `CoAt`'s `pp5` clause, off the carried REGION sharpened by the
-- stability refutation of `bsWsb`.  Like `pp4`'s, it no longer reads its `BFAt`
-- argument — F18 is the mutation that says so.
coAt-split-at l s (producing b pp5) eq db nw  _ _ =
  region⇒stream l s nw (LDB.drvBF-at-pp5 l s b eq db)
coAt-split-at l s (producing _ pp6) _ _ _  _ _ = tt
coAt-split-at l s (producing _ pp7) _ _ _  _ _ = tt
coAt-split-at l s (producing _ pp8) _ _ _  _ _ = tt
coAt-split-at l s (producing _ pp9) _ _ _  _ _ = tt

-- … and the requirement PROJECTS onto its ChainSync half (nothing invented)
coAt⇒cs : (l : TwoLegs) (s : SysState) (x : CPPh) → CoAt l s x → CSAt l s x
coAt⇒cs l s (consuming _ cp0) _  = tt
coAt⇒cs l s (consuming _ cp1) _  = tt
coAt⇒cs l s (consuming _ cp2) _  = tt
coAt⇒cs l s (consuming _ cp3) _  = tt
coAt⇒cs l s (consuming _ cp4) _  = tt
-- (T7) the `cp5` arm has left the CS half as well, so the projection is `tt` there —
-- and with it the half's only CLIENT slot
coAt⇒cs l s (consuming _ cp5) _  = tt
-- (T8c-iii) … and the last two arms have left the CS half, so the projection is `tt`
-- at all seventeen shapes and the half is EMPTY
coAt⇒cs l s (consuming _ cp6) _  = tt
coAt⇒cs l s (producing _ pp0) _  = tt
-- (T5) the `pp1` arm left the CS half, so the projection has nothing to say there
coAt⇒cs l s (producing _ pp1) _  = tt
-- (T6d) … and the `pp2` arm has left it too
coAt⇒cs l s (producing _ pp2) _  = tt
coAt⇒cs l s (producing _ pp3) _  = tt
coAt⇒cs l s (producing _ pp4) _  = tt
coAt⇒cs l s (producing _ pp5) _  = tt
coAt⇒cs l s (producing _ pp6) _  = tt
coAt⇒cs l s (producing _ pp7) _  = tt
coAt⇒cs l s (producing _ pp8) _  = tt
coAt⇒cs l s (producing _ pp9) _  = tt

-- … and onto its BlockFetch half
coAt⇒bf : (l : TwoLegs) (s : SysState) (x : CPPh) → CoAt l s x → BFAt l s x
coAt⇒bf l s (consuming _ cp0) _  = tt
coAt⇒bf l s (consuming _ cp1) _  = tt
coAt⇒bf l s (consuming _ cp2) _  = tt
coAt⇒bf l s (consuming _ cp3) _  = tt
-- (T10) the `cp4` arm has left the half, so the projection has nothing to say there
coAt⇒bf l s (consuming _ cp4) _  = tt
coAt⇒bf l s (consuming _ cp5) _  = tt
coAt⇒bf l s (consuming _ cp6) _  = tt
coAt⇒bf l s (producing _ pp0) _  = tt
coAt⇒bf l s (producing _ pp1) _  = tt
coAt⇒bf l s (producing _ pp2) _  = tt
-- (T11h) … and the `pp3` arm has left the half too, so the projection is `tt` at all
-- seventeen shapes and the BF half is EMPTY — `csAt-triv`'s situation one axis over
coAt⇒bf l s (producing _ pp3) _  = tt
-- (T1)/(T2) the `pp4` and `pp5` arms left the half, so the projection has nothing
-- to say at either
coAt⇒bf l s (producing _ pp4) _  = tt
coAt⇒bf l s (producing _ pp5) _  = tt
coAt⇒bf l s (producing _ pp6) _  = tt
coAt⇒bf l s (producing _ pp7) _  = tt
coAt⇒bf l s (producing _ pp8) _  = tt
coAt⇒bf l s (producing _ pp9) _  = tt

-- the recomposition at the relay driver's actual phase — the `refl` is what
-- discharges (T1)'s phase premise, so this signature carries only the COUPLING
relayCo-from : (l : TwoLegs) (s : SysState)
             → LDB.DrvBF l s → ¬ (coarsenBFs (dnSrv l s) ≡ NS.bsWsb)
             -- (T6d) … and the CS region's own refutation beside it
             → ¬ (coarsenCSs (dnCSs l s) ≡ NS.csWar)
             -- (T8c-iii) … and the `csIdle` exclusion bundle.  *** THE CS RESIDUAL
             -- ARGUMENT IS GONE — that is the retirement: `csAt-triv` supplies it, so no
             -- caller passes one and `LivenessProof.Premises` loses `csRes`. ***
             → CsIdleExcl l s
             -- *** (T10) … and the `cp4` arm's equation, as a Π over its own guard. ***
             -- This is where the arm's discharge enters: §4's two consumers hold the
             -- up-hop facts `upIdle-of` wants, and NOTHING here is a new premise —
             -- `BFResidual` below LOST the `cp4` equation in the same commit
             → ((b : Block₃) → relayOf l s ≡ consuming b cp4
                → coarsenBFc (upClient l s) ≡ NS.bcIdle)
             -- *** (T11h) … and the `pp3` arm's equation, as a Π over its own guard —
             -- the `cp4` argument's shape exactly.  *** AND THE `BFResidual` ARGUMENT IS
             -- GONE — that is the discharge: `bfAt-triv` supplies it, so no caller passes
             -- one and `LivenessProof.Premises.bfRes` funds nothing. ***
             → ((b : Block₃) → relayOf l s ≡ producing b pp3
                → Σ[ rg ∈ ChainRange ] (coarsenBFs (dnSrv l s) ≡ NS.bsAreq rg))
             → RelayCo l s
relayCo-from l s db nw ncw ex ui ai =
  coAt-split-at l s (relayOf l s) refl db
    (sharp-all l s (relayOf l s) refl nw ncw ex ui ai) (csResidual-triv l s)
    (bfResidual-triv l s)

-- … and its two projections, at the same phase
relayCo⇒cs : (l : TwoLegs) (s : SysState) → RelayCo l s → CSResidual l s
relayCo⇒cs l s = coAt⇒cs l s (relayOf l s)

relayCo⇒bf : (l : TwoLegs) (s : SysState) → RelayCo l s → BFResidual l s
relayCo⇒bf l s = coAt⇒bf l s (relayOf l s)

------------------------------------------------------------------------
-- §4  THE api FACTS RESTATED MODULO THE SPLIT — `isStable`-scoped throughout.
--
-- The shapes mirror `LiveRelayOpen` §6e one-for-one (`-s` scoped by stability,
-- `-ws` scoped by the window as well), with its ONE residual argument replaced
-- by TWO.  Both are scoped by the same witness, which is the point: the
-- consumer's `isStable` is handed to each half separately, so a discharge of
-- either half is usable on its own without touching the other's premise.
--
-- WHY BOTH HALVES ARE STILL PREMISES   <<< SUPERSEDED T8c-iii: only the BF half is;
-- see (b) >>>.  Because §5's finding is that the BF half
-- is not dischargeable from `ChanLeg`.  When it becomes one, the replacement is
-- a one-line edit at each of these four sites   <<< SUPERSEDED T8c-iii: TWO sites; see
-- (d) >>> — drop the `fbf` argument and
-- apply the discharge lemma — and NOTHING downstream changes, because
-- `LiveStableOffer`'s `parked-at` / `parked-of` / `stabR-final` take
-- `InFlightOpen` as an ARGUMENT (`:1581`, `:1630`, `:1693`).
-- *** RE-DERIVED AT TASK 5: *** `LivenessProof.Premises` no longer carries
-- `ifoBD`/`ifoCD` at all, nor any channel field — its THREE fields are `cellCp3` and
-- the two halves BELOW (`csRes`/`bfRes`)   <<< SUPERSEDED T8c-iii: TWO fields, and
-- `csRes` does not exist — see (c) in this section's T8c-iii postscript >>>,
-- `LiveChanJoin` carrying the whole
-- `ChanLeg` in the FSim's `Rel`, and
-- `LivenessProof.ifo-of` (`:432`; `:297-314` was the pre-T12 reading) BUILDS both
-- `InFlightOpen` records, feeding
-- `relayOpen-in-s′`/`-out-s′` the two scoped halves directly.  So the four sites
-- below are now the ONLY consumers of the split, which makes the one-line
-- replacement above even more local than when this note was first written.
-- *** AND (T1) EXERCISED IT, PER ARM RATHER THAN PER HALF. ***  The prediction was
-- right about the SHAPE and wrong about the GRANULARITY: an arm discharges without
-- its half doing so, and the edit is not "drop the `fbf` argument" but "ADD the
-- carried coupling in front of it" — one binder at each of the four sites, and the
-- arm leaves `BFAt` (§2).  `ifo-of` supplies the coupling off the joint invariant
-- it already destructures, so it is NOT a new premise: `Premises` still has its
-- three fields, and only `bfRes`'s TYPE shrank.  Nothing downstream changed, exactly
-- as the note above predicted.
-- *** (T6d) THE SAME PATTERN, A SECOND BINDER, AND STILL NO NEW PREMISE. ***  The
-- `pp2` discharge adds `ChanCSDn` at each of the four sites — the leg's DOWN-hop
-- ChainSync channel invariant — and `LivenessProof.ifo-of` reads it off the join's
-- SIXTH trailing factor, exactly as it reads `ChanDn` off the fourth.  `Premises`
-- still has its three fields and only `csRes`'s TYPE shrank (four equations to
-- three).  The two `-ws′` forms are updated for uniformity; they remain
-- consumer-less, as they were at T1.
-- *** (T7) AND THE `cp5` DISCHARGE COSTS THESE FOUR SITES NOTHING AT ALL. ***  It is a
-- POSITION, so it needs no sharpening refutation and therefore no new binder: the four
-- signatures below are byte-identical across T7, and `Premises` still has its three
-- fields with only `csRes`'s TYPE shrinking again (three equations to two).  That is the
-- first arm of the five whose discharge did not touch this section.
--
-- *** (T8c-iii) AND NOW THE SECTION'S OWN PREMISE IS GONE.  FIVE PARTICULARS ABOVE ARE
-- FALSE AT HEAD, listed so a reader greps the correction and not the claim: ***
--   (a) "its ONE residual argument replaced by TWO" — there is ONE again: the CS half is
--       DISCHARGED, so only `fbf` remains (plus the carried pair, which is not a premise);
--   (b) "WHY BOTH HALVES ARE STILL PREMISES" — only the BF half is.  §5's finding stands
--       for it; the CS half left by the route §1 and `LiveDrvCSD` §8 describe;
--   (c) "its THREE fields are `cellCp3` and the two halves BELOW (`csRes`/`bfRes`)" —
--       `Premises` has TWO fields and `csRes` DOES NOT EXIST;
--   (d) "a one-line edit at each of these four sites" — the CS discharge was not
--       one-line and there are no longer four sites: TWO, because the two `-ws′` forms
--       were DELETED (the deletion paragraph is ~70 lines below, at §4's tail);
--   (e) "the four sites below are now the ONLY consumers of the split" — the split has
--       one half left, and its consumers are the `-s′` pair alone.
-- *** WHAT DID HOLD: *** the T1/T6d prediction about GRANULARITY and about binders not
-- being premises held a third time — the `cp6`/`pp0` discharge adds `LiveDrvCSD.DnJoint`
-- at each remaining site and `LivenessProof.ifo-of` reads it off the join's SEVENTH
-- trailing factor, exactly as it reads the coupling off the fifth and `ChanCSDn` off the
-- sixth.  What did NOT hold is the premise-count prediction: this discharge is the one
-- that could not move into `LiveDrvBF.DrvCp`, so §3 took a THIRD unconditional premise
-- (the bundled `CsIdleExcl`) — and that is what fired the `-ws′` deletion trigger.
-- *** (T12) THE SECTION'S SUBJECT NO LONGER EXISTS.  Everything above about "the BF
-- half is still a premise", about `fbf`, and about `Premises`' field count is HISTORY:
-- `pp3` was discharged at T11h (§3's `Sharp`, off the carried `LiveDrvBFD.BFFresh`),
-- `BFAt` is `⊤` at all seventeen shapes, `bfRes` was retired at T12 and `Premises` has
-- ONE field, `cellCp3` (SUPERSEDED IN PLACE AT THE CELLCP3 WINDOW: ZERO fields —
-- `cellCp3` is a theorem, `LiveChanJoin.cellCp3-of`).  The T1/T6d/T8c-iii prediction about GRANULARITY held a FOURTH
-- and final time: the discharge added a carried binder, not a premise, and the two
-- signatures below take `BFFresh` where they took `fbf`. ***
------------------------------------------------------------------------

-- the CONSUME-tail arm, with (T1) the CARRIED coupling in front — NOT a premise:
-- `LivenessProof.ifo-of` reads it off the joint invariant it already holds.
-- (SUPERSEDED IN PLACE: this read "with the two halves of the residual required
-- separately and each only where the consumer asks".  Neither half is a premise now —
-- `csRes` retired at T8c-iii, `bfRes` at T12 — and what these two take instead is the
-- CARRIED `LiveDrvBFD.BFFresh`.)
relayOpen-in-s′ : (l : TwoLegs) (r : RState)
                -- *** (T10) THE UP LINK's UNBROKENNESS, and the up hop's own facts. ***
                -- The `cp4` arm's refutations are moves of the UP medium, so the two
                -- relay positions' antecedent widened to both links
                -- (`LiveStableOffer.InFlightOpen`); `parked-at` already held both
                → broken (med (toSys r)) (upLink l) ≡ false
                → broken (med (toSys r)) (dnLink l) ≡ false
                -- (T10) the up-hop channel invariant — `LivenessProof.ifo-of` already
                -- computes it (`ivU`) for the two up-hop fields
                → ChanUp l (toSys r)
                → ChanDn l (toSys r)
                -- (T6d) … and the leg's DOWN-hop ChainSync channel invariant, which
                -- `LivenessProof.ifo-of` reads off the join's SIXTH trailing factor
                → ChanCSDn l (toSys r)
                → LDB.DrvBF l (toSys r)
                -- *** (T8c-iii) THE CS RESIDUAL PARAMETER IS GONE — the retirement. ***
                -- In its place the CARRIED pair, which `LivenessProof.ifo-of` reads off
                -- the join's SEVENTH trailing factor exactly as it reads `db` off the
                -- fifth.  It is NOT stability-scoped, because it is an invariant
                -- *** (T10) … and the UP hop's carried pair beside it — the join's
                -- EIGHTH factor — plus the token, which is `LegJoint`'s first
                -- component.  Both are CARRIED, so neither is a new premise; they are
                -- what `upIdle-of` turns into the `cp4` equation ***
                → LDBA.UpJoint l (toSys r) → PipeInv l (toSys r)
                → LDC.DnJoint l (toSys r)
                -- *** (T11h) THE BF RESIDUAL PARAMETER IS GONE — the discharge.  In its place the
                -- CARRIED freshness clause, which `LivenessProof.ifo-of` reads off the join's FIFTH
                -- factor's THIRD half exactly as it reads `db` off its first.  Like the carried pair it
                -- is NOT stability-scoped, because it is an invariant
                → LBFD.BFFresh l (toSys r)
                → RefutedAt l lpRelayIn blkA r
relayOpen-in-s′ l r hbU hb ivU ivD ivCS db upj pinv dnj fresh at sta =
  relayOpen-in l r
    (relayCo-from l (toSys r) db (λ w → srvWsb-⊥ l r hb ivD w sta)
      (λ w → csWar-⊥ l r hb ivCS
               (trans (cong coarsenCSs (sym (dnCSs-is-of l (toSys r)))) w) sta)
    (mkCsIdleExcl dnj
      -- (1) the drain τ, (2) the server's own read, (3) node D's client's write and
      -- (4) the api sync — `LiveSrvOpen` §6's three plus `LiveDrvCSD` §3's, each
      -- wanting only this leg's dn-link unbrokenness and `sta`
      (λ dr → cellDrainCS-⊥ l r (proj₁ dr) hb (proj₂ dr) sta)
      (λ hidl rq → cellReqCS-⊥ l r (proj₁ rq) (proj₁ (proj₂ rq))
                     (proj₁ (proj₂ (proj₂ rq))) hb hidl
                     (proj₂ (proj₂ (proj₂ rq))) sta)
      (λ he hcw → cliWreqCS-⊥ l r hb he hcw sta)
      (λ hci hph → LDC.cliIdle-cp0-⊥ l r (cblkOf l (toSys r)) hci hph refl sta))
      -- (T10) the `cp4` arm's equation, off §2c and the carried pair
      (upIdle-of l r hbU ivU upj pinv sta)
      -- (T11h) … and the `pp3` arm's equation, off the CARRIED freshness clause plus node
      -- D's coupling and §6h's record; the guard is free at the arm's own sub-phase
      (λ b eq → areq-of⁺⁺ l r hb fresh (LDC.dnJoint⇒cpl l (toSys r) dnj) sta b eq
                  (LDC.dnJoint⇒rfw l (toSys r) dnj
                     (LDC.relayRfw-pp3 l (toSys r) b eq))))
    at sta

-- … and the PRODUCE-tail arm
relayOpen-out-s′ : (l : TwoLegs) (r : RState)
                 -- (T10) the up link's unbrokenness and the up-hop invariant (see the
                 -- `-in-s′` twin)
                 → broken (med (toSys r)) (upLink l) ≡ false
                 → broken (med (toSys r)) (dnLink l) ≡ false
                 → ChanUp l (toSys r)
                 → ChanDn l (toSys r)
                 -- (T6d) … and the CS twin
                 → ChanCSDn l (toSys r)
                 → LDB.DrvBF l (toSys r)
                 -- *** (T8c-iii) THE CS RESIDUAL PARAMETER IS GONE — the retirement;
                 -- the CARRIED pair takes its place (see the `-in-s′` twin)
                 -- (T10) … and the up hop's carried pair plus the token (see the
                 -- `-in-s′` twin)
                 → LDBA.UpJoint l (toSys r) → PipeInv l (toSys r)
                 → LDC.DnJoint l (toSys r)
                 -- *** (T11h) THE BF RESIDUAL PARAMETER IS GONE — the discharge.  In its place the
                 -- CARRIED freshness clause, which `LivenessProof.ifo-of` reads off the join's FIFTH
                 -- factor's THIRD half exactly as it reads `db` off its first.  Like the carried pair it
                 -- is NOT stability-scoped, because it is an invariant
                 → LBFD.BFFresh l (toSys r)
                 → RefutedAt l lpRelayOut blkA r
relayOpen-out-s′ l r hbU hb ivU ivD ivCS db upj pinv dnj fresh at sta =
  relayOpen-out l r
    (relayCo-from l (toSys r) db (λ w → srvWsb-⊥ l r hb ivD w sta)
      (λ w → csWar-⊥ l r hb ivCS
               (trans (cong coarsenCSs (sym (dnCSs-is-of l (toSys r)))) w) sta)
    (mkCsIdleExcl dnj
      -- (1) the drain τ, (2) the server's own read, (3) node D's client's write and
      -- (4) the api sync — `LiveSrvOpen` §6's three plus `LiveDrvCSD` §3's, each
      -- wanting only this leg's dn-link unbrokenness and `sta`
      (λ dr → cellDrainCS-⊥ l r (proj₁ dr) hb (proj₂ dr) sta)
      (λ hidl rq → cellReqCS-⊥ l r (proj₁ rq) (proj₁ (proj₂ rq))
                     (proj₁ (proj₂ (proj₂ rq))) hb hidl
                     (proj₂ (proj₂ (proj₂ rq))) sta)
      (λ he hcw → cliWreqCS-⊥ l r hb he hcw sta)
      (λ hci hph → LDC.cliIdle-cp0-⊥ l r (cblkOf l (toSys r)) hci hph refl sta))
      -- (T10) the `cp4` arm's equation, off §2c and the carried pair
      (upIdle-of l r hbU ivU upj pinv sta)
      -- (T11h) … and the `pp3` arm's equation, off the CARRIED freshness clause plus node
      -- D's coupling and §6h's record; the guard is free at the arm's own sub-phase
      (λ b eq → areq-of⁺⁺ l r hb fresh (LDC.dnJoint⇒cpl l (toSys r) dnj) sta b eq
                  (LDC.dnJoint⇒rfw l (toSys r) dnj
                     (LDC.relayRfw-pp3 l (toSys r) b eq))))
    at sta

-- *** (T8c-iii) THE TWO WINDOW-SCOPED COROLLARIES ARE DELETED, and their own note
-- required it. ***  `relayOpen-in-ws′` / `-out-ws′` were kept at T6d as a documented
-- intended shape, with an explicit re-review trigger: *** "delete them in that task's
-- FIRST commit if either a THIRD unconditional premise ever lands on §3's
-- `coAt-split-at`, or the assembly's uniform shape is abandoned." ***  The `cp6`/`pp0`
-- discharge lands exactly that third premise (`CsIdleExcl`), so the trigger fires and
-- the ruling is paid here rather than deferred.  They had been CONSUMER-LESS since T1
-- (`LivenessProof` uses the `-s′` pair), so nothing downstream moves; the design record
-- they carried is this paragraph, and `LiveCellOpen`'s §4 cross-reference is updated to
-- point at it.

------------------------------------------------------------------------
-- §5  *** WHY THE BLOCKFETCH HALF IS *NOT* DISCHARGEABLE FROM `ChanLeg` —
-- MACHINE-CHECKED, NOT ARGUED. ***
--
-- The E2 route this task implements was chartered on the claim that the four BF
-- arms "discharge from `ChanUp`'s client place and `ChanDn`'s server place",
-- because `cp4`'s `upClient` is `ChanUp`'s THIRD place and `pp3`/`pp4`/`pp5`'s
-- `dnSrv` is `ChanDn`'s FIRST place (`LiveChanInv.agda:1199-1204`) and `ChanLeg`
-- is fully proved (base `:1429`, frame `:1415-1421`, per-step preservation
-- `:1406-1408`).  The slot-naming half of that is exactly right.  The INFERENCE
-- half is false, and the four lemmas below refute it as theorems rather than
-- disputing it as prose.
--
-- THE REASON, IN ONE LINE: every one of `ChanInv`'s five fields has a SERVER-or-
-- CELL antecedent and a CLIENT conclusion (`cvStr`/`cvPre`/`cvReq`/`cvQui`) or a
-- CELL antecedent and a server-REGION conclusion (`cvBlk`) — `:380-388`.  So the
-- invariant constrains no server POSITION at all (killing `pp3`/`pp4`/`pp5`), and
-- constrains the client only from a server-or-cell antecedent that a
-- relay-DRIVER position does not supply (killing `cp4`).
--
-- WHAT THESE FOUR LEMMAS DO AND DO NOT SHOW.  They show that the channel
-- invariant AT ITS OWN THREE PLACES, with no further antecedent, implies none of
-- the four equations — i.e. the chartered inference is unavailable, uniformly in
-- the other two places.  They do NOT show that no discharge exists: a discharge
-- that also reads the relay DRIVER's phase remains logically open.  That object
-- is a DRIVER-to-PEER coupling, which `LiveRelayOpen` §7 prices as its item (b)
-- and which no proved invariant in this development supplies — the two candidates
-- in that direction, `LiveTokenExcl.UpChainCp3`/`DnChainCp3` (`:256-262`), are
-- themselves unproved PARKED premises, and both are occupancy-antecedent rather
-- than driver-antecedent.  §6 turns that into T3c's inventory.
--
-- AND NOTE WHAT `chanInv-pre-empty` KILLS.  The obvious retreat from "the exact
-- position" is "the server's REGION" — weaken `pp3`/`pp4`/`pp5` to `SrvPre`/
-- `SrvStr` membership and discharge the rest by exhibiting an enabled io move.
-- That retreat is also unavailable from `ChanDn` alone: at one and the same cell
-- and client (`empty`, `bcBusy`) the invariant admits both a pre-region server
-- (`bsWsb`) and a server in neither region (`bsIdle`), so it pins the region no
-- more than it pins the position.
------------------------------------------------------------------------

-- the invariant at an IDLE server, an EMPTY cell and an AWAITING client — the
-- `chanInv-init` configuration with the client moved off `bcIdle` (every
-- antecedent is still uninhabited except `cvPre`'s, whose server is not pre)
-- (T10) … and its two new clauses are uninhabited-antecedent as well: `empty` is no
-- unread `MsgStartBatch` and `bcBusy` is not in the streaming region.  The witness
-- SURVIVES the sixth and seventh fields, which is the machine check that neither
-- narrows the blindness §5 records
chanInv-idle-busy : ChanInv NS.bsIdle empty NS.bcBusy
chanInv-idle-busy =
  mkChan (λ ()) (λ { (_ , _ , _ , _ , ()) }) (λ ())
         (λ ()) (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) }) (λ ())

-- … and at a PRE-region server with the same cell and client: `cvPre` is
-- discharged by the client's own region and `cvQui` by the empty cell.
-- *** (T2) NOTE WHAT THIS WITNESS NOW COSTS. ***  `cvQui`'s strengthening
-- (`CellPreQ`, `LiveChanInv` §2) makes the EMPTY-cell witness cheaper — `inj₁ refl`
-- — and the FULL-cell one IMPOSSIBLE: `ChanInv bsWsb (full (rrPayload r)) bcBusy`,
-- the instance the campaign's gate verification machine-checked as inhabited under
-- the old five clauses, is now uninhabitable.  That is exactly the state the `pp5`
-- ladder had to exclude, and excluding it in the INVARIANT is what T2 did instead of
-- paying for a sixth field.
chanInv-pre-empty : ChanInv NS.bsWsb empty NS.bcBusy
chanInv-pre-empty =
  mkChan (λ ()) (λ { (_ , _ , _ , _ , ()) }) (λ _ → tt)
         (λ _ → inj₁ refl) (λ { (_ , _ , _ , _ , ()) })
         (λ { (_ , _ , _ , ()) }) (λ ())

-- the four position distinctions the refutations need
bsIdle≢bsBusy : ¬ (NS.bsIdle ≡ NS.bsBusy)
bsIdle≢bsBusy ()

bsIdle≢bsStream : ¬ (NS.bsIdle ≡ NS.bsStream)
bsIdle≢bsStream ()

bsIdle≢bsAreq : (rg : ChainRange) → ¬ (NS.bsIdle ≡ NS.bsAreq rg)
bsIdle≢bsAreq rg ()

bcBusy≢bcIdle : ¬ (NS.bcBusy ≡ NS.bcIdle)
bcBusy≢bcIdle ()

-- *** (cp4)  `ChanInv` does not imply the `cp4` equation. ***  Its client place
-- may be `bcBusy` while the other two places are `chanInv-init`'s
chanInv-⊮-cp4 : ¬ ((sa : NS.BFsPos) (ph : CopyPhase) (ca : NS.BFcPos)
                   → ChanInv sa ph ca → ca ≡ NS.bcIdle)
chanInv-⊮-cp4 f = bcBusy≢bcIdle (f NS.bsIdle empty NS.bcBusy chanInv-idle-busy)

-- *** (pp3)  … nor the `pp3` equation *** — no field of `ChanInv` concludes
-- anything about the server's position, so `bsIdle` satisfies it
chanInv-⊮-pp3 : ¬ ((sa : NS.BFsPos) (ph : CopyPhase) (ca : NS.BFcPos)
                   → ChanInv sa ph ca → Σ[ rg ∈ ChainRange ] (sa ≡ NS.bsAreq rg))
chanInv-⊮-pp3 f =
  bsIdle≢bsAreq (proj₁ (f NS.bsIdle empty NS.bcIdle chanInv-init))
                (proj₂ (f NS.bsIdle empty NS.bcIdle chanInv-init))

-- *** (pp4)  … nor the `pp4` equation *** — STILL TRUE AND STILL LOAD-BEARING
-- AFTER (T1): what discharges `pp4` is not `ChanInv` but `LiveDrvBF.DrvBF`, whose
-- antecedent is the relay DRIVER's phase.  This refutation is exactly why the
-- campaign had to build that object rather than read the arm off the channel
-- invariant, and F10 below is its own falsification.
chanInv-⊮-pp4 : ¬ ((sa : NS.BFsPos) (ph : CopyPhase) (ca : NS.BFcPos)
                   → ChanInv sa ph ca → sa ≡ NS.bsBusy)
chanInv-⊮-pp4 f = bsIdle≢bsBusy (f NS.bsIdle empty NS.bcIdle chanInv-init)

-- *** (pp5)  … nor the `pp5` equation *** — STILL TRUE AND STILL LOAD-BEARING AFTER
-- (T2), for `pp4`'s reason and one more: what discharges `pp5` is the coupling's
-- REGION plus a STABILITY refutation, and neither is a consequence of `ChanInv` at its
-- own three places.  The strengthened `cvQui` is what makes the stability half
-- available, but it still says nothing about the server's POSITION.
chanInv-⊮-pp5 : ¬ ((sa : NS.BFsPos) (ph : CopyPhase) (ca : NS.BFcPos)
                   → ChanInv sa ph ca → sa ≡ NS.bsStream)
chanInv-⊮-pp5 f = bsIdle≢bsStream (f NS.bsIdle empty NS.bcIdle chanInv-init)

-- *** THE REGION RETREAT IS ALSO UNAVAILABLE. ***  One cell and one client, two
-- servers in different regions: whatever `ChanInv` says at `(empty , bcBusy)`, it
-- says of `bsIdle` and of `bsWsb` alike, so it separates no server region either
chanInv-region-blind : Σ[ sa ∈ NS.BFsPos ] Σ[ sa′ ∈ NS.BFsPos ]
                         (ChanInv sa empty NS.bcBusy
                          × (ChanInv sa′ empty NS.bcBusy × (¬ (sa ≡ sa′))))
chanInv-region-blind =
  NS.bsIdle , NS.bsWsb , chanInv-idle-busy , chanInv-pre-empty , λ ()

-- *** THE SAME THING SAID ON THE CHARTERED OBJECT ITSELF. ***  `ChanLeg` is not
-- merely uninformative about the server's position in the abstract: it holds
-- PROVABLY at `initial` (`LiveChanInv.chanLeg-init`), and at `initial` the leg's
-- down-hop BF server is idle — that is exactly why `chanLeg-init` typechecks as
-- `chanInv-init , chanInv-init`, which forces `coarsenBFs (dnSrv l initial)` to
-- reduce to `NS.bsIdle`.  So all three `dnSrv` equations FAIL at a state where
-- `ChanLeg` holds.
--
-- READ THE SCOPE OF THESE THREE EXACTLY.  They refute the UNCONDITIONAL reading
-- ("`ChanLeg` gives the equation"), which is the reading under which the four
-- arms would have been a corollary layer.  They do NOT refute the CONDITIONAL
-- reading ("`ChanLeg` plus the relay driver's own phase gives it") — at `initial`
-- the relay driver is not at `pp3`/`pp4`/`pp5` at all, so `initial` says nothing
-- about that.  The conditional reading is precisely the DRIVER-to-PEER coupling,
-- and refuting or proving IT needs a witness state with the driver pinned, i.e.
-- reachability machinery this development does not carry at the state level.
-- That is the honest boundary of this section, and §6 is written to it.

-- (pp3)  `ChanLeg` does not pin the down-hop server's position …
chanLeg-⊮-pp3 : ¬ ((l : TwoLegs) (s : SysState) → ChanLeg l s
                   → Σ[ rg ∈ ChainRange ] (coarsenBFs (dnSrv l s) ≡ NS.bsAreq rg))
chanLeg-⊮-pp3 f =
  bsIdle≢bsAreq (proj₁ (f legBD initial (chanLeg-init legBD)))
                (proj₂ (f legBD initial (chanLeg-init legBD)))

-- (pp4)  … nor to `bsBusy` …
chanLeg-⊮-pp4 : ¬ ((l : TwoLegs) (s : SysState) → ChanLeg l s
                   → coarsenBFs (dnSrv l s) ≡ NS.bsBusy)
chanLeg-⊮-pp4 f = bsIdle≢bsBusy (f legBD initial (chanLeg-init legBD))

-- (pp5)  … nor to `bsStream`
chanLeg-⊮-pp5 : ¬ ((l : TwoLegs) (s : SysState) → ChanLeg l s
                   → coarsenBFs (dnSrv l s) ≡ NS.bsStream)
chanLeg-⊮-pp5 f = bsIdle≢bsStream (f legBD initial (chanLeg-init legBD))

------------------------------------------------------------------------
-- §5b  *** (T9) WHY THE `cp6`/`pp0` FRESHNESS ROUTE DOES NOT TRANSPOSE TO `pp3` —
-- MACHINE-CHECKED, NOT ARGUED.  THE ARM IS STILL A PREMISE, AND THE REASON IS ONE
-- SUB-CASE. ***
--
-- *** THE CLAIM THIS SECTION REFUTES, QUOTED SO IT CANNOT BE REINTRODUCED BY COPY:
-- *** the (T8c) review's BF re-gate, delta 2, read *"`pp3`'s blocker … is therefore
-- NOT the obstruction the gate thought: it is a BF transcription of a landed,
-- carried, guarded object.  `pp3` returns to GO, and its risk class drops from 'new
-- KIND' to 'transcription'"*, and priced the arm at 880-1,530 on that basis.
-- *** THE TRANSCRIPTION HALF IS RIGHT AND THE VERDICT IS WRONG, and the four
-- negatives below are why. ***
--
-- WHAT DOES TRANSPOSE, and it is genuinely cheap — this section is not a NO-GO on
-- the whole route.  The `cp6`/`pp0` machinery has a BlockFetch twin at every piece
-- that lives ON THE DOWN BF HOP:
--   · a guard region `RelayFreshBF` = "the relay has not yet fired `reqBFRange`" =
--     the whole `consuming` half plus `producing _ {pp0 … pp3}` (the emit is
--     `produce`'s FOURTH event, `FourNodeDiamond:205`, and it is what takes the dn
--     BF server off `bsAreq rg` — `bfSnxt (bsAreq r) … reqBFRange ≡ just bsBusy`,
--     `NodeSpecs:531-535`).  `pp3` is INSIDE it, so the guard is free at the arm.
--   · a server half `{bsIdle, bsAreq rg}` (`bsIdle`'s only two rows are wire-reads,
--     `NodeSpecs:588-595`, and the api emit above is the only way out of `bsAreq`);
--   · a client half `{bcIdle, bcWrr rg, bcBusy}` — `bcStream`/`bcAblk`/`bcWcd`/
--     `bcTerm` all need the relay's own `sendBFStartBatch` (`pp4`) or the client's
--     own done, i.e. they are outside the guard.  *** THIS CONJUNCT IS THE SHARED
--     ITEM S-a's CONTENT, AND IT IS NOT A `ChanInv` FIELD: *** the two states the BF
--     re-gate wanted a client-antecedent `ChanInv` clause for — `(bsIdle, empty,
--     bcBusy)` and `(bsIdle, empty, bcStream)` — are excluded HERE, `bcStream` by
--     this conjunct and `bcBusy` by the correlation below.  A hop-generic `ChanInv`
--     field cannot do it: `(bsIdle, empty, bcIdle)` is `chanInv-init` itself, so the
--     exclusion is necessarily GUARDED on the relay's phase and therefore leg-level.
--   · a cell half and a correlation, `DnFreshC`'s shape exactly.
-- Under those, refuting `bsIdle` at `pp3` splits into the same five sub-cases as
-- `dnFresh⇒areq`'s, and THREE of the five are free or nearly so: the correlation
-- kills `bcBusy`, and at `bcIdle` a BF driver-tail coupling pins node D's driver to
-- `{cp0, cp1, cp2}`, of which `cp2` is the api sync the gate verification already
-- costed as cheap and *** `cp0` IS ALREADY A THEOREM — `LiveDrvCSD.cliIdle-cp0-⊥`
-- off the CARRIED `DrvCliD`, which is UNGUARDED and therefore still live at `pp3`.
-- ***
--
-- *** WHAT DOES NOT TRANSPOSE: THE `cp1` SUB-CASE.  It is one leaf of one dispatch,
-- and it carries two objects the campaign has never built. ***
--
-- The configuration is: relay driver at `producing b pp3`, node D's driver at `cp1`,
-- dn BF server `bsIdle`, dn BF cell `empty`, node D's dn BF client `bcIdle`.  Every
-- component of the DOWN BF HOP is move-free there — `bsIdle` has no api row at all
-- so the relay's own `reqBFRange` offer does not fire, `bsIdle`'s two wire-reads need
-- a full cell, `bcIdle`'s two rows are both api (`NodeSpecs:518-524`) and *** node
-- D's driver does not offer either of them at `cp1` (`LiveDrvCSD.consD-cp1-no-brr`,
-- §6d — the family's first BlockFetch member, built for exactly this) ***, and an
-- empty cell has no medium τ.  So the refutation has to come from the CHAINSYNC
-- axis, and that is where the route fails:
--
--   (1) `LiveDrvCSD.DnFresh` IS VACUOUS AT `pp3` — `relayFresh-⊮-pp3` below.  The
--       object the review calls "landed, carried, guarded" is guarded by
--       `RelayFresh`, whose `producing _ pp3` clause is `⊥` BY CONSTRUCTION
--       (`LiveDrvCSD:802-810`), and it has to be: at `pp3` the dn CS server is past
--       `csAreq`, so `SrvFresh` is FALSE there.  The BF twin therefore cannot reuse
--       `DnFresh`'s CS conjuncts under its own wider guard — it needs its own, and
--       its PHASE conjunct is exactly the token's `InCp03` (negative (4)), i.e. NO
--       narrowing at all, where `PhFresh` narrowed `{cp0 … cp3}` to `{cp0, cp1}`.
--   (2) `LiveDrvBF.DrvCp` IS TRIVIAL AT `pp3` — `drvCp-triv-at-pp3` below.  Nothing
--       carried says anything about the relay's OWN dn CS server at `pp3`, so
--       "the CS reply is still in flight" is not available as a fact.
--   (3) THE CARRIED `DrvCliD` LEAVES FIVE CLIENT POSITIONS AT `cp1` —
--       `cliPost-cp1-blind` below.  Its `cp1` clause is the region `CliPost`
--       (`LiveDrvCSD:271-283`), and of its five members only `ccArf ht` has an api
--       row node D's driver offers at `cp1` (`csCnxt (ccArf ht) …
--       recvCSRollforward`, `NodeSpecs:359-363`).  `ccMust` and `ccArb pt` are
--       GENUINELY STUCK on this hop: `ccMust`'s two rows are both wire-reads
--       (`:344-352`) and `ccArb pt`'s only row is `recvCSRollback`, which `consume`
--       never offers (`LiveDrvCSD.consD-no-rb`, §6b(2a), phase-generic).
--   (4) THE TOKEN DOES NOT SEPARATE THEM — `token-⊮-pp3-cp1` below.  At `producing b
--       pp3` the token's relay region is `RelayHas`, which admits it, so the levels
--       `L3`/`L4` are the only ones excluded and every surviving level's D-consumer
--       constraint is `InCp03` — which admits `cp1`.  So `PipeInv` is blind here,
--       exactly as `ChanInv` is blind at §5's three places.
--
-- *** AND THE PIN THAT WOULD CLOSE IT IS FALSE, not merely unbuilt. ***  The obvious
-- repair is a cross-node driver-to-DRIVER clause "relay at `pp3` ⇒ node D past
-- `cp1`".  That clause is UNTRUE: the relay's `pp2 → pp3` step is its own
-- `sendCSRollForward` api sync (`FourNodeDiamond:204`), and at that instant the
-- header has not been written to the wire, let alone read by node D's client or
-- consumed by its driver — so node D is at `cp0` or `cp1` for a whole stretch of
-- states whose relay phase is `pp3`.  The honest obligation at those states is a
-- STABILITY REFUTATION through the ChainSync axis, and it needs, per sub-case:
--
--   (i)   a `DrvCp` clause at `producing _ pp3` pinning the relay's own dn CS server
--         to the post-emit region — a new REGION on the landed coupling, and NOT
--         io-closed (the server's wire-send leaves it), so it needs a sharpening of
--         `region⇒stream`'s kind as well;
--   (ii)  TWO new CS io ladders, POSITIONALLY DISTINCT from the two `LiveIoIntroCS`
--         §1c/§2b built: the relay's dn CS server WRITING and node D's dn CS client
--         READING.  The built pair is node D's client writing and the relay's server
--         reading — the other two directions.  The range's measured per-ladder
--         density is ≈183;
--   (iii) an exclusion of `ccArb pt` — the client never reaches it because `produce`
--         never rolls back, but nothing in the tree says so, and saying it is a new
--         invariant clause with a producer-site cost;
--   (iv)  a node-D api sync at `cp1` for the `ccArf ht` member — the `cliIdle-cp0-⊥`
--         transposition, with the `Header × Tip` value gate that T5's
--         `LiveCSRow.cscRfwLands` already pays.  This one IS cheap.
--
-- Of these, (iv) is a transcription, (i) and (iii) are new objects and (ii) is the
-- same "unbuilt list" item that made T8c 1.81× its band.  *** NONE of (i)-(iv)
-- appears in the review's `pp3` line items P1-P5, which price the BF hop only. ***
-- Re-priced honestly: the BF-hop transposition 380-620 (P1 + P2 + one BF read rung),
-- the `cp1` chain 620-1,080 ((i) 150-300, (ii) 300-450, (iii) 110-230, (iv) 60-100),
-- the carry 180-300, guards 40-80 — *** 1,220-2,080, against a band of 880-1,530 and
-- a STOP of 1,700, at a class of arm whose measured multiplier in this campaign is
-- 1.2-1.8×. ***  It does not fit, and the two new kinds are the reason.
--
-- *** (T11) WHAT THIS SECTION STILL GETS RIGHT AND WHAT IS NOW SUPERSEDED — read
-- this before pricing anything off the inventory above. ***  The four negatives,
-- the leaf's EXISTENCE and the pin's FALSITY are untouched and still the reason
-- the arm needs an object of its own.  What has changed:
--   · *** THE OBJECT EXISTS: `LiveDrvBFD` *** — the BF twin with its OWN wide
--     guard region, its base, its frame, its six step classes, node D's joint BF
--     adjacency and the sharpening `bfFresh⇒areq`.  §2d is its consumer and it
--     proves `BFAt`'s `pp3` clause modulo the leaf.  So "the BF-hop
--     transposition" is DONE, not priced.
--   · *** "TWO new CS io ladders … 300-450" IS SUPERSEDED TWICE OVER: *** the
--     server-WRITE half already existed (T9-verify measured its position instance
--     at 22), and T11 MEASURED the BlockFetch pair of the same two directions at
--     145 net for BOTH (`LiveIoIntro` §10) with rung 1 already banked in the
--     oracle.  Price the remaining CS half — node D's client READING — at that
--     unit, ~75, not at 300-450.
--   · *** "the `cp1` api sync itself, 60-100" IS LANDED *** (`LiveDrvCSD` §6f), and
--     with it ONE of the leaf's five client positions.  `cliPost-cp1-rest` is the
--     machine-checked residual: FOUR positions, not five.
--   · the re-priced band "1,220-2,080" was superseded by the T10 review's
--     1,250-2,210 before this task and is superseded again by its actuals.
-- WHAT IS STILL OPEN, and it is the honest closing set: the relay's own dn CS
-- server region at `pp3` (T9's item (i)), the payload correlation, the one
-- remaining CS io ladder and the `ccArb` exclusion — for THREE of the four
-- surviving positions plus the full-cell case of the fourth.
--
-- WHAT (T9) THEREFORE LANDED, AND WHAT IT DID NOT.  The four negatives below, the
-- family's BlockFetch member (`LiveDrvCSD` §6d) that decides the inventory, and the
-- S-a finding above — S-a is NOT a `ChanInv` field and should not be priced as one.
-- `BFAt`'s `pp3` clause is UNCHANGED and `bfRes` is still a TWO-equation premise.
-- *** (T10) `bfRes` IS NOW A ONE-EQUATION PREMISE — `pp3` alone. ***  The other
-- equation was `cp4`, and §2c discharged it; everything this section says about `pp3`
-- itself is untouched, which is the point: the two arms were never the same problem.
------------------------------------------------------------------------

-- *** (1)  THE CARRIED FRESHNESS CLAUSE IS VACUOUS AT `pp3`. ***  `DnFresh` is a
-- guarded implication and its guard's `pp3` clause is `⊥`, so a consumer at `pp3`
-- can extract NOTHING from `LegJointU`'s seventh factor.  One line, and it is the
-- whole of the difference between the `cp6`/`pp0` route and this one
relayFresh-⊮-pp3 : (b : Block₃) → LDC.RelayFresh (producing b pp3) → ⊥
relayFresh-⊮-pp3 b ()

-- *** (2)  … AND THE CARRIED RELAY COUPLING IS TRIVIAL THERE. ***  `DrvCp`'s `pp3`
-- clause is `⊤`, so nothing carried pins the relay's own dn CS server at the arm's
-- phase.  Stated POSITIVELY (the clause is inhabited by `tt` at any leg and state)
-- because that is the sharper form: it is not that the fact is hard to get, it is
-- that the carried object has no place to keep it
drvCp-triv-at-pp3 : (l : TwoLegs) (s : SysState) (b : Block₃)
                  → LDB.DrvCp l s (producing b pp3)
drvCp-triv-at-pp3 l s b = U.tt

-- *** (3)  … AND THE CARRIED NODE-D COUPLING LEAVES FIVE CLIENT POSITIONS AT `cp1`.
-- ***  All five members of `CliPost` witnessed, the two payload-carrying ones
-- uniformly in their payload.  Only `ccArf ht` has an api partner at `cp1`; `ccMust`
-- and `ccArb pt` are stuck on this hop and must be EXCLUDED, not refuted
cliPost-cp1-blind : LDC.CliPost NS.ccWreq × LDC.CliPost NS.ccAwait
                  × LDC.CliPost NS.ccMust
                  × ((ht : Header × Tip) → LDC.CliPost (NS.ccArf ht))
                  × ((pt : Point × Tip) → LDC.CliPost (NS.ccArb pt))
cliPost-cp1-blind = tt , tt , tt , (λ _ → tt) , (λ _ → tt)

-- *** (4)  … AND THE TOKEN DOES NOT SEPARATE THE RELAY's `pp3` FROM NODE D's `cp1`.
-- ***  `RelayHas` is the token's relay constraint at level `L2` and admits `pp3`;
-- `InCp03` is its D-consumer constraint at every level `L2` admits and it admits
-- `cp1`.  So the pair is consistent with `PipeInv` and the phase exclusion cannot
-- come from there
token-⊮-pp3-cp1 : (b : Block₃) → RelayHas (producing b pp3) × InCp03 cp1
token-⊮-pp3-cp1 b = tt , tt

------------------------------------------------------------------------
-- §5c  *** (T10) THE `cp4` ARM's GUARD CHECK, AND THE TWO FACTS IT TURNS UP. ***
--
-- The T9 lesson is a MANDATORY FIRST STEP for any arm that leans on a carried
-- object: *** evaluate the object's GUARD at the arm's OWN sub-phase before pricing
-- or building anything on it. ***  Done here in writing and machine-checked, for
-- every object the `cp4` route touches.  The four lemmas below are the whole of it;
-- the two verdicts that MATTER are (2) — a POSITIVE, and it retires the item both
-- prior gates called this arm's one genuinely unbuilt kind — and (3), a NEGATIVE
-- that would have cost a wasted route.
--
--   `RelayFresh`  (`LiveDrvCSD`'s freshness guard)  — `⊤` at `consuming _ cp4`,
--                 because its region is the WHOLE consuming half plus `producing _
--                 pp0`.  So node D's freshness clause IS live here, exactly where it
--                 was VACUOUS at `pp3` (§5b(1)).  It is live and it is USELESS: its
--                 four conjuncts are about the leg's DOWN ChainSync hop, and `cp4`
--                 is an equation about the leg's UP BlockFetch hop.  Recorded so a
--                 successor does not read §5b's negative as a general one.
--   `RelayHas`    (the token's relay constraint at level `L2`) — `⊤` at `cp4`,
--                 and `RelayPre`/`RelayFwd` are BOTH `⊥` there, so `L2` is the ONLY
--                 surviving token level and its PRODUCER constraint is `ProdSent`.
--   `RelayPre`    (`LiveLegStep.CellCp3`'s SECOND hypothesis) — `⊥` at `cp4`.
--   `DrvCp`'s `cp4` clause — live (`≡ ccIdle` at the up CS client), and on the
--                 WRONG AXIS: it is the `cp5` chain's third carrier, ChainSync.
--
-- *** (2) IS THE ARM's PIN, AND IT IS FREE. ***  The T8c gate priced C3 — "the `pp6`
-- cross-node driver-to-DRIVER pin, the one genuinely unbuilt kind left" — at 250-550,
-- and the T9 verification re-derived it at 280-620 with the note that the ORDER fact
-- behind it is true (the relay reaches `cp4` only by `recvBFBlock`, so node A must
-- have fired `sendBFBlock`).  *** That order fact is the token's own `L2` clause and
-- has been carried since `PipeInv` was written: *** at `consuming _ cp4` the level
-- computation kills `L0`/`L1` by `RelayPre` and `L3`/`L4` by `RelayFwd`, leaving
-- `L2`, whose producer constraint IS `ProdSent (prodOf l s)` — node A's driver at
-- `pp6` or later on the leg's UP link.  `pipeInv⇒sent-cp4` below is the whole proof.
-- Nothing new is built, nothing is premised: the pin is a PROJECTION of `LegJointU`'s
-- first factor (`LegJoint → PipeInvS → PipeInv⁺ → PipeInv`, the route
-- `LiveDrvCSD` §4's `PipeInv` note already spells out).
--
-- *** (3) IS THE TRAP THE GUARD CHECK EXISTS TO CATCH. ***  The chartered end state
-- was `Premises = {cellCp3}` alone, so `cellCp3` could legitimately be USED as a
-- hypothesis when discharging `bfRes` — it cost nothing at that end state.  (The
-- cellCp3 window has since discharged `cellCp3` too, so the end state is
-- `Premises = {}` and nothing here needs the licence.)  The T9
-- verification tried that route at `pp3` and found it vacuous there because
-- `CellCp3`'s antecedent (`CellFull⁺ b (cellUp …)`, the BLOCK in the cell) is false
-- at `pp3`.  *** At `cp4` it is vacuous for a DIFFERENT reason, one sub-phase-check
-- deeper: `CellCp3`'s two halves each take a SECOND hypothesis, and the up half's is
-- `RelayPre (relayOf l s)` (`LiveLegStep:967-972`, the T8b conditional reshape),
-- which is `⊥` at `cp4`. ***  So the premise supplies nothing here either, and for a
-- reason no reading of the antecedent would have found.  Do not re-derive it.
--
-- *** (T10, the discharge commit) BOTH OBJECTS ARE NOW SUPPLIED — see §2c. ***  What
-- follows is the record of what the arm owed BEFORE the discharge, kept because it is
-- what priced it: the two objects were the up-hop channel invariant's client place and
-- node A's `MsgBatchDone`, and they arrived as `LiveChanInv.ChanUp` (already carried)
-- and the new `LiveDrvBFA.UpJoint` (the join's eighth factor).
-- The two objects the arm therefore still owes are named at §7's `cp4` entry: they
-- are NOT the pin.
------------------------------------------------------------------------

-- *** (1)  THE FRESHNESS GUARD IS LIVE AT `cp4` — the exact contrast with §5b(1). ***
-- `RelayFresh`'s region is the whole consuming half, so the carried clause is
-- extractable here.  It is also on the wrong axis (down ChainSync), which is why the
-- arm cannot use it: the check is about VACUITY, and passing it is not sufficiency
relayFresh-at-cp4 : (b : Block₃) → LDC.RelayFresh (consuming b cp4)
relayFresh-at-cp4 b = tt

-- *** (2)  THE `pp6` PIN, AS A THEOREM OFF THE CARRIED TOKEN. ***  At `consuming b
-- cp4` the token can only be at `L2` — `L0`/`L1` need `RelayPre` and `L3`/`L4` need
-- `RelayFwd`, both `⊥` there — and `L2`'s producer constraint is `ProdSent`.  So
-- "node A has already fired `sendBFBlock` on the leg's up link" is CARRIED, not owed
-- *** RELOCATED (T10, the discharge commit): the definition now stands at §2c, ABOVE
-- §3, because §3's `upIdle-of` consumes it and Agda has no forward definitions.  The
-- statement is byte-identical; only its position moved, so F85 below re-aims at §2c's
-- `L0` clause rather than at this section's.

-- *** (3)  … AND THE `cellCp3` ESCAPE IS VACUOUS AT `cp4`, one hypothesis deeper
-- than the `pp3` instance. ***  The up half of `CellCp3` takes `RelayPre (relayOf l
-- s)` as its second hypothesis and `RelayPre (consuming b cp4)` is `⊥`, so the
-- campaign's one chartered residual premise cannot be leaned on here
relayPre-⊮-cp4 : (b : Block₃) → RelayPre (consuming b cp4) → ⊥
relayPre-⊮-cp4 b ()

-- *** §5c's FALSIFICATION (T10), arity-preserving, RED, reverted. ***
--
-- (F85  THE LEVEL COMPUTATION IS WHAT PRODUCES THE PIN)  `pipeInv⇒sent-cp4`'s `L0`
--      clause RETURNS its producer conjunct (`hp`) instead of refuting the level
--      through `RelayPre` — i.e. it claims the token's LOWEST level would give the
--      pin too, which is the reading under which the arm would not need `cp4`'s own
--      relay region at all.
--      *** RED ***: `LiveRelayCS.agda:1192.48-50: [UnequalTerms] …PipeInv.ProdNotSent
--      blkA (prodOf l s) !=< ProdSent (prodOf l s) … when checking that the
--      expression hp has type ProdSent (prodOf l s)`, EXIT=42.  So the pin is NOT a
--      property of the token as such: it comes from `cp4` killing `L0`/`L1` by
--      `RelayPre` and `L3`/`L4` by `RelayFwd`, which leaves the ONE level whose
--      producer constraint is the SENT one.  Re-aiming note: this mutation dies the
--      moment `prodP L0` stops being `ProdNotSent`.
--
-- *** (4)  … AND THE CARRIED BF COUPLING IS ON THE OTHER AXIS AT `cp4`. ***  `DrvCp`'s
-- `cp4` clause is the `cp5` chain's third CARRIER — the leg's UP-hop CHAINSYNC client
-- at `ccIdle` — so it is live, sharp, and says nothing about the BlockFetch hop the
-- arm's equation is about.  Stated as the projection a consumer would write
drvCp-cs-at-cp4 : (l : TwoLegs) (s : SysState) (b : Block₃)
                → relayOf l s ≡ consuming b cp4
                → LDB.DrvBF l s → coarsenCSc (upCSc l s) ≡ NS.ccIdle
drvCp-cs-at-cp4 l s b eq db = LDB.drvCp-toC4 l s db b eq

------------------------------------------------------------------------
-- §6  *** THE CHAINSYNC RESIDUAL, CLASSIFIED — five equations when this section was
-- written, FOUR since (T5) discharged (ii), THREE since (T6d) discharged (iii), TWO
-- since (T7) discharged (i). ***
-- What a follow-on must prove, per equation, with the table row that fixes it.  The
-- classification is kept WHOLE, (i), (ii) and (iii) included: they are what priced the
-- arms that landed, and (iv) is unchanged by any of the three landings.
--
-- `CSAt` had FIVE clauses carrying FOUR distinct claims at five sub-phases when this
-- was written; since (T7) it has TWO clauses carrying ONE claim at two sub-phases
-- (`cp6` and `pp0` carry the SAME equation — the collapse is definitional,
-- see `LiveRelayOpen` §2), over exactly ONE slot: the leg's down-hop CS SERVER, at ONE
-- position (`csAreq`).  *** The CS half is now a SINGLE claim, and it is item (iv). ***
-- They were NOT instances of one problem; they fell into three structurally different
-- kinds, and the cheap one was cheap for a reason that has nothing to do with a
-- channel invariant:
--
-- (i)  `cp5` — up CS client `≡ ccIdle`.  *** DRIVER-TAIL — AND (T7) DISCHARGED. ***
--      `ccIdle` is left
--      ONLY by the three api sends `csCnxt` gates at that position
--      (`sendCSRequestNext`/`sendCSFindIntersect`/`sendCSDone`,
--      `NodeSpecs.agda:306-314`), every one of which needs the relay's own driver
--      to offer it; and the relay's own `cp1` PUTS the client there, because
--      `csCnxt (ccArf ht) … recvCSRollforward` with the payload matching is
--      `just ccIdle` (`:361-365`).  So no io step and no other node can move this
--      slot: what is needed is a coupling between the relay driver's consume
--      sub-phase and its own up-hop CS client, preserved along the DRIVER's steps
--      only.  NO channel invariant and NO io ladder is involved.
--
--      *** THIS PARAGRAPH'S TWO PREDICTIONS, SCORED AT T7. ***  (a) "NO channel
--      invariant and NO io ladder is involved" — *** RIGHT, and it is why the arm needed
--      no sharpening and added no premise to §3. ***  (b) "the cheapest of the five and
--      the one to fund first" — *** WRONG, twice over, and the correction matters more
--      than the claim did. ***  It was not the cheapest: (ii) was, and (ii) landed two
--      tasks earlier at roughly a third of the price.  Nor should it have been funded
--      first: the arm needs FOUR funded sub-phases (`cp2`-`cp5`, item (ii)'s paragraph
--      below already spotted that), a whole api LANDING family on the CONSUME side
--      (`LiveLegApiCone` §1c⁗/§2b⁗/§1d, THREE new local `decCons` anchors and FOUR new
--      classifier components), a new `DriverExposed⁺` field pair, and three of its four
--      api arms carry a SOURCE PHASE that both landed CS arms escaped.  The one
--      genuine discount was already banked and not by this arm's own task: T5's per-key
--      pin `LiveCSRow.cscRfwLands` and the two `ccIdle` io refutations were built at T5
--      for a consumer that did not yet exist, and they pay the whole of the
--      `Header × Tip` value gate this section's own text flags.
--      What T7 built on top of them: the landing family above, `DrvCp`'s four new
--      clauses with `drvCp-of`'s four new arguments, and one clause of §3.  §1's `cp5`
--      clause is `⊤` now.
--
-- (ii) `pp1` — dn CS server `≡ csCanAwait`.  *** SEQUENTIAL — AND (T5) DISCHARGED.
--      ***  It is exactly the target of `pp0`'s OWN sync: `csSnxt csAreq …
--      reqCSRequestNext ≡ just csCanAwait` (`:428-429`), which is `peer-pp0`'s
--      conclusion verbatim (`LiveRelayOpen:258-267`).  This section called it "the
--      same shape as (i)" and that was RIGHT about the shape and WRONG about the
--      price: `pp1` is entered by ONE row and needs ONE funded sub-phase, while (i)
--      needs FOUR (`cp2`-`cp5`, because the three steps after the client reaches
--      `ccIdle` are BlockFetch api events that do not touch it) — so `pp1` was the
--      cheap arm of the five and (i) is not cheap at all.  What T5 built: the per-key
--      pin (`LiveCSRow` §4b), the cone's `pp1` landing (`LiveLegApiCone` §1c″/§2b″
--      and `DnCsDrv`), owner grant #11's CS-server io channel, and one more clause on
--      the LANDED coupling.  §1's `pp1` clause is `⊤` now.
--
-- (iii) `pp2` — dn CS server `≡ csMust`.  *** SEQUENTIAL PLUS ONE IO HOP — AND (T6d)
--      DISCHARGED. ***  `pp1`'s sync lands the server at `csWar`, not at `csMust`
--      (`csSnxt csCanAwait … sendCSAwaitReply ≡ just csWar`, `:445-446`), and
--      `csWar` reaches `csMust` only by the server's WIRE-SEND of its
--      `MsgCSAwaitReply` (`csSnxt csWar (input …) ≡ just csMust`, `:472-475`).
--      So the honest obligation is "`csMust`, or else the intermediate `csWar`
--      with its wire-send enabled" — and under `isStable` the second disjunct is
--      REFUTABLE rather than premised, provided one has (a) a CS down-hop channel
--      invariant strong enough to say the cell is not blocking the send, and
--      (b) a CS io ladder to fire it.  *** THE PARAGRAPH BELOW SAID "NEITHER EXISTS"
--      AND THAT SENTENCE IS NOW FALSE: *** T6b BUILT both — `LiveChanCS` (the per-hop
--      ChainSync channel invariant, three clauses) and `LiveIoIntroCS` (the CS-keyed
--      medium fold/link/whole-medium ladders, rungs 1-4) — T6c JOINED the invariant to
--      the FSim's `Rel` as `LegJointU`'s sixth trailing factor and built the
--      refutation `LiveSrvOpen.csWar-⊥`, and T6d carried the region and closed the
--      arm.  The shape is `pp5`'s exactly: `LiveDrvBF.DrvCp`'s `pp2` clause is the
--      REGION `{csWar, csMust}`, §3's `csRegion⇒must` sharpens it on the stability
--      refutation, and §1's `pp2` clause is `⊤`.  What made it dearer than (ii): the
--      whole channel layer (1,392 code at T6b) plus grant #12's io-cone CS client
--      family, against (ii)'s one funded sub-phase.
--
-- (iv) `cp6` / `pp0` — dn CS server `≡ csAreq`.  *** CO-PARTY-DRIVEN, AND THE
--      DEEPEST OF THE FIVE. ***  `csAreq` is reached ONLY by the server READING a
--      `MsgCSRequestNext` off the down CS cell (`csSnxt csIdle (output …)
--      MsgCSRequestNext ≡ just csAreq`, `:416-418`).  That message is node D's CS
--      client's, so this equation is not a fact about the relay at all: it needs
--      node D's CS client to have issued the request and the down CS medium to
--      have carried it.  It is therefore in the same territory as the campaign's
--      PARKED `lpDnClient` position, and it is the one arm of the five that a
--      relay-local invariant cannot reach on principle.
--
--      *** (T8) THE SOUNDNESS GATE ON ITEM (iv) — VERDICT: BOTH ARMS ARE SOUND AS
--      SCOPED, AND THE OBLIGATION IS NEITHER VACUOUS NOR WITNESSED-AGAINST. ***
--      The question the gate had to answer BEFORE any funding is whether
--      `isStable ∧ (relay driver at cp6 / pp0) ⇒ dnCSs ≡ csAreq` is TRUE at all
--      — `cp4`'s api arm is on record as FALSE as a plain state invariant, which
--      is why the whole residual is `isStable`-scoped, and node D's driver is not
--      lock-stepped with the relay's.  The answer is derived, position by
--      position, from the two tables and the CARRIED invariant; the inventory:
--
--      NOT VACUOUS.  At `consuming _ cp6` the driver is NOT stuck on a τ: `ret r
--      >>= k` FORCES to `k r` (`CSP.Operators:337-338`), so `consuming b cp6` and
--      `producing b pp0` decode to the SAME tree and both offer `apiCS (dnLink l)
--      hi reqCSRequestNext` (`relay-offer-cp6`/`-pp0` are the same body — the
--      collapse is definitional, no silent step to fire).  (This also re-confirms
--      `cp6`/`pp0` are ONE claim: same tree, same offer, same equation — and the
--      collapse is not merely argued here, it is already MACHINE-CHECKED in the
--      tree, `relay-offer-cp6` being `relay-offer-pp0`'s body verbatim,
--      `LiveRelayOpen:402-404`.)
--
--      *** (T8b) CORRECTION — THE PARAGRAPH ABOVE ESTABLISHES THE ONE-CLAIM HALF,
--      NOT A SATISFIABILITY HALF, and the sentence it used to end with ("so
--      `isStable` is satisfiable at both sub-phases and neither clause is vacuously
--      true") was about the wrong notion. ***  Under the intended discharge the
--      antecedent is in fact UNSATISFIABLE: `CSAt`'s clause composed with
--      `arm-cp6`/`arm-pp0` says "no stable state has the relay's driver at
--      `cp6`/`pp0`" (the arms consume the pin to produce `RefutedAt`).  The verdict
--      is untouched — the obligation is still TRUE and still has to be proved by
--      excluding eleven positions and refuting `csIdle` — but a successor who reads
--      the old sentence as promising a STABLE WITNESS at `cp6`/`pp0` will hunt for
--      something that does not exist.  The correct statement: the clause is a real
--      obligation because its proof route is NON-DEGENERATE (exclusion of eleven
--      plus refutation of `csIdle`), and its composite with the arms is a stability
--      REFUTATION.  One consequence worth recording: the `⊥`-elim route (prove "at
--      `cp6`/`pp0` + `isStable` ⇒ `⊥`" and get the equation ex falso) is an equally
--      valid discharge shape, so T7's "a positive conclusion is dearer than a
--      refutation" pricing note carries no real cost difference on this arm.
--
--      THE THIRTEEN SERVER POSITIONS, split by what closes them (`csSnxt`
--      `:414-490`, `csCnxt` `:304-381`):
--        · `csAreq`  — the goal.
--        · `csIdle`  — REFUTABLE under `isStable`, four sub-cases on the dn CS
--          cell and node D's CS client: `draining` ⇒ `medDrainτCS-dn`; `full` with
--          the request ⇒ the server's own wire READ; `empty` + D's client at
--          `ccWreq` ⇒ the client's write (`medOfferInCS-dn`); `empty` + D's client
--          at `ccIdle` ⇒ *** THE api SYNC INSIDE NODE D ***: `consume`'s head is
--          `apiCS l hi sendCSRequestNext` (`FourNodeDiamond:238-240`), `ccIdle`
--          accepts it (`csCnxt:306-308`), it is hidden by `keptB`'s catch-all
--          (`Spec:115`, `refl`) — the `pp3`-route mechanism, and the intro kit for
--          it is the one node-D object the tree lacks.
--        · the OTHER ELEVEN — `csCanAwait`, `csAfi _`, `csInt`, `csMust`,
--          `csWrf _`, `csWrb _`, `csWar`, `csWif _`, `csWin _`, `csDdone`,
--          `csTerm` — are NOT refutable at `cp6` and MUST BE EXCLUDED, not
--          refuted.  Only `csWar` has a refutation (`LiveSrvOpen.csWar-⊥:471-484`);
--          at `csCanAwait`/`csAfi _`/`csInt` the channel invariant's own
--          `ccQui`/`ccPre` give cell empty-or-draining and a read-only client, and
--          the driver at `cp6` offers only `reqCSRequestNext`, which none of them
--          accepts — a genuinely STUCK configuration, merely unreachable.  *** THE
--          NEGATIVE RESULT OF THE GATE IS THEREFORE NOT A FALSE ARM BUT A SHAPE
--          CONSTRAINT: the exclusion has to be an INVARIANT clause, and the
--          stability refutation may only be asked to close `csIdle`. ***
--
--          *** (T8b) CORRECTION — `csMust` IS NOT ONE OF THOSE THREE, and the reason
--          this bucket used to give for it is a fact the tree contradicts. ***
--          `SrvPre NS.csMust = ⊥` (`LiveChanCS:246`), and `LiveChanCS:231-238`
--          records why it MUST be: falsification F31 (adding `csMust` to `SrvPre`)
--          goes RED at `chan-srvSend`'s `ssAR` arm.  So at `csMust` there is NO cell
--          fact and NO client fact.  The bucket survives and is reinforced: with no
--          cell fact the cell may hold the unread `MsgCSAwaitReply`, in which case
--          node D's client at `ccAwait` could read it (`csMust` would be REFUTABLE,
--          not stuck), while at `(csMust , empty , ccMust)` nothing is enabled and
--          the position is genuinely stuck-but-unreachable.  Either way "exclude, do
--          not refute" is right — but do not go looking for a `ccQui` at `csMust`.
--          Note also that `csAfi`'s non-acceptance is `csSnxt:431-435`, OUTSIDE the
--          `:439-459` range this paragraph's neighbours cite.
--
--          *** (T8b) AND "STUCK" IS SCOPED. ***  The eleven positions are shown to
--          have no enabled move among FOUR components — the relay's dn CS server, the
--          hop's cell, node D's dn CS client and the relay's driver.  The BF axis,
--          the KeepAlive drivers, node A and the up hop are not enumerated, so the
--          honest claim is "not refutable FROM THESE FACTS".
--
--      WHAT MAKES THE EXCLUSION INDUCTIVE (checked against both tables, all six
--      adjacencies): a FOUR-conjunct clause at the relay's consume phases plus
--      `pp0` — dnCSs ∈ {`csIdle`, `csAreq`} × D's dn CS client ∈ {`ccIdle`,
--      `ccWreq`, `ccAwait`} × the dn CS cell ∈ {`empty`, `draining _`, `full`
--      REQUEST} × D's own consume phase ∈ {`cp0`, `cp1`} — each threatening step
--      being refuted by a SIBLING conjunct: the server's two other reads
--      (`csIdle → csAfi`, `csIdle → csDdone`) by the cell conjunct, the client's
--      three reply reads (`ccAwait → ccArf`/`ccArb`/`ccMust`) by the cell
--      conjunct, the client's other two writes (`ccWfi`, `ccWdone`) by the client
--      conjunct, the relay server's five wire-sends by the server conjunct, and
--      D's `cp1 → cp2` by the client conjunct.  Plus ONE correlation the bare
--      conjunction cannot express and `ChanCS` does not have: *** an awaiting
--      client with an idle server has its request UNREAD in the cell ***
--      (`sa ≡ csIdle → CliAwt ca → ReqFull ph`), which is what kills the last
--      sub-case (`csIdle`, `empty`, `ccAwait`).  That clause is inductive for the
--      same reason `ccReq` is: the only step establishing it is the client's own
--      write, and `draining` at (`csIdle`, `ccAwait`) is refuted by its own
--      instance in the predecessor.
--
--      *** (T8b) TWO REPAIRS TO THAT LIST, both from the T8 review, and both
--      load-bearing. ***
--        (I-1)  the cell conjunct must be `full` REQUEST *narrowly* — the cell holds
--               `MsgCSRequestNext` and NOTHING ELSE.  `LiveChanCS.ReqFull` also
--               admits `full (MsgCSFindIntersect ps)` (`:279-281`), and at such a
--               cell the server's `csIdle → csAfi ps` read (`:420-423`) is ENABLED
--               and lands OUTSIDE the region — so the clause with the wide arm is
--               not preservable.  The narrow arm is `LiveDrvCSD.ReqOnly`.
--        (I-2)  the list omits ONE exit step, `csAreq + reqCSRequestNext →
--               csCanAwait` (`csSnxt:428-429`).  No sibling conjunct refutes it and
--               the phase conjunct does not either (that conjunct is about NODE D's
--               phase).  It is refuted ONLY by the arms' own relay-phase antecedent:
--               the step is the `apiES` sync with the RELAY's driver, which the same
--               step moves to `producing b pp1`.  *** CONSEQUENCE: `DnFresh` IS FALSE
--               AS AN UNCONDITIONAL STATE INVARIANT (any ordinary post-emit state is
--               a witness), so the "carry it as a new TRAILING FACTOR" option below
--               is unsound unless the factor is itself PHASE-GUARDED. ***  The
--               landed guard is `LiveDrvCSD.RelayFresh` — the whole `consuming` half
--               plus `producing _ pp0` — and its preservation needs a per-step-class
--               dispatch on the RELAY's phase, not only on node D's.
--
--      *** AND ONE REAL DISCOUNT, FOUND AT THE GATE: THE CROSS-NODE PHASE
--      ORDERING IS ALREADY PAID FOR. ***  `PipeInv`'s token is `Σ[ lvl ] (prodP
--      lvl (prodOf l s) × relayP lvl (relayOf l s) × consP lvl (phOf l s))`
--      (`PipeInv:217-224`), `RelayHas (consuming _ cp6)` and `RelayHas (producing
--      _ pp0)` are `⊤` (`:146`, `:147`) with `RelayPre` `⊥` at both (`:134` for the
--      consume sub-phase, *** `:135` for `producing _ _` ***) and `RelayFwd` `⊥` at
--      both (`:160-161`), so the token is pinned at `L2` and `consP L2 = InCp03`
--      (`:212`) hands over *** node D's consume phase ∈ {cp0 … cp3} ***
--      (`WalkPr:69-76`) for free, from a factor the FSim's `Rel` ALREADY carries.
--      *** (T8b) THE CARRYING ROUTE, EXACTLY (review I-4): `PipeInv` rides
--      `LegJointU`'s FIRST factor and NOT `PipeVal`. ***  `LegJointU = LegJoint ×
--      PipeVal × KAcFrz × ChanLeg` (`LiveChanJoin:242`), `LegJoint = PipeInvS ×
--      LegInv × TokenExcl` (`LiveLegAssembly:221`), `PipeInvS = PipeInv⁺ ×
--      SrvCoupled` (`PipeInvProd:110`), `PipeInv⁺ = PipeInv × Coupled`
--      (`PipeInv:492`) — three projections deep on the first factor.  `PipeVal` is
--      the block-VALUE invariant (`PipeValInv:163-172`) and carries no token, so a
--      successor following a "via `PipeVal`" route would find nothing there.
--      The `cp4` gate priced a "cross-node `pp6` pin" as a new kind; on THIS arm
--      three quarters of it is a projection of a landed invariant, and the fourth
--      conjunct above only has to narrow {cp0 … cp3} to {cp0, cp1}.
--
--      *** (T8b) "UNCHANGED" IS NOT ACCURATE (review M-2), and both changes are
--      improvements. ***  (a) The T6-verify §4 owner decision — WIDEN THE CHANNEL
--      LAYER TO ALL THIRTEEN SERVER POSITIONS — has been REPLACED by a leg-level
--      region clause (`LiveDrvCSD.SrvFresh`); `LiveChanCS` is untouched and stays
--      scoped to its pre region.  (b) §4's first bullet — "the five `csW*` positions
--      ride the layer exactly as `pp2` does" — is CORRECTED by the gate: only
--      `csWar` is in `SrvPre` (`LiveChanCS:249`, against `:247-248` and `:250-251`).
--      With that said:
--
--      THE SUFFICIENT SET IS OTHERWISE THE T6-VERIFY §4 LIST and every
--      ingredient is banked or priced: node D's CS driver-tail coupling (`cp0` ↔
--      `ccIdle` — NOT built), the node-D api-sync INTRO kit (the inversion exists
--      at `LiveLegApiExpose:319-428`, the intro does not; every piece it needs is
--      banked — `aicCSreq` at `SysRoute:145`, the node-D fingerprint at `:1191`,
--      `absBundleG-api-no`, `drvD-{BD,CD}-no`, `lift-api-node-ev`,
--      `apiNodes-whole`, `hiddenMove-⊥`, and `nodeD-offer-BD` `:864-893` as the
--      literal template), the relay `DrvCp` exclusion clauses at the consume
--      phases, and the correlation clause on the CS channel invariant.  *** NO
--      COUNTER-STATE EXISTS inside the carried invariant plus those clauses, and
--      the ONE position the stability argument has to close is `csIdle`. ***
--
-- *** WHAT CHAINSYNC MACHINERY EXISTS, AND WHAT MUST BE BUILT. ***  Re-derived by
-- grep rather than relayed:
--
--   EXISTS.  (1) The four peer offers and their coarsening commutations —
--   `peer-cp5`/`-pp0`/`-pp1`/`-pp2` off `aCSc`/`aCSs` and `ceqCSc03`/`ceqCSs11`/
--   `ceqCSs06`/`ceqCSs07` (`SysOracle_PeerEvCSBF.agda:332-334`, `:680-682`,
--   `:665-667`, `:668-670`).  (2) The node-level bundle lifts
--   `absBundle-CSc-ev`/`absBundle-CSs-ev` (`SysOracle_RouteKaTs`).  (3) The two
--   slot accessors `upCSc`/`dnCSs` and the coarsenings `coarsenCSc`/`coarsenCSs`.
--   (4) The two api sync kits, generic in the event — `LiveRelayOpen` §4.  So the
--   whole api LADDER for the CS half is already banked: T3c needs to build NO
--   ladder, which is the one respect in which the CS half is cheaper than the
--   E2 charter assumed.
--
--   *** (T6d) ERA-SCOPE THE TWO PARAGRAPHS BELOW. ***  They were written before the
--   ChainSync channel layer existed and their items (2) and (3) — "a CHAINSYNC per-hop
--   channel invariant" and "CS io ladders for (iii)" — are BOTH BUILT AND IN THE
--   ENDPOINT CLOSURE (`LiveChanCS`, `LiveIoIntroCS`, joined by `LiveChanJoinCS`).  The
--   closing sentence "the CS channels appear in this development ONLY as things to be
--   excluded, never as things whose readiness is established" is likewise no longer
--   true.  They are kept verbatim as the pricing record they were, not as current
--   fact; item (1) is the only one still open, and only for (i).
--
--   *** (T7) AND ITEM (1) OF "MUST BE BUILT" IS NOW BUILT TOO, SO NOTHING IN THE
--   PARAGRAPH BELOW IS STILL OPEN. ***  Its three items were: (1) a driver-tail coupling
--   for (i) and (ii) — T1 built the object (`LiveDrvBF.DrvCp`, on the BF axis), T5 added
--   (ii)'s clause and T7 added (i)'s, so both named arms are closed; (2) a ChainSync
--   per-hop channel invariant — T6b built it; (3) CS io ladders — T6b built those.  The
--   whole paragraph is now a PRICING RECORD and not a work list.  Its sentence "the CS
--   channels appear in this development ONLY as things to be excluded" was already
--   flagged false at T6d; note additionally that its size estimate for (2) was fair —
--   `LiveChanCS` measured 993 code against `LiveChanInv`'s 888 — and that (1)'s warning
--   about `LiveTokenExcl.UpChainCp3`/`DnChainCp3` was CORRECT and load-bearing: the
--   coupling that landed is driver-antecedent, and neither parked premise was used as a
--   starting point at any of T1/T5/T6d/T7.
--
--   MUST BE BUILT.  (1) A driver-tail coupling for (i) and (ii) — the object the
--   campaign has never proved in this direction, and note that its two nearest
--   relatives are BOTH unproved parked premises (`LiveTokenExcl.UpChainCp3`/
--   `DnChainCp3 :256-262`) and are occupancy-antecedent rather than
--   driver-antecedent, so they are not a starting point.  (2) For (iii) and (iv),
--   a CHAINSYNC per-hop channel invariant, i.e. the `ChanInv` analogue over
--   `(CSsPos , CopyPhase , CScPos)`.  Its tables are strictly larger than
--   BlockFetch's — thirteen `CSsPos` constructors (`NodeSpecs.agda:393-406`)
--   against ten `BFsPos`, twelve `CScPos` (`:284-296`) against seven `BFcPos` —
--   and `LiveChanInv` is 888 code lines for the BlockFetch one.  (3) CS io
--   ladders for (iii): every ladder the campaign banks is keyed at
--   `N2N_BlockFetch`, and the ONLY places `N2N_ChainSync` occurs in the liveness
--   layers are key-DISJOINTNESS frame facts — `cell-no-in-iv`/`cell-no-out-iv`
--   (`LiveIoIntro.agda:294-298`, `:832-836`), which are generic in the cell phase
--   and say nothing about the CS channel's state, and `writeHit-chan`'s CS
--   instances in `LiveLegIoCone`.  The CS channels appear in this development ONLY
--   as things to be excluded, never as things whose readiness is established.
--
-- *** AND THE HONEST BOTTOM LINE FOR A GATE. ***  The CS residual — five equations
-- then, TWO now, and both of them item (iv) — is not one object.  (i) and (ii) are one cheap object (a driver-tail coupling,
-- no channel invariant); (iii) adds a CS channel invariant and a CS io ladder;
-- (iv) adds a claim about NODE D and belongs with the parked `lpDnClient` work.
-- *** (T7) THE PARTITION IS NOW FULLY MEASURED, AND ITS ONE ERROR WAS THE PAIRING. ***
-- Three of the four kinds are discharged, in the order (ii) → (iii) → (i) and NOT in the
-- order this section recommended; the classification's structural distinctions all held,
-- but its cost ordering did not, because it paired (i) with (ii) as "one cheap object"
-- when (i) alone is a four-sub-phase chain on the CONSUME side with its own landing
-- family.  What is LEFT on the ChainSync axis is (iv) ALONE — `cp6`/`pp0`, `≡ csAreq`,
-- node D's CS client's request — and nothing any of the three landings bought unlocks
-- it: it is a claim about ANOTHER NODE, and the only object in the tree pointing at it
-- is the parked `lpDnClient` work.
-- *** (T6d) MEASURED, and the classification's own ordering held: *** (iii) cost the
-- channel layer AND grant #12 AND the landing family, i.e. the three items this
-- paragraph names, in that order and at three separate tasks.  What is LEFT is (i) —
-- the four funded sub-phases `cp2`-`cp5` plus a CS-CLIENT driver-tail arm — and (iv),
-- the node-D claim.  Neither is unlocked by anything (iii) bought except the io cone's
-- CS client family, which grant #12 landed for `cp5` in advance.
-- *** (T5) MEASURED: (ii) ALONE closed, and (i) did NOT come with it. ***  The
-- sentence below is right that neither api fact is unlocked by two arms; what it got
-- wrong is the PAIRING — (i) needs four funded sub-phases and a CS-CLIENT io channel,
-- (ii) needed one and the SERVER channel, so they were never one item.  The rest of
-- the paragraph stands:
-- A follow-on that funds only (i)+(ii) closes two of the five and leaves both api
-- facts premised, because `RefutedAt l lpRelayIn` needs all three of
-- `cp4`/`cp5`/`cp6` and `lpRelayOut` all six of `pp0`-`pp5` — the same reason
-- `LiveRelayOpen` §7's option 3 buys nothing.  The split this module lands is what
-- makes that arithmetic visible; it does not change it.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §7  FALSIFICATIONS — six at first, plus T1's/T2's/T5's/T6d's discharge guards and
-- (T7) F47/F48/F49; all arity-preserving, all RED, all reverted
-- byte-identically (`git diff --stat` verified EMPTY after each).  One per claim this
-- module actually makes.
--
-- *** READ THE RE-AIMING RULE AT THE END OF THIS SECTION BEFORE DISCHARGING ANY FURTHER
-- ARM. ***  It applies to BOTH halves and it has already been needed twice: F7 (CS) went
-- stale at T5/T6d/T7 and F8 (BF) at T2, and neither staleness was visible from the
-- falsification's own green record.  F48 and F49 are the two re-aims.
--
-- (F7  THE VACUITY MODE OF THE CS HALF)  replace `CSAt`'s `consuming _ cp5`
--      clause by `⊤`.
--      *** RED ***: `:217.42-44: [UnequalTerms] Level.Lift lzero ⊤ !=<
--      coarsenCSc (upCSc l s) ≡ NS.ccIdle … when checking that the expression cs
--      has type CoAt l s (consuming x cp5)`, EXIT=42.  So a silently-weakened
--      clause of the CS half is a type error AT `coAt-split-at`, not a weaker
--      theorem — which is what makes `CSAt` a faithful half of `CoAt` rather than
--      a convenient one.  (The name in this record read `coAt-split` until the T7 fix
--      round: the definition has been `coAt-split-at` since the phase argument became
--      explicit, and `relayCo-from` is what instantiates it at `relayOf l s`.)
--      *** (T7) THIS MUTATION IS NO LONGER AVAILABLE AT `cp5` EITHER, AND THAT IS THE
--      DISCHARGE — F8's disposal, verbatim, at the CS half. ***  `CSAt`'s `cp5` clause
--      IS `⊤` now, so there is nothing to weaken there; F47 below is its replacement and
--      it tests the post-discharge property (the arm is a THEOREM, not a weakening).
--      *** AND THE VACUITY MODE OF THE CS HALF IS STILL GUARDED, but the guard has MOVED
--      TWICE and the record must say where it is: F7 was the CS half's ONLY vacuity
--      guard until T5, and T5/T6d/T7 have now emptied three of its five funded clauses.
--      What guards it today is F48 below: F7's mutation RE-AIMED at `consuming _ cp6`,
--      one of the two clauses that remain, and RUN at T7 rather than assumed.  ***
--      Do not read F7's own report as covering the current clause list — read F48's. ***
--
-- (F8  THE VACUITY MODE OF THE BF HALF)  the same at `BFAt`'s `producing _ pp5`.
--      *** RED ***: `:224.42-44: [UnequalTerms] Level.Lift lzero ⊤ !=<
--      coarsenBFs (dnSrv l s) ≡ NS.bsStream …`, EXIT=42.
--      *** (T2) THIS MUTATION IS NO LONGER AVAILABLE AT `pp5`, AND THAT IS THE
--      DISCHARGE. ***  `BFAt`'s `pp5` clause IS `⊤` now, so there is nothing to weaken
--      there; F18 below is its replacement, and it tests the property that matters
--      after a discharge (the arm is a THEOREM, not a weakening).
--      *** (T7 fix round) AND THE SENTENCE THAT USED TO CLOSE THIS RECORD WAS AN
--      ASSERTION, NOT A RUN. ***  It read "*the vacuity mode of the BF half is still
--      guarded at its remaining funded clauses — `consuming _ cp4` and `producing _
--      pp3`*", which recorded where the guard COULD be re-aimed and not that anyone had
--      re-aimed it — so from T2 to T7 the BF half had NO EXECUTED vacuity guard at any
--      live clause, exactly the state the CS half was in before F48.  **Era-scoping a
--      mutation records that it is no longer AVAILABLE; it does not record that the
--      property is still GUARDED, and those are different claims.**  F49 below is the
--      re-aim, RUN at `consuming _ cp4`.  `producing _ pp3` carries a DIFFERENT equation
--      (a Σ over `ChainRange`), so — unlike `cp6`/`pp0`, which carry one equation between
--      them — it is not covered definitionally by F49's run and would need its own.
--
-- (F9  THE `isStable` SCOPE, on the restated fact)  `relayOpen-in-s′` feeds the
--      CS half the POSITION (`fcs at`) in place of the STABILITY WITNESS
--      (`fcs sta`) — same arity, both in scope.  This is `LiveRelayOpen`'s F6 at
--      the split's own consumer.
--      *** RED ***: `:309.51-53: [UnequalTerms] (Σ (RelayIn⁺ blkA blkA (relayOf l
--      (toSys r))) (λ x → ProdSent … × InCp03 …)) !=< (isStable (radec r ∖ hidden
--      blkA))`, EXIT=42.  So the split inherits §6e's scoping intact: nothing else
--      in scope can stand in for the witness the consumer hands over.
--
-- (F10  THE WITNESS OF THE §5 REFUTATION)  `chanInv-⊮-pp4` applies its
--      hypothesis at `NS.bsBusy` instead of `NS.bsIdle` — i.e. at the very
--      position the equation asks for.
--      *** RED ***: `:427.34-74: [UnequalTerms] NS.bsBusy != NS.bsIdle of type
--      NS.BFsPos … the inferred type of an application NS.bsBusy ≡ NS.bsBusy
--      matches the expected type NS.bsIdle ≡ NS.bsBusy`, EXIT=42 — and the
--      mismatch is forced by `chanInv-init`'s OWN type.  So the refutation is not
--      vacuous: it is the fact that the invariant's proved witness sits at
--      `bsIdle` that does the work, and no other witness in scope substitutes.
--
-- (F11  THE TWO HALVES ARE NOT INTERCHANGEABLE)  `relayCo-from` passes its two
--      residuals to `coAt-split-at` in the opposite order — same arity, same types
--      in scope.  (Named `coAt-split` in this record until the T7 fix round; the
--      mutation is still available at the renamed definition, so nothing was unguarded.)
--      *** RED ***: `:273.55-57: [UnequalTerms] (BFAt l s (relayOf l s)) !=<
--      (CSAt l s (relayOf l s))`, EXIT=42.  So the split is by PROTOCOL and the
--      two halves are genuinely different obligations, not a relabelling.
--
-- (F12  (T1) THE `pp4` ARM IS A THEOREM, NOT A WEAKENING)  `coAt-split-at`'s `pp4`
--      clause reads its `BFAt` argument (`… eq db _ bf = bf`) instead of the carried
--      coupling — same arity, both in scope, and it is EXACTLY the shape the arm had
--      before the discharge.
--      *** RED ***: at the `pp4` clause (`:264` here; the mutant reported
--      `:254.51-53`, before this section's own prose grew above it) —
--      `[UnequalTerms] Level.Lift lzero ⊤ !=< coarsenBFs
--      (dnSrv l s) ≡ NS.bsBusy … when checking that the expression bf has type CoAt
--      l s (producing b pp4)`, EXIT=42.  So `BFAt`'s `⊤` at `pp4` is NOT a silent
--      weakening of the residual: `CoAt`'s own clause still demands the equation, and
--      nothing but `LiveDrvBF`'s own `pp4` clause supplies it.  This is the
--      falsification that makes "discharged" mean discharged.
--      *** (T2) IT IS KEPT AFTER THE SHAPE SWITCH, AND IT IS NOT REDUNDANT. ***  T1
--      recorded F12 as standing in for the totality `DrvBF`'s record shape gave up;
--      T2 restored that totality (`LiveDrvBF.DrvCp`/`drvCp-of`, both seventeen
--      clauses), and F12 still tests what no coverage check can see — that the
--      CONTENT of a discharged arm did not quietly become `⊤` on both sides at once.
--      Totality guards the EXISTENCE of an arm per sub-phase; F12 guards its content.
--
-- (F18  (T2) THE `pp5` ARM IS A THEOREM TOO)  `coAt-split-at`'s `pp5` clause reads its
--      `BFAt` argument (`… eq db nw _ bf = bf`) instead of the carried region and the
--      sharpening — same arity, everything in scope, and it is EXACTLY the shape the
--      arm had before this discharge.
--      *** RED ***: `:313.54-56: [UnequalTerms] Level.Lift lzero ⊤ !=< coarsenBFs
--      (dnSrv l s) ≡ …NS.bsStream … when checking that the expression bf has type CoAt
--      l s (producing b pp5)`, EXIT=42.  So `BFAt`'s `⊤` at `pp5` is no more a silent
--      weakening than `pp4`'s: `CoAt`'s own clause still demands `≡ bsStream`, and
--      nothing but the carried region PLUS `srvWsb-⊥` supplies it.  (F19/F20 at
--      `LiveDrvBF` §6 do the same job for the region's two novel arm families, and F21
--      at `LiveSrvOpen` §3 for the sharpening's ladder.)
--
-- (F26  (T5) THE `pp1` ARM IS A THEOREM TOO)  `coAt-split-at`'s `pp1` clause reads its
--      `CSAt` argument (`… eq db _ cs _ = cs`) instead of the carried coupling — same
--      arity, everything in scope, and it is EXACTLY the shape the arm had before this
--      discharge.
--      *** RED ***: `[UnequalTerms] Level.Lift lzero ⊤ !=< coarsenCSs (dnCSs l s) ≡
--      NS.csCanAwait … when checking that the expression cs has type CoAt l s
--      (producing b pp1)`, EXIT=42.  So `CSAt`'s `⊤` at `pp1` is no silent weakening:
--      `CoAt`'s own clause still demands `≡ csCanAwait`, and nothing but the coupling's
--      own `pp1` clause supplies it.  (F27, at `PipeNodeIoEvo`'s top cone, does the
--      same job for grant #11's carry — the FIRED node's CS-server fact cannot be
--      answered by the fixed-slot witness.)
--
-- (F43  (T6d) THE `pp2` ARM IS A THEOREM TOO)  `coAt-split-at`'s `pp2` clause reads
--      its `CSAt` argument (`… eq db _ ncw cs _ = cs`) instead of the carried region
--      and the sharpening — same arity, everything in scope, and it is EXACTLY the
--      shape the arm had before this discharge.  F26's mutation one sub-phase on, and
--      F18's shape on the other axis.
--      *** RED ***: `:399.3-5: [UnequalTerms] Level.Lift lzero ⊤ !=< coarsenCSs
--      (dnCSs l s) ≡ …NS.csMust … when checking that the expression cs has type CoAt l
--      s (producing b pp2)`, EXIT=42.  So `CSAt`'s `⊤` at `pp2` is no silent
--      weakening: `CoAt`'s own clause still demands `≡ csMust`, and nothing but the
--      carried REGION plus `csWar-⊥` supplies it.  (F41, at `LiveLegApiCone`'s
--      `DnCsAwLand`, guards the landing that establishes the region — a wrong-PHASE
--      report goes red at the cone's own producer; F42, at `LiveDrvBF`
--      §6, guards the region's io closure.)
--
-- (F47  (T7) THE `cp5` ARM IS A THEOREM TOO, AND IT IS THE FIRST ON THE CONSUME SIDE)
--      `coAt-split-at`'s `cp5` clause reads its `CSAt` argument (`… eq db _ _ cs _ = cs`)
--      instead of the carried coupling — same arity, everything in scope, and EXACTLY the
--      shape the arm had before this discharge.  F26's mutation at a `consuming`
--      sub-phase; no sharpening is involved, so it is `pp1`'s shape and not `pp2`'s.
--      *** RED ***: `:433.57-59: [UnequalTerms] Level.Lift lzero ⊤ !=< coarsenCSc
--      (upCSc l s) ≡ …NS.ccIdle … when checking that the expression cs has type CoAt l s
--      (consuming b cp5)`, EXIT=42.  So `CSAt`'s `⊤` at `cp5` is no silent weakening:
--      `CoAt`'s own clause still demands `≡ ccIdle`, and nothing but the coupling's own
--      `cp5` clause — carried through its three `cp2`/`cp3`/`cp4` carriers — supplies it.
--      (F44, at `LiveLegApiCone`'s `UpCsRfLand`, guards the LANDING that establishes the
--      position; F45, at `LiveDrvBF` §6, guards the three carrying hops; F46, at
--      `LiveLegApiCone` §2b⁗, guards the tag/carrier pairing the landing reads.)
--
-- (F48  (T7) THE VACUITY MODE OF THE CS HALF, RE-AIMED — F7's MUTATION AT A CLAUSE THAT
--      STILL EXISTS)
--      *** RETIRED AT T8c-iii, AND THE RETIREMENT WENT UNRECORDED UNTIL T10's FIX ROUND:
--      THIS MUTATION IS A NO-OP. ***  `CSAt` is `⊤` at ALL SEVENTEEN clauses since
--      T8c-iii, so "replace `consuming _ cp6` by `⊤`" changes nothing, and
--      `coAt-split-at`'s `cp6`/`pp0` clauses no longer read their `cs` argument at all —
--      they derive from `CsIdleExcl`.  The recorded RED below describes a file shape that
--      no longer exists.  This is EXACTLY the failure the re-aiming rule was written for
--      ("the retirement is invisible because the falsification's own record stays green in
--      the file"), and T10 made it worse by asserting the opposite as a positive claim.
--      *** F92 (§10) IS THE RE-AIM, AND IT RAN. ***  Read F92's report, not this one, for
--      what guards the CS half today.  The paragraph below is kept as history.  F7 tested `CSAt`'s `consuming _ cp5` clause and that clause is now
--      `⊤` by construction, so F7's own report no longer guards anything; T5, T6d and T7
--      between them emptied three of the CS half's five funded clauses.  This is F7
--      re-aimed at `consuming _ cp6`, one of the TWO that remain: replace it by `⊤`.
--      *** RED ***: `:434.57-59: [UnequalTerms] Level.Lift lzero ⊤ !=< coarsenCSs
--      (dnCSs l s) ≡ …NS.csAreq … when checking that the expression cs has type CoAt l s
--      (consuming x cp6)`, EXIT=42.  So the property F7 established for the CS half is
--      LIVE again and at a current clause: a silently-weakened clause is a type error at
--      `coAt-split-at`, not a weaker theorem.  *** Re-aim it again whenever a funded
--      clause of either half is discharged — the guard follows the clause list. ***
--      `producing _ pp0` carries the same equation as `cp6` definitionally, so it needs
--      no separate run.
--
-- (F49  (T7 fix round) THE VACUITY MODE OF THE **BF** HALF, RE-AIMED — F8's MUTATION AT A
--      CLAUSE THAT STILL EXISTS)  F48's twin, and it exists because F48's own principle
--      condemns F8: F8 tested `BFAt`'s `producing _ pp5` clause, that clause became `⊤`
--      at T2, and F8's disposal note then ASSERTED that the remaining clauses still
--      guarded the mode rather than RUNNING one.  So the BF half went five tasks with no
--      executed vacuity guard.  This is F8 re-aimed at `consuming _ cp4`, the half's
--      surviving relay-local funded clause: replace it by `⊤`.
--      *** RED ***: `:428.57-59: [UnequalTerms] Level.Lift lzero ⊤ !=< coarsenBFc
--      (upClient l s) ≡ …NS.bcIdle … when checking that the expression bf has type CoAt l
--      s (consuming x cp4)`, EXIT=42 — at `coAt-split-at`'s `cp4` clause, which still
--      READS its `BFAt` argument (`… _ _ _ _ _ bf = bf`), so `CoAt`'s own `cp4` equation
--      is there to be demanded.  Both halves now have a LIVE, EXECUTED vacuity guard:
--      F48 at `CSAt`'s `cp6`, F49 at `BFAt`'s `cp4`.
--
-- *** THE RE-AIMING RULE, STATED ONCE FOR BOTH HALVES (T7 fix round). ***  A vacuity
-- guard's target is a FUNDED clause, and this campaign turns funded clauses into `⊤` for
-- a living — so **every discharge silently retires the guard whose target it emptied**,
-- and the retirement is invisible because the falsification's own record stays green in
-- the file.  The rule: *when an arm is discharged, check whether it was the target of
-- this section's vacuity guard, and if it was, re-aim the guard at a surviving funded
-- clause and RUN it in the same task.*  It has had to move twice — F7→F48 on the CS half
-- (T7), F8→F49 on the BF half (T7's fix round) — and the two moves were needed because
-- five of the nine arms left between T1 and T7.  Only TWO funded clauses remain per half
-- (`cp6`/`pp0` and `cp4`/`pp3`), so the next discharge on either axis will need the move
-- again, and at that point one half may run out of targets entirely — at which point the
-- honest record is "this half has no vacuity mode left to guard because it has no funded
-- clause left", not silence.
--
-- *** (T10) THE MOVE WAS NEEDED, AND IT WAS MADE: F49 → F91. ***  `cp4` was F49's own
-- target, so discharging it retired that guard exactly as the rule predicts.  F91 (§10)
-- is F49 re-aimed at `producing _ pp3`, the BF half's ONE surviving funded clause, and
-- it RAN RED.  The half did NOT run out of targets — but it is now one clause from it,
-- so the next discharge on this axis is the one that will have to record the honest
-- "nothing left to guard".  *** AND THE CS HALF's OWN STATE, CORRECTED IN T10's FIX
-- ROUND: F48 has been a NO-OP since T8c-iii — `CSAt` is `⊤` at all seventeen — so the CS
-- half had NO live vacuity guard at all, and T10's first pass asserted "F48 still stands
-- at `cp6`", which was false.  F92 (§10) is the re-aim, at the ONE funded target the CS
-- axis still has: `Sharp`'s `cp6` clause (`= CsIdleExcl l s`).  So both halves have a
-- live, executed guard again — F92 on the CS side, F91 on the BF side — and each half has
-- exactly ONE funded target left. ***
--
-- *** AND THE RULE GAINS ITS THIRD CLAUSE, from this miss. ***  The re-aiming rule as
-- written says "when an arm is discharged, check whether it was the target of this
-- section's vacuity guard".  T8c-iii discharged `cp6`/`pp0` and did check that — but the
-- guard's target was `CSAt`'s clause, and what the discharge emptied was the whole
-- HALF, which is a bigger event than one clause.  The clause: *when a discharge empties
-- the LAST funded clause of a half, the half's guard must move to whatever object still
-- carries a funded requirement (since T10 that object is `Sharp`), or the half must
-- record that it has none.*  A guard whose target is `⊤` at every shape is not a weak
-- guard, it is no guard.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §8  (T8c-iii) *** THE `cp6`/`pp0` DISCHARGE's OWN GUARD, AND THE THREE RE-RUNS THE
-- NEW ARITY OWED. ***  All arity-preserving, all RUN, all RED, all reverted by STRING
-- INVERSION with `git status` verified clean after each.
--
-- *** WHY THE THREE RE-RUNS WERE OWED, and this is the F7→F48 rule applied rather than
-- cited: *** F26, F43 and F47 each assert that a discharged clause "no longer reads its
-- `CSAt` argument" by mutating it back to `= cs`.  §3's signature gained a premise
-- (`CsIdleExcl`), which SHIFTS every clause's argument list by one — so each mutation
-- had to be re-applied at the new arity rather than trusted on its green history.  All
-- three are still RED, and their errors are now SHARPER than before, because the `CSAt`
-- argument they reach for is `⊤` at every shape:
--
--   (F26 RE-RUN, `pp1`)  `:546.56-58: [UnequalTerms] Level.Lift lzero ⊤ !=< coarsenCSs
--        (dnCSs l s) ≡ NS.csCanAwait … when checking that the expression cs has type
--        CoAt l s (producing b pp1)`
--   (F43 RE-RUN, `pp2`)  `:550.58-60: … !=< coarsenCSs (dnCSs l s) ≡ NS.csMust …
--        CoAt l s (producing b pp2)`
--   (F47 RE-RUN, `cp5`)  `:525.56-58: … !=< coarsenCSc (upCSc l s) ≡ NS.ccIdle …
--        CoAt l s (consuming b cp5)`
--
-- *** NONE of the three ran out of targets *** — each still has a funded `CoAt` clause
-- to guard, because `CoAt` is untouched by this range and only `CSAt` emptied.  Had one
-- run out, the honest record would have been "no funded clause left to guard"; it did
-- not, so this is the other outcome and it is recorded as such.
--
-- (F80  *** THE NEW DISCHARGE's GUARD — the two arms' guards are NOT
--      interchangeable. ***)  Feed the `cp6` clause the `pp0` arm's guard
--      (`relayFresh-pp0` for `relayFresh-cp6`).  Arity-preserving, both in scope, and
--      it is the mutation the two clauses' near-identical bodies invite.  *** RED ***
--      `LiveRelayCS.agda:535.53-55: error: [UnequalTerms] (consuming b cp6) !=
--      (producing b …pp0) of type CPPh when checking that the expression eq has type
--      relayOf l s ≡ …producing b …pp0`.  What it establishes: the sharpening is applied
--      at each arm's OWN sub-phase, and the phase equation `eq` — not the guard's name —
--      is what ties it there.  A copy-paste between the two clauses cannot typecheck.
--
-- (F81, DECLARED NOT RUN)  the "read `cs`" mutation at `cp6`/`pp0`, i.e. F26/F43/F47's
--      mutation at the two NEW clauses.  Not run, and the ground is that the three
--      re-runs above ARE that experiment: `CoAt`'s `cp6`/`pp0` clauses are the same
--      equation shape as `pp1`'s and `pp2`'s, and the three errors show a `⊤` `CSAt`
--      argument failing against exactly such a clause three times over.  Declared here
--      rather than omitted, so a successor can run it if they disagree.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §9  (T9) THE `pp3` RE-CLASSIFICATION's OWN GUARDS — TWO, one per novel family of
-- §5b.  Both are arity-preserving and both were RUN and REVERTED.
--
-- (F83  *** THE VACUITY IS ABOUT `pp3`, NOT ABOUT THE WHOLE `producing` HALF. ***)
--      Re-aim `relayFresh-⊮-pp3` at `producing b pp0` — the ONE producing member the
--      guard region admits — keeping the absurd pattern.  Arity-preserving, and it is
--      the mutation that would turn the negative into a claim about the arm's SIBLING.
--      *** RED ***  `LiveRelayCS.agda:1086.1-22: error: [ShouldBeEmpty] LDC.RelayFresh
--      (producing b pp0) should be empty, but that's not obvious to me when checking
--      the clause left hand side relayFresh-⊮-pp3 b ()`.  What it establishes: the
--      guard region genuinely SEPARATES `pp0` from `pp3`, so negative (1) is a fact
--      about the arm this task was funded for and not a vacuous statement about
--      `RelayFresh`'s producing clauses in general.  It also re-confirms from the
--      other side why `cp6`/`pp0` were dischargeable and `pp3` is not: the same guard,
--      opposite verdicts.
--
-- (F84  *** THE FIVE-MEMBER LIST IS EXACTLY THE REGION. ***)  In
--      `cliPost-cp1-blind`, swap the first conjunct's position for `NS.ccIdle` — the
--      one position `CliPost` EXCLUDES (`LiveDrvCSD.cliPost-idle-⊥` is the landed
--      refutation) — leaving the witness `tt` in place.  Arity-preserving.
--      *** RED ***  `LiveRelayCS.agda:1105.21-23: error: [UnequalTerms] Level.Lift
--      _ℓ_625 U.⊤ !=< ⊥ when checking that the expression tt has type LDC.CliPost
--      NS.ccIdle`.  What it establishes: the blindness witness enumerates the region's
--      actual members and is not a five-fold `tt` against a catch-all — `CliPost` is
--      a real dispatch, and the `cp1` sub-case's arity is FIVE, which is the number
--      §5b's inventory (iii)/(iv) is priced against.
--
-- *** RE-AIMING NOTES. ***  F83 dies if `RelayFresh`'s region is ever widened past
-- `pp0` (which §5b explains is unsound for the CS conjuncts — a BF twin needs its OWN
-- guard, not a wider shared one), and in that case the whole of §5b wants re-deriving
-- rather than re-guarding.  F84 dies if `CliPost` is ever narrowed to the `ccArf`
-- singleton — which is exactly what a `cp1` discharge would need and is exactly what
-- items (i)-(iii) of §5b's inventory would have to buy.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §10  (T10) *** THE `cp4` DISCHARGE's OWN GUARDS, AND THE FOUR RE-RUNS THE
-- REFACTORED ARITY OWED. ***  Seven runs, all arity-preserving, all RUN, all RED, all
-- reverted by STRING INVERSION with `git diff` verified clean after each — plus F92 (two
-- stages) added in T10's fix round, which is the CS half's re-aim and is recorded last.
--
-- (F89  *** THE `cp4` ARM IS A THEOREM. ***)  §3's `cp4` clause reads its `BFAt`
--      argument (`… _ _ _  _ bf = bf`) instead of its own `Sharp` — same arity,
--      everything in scope, and it is EXACTLY the shape the arm had before this
--      discharge (F49's own mutation, one commit later).
--      *** RED ***: `LiveRelayCS.agda:672.51-53: [UnequalTerms] Level.Lift lzero U.⊤
--      !=< coarsenBFc (upClient l s) ≡ …NS.bcIdle … when checking that the expression
--      bf has type CoAt l s (consuming x cp4)`, EXIT=42.  So `BFAt`'s new `⊤` at `cp4`
--      is no silent weakening: `CoAt`'s own clause still demands `≡ bcIdle`, and
--      nothing but §2c's `upIdle-of` — the carried pair plus the token's level
--      computation plus stability — supplies it.
--
-- (F90  *** THE ARM RUNS ON THE **UP** LINK, WHICH IS WHY THE FIELD WIDENED. ***)  At
--      `relayOpen-in-s′`, feed `upIdle-of` the DOWN link's unbrokenness (`hb`) instead
--      of the up one (`hbU`).  Both are in scope and both have the same shape, so this
--      is the mutation the widened signature invites.
--      *** RED ***: `:911.22-24: [UnequalTerms] (dnLink l) != (upLink l) of type Fin
--      (numLinks p) … when checking that the expression hb has type broken (med (toSys
--      r)) (upLink l) ≡ false`, EXIT=42.  What it establishes: the `cp4` refutations are
--      moves of the leg's UP medium, so `InFlightOpen`'s two relay positions genuinely
--      needed the second link fact — the widening is load-bearing, not tidying.
--
-- (F91  *** F49 RE-AIMED — the BF half's vacuity guard, moved because `cp4` was its
--      target. ***)  This is the F7→F48/F8→F49 rule applied for the third time:
--      replace `BFAt`'s `producing _ pp3` clause (the half's ONE surviving funded
--      clause) by `⊤`.
--      *** RED ***: `:704.51-53: [UnequalTerms] Level.Lift lzero U.⊤ !=< Σ ChainRange
--      (λ rg → coarsenBFs (dnSrv l s) ≡ …NS.bsAreq rg)`, EXIT=42.  So the BF half's
--      vacuity mode is still guarded by an EXECUTED mutation at a clause that exists.
--      *** It did NOT run out of targets — but `pp3` is the last one, so the next
--      discharge on this axis owes the honest "no funded clause left to guard". ***
--      *** (T11h) THAT DEBT IS NOW DUE, AND IT IS PAID HONESTLY: F91 IS RETIRED WITH NO
--      SUCCESSOR IN ITS OWN FAMILY. ***  `pp3` is discharged, so `BFAt` is `⊤` at all
--      seventeen shapes and `bfAt-triv` is the proof of it — there is no funded `BFAt`
--      clause left to weaken, exactly as F49's own note predicted, and the same is now
--      true of `CSAt` (T8c-iii).  The guard does NOT vanish, it MIGRATES: the
--      requirement moved into §3's `Sharp`, and F108 below is the mutation at its new
--      home.  This is the F7→F48→F49→F91 chain's terminus on the BF axis.
--
-- (F108 *** F91's SUCCESSOR AT THE NEW HOME — the `pp3` requirement now lives in
--      `Sharp`, so that is where the vacuity mutation belongs. ***)  replace §3's
--      `Sharp l s (producing _ pp3)` clause by `⊤`, arity-preserving and clause-set
--      preserving.
--      *** RED ***: `:924.54-61: [UnequalTerms] Σ ChainRange (λ rg → coarsenBFs (dnSrv l
--      s) ≡ NS.bsAreq rg) !=< Level.Lift Agda.Primitive.lzero U.⊤ … when checking that
--      the expression ai b eq has type Sharp l s (producing b pp3)`, EXIT=42.  This is
--      F89's error shape at the second `Sharp` clause, and it closes the gap the
--      "WHAT IS **NOT** GUARDED" note below declared open.  Reverted by string
--      inversion, `git status` clean after.
--
-- *** WHY THE FOUR RE-RUNS WERE OWED. ***  §8's reason, one refactor on: F18, F26, F43
-- and F47 each assert that a discharged clause "no longer reads its `CSAt`/`BFAt`
-- argument", and §3's signature LOST three arguments and gained one (`Sharp`), which
-- shifts every clause's argument list by two.  A mutation stated at the old arity is
-- not the same experiment, so all four were re-applied and re-run:
--
--   (F26 RE-RUN, `pp1`)  `:698.53-55: [UnequalTerms] Level.Lift lzero U.⊤ !=< coarsenCSs
--        (dnCSs l s) ≡ NS.csCanAwait … CoAt l s (producing b pp1)`
--   (F43 RE-RUN, `pp2`)  `:702.54-56: … !=< coarsenCSs (dnCSs l s) ≡ NS.csMust …
--        CoAt l s (producing b pp2)`
--   (F47 RE-RUN, `cp5`)  `:677.53-55: … !=< coarsenCSc (upCSc l s) ≡ NS.ccIdle …
--        CoAt l s (consuming b cp5)`
--   (F18 RE-RUN, `pp5`)  `:710.54-56: … !=< coarsenBFs (dnSrv l s) ≡ NS.bsStream …
--        CoAt l s (producing b pp5)`
--
-- All four still RED, and none ran out of targets — `CoAt` is untouched by this range,
-- so every discharged arm still has a funded `CoAt` clause to guard.
--
-- *** WHAT IS **NOT** GUARDED, DECLARED. ***  The `Sharp` refactor itself has no
-- mutation of its own: a `Sharp` clause weakened to `⊤` at a FUNDED arm goes red at
-- `coAt-split-at` (that is F89's and F91's error shape, and F18/F26/F43/F47's), and a
-- `sharp-all` clause returning the wrong premise cannot typecheck because the four
-- premise types are pairwise distinct.  Declared here rather than omitted, so a
-- successor can run one if they disagree.
-- <<< SUPERSEDED BY F92, ONE FIX ROUND LATER: the first half of that declaration was
-- RUN, and it is now the CS half's vacuity guard.  The second half stands as declared. >>>
--
-- (F92  *** F48 RE-AIMED — THE CS HALF's VACUITY GUARD, WHICH HAD BEEN A NO-OP SINCE
--      T8c-iii. ***)  T10's first pass claimed "the CS half is untouched: F48 still
--      stands at `cp6`".  FALSE: F48 mutates `CSAt`'s `cp6` clause, `CSAt` is `⊤` at all
--      seventeen shapes since T8c-iii emptied the half, and `coAt-split-at`'s `cp6`/`pp0`
--      clauses do not read their `cs` argument any more.  Since T10 the CS axis has
--      exactly one FUNDED object at `cp6` — `Sharp`'s own clause (`= CsIdleExcl l s`) —
--      so that is where the guard belongs.  Run in TWO stages, because the first stage's
--      error lands at the BUILDER (which the file defines first) and the interesting
--      claim is about the CONSUMER:
--      (a) weaken `Sharp`'s `cp6` clause to `⊤`.  *** RED ***:
--          `LiveRelayCS.agda:657.51-53: [UnequalTerms] CsIdleExcl l s !=< Level.Lift
--          lzero U.⊤ … when checking that the expression ex has type Sharp l s (consuming
--          x cp6)`, EXIT=42 — `sharp-all`'s `cp6` clause can no longer deliver the bundle.
--      (b) the same weakening WITH `sharp-all`'s `cp6` clause repaired to `tt`, so the
--          error must land at the consumer.  *** RED ***: `:699.39-41: [UnequalTerms]
--          (Level.Lift lzero U.⊤) !=< (CsIdleExcl _l _s) … when checking that the
--          expression ex has type CsIdleExcl _l _s`, EXIT=42 — `coAt-split-at`'s `cp6`
--          arm projects `ceJoint`/`ceDrain`/`ceRead`/`ceWrite`/`ceSync` out of it, so the
--          requirement is genuinely READ and not merely declared.
--      Both stages reverted by string inversion, `git diff` clean after each.  What it
--      establishes: the CS half's vacuity mode is guarded again, by an EXECUTED mutation
--      at a clause that exists — and the guard's home moved from `CSAt` to `Sharp`, which
--      is where the refactor put the funded requirements.
------------------------------------------------------------------------

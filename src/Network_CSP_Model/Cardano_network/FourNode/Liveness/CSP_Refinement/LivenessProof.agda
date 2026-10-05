{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- `LivenessProof` — THE TRANSPORT, and the two headlines of the four-node
-- CSP-refinement liveness route.
--
--   `livenessSpec`     : the headline — `Spec.LivenessSpec`
--                        (`∀ b → LSpec b true true ⊑FD (breakableSystemOf b ∖
--                        hidden b)`) at the premise family named below, which
--                        since the cellCp3 window is EMPTY;
--   `livenessSpec-un`  : the same, with that empty family spent — UNCONDITIONAL;
--   `livenessDivFree`  : the UNCONDITIONAL one — `∀ b → DivergenceFree
--                        (breakableSystemOf b ∖ hidden b)`, at NO premises at all.
--
-- *** (THE CELLCP3 WINDOW) `Premises` IS EMPTY AND THE ROUTE IS UNCONDITIONAL. ***
-- `cellCp3` — the last field — is DISCHARGED: `LiveChanJoin.cellCp3-of` proves it off
-- the CARRIED join (`LiveChanInv`'s `cvBlk`/`cvStr` for half one, the new `UpIdl` /
-- `DnIdl` members for half two, the two regions partitioning the position hypothesis).
-- Every "ONE field" / "ONE premise family" / "CONDITIONAL headline" reading below is
-- SUPERSEDED IN PLACE by this note: the count is ZERO. ***
--
-- *** READ THIS BEFORE QUOTING `livenessSpec`. ***  It is a THEOREM AT PREMISES,
-- exactly as `CSP_Refinement/STABR_STATUS.md` §1/§3/§4 records, and the house
-- rule of this effort is NEVER TO QUOTE THE CONCLUSION WITHOUT THEM.  The eight
-- families of `LiveFSim.Sim`'s original audit are listed below; FIVE of them —
-- (P4), (P6), (P7), (P8) and now (P5) — are THEOREMS, and (P2)/(P3)'s twelve
-- `InFlightOpen` facts are no longer assumed at all: EIGHT are THEOREMS (§0 builds
-- the records) and ALL EIGHT are PREMISE-FREE — they consume no `Premises` field,
-- because the channel invariant they need is CARRIED IN FULL by the FSim's `Rel`
-- (`LiveChanJoin`, both hops, on grants #7 and #8 plus the grant-free node-D
-- re-mirror), though like all four io fields they still take the field's OWN
-- link-unbrokenness antecedent, which is intrinsic to the `InFlightOpen` field type.
-- *** (T11h) NOTHING REMAINS: the api residual is ZERO co-position equations. ***  `pp3`
-- — the BF half's last, and the last of all nine — is DISCHARGED at `LiveRelayCS` §3
-- from the CARRIED `LiveDrvBFD.BFFresh` (`LiveChanJoin`'s fifth factor's THIRD half)
-- through `areq-of⁺⁺`, and `LiveRelayCS.BFAt` is now `⊤` at all seventeen shapes with
-- `bfAt-triv` the proof of it.  (This read "ONE co-position equation, `pp3`" until T11h
-- and "TWO (`cp4`, `pp3`)" until T10.)
-- (NINE before the cross-node api campaign, and ALL NINE are now discharged: `pp4` at
-- T1, `pp5` at T2, `pp1` at T5, `pp2` at T6d, `cp5` at T7, *** `cp6`/`pp0` at T8c-iii
-- ***, *** `cp4` at T10 *** and *** `pp3` at T11h ***; the first five carried as
-- `LiveDrvBF.DrvCp`'s own clauses, `cp6`/`pp0` DERIVED at `LiveRelayCS` §3 from the
-- carried `LiveDrvCSD.DnJoint`, `cp4` at `LiveRelayCS` §2c from the carried
-- `LiveDrvBFA.UpJoint`, and `pp3` at §3's own `Sharp` from the carried
-- `LiveDrvBFD.BFFresh` — see (P3′) below.)
-- *** (T8c-iii) THE CHAINSYNC HALF OF THE RESIDUAL IS GONE, so `csRes` is RETIRED.
-- `LiveRelayCS.CSAt` is now `⊤` at all seventeen shapes and `csResidual-triv` is the
-- proof of it. ***
-- *** (T11h) AND SO IS THE BLOCKFETCH HALF: `bfRes` FUNDS NOTHING — no consumer applies
-- it, `LiveRelayCS.BFAt` is `⊤` at all seventeen shapes and `bfAt-triv` is the proof. ***
-- *** (T12, THE CLOSE) SO `bfRes` IS RETIRED TOO, AND `Premises` HAS ONE FIELD:
-- `cellCp3` ALONE.  `livenessSpec`'s DEFINITION is unchanged (byte-identical for the
-- sixth consecutive task, md5 `cbbbb200…`), and its STATEMENT is therefore strictly
-- STRONGER — a theorem at one premise where it used to be a theorem at two. ***
-- (SUPERSEDED IN PLACE: the block above read "`Premises` has TWO fields" from T8c-iii
-- and "The FIELD is kept … the close task retires it, which is why `Premises` still
-- reads TWO below" from T11h.)
-- *** (T6c) THIS COUNT WAS ONCE STALE BY ONE ARM: T5's `pp1` discharge was never swept
-- into this header, so the tree's most-read status statement read SEVEN/five while the
-- ledger read six.  Swept at T6c, again at T6d with `pp2`, at T7 with `cp5` and at
-- T8c-iii with `cp6`/`pp0`, at T10 with `cp4` and at T11h with `pp3`; the residual is
-- *** ZERO ***
-- and this line is where it lives — *** AND THE COUNT LIVES IN THREE FILES, NOT TWO:
-- this header, `STABR_STATUS.md`, and `LiveFSim` §0/§4/§7 (which carries the number
-- INSIDE A CLAIM rather than on a count line, and so went five arms stale).  Banked at
-- T6d as "sweep BOTH or neither"; CORRECTED AT T12 to THREE — T11h swept two of the
-- three and `LiveFSim` still said `bfRes` was ONE equation.  After any retirement,
-- grep the retired NAMES across `CSP_Refinement`, not just the count lines. ***
-- *** (T11h) THREE PRE-EXISTING STALE LINES SWEPT WITH IT: this count read TWO (T10's
-- `cp4` discharge was never swept here), the sentence below read THREE fields where
-- `Premises` has had TWO since T8c-iii, and `STABR_STATUS.md`'s own count read TWO. ***
-- So `Premises` carried ONE field (ZERO since the window — see the top block):
--
--   (P1) `cellCp3`  — the cell/reader alignment (owner decision #4; conditional
--        form `CellFull⁺ b → RelayPre → RelayCp3`, riding the invariant
--        transport).  Supplier `LiveTokenExcl.cellCp3-of`, parked.
--   (P2″) *** NOT A PREMISE HERE ANY MORE. ***  The leg's WHOLE BlockFetch channel
--        invariant (`LiveChanInv.ChanLeg` = `ChanUp × ChanDn`) is CARRIED:
--        `LiveChanJoin` threads it through all five step classes off the fired
--        per-peer ROWS the io and api cones report (grants #7 and #8), with the arms
--        stated HOP-PARAMETRICALLY and instantiated at each hop.  The DOWN hop's
--        client is NODE D's, and node D's api peel used to be the frozen
--        `PipeEvDriverCone.NodeDDrv`, which reports only
--        `(fixed) ⊎ (¬holding successor)` about the very client it moves — no row, no
--        successor identity — with the weak slot inherited from one layer deeper
--        (`PipeBundleEvo.BundleGEvR⁺`'s own client slot, matched at 28 sites in three
--        modules), so widening it would NOT have been a peel-local base edit.  It
--        needed none: `LiveLegApiExpose` §8 re-mirrors that peel in the CSP layer,
--        calling the landed `decBFc-apiBF-succ-row⁺` through `absBundleG-api-evo⁺`
--        and bypassing `BundleGEvR⁺`.  Base, frame and per-class preservation of the
--        object itself are PROVED in `LiveChanInv`.
--        *** From the carried object, EIGHT of the twelve in-flight facts are
--        premise-free theorems: *** `oUpCell`/`oDnCell` (`LiveChanInv` §7) and
--        `oUpSrv`/`oDnSrv` (`LiveSrvOpen` §2) at both legs, each taking the leg's link
--        unbrokenness as its own antecedent and `NoTwoTokens` from the carried
--        invariant.
--   (P3′) `bfRes` — the api residual.  *** NOT A PREMISE HERE ANY MORE, AND NO
--        LONGER A FIELD AT ALL (T12). ***  `csRes` went at T8c-iii and `bfRes` goes
--        here; NINE co-position equations were charted and ALL NINE ARE THEOREMS, so
--        both `LiveRelayCS.CSResidual` and `.BFResidual` are proved outright
--        (`csResidual-triv`, `bfResidual-triv`) and the record needs neither.  THE
--        LABEL IS RETIRED — do not count labels here to count premises, count the
--        FIELDS of `Premises` (the mistake this header made for three tasks).
--        (SUPERSEDED IN PLACE, the count history kept so a grep for the old numbers
--        finds the correction: this entry read "since (T7) TWO ChainSync co-position
--        equations and TWO BlockFetch ones" and "ALL FOUR remaining equations are
--        CROSS-NODE" before T8c-iii, "TWO BlockFetch co-position equations
--        (`cp4`/`pp3`)" before T10, "ONE equation — `pp3` alone, the down-hop BF
--        server's `∃ rg. ≡ bsAreq rg`, the only arm of the original nine whose equation
--        is a Σ rather than a position" before T11h, and "NOW IT IS ZERO … the field is
--        kept only so `livenessSpec` and this module's interface stay byte-identical;
--        retiring it is the close task's" between T11h and T12.)
--        The two api facts `oRelayIn`/`oRelayOut` are now premise-free (modulo their
--        own link antecedents — since T10 BOTH of the leg's, because the `cp4`
--        discharge's refutations are moves of the UP medium).  WHERE THE NINE WENT:
--        `pp4` at T1, `pp5` at T2, `pp1` at T5, `pp2` at T6d, `cp5` at T7,
--        `cp6`/`pp0` at T8c-iii, `cp4` at T10 and `pp3` at T11h — the first five now
--        `LiveDrvBF`'s `DrvCp` clauses, CARRIED by the FSim's `Rel` (`LiveChanJoin`'s
--        FIFTH trailing factor) and fed to the two api facts by `ifo-of` below.  `cp5`'s
--        needed THREE extra funded clauses of `DrvCp` beside its own (`cp2`/`cp3`/`cp4`,
--        pure carriers) but NO extra ingredient at the consumer, being a position.
--        `pp5`'s and `pp2`'s are
--        REGIONS and need one more ingredient each at the consumer — the stability
--        refutations of `bsWsb` (`LiveSrvOpen.srvWsb-⊥`) and of `csWar`
--        (`LiveSrvOpen.csWar-⊥`, itself running on the ChainSync channel invariant the
--        join carries as its sixth trailing factor) — which is why the two api
--        fields of `InFlightOpen` carry the down link's unbrokenness antecedent
--        beside the four io ones.  `cp6`/`pp0`, `cp4` and `pp3` left by the OTHER
--        route — DERIVED at `LiveRelayCS` from a carried object rather than moved into
--        `DrvCp` (§3 off `LiveDrvCSD.DnJoint`, §2c off `LiveDrvBFA.UpJoint`, and §3's
--        own `Sharp` off `LiveDrvBFD.BFFresh`, the FIFTH factor's THIRD half).
--   (P4) `noDivH`  — *** NOT A PREMISE HERE. ***  Divergence-freedom of the
--        hidden abstraction is a THEOREM: `LiveHeavyFacts` discharges
--        `LiveNoDivH.Descent` at six banked walk-layer facts and this module
--        passes `noDivH` by name.  That is also what makes the second headline
--        unconditional.
--   (P5) `noRetA`  — *** NOT A PREMISE HERE ANY MORE. ***  On the owner's LTL
--        grant #6 the io cone (`PipeNodeIoEvo`) carries a THIRD abstract fact
--        family, the one that transports a bundle's `InertPos` answer to the top;
--        with it, the joint invariant `LegJointB` can CARRY the inert-freeze
--        conjunct (`LiveRetFree.KAcFrz`: node B's link-AB KA client sits at its
--        loop head, whose coarse image `NS.kcClient` is not `Fin`), and
--        `LiveRetFree.radec-noRet` peels a `ret` of the whole abstract decode down
--        to that one peer.  The api class carries it too (`done l d
--        N2N_KeepAlive` is the one `IsApiCSBF` label that can move the slot), and
--        the medium-τ / `break` successors keep every node record literally.
--   (P6) `brkBits` — *** NOT A PREMISE HERE ANY MORE. ***  The base-layer
--        `PES.break-invert` was widened (the owner's LTL grant) to carry the
--        `broken`-bit update it always built, and `LiveFSim`'s §A4 proves the
--        fact outright — pointwise, because `SR.broken-upd` and the coupling's
--        `brkSet` are pointwise-equal but distinct closed terms and there is no
--        function extensionality in this development.
--   (P7) `prodLands` — *** NOT A PREMISE HERE ANY MORE. ***  The ⁺ cone now
--        KEEPS the generic producer landing (`LiveLegApiCone.SrvLands`) that its
--        own `srvUp-of` always built, and exports the fired-link pin its node-A
--        peels already took as an argument; `LiveFSim` §A5 reads the fact off
--        the cone's new per-leg slot.  No base module was touched.
--   (P8) `recvLands` — *** NOT A PREMISE HERE ANY MORE EITHER. ***  On the
--        owner's LTL grant #5 the node-D api peel (`PipeEvDriverCone.NodeDDrv`)
--        now CARRIES the firing consume-driver step it always had; from it the
--        cone recovers the `cp3` gate its SESSION-40 anchor is conditioned on
--        (a `recvBFBlock` table inversion) and the FIRED LINK that refutes the
--        co-leg — the case the gate proved undecidable from the projected fields
--        alone.  `LiveFSim` §A6 reads the fact off the cone's new slot.
--
-- *** So the conditional headline rests on (P1) ALONE, and since T12 that is also the
-- SHAPE of `Premises`: ONE field, `cellCp3` — true, reachability-shaped, assumed. ***
-- (SUPERSEDED IN PLACE AT THE CELLCP3 WINDOW: `cellCp3` is a THEOREM
-- (`LiveChanJoin.cellCp3-of`), `Premises` has ZERO fields and the headline rests on
-- NOTHING.  `cellCp3` is now a RETIRED NAME — every occurrence below is history.)
-- (SUPERSEDED IN PLACE: this read "(P1) and (P3′): THREE fields" before T11h — a
-- PRE-EXISTING staleness, `Premises` having had TWO since T8c-iii — and "rests on (P1)
-- ALONE — (P3′) funds nothing … TWO fields" between T11h and T12.)  *** THE GAIN IS DISCHARGEABILITY, NOT PREMISE
-- STRENGTH — do not state it the other way round. ***  §0 DERIVES the twelve
-- position facts from these fields, so the new set IMPLIES the old one (the converse
-- fails: twelve position refutations do not give a per-hop channel invariant), i.e. it
-- is logically at least as strong.  What is better is WHAT is assumed: the carryable
-- object is GONE from the record entirely (the join carries both hops), leaving the
-- cell/reader alignment ALONE — ZERO co-position equations, nine before
-- (AND SINCE THE CELLCP3 WINDOW THAT ALIGNMENT IS A THEOREM TOO, so what is assumed
-- is NOTHING) —
-- T1/T2/T5/T6d/T7/T8c-iii/T10/T11h (SUPERSEDED IN PLACE: this read "plus FOUR charted
-- co-position equations", stale since T8c-iii) — where instalment 3
-- assumed twelve position facts with no route of any kind.  Every peel-shaped premise
-- of instalment 3 is a theorem, and so is (P5) — the last one whose content was a fact
-- about a peer rather than about the token's walk.
-- Deliberate, priced and roadmapped (STABR_STATUS §3), and still the gap between
-- "theorem" and "the property, unconditionally".
--
-- *** THE TWO CLASSICAL SEAMS ENTER HERE. ***  Unlike the LTL route (`Praos
-- BlockLiveness⁺`, postulate-free), THIS route is not postulate-free, and this
-- module is where that becomes true — both seams are consumed by the transport
-- chain below and by nothing upstream of it:
--
--   · `CSP.Laws.Bisim.DRCongruence.modA-transfer` (`:278-282`) — the classical
--     König step "divergence-modulo-`A` transfers across `≈DR`", consumed by
--     `cong-∖`'s `div→`/`div←` fields (`:293-296`).  Note that `LiveNoDivH`
--     deliberately avoided it upstream (its descent route uses only the
--     postulate-free `div∖→modA`); it re-enters unavoidably with the hiding
--     congruence.
--   · `Semantics.DRImpliesFD.¬-divergent→normal` (`:69-73`) — "a non-divergent
--     tree reaches a τ-normal form (stable or `ret`)", consumed by
--     `drbisim→⊑FD` through `drbisim→fsim`'s `stab` field.
--
-- Both are sanctioned repo postulates, each derivable from one `dne` and
-- certified in `CSP.Laws.ClassicalFromLEM`.  Restate this in any publication.
--
-- SHAPE.  The route's modules are parameterised by the produced block `blkA`,
-- while `LivenessSpec` quantifies over it.  So the per-block work sits in the
-- inner `module At (blkA : Block₃)`, whose `Premises` record packages the fields AT
-- THAT BLOCK — and there are NONE (T8c-iii retired `csRes`, T12 retired `bfRes` after
-- T11h's `pp3` discharge left it funding nothing, and the cellCp3 window retired
-- `cellCp3`; the record is kept EMPTY so the headline's type does not move) —
-- §0 builds the two `InFlightOpen` records off the carried join, and the headlines
-- below close `∀ b` over `At`.
--
-- No postulates, holes, `--allow-unsolved-metas`, `NON_TERMINATING` or `mutual`
-- IN THIS MODULE (the two seams above live in the imported generic layers).
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LivenessProof where

open import Level using ( 0ℓ )
open import Data.Unit using () renaming ( ⊤ to ⊤₀ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Bool using ( true )
open import Data.Empty using ( ⊥ )
open import Data.Product using ( _×_; _,_; proj₁; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; cong )

open import Process_Trees using ( PTree; ExtI; ret; isStable )
open PTree using ( force )

------------------------------------------------------------------------
-- The alphabet, the operator layer and the semantic vocabulary.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; Block₃; apiES )
open import CSP.Examples.Cardano_network.Base using ( hi )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; break; apiBF; sendBFBlock; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBreakable using
  ( breakableSystem )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( ev; evl; evLabel; _─[_]─►_ )
open import Semantics.FailuresDivergences
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _⊑FD_; ⊑FD-trans )
open import Semantics.DRBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _≈DR_; drbisim-sym )
open import Semantics.DRImpliesFD {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( drbisim→⊑FD )
open import Semantics.Deadlock {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( embed∖√ )
open import Semantics.DeadlockDR {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( DivergenceFree; drbisim-divergenceFree )

-- the ≈DR hiding congruence (this is the `modA-transfer` seam's entry point)
open import CSP.Laws.Bisim.DRCongruence (Net_Api-≟ {Payload}) using ( cong-∖ )

------------------------------------------------------------------------
-- The statement module: the specification, the hidden set, and the system.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( LSpec; LivenessSpec; hidden; breakableSystemOf )

------------------------------------------------------------------------
-- THE PER-BLOCK WORK.
------------------------------------------------------------------------

-- everything the transport needs AT ONE produced block
module At (blkA : Block₃) where

  open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem blkA
    using ( abstractSystem )
  open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
    using ( NetProc; RState; radec; toSys; rinit; radec-init )
  open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
    using ( med )
  open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
    using ( broken )
  open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
    using ( bsBlk1 )
  open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
    using ( absNodesOf )
  -- *** the R2 bisimulation: the real system IS the abstraction, up to ≈DR ***
  open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
    using ( sysBisim )
  open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
    using ( TwoLegs; legBD; legCD; phOf; cblkOf; linkOf )
  open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriverCone blkA
    using ( upLinkOf )
  open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
    using ( upSrv )
  -- `PES` and `brkSet` are kept for the (P6) DOCUMENTATION above only: the field
  -- that used them left `Premises` when `LiveFSim` §A4 discharged it, and both
  -- modules are in this module's closure anyway (through `LFS`/`LA`)
  import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvStep blkA as PES
  open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveSpecCouple blkA
    using ( pastRecv; brkSet )
  open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiExpose blkA
    using ( driverExpose⁺ )
  import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegStep blkA as LS
  import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegAssembly blkA as LA
  -- the CARRIED channel invariant: the assembly's product with the leg's UP-hop
  -- `ChanUp` joined to it, and the five arms that thread it (the `ChanLeg` join)
  import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanJoin blkA as LCJ
  open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveStableOffer blkA
    using ( InFlightOpen; mkOpen )
  -- the CARRIED exclusion the eight io theorems consume (a PROVED conjunct of the
  -- `Rel`'s `LegJointB`, reached through `LegJoint`'s third component)
  open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveTokenExcl blkA
    using ( noTwoOf )
  -- *** THE EIGHT io THEOREMS, and the api RESIDUAL. ***  Four cell/server
  -- refutations off the channel invariant (`LiveChanInv` §7, `LiveSrvOpen` §2, both
  -- at BOTH legs) and the two api refutations modulo the protocol-split residual
  -- (`LiveRelayCS` §4).  These three modules were import-by-nobody until here.
  import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanInv blkA as LCI
  import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveSrvOpen blkA as LSO
  import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveRelayCS blkA as LRC
  -- the FSim witness (P1)-(P8), with (P4), (P6), (P7) and (P8) discharged inside
  -- it (§A4/§A5/§A6 prove the last three; `LiveHeavyFacts` supplies (P4))
  import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveFSim blkA as LFS
  import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveHeavyFacts blkA as LHF

  ----------------------------------------------------------------------
  -- The premise family of the headline at this block — EMPTY since the cellCp3
  -- window (it held ONE field, `cellCp3`, until then)
  -- ((P4)-(P8) omitted — all five are discharged, and (P2)/(P3)'s twelve
  -- `InFlightOpen` facts are now BUILT below, eight of them from theorems).
  -- (SUPERSEDED IN PLACE: this said "THREE premise families" while the record had
  -- TWO fields from T8c-iii and has ONE from T12.  COUNT THE FIELDS, NOT THE
  -- LABELS — `csRes`'s (P2), `bfRes`'s (P3′) and (P2″) are all retired labels, and
  -- counting labels is exactly the mistake this header made for three tasks.)
  ----------------------------------------------------------------------

  -- the premise `lspec-fd` holds at, packaged so `∀ b` can quantify over it
  record Premises : Set₁ where
      -- *** (P1) `cellCp3` — RETIRED AT THE WINDOW (the cellCp3 campaign, slice D),
      -- AND WITH IT THE WHOLE FIELD BLOCK.  `Premises` IS NOW AN EMPTY RECORD. ***
      -- It read `cellCp3 : (l : TwoLegs) (b : Block₃) (r : RState) → LS.CellCp3 l b r`
      -- — (C2)'s reachability bill, the cell/reader alignment.  It is DISCHARGED, not
      -- weakened away: `LiveChanJoin.cellCp3-of` (§5e) proves it off the CARRIED join
      -- alone — half one is `LiveChanInv`'s `cvBlk`/`cvStr` (an unread block in a hop's
      -- cell puts that hop's reader in its streaming region) and half two is the two
      -- factors slices A and B landed (`LiveDrvBFA.UpIdl`, `LiveDrvBFD.DnIdl`: the
      -- reader is at `bcIdle` throughout its pre-request region), the two regions
      -- PARTITIONING the premise's own position hypothesis so the conclusion is the
      -- one sub-phase left, `cp3`.  `LiveLegAssembly`'s io READ class takes it on its
      -- preservation MAP (slice D's reshape, the `ifoBD` precedent) and
      -- `LiveChanJoin`'s own arm supplies it, so it never reaches `LiveFSim.Sim`.
      --
      -- *** THE RECORD IS KEPT, EMPTY, ON PURPOSE. ***  Deleting it would change
      -- `livenessSpec`'s TYPE, i.e. move the statement; keeping it empty leaves the
      -- headline's term and type byte-identical while making its hypothesis trivially
      -- inhabited (`record {}`) — which is what `livenessSpec-un` below spends. So
      -- `Premises` has ZERO fields and the counts throughout this module say ZERO.
      -- (P2″) *** GONE. ***  There is no channel-invariant premise any more: the
      -- WHOLE of `LiveChanInv.ChanLeg` — both hops, both legs — is CARRIED by the
      -- FSim's `Rel` (`LiveChanJoin`, hop-parametric, all five step classes).  The
      -- down hop's client is node D's, and node D's api peel used to be frozen and
      -- row-less; `LiveLegApiExpose` §8 re-mirrors it in the CSP layer off the landed
      -- `PipeBundleEvo.decBFc-apiBF-succ-row⁺`, with no base edit.  So ALL EIGHT io
      -- in-flight facts below are premise-free theorems (they keep only the fields'
      -- own link antecedent).
      -- (P3′) *** RETIRED AT THE CLOSE (T12), the way `csRes` went at T8c-iii. ***
      -- `bfRes` — the api RESIDUAL, `isStable`-scoped — IS GONE FROM THIS RECORD.
      -- Not weakened away: DISCHARGED.  ALL NINE of the original co-position
      -- equations are theorems — `pp4` (T1), `pp5` (T2), `pp1` (T5), `pp2` (T6d),
      -- `cp5` (T7), `cp6`/`pp0` (T8c-iii), `cp4` (T10) and `pp3` (T11h) — so BOTH
      -- `LRC.CSResidual` and `LRC.BFResidual` are theorems outright
      -- (`csResidual-triv`, `bfResidual-triv`; `CSAt` and `BFAt` are `⊤` at all
      -- seventeen shapes) and neither needs a field.  The T11h review INHABITED this
      -- field's type PREMISE-FREE before the deletion, which is the evidence that
      -- deleting it strengthens `livenessSpec` rather than moving work elsewhere.
      -- *** So `Premises` had ONE field, `cellCp3`, and the count above said ONE —
      -- and at the cellCp3 window that field went too: the count is ZERO. ***
      -- (SUPERSEDED IN PLACE, the whole count history kept so a grep for the old
      -- numbers finds the correction: this note read "TWO ChainSync co-position
      -- equations and TWO BlockFetch ones" before T8c-iii, "TWO BlockFetch
      -- co-position equations (`cp4`/`pp3`)" before T10, "ONE BlockFetch co-position
      -- equation, `pp3`, at the relay driver's own phase, and NO ChainSync ones"
      -- before T11h, and between T11h and T12 "ZERO … this field is UNUSED; it is
      -- kept so `livenessSpec` is byte-identical, and the close task retires it".)
      -- WHERE THE NINE DISCHARGES WENT — the campaign's result, kept because the
      -- routes are what a reader needs and the field no longer records them: the
      -- first five equations became `LiveDrvBF.DrvCp` clauses, CARRIED by the FSim's
      -- `Rel` as `LiveChanJoin`'s FIFTH trailing factor; `cp6`/`pp0` are DERIVED at
      -- `LiveRelayCS` §3 from the carried `LiveDrvCSD.DnJoint` (SEVENTH factor) plus
      -- the bundled `CsIdleExcl` — the only pair whose equation could NOT move into
      -- `DrvCp`; `cp4` at §2c from the carried `LiveDrvBFA.UpJoint` (EIGHTH factor)
      -- plus the token's own level computation at the guard; and `pp3` — the last of
      -- all nine, and cross-node — at §3's own `Sharp` from the carried
      -- `LiveDrvBFD.BFFresh` (the FIFTH factor's THIRD half).  `pp5`'s and `pp2`'s
      -- clauses are REGIONS and take one further ingredient each at the consumer:
      -- the stability refutations of `bsWsb` (`LiveSrvOpen.srvWsb-⊥`) and of `csWar`
      -- (`LiveSrvOpen.csWar-⊥`, itself running on the ChainSync channel invariant the
      -- join carries as its SIXTH factor).  `cp4`'s refutations are moves of the UP
      -- medium — which is why the two api fields of `InFlightOpen` carry BOTH of the
      -- leg's link-unbrokenness antecedents beside the four io ones.

  ----------------------------------------------------------------------
  -- §0  *** THE TWELVE `InFlightOpen` FACTS, BUILT. ***  Eight are theorems and
  -- four are the residual's consumers, so the record is no longer a premise.
  --
  -- WHERE EACH FIELD'S PREMISES COME FROM:
  --   · the leg's own hop invariants — BOTH CARRIED, off the join's trailing factor
  --     (read by `ivU`/`ivD` below);
  --   · `NoTwoTokens` — CARRIED, off `LegJointB`'s `LegJoint`/`TokenExcl` component
  --     (this is why the supplier takes the invariant as an argument);
  --   · the link's unbrokenness — NOT supplied here: it is the fields' own
  --     antecedent, and `LiveStableOffer.parked-of` forwards the obligated window's
  --     `wLink1`/`wLink2` into it at the one site that consumes the record;
  --   · the api halves — from (P3′), each `isStable`-scoped exactly as the fields'
  --     `RefutedAt` shape hands stability over.
  ----------------------------------------------------------------------

  -- one leg's six in-flight refutations: four THEOREMS off the channel invariant
  -- and the carried exclusions, two off the api residual
  -- (`LegJointUB`'s leg index is VESTIGIAL — `LegJointUB _ s = (l : TwoLegs) →
  -- LegJointU l s`, so the `legBD` below is a phantom kept for interface shape and
  -- this premise is NOT leg-specific; the same phantom appears at `LiveChanJoin`'s
  -- five arms and `LiveFSim:1275-1276`.)
  ifo-of : (l : TwoLegs) (r : RState)
         → LCJ.LegJointUB legBD (toSys r)
         -- (T8c-iii) the CS-residual argument is GONE; the carried pair below replaces
         -- it and is read off the join exactly as `drv` is.  *** (T12) AND SO IS THE
         -- BF-residual argument — the last one: `bfr` below is read off the SAME join,
         -- so this function is now a function of the CARRIED invariant ALONE and needs
         -- no `Premises` field at all. ***
         → InFlightOpen l r
  ifo-of l r j =
    mkOpen (λ hb → LSO.srvOpen-up        l r hb ivU ntt)
           (λ hb → LCI.cellOpen-up-chan  l r hb ivU ntt)
           -- *** (T10) the two relay positions take BOTH link facts now — the `cp4`
           -- arm's refutations are moves of the UP medium — and both up-hop carriers
           -- beside the down one.  All four are read off the SAME `j`, so `Premises`
           -- loses an equation and gains nothing ***
           -- *** (T11h) … and the BF residual argument is GONE too: the two api facts
           -- take the CARRIED freshness clause instead, read off the join's FIFTH factor
           -- exactly as `drv` is.  *** (T12) `Premises.bfRes` funded NOTHING and IS NOW
           -- DELETED — this is the whole payoff of the `pp3` discharge ***
           (λ hbU hb → LRC.relayOpen-in-s′  l r hbU hb ivU ivD ivCS drv upj pinv dnj bfr)
           (λ hbU hb → LRC.relayOpen-out-s′ l r hbU hb ivU ivD ivCS drv upj pinv dnj bfr)
           (λ hb → LSO.srvOpen-dn        l r hb ivD ntt)
           (λ hb → LCI.cellOpen-dn-chan  l r hb ivD ntt)
    where
    -- BOTH hops' invariants are CARRIED (the join's trailing factor, whole)
    ivU = LCJ.chanUp-of l (toSys r) (j l)
    ivD = LCJ.chanDn-of l (toSys r) (j l)
    -- (T1) … and so is S1, the BF driver-tail coupling — the join's FIFTH factor.
    -- This is the whole interface cost of the `pp4` discharge: the two api facts
    -- take it as an argument and `bfRes` (then still a field) lost that arm from its
    -- type.
    drv = LCJ.drvBF-of l (toSys r) (j l)
    -- *** (T11h) … and its THIRD half, `LiveDrvBFD.BFFresh` — the whole interface cost
    -- of the `pp3` discharge: the two api facts take it as an argument and `bfRes` lost
    -- its last funded clause (T12: and then the field itself). ***
    bfr = LCJ.bfFresh-of l (toSys r) (j l)
    -- *** (T8c-iii) … and node D's freshness clause paired with its coupling — the
    -- join's SEVENTH factor, and the whole interface cost of the `cp6`/`pp0`
    -- discharge: the two api facts take it as an argument and `csRes` is gone. ***
    dnj = LCJ.dnJoint-of l (toSys r) (j l)
    -- (T6d) … and the leg's DOWN-hop ChainSync channel invariant — the join's SIXTH
    -- factor, whose second component is the down hop.  This is the whole interface
    -- cost of the `pp2` discharge: the two api facts take it as an argument and
    -- `csRes` (retired at T8c-iii) had lost that arm from its type.  NOT a new premise
    ivCS = proj₂ (LCJ.chanCSLeg-of l (toSys r) (j l))
    -- … and so are the pairwise exclusions (`LegJoint`'s third component)
    ntt = noTwoOf (proj₂ (proj₂ (proj₁ (j l))))
    -- *** (T10) … and the UP hop's carried pair — the join's EIGHTH factor, and the
    -- whole interface cost of the `cp4` discharge: the two api facts take it (with the
    -- token beside it) and `bfRes` (then still a field) lost that equation from its
    -- type ***
    upj = LCJ.upJoint-of l (toSys r) (j l)
    -- … and the token itself, four `proj₁`s down (`LegJoint`'s first component is
    -- `PipeInvS = PipeInv⁺ × SrvCoupled` and `PipeInv⁺ = PipeInv × Coupled`), which is
    -- where the `cp4` guard's `ProdSent` comes from
    pinv = proj₁ (proj₁ (proj₁ (proj₁ (j l))))

  ----------------------------------------------------------------------
  -- §1  THE FSIM WITNESS, with (P4), (P5), (P6), (P7) and (P8) discharged.
  ----------------------------------------------------------------------

  -- `LiveFSim`'s conclusion at this block: the spec refines the HIDDEN
  -- ABSTRACTION.  *** ZERO premises come from the record — it is EMPTY (the cellCp3
  -- window), and `Sim`'s telescope is THREE parameters, none of them a premise:
  -- `ifoBD`/`ifoCD` are applications of the carried join and `noDivH` is a theorem.
  -- The `(pr : Premises)` argument below is UNUSED and is kept only so this type does
  -- not move. ***  (SUPERSEDED IN PLACE: this read "Three premises come from the
  -- record; the fourth, `noDivH`, is …".)  `noDivH` is
  -- `LiveHeavyFacts`' instantiation of `LiveNoDivH.Descent` — a theorem (as are
  -- (P5), (P6), (P7) and (P8), which `LiveFSim` now proves internally and no
  -- longer asks for; (P5) is the one the joint invariant's new inert-freeze
  -- conjunct closes — `LiveRetFree.radec-noRet` at `LegJointB`'s own component).
  lspec-fd : (pr : Premises)
           → LSpec blkA true true ⊑FD (abstractSystem ∖ hidden blkA)
  lspec-fd pr = LFS.Sim.Assemble.lspec-fd
                  -- *** (the cellCp3 window) the `Premises.cellCp3` argument is gone
                  -- with the field: `LiveChanJoin` discharges it inside its own read
                  -- arm, so `Sim` has three parameters and none of them is a premise ***
                  -- *** (T12) both `ifo`s are now applications of the CARRIED join
                  -- ALONE: the `Premises.bfRes` argument is gone with the field ***
                  (λ r j → ifo-of legBD r j)
                  (λ r j → ifo-of legCD r j)
                  LHF.noDivH

  ----------------------------------------------------------------------
  -- §2  THE TRANSPORT — from the abstraction back to the real system.
  --
  -- `sysBisim : breakableSystem blkA ≈DR abstractSystem` (R2, 0 postulates) is the
  -- whole content; the chain is congruence, symmetry, and the FD projection:
  --
  --   cong-∖ (hidden blkA) sysBisim
  --     : (breakableSystem ∖ hidden) ≈DR (abstractSystem ∖ hidden)
  --   drbisim-sym  ⇒  the same, the other way round
  --   drbisim→⊑FD  ⇒  (abstractSystem ∖ hidden) ⊑FD (breakableSystem ∖ hidden)
  --
  -- ORIENTATION (the one thing to get right): `drbisim→⊑FD : P ≈DR Q → P ⊑FD Q`
  -- puts the ARGUMENT's LEFT side on the LEFT of `⊑FD`, and `⊑FD-trans` composes
  -- `LSpec ⊑FD abstraction` with `abstraction ⊑FD system`.  So the `drbisim-sym`
  -- is NOT decorative: without it the chain would deliver the abstraction on the
  -- wrong side and not compose at all.
  ----------------------------------------------------------------------

  -- the hidden real system and the hidden abstraction are ≈DR (hide congruence)
  hide-bisim : (breakableSystem blkA ∖ hidden blkA) ≈DR (abstractSystem ∖ hidden blkA)
  hide-bisim = cong-∖ (hidden blkA) sysBisim

  -- … so the abstraction FD-refines the real system (the `⊑FD` direction the
  -- composition needs)
  abs⊑sys : (abstractSystem ∖ hidden blkA) ⊑FD (breakableSystem blkA ∖ hidden blkA)
  abs⊑sys = drbisim→⊑FD (drbisim-sym hide-bisim)

  -- the statement module's system IS the R2 system, definitionally, at EVERY
  -- block (`Spec.nodeAOf = nodeA`) — the bridge the two headlines cross
  breakableSystemOf-is-breakableSystem : breakableSystemOf blkA ≡ breakableSystem blkA
  breakableSystemOf-is-breakableSystem = refl

  ----------------------------------------------------------------------
  -- §3  THE TWO HEADLINES AT THIS BLOCK.
  ----------------------------------------------------------------------

  -- The CSP-refinement liveness statement at this block, at `Premises` — which the
  -- cellCp3 window emptied (T8c-iii retired `csRes`, T12 `bfRes`, the window
  -- `cellCp3`), so this is unconditional in substance and `livenessSpec-un` spends it.
  -- The `(pr : Premises)` argument is KEPT so the type and term do not move.  *** Do not read `ifoBD`/`ifoCD` here: *** they are
  -- `LiveFSim.Sim`'s parameters (`LiveFSim:1275-1276`, re-derived at the post-close fix
  -- round — the old `:1241-1242` had drifted 34 lines), SUPPLIED by `ifo-of` above,
  -- and have not been `Premises` fields since the task-4 restructure.
  livenessSpec-at : (pr : Premises)
                  → LSpec blkA true true ⊑FD (breakableSystemOf blkA ∖ hidden blkA)
  livenessSpec-at pr = ⊑FD-trans (lspec-fd pr) abs⊑sys

  -- the hidden ABSTRACTION is divergence-free at every √-free-reachable state:
  -- `LiveHeavyFacts`' trace-prefix closure, with the √-free run embedded into
  -- the general big-step run (`Semantics.Deadlock.embed∖√`)
  absHide-divFree : DivergenceFree (abstractSystem ∖ hidden blkA)
  absHide-divFree reach =
    LHF.ndivsReach rinit (cong (_∖ hidden blkA) (sym radec-init)) (embed∖√ reach)

  -- UNCONDITIONAL: the real hidden system never livelocks.  `sysBisim` and the
  -- discharged descent are its ONLY inputs — no premise of the FSim enters.
  livenessDivFree-at : DivergenceFree (breakableSystemOf blkA ∖ hidden blkA)
  livenessDivFree-at = drbisim-divergenceFree hide-bisim absHide-divFree

------------------------------------------------------------------------
-- §4  THE HEADLINES, ∀ b.
------------------------------------------------------------------------

-- *** THE HEADLINE, AND ITS PREMISE FAMILY IS NOW EMPTY. ***  `Spec.LivenessSpec` —
-- the CSP failures-divergences counterpart of the LTL route's `BlockLiveness⁺` — holds
-- as soon as `Premises` holds at every block, and since the cellCp3 window `Premises`
-- has ZERO fields, so that is NO CONDITION AT ALL: `livenessSpec-un` below is this
-- theorem with the hypothesis spent.  *** (T12, and again at the window) The TERM below
-- is unchanged — it has been byte-identical since the campaign's base commit — while
-- the STATEMENT it inhabits is strictly stronger at every retirement: `csRes` left at
-- T8c-iii, `bfRes` at T12, and `cellCp3` at the window. ***
-- (`ifoBD`/`ifoCD` were never among them either — they are `LiveFSim.Sim`'s parameters
-- and are THEOREMS here, built by `ifo-of` off the CARRIED join alone.)
livenessSpec : (∀ (b : Block₃) → At.Premises b) → LivenessSpec
livenessSpec prem b = At.livenessSpec-at b (prem b)

-- *** THE UNCONDITIONAL FORM — the campaign's END STATE. ***  `Premises` is an EMPTY
-- record, so its ∀-`Block₃` family is inhabited by `record {}` and the conditional
-- headline above discharges outright.  Two statements rather than one because
-- `livenessSpec`'s type and term must not move (the window WEAKENED its premise; it
-- did not restate it); this line is what makes "unconditional" a checked fact rather
-- than a reading of an empty record.
livenessSpec-un : LivenessSpec
livenessSpec-un = livenessSpec (λ _ → record {})

-- *** THE UNCONDITIONAL HEADLINE. ***  The hidden broken four-node diamond is
-- DIVERGENCE-FREE at every block: no √-free-reachable state performs an
-- infinite τ-run.  This one is premise-FREE — it needs only the R2 bisimulation
-- and the discharged lexicographic descent — and it is the route's first
-- unconditional result about the real system.
livenessDivFree : ∀ (b : Block₃) → DivergenceFree (breakableSystemOf b ∖ hidden b)
livenessDivFree b = At.livenessDivFree-at b

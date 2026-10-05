{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Phase-2 Task 1 — `LegInv`, the POSITIVE per-leg TOKEN-LOCATION invariant.
--
-- WHY THIS MODULE EXISTS.  The banked `PipeInv⁺` (`LTL/Value/PipeInv.agda:492`)
-- is a ONE-WAY UPSTREAM coupling: each of its four `Coupled` clauses has the
-- shape "some downstream slot is occupied ⇒ some upstream driver has advanced".
-- On the ALL-EMPTY configuration every one of those four antecedents is
-- uninhabited, so `Coupled` is VACUOUSLY true there and `PipeInv⁺` supplies NO
-- positive token existence.  Consequently `PipeInv⁺` admits the PHANTOM-TOKEN
-- state `s✗` — stable, inside the obligated window, and offering nothing — which
-- is exactly the state that defeats the FSim `stabR` obligation (gate verdict
-- §6, `docs/superpowers/specs/2026-08-11-stable-offer-falsification.md`).
--
-- `LegInv` is the POSITIVE dual.  It is the verdict's hop table promoted to a
-- datatype: `LegPos` names WHERE the token is, and every `AtPos` clause asserts
-- POSITIVE OCCUPANCY of exactly one slot together with the driver phases that
-- slot's position forces.  `PipeInv`'s five `PLvl` levels are its coarse image
-- (`legInv⇒pipeInv`), so every existing `PipeInv` consumer keeps working; and
-- `legInv-excludes-phantom` at the foot of this module is the machine-checked
-- record that `LegInv` rules out `s✗` while `PipeInv⁺` does not.
--
-- SCOPE.  This module STATES the invariant: the position table, the per-position
-- component conjunctions, the base case at `initial`, the coarse-image map onto
-- `PipeInv`, two corollary readers, and the phantom exclusion (both halves of the
-- contrast — see §7).  PRESERVATION under steps is deliberately NOT here
-- (Phase-2 Tasks 2-3, `LiveLegStep`).
--
-- ---------------------------------------------------------------------
-- THE TWO TASK-1 WEAKNESSES, AND WHERE THEY NOW STAND.  Both were recorded here
-- as deliberate Task-1 choices and both were PRICED AT THE TASK-2 GATE.  The
-- gate decided them in opposite directions; the current state is:
--
-- (W1) PAYLOAD PIN — *** ADDED (Task 3, §1c). ***  Task 1 shipped `AtPos` with
--      the unpinned occupancy predicates: `CellHasBlk`/`BFcHasBlk`/`BFsHasBlk`
--      all DISCARD their `Block` argument (`PipeInv.agda:467-478`,
--      `PipeBundleEvo.agda:335`) and `RelayIn`/`RelayOut` discard `CPPh`'s
--      `Block₃` field, so `LegInv` asserted "*A* block occupies the slot", not
--      "*THE* token does".  That is enough for `stabR` (which needs OFFER
--      EXISTENCE) but NOT enough to conclude that what D receives is what A
--      produced.  `AtPos` is now indexed by the carried block and every
--      occupancy conjunct is stated AT that block (§1c), with `lpPreSend`
--      pinning it to `blkA` and `lpDone` reading it back off `cblkOf`.  The
--      gate's `PIN NOW` verdict rested on the discharging sites already proving
--      it (`decBFs-sendBF-succ`'s payload `≟`, `CliBlkVal = q ≡ bcBlk1 b`).
--
-- (W2) NO EXCLUSIVITY — *** NOT ADDED, by gate decision. ***  Measured at
--      ≈+2,300 code lines (nine occupancies × six arms), which would have fired
--      the cost trigger; the substitute is the `H19` cell-reader clause.
--      `AtPos l k b s` asserts POSITIVE occupancy of slot `k`; it
--      does NOT assert the other eight slots are empty.  So `LegInv` is "the
--      block occupies ONE of the ten slots", not "EXACTLY one".  Consequences:
--      `CellReaderAligned`'s third arm cannot be read as "both cells are empty"
--      (§6), and the strong far-end-reader form of alignment is out of reach
--      (§6's HONEST LIMITATION).  Adding exclusivity would roughly multiply
--      Task 3's per-step obligation by nine, which is precisely why it is a gate
--      decision and not a Task-1 one.
--
-- MODULE WEIGHT — DISCLOSED DEVIATION.  The Phase-2 plan labels this module
-- "cheap".  It is NOT, and cannot be: the required export `legInv⇒pipeInv`
-- names `PipeInv` as its result type, `PipeInv` imports `WalkPr`, `WalkPr`
-- imports `WalkDExpose`, and `WalkDExpose` pulls `SysRoute` → `SysOracle` →
-- the whole `SysOracle_*` layer.  So this module sits in the HEAVY closure by
-- construction.  Everything ELSE in this file reads only the cheap
-- `SysDecode`/`SysNode`/`SysMedium` carriers, so if the closure cost ever needs
-- to be avoided the fix is to relocate `legInv⇒pipeInv` alone into a separate
-- one-lemma bridge module and restate the accessors here locally.  See the
-- Task-1 report.
--
-- ---------------------------------------------------------------------
-- STEP-1 REACHABILITY QUESTIONS, ANSWERED IN WRITING (both as EXPECTED).
--
-- Q1.  Does any `(l, lo)` CS/BF peer have an `input` row that could FILL an
--      `(l, lo, N2N_*)` cell?   ANSWER: **NO**.
--      Mechanism, read off `R2_Bisim/NodeSpecs.agda`: every `input` (wire-send)
--      row of both peers is reachable ONLY out of the table head — CS client
--      `ccIdle` (`:306-314`) and BF client `bcIdle` (`:518-522`) — and only via
--      an `apiCS l d sendCS…` / `apiBF l d sendBF…` event whose row demands
--      `d′ ≟ d`.  Those api events lie in `apiES` and are therefore
--      DRIVER-GATED (the module says so itself at `:280` "api events ∈ apiES ⇒
--      driver-gated" and `:497`).  The servers are the same shape: their
--      `input` rows (`bsWsb`/`bsWnb`/`bsWblk`/`bsWbd`, `:610-639`) are entered
--      only from an api `sendBF…` at their own direction.  Every driver in this
--      scenario fires at direction `hi` (`decProd`/`decCons` emit
--      `apiCS l hi …`/`apiBF l hi …`, `SysNode.agda:800-830`, `:935-958`), and
--      the `(l, lo)` slots hold the MIRROR peers (node A is `bundleG l lo hi`,
--      i.e. clients on `lo`; nodes B/C/D are `hi/lo`, `lo/hi`, `hi/lo`,
--      `SysNode.agda:905`).  So no `(l, lo)` peer's api is ever offered, no
--      `(l, lo)` peer ever leaves its head, and no `(l, lo, N2N_*)` cell can
--      ever be filled.  `LegPos` therefore needs NO environment component.
--
-- Q2.  Does the TS warm-up's `MsgTSInit` occupy a cell key DISTINCT from
--      `(l, hi, N2N_BlockFetch)` and `(l, hi, N2N_ChainSync)`?  ANSWER: **YES**.
--      `NodeSpecs.agda:673-678` gates the warm-up wire-send on
--      `input l′ d′ N2N_TxSubmission` with payload `txSubmission MsgTSInit`, so
--      its cell key is `(l, d, N2N_TxSubmission)`.  `IDs`
--      (`Cardano_network/Base.agda:33-35`) has six pairwise-distinct
--      constructors, and `N2N_TxSubmission` is neither `N2N_BlockFetch` nor
--      `N2N_ChainSync`.  NAMING CORRECTION to the brief: the constructor is
--      `N2N_TxSubmission`, NOT `N2N_TxSubmission2` — there is no `…2` in this
--      model.  The substance of the answer is unaffected.
------------------------------------------------------------------------

open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( _×_; _,_; Σ; Σ-syntax; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; empty; full; draining )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN
  using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
        ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; CPPh; consuming; producing
        ; BFcPos; bcBlk1; BFsPos; bsBlk1 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD; phOf; InCp03; cblkOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf; relayOf; cellUp; cellDn; upClient; dnClient
        ; ProdSent; ProdNotSent; RelayPre; RelayHas; RelayFwd; ConsRecv
        ; CellHasBlk; BFcHasBlk
        ; PLvl; L0; L1; L2; L3; L4; PipeInv; PipeInv⁺
        ; prodSent-notSent-⊥; relayPre-has-⊥; inCp03-recv-⊥ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( relayBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload )

------------------------------------------------------------------------
-- §1  The two relay sub-classes.
--
-- `PipeInv` splits the relay into `RelayPre` / `RelayHas` / `RelayFwd`, but
-- `RelayHas` FUSES two distinct token locations: the relay driver finishing its
-- consume tail (`consuming _ cp4..cp6`) and the relay driver re-producing
-- onward (`producing _ pp0..pp5`).  `LegPos` keeps them apart (`lpRelayIn` vs
-- `lpRelayOut`), so the two sub-classes are stated here.  They are the ONLY
-- genuinely new predicates in this module: `ProdSent`/`ProdNotSent`/`RelayPre`/
-- `RelayHas`/`RelayFwd`/`ConsRecv`/`CellHasBlk`/`BFcHasBlk` come from `PipeInv`
-- and `BFsHasBlk` from `PipeBundleEvo` (producer-site rule — do not re-define).
------------------------------------------------------------------------

-- the relay driver HOLDS the block on its CONSUME side: it has received it and
-- is finishing the consume tail (`consuming _ cp4..cp6`)
RelayIn : CPPh → Set
RelayIn (consuming _ cp0) = ⊥
RelayIn (consuming _ cp1) = ⊥
RelayIn (consuming _ cp2) = ⊥
RelayIn (consuming _ cp3) = ⊥
RelayIn (consuming _ cp4) = ⊤
RelayIn (consuming _ cp5) = ⊤
RelayIn (consuming _ cp6) = ⊤
RelayIn (producing _ _)   = ⊥

-- the relay driver HOLDS the block on its PRODUCE side: the consume leg is done
-- and it is re-producing onward, pre-`sendBFBlock` (`producing _ pp0..pp5`)
RelayOut : CPPh → Set
RelayOut (consuming _ _)   = ⊥
RelayOut (producing _ pp0) = ⊤
RelayOut (producing _ pp1) = ⊤
RelayOut (producing _ pp2) = ⊤
RelayOut (producing _ pp3) = ⊤
RelayOut (producing _ pp4) = ⊤
RelayOut (producing _ pp5) = ⊤
RelayOut (producing _ pp6) = ⊥
RelayOut (producing _ pp7) = ⊥
RelayOut (producing _ pp8) = ⊥
RelayOut (producing _ pp9) = ⊥

-- the consume-side relay hold is one of `PipeInv`'s `RelayHas` phases
relayIn⇒has : (r : CPPh) → RelayIn r → RelayHas r
relayIn⇒has (consuming _ cp0) ()
relayIn⇒has (consuming _ cp1) ()
relayIn⇒has (consuming _ cp2) ()
relayIn⇒has (consuming _ cp3) ()
relayIn⇒has (consuming _ cp4) _ = tt
relayIn⇒has (consuming _ cp5) _ = tt
relayIn⇒has (consuming _ cp6) _ = tt
relayIn⇒has (producing _ _)   ()

-- the produce-side relay hold is one of `PipeInv`'s `RelayHas` phases
relayOut⇒has : (r : CPPh) → RelayOut r → RelayHas r
relayOut⇒has (consuming _ _)   ()
relayOut⇒has (producing _ pp0) _ = tt
relayOut⇒has (producing _ pp1) _ = tt
relayOut⇒has (producing _ pp2) _ = tt
relayOut⇒has (producing _ pp3) _ = tt
relayOut⇒has (producing _ pp4) _ = tt
relayOut⇒has (producing _ pp5) _ = tt
relayOut⇒has (producing _ pp6) ()
relayOut⇒has (producing _ pp7) ()
relayOut⇒has (producing _ pp8) ()
relayOut⇒has (producing _ pp9) ()

-- a relay cannot be both pre-receive and holding on its consume side
relayPre-in-⊥ : (r : CPPh) → RelayPre r → RelayIn r → ⊥
relayPre-in-⊥ r hPre hIn = relayPre-has-⊥ r hPre (relayIn⇒has r hIn)

-- a relay cannot be both pre-receive and holding on its produce side
relayPre-out-⊥ : (r : CPPh) → RelayPre r → RelayOut r → ⊥
relayPre-out-⊥ r hPre hOut = relayPre-has-⊥ r hPre (relayOut⇒has r hOut)

------------------------------------------------------------------------
-- §1b  THE TWO TASK-2 DESIGN CORRECTIONS (C1) and (C2), as predicates.
--
-- Both were forced by the Task-2 measurement spike
-- (`docs/superpowers/specs/2026-08-11-leginv-remirror-spike-report.md` §5) and
-- both were machine-checked there before landing here.  They TIGHTEN three
-- `AtPos` clauses; every export of this module survives the tightening, because
-- each tightened predicate comes with the implication back to the old one
-- (`cellFull⇒hasBlk`, `relayCp3⇒pre`, `consCp3⇒inCp03`) and every consumer
-- either discards the conjunct (`legInv⇒pipeInv`'s occupancy slot) or is routed
-- through that implication.
--
-- (C1)  THE CELL POSITIONS MUST BE `full`-ONLY.  `CellHasBlk` holds of BOTH
--       `full x` and `draining x` (`PipeInv.agda:467-470`), but `draining` is the
--       POST-READ loop-back phase (`SysStep.agda:1240-1252`: the cell re-enters
--       through a `sil` only AFTER the reader has taken the payload), so at
--       `draining` the token is ALREADY in the far-end BF client.  With
--       `CellHasBlk` the medium-drain τ at the token's own cell turns
--       `draining x` into `empty` and DESTROYS the position with no successor
--       derivable — i.e. `LegInv` as Task 1 stated it is NOT PRESERVED by the
--       medium τ.  With `CellFullBlk` a token-bearing cell is `full`, the drained
--       key's source is `draining x` (`WalkConvTauInv.medium-τ-inv-wt` reports
--       exactly that), so a token-bearing cell can never be the drained one and
--       the medium-τ arm becomes a pure transport.  CONSEQUENCE, budgeted: the
--       `full → draining` OUTPUT io is now the `lpUpCell → lpUpClient` HOP, whose
--       positive fact is banked (`PipeCliIoDec.CliBlkVal`, `:115-117`).
--
-- (C2)  THE TWO CLIENT POSITIONS MUST PIN THEIR DRIVER TO EXACTLY `cp3`.
--       `AtPos l lpUpClient` pinned the relay only to `RelayPre` (= `cp0..cp3`).
--       On the two NON-`recvBFBlock` visible relay consume moves the relay's own
--       upstream BF client fires WITH the relay and lands ¬-holding
--       (`PipeEvDriver.agda:135-140` says so in as many words), so from
--       `cp0..cp2` the preservation obligation would have a FALSE case: the token
--       leaves the client with no receiver.  Pinning to `cp3` — the only phase
--       from which the relay's next consume move IS `recvBFBlock` — removes it.
--       The same argument applies to `lpDnClient`, whose consumer-side pin was
--       `InCp03` (= `cp0..cp3`).  This is a RESTATEMENT, not new proof debt: the
--       falsification verdict §4 already records the reachability argument
--       ("`dnClient ≡ bcBlk1 b ⇒ phOf ≡ cp3`", no separate driver-side
--       obligation).
------------------------------------------------------------------------

-- (C1) a medium copy cell holds a fetched block AND HAS NOT YET BEEN READ:
-- `full` only, never the post-read `draining` phase
CellFullBlk : CopyPhase → Set
CellFullBlk empty        = ⊥
CellFullBlk (full pl)    = CellHasBlk (full pl)
CellFullBlk (draining _) = ⊥

-- (C1) the tightened cell predicate still implies `PipeInv`'s `CellHasBlk`, so
-- every coarse consumer of this module survives the tightening untouched
cellFull⇒hasBlk : (ph : CopyPhase) → CellFullBlk ph → CellHasBlk ph
cellFull⇒hasBlk empty        ()
cellFull⇒hasBlk (full pl)    h = h
cellFull⇒hasBlk (draining _) ()

-- (C2) the relay driver is at EXACTLY the pre-`recvBFBlock` phase `cp3`
RelayCp3 : CPPh → Set
RelayCp3 (consuming _ cp0) = ⊥
RelayCp3 (consuming _ cp1) = ⊥
RelayCp3 (consuming _ cp2) = ⊥
RelayCp3 (consuming _ cp3) = ⊤
RelayCp3 (consuming _ cp4) = ⊥
RelayCp3 (consuming _ cp5) = ⊥
RelayCp3 (consuming _ cp6) = ⊥
RelayCp3 (producing _ _)   = ⊥

-- (C2) the `cp3` pin is one of `PipeInv`'s pre-receive relay phases
relayCp3⇒pre : (r : CPPh) → RelayCp3 r → RelayPre r
relayCp3⇒pre (consuming _ cp0) ()
relayCp3⇒pre (consuming _ cp1) ()
relayCp3⇒pre (consuming _ cp2) ()
relayCp3⇒pre (consuming _ cp3) _ = tt
relayCp3⇒pre (consuming _ cp4) ()
relayCp3⇒pre (consuming _ cp5) ()
relayCp3⇒pre (consuming _ cp6) ()
relayCp3⇒pre (producing _ _)   ()

-- (C2) node D's consumer driver is at EXACTLY the pre-`recvBFBlock` phase `cp3`
ConsCp3 : ConsPh → Set
ConsCp3 cp0 = ⊥
ConsCp3 cp1 = ⊥
ConsCp3 cp2 = ⊥
ConsCp3 cp3 = ⊤
ConsCp3 cp4 = ⊥
ConsCp3 cp5 = ⊥
ConsCp3 cp6 = ⊥

-- (C2) the consumer `cp3` pin is one of the pre-receive phases `InCp03`
consCp3⇒inCp03 : (c : ConsPh) → ConsCp3 c → InCp03 c
consCp3⇒inCp03 cp0 ()
consCp3⇒inCp03 cp1 ()
consCp3⇒inCp03 cp2 ()
consCp3⇒inCp03 cp3 _ = tt
consCp3⇒inCp03 cp4 ()
consCp3⇒inCp03 cp5 ()
consCp3⇒inCp03 cp6 ()

------------------------------------------------------------------------
-- §1c  THE PAYLOAD PIN (W1, now DISCHARGED) — the five occupancy predicates
-- in their BLOCK-INDEXED form, with the forgetful maps back to the unpinned
-- ones.
--
-- Task 1 shipped `LegInv` with the occupancy predicates
-- `BFsHasBlk`/`CellFullBlk`/`BFcHasBlk`/`RelayIn`/`RelayOut`, every one of which
-- DISCARDS the block it is carrying.  So the invariant said "*A* block occupies
-- the slot", not "*THE* token does", and no chain of hops could conclude that
-- what D receives is what A produced.  The gate verdict priced the pin and
-- directed that it ride along with Task 3 (`W1: PIN NOW`), because the
-- discharging sites already PROVE it — `PipeSrvIoDec.decBFs-sendBF-succ`
-- decides the payload `≟` at the `bsBlk1 b` row and `PipeCliIoDec.CliBlkVal`
-- IS `q ≡ bcBlk1 b`.
--
-- THE SHAPE, and why it costs the arms nothing.  Four of the five are stated as
-- a BARE EQUALITY on the slot (`upSrv l s ≡ bsBlk1 b`, …).  That is deliberate:
-- an equality both PINS the block and IMPLIES the occupancy (the forgetful maps
-- below are one `refl` pattern each), and — the point — it is transported by
-- exactly the same single `subst` the unpinned predicate needed, because
-- `SrvHas⁺ b`/`CliHas⁺ b`/`CellFull⁺ b` are each a predicate ON THE SLOT with
-- the block already fixed.  The relay is the exception: `RelayIn`/`RelayOut`
-- already pin the PHASE region, so its pinned form pairs them with
-- `PipeValInv.relayBlk`'s recorded block (producer-site rule — the accessor
-- exists, do not re-define it).
------------------------------------------------------------------------

-- a BF SERVER slot holds EXACTLY block `b`
SrvHas⁺ : Block₃ → BFsPos → Set
SrvHas⁺ b bfs = bfs ≡ bsBlk1 b

-- the pinned server occupancy implies the unpinned one
srvHas⁺⇒hasBlk : (b : Block₃) (bfs : BFsPos) → SrvHas⁺ b bfs → BFsHasBlk bfs
srvHas⁺⇒hasBlk b .(bsBlk1 b) refl = tt

-- a BF CLIENT slot holds EXACTLY block `b`
CliHas⁺ : Block₃ → BFcPos → Set
CliHas⁺ b bfc = bfc ≡ bcBlk1 b

-- the pinned client occupancy implies the unpinned one
cliHas⁺⇒hasBlk : (b : Block₃) (bfc : BFcPos) → CliHas⁺ b bfc → BFcHasBlk bfc
cliHas⁺⇒hasBlk b .(bcBlk1 b) refl = tt

-- a medium copy cell holds EXACTLY the `MsgBlock b` wire payload, UNREAD
-- (`full`, never the post-read `draining` — this is (C1) with the pin on top)
CellFull⁺ : Block₃ → CopyPhase → Set
CellFull⁺ b ph = ph ≡ full (blkPayload b)

-- the pinned cell occupancy implies the (C1) unpinned one: `blkPayload b` IS a
-- `blockFetch (MsgBlock b)` wire tuple, so `CellHasBlk (full (blkPayload b))`
-- reduces to `⊤`
cellFull⁺⇒fullBlk : (b : Block₃) (ph : CopyPhase) → CellFull⁺ b ph → CellFullBlk ph
cellFull⁺⇒fullBlk b .(full (blkPayload b)) refl = tt

-- the relay driver has received EXACTLY block `b` (consume tail, cp4..cp6)
RelayIn⁺ : Block₃ → CPPh → Set
RelayIn⁺ b r = RelayIn r × (relayBlk r ≡ b)

-- the relay driver is re-producing EXACTLY block `b` (produce tail, pp0..pp5)
RelayOut⁺ : Block₃ → CPPh → Set
RelayOut⁺ b r = RelayOut r × (relayBlk r ≡ b)

------------------------------------------------------------------------
-- §2  `LegPos` — WHERE THE TOKEN IS on one leg.
--
-- This is §4's hop table promoted to a datatype.  `PipeInv`'s five `PLvl`
-- levels are its coarse image, and — unlike `PipeInv` — every constructor
-- asserts POSITIVE occupancy of exactly one slot, which is what excludes the
-- phantom-token state `s✗` (verdict §6).
--
-- The nine SLOTS the token can occupy are the nine components `LegInv` reads:
-- the producer chain, the two BF servers, the two medium cells, the two BF
-- clients, and the relay driver (which contributes TWO positions, its consume
-- tail and its produce tail) — plus the terminal `lpDone`.
------------------------------------------------------------------------

-- the token's location on one leg
data LegPos : Set where
  lpPreSend  : LegPos   -- token not yet emitted: producer at pp0..pp5
  lpUpSrv    : LegPos   -- A's BF server holds it (`bsBlk1`)
  lpUpCell   : LegPos   -- the up cell holds `MsgBlock`, unread (`full`; see C1)
  lpUpClient : LegPos   -- the relay's BF client holds it (`bcBlk1`), relay at cp3
  lpRelayIn  : LegPos   -- the relay driver has received it: consuming _ cp4..cp6
  lpRelayOut : LegPos   -- the relay driver is re-producing: producing _ pp0..pp5
  lpDnSrv    : LegPos   -- the relay's BF server holds it (`bsBlk1`)
  lpDnCell   : LegPos   -- the down cell holds `MsgBlock`, unread (`full`; C1)
  lpDnClient : LegPos   -- D's BF client holds it (`bcBlk1`), D at cp3 — PARKED
  lpDone     : LegPos   -- D has received: phOf ∈ cp4..cp6

------------------------------------------------------------------------
-- §3  `AtPos` — the component-level content of a position.
--
-- Each clause is (occupied slot, POSITIVELY) × (the driver phases that slot's
-- position forces) — the second factor is what `LiveStableOffer` reads and what
-- `PipeInv` is the coarse image of.  The clauses are derived from the REAL
-- constructor lists (`ProdPh`/`ConsPh`/`CPPh` at `SysNode.agda:794`/`:928`/
-- `:1032`, `BFcPos` `:368`, `BFsPos` `:394`, `CopyPhase` `SysMedium.agda:118`),
-- not from the verdict's prose table.
--
-- DEVIATION FROM THE BRIEF'S SKELETON, at `lpDone`.  The brief writes
-- `AtPos l lpDone s = ConsRecv (phOf l s)` alone.  That cannot work: `lpDone`
-- must map to `PipeInv`'s `L4`, whose `AtLvl` is
-- `ProdSent × RelayFwd × ConsRecv`, so the two upstream conjuncts are needed or
-- `legInv⇒pipeInv` has nothing to return.  They are added here.  (This is
-- exactly the "a mismatch is a type error rather than a silent gap" effect
-- Step 2 was asking for.)  The `lpRelayIn`/`lpRelayOut` clauses likewise carry
-- their relay sub-class INSTEAD of a separate `RelayPre`/`RelayHas` conjunct —
-- `RelayIn`/`RelayOut` already pin the relay phase.
------------------------------------------------------------------------

-- the component-level content of a token position, WITH THE PAYLOAD PINNED to
-- the block `b` the position is carrying (§1c)
AtPos : TwoLegs → LegPos → Block₃ → SysState → Set
AtPos l lpPreSend   b s = (b ≡ blkA) × ProdNotSent (prodOf l s)
                        × RelayPre (relayOf l s) × InCp03 (phOf l s)
AtPos l lpUpSrv     b s = SrvHas⁺ b (upSrv l s) × ProdSent (prodOf l s)
                        × RelayPre (relayOf l s) × InCp03 (phOf l s)
AtPos l lpUpCell    b s = CellFull⁺ b (cellUp l s) × ProdSent (prodOf l s)
                        × RelayPre (relayOf l s) × InCp03 (phOf l s)
AtPos l lpUpClient  b s = CliHas⁺ b (upClient l s) × ProdSent (prodOf l s)
                        × RelayCp3 (relayOf l s) × InCp03 (phOf l s)
AtPos l lpRelayIn   b s = RelayIn⁺ b (relayOf l s) × ProdSent (prodOf l s)
                        × InCp03 (phOf l s)
AtPos l lpRelayOut  b s = RelayOut⁺ b (relayOf l s) × ProdSent (prodOf l s)
                        × InCp03 (phOf l s)
AtPos l lpDnSrv     b s = SrvHas⁺ b (dnSrv l s) × ProdSent (prodOf l s)
                        × RelayFwd (relayOf l s) × InCp03 (phOf l s)
AtPos l lpDnCell    b s = CellFull⁺ b (cellDn l s) × ProdSent (prodOf l s)
                        × RelayFwd (relayOf l s) × InCp03 (phOf l s)
AtPos l lpDnClient  b s = CliHas⁺ b (dnClient l s) × ProdSent (prodOf l s)
                        × RelayFwd (relayOf l s) × ConsCp3 (phOf l s)
AtPos l lpDone      b s = (cblkOf l s ≡ b) × ProdSent (prodOf l s)
                        × RelayFwd (relayOf l s) × ConsRecv (phOf l s)

------------------------------------------------------------------------
-- §4  The invariant, its base case, and the coarse image onto `PipeInv`.
------------------------------------------------------------------------

-- THE INVARIANT: SOME block occupies one of the ten slots, POSITIVELY, and
-- every component fact of that position is stated AT THAT BLOCK.  The block is
-- existential rather than fixed to `blkA` because the hop lemmas carry it
-- unchanged from source to target; `lpPreSend`'s own clause pins it to `blkA`,
-- so the identity propagates from the base case by construction.
LegInv : TwoLegs → SysState → Set
LegInv l s = Σ[ b ∈ Block₃ ] Σ[ k ∈ LegPos ] AtPos l k b s

-- at `initial` the token is at the producer's unstepped head (`prod-Al ≡ pp0`,
-- relay at its consume head `consuming blkA cp0`, consumer pending `cp0`), and
-- the block it is waiting to emit IS `blkA`
legInv-init : (l : TwoLegs) → LegInv l initial
legInv-init legBD = blkA , lpPreSend , refl , tt , tt , tt
legInv-init legCD = blkA , lpPreSend , refl , tt , tt , tt

-- the coarse image: every position maps onto one of `PipeInv`'s five `PLvl`s
-- (`lpPreSend ↦ L0`; the three up-hop slots ↦ `L1`; the two relay slots ↦ `L2`;
-- the three down-hop slots ↦ `L3`; `lpDone ↦ L4`), forgetting the positive
-- occupancy conjunct — so every existing `PipeInv` consumer keeps working
legInv⇒pipeInv : (l : TwoLegs) (s : SysState) → LegInv l s → PipeInv l s
legInv⇒pipeInv l s (b , lpPreSend  , _ , hn , hr , hc) = L0 , hn , hr , hc
legInv⇒pipeInv l s (b , lpUpSrv    , _ , hp , hr , hc) = L1 , hp , hr , hc
legInv⇒pipeInv l s (b , lpUpCell   , _ , hp , hr , hc) = L1 , hp , hr , hc
legInv⇒pipeInv l s (b , lpUpClient , _ , hp , hr , hc) =
  L1 , hp , relayCp3⇒pre (relayOf l s) hr , hc
legInv⇒pipeInv l s (b , lpRelayIn  , (hIn  , _) , hp , hc) =
  L2 , hp , relayIn⇒has  (relayOf l s) hIn , hc
legInv⇒pipeInv l s (b , lpRelayOut , (hOut , _) , hp , hc) =
  L2 , hp , relayOut⇒has (relayOf l s) hOut , hc
legInv⇒pipeInv l s (b , lpDnSrv    , _ , hp , hr , hc) = L3 , hp , hr , hc
legInv⇒pipeInv l s (b , lpDnCell   , _ , hp , hr , hc) = L3 , hp , hr , hc
legInv⇒pipeInv l s (b , lpDnClient , _ , hp , hr , hc) =
  L3 , hp , hr , consCp3⇒inCp03 (phOf l s) hc
legInv⇒pipeInv l s (b , lpDone     , _ , hp , hr , hc) = L4 , hp , hr , hc

------------------------------------------------------------------------
-- §5  Corollary reader 1 — the OBLIGATED-WINDOW token existence.
--
-- This is the reading `stabR` needs and the one `PipeInv⁺` cannot give:
-- produced on the entry link and D still pending ⇒ the token occupies one of
-- the EIGHT in-flight slots (never `lpPreSend`, never `lpDone`).  THIS is the
-- clause that kills `s✗`.
------------------------------------------------------------------------

-- POSITIVE token existence: the block occupies one of the EIGHT in-flight slots.
--
-- DELIBERATELY stated as the BARE OCCUPANCY DISJUNCTION and NOT as
-- `Σ[ k ∈ LegPos ] (InFlight k × AtPos l k s)`.  The `Σ`-over-`AtPos` form would
-- be VACUITY-BLIND: it is defined in terms of `AtPos`, so deleting a positive
-- occupancy conjunct from an `AtPos` clause would weaken both sides in step and
-- `legInv⇒token` would still typecheck.  In this form each arm is an occupancy
-- fact that `legInv⇒token` has to PRODUCE, so dropping any positive conjunct
-- from `AtPos` is a type error here.  This is the module's non-vacuity guard,
-- and it is also the shape `stabR` wants (a bare occupancy fact, not a bundle).
TokenSomewhere : TwoLegs → SysState → Set
TokenSomewhere l s =
    BFsHasBlk  (upSrv    l s)   -- A's BF server holds it (`bsBlk1`)
  ⊎ CellHasBlk (cellUp   l s)   -- the up cell holds a `MsgBlock`
  ⊎ BFcHasBlk  (upClient l s)   -- the relay's BF client holds it (`bcBlk1`)
  ⊎ RelayIn    (relayOf  l s)   -- the relay driver has received it
  ⊎ RelayOut   (relayOf  l s)   -- the relay driver is re-producing it
  ⊎ BFsHasBlk  (dnSrv    l s)   -- the relay's BF server holds it (`bsBlk1`)
  ⊎ CellHasBlk (cellDn   l s)   -- the down cell holds a `MsgBlock`
  ⊎ BFcHasBlk  (dnClient l s)   -- D's BF client holds it — THE PARKED SLOT

-- inside the obligated window (`ProdSent` + D still `InCp03`) the token is
-- somewhere in flight: `lpPreSend` is refuted by `ProdSent` and `lpDone` by
-- `InCp03`, and each of the remaining eight positions HANDS OVER its positive
-- occupancy witness
legInv⇒token : (l : TwoLegs) (s : SysState) → LegInv l s
             → ProdSent (prodOf l s) → InCp03 (phOf l s) → TokenSomewhere l s
legInv⇒token l s (b , lpPreSend , _ , hn , _ , _) hp hc =
  ⊥-elim (prodSent-notSent-⊥ (prodOf l s) hp hn)
legInv⇒token l s (b , lpUpSrv    , hb , _ , _ , _) hp hc =
  inj₁ (srvHas⁺⇒hasBlk b (upSrv l s) hb)
legInv⇒token l s (b , lpUpCell   , hb , _ , _ , _) hp hc =
  inj₂ (inj₁ (cellFull⇒hasBlk (cellUp l s) (cellFull⁺⇒fullBlk b (cellUp l s) hb)))
legInv⇒token l s (b , lpUpClient , hb , _ , _ , _) hp hc =
  inj₂ (inj₂ (inj₁ (cliHas⁺⇒hasBlk b (upClient l s) hb)))
legInv⇒token l s (b , lpRelayIn  , (hIn  , _) , _ , _) hp hc =
  inj₂ (inj₂ (inj₂ (inj₁ hIn)))
legInv⇒token l s (b , lpRelayOut , (hOut , _) , _ , _) hp hc =
  inj₂ (inj₂ (inj₂ (inj₂ (inj₁ hOut))))
legInv⇒token l s (b , lpDnSrv    , hb , _ , _ , _) hp hc =
  inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ (srvHas⁺⇒hasBlk b (dnSrv l s) hb))))))
legInv⇒token l s (b , lpDnCell   , hb , _ , _ , _) hp hc =
  inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁
    (cellFull⇒hasBlk (cellDn l s) (cellFull⁺⇒fullBlk b (cellDn l s) hb))))))))
legInv⇒token l s (b , lpDnClient , hb , _ , _ , _) hp hc =
  inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (cliHas⁺⇒hasBlk b (dnClient l s) hb)))))))
legInv⇒token l s (b , lpDone , _ , _ , _ , hd) hp hc =
  ⊥-elim (inCp03-recv-⊥ (phOf l s) hc hd)

------------------------------------------------------------------------
-- §6  Corollary reader 2 — cell/reader alignment.
--
-- The leg's two medium slots are the copy cells keyed `(linkAB/AC, hi,
-- N2N_BlockFetch)` and `(linkBD/CD, hi, N2N_BlockFetch)` (`PipeInv.agda:424`,
-- `:430`).  A cell keyed on `N2N_BlockFetch` is drained by the BlockFetch
-- CLIENT at the same `(link, hi)`, whose streaming row accepts exactly
-- `blockFetch (MsgBlock b)` (`NodeSpecs.agda:544-547`).  So `CellHasBlk` — the
-- SESSION-28-corrected "holds a `MsgBlock`", not mere non-emptiness — is
-- precisely "the payload is in the far-end reader's accepted set".  That
-- refinement is the one `LTL/Evidence/PipeCellFalse.agda` was written to force:
-- node A's BF server writes `MsgStartBatch` into the SAME cell while the
-- producer is still at `pp5`, so a non-emptiness antecedent lies on every
-- delivering run.
--
-- `legInv⇒aligned` DECIDES which of the two cells (if either) holds the token,
-- and pairs the answer with the relay phase that identifies its reader: at the
-- up cell the relay is still pre-receive (so the reader is the RELAY's client),
-- at the down cell the relay has forwarded (so the reader is D's client).
--
-- HONEST LIMITATION (reported, not hidden).  This does NOT pin the far-end
-- client's own FSM position (e.g. "`upClient` is at a streaming-await
-- position").  That STRONGER form is NOT derivable from `AtPos` as specified:
-- `AtPos l lpUpCell` constrains the cell and the three drivers but says nothing
-- about `upClient`.  Deriving it would need a reader-position conjunct added to
-- the two cell clauses, whose truth rests on cell CAPACITY reasoning (a copy
-- cell holds one payload, so a `MsgBlock` in the cell means the earlier
-- `MsgStartBatch` was already drained and the client has advanced past
-- `bcBusy`) — i.e. another invariant, and a Task-3 preservation cost.  See the
-- Task-1 report.
------------------------------------------------------------------------

-- the positions at which the token is in NEITHER of the leg's two cells
NonCell : LegPos → Set
NonCell lpPreSend  = ⊤
NonCell lpUpSrv    = ⊤
NonCell lpUpCell   = ⊥
NonCell lpUpClient = ⊤
NonCell lpRelayIn  = ⊤
NonCell lpRelayOut = ⊤
NonCell lpDnSrv    = ⊤
NonCell lpDnCell   = ⊥
NonCell lpDnClient = ⊤
NonCell lpDone     = ⊤

-- the token is in the up cell (with the relay still pre-receive, so the reader
-- is the relay's BF client), or in the down cell (with the relay forwarded, so
-- the reader is D's BF client), or its WITNESSING POSITION is not a cell.
--
-- The third arm says only that — NOT that both cells are empty.  `AtPos` carries
-- no exclusivity (see the module header's DELIBERATE WEAKNESS note), so a
-- non-cell witnessing position is compatible with a cell holding some other
-- block.  Do not read the third arm as "the cells are empty".
CellReaderAligned : TwoLegs → SysState → Set
CellReaderAligned l s =
    (CellHasBlk (cellUp l s) × ProdSent (prodOf l s) × RelayPre (relayOf l s))
  ⊎ (CellHasBlk (cellDn l s) × ProdSent (prodOf l s) × RelayFwd (relayOf l s))
  ⊎ (Σ[ b ∈ Block₃ ] Σ[ k ∈ LegPos ] (NonCell k × AtPos l k b s))

-- every `LegInv` position decides the cell/reader alignment
legInv⇒aligned : (l : TwoLegs) (s : SysState) → LegInv l s → CellReaderAligned l s
legInv⇒aligned l s (b , lpUpCell , hb , hp , hr , _) =
  inj₁ (cellFull⇒hasBlk (cellUp l s) (cellFull⁺⇒fullBlk b (cellUp l s) hb) , hp , hr)
legInv⇒aligned l s (b , lpDnCell , hb , hp , hr , _) =
  inj₂ (inj₁ (cellFull⇒hasBlk (cellDn l s) (cellFull⁺⇒fullBlk b (cellDn l s) hb)
             , hp , hr))
legInv⇒aligned l s (b , lpPreSend  , at) = inj₂ (inj₂ (b , lpPreSend  , tt , at))
legInv⇒aligned l s (b , lpUpSrv    , at) = inj₂ (inj₂ (b , lpUpSrv    , tt , at))
legInv⇒aligned l s (b , lpUpClient , at) = inj₂ (inj₂ (b , lpUpClient , tt , at))
legInv⇒aligned l s (b , lpRelayIn  , at) = inj₂ (inj₂ (b , lpRelayIn  , tt , at))
legInv⇒aligned l s (b , lpRelayOut , at) = inj₂ (inj₂ (b , lpRelayOut , tt , at))
legInv⇒aligned l s (b , lpDnSrv    , at) = inj₂ (inj₂ (b , lpDnSrv    , tt , at))
legInv⇒aligned l s (b , lpDnClient , at) = inj₂ (inj₂ (b , lpDnClient , tt , at))
legInv⇒aligned l s (b , lpDone     , at) = inj₂ (inj₂ (b , lpDone     , tt , at))

------------------------------------------------------------------------
-- §7  THE GATE-VERDICT COUNTEREXAMPLE — BOTH HALVES OF THE CONTRAST.
--
-- These three lemmas STAY in the module permanently.  They are the
-- machine-checked statement of WHY Phase 2 needed a new invariant, and the
-- contrast needs BOTH directions to say anything:
--
--   `legInv-excludes-phantom`  — `LegInv` REFUTES the phantom hypothesis set
--   `pipeInv⁺-admits-phantom`  — `PipeInv⁺` HOLDS on the same hypothesis set
--   `phantom-gap`              — the two together, as one type
--
-- `LegInv` refutes it because `ProdSent` and `InCp03` force `TokenSomewhere`, and
-- every one of its eight occupancy arms is refuted by an all-empty / non-holding
-- hypothesis.  `PipeInv⁺` holds because its token sits at `L1` and all four
-- `Coupled` clauses go through by REFUTING their antecedent — verdict §6's
-- observation that `Coupled` is vacuous at the all-empty configuration.
--
-- In decode coordinates `s✗` has all cells empty, all four links unbroken,
-- `prod-AB = pp9`, `cp-B = consuming blkA cp3`, `cons-BD = consD blkA cp3`, and
-- both BF clients non-holding.  NOTE, as a correction to the verdict's recorded
-- conjunction: the two BF SERVER slots must ALSO be non-holding for the
-- EXCLUSION half to go through.  The verdict's `s✗` description mentions only the
-- clients, because `PipeInv⁺`'s `Coupled` reads only cells and clients — the
-- servers live in `SrvCoupled` (`PipeSrvInv.agda:77-80`).  `LegInv` reads all
-- NINE slots, so the exclusion needs all eight in-flight refutations, and they
-- appear as hypotheses below.  (This does not weaken the result: `bsBlk1` is
-- entered only via the api `sendBFBlock` fire and left by the wire-send, so a
-- producer at `pp9` has long since driven both servers past it.)
--
-- All three are generic in the leg — they hold for `legBD` AND `legCD`.
------------------------------------------------------------------------

-- refute each of the eight in-flight slots from the all-empty / non-holding /
-- relay-pre-receive hypotheses (kept separate from the headline so the headline
-- needs no `with` — the campaign's `let`-never-`with` rule for `blkA`-modules).
-- Generic in the leg: no clause matches on `l`.
phantom-⊥ :
    (l : TwoLegs) (s : SysState)
  → (CellHasBlk (cellUp   l s) → ⊥) → (CellHasBlk (cellDn   l s) → ⊥)
  → (BFcHasBlk (upClient l s) → ⊥) → (BFcHasBlk (dnClient l s) → ⊥)
  → (BFsHasBlk (upSrv    l s) → ⊥) → (BFsHasBlk (dnSrv    l s) → ⊥)
  → RelayPre (relayOf l s)
  → TokenSomewhere l s → ⊥
phantom-⊥ l s ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre (inj₁ hb) = ¬us hb
phantom-⊥ l s ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre (inj₂ (inj₁ hb)) = ¬cu hb
phantom-⊥ l s ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre (inj₂ (inj₂ (inj₁ hb))) = ¬uc hb
phantom-⊥ l s ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre (inj₂ (inj₂ (inj₂ (inj₁ hIn)))) =
  relayPre-in-⊥  (relayOf l s) hPre hIn
phantom-⊥ l s ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ hOut))))) =
  relayPre-out-⊥ (relayOf l s) hPre hOut
phantom-⊥ l s ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ hb)))))) = ¬ds hb
phantom-⊥ l s ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₁ hb))))))) = ¬cd hb
phantom-⊥ l s ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre
  (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ (inj₂ hb))))))) = ¬dc hb

-- HALF 1 OF THE CONTRAST: the phantom-token state is NOT a `LegInv` state.
-- Generic in the leg (`legBD` AND `legCD`) — nothing here reads the leg.
legInv-excludes-phantom :
    (l : TwoLegs) (s : SysState)
  → ProdSent (prodOf l s) → InCp03 (phOf l s)
  → (CellHasBlk (cellUp   l s) → ⊥) → (CellHasBlk (cellDn   l s) → ⊥)
  → (BFcHasBlk (upClient l s) → ⊥) → (BFcHasBlk (dnClient l s) → ⊥)
  → (BFsHasBlk (upSrv    l s) → ⊥) → (BFsHasBlk (dnSrv    l s) → ⊥)
  → RelayPre (relayOf l s)
  → LegInv l s → ⊥
legInv-excludes-phantom l s hSent hPend ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre linv =
  phantom-⊥ l s ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre
    (legInv⇒token l s linv hSent hPend)

-- HALF 2 OF THE CONTRAST: under the SAME hypotheses, `PipeInv⁺` HOLDS.
--
-- This is the half that makes the pair MEAN something.  On its own,
-- `legInv-excludes-phantom` could be hypothesis-vacuous — hypotheses so strong
-- that nothing could satisfy them would refute `LegInv` for free and say nothing
-- about the two invariants' relative strength.  Together the two lemmas are the
-- machine-checked form of GATE VERDICT §6: the phantom hypothesis set SEPARATES
-- `PipeInv⁺` from `LegInv`, so no proof built on `PipeInv⁺` can supply the
-- positive token existence `stabR` needs, and a new invariant was genuinely
-- required rather than merely convenient.
--
-- Note WHICH hypotheses this half consumes: the token sits at `L1` off
-- `hSent`/`hPre`/`hPend`, and ALL FOUR `Coupled` clauses discharge by REFUTING
-- their antecedent (`¬cu`/`¬uc`/`¬cd`/`¬dc`) — never by proving a consequent.
-- That is verdict §6's observation in machine-checked form: at the all-empty
-- configuration `Coupled` is vacuously true, which is exactly why it supplies no
-- occupancy.  The two SERVER refutations (`¬us`/`¬ds`) are NOT needed here at
-- all, because `Coupled` reads only cells and clients — the servers live in
-- `SrvCoupled` (`PipeSrvInv.agda:77-80`).  `LegInv` reads all nine slots and so
-- needs all eight; the contrast therefore holds at the LARGER hypothesis set,
-- where this half holds a fortiori.
--
-- HONEST SCOPE: neither half exhibits a CONCRETE `s✗`, so neither rules out the
-- hypothesis set being unsatisfiable.  That would need a literal `SysState`
-- built with `prod-AB = pp9`, `cp-B = consuming blkA cp3`,
-- `cons-BD = consD blkA cp3` and all cells `empty`; the verdict did that
-- enumeration in prose (§6).  What IS machine-checked here is the separation.
pipeInv⁺-admits-phantom :
    (l : TwoLegs) (s : SysState)
  → ProdSent (prodOf l s) → InCp03 (phOf l s)
  → (CellHasBlk (cellUp   l s) → ⊥) → (CellHasBlk (cellDn   l s) → ⊥)
  → (BFcHasBlk (upClient l s) → ⊥) → (BFcHasBlk (dnClient l s) → ⊥)
  → RelayPre (relayOf l s)
  → PipeInv⁺ l s
pipeInv⁺-admits-phantom l s hSent hPend ¬cu ¬cd ¬uc ¬dc hPre =
    (L1 , hSent , hPre , hPend)
  , (λ h → ⊥-elim (¬cu h))
  , (λ h → ⊥-elim (¬uc h))
  , (λ h → ⊥-elim (¬cd h))
  , (λ h → ⊥-elim (¬dc h))

-- THE GAP, as one statement: at any state satisfying the phantom hypotheses,
-- `PipeInv⁺` HOLDS and `LegInv` is REFUTED.  This is the module's reason to
-- exist, and it is now a type rather than a citation.
phantom-gap :
    (l : TwoLegs) (s : SysState)
  → ProdSent (prodOf l s) → InCp03 (phOf l s)
  → (CellHasBlk (cellUp   l s) → ⊥) → (CellHasBlk (cellDn   l s) → ⊥)
  → (BFcHasBlk (upClient l s) → ⊥) → (BFcHasBlk (dnClient l s) → ⊥)
  → (BFsHasBlk (upSrv    l s) → ⊥) → (BFsHasBlk (dnSrv    l s) → ⊥)
  → RelayPre (relayOf l s)
  → PipeInv⁺ l s × (LegInv l s → ⊥)
phantom-gap l s hSent hPend ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre =
    pipeInv⁺-admits-phantom  l s hSent hPend ¬cu ¬cd ¬uc ¬dc hPre
  , legInv-excludes-phantom  l s hSent hPend ¬cu ¬cd ¬uc ¬dc ¬us ¬ds hPre

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- TokenExcl campaign, COMPLETE (slices 0/A/B/C/D + the closure P1/P2/P3) —
-- `LiveTokenExcl`, the ONE `Rel` component that discharges the per-state
-- reachability premises Task 3 left open.  Of the two, `NoTwoTokens` is PROVED
-- here — statement, base case, frame and preservation over every step class, with
-- NO leaf parameters left — and `cellCp3` was the campaign's single residual
-- premise, PARKED in §1b in its conditional shape for a future window campaign.
--
-- *** (THE CELLCP3 WINDOW) `cellCp3` IS DISCHARGED, AND NOT BY THIS MODULE'S ROUTE. ***
-- `LiveChanJoin.cellCp3-of` (§5e) proves it off the CARRIED join — `LiveChanInv`'s
-- `cvBlk`/`cvStr` plus the two new `UpIdl`/`DnIdl` members — so `LivenessProof.Premises`
-- is EMPTY.  §1b's two chain alignments and §3's `chains⇒cellCp3`/`cellCp3-of` bridge
-- STAY PARKED and now have no consumer at all: they are the route NOT taken, kept
-- because they are type-checked and because the ledger's price history refers to them.
--
-- WHAT TASK 3 LEFT.  `LiveLegStep` is green with exactly two premises, both
-- per-STATE facts (re-derived by `grep` at commit `9e1a231`):
--
--   (a) `cellCp3` — the `module _` parameter at `LiveLegStep:1081` (this read
--       `:1058`; the six anchors in this block all drifted 23-40 lines short and are
--       re-derived here), of type
--       `(l : TwoLegs) (b : Block₃) (r : RState) → CellCp3 l b r`, consumed by
--       the io-READ arm `legInv-read` (`:1088`).  *** IT IS NOT AN ASSUMPTION OF THE
--       ROUTE ANY MORE: the cellCp3 window proved it (`LiveChanJoin.cellCp3-of`), and
--       this parameter survives only because `legInv-read`'s sole consumer is §3's
--       `legInv-read⁺`, itself under a NEVER-APPLIED `module _ (ch : …)`. ***  It is (C2)'s bill: a leg whose own cell still holds the UNREAD
--       token has its reader's driver at exactly the pre-`recvBFBlock` phase.
--   (b) `NoTwoTokens l s` — an argument of `legStep→legInv` (`:1591`), threaded
--       unchanged into `relayMove` (`:1464`, used at `:1480`/`:1485`) and
--       `consMove` (`:1525`, used at `:1555`/`:1559`).  It is W2's bill: the
--       four pairwise token exclusions at the SOURCE state.
--
-- WHAT THIS MODULE IS.  Route (A) of the instalment-3 review: ONE new `Rel`
-- component, `TokenExcl`, bundling BOTH facts, with NO base-module edit and NO
-- `Reachable` induction (preservation is per single step, the `LegInv`
-- pattern; carrying the component along a run is the assembly's job, exactly as
-- for `LegInv`).  The two producer-site definitions are IMPORTED from
-- `LiveLegStep` rather than restated, so the bridges below cannot drift out of
-- agreement with what the arms demand — a restatement would be the one mistake
-- that invalidates everything downstream.
--
-- THE WIDENING (instalment-3 review, and the reason `CellCp3` alone is not an
-- inductive invariant).  `CellCp3` speaks only about the two CELLS.  Its own
-- FILL step — the leg's BF server writing the block onto the wire — turns
-- SERVER occupancy into CELL occupancy while every driver is fixed
-- (`PipeTauIo.legProd`/`legRelay`/`legCons`), so a cell-only statement would
-- have to ESTABLISH the alignment at the fill out of nothing.  Widened to the
-- 3-SLOT UPSTREAM CHAIN (`upSrv` ⊎ `cellUp` ⊎ `upClient`, and its downstream
-- twin) the fill becomes a pure TRANSPORT: the antecedent moves from one
-- disjunct to the next inside the SAME disjunction and the consequent does not
-- move at all.  §1 states the chains; §5 records where the debt lands instead.
--
-- THE BLOCK INDEX — A DELIBERATE DEVIATION FROM THE BRIEF, REPORTED.  The
-- review asked that the restatement be INDEXED BY THE POSITION'S BLOCK, to fix
-- the over-quantification of `LiveLegStep`'s `∀ b` premise.  A block-INDEXED
-- record cannot supply that premise: the block is EXISTENTIAL inside `LegInv`
-- (`LiveLegInv:457`) and is not available at the module-application site, so a
-- `TokenExcl l b s` could never be applied at the `b` the arm later destructs.
-- This module goes one better and drops the index ALTOGETHER: the chains are
-- stated with the BLOCK-FREE occupancy predicates `BFsHasBlk`/`CellFullBlk`/
-- `BFcHasBlk` — `NoTwoTokens`' own vocabulary, with the cell predicate at (C1)'s
-- `full`-only form for the reason §1 gives — which is STRICTLY STRONGER than the
-- `∀ b` form (every `CellFull⁺ b` implies `CellFullBlk` through
-- `LiveLegInv.cellFull⁺⇒fullBlk`, and nothing converse is needed), and hence
-- supplies the `∀ b` premise in one line (§3).  So the over-quantification is
-- removed rather than relocated, and the whole component is stated in ONE
-- vocabulary.
--
-- CONTENTS
--   §1   the two 3-slot occupancy chains
--   §1b  the two chain ALIGNMENTS — stated, PARKED, not fields (the `cellCp3`
--        supplier the future window campaign inherits, type-checked by §3)
--   §2   `TokenExcl`, the component (`NoTwoTokens` + the two AUX server/cell
--        exclusions), and its base case at `initial`
--   §3   the BRIDGES — machine-checked to be exactly what the two arms demand
--   §4   the FRAME lemma (the SIX components the component reads)
--   §5   the SCOPE FINDING on preservation, stated in the module so no successor
--        re-derives it
--   §6   *** THE RECORD OF FINDING 2: `NoTwoTokens` WAS FALSE AS STATED ***
--        (prose: the machine-checked refutation, and the (C1) fix that landed)
--   §7   PRESERVATION of the six exclusions: §7a the core, §7b the cell lemmas,
--        §7c the medium-τ drain, §7d the two io arms, §7e the visible api arm —
--        ALL PREMISE-FREE since the closure (P1)/(P2)/(P3)
--   §8   the CLOSURE table, and what is left (`cellCp3` only)
--
-- No postulate, no hole, no `mutual`.  `let`, never `with`, in anything whose
-- type mentions the imported `LegInv`/`AtPos`/`CellCp3` (the `blkA`-parameter
-- hazard).
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; subst )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveTokenExcl
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link; input; output )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; hi; IDs; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission
  ; N2N_KeepAlive; N2N_LeiosNotify; N2N_LeiosFetch
  -- the two enum `DecEq` instances `setHit-np`'s `≟-yes-refl` resolves against
  ; DecEq-Dir; DecEq-IDs )
-- and the `Fin` instance for `Link` (the same one-line pairing `PipeFillSource`
-- uses for its own `_≟_` dispatch)
open import Class.DecEq using ( DecEq; _≟_ )
import Class.DecEq.Instances as DecEqI

-- ASSEMBLY slice A1: the LTS level, needed by §7f's WIRED visible arm alone (the
-- arm takes the api step itself, so `VisLeaves` is derived rather than assumed)
open import Process_Trees using ( ExtI )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( apiES )
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( EventSet )
open EventSet using ( mem )
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absNodesOf; nodesOf )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; initial )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD; phOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf; relayOf; cellUp; cellDn; upClient; dnClient
        ; ProdSent; ProdNotSent; RelayHas; RelayFwd; CellHasBlk; BFcHasBlk
        ; Coupled; prodSent-notSent-⊥ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  -- the two server EVOLUTIONS are §7f's pass-through: the assembly's `PipeInvS`
  -- half needs them at the SAME successor this arm returns
  using ( upSrv; dnSrv; UpSrvEvo; DnSrvEvo )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; MedState; phase; empty; full; draining )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA
  using ( phase-upd; flipCell; ≟-yes-refl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( setCell )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA
  using ( BFcPos; BFsPos )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriverCone blkA
  using ( LegDriverStep; ldProd; ldRelay; ldCons; ldFix; LegValStep )
-- §7's io axis: the FROZEN successor-negative classifiers (the shape this
-- module's io arms need, and the one the ⁺ cone does NOT return — see §7d), their
-- four-slot families and the leg projections, plus the read arm's block pin
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeIoEvo blkA
  using ( CliIoCls; SrvIoCls; AllCliIoCls; AllSrvIoCls )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleIoEvo blkA
  using ( BlkReadAt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( PlIsBlk; upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeMedKey blkA
  using ( setRead )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauIo blkA
  using ( pickCliUp; pickCliDn; pickSrvUp; pickSrvDn )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA
  using ( LegInv; RelayCp3; ConsCp3; CellFullBlk; CellFull⁺; CliHas⁺
        ; cellFull⁺⇒fullBlk; cellFull⇒hasBlk )
-- the TWO PREMISES, taken from their PRODUCER SITE so the bridges cannot drift:
-- `CellCp3` (`LiveLegStep:967-972`; `:949` and `:964-969` are stale readings),
-- `NoTwoTokens` and the two arms that
-- consume them (`legInv-read` `:1065`, `legStep→legInv` `:1587`)
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegStep blkA
  using ( CellCp3; NoTwoTokens; noTwo
        ; nUpSrvCli; nUpCellCli; nDnSrvCli; nDnCellCli
        ; legInv-read; legStep→legInv
        -- §7c: the medium-drain key dispatch, re-used in the BACKWARD direction
        ; cell-drain-eq⁺ )
-- the visible arm's proved hand-over record, under the name `LiveLegStep` uses,
-- with the two SERVER-keep fields §7e reads and the relay-phase disjointness
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiExpose blkA
  renaming ( VisLeaves⁺ to VisLeaves )
  using ( vUpSrvKeep; vDnSrvKeep; relayHas-fwd-⊥
        -- §7e's (P3), discharged: the two SOURCE-PHASE fields
        ; vUpSrvGain; vDnSrvGain
        -- ASSEMBLY slice A1: leg `l`'s slice of the ⁺ cone from ONE peel — the
        -- driver step, the server evolutions, the value data and the PROVED
        -- `VisLeaves⁺`, all at one and the same existential successor
        ; driverExpose⁺-at )
-- §7d's io axis, PAIRED: the ⁺ cone now reports the FROZEN successor-directed
-- classifiers at its OWN successor (P1 discharged in `LiveLegIoCone`'s §1b/§6),
-- so the io arms read a cone OUTPUT where they used to take a premise
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegIoCone blkA
  using ( AllCliP; AllSrvP; frozenCli; frozenSrv
        -- §7d's (P2), discharged: the paired server fact's WRITE-OWNERSHIP answer
        ; SrvWriteOwn )

------------------------------------------------------------------------
-- §1  THE TWO 3-SLOT OCCUPANCY CHAINS.
--
-- `UpChain` is "SOME block occupies one of the three slots between node A's
-- producer and the relay's driver"; `DnChain` is its mirror between the relay's
-- driver and node D's consumer.  They are stated with the BLOCK-FREE occupancy
-- predicates `BFsHasBlk`/`CellFullBlk`/`BFcHasBlk`, which is what makes §3's two
-- bridges one-liners.
--
-- *** WHY THE CELL DISJUNCT IS `CellFullBlk` AND NOT `CellHasBlk` — (C1), ONE
-- LAYER UP. ***  `CellHasBlk` holds of `draining` as well as `full`
-- (`PipeInv:467-470`), and `draining` is the POST-READ phase at which the token
-- is ALREADY in the far-end client (`LiveLegInv:230-236`).  A `CellHasBlk`
-- disjunct would therefore still be inhabited AFTER the reader's driver has
-- consumed the block and left `cp3`, making the alignment FALSE at every
-- read-but-not-yet-drained state.  `CellFullBlk` is exactly (C1)'s `full`-only
-- predicate and is what the io-READ arm's antecedent (`CellFull⁺ b`) reduces to,
-- so nothing is lost at the bridge.  §6 machine-checks the same trap in the
-- premise this component is supposed to DISCHARGE.
--
-- WHY A ⊎ AND NOT THREE SEPARATE FIELDS.  Three fields would be three
-- implications with the same consequent, i.e. exactly this — but the ⊎ form is
-- the one the preservation arms want: a hop moves the witness from one disjunct
-- to the next and the implication is transported ONCE, not three times.
------------------------------------------------------------------------

-- some block occupies one of the leg's three UPSTREAM slots (node A's BF
-- server, the up copy cell, the relay's BF client)
UpChain : TwoLegs → SysState → Set
UpChain l s =
    BFsHasBlk   (upSrv    l s)
  ⊎ CellFullBlk (cellUp   l s)
  ⊎ BFcHasBlk   (upClient l s)

-- some block occupies one of the leg's three DOWNSTREAM slots (the relay's BF
-- server, the down copy cell, node D's BF client)
DnChain : TwoLegs → SysState → Set
DnChain l s =
    BFsHasBlk   (dnSrv    l s)
  ⊎ CellFullBlk (cellDn   l s)
  ⊎ BFcHasBlk   (dnClient l s)

------------------------------------------------------------------------
-- §1b  *** THE TWO CHAIN ALIGNMENTS — STATED ONLY, NOT PROVED, AND NOT FIELDS
-- OF THE COMPONENT. ***
--
-- These were `TokenExcl`'s first two fields at `37e4e75`.  Instalment 2 REMOVES
-- them from the record on the controller's ROUTE DECISION (option 2 of the
-- instalment-1 review): the alignment's honest inductive object is the relay's
-- REQUEST WINDOW, not the three occupancy slots (§5 records the derivation, and
-- the reviewer independently priced EVERY window route above this campaign's
-- cap), so the alignment — and with it the `cellCp3` premise it discharges —
-- is DEFERRED TO A FUTURE CAMPAIGN.  What is proved here instead is the
-- EXCLUSION half (§2, §7), which halves `LiveLegStep`'s residual premise set.
--
-- They are kept as NAMED STATEMENTS rather than deleted for two reasons: §3's
-- bridge machine-checks that they are exactly what supplies the (now
-- CONDITIONAL) `cellCp3`, so a future campaign inherits the interface already
-- type-checked; and the parked obligation stays visible in the source instead of
-- living only in a ledger.  Nothing in this module DEPENDS on them.
-- (SUPERSEDED IN PLACE AT THE CELLCP3 WINDOW: the window did NOT take this route —
-- `cellCp3` is a theorem off the carried join, so these two are parked with no
-- consumer.  Reason (2) still applies; reason (1) is now history.)
------------------------------------------------------------------------

-- PARKED (future campaign): an occupied upstream slot forces the relay's driver
-- to sit at exactly the pre-`recvBFBlock` phase `cp3`
UpChainCp3 : TwoLegs → SysState → Set
UpChainCp3 l s = UpChain l s → RelayCp3 (relayOf l s)

-- PARKED (future campaign): an occupied downstream slot forces node D's consumer
-- driver to sit at exactly the pre-`recvBFBlock` phase `cp3`
DnChainCp3 : TwoLegs → SysState → Set
DnChainCp3 l s = DnChain l s → ConsCp3 (phOf l s)

------------------------------------------------------------------------
-- §2  THE COMPONENT, AND ITS BASE CASE.
------------------------------------------------------------------------

-- THE COMPONENT (NARROWED, instalment 2): the SIX pairwise token EXCLUSIONS.
-- Four of them are `LiveLegStep`'s own `NoTwoTokens` — imported, never restated,
-- and now at the (C1)-fixed field types (slice A).  The other two are the
-- SERVER-versus-ITS-OWN-CELL pair, which is NOT one of the four `LiveLegStep`
-- demands but IS what makes the four inductive: at the io READ the reader's
-- client newly holds while its own cell was still `full`, so the only fact that
-- can empty the server slot at that step is the source's server/cell exclusion
-- (§7's core, clause F5).  Adding them is a WIDENING of the proved component,
-- not a weakening of the premise: `NoTwoTokens` is delivered unchanged (§3).
--
-- The two chain ALIGNMENTS that stood here are PARKED — see §1b.
--
-- All six are REACHABILITY facts — false at an arbitrary `SysState`, true at
-- every state of a run — which is why they are a `Rel` component carried BESIDE
-- `LegInv` rather than conjuncts of `AtPos`.
record TokenExcl (l : TwoLegs) (s : SysState) : Set where
  constructor tokenExcl
  field
    -- the four pairwise exclusions, at `LiveLegStep`'s own record type
    noTwoOf    : NoTwoTokens l s
    -- AUX: the leg's upstream server and its own up cell are never both occupied
    nUpSrvCell : BFsHasBlk (upSrv l s) → CellFullBlk (cellUp l s) → ⊥
    -- AUX: the leg's downstream server and its own down cell, likewise
    nDnSrvCell : BFsHasBlk (dnSrv l s) → CellFullBlk (cellDn l s) → ⊥
open TokenExcl public

-- BASE — at `initial` every BF server and BF client sits at its idle loop head
-- and every cell is `empty`, so all six exclusions' first antecedents are
-- uninhabited and every field is vacuous.  Per leg, because the slot accessors
-- only reduce once the leg is known.
tokenExcl-init : (l : TwoLegs) → TokenExcl l initial
tokenExcl-init legBD = tokenExcl (noTwo (λ ()) (λ ()) (λ ()) (λ ())) (λ ()) (λ ())
tokenExcl-init legCD = tokenExcl (noTwo (λ ()) (λ ()) (λ ()) (λ ())) (λ ()) (λ ())

------------------------------------------------------------------------
-- §3  THE BRIDGES.
--
-- These are the whole point of slice 0: each is a MACHINE CHECK that
-- `TokenExcl` supplies exactly what an arm demands, at the arm's own type.
-- Nothing here restates a premise — `CellCp3` and `NoTwoTokens` are the
-- imported producer-site definitions, and the last two bridges APPLY the arms.
------------------------------------------------------------------------

-- BRIDGE 1 (premise (a), per state): the two cell alignments are the CELL
-- disjunct of the two PARKED chains (§1b), read through `LiveLegInv`'s forgetful
-- map `cellFull⁺⇒fullBlk` (`CellFull⁺ b` ⇒ `CellFullBlk`).  The `∀ b` the arm
-- quantifies over costs nothing: the block-free antecedent does not mention it.
--
-- INSTALMENT 2: the two chains are no longer FIELDS, so this bridge takes them as
-- HYPOTHESES.  That is exactly the honest content — `cellCp3` REMAINS a premise of
-- `LiveLegStep`, and this type is the machine-checked statement of what a future
-- campaign has to prove to retire it (nothing more, nothing less).
--
-- SLICE B: `CellCp3` is now the CONDITIONAL form (`LiveLegStep`'s §9, reshaped),
-- so each half is handed the reader's pending-phase conjunct as well; the chain
-- alignment does not need it and DISCARDS it, which is the machine check that the
-- reshape is FREE — a strictly weaker obligation is still supplied in one line.
chains⇒cellCp3 : (l : TwoLegs) (r : RState)
               → UpChainCp3 l (toSys r) → DnChainCp3 l (toSys r)
               → (b : Block₃) → CellCp3 l b r
chains⇒cellCp3 l r up dn b =
    (λ h _ → up (inj₂ (inj₁ (cellFull⁺⇒fullBlk b (cellUp l (toSys r)) h))))
  , (λ h _ → dn (inj₂ (inj₁ (cellFull⁺⇒fullBlk b (cellDn l (toSys r)) h))))

-- BRIDGE 2 (premise (a), as the io-READ arm's `module _` PARAMETER): its type is
-- transcribed from `LiveLegStep`'s §9 `module _` and checked against the imported
-- `CellCp3`.  The hypothesis is the PARKED alignment at every reachable state,
-- which is what a future campaign's component would carry in the FSim `Rel`
-- (never a `Reachable` induction here).
cellCp3-of : ((l : TwoLegs) (r : RState) → UpChainCp3 l (toSys r) × DnChainCp3 l (toSys r))
           → (l : TwoLegs) (b : Block₃) (r : RState) → CellCp3 l b r
cellCp3-of ch l b r = chains⇒cellCp3 l r (proj₁ (ch l r)) (proj₂ (ch l r)) b

-- BRIDGE 3 (premise (b), per state): the exclusions are a projection.  The SAME
-- value is what `relayMove` (`LiveLegStep:1464`) and `consMove` (`:1525`)
-- receive — `legStep→legInv` threads its `nt` argument into both unchanged
-- (`:1603`, `:1609`), so this one bridge serves all three sites.
tokenExcl⇒noTwoTokens : (l : TwoLegs) (s : SysState) → TokenExcl l s → NoTwoTokens l s
tokenExcl⇒noTwoTokens l s tex = noTwoOf tex

-- BRIDGE 4 has MOVED, and is now WIRED — see §7f's `legJointVis` (ASSEMBLY slice
-- A1).  It used to be the visible api arm with only its `NoTwoTokens` slot filled,
-- still TAKING `VisLeaves l s s′`, `LegDriverStep` and `LegValStep` as arguments at
-- a GIVEN `s′`.  All three now come from ONE peel of `LiveLegApiExpose`'s ⁺ cone
-- inside the arm itself, so the arm takes the api STEP and returns its own `s′`;
-- the retired `VisLeaves` argument appears in NO arm signature any more.  It could
-- not stay here: it must come AFTER §7e's `tokenExcl-vis`, whose result it pairs
-- with at that one successor.

-- BRIDGE 5 (premise (a), AT THE ARM): the io-READ arm with its premise slot
-- filled.  Deliberately signature-FREE — the type is INHERITED from
-- `legInv-read`, so this definition typechecks only if `cellCp3-of`'s result is
-- literally the module parameter's type, and no transcription of the arm's ten
-- arguments can drift.
module _ (ch : (l : TwoLegs) (r : RState) → UpChainCp3 l (toSys r) × DnChainCp3 l (toSys r)) where

  -- the io-SYNC READ arm, premise-free in `cellCp3` once the PARKED alignment is
  -- available (instalment 2: it is not — this is the interface, type-checked)
  legInv-read⁺ = legInv-read (cellCp3-of ch)

------------------------------------------------------------------------
-- §4  THE FRAME LEMMA.
--
-- The backbone of the POSITION-PRESERVING step classes (the medium-τ drain at a
-- cell that is not the leg's, and `ldFix`): all six components the NARROWED
-- component reads are fixed, so every field transports by `subst`.  It is the
-- degenerate instance of §7's core and is kept because several assembly classes
-- have the six equalities outright and need nothing else.
------------------------------------------------------------------------

-- FRAME: a step fixing all six components the component reads preserves it
tokenExcl-frame : (l : TwoLegs) (s s′ : SysState)
  → upSrv    l s ≡ upSrv    l s′ → dnSrv    l s ≡ dnSrv    l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
  → TokenExcl l s → TokenExcl l s′
tokenExcl-frame l s s′ use dse cue cde ue de tex = tokenExcl
  (noTwo
    (λ h1 h2 → nUpSrvCli  (noTwoOf tex) (subst BFsHasBlk   (sym use) h1)
                                        (subst BFcHasBlk   (sym ue)  h2))
    (λ h1 h2 → nUpCellCli (noTwoOf tex) (subst CellFullBlk (sym cue) h1)
                                        (subst BFcHasBlk   (sym ue)  h2))
    (λ h1 h2 → nDnSrvCli  (noTwoOf tex) (subst BFsHasBlk   (sym dse) h1)
                                        (subst BFcHasBlk   (sym de)  h2))
    (λ h1 h2 → nDnCellCli (noTwoOf tex) (subst CellFullBlk (sym cde) h1)
                                        (subst BFcHasBlk   (sym de)  h2)))
  (λ h1 h2 → nUpSrvCell tex (subst BFsHasBlk (sym use) h1)
                            (subst CellFullBlk (sym cue) h2))
  (λ h1 h2 → nDnSrvCell tex (subst BFsHasBlk (sym dse) h1)
                            (subst CellFullBlk (sym cde) h2))

------------------------------------------------------------------------
-- §5  THE SCOPE FINDING ON PRESERVATION (slices A/B) — recorded here so no
-- successor re-derives it, and so the statement above is read with its cost.
--
-- Slice 0 (this file) is the STATEMENT, the base case, the frame and the four
-- bridges; the per-step theorem is NOT here.  While building the statement the
-- creation sites were enumerated against the real FSMs, and ONE of them is not
-- covered by the reviewed design.  In full:
--
-- (1)  DESTRUCTION SITES ARE AS PRICED.  The alignment's hard case — "the relay
--      leaves `cp3` while the chain is occupied" — happens only at the relay's
--      own `recvBFBlock` (`SysNode:945-949`: `cp3` has exactly ONE api row).
--      There the successor's three upstream antecedents are all refutable:
--      `cellUp` is fixed across an api step and `nUpCellCli` refutes it from the
--      co-firing client's occupancy; `upSrv` is fixed (node A does not fire) and
--      `nUpSrvCli` refutes it; the client's own successor is `bcSil` after the
--      co-firing `recvBFBlock`.  Only the LAST of the three needs a fact the
--      cones do not currently export (a SUCCESSOR-negative client keep) — and
--      `PipeSrvInv.UpSrvEvo`/`DnSrvEvo` (`:133-140`), which `driverExpose⁺`
--      already returns for both legs (`LiveLegApiCone:1262-1263`), are the
--      server-side precedent for exactly that shape.
--
-- (2)  *** THE CREATION SITE IS NOT COVERED, AND THE 3-SLOT WIDENING MOVES THE
--      DEBT RATHER THAN RETIRING IT. ***  The upstream chain FIRST becomes
--      occupied at node A's producer `a56` step (`pp5 → pp6`, the api
--      `sendBFBlock`), where `LiveLegApiExpose.vProdSend` pins
--      `upSrv l s′ ≡ bsBlk1 blkA`.  The relay is FIXED across that step (node A
--      fired), so `upChainCp3` at `s′` demands `RelayCp3 (relayOf l s)` — the
--      relay must ALREADY be at `cp3` when node A sends.  That is TRUE, and the
--      reason is the one Task 3 recorded in prose (`LiveLegStep:866-869`): node
--      A's BF SERVER accepts an api `sendBFBlock` only from its post-request
--      region (`BFsPos`'s `bsStart1`/`bsSil BF.stStreaming`, `SysNode:394-404`),
--      it enters that region only by reading the relay's `MsgRequestRange` off
--      the wire, and that request is written by the relay's own BF client
--      CO-FIRING with the relay driver's `cp2 → cp3` api `sendBFRequestRange`
--      (`SysNode:938-944`).  But NONE of that is expressible in the three
--      occupancy predicates above: the request path needs (i) the client's
--      REQUEST region (`bcReq1`/`bcSil BF.stBusy`), (ii) the up cell holding a
--      `MsgRequestRange` rather than a `MsgBlock` — the SAME cell key, so the
--      message type is the discriminator — and (iii) the server's post-request
--      region.  I.e. the chain that is genuinely inductive is the whole `cp3`
--      WINDOW (six links, message-type-discriminated), not the three
--      block-occupancy slots the review priced.
--
--      A cheaper-looking escape does NOT exist, and both alternatives were
--      checked before this was written: dropping `upSrv` from the chain moves the
--      same obligation onto the io FILL step (the widening's whole purpose), and
--      taking the alignment out of `AtPos` instead would be an edit to
--      `LiveLegInv` — a base module of this campaign.
--
--      One further asymmetry, which is why the window cannot simply be widened
--      to "the client is active": the client does NOT leave its streaming region
--      when the relay receives (`bcBlk1 b → bcSil BF.stStreaming`,
--      `SysNode:372`, decode `:382-386`), so "client active ⇒ `cp3`" is FALSE just after the
--      relay's receive.  A window statement must therefore discriminate
--      positions, not `BF.BFState`s.
--
-- (3)  CONSEQUENCE FOR THE BUDGET, reported not absorbed.  Slices A/B as briefed
--      (≈300-450 and ≈800-1,000) price the FOUR ARMS over the three-slot chain.
--      Closing (2) adds the request-path links on BOTH sides, each with the
--      io-key and message-type reasoning that cost `LiveLegIoCone` 591 lines and
--      `LiveLegApiCone` 1,382 for comparable content, plus the successor-negative
--      client layer of (1).  The honest projection therefore crosses the 2,100
--      cap, which is why this slice stops green here and the finding goes to the
--      controller rather than being worked around.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §6  *** THE RECORD OF FINDING 2: `NoTwoTokens` WAS FALSE AS STATED, AND THE
-- FIX IS NOW APPLIED. ***
--
-- Instalment 1 (commit `37e4e75`) MACHINE-CHECKED the falseness in this very
-- module; instalment 2 applied the controller-approved (C1)-pattern fix to
-- `LiveLegStep`'s record (the two cell fields now read `CellFullBlk`, and the two
-- `cellFull⇒hasBlk` wrappers at its `relayMove`/`consMove` use sites are gone).
-- The four lemmas that DERIVED `⊥` — `CellDrain⁺`, `noTwo-post-read-up-⊥`,
-- `noTwo-post-read-dn-⊥`, `noTwoTokens-unprovable` — are therefore RETIRED: at
-- the fixed field types they no longer typecheck, and that failure IS the fix's
-- signal.  They live in git history at `37e4e75`; what follows is this campaign's
-- required prose RECORD of the finding, kept because the same trap has now been
-- walked into twice (`LiveLegInv:227-241` recorded it for `AtPos`, and
-- `NoTwoTokens`, written later, regressed to `CellHasBlk`).
--
-- THE REFUTATION, as it stood.  The two CELL exclusions were stated with
-- `CellHasBlk`, which holds of `draining` as well as `full` (`PipeInv:467-470`),
-- and `draining` is the POST-READ phase at which the far-end BF client HAS JUST
-- TAKEN THE BLOCK.  `noTwo-post-read-up-⊥` had the type
--
--   (l : TwoLegs) (s : SysState) (b : Block₃)
--     → cellUp l s ≡ draining (blkPayload b) → CliHas⁺ b (upClient l s)
--     → NoTwoTokens l s → ⊥
--
-- and its body was one line: `nUpCellCli nt (subst CellHasBlk (sym ec) tt)
-- (subst BFcHasBlk (sym ecl) tt)` — both antecedents reduce to `⊤` because
-- `blkPayload b` is a `blockFetch (MsgBlock b)` wire tuple
-- (`PipeValFill:111-112`, `PipeInv:449-451`) and `bcBlk1 b` is `BFcHasBlk`
-- outright.  The `dnClient` twin and their join were the same one-liner.
--
-- WHY NO CONCRETE WITNESS WAS NEEDED (the dilemma, unchanged and worth keeping).
-- The shape is produced by `LiveLegStep`'s own io-READ arm's REACHABLE successor:
-- `legInv-read` returns `r′` carrying `rStepʷ …` whose fired cell is
-- `draining x` and whose reader holds the block.  So EITHER a reachable state has
-- that shape and the old premise was false there, OR none does and the
-- `lpUpCell → lpUpClient` hop never fires, which would make the token-location
-- argument vacuous at the one hop the block must cross.
--
-- The four ⊥-deriving lemmas that stood here are RETIRED by the fix (they
-- cannot typecheck against the corrected field types); the paragraph above is
-- their record.  Nothing else in this module changes: §1's `UpChain`/`DnChain`
-- were already stated the fixed way, and §4's frame now `subst`s `CellFullBlk`.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §7  PRESERVATION OF THE EXCLUSIONS — the proved half of the component.
--
-- THE SHAPE OF THE WHOLE SECTION.  Every step class reduces to ONE core lemma
-- (§7a) whose six hypotheses are the only things a step class ever has to say
-- about itself.  Read them as "who can be OCCUPIED at the successor, and why":
--
--   (a) a CLIENT that holds at `s′` either held at `s`, or it JUST READ — and a
--       read leaves the source cell `full` and the successor cell NOT full;
--   (b) a SERVER never GAINS a block on the io/τ axis (it enters `bsBlk1` only
--       through the api `sendBFBlock`);
--   (c) a CELL that is full at `s′` was full at `s`, or it was just FILLED by the
--       leg's own server — which held the block at `s` and does not at `s′`.
--
-- The six exclusions then pay for each other exactly as the reviewer's `a56`
-- verification predicted, with the two AUX server/cell fields (§2) as the missing
-- link at the read: F1 needs (a)'s read arm to hand it the source CELL, and F5
-- needs (c)'s fill arm to hand it the successor SERVER.
--
-- WHAT IS PROVED HERE, HONESTLY.  Three of the four step classes are proved:
-- the FRAME class (§4), the MEDIUM-τ DRAIN (§7c, premise-FREE) and — modulo ONE
-- named leaf each — the two io classes (§7d) and the VISIBLE api class (§7e).
-- The three leaves are NOT postulates and NOT weakenings: each is a fact the
-- system genuinely has, stated at the exact type its own cone would deliver it
-- at, and each is UNAVAILABLE FROM WHAT THE CONES EXPORT TODAY for a stated
-- structural reason.  They are, in the order the arms consume them:
--
--   (P1) *** DISCHARGED (session-55). ***  The FROZEN, SUCCESSOR-negative io
--        classifiers (`PipeNodeIoEvo:126-132`) at the ⁺ cone's successor were the
--        first leaf: PROVED by `top-nodes-io-evo`, but at ITS OWN successor
--        witness, while the ⁺ cone returned only the PREDECESSOR-directed
--        `CliIoCls⁺`/`SrvIoCls⁺`.  `LiveLegIoCone`'s §1b now instantiates the
--        granted `IoFacts` dispatch ONCE at the PAIRED facts
--        `CliIoClsP = CliIoCls⁺ × CliIoCls`, `SrvIoClsP = SrvIoCls⁺ × SrvIoCls`,
--        so a single cone call (`top-nodes-io-evoP⁺`) reports both directions at
--        ONE successor — and the frozen arms cost NOTHING: they are the FOURTH
--        components of `decBF{s,c}-{send,receive}BF-succ`, computed and discarded
--        at the four callbacks all along.  The two io arms below therefore take
--        `IoCone`, the cone's own output pair, in place of the leaf, and the ⁺-only
--        view (`bd⁺`/`facts⁺`/`top-nodes-io-evo⁺`) is `proj₁` of the paired one, so
--        `LiveLegStep` is untouched.  NO base module was edited.
--   (P2) *** DISCHARGED (session-55, GRANT #1's second exercise). ***  The io
--        WRITE-OWNERSHIP fact — a wire INPUT that puts a BLOCK into the leg's own
--        BF cell was written by that leg's own BF server, which therefore HELD the
--        block and no longer does — is now the THIRD component of the paired
--        server fact (`LiveLegIoCone.SrvWriteOwn`), and §7d projects the leg's own
--        out of the four with `ownUpOf`/`ownDnOf`.  Its server-side half was
--        banked (`PipeFillSource.blockFill-forces-srv`); the missing half was the
--        IDENTIFICATION of the firing peer, i.e. the SERVER mirror of the
--        ownership premise session-53 added to `IoFacts.cRefl` for CLIENTS.
--        `PipeNodeIoEvo`'s §1c now supplies it: `NoSrvWriteAt` + the four
--        per-node witnesses, with `sRefl` taking it exactly as `cRefl` takes
--        `NoCliReadAt`.  `facts₀` ignores the new argument, so the frozen cone is
--        re-derived and the FULL LTL endpoint (`LTL.BlockLiveness`) was verified
--        GREEN (EXIT=0, 2 min 43 s) before the commit carrying the edit landed.
--   (P3) *** DISCHARGED (session-55). ***  The api CREATION fact — if the leg's
--        server did NOT hold before a visible step and does after it, the step is
--        node A's `a56` send (source `ProdNotSent`) resp. the relay's forward
--        (source `RelayHas`) — is now two PROVED fields of the visible cone's own
--        record, `VisLeaves⁺.vUpSrvGain`/`vDnSrvGain`, beside `vProdSend`, whose
--        consequent halves they complete.  Both fall out of
--        `PipeProdFire.decProd-sbb-pp5` at the ONE place where the co-firing
--        DRIVER STEP is in hand (`srvUp-of`, and the relay classifier's new ninth
--        component for the dn half); `ldProd` projects that step away, which is
--        why it could not be done downstream.
--
-- THE CLOSURE, then: all three are gone.  `tokenExcl-fill`/`-read` take the io
-- cone's own two families (`IoCone` — exactly `legInv-fill`'s `allCli`/`allSrv`
-- binders) and `tokenExcl-vis` takes `VisLeaves` and `Coupled`, which the assembly
-- already carries; NO arm takes a leaf.  The names `SrvGainUp`/`SrvGainDn` survive
-- as the TYPES of the two proved cone fields, and §7d's `IoCone` as the cone's
-- output type — nothing here is stated-but-unproved any more.
------------------------------------------------------------------------

-- eliminate a disjunction into `⊥` (the campaign's `with`-free discipline: every
-- ⊎ is consumed by a pattern-matching helper, never by a `with`)
orE : {A B : Set} → (A → ⊥) → (B → ⊥) → A ⊎ B → ⊥
orE f g (inj₁ a) = f a
orE f g (inj₂ b) = g b

-- map a disjunction's SECOND arm (same discipline, for the answers that are
-- themselves disjunctions rather than refutations)
mapR : {A B C : Set} → (B → C) → A ⊎ B → A ⊎ C
mapR f (inj₁ a) = inj₁ a
mapR f (inj₂ b) = inj₂ (f b)

------------------------------------------------------------------------
-- §7a  THE CORE.  Six occupancy answers ⇒ the six exclusions at the successor.
------------------------------------------------------------------------

-- PRESERVATION CORE: the exclusions are preserved by any step that can answer
-- (a) for its two clients, (b) for its two servers and (c) for its two cells
tokenExcl-core : (l : TwoLegs) (s s′ : SysState)
  -- (a) the two CLIENTS: held already, or just read (source cell full, successor not)
  → (BFcHasBlk (upClient l s′) → BFcHasBlk (upClient l s)
       ⊎ (CellFullBlk (cellUp l s) × (CellFullBlk (cellUp l s′) → ⊥)))
  → (BFcHasBlk (dnClient l s′) → BFcHasBlk (dnClient l s)
       ⊎ (CellFullBlk (cellDn l s) × (CellFullBlk (cellDn l s′) → ⊥)))
  -- (b) the two SERVERS never gain
  → (BFsHasBlk (upSrv l s′) → BFsHasBlk (upSrv l s))
  → (BFsHasBlk (dnSrv l s′) → BFsHasBlk (dnSrv l s))
  -- (c) the two CELLS: full already, or just filled by the leg's own server
  → (CellFullBlk (cellUp l s′) → CellFullBlk (cellUp l s)
       ⊎ (BFsHasBlk (upSrv l s) × (BFsHasBlk (upSrv l s′) → ⊥)))
  → (CellFullBlk (cellDn l s′) → CellFullBlk (cellDn l s)
       ⊎ (BFsHasBlk (dnSrv l s) × (BFsHasBlk (dnSrv l s′) → ⊥)))
  → TokenExcl l s → TokenExcl l s′
tokenExcl-core l s s′ acu acd bsu bsd ccu ccd tex = tokenExcl
  (noTwo
    -- F1  (upSrv , upClient): the client held (source F1), or it just read and
    -- the source cell was full (source F5)
    (λ h1 h2 → orE (λ hcli → nUpSrvCli (noTwoOf tex) (bsu h1) hcli)
                   (λ hce  → nUpSrvCell tex (bsu h1) (proj₁ hce))
                   (acu h2))
    -- F2  (cellUp , upClient): if the client held, the cell was full (source F2)
    -- or the server held it (source F1); if the client just read, the successor
    -- cell is NOT full and the hypothesis is refuted outright
    (λ h1 h2 → orE (λ hcli → orE (λ hce  → nUpCellCli (noTwoOf tex) hce hcli)
                                 (λ hsrv → nUpSrvCli (noTwoOf tex) (proj₁ hsrv) hcli)
                                 (ccu h1))
                   (λ hce  → proj₂ hce h1)
                   (acu h2))
    -- F3, F4: the downstream mirrors
    (λ h1 h2 → orE (λ hcli → nDnSrvCli (noTwoOf tex) (bsd h1) hcli)
                   (λ hce  → nDnSrvCell tex (bsd h1) (proj₁ hce))
                   (acd h2))
    (λ h1 h2 → orE (λ hcli → orE (λ hce  → nDnCellCli (noTwoOf tex) hce hcli)
                                 (λ hsrv → nDnSrvCli (noTwoOf tex) (proj₁ hsrv) hcli)
                                 (ccd h1))
                   (λ hce  → proj₂ hce h1)
                   (acd h2)))
  -- F5  (upSrv , cellUp): the cell was full already (source F5), or it was just
  -- filled — and then the filling server does NOT hold at the successor
  (λ h1 h2 → orE (λ hce  → nUpSrvCell tex (bsu h1) hce)
                 (λ hsrv → proj₂ hsrv h1)
                 (ccu h2))
  -- F6: the downstream mirror
  (λ h1 h2 → orE (λ hce  → nDnSrvCell tex (bsd h1) hce)
                 (λ hsrv → proj₂ hsrv h1)
                 (ccd h2))

------------------------------------------------------------------------
-- §7b  THE CELL LEMMAS, generic in the written phase.  `LiveLegStep`'s cell
-- machinery is FORWARD (it transports an occupancy along the step); the
-- exclusions read cells BACKWARD, so the same `setRead`/`cell-drain-eq⁺`
-- dispatches are used in the other direction here.
------------------------------------------------------------------------

-- the fired key's cell IS the written phase in the successor (the phase-GENERIC
-- `LiveLegStep.setHit-in`, which is stated at `full x` only)
setHit-np : (g : Link → Dir → IDs → CopyPhase)
            (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (np : CopyPhase)
          → phase-upd g l₀ (setCell (g l₀) d₀ id₀ np) l₀ d₀ id₀ ≡ np
setHit-np g l₀ d₀ id₀ np
  rewrite ≟-yes-refl l₀ | ≟-yes-refl d₀ | ≟-yes-refl id₀ = refl

-- BACKWARD across a cell UPDATE: a successor cell satisfying `P` is either at an
-- UNTOUCHED key (and `P` holds of the source cell) or IS the fired key (and the
-- successor phase is the written one)
cellHit : (P : CopyPhase → Set) (g : Link → Dir → IDs → CopyPhase)
    (k : Link) (kd : Dir) (ki : IDs) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (np : CopyPhase)
    {cu cu′ : CopyPhase}
  → cu  ≡ g k kd ki
  → cu′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ np) k kd ki
  → P cu′ → P cu ⊎ ((k ≡ l₀) × (kd ≡ d₀) × (ki ≡ id₀) × (cu′ ≡ np))
cellHit P g k kd ki l₀ d₀ id₀ np ceq c′eq h
  with setRead g l₀ d₀ id₀ np k kd ki
... | inj₁ eq                    = inj₁ (subst P (sym (trans ceq (trans eq (sym c′eq)))) h)
... | inj₂ (e1 , e2 , e3 , eq)    = inj₂ (e1 , e2 , e3 , trans c′eq eq)

-- BACKWARD unconditionally, when `P` is FALSE at the written phase (the READ's
-- `draining x`): the fired key's successor fails `P`, so `P` at the successor
-- forces an untouched key
cellBack : (P : CopyPhase → Set) (g : Link → Dir → IDs → CopyPhase)
    (k : Link) (kd : Dir) (ki : IDs) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (np : CopyPhase)
    {cu cu′ : CopyPhase}
  → (P np → ⊥)
  → cu  ≡ g k kd ki
  → cu′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ np) k kd ki
  → P cu′ → P cu
cellBack P g k kd ki l₀ d₀ id₀ np ¬np ceq c′eq h
  with cellHit P g k kd ki l₀ d₀ id₀ np ceq c′eq h
... | inj₁ hc                 = hc
... | inj₂ (_ , _ , _ , eq)   = ⊥-elim (¬np (subst P eq h))

-- BACKWARD across a MEDIUM DRAIN: the drained key's successor is `empty`, so a
-- predicate false at `empty` (every cell OCCUPANCY) transports back
cellDrainBack : (m : MedState) (i : Link) (d₀ : Dir) (id₀ : IDs)
    (kl : Link) (kd : Dir) (kid : IDs) (P : CopyPhase → Set)
  → (P empty → ⊥)
  → P (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀) kl kd kid)
  → P (phase m kl kd kid)
cellDrainBack m i d₀ id₀ kl kd kid P ¬e h
  with cell-drain-eq⁺ m i d₀ id₀ kl kd kid
... | inj₁ eq                 = subst P eq h
... | inj₂ (_ , _ , _ , eq)   = ⊥-elim (¬e (subst P eq h))

-- at a READ HIT on the leg's own key: the source cell was `full x` and the
-- successor cell is `draining x` (the two facts (a)'s read arm hands the core)
readHitCells : (g : Link → Dir → IDs → CopyPhase) (k : Link)
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {cu cu′ : CopyPhase}
  → cu  ≡ g k hi N2N_BlockFetch
  → cu′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (draining x)) k hi N2N_BlockFetch
  → g l₀ d₀ id₀ ≡ full x
  → l₀ ≡ k → d₀ ≡ hi → id₀ ≡ N2N_BlockFetch
  → (cu ≡ full x) × (cu′ ≡ draining x)
readHitCells g k l₀ d₀ id₀ x ceq c′eq sf refl refl refl =
  trans ceq sf , trans c′eq (setHit-np g l₀ d₀ id₀ (draining x))

-- a BF wire READ carrying a block is at the reader's OWN key on the BlockFetch
-- channel: the five other channels make `BlkReadAt` `⊥`
blkRead-key : (k : Link) (kd : Dir) (q : BFcPos)
              (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → BlkReadAt k kd q (output l₀ d₀ id₀) x
  → (l₀ ≡ k) × (d₀ ≡ kd) × (id₀ ≡ N2N_BlockFetch) × PlIsBlk x
blkRead-key k kd q l₀ d₀ N2N_BlockFetch   x (e1 , e2 , pb , _) = e1 , e2 , refl , pb
blkRead-key k kd q l₀ d₀ N2N_ChainSync    x ()
blkRead-key k kd q l₀ d₀ N2N_TxSubmission x ()
blkRead-key k kd q l₀ d₀ N2N_KeepAlive    x ()
blkRead-key k kd q l₀ d₀ N2N_LeiosNotify  x ()
blkRead-key k kd q l₀ d₀ N2N_LeiosFetch   x ()

------------------------------------------------------------------------
-- §7c  THE MEDIUM-τ DRAIN ARM — PREMISE-FREE.
--
-- The nodes are untouched by a drain, so all four peer slots are literally equal
-- and both cells transport backward through `cellDrainBack`.  The four cell
-- equations are exactly what `PipeTauIo.cellUp-key`/`cellDn-key` give at the
-- source and at the drained successor, i.e. what `LiveLegStep`'s own medium-τ arm
-- has in hand.
------------------------------------------------------------------------

-- ONE medium drain preserves the exclusions
tokenExcl-drain : (l : TwoLegs) (s s′ : SysState)
    (m : MedState) (i : Link) (d₀ : Dir) (id₀ : IDs)
  → cellUp l s ≡ phase m (upLink l) hi N2N_BlockFetch
  → cellDn l s ≡ phase m (dnLink l) hi N2N_BlockFetch
  → cellUp l s′ ≡ phase-upd (phase m) i (flipCell (phase m i) d₀ id₀)
                    (upLink l) hi N2N_BlockFetch
  → cellDn l s′ ≡ phase-upd (phase m) i (flipCell (phase m i) d₀ id₀)
                    (dnLink l) hi N2N_BlockFetch
  → upSrv    l s ≡ upSrv    l s′ → dnSrv    l s ≡ dnSrv    l s′
  → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
  → TokenExcl l s → TokenExcl l s′
tokenExcl-drain l s s′ m i d₀ id₀ cuS cdS cuS′ cdS′ use dse ue de tex =
  tokenExcl-core l s s′
    (λ h → inj₁ (subst BFcHasBlk (sym ue) h))
    (λ h → inj₁ (subst BFcHasBlk (sym de) h))
    (λ h → subst BFsHasBlk (sym use) h)
    (λ h → subst BFsHasBlk (sym dse) h)
    (λ h → inj₁ (subst CellFullBlk (sym cuS)
                   (cellDrainBack m i d₀ id₀ (upLink l) hi N2N_BlockFetch
                      CellFullBlk (λ ()) (subst CellFullBlk cuS′ h))))
    (λ h → inj₁ (subst CellFullBlk (sym cdS)
                   (cellDrainBack m i d₀ id₀ (dnLink l) hi N2N_BlockFetch
                      CellFullBlk (λ ()) (subst CellFullBlk cdS′ h))))
    tex

------------------------------------------------------------------------
-- §7d  THE TWO io ARMS, and the two io leaves (P1), (P2).
------------------------------------------------------------------------

-- (P1, DISCHARGED) THE io CONE'S OWN OUTPUT: the two PAIRED slot families
-- `LiveLegIoCone.top-nodes-io-evoP⁺` reports at ONE successor — the ⁺
-- (predecessor-directed) facts the `legInv-*` arm reads AND the FROZEN
-- successor-directed classifiers these arms read.  This is a cone OUTPUT, i.e.
-- exactly the pair of binders `LiveLegStep.legInv-fill` already holds at this
-- point (`allCli`/`allSrv`), NOT a premise: §7d used to take the frozen families
-- as the leaf (P1) because no cone returned them at the ⁺ successor.
IoCone : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
IoCone s s′ e a = AllCliP s s′ e a × AllSrvP s s′ e a

-- (P2, DISCHARGED) the io WRITE-OWNERSHIP answers — "a BLOCK arriving in the
-- leg's own up (resp. down) BF cell came from that leg's own server, which held it
-- and now does not" — are now COMPONENTS of the cone's paired server facts
-- (`LiveLegIoCone`'s §1c, off `PipeFillSource.blockFill-forces-srv` at the fired
-- slot and off `PipeNodeIoEvo`'s new `NoSrvWriteAt` premise at every fixed one).
-- These two projections pick the leg's own out of the four; `SrvWriteOwn`'s fourth
-- antecedent `PlIsBlk x` IS `CellHasBlk (full x)` by definition, so the arm's
-- clause bodies below are unchanged.

-- the leg's UPSTREAM write-ownership answer out of the four
ownUpOf : (l : TwoLegs) (s s′ : SysState)
          (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
        → AllSrvP s s′ (input l₀ d₀ id₀) x
        → SrvWriteOwn (upLink l) hi (upSrv l s) (upSrv l s′) (input l₀ d₀ id₀) x
-- (grant #7) the write-ownership half is now the THIRD of four components (the
-- fired row is trailing), so the projection reaches one level deeper
ownUpOf legBD s s′ l₀ d₀ id₀ x (q , _ , _ , _) = proj₁ (proj₂ (proj₂ q))
ownUpOf legCD s s′ l₀ d₀ id₀ x (_ , q , _ , _) = proj₁ (proj₂ (proj₂ q))

-- the leg's DOWNSTREAM write-ownership answer out of the four
ownDnOf : (l : TwoLegs) (s s′ : SysState)
          (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
        → AllSrvP s s′ (input l₀ d₀ id₀) x
        → SrvWriteOwn (dnLink l) hi (dnSrv l s) (dnSrv l s′) (input l₀ d₀ id₀) x
ownDnOf legBD s s′ l₀ d₀ id₀ x (_ , _ , q , _) = proj₁ (proj₂ (proj₂ q))
ownDnOf legCD s s′ l₀ d₀ id₀ x (_ , _ , _ , q) = proj₁ (proj₂ (proj₂ q))

-- a client does not GAIN a block on a wire INPUT (`BlkReadAt` is `⊥` off an
-- `output`, so the frozen classifier's third arm is absurd there)
-- (the peer KEY *and* the whole LABEL are explicit: under an `input` label the
-- classifier's third arm reduces to `⊥`, so `CliIoCls`'s type no longer MENTIONS
-- either — the campaign's explicit-index rule for indices that survive only in a
-- ⊥-reducing arm, and the measured cost of getting it wrong is two
-- `[UnsolvedMetaVariables]` build cycles)
cliNoGain-in : (k : Link) (kd : Dir) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
               {q q′ : BFcPos}
             → CliIoCls k kd q q′ (input l₀ d₀ id₀) x → BFcHasBlk q′ → BFcHasBlk q
cliNoGain-in k kd l₀ d₀ id₀ x (inj₁ refl)      h = h
cliNoGain-in k kd l₀ d₀ id₀ x (inj₂ (inj₁ ¬h)) h = ⊥-elim (¬h h)
cliNoGain-in k kd l₀ d₀ id₀ x (inj₂ (inj₂ ())) h

-- a server never GAINS a block on an io (it enters `bsBlk1` only from the api)
srvNoGain : {bfs bfs′ : BFsPos} → SrvIoCls bfs bfs′ → BFsHasBlk bfs′ → BFsHasBlk bfs
srvNoGain (inj₁ refl) h = h
srvNoGain (inj₂ ¬h)   h = ⊥-elim (¬h h)

-- ONE hidden io-SYNC FILL preserves the exclusions, given (P1) and (P2)
tokenExcl-fill : (l : TwoLegs) (s s′ : SysState)
    (g : Link → Dir → IDs → CopyPhase)
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → cellUp l s ≡ g (upLink l) hi N2N_BlockFetch
  → cellDn l s ≡ g (dnLink l) hi N2N_BlockFetch
  → cellUp l s′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (full x))
                    (upLink l) hi N2N_BlockFetch
  → cellDn l s′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (full x))
                    (dnLink l) hi N2N_BlockFetch
  → IoCone s s′ (input l₀ d₀ id₀) x
  → TokenExcl l s → TokenExcl l s′
tokenExcl-fill l s s′ g l₀ d₀ id₀ x cuS cdS cuS′ cdS′ (cliP , srvP) tex =
  tokenExcl-core l s s′
    (λ h → inj₁ (cliNoGain-in (upLink l) hi l₀ d₀ id₀ x
                   (pickCliUp l s s′ (input l₀ d₀ id₀) x allCli) h))
    (λ h → inj₁ (cliNoGain-in (dnLink l) hi l₀ d₀ id₀ x
                   (pickCliDn l s s′ (input l₀ d₀ id₀) x allCli) h))
    (λ h → srvNoGain (pickSrvUp l s s′ allSrv) h)
    (λ h → srvNoGain (pickSrvDn l s s′ allSrv) h)
    (λ h → mapR (λ { (e1 , e2 , e3 , eq) → ownU e1 e2 e3 (subst CellFullBlk eq h) })
                (cellHit CellFullBlk g (upLink l) hi N2N_BlockFetch l₀ d₀ id₀ (full x)
                   cuS cuS′ h))
    (λ h → mapR (λ { (e1 , e2 , e3 , eq) → ownD e1 e2 e3 (subst CellFullBlk eq h) })
                (cellHit CellFullBlk g (dnLink l) hi N2N_BlockFetch l₀ d₀ id₀ (full x)
                   cdS cdS′ h))
    tex
  where
  -- the two FROZEN families, read off the cone's paired ones (P1)
  allCli = frozenCli s s′ (input l₀ d₀ id₀) x cliP
  allSrv = frozenSrv s s′ (input l₀ d₀ id₀) x srvP
  -- the leg's two WRITE-OWNERSHIP answers, read off the same server family (P2)
  ownU = ownUpOf l s s′ l₀ d₀ id₀ x srvP
  ownD = ownDnOf l s s′ l₀ d₀ id₀ x srvP

-- ONE hidden io-SYNC READ preserves the exclusions, given (P1).  The read needs
-- NO ownership leaf: the frozen client classifier's own third arm pins the read
-- to the reader's key, which is what identifies the fired cell with the leg's.
tokenExcl-read : (l : TwoLegs) (s s′ : SysState)
    (g : Link → Dir → IDs → CopyPhase)
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → cellUp l s ≡ g (upLink l) hi N2N_BlockFetch
  → cellDn l s ≡ g (dnLink l) hi N2N_BlockFetch
  → cellUp l s′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (draining x))
                    (upLink l) hi N2N_BlockFetch
  → cellDn l s′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (draining x))
                    (dnLink l) hi N2N_BlockFetch
  → g l₀ d₀ id₀ ≡ full x
  → IoCone s s′ (output l₀ d₀ id₀) x
  → TokenExcl l s → TokenExcl l s′
tokenExcl-read l s s′ g l₀ d₀ id₀ x cuS cdS cuS′ cdS′ sf (cliP , srvP) tex =
  tokenExcl-core l s s′
    (cliRead-ans (upLink l) (upClient l s) (upClient l s′)
       (pickCliUp l s s′ (output l₀ d₀ id₀) x allCli) cuS cuS′)
    (cliRead-ans (dnLink l) (dnClient l s) (dnClient l s′)
       (pickCliDn l s s′ (output l₀ d₀ id₀) x allCli) cdS cdS′)
    (λ h → srvNoGain (pickSrvUp l s s′ allSrv) h)
    (λ h → srvNoGain (pickSrvDn l s s′ allSrv) h)
    (λ h → inj₁ (cellBack CellFullBlk g (upLink l) hi N2N_BlockFetch l₀ d₀ id₀
                   (draining x) (λ ()) cuS cuS′ h))
    (λ h → inj₁ (cellBack CellFullBlk g (dnLink l) hi N2N_BlockFetch l₀ d₀ id₀
                   (draining x) (λ ()) cdS cdS′ h))
    tex
  where
  -- the two FROZEN families, read off the cone's paired ones (P1)
  allCli = frozenCli s s′ (output l₀ d₀ id₀) x cliP
  allSrv = frozenSrv s s′ (output l₀ d₀ id₀) x srvP
  -- the READ's client answer (a): fixed, absurd, or the hit — and on the hit the
  -- source cell IS `full x` (a block, by `PlIsBlk`) and the successor `draining x`
  cliRead-ans : (k : Link) (q q′ : BFcPos)
              → CliIoCls k hi q q′ (output l₀ d₀ id₀) x
              → {cu cu′ : CopyPhase}
              → cu  ≡ g k hi N2N_BlockFetch
              → cu′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (draining x))
                        k hi N2N_BlockFetch
              → BFcHasBlk q′ → BFcHasBlk q ⊎ (CellFullBlk cu × (CellFullBlk cu′ → ⊥))
  cliRead-ans k q q′ (inj₁ refl)      ceq c′eq h = inj₁ h
  cliRead-ans k q q′ (inj₂ (inj₁ ¬h)) ceq c′eq h = ⊥-elim (¬h h)
  cliRead-ans k q q′ (inj₂ (inj₂ br)) ceq c′eq h =
    let (k1 , k2 , k3 , blk) = blkRead-key k hi q′ l₀ d₀ id₀ x br
        (cf , cd)            = readHitCells g k l₀ d₀ id₀ x ceq c′eq sf k1 k2 k3
    in  inj₂ (subst CellFullBlk (sym cf) blk , (λ h′ → subst CellFullBlk cd h′))

------------------------------------------------------------------------
-- §7e  THE VISIBLE api ARM, and the api leaf (P3).
--
-- On the api axis BOTH CELLS ARE FIXED — every `LegDriverStep` constructor
-- carries `cellUp`/`cellDn` equalities — so (c) is pure transport and the whole
-- arm turns on the two SERVER slots.  `VisLeaves⁺.vUpSrvKeep`/`vDnSrvKeep` give
-- the PREDECESSOR-negative disjunct, whose second arm is exactly the CREATION
-- case; (P3) is what names its source phase, and `Coupled` then refutes every
-- other occupancy from that phase (this is the reviewer's `a56` argument, and it
-- is the only place the couplings are used).
------------------------------------------------------------------------

-- (P3, DISCHARGED) the api CREATION answer, upstream: a step that makes the leg's
-- up server hold IS node A's `a56` send, whose source producer has NOT sent.  This
-- is now the TYPE OF A PROVED FIELD, `VisLeaves⁺.vUpSrvGain` — `LiveLegApiExpose`'s
-- §5 reads the producer's phase off the fired `sendBFBlock` with
-- `PipeProdFire.decProd-sbb-pp5`, at the ONE site where the driver STEP is still in
-- hand (`srvUp-of`; `ldProd` projects it away, which is why it cannot be done here)
SrvGainUp : (l : TwoLegs) (s s′ : SysState) → Set
SrvGainUp l s s′ = (BFsHasBlk (upSrv l s) → ⊥) → BFsHasBlk (upSrv l s′)
                 → ProdNotSent (prodOf l s)

-- (P3, DISCHARGED) the api CREATION answer, downstream: the mirror, proved as
-- `VisLeaves⁺.vDnSrvGain` off the relay classifier's own new source-phase component
SrvGainDn : (l : TwoLegs) (s s′ : SysState) → Set
SrvGainDn l s s′ = (BFsHasBlk (dnSrv l s) → ⊥) → BFsHasBlk (dnSrv l s′)
                 → RelayHas (relayOf l s)

-- ONE visible api step preserves the exclusions, given (P3).  Stated at the
-- COMPONENT equalities/disjuncts the four `LegDriverStep` constructors supply, so
-- `tokenExcl-vis` below is a four-line dispatch.
tokenExcl-api : (l : TwoLegs) (s s′ : SysState)
  → cellUp l s ≡ cellUp l s′ → cellDn l s ≡ cellDn l s′
  → ((upClient l s ≡ upClient l s′) ⊎ (BFcHasBlk (upClient l s′) → ⊥))
  → ((dnClient l s ≡ dnClient l s′) ⊎ (BFcHasBlk (dnClient l s′) → ⊥))
  → ((upSrv l s ≡ upSrv l s′) ⊎ (BFsHasBlk (upSrv l s) → ⊥))
  → ((dnSrv l s ≡ dnSrv l s′) ⊎ (BFsHasBlk (dnSrv l s) → ⊥))
  → SrvGainUp l s s′ → SrvGainDn l s s′
  → Coupled l s → TokenExcl l s → TokenExcl l s′
tokenExcl-api l s s′ cue cde ucE dcE usE dsE gU gD cpl tex = tokenExcl
  (noTwo
    -- F1: the client is fixed (or absurd); the server is fixed (source F1) or was
    -- EMPTY — and then (P3) + the client's own coupling contradict the producer
    (λ h1 h2 → orE (λ ue → orE (λ use → nUpSrvCli (noTwoOf tex)
                                          (subst BFsHasBlk (sym use) h1)
                                          (subst BFcHasBlk (sym ue) h2))
                               (λ ¬us → prodSent-notSent-⊥ (prodOf l s)
                                          (ucP (subst BFcHasBlk (sym ue) h2))
                                          (gU ¬us h1))
                               usE)
                   (λ ¬uc → ¬uc h2)
                   ucE)
    -- F2: both cells are fixed and the client is fixed (or absurd) — source F2
    (λ h1 h2 → orE (λ ue → nUpCellCli (noTwoOf tex) (subst CellFullBlk (sym cue) h1)
                                      (subst BFcHasBlk (sym ue) h2))
                   (λ ¬uc → ¬uc h2)
                   ucE)
    -- F3, F4: the downstream mirrors, with the relay's `RelayHas`/`RelayFwd`
    -- disjointness in place of the producer's
    (λ h1 h2 → orE (λ de → orE (λ dse → nDnSrvCli (noTwoOf tex)
                                          (subst BFsHasBlk (sym dse) h1)
                                          (subst BFcHasBlk (sym de) h2))
                               (λ ¬ds → relayHas-fwd-⊥ (relayOf l s) (gD ¬ds h1)
                                          (dcP (subst BFcHasBlk (sym de) h2)))
                               dsE)
                   (λ ¬dc → ¬dc h2)
                   dcE)
    (λ h1 h2 → orE (λ de → nDnCellCli (noTwoOf tex) (subst CellFullBlk (sym cde) h1)
                                      (subst BFcHasBlk (sym de) h2))
                   (λ ¬dc → ¬dc h2)
                   dcE))
  -- F5: the cell is fixed; the server is fixed (source F5) or was EMPTY — and
  -- then (P3) + the CELL's coupling contradict the producer
  (λ h1 h2 → orE (λ use → nUpSrvCell tex (subst BFsHasBlk (sym use) h1)
                            (subst CellFullBlk (sym cue) h2))
                 (λ ¬us → prodSent-notSent-⊥ (prodOf l s)
                            (cuP (cellFull⇒hasBlk (cellUp l s)
                                    (subst CellFullBlk (sym cue) h2)))
                            (gU ¬us h1))
                 usE)
  -- F6: the downstream mirror
  (λ h1 h2 → orE (λ dse → nDnSrvCell tex (subst BFsHasBlk (sym dse) h1)
                            (subst CellFullBlk (sym cde) h2))
                 (λ ¬ds → relayHas-fwd-⊥ (relayOf l s) (gD ¬ds h1)
                            (cdP (cellFull⇒hasBlk (cellDn l s)
                                    (subst CellFullBlk (sym cde) h2))))
                 dsE)
  where
  -- `Coupled`'s four clauses, named (`PipeInv`'s own component order)
  cuP : CellHasBlk (cellUp l s) → ProdSent (prodOf l s)
  cuP = proj₁ cpl
  ucP : BFcHasBlk (upClient l s) → ProdSent (prodOf l s)
  ucP = proj₁ (proj₂ cpl)
  cdP : CellHasBlk (cellDn l s) → RelayFwd (relayOf l s)
  cdP = proj₁ (proj₂ (proj₂ cpl))
  dcP : BFcHasBlk (dnClient l s) → RelayFwd (relayOf l s)
  dcP = proj₂ (proj₂ (proj₂ cpl))

-- THE VISIBLE ARM AT THE CONE'S OWN WITNESSES: one clause per `LegDriverStep`
-- constructor, each handing `tokenExcl-api` that constructor's equalities.  The
-- two SERVER disjuncts come from `VisLeaves` (proved by `driverExpose⁺` for every
-- api step), the two CLIENT ones from the constructor itself.
tokenExcl-vis : (l : TwoLegs) (s s′ : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → Coupled l s
  → VisLeaves l s s′ → LegDriverStep l s s′ e a
  → TokenExcl l s → TokenExcl l s′
tokenExcl-vis l s s′ cpl vl (ldProd _ _ _ cue cde ue de) tex =
  tokenExcl-api l s s′ cue cde (inj₁ ue) (inj₁ de)
    (vUpSrvKeep vl) (vDnSrvKeep vl) (vUpSrvGain vl) (vDnSrvGain vl) cpl tex
tokenExcl-vis l s s′ cpl vl (ldRelay _ _ _ cue cde de upEvo _ _) tex =
  tokenExcl-api l s s′ cue cde upEvo (inj₁ de)
    (vUpSrvKeep vl) (vDnSrvKeep vl) (vUpSrvGain vl) (vDnSrvGain vl) cpl tex
tokenExcl-vis l s s′ cpl vl (ldCons _ _ _ _ cue cde ue dnEvo _) tex =
  tokenExcl-api l s s′ cue cde (inj₁ ue) dnEvo
    (vUpSrvKeep vl) (vDnSrvKeep vl) (vUpSrvGain vl) (vDnSrvGain vl) cpl tex
tokenExcl-vis l s s′ cpl vl (ldFix _ _ _ cue cde ue de) tex =
  tokenExcl-api l s s′ cue cde (inj₁ ue) (inj₁ de)
    (vUpSrvKeep vl) (vDnSrvKeep vl) (vUpSrvGain vl) (vDnSrvGain vl) cpl tex

------------------------------------------------------------------------
-- §7f  THE WIRED VISIBLE ARM (ASSEMBLY slice A1) — `VisLeaves` DERIVED.
--
-- Task 3 left `VisLeaves` PROVED but not APPLIED: `legStep→legInv` still took the
-- record as an argument, and so did §3's old BRIDGE 4.  This arm closes that: it
-- takes the api STEP, peels `LiveLegApiExpose.driverExpose⁺-at` ONCE, and feeds the
-- record, the `LegDriverStep` and the `LegValStep` to `legStep→legInv` and
-- `tokenExcl-vis` itself.
--
-- WHY IT MUST BE ONE JOINT ARM, AND WHY IT PASSES THE DRIVER STEP OUT.  The
-- successor is EXISTENTIAL in the cone's result, so a second peel — for the other
-- component, or for the frozen `driverExpose` the `PipeInvS` engine uses — lands at
-- a DIFFERENT `s′` and the two preservation maps cannot be paired (nothing in the
-- repo makes `absDec` injective, so `M ≡ absNodesOf s′₁` and `M ≡ absNodesOf s′₂`
-- do not identify the two states).  Hence: one peel, both components out, and the
-- leg's `LegDriverStep` + server evolutions passed OUT so the assembly can finish
-- `PipeInv⁺` (`PipeEvStep.legStep→pres`) and `SrvCoupled`
-- (`PipeSrvInv.srvCoupled-pres`) at THIS successor without peeling again.
--
-- `Coupled l s` is the only premise, and it is not a new one: it is `PipeInv⁺`'s
-- own second half, which the assembly carries beside `LegInv` anyway.  Its second
-- and fourth clauses ARE `legStep→legInv`'s `ucC`/`dcC`, so they are read off `cpl`
-- here instead of being demanded separately.
--
-- *** WHY BOTH PREMISES SIT INSIDE THE RETURNED MAP (assembly slice A2, the
-- instalment-1 reviewer's Important). ***  The consumer is `LiveLegStep.Fold`'s
-- `EvStepG` (`:255`), whose successor must be INVARIANT-INDEPENDENT: it returns
-- `Σ[ r′ ] (M ≡ radec r′) × (Inv l (toSys r) → Inv l (toSys r′))`, i.e. the
-- reachable successor is produced BEFORE anything about the source state is
-- known.  Taking `Coupled`/`TokenExcl` before the `Σ` (as this arm did at
-- `0a7c90f`) would make `s′` — and hence `r′` and the `M ≡ radec r′` equation —
-- depend on the invariant, which `EvStepG` cannot supply at that point.  The peel
-- itself needs neither premise (`driverExpose⁺-at` takes only the step), so both
-- move INTO the map: the successor is named unconditionally and the two
-- preservation halves are handed out under their own hypotheses.
------------------------------------------------------------------------

-- ONE visible api step, at the JOINT invariant: the exclusions and the token
-- location are both preserved, at the ONE successor the ⁺ cone's single peel names
legJointVis : (l : TwoLegs) (s : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → apiES .mem (X , e) a
  → absNodesOf s ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ s′ ∈ SysState ] (med s ≡ med s′) × (M ≡ absNodesOf s′)
      × (nodesOf s ═[ ev (evl (evLabel X e a)) ]═► nodesOf s′)
      × LegDriverStep l s s′ e a
      × (UpSrvEvo l s s′ × DnSrvEvo l s s′)
      × (Coupled l s → TokenExcl l s
           → (LegInv l s → LegInv l s′) × TokenExcl l s′)
legJointVis l s apimem step =
  let (s′ , medEq , Meq , wrun , ld , srv , vl , lv) = driverExpose⁺-at l s apimem step
  in  s′ , medEq , Meq , wrun , ld , srv
    , λ cpl tex →
        legStep→legInv l s s′ (proj₁ (proj₂ cpl)) (proj₂ (proj₂ (proj₂ cpl)))
          (noTwoOf tex) vl ld lv
      , tokenExcl-vis l s s′ cpl vl ld tex

------------------------------------------------------------------------
-- §8  THE CLOSURE, and what is left.
--
-- The four step classes `LiveLegStep`'s own arms dispatch on are now covered:
--
--   | class                        | this module        | premises           |
--   |------------------------------|--------------------|--------------------|
--   | medium-τ drain               | `tokenExcl-drain`  | NONE               |
--   | io-SYNC fill  (`input`)      | `tokenExcl-fill`   | NONE               |
--   | io-SYNC read  (`output`)     | `tokenExcl-read`   | NONE               |
--   | visible api                  | `tokenExcl-vis`    | `Coupled` only     |
--   | (component-fixing classes)   | `tokenExcl-frame`  | NONE               |
--
-- `Coupled` is not a new premise: it is `PipeInv⁺`'s own second half, which the
-- assembly already carries beside `LegInv` (`legStep→legInv` takes two of its four
-- clauses today).  The `RState`-level wrappers are NOT here for the same reason
-- `LiveLegStep` defers its own two state-level arms to the assembly (Task 6): the
-- τ dispatch needs the heavy `WalkConvTauInv` layer, which the cheap-prefix rule
-- keeps out of this module.  Each arm above is stated at exactly the witnesses the
-- corresponding `legInv-*` arm has in hand at that point, so the assembly's
-- dispatch carries `TokenExcl` beside `LegInv` clause for clause.
--
-- WHAT `LiveLegStep` GETS TODAY: `NoTwoTokens` — via `tokenExcl⇒noTwoTokens` and
-- `legStep→legInv⁺` (§3) — with its preservation reduced to (P1)-(P3).  WHAT IT
-- STILL DOES NOT GET: `cellCp3`, whose alignment is PARKED in §1b with its
-- interface type-checked (§3's `cellCp3-of`) for the future window campaign.
------------------------------------------------------------------------

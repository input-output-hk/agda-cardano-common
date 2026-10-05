{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- InFlightOpen completion, Task 1 — THE TWO io CELL POSITIONS, at both legs:
-- `InFlightOpen.oUpCell` and `oDnCell`, i.e. FOUR of the twelve facts.
--
-- WHAT IS PROVED, and at exactly the field type.  `LiveStableOffer.RefutedAt l k
-- blkA r` is `AtPos l k blkA (toSys r) → isStable (radec r ∖ hidden blkA) → ⊥`,
-- and the four theorems below have that conclusion at `k = lpUpCell` / `lpDnCell`
-- and `l = legBD` / `legCD`.  The route is the one the LegPos-24 spike measured
-- (its `noUpCell-BD`, promoted off the two ladders `LiveIoIntro` now BUILDS
-- rather than premises):
--
--   the cell's own `full (blkPayload blkA)` phase — which is `AtPos`'s FIRST
--   conjunct at both cell positions, verbatim — makes the medium offer the
--   delivery (`medOfferOut`); the reader peer at its streaming position makes the
--   nodes side offer the same event (`bfc-offer-out` + `cliOutNodes-*`); the two
--   SYNC into a τ of the doubly-hidden tree (`ioMove-⊥`), which stability refutes.
--
-- *** THE TWO RESIDUAL HYPOTHESES, STATED PLAINLY — do not quote these four
-- theorems without them. ***  Neither is provable inside this module and neither
-- is a defect of the ladders; both are recorded in the Task-1 report with their
-- exact suppliers:
--
--   (H1) `broken (med (toSys r)) (upLink l) ≡ false` — a BROKEN link decodes to
--        `Skip` (`SysMedium.decLink … true`), which offers nothing, so the arm is
--        FALSE without it.  It is NOT new debt and NOT invariant content: the
--        obligated window already carries both of the leg's links unbroken
--        (`LiveStableOffer.Window`'s `wLink1`/`wLink2`, derived from the SPEC
--        position).  It is, however, an INTERFACE gap: `InFlightOpen`'s fields
--        were stated window-FREE, and `parked-at` — which does hold the window —
--        passed only `wSent`/`wPend` on.  *** THAT GAP IS CLOSED (Task 4): ***
--        `InFlightOpen`'s four io fields now CARRY the antecedent
--        (`broken (med (toSys r)) (upLink l) ≡ false →` and its `dnLink` twin,
--        `LiveStableOffer:1554-1566`) and `parked-of`/`parked-at` thread
--        `wLink1`/`wLink2` into them (`:1581-1636`); this module's theorems are
--        consumed at exactly that shape by `LivenessProof.ifo-of` (`:281-306`).
--        "Every link is unbroken" was never an available substitute: `break` is a
--        visible event of the implementation and
--        `LiveLegAssembly.evStepB-break` transports the invariant across it.
--   (H2) `CellRdy l (toSys r)` — the reader-alignment content, §1.  This is the
--        cell-capacity/FIFO clause the campaign has chartered twice
--        (`LiveLegInv`'s §6 HONEST LIMITATION, `:564-573`, names exactly this
--        conjunct and says it is not derivable from `AtPos`).  It is stated here
--        in the shape the four arms consume, PARKED in the `cellCp3` style — this
--        module proves the arms FROM it and depends on no proof OF it, exactly as
--        `LiveTokenExcl` §1b parks `UpChainCp3`/`DnChainCp3`.  The report prices
--        its preservation and records the two naive shapes that are FALSE.
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`, no `with` in anything
-- whose type mentions the imported `AtPos`/`RefutedAt` (the `blkA`-parameter
-- hazard).
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Bool using ( false )
open import Data.Empty using ( ⊥ )
open import Data.Product using ( Σ; _×_; _,_; proj₁; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Process_Trees using ( ExtI; isStable )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCellOpen
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; output )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )
open import CSP.Examples.Cardano_network.Base using ( hi; N2N_BlockFetch )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.Stability {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( stable-no-τ )
import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload}) as TLH

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( broken; decMed )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( IoOffers; absNodesOf; lift-io-sync-whole-τ; coarsenBFc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( cellUp; cellDn; upClient; dnClient )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( hidden )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA
  using ( AtPos; lpUpCell; lpDnCell; CellFull⁺ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveStableOffer blkA
  using ( RefutedAt; Window; wLink1; wLink2 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveIoIntro blkA
  using ( iomem-out; medOfferOut; bfc-offer-out
        ; cliOutNodes-B; cliOutNodes-C; cliOutNodes-D-BD; cliOutNodes-D-CD )

------------------------------------------------------------------------
-- §1  THE READER-ALIGNMENT CONTENT (H2), stated in the shape the arms consume.
--
-- `bfCnxt` accepts a `MsgBlock` DELIVERY at exactly one abstract client
-- position, `bcStream` (`NodeSpecs.agda:544-547`; the LegPos-24 spike's mutation
-- M-B is the machine-checked record that this pin is LOAD-BEARING, not vacuous:
-- moving it to `bcBusy` turns `ceqBFc05`'s `subst` red).  So the content the two
-- cell arms need is exactly "a cell holding the token has its reader there", and
-- it is CONDITIONAL on the cell — never a bare position claim.
------------------------------------------------------------------------

-- the reader peer is at the streaming position (the ONLY one whose table edge
-- accepts a `MsgBlock` delivery).  Stated through `coarsenBFc` because
-- `SysStep.absBFc l d q` depends on `q` only through it — exactly the strength an
-- offer construction needs, and no more.
CliStream : SN.BFcPos → Set
CliStream q = coarsenBFc q ≡ NS.bcStream

-- (H2) THE PARKED CONJUNCT: on one leg, EACH of the two cells, if it holds the
-- token unread, has its own reader aligned.  Nothing in this module proves it and
-- nothing depends on a proof of it — it is the `cellCp3`-shaped interface a future
-- invariant slice must fill (see the header, and the Task-1 report for the
-- preservation route and for the two naive shapes that are FALSE).  *** `cellCp3`
-- ITSELF IS NO LONGER PARKED: the cellCp3 window proved it off the carried join
-- (`LiveChanJoin.cellCp3-of`).  The reference here is to the SHAPE, and the window's
-- route — cell ⇒ reader region off `ChanLeg`, plus a pre-request client region — is
-- the one a filler of THIS conjunct should copy. ***
CellRdy : TwoLegs → SysState → Set
CellRdy l s = (CellFull⁺ blkA (cellUp l s) → CliStream (upClient l s))
            × (CellFull⁺ blkA (cellDn l s) → CliStream (dnClient l s))

------------------------------------------------------------------------
-- §2  THE io REFUTATION KIT.
--
-- `LiveStableOffer` has only the api one (`hiddenMove-⊥`, whose event must be in
-- `hidden blkA`).  An io event is hidden by the FIRST hide instead, as a
-- medium⊗nodes SYNC (`lift-io-sync-whole-τ`, which demands BOTH operand steps),
-- and the resulting τ of `radec r` rides the SECOND hide UNCONDITIONALLY
-- (`TraceLawsHide.Hide-τ`, tag0) — which is why the io family needs two intro
-- ladders and no hide-membership side condition.
------------------------------------------------------------------------

-- a medium⊗nodes io SYNC is a τ of the doubly-hidden tree, which a stable
-- configuration cannot perform.  (The LegPos-24 spike's `ioMove-⊥`, promoted.)
ioMove-⊥ : (r : RState) {X : Set 0ℓ} {ee : Net_Api Payload X} {a : X}
         → ioES .mem (X , ee) a
         → IoOffers (decMed (med (toSys r))) ee a
         → IoOffers (absNodesOf (toSys r)) ee a
         → isStable (radec r ∖ hidden blkA) → ⊥
ioMove-⊥ r iomem (_ , sM) (_ , sN) sta =
  stable-no-τ sta
    (TLH.Hide-τ (hidden blkA) (radec r)
      (lift-io-sync-whole-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) iomem sM sN))

------------------------------------------------------------------------
-- §3  *** THE FOUR FACTS. ***
--
-- Each is a THREE-line composition, and that is the point the spike measured:
-- with the ladders built and the alignment content given, an io in-flight CELL
-- closes with no further machinery.  WHICH CONJUNCT OF `AtPos` PAYS: the FIRST
-- one only (`CellFull⁺ blkA`, the cell's own phase) — `ProdSent`, `RelayPre` /
-- `RelayFwd` and `InCp03` are not read, so the arms hold at any driver phases.
--
-- The leg dispatch is on an EXPLICIT `TwoLegs` argument (never a `with`, the
-- campaign's `blkA`-module rule), so each clause's `AtPos` premise reduces to
-- that leg's own slot equation and the ladder instance is the leg's own.
------------------------------------------------------------------------

-- *** ARM `lpUpCell`, BOTH LEGS. ***  A stable configuration cannot have the
-- token sitting UNREAD in the leg's UP cell: the cell offers its `output` and the
-- relay's own BF client (node B on leg BD, node C on leg CD) takes it.
cellOpen-up : (l : TwoLegs) (r : RState)
            → broken (med (toSys r)) (upLink l) ≡ false
            → CellRdy l (toSys r)
            → RefutedAt l lpUpCell blkA r
cellOpen-up legBD r hbrk rdy at sta =
  ioMove-⊥ r (iomem-out linkAB hi N2N_BlockFetch (blkPayload blkA))
    (medOfferOut (med (toSys r)) linkAB (blkPayload blkA) hbrk (proj₁ at))
    (cliOutNodes-B (toSys r) (blkPayload blkA)
      (bfc-offer-out linkAB hi (SN.NodeStateB.bfC-AB (nB (toSys r))) blkA
        (proj₁ rdy (proj₁ at))))
    sta
cellOpen-up legCD r hbrk rdy at sta =
  ioMove-⊥ r (iomem-out linkAC hi N2N_BlockFetch (blkPayload blkA))
    (medOfferOut (med (toSys r)) linkAC (blkPayload blkA) hbrk (proj₁ at))
    (cliOutNodes-C (toSys r) (blkPayload blkA)
      (bfc-offer-out linkAC hi (SN.NodeStateC.bfC-AC (nC (toSys r))) blkA
        (proj₁ rdy (proj₁ at))))
    sta

-- *** ARM `lpDnCell`, BOTH LEGS. ***  … and not in the leg's DOWN cell either:
-- there the reader is node D's BF client on that leg's down link.
cellOpen-dn : (l : TwoLegs) (r : RState)
            → broken (med (toSys r)) (dnLink l) ≡ false
            → CellRdy l (toSys r)
            → RefutedAt l lpDnCell blkA r
cellOpen-dn legBD r hbrk rdy at sta =
  ioMove-⊥ r (iomem-out linkBD hi N2N_BlockFetch (blkPayload blkA))
    (medOfferOut (med (toSys r)) linkBD (blkPayload blkA) hbrk (proj₁ at))
    (cliOutNodes-D-BD (toSys r) (blkPayload blkA)
      (bfc-offer-out linkBD hi (SN.NodeStateD.bfC-BD (nD (toSys r))) blkA
        (proj₂ rdy (proj₁ at))))
    sta
cellOpen-dn legCD r hbrk rdy at sta =
  ioMove-⊥ r (iomem-out linkCD hi N2N_BlockFetch (blkPayload blkA))
    (medOfferOut (med (toSys r)) linkCD (blkPayload blkA) hbrk (proj₁ at))
    (cliOutNodes-D-CD (toSys r) (blkPayload blkA)
      (bfc-offer-out linkCD hi (SN.NodeStateD.bfC-CD (nD (toSys r))) blkA
        (proj₂ rdy (proj₁ at))))
    sta

------------------------------------------------------------------------
-- §4  (H1) DISCHARGED FROM THE WINDOW — the interface fact, machine-checked.
--
-- The claim in the header ("(H1) is not new debt, the obligated window already
-- carries it") is stated here as a TYPE rather than as prose: given the leg's own
-- window AT THE LEG'S OWN TWO LINKS — which is exactly what `window-BD` /
-- `window-CD` produce (`Window legBD (toSys r) linkAB linkBD` and
-- `Window legCD (toSys r) linkAC linkCD`, and `upLink`/`dnLink` are those very
-- links) — the two cell arms are `RefutedAt` with NO link hypothesis left, so the
-- residual is `CellRdy` ALONE.
--
-- WHAT THIS MEASURED, AND THE INTERFACE EDIT THAT LANDED.  When this section was
-- written the window was available at `LiveStableOffer.parked-of` but was NOT
-- passed into `InFlightOpen`'s fields (`parked-at` forwarded only `wSent`/`wPend`),
-- so the two fields as banked were window-FREE and therefore STRONGER than these
-- two theorems.  *** TASK 4 MADE THE EDIT, in the window-FREE direction: *** the
-- four io fields took the LINK antecedent itself (`LiveStableOffer:1554-1566`) —
-- character-for-character the hypothesis of §3's raw pair — and `parked-of`
-- (`:1630`) now takes the window at the leg's own two links and threads
-- `wLink1`/`wLink2` through `parked-at` (`:1581`) into the four io arms.  So the
-- RAW forms `cellOpen-up`/`-dn` are what the tree consumes (through
-- `LiveChanInv.cellOpen-up-chan`/`-dn-chan` at `LivenessProof.ifo-of`), and the
-- two window forms below are kept as the natural interface for a
-- window-HOLDING caller rather than as the consumed route (see the note at the
-- end of this section).  No amount of io machinery could have removed a
-- `broken … ≡ true` counter-state: a broken link's medium IS `Skip` and `break`
-- is a visible event the invariant is transported across.
------------------------------------------------------------------------

-- the UP cell arm, with (H1) taken off the leg's window
cellOpen-up-w : (l : TwoLegs) (r : RState)
              → Window l (toSys r) (upLink l) (dnLink l)
              → CellRdy l (toSys r)
              → RefutedAt l lpUpCell blkA r
cellOpen-up-w l r w rdy = cellOpen-up l r (wLink1 w) rdy

-- … and the DOWN cell arm, off the window's SECOND link field
cellOpen-dn-w : (l : TwoLegs) (r : RState)
              → Window l (toSys r) (upLink l) (dnLink l)
              → CellRdy l (toSys r)
              → RefutedAt l lpDnCell blkA r
cellOpen-dn-w l r w rdy = cellOpen-dn l r (wLink2 w) rdy

------------------------------------------------------------------------
-- *** DELIBERATE-KEEP NOTE (Task 4; inventory extended at the whole-branch final
-- review, M-4), FOR ALL TWELVE ORPHANED COROLLARIES. ***
--
-- After Task 4's interface edit the tree's consumer (`LivenessProof.ifo-of`)
-- takes the RAW, link-antecedent forms, so TWELVE definitions in this family now
-- have NO consumer anywhere in `src/`.  They are kept on purpose — a
-- window-HOLDING caller is the natural second client of these arms, and each is
-- one line — so a cleanup pass must not read them as dead code:
--
--   · `cellOpen-up-w` / `cellOpen-dn-w`            (this module, above);
--   · `LiveSrvOpen.srvOpen-up-w` / `srvOpen-dn-w`  (its §4 — §3 since the
--     cross-node campaign's T2 is the `pp5` sharpening);
--   · `LiveChanInv.cellOpen-w-chan`                (its §7c);
--   · `LiveChanInv.chanLeg⇒cellRdy`                (its §7 — kept for a
--     different reason: it is the TYPE-LEVEL record that Task 1's parked
--     `CellRdy` parameter is discharged, which is the only place that fact is
--     visible in a type);
--   · (T8c-iii) the `LiveRelayCS.relayOpen-in-ws′` / `-out-ws′` pair NO LONGER
--     EXISTS — the `cp6`/`pp0` discharge landed a third unconditional premise on
--     `coAt-split-at`, which fired that pair's own deletion trigger.  Its design
--     record is the paragraph that replaced it, at `LiveRelayCS` §4.  (What this entry
--     used to say: they were the window-scoped twins of the `-s′` pair, still uncalled
--     and wider since T2, flagged for the post-T3 re-gate as "≈20 lines that break
--     nothing".  The re-gate never ran; the deletion trigger fired instead.);
--   · `LiveRelayOpen.relayOpen-in-s` / `-out-s` / `-in-ws` / `-out-ws`
--     (its §6d — superseded by `LiveRelayCS`'s protocol-SPLIT `-s′` forms, kept
--     because they are the unsplit statements of record).
--
-- All TEN (twelve before T8c-iii deleted the `-ws′` pair) occur exactly twice in
-- `src/` (signature + definition).  A cleanup
-- pass that wants them gone should drop the FOUR window-scoped forms (six before
-- T8c-iii deleted the `-ws′` pair), not the raw
-- ones the consumer uses.
------------------------------------------------------------------------

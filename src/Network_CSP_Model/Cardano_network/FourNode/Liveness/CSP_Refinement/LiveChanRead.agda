{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- InFlightOpen completion, Task 2 — THE PAYLOAD-GENERIC READER LAYER.
--
-- WHY THIS MODULE EXISTS, and why it is stated PAYLOAD-GENERICALLY.  Task 1's
-- cell arms consume a reader fact PINNED at one payload class and one reader
-- position: `LiveCellOpen.CellRdy` says "a cell holding `blkPayload blkA` has
-- its reader at `bcStream`".  The Task-1 review's finding I-2 is that the SAME
-- clause family must serve the H19 row of the two SERVER positions, whose
-- middle arm is the same statement at a DIFFERENT payload and a DIFFERENT
-- reader position (`MsgStartBatch` at `bcBusy`, `spike-verify-report.md:238`
-- off `NodeSpecs.agda:536-539`) — so the clause must be stated ONCE, generically
-- in the payload, with both pins DERIVED.  That is what §1-§2 do:
--
--   `CliAccepts i d q x`  =  "the BF client at position `q` has a table row for
--                            the cell's delivery of the wire payload `x`"
--
-- is a bare `Σ` over `NodeSpecs.bfCnxt`, with NO payload and NO position pin.
-- The pin the live route consumes is a THEOREM about it (§2):
-- `acceptsBlk⇒stream`, "accepting a `MsgBlock` delivery IS being at `bcStream`".
-- Nothing here is invariant content — every definition is a theorem about the
-- decode tables and the two io intro ladders `LiveIoIntro` built.
--
-- *** WHAT WAS DELETED IN TASK 2b, AND WHY (do not re-add). ***  The first
-- landing of this module also carried the three CONVERSE/second pins
-- (`streamAcceptsBlk`, `acceptsSb⇒busy`, `busyAcceptsSb`) and a §4 that reached
-- the two cell arms through a `CellOpenPre` premise.  Both are SUPERSEDED and
-- were never applied: the converses are needed only in the LENIENT
-- `∀ {t md ln}` form (`LiveChanInv.busyAcceptsSbM`/`streamAcceptsBlkM`), which
-- these pinned-at-`time₀/FromResponder/length₀` versions cannot supply; and
-- `LiveChanInv` §7 reaches `RefutedAt … lpUpCell` through `ChanUp`/`ChanDn`
-- instead, so keeping §4 left THREE parallel routes to one conclusion and
-- three interfaces for the wiring to satisfy.  ONE route now: §3's payload-
-- generic refutation, consumed by `LiveChanInv` §7.
--
-- CONTENTS
--   §1  the payload-generic acceptance predicate and the reader OFFER it
--       produces (`cliOffer`, which generalises `LiveIoIntro.bfc-offer-out`:
--       that lemma's `bcStream`/`blkPayload b` pins are §2's instance and
--       `LiveChanInv.streamAcceptsBlkM`'s)
--   §2  the pin, by exhaustive dispatch on the ABSTRACT client position
--       (`NodeSpecs.BFcPos` — seven constructors, no catch-all)
--   §3  the payload-generic CELL refutation: a stable configuration cannot hold
--       a payload its own reader accepts, in either of a leg's two cells.  The
--       four Task-1 cell facts are its `blkPayload blkA` instance (taken in
--       `LiveChanInv` §7) and the H19 middle arm is its `MsgStartBatch` one.
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`, no `funext`.
------------------------------------------------------------------------

open import Data.Bool using ( false )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Maybe using ( just )
open import Data.Product using ( Σ-syntax; _,_; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl )

open import Process_Trees using ( isStable )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanRead
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟; Link; output )
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; blockFetch; MsgStartBatch )
open import CSP.Examples.Cardano_network.Base
  using ( Dir; hi; N2N_BlockFetch; FromResponder )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( time₀; length₀ )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∖_ )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( med; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( broken; full )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( IoOffers; absBFc; coarsenBFc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( tableSpec-ev-fwd; nothing-absurd )
-- (T2 review M-1) the BF client's abstract offer table, IMPORTED rather than
-- re-spelled: `SysIoLink5:2324-2325` is the copy `PipeCliIoDec`/`PipeBundleRecv`
-- already use, and `absBFc i d q` is `tableSpec (Tbfc i d) (coarsenBFc q)` by
-- definition (`SysStep:555-556`), so one KEEP-IN-SYNC surface disappears
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA
  using ( Tbfc )
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
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveIoIntro blkA
  using ( iomem-out; medOfferOut
        ; cliOutNodes-B; cliOutNodes-C; cliOutNodes-D-BD; cliOutNodes-D-CD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCellOpen blkA
  using ( ioMove-⊥ )

------------------------------------------------------------------------
-- §1  THE PAYLOAD-GENERIC ACCEPTANCE PREDICATE, AND THE OFFER IT PRODUCES.
--
-- `absBFc i d q` is `tableSpec (Tbfc i d) (coarsenBFc q)` by definition
-- (`SysStep.agda:555-556`), so the client's whole offer behaviour is the one
-- table row `bfCnxt i d (coarsenBFc q)` — which is why "the reader accepts `x`"
-- needs no more than the existence of that row, and why the offer construction
-- below is four lines rather than a per-payload ladder.
------------------------------------------------------------------------

-- *** THE CLAUSE, PAYLOAD-GENERIC. ***  the wire payload `x` is in the accepted
-- set of the BF client sitting at the ABSTRACT position `qa`: its table has a
-- row for the cell's `output` delivery of `x`.  No payload pin, no position pin
-- — both are §2's theorems.
CliAcceptsA : Link → Dir → NS.BFcPos → Payload → Set
CliAcceptsA i d qa x =
  Σ[ qa′ ∈ NS.BFcPos ]
    (NS.bfCnxt i d qa (Payload , output i d N2N_BlockFetch) x ≡ just qa′)

-- … the same at a FINE client position (the component the state actually
-- carries); `absBFc` depends on the fine position only through `coarsenBFc`
CliAccepts : Link → Dir → SN.BFcPos → Payload → Set
CliAccepts i d q x = CliAcceptsA i d (coarsenBFc q) x

-- an accepting position is NOT terminal: `bfCfin` is `true` only at `bcTerm`,
-- and `bcTerm` has no table row at all.  (Exhaustive on `NS.BFcPos`'s seven
-- constructors — no catch-all.)
cliFin : (i : Link) (d : Dir) (qa : NS.BFcPos) (x : Payload)
       → CliAcceptsA i d qa x → NS.bfCfin qa ≡ false
cliFin i d NS.bcIdle      x _        = refl
cliFin i d (NS.bcWrr r)   x _        = refl
cliFin i d NS.bcBusy      x _        = refl
cliFin i d NS.bcWcd       x _        = refl
cliFin i d NS.bcStream    x _        = refl
cliFin i d (NS.bcAblk b)  x _        = refl
cliFin i d NS.bcTerm      x (_ , eq) = ⊥-elim (nothing-absurd eq)

-- *** THE READER OFFER, PAYLOAD-GENERIC. ***  a BF client whose table accepts
-- `x` OFFERS the cell's delivery of `x`.  This generalises
-- `LiveIoIntro.bfc-offer-out`, whose `coarsenBFc q ≡ bcStream` premise and
-- `blkPayload b` payload are recovered as §2's `streamAcceptsBlk` instance.
cliOffer : (i : Link) (d : Dir) (q : SN.BFcPos) (x : Payload)
         → CliAccepts i d q x
         → IoOffers (absBFc i d q) (output i d N2N_BlockFetch) x
cliOffer i d q x acc =
    _
  , tableSpec-ev-fwd (Tbfc i d) (coarsenBFc q)
      (cliFin i d (coarsenBFc q) x acc) (proj₂ acc)

------------------------------------------------------------------------
-- §2  THE PIN, DERIVED.
--
-- This is the review's I-2 instance: the payload class DECIDES the reader
-- position, because `bfCnxt`'s delivery rows are `bcBusy ↦ MsgStartBatch /
-- MsgNoBlocks` and `bcStream ↦ MsgBlock b / MsgBatchDone` and nothing else
-- (`NodeSpecs.agda:536-551`).  The `⇒` direction is an exhaustive dispatch on
-- the abstract position; the CONVERSE directions are `LiveChanInv`'s lenient
-- `busyAcceptsSbM`/`streamAcceptsBlkM`, one banked table row each.
------------------------------------------------------------------------

-- the `MsgStartBatch` wire payload of a responder-side BF sender (the
-- `blkPayload` sibling: `PipeValFill.agda:111-112` is the block one)
sbPayload : Payload
sbPayload = time₀ , FromResponder , length₀ , blockFetch MsgStartBatch

-- a client that accepts a `MsgBlock` delivery IS at the streaming position
acceptsBlk⇒stream : (i : Link) (d : Dir) (qa : NS.BFcPos) (b : Block₃)
                  → CliAcceptsA i d qa (blkPayload b) → qa ≡ NS.bcStream
acceptsBlk⇒stream i d NS.bcIdle     b (_ , eq) = ⊥-elim (nothing-absurd eq)
acceptsBlk⇒stream i d (NS.bcWrr r)  b (_ , eq) = ⊥-elim (nothing-absurd eq)
acceptsBlk⇒stream i d NS.bcBusy     b (_ , eq) = ⊥-elim (nothing-absurd eq)
acceptsBlk⇒stream i d NS.bcWcd      b (_ , eq) = ⊥-elim (nothing-absurd eq)
acceptsBlk⇒stream i d NS.bcStream   b _        = refl
acceptsBlk⇒stream i d (NS.bcAblk c) b (_ , eq) = ⊥-elim (nothing-absurd eq)
acceptsBlk⇒stream i d NS.bcTerm     b (_ , eq) = ⊥-elim (nothing-absurd eq)

------------------------------------------------------------------------
-- §3  *** THE PAYLOAD-GENERIC CELL REFUTATION. ***
--
-- The engine of Task 1's four cell arms, with the payload freed: a stable
-- configuration cannot leave a payload in one of the leg's two BlockFetch cells
-- when the cell's own reader accepts it, because the medium offers the delivery
-- (`medOfferOut`, itself payload-generic), the reader's node offers the same
-- event (§1's `cliOffer` past the four banked whole-nodes rungs) and the two
-- SYNC into a τ of the doubly-hidden tree (`ioMove-⊥`).
--
-- BOTH CONSUMERS: at `x = blkPayload blkA` this is `oUpCell`/`oDnCell` (§4); at
-- `x = sbPayload` it is the H19 middle arm at `lpUpSrv`/`lpDnSrv`.  The reader
-- of BOTH cells of BOTH legs sits at direction `hi` — the relay's BF client
-- (`absNodeB linkAB hi …`, `absNodeC linkAC hi …`) and node D's
-- (`absNodeD linkBD hi …`, `linkCD hi …`, `SysStep.agda:767-783`) — which is
-- the same `(link , hi , N2N_BlockFetch)` key the cell accessors read
-- (`PipeInv.agda:424-426`, `:430-432`).
------------------------------------------------------------------------

-- the leg's UP cell: a payload its reader accepts refutes stability
cellFull-up-⊥ : (l : TwoLegs) (r : RState) (x : Payload)
              → broken (med (toSys r)) (upLink l) ≡ false
              → cellUp l (toSys r) ≡ full x
              → CliAccepts (upLink l) hi (upClient l (toSys r)) x
              → isStable (radec r ∖ hidden blkA) → ⊥
cellFull-up-⊥ legBD r x hbrk hfull acc sta =
  ioMove-⊥ r (iomem-out linkAB hi N2N_BlockFetch x)
    (medOfferOut (med (toSys r)) linkAB x hbrk hfull)
    (cliOutNodes-B (toSys r) x
      (cliOffer linkAB hi (SN.NodeStateB.bfC-AB (nB (toSys r))) x acc))
    sta
cellFull-up-⊥ legCD r x hbrk hfull acc sta =
  ioMove-⊥ r (iomem-out linkAC hi N2N_BlockFetch x)
    (medOfferOut (med (toSys r)) linkAC x hbrk hfull)
    (cliOutNodes-C (toSys r) x
      (cliOffer linkAC hi (SN.NodeStateC.bfC-AC (nC (toSys r))) x acc))
    sta

-- … and the leg's DOWN cell, whose reader is node D's client on that link
cellFull-dn-⊥ : (l : TwoLegs) (r : RState) (x : Payload)
              → broken (med (toSys r)) (dnLink l) ≡ false
              → cellDn l (toSys r) ≡ full x
              → CliAccepts (dnLink l) hi (dnClient l (toSys r)) x
              → isStable (radec r ∖ hidden blkA) → ⊥
cellFull-dn-⊥ legBD r x hbrk hfull acc sta =
  ioMove-⊥ r (iomem-out linkBD hi N2N_BlockFetch x)
    (medOfferOut (med (toSys r)) linkBD x hbrk hfull)
    (cliOutNodes-D-BD (toSys r) x
      (cliOffer linkBD hi (SN.NodeStateD.bfC-BD (nD (toSys r))) x acc))
    sta
cellFull-dn-⊥ legCD r x hbrk hfull acc sta =
  ioMove-⊥ r (iomem-out linkCD hi N2N_BlockFetch x)
    (medOfferOut (med (toSys r)) linkCD x hbrk hfull)
    (cliOutNodes-D-CD (toSys r) x
      (cliOffer linkCD hi (SN.NodeStateD.bfC-CD (nD (toSys r))) x acc))
    sta


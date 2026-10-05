{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- InFlightOpen completion, Task 2c — THE TWO io SERVER POSITIONS, at both legs:
-- `InFlightOpen.oUpSrv` and `oDnSrv`, i.e. FOUR more of the twelve facts (with
-- Task 1's/Task 2's four cell facts, EIGHT of twelve).
--
-- WHAT IS PROVED, and at exactly the field type.  `LiveStableOffer.RefutedAt l k
-- blkA r` is `AtPos l k blkA (toSys r) → isStable (radec r ∖ hidden blkA) → ⊥`,
-- and the four theorems below have that conclusion at `k = lpUpSrv` / `lpDnSrv`
-- and `l = legBD` / `legCD`.
--
-- WHY THIS IS HARDER THAN THE CELL FACTS, IN ONE SENTENCE.  At a CELL position
-- the enabled move is fixed by the position itself (the cell holds a payload, so
-- the medium offers its delivery); at a SERVER position `AtPos` says only that the
-- server HOLDS the token (`SrvHas⁺ blkA`, i.e. `bsBlk1 blkA`), and WHICH move is
-- enabled depends on the state of the cell the server is about to write —
-- which is exactly the three-armed disjunction `LiveChanInv.H19` supplies:
--
--   H19 arm            enabled move                     ladder / kit used
--   ----------------   ------------------------------   ----------------------
--   `ph ≡ empty`       the SERVER's own wire-send       `medOfferIn` (L3) ⊗
--                      `input i hi BF ! blkPayload b`   `srvInNodes-*` (L5)
--                                                       via `ioMove-⊥`
--   `ph ≡ full x` and  the READER's delivery            `LiveChanRead`'s
--   the reader accepts `output i hi BF ! x`              `cellFull-{up,dn}-⊥`
--                                                       (Task 2's, REUSED as is)
--   `ph ≡ full x` and  none — the state is REFUTED       `NoTwoTokens`'
--   the reader HOLDS                                     `n{Up,Dn}SrvCli`
--   `ph ≡ draining x`  the MEDIUM's own drain τ          `medDrainτ` (L4) via
--                                                        §1's `medτMove-⊥`
--
-- so three of the four arms are a ladder application and the fourth is the
-- carried exclusion theorem.  The `CliHoldA` escape is the one the Task-2 report's
-- §3 counter-state forced into H19's middle arm; here it is cut by `NoTwoTokens`'
-- SERVER fields (`nUpSrvCli`/`nDnSrvCli`), not its cell ones — a holding reader
-- and a holding server would be two tokens on one leg.
--
-- *** THE RESIDUAL HYPOTHESES, STATED PLAINLY — do not quote these four theorems
-- without them. ***  They are EXACTLY the two the four cell facts carry
-- (`LiveChanInv.cellOpen-{up,dn}-chan`), and for the same reasons:
--
--   (H1) `broken (med (toSys r)) (upLink l) ≡ false` — a BROKEN link decodes to
--        `Skip`, which neither accepts an `input` nor performs the drain τ, so
--        ALL THREE arms are false without it (the ev arms because `decLink … true`
--        offers nothing, the τ arm because it has no τ).  Task 1's (H1) unchanged;
--        `LiveStableOffer.Window`'s `wLink1`/`wLink2` carry it and §3 below takes
--        it off the window exactly as `LiveCellOpen.cellOpen-{up,dn}-w` does.
--        Task 4's interface item is unchanged by this module.
--   (H2) `ChanUp l (toSys r)` / `ChanDn l (toSys r)` — the per-hop channel
--        invariant (`LiveChanInv` §3, with base, frame and a per-step-class
--        preservation calculus).  This REPLACES the cell facts' `CellRdy`: the
--        server arms need the whole three-armed H19, not just the reader pin, so
--        they consume the invariant directly rather than through `CellRdy`.
--   plus the carried `NoTwoTokens l (toSys r)` (proved in `LiveTokenExcl`),
--        in exactly the position the cell facts use it.
--
-- No postulate, no hole, no `mutual`, no `NON_TERMINATING`, no `funext`, and no
-- `with` in anything whose type mentions an imported `blkA`-parameterised
-- predicate — every dispatch (the leg, and H19's three arms) is on an EXPLICIT
-- argument, the campaign's `blkA`-module rule.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Bool using ( false )
open import Data.Empty using ( ⊥ )
open import Data.Maybe using ( just )
open import Data.Product using ( Σ; Σ-syntax; _,_; proj₁ )
open import Data.Sum using ( inj₁; inj₂ )
open import Data.Unit.Polymorphic using ( tt )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; cong; subst )

open import Process_Trees using ( ExtI; isStable )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveSrvOpen
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p
  -- (T8c-ii) §6's `ReqOnly` arm fires the READER's polarity
  using ( Net_Api; Net_Api-≟; Link; input; output )
open import CSP.Examples.Cardano_network.Data p
  -- (T8c-ii) §6's `ReqOnly` arm names the message its payload carries
  -- (T11) … and §7's three BlockFetch arms name the RANGE REQUEST's
  using ( Payload; chainSync; MsgCSRequestNext
        ; blockFetch; ChainRange; MsgRequestRange
        -- (T11) §8's three client-READ arms name the two responder messages the
        -- `pp3` leaf's full-cell cases can carry
        ; MsgCSAwaitReply; MsgCSRollForward; Header; Tip )
open import CSP.Examples.Cardano_network.Base using ( Dir; hi; N2N_BlockFetch
  -- (T6c) §5's channel
  ; N2N_ChainSync
  -- (T8c-ii) the payload tuple's lenient middle component
  ; Mode
  -- (T11) … and the initiator-side mode the client's own write is pinned at, and
  -- the responder-side one §8(4)'s write arm names
  ; FromInitiator; FromResponder )
open import CSP.Examples.Cardano_network.Params using ( Params )
-- (T8c-ii) … and its two lenient outer ones
-- (T11) … and the two the client's PINNED request payload names
open Params p using ( Time; Length; time₀; length₀ )
import CSP.Examples.Cardano_network.BlockFetch p as BF
-- (T11) §8's target positions are CS-client fine heads
import CSP.Examples.Cardano_network.ChainSync p as CS

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∖_ )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; τ )
open import Semantics.Stability {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( stable-no-τ )
import CSP.Laws.Traces.TraceLawsHide (Net_Api-≟ {Payload}) as TLH

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( med )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  -- (T8c-ii) `full`/`draining` are §6's two non-empty cell arms
  using ( broken; decMed; phase; empty; full; draining )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; IoOffers; absNodesOf; absBFs; coarsenBFs; coarsenBFc; coarsenCSs
        ; lift-med-whole-τ
        -- (T8c-ii) §6's client arm is stated at node D's own CS-client slot
        ; coarsenCSc
        -- (T11) §8's arms build node D's CS client's own read step
        ; absCSc )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
-- (T2) the PRE-region wire-send row, §3's rung 1 (`bfSnxt bsWsb (input …)
-- MsgStartBatch ≡ just bsStream`)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_PeerEvCSBF blkA
  -- (T11) … and §8's three client-READ rows, all LENIENT in the payload's first
  -- three components
  using ( aBFs; ceqBFs09; aCSc; ceqCSc04; ceqCSc06; ceqCSc07 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; radec; toSys )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( cellUp; cellDn; upClient; dnClient )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.Spec
  using ( hidden )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA
  using ( lpUpSrv; lpDnSrv; SrvHas⁺; srvHas⁺⇒hasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegStep blkA
  using ( NoTwoTokens; nUpSrvCli; nDnSrvCli )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveStableOffer blkA
  using ( RefutedAt; Window; wLink1; wLink2 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveCellOpen blkA
  using ( ioMove-⊥ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveIoIntro blkA
  using ( iomem-in; medOfferIn; medDrainτ; bfs-in-step
        ; srvInNodes-A-AB; srvInNodes-A-AC; srvInNodes-B-BD; srvInNodes-C-CD
        -- (T8c-ii) the READER polarity's io membership witness (`LiveIoIntroCS`
        -- CALLS this one too but does not re-export it — `using` is not `public`)
        ; iomem-out
        -- (T11) §7's three arms: the reader-polarity WHOLE-MEDIUM intro, and §10's
        -- two new BlockFetch ladders with their rung-1s
        ; medOfferOut; bfs-out-step; bfc-in-step
        ; srvOutNodes-B-BD; srvOutNodes-C-CD
        ; cliInNodes-D-BD; cliInNodes-D-CD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanRead blkA
  using ( cellFull-up-⊥; cellFull-dn-⊥; sbPayload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanInv blkA
  using ( SrvStr; H19; chanInv⇒h19; ChanUp; ChanDn; holdA⇒hasBlk
        -- (T2) §3's own two: the PRE region and the cell predicate its strengthened
        -- `cvQui` clause delivers
        ; SrvPre; CellPreQ; cvQui )
-- (T6c) the CHAINSYNC channel invariant's down hop and its `csWar` consumer, and the
-- CS io kits `LiveIoIntroCS` landed for exactly this refutation
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveChanCS blkA
  using ( ChanCSDn; chanCSDn-war; dnCSsOf; cellCSDn; arPayload
        -- (T8c-ii) §6's client arm: node D's own CS-client accessor and its request
        -- payload
        ; dnCScOf; rnPayload )
  renaming ( CellPreQ to CellPreQCS )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveIoIntroCS blkA
  using ( medOfferInCS; medDrainτCS-dn; srvInNodes-dnCS
        -- (T8c-ii) the three kits §2b/§1c landed for §6's three arms
        ; medOfferOutCS; cliInNodes-dnCS; srvOutNodes-dnCS
        -- (T11) … and §2c's NEW fourth direction: node D's client READING, plus
        -- §3's new `csWrf` POSITION instance of the server's own write
        ; cliOutNodes-dnCS; srvInNodesRfw-dnCS )

------------------------------------------------------------------------
-- §1  THE TWO REFUTATION KITS THE SERVER ARMS NEED.
--
-- `LiveCellOpen` §2 has the io-SYNC one (`ioMove-⊥`: a medium⊗nodes visible io
-- sync is a τ of the doubly-hidden tree).  The `draining` arm needs the OTHER
-- flavour: a τ of the MEDIUM ALONE, which rides the first hide with no nodes
-- operand at all (`lift-med-whole-τ`, the sibling of `lift-io-sync-whole-τ`) and
-- then the second hide unconditionally (`TraceLawsHide.Hide-τ`, tag0).  That is
-- why the `draining` arm needs no nodes-side ladder.
------------------------------------------------------------------------

-- a MEDIUM-only τ is a τ of the doubly-hidden tree, which a stable configuration
-- cannot perform (the `ioMove-⊥` sibling; `radec r` IS the
-- `(decMed … ∥⇘ ioES ⇙ absNodesOf …) ∖ ioES ∖ hidden blkA` stack by definition)
medτMove-⊥ : (r : RState)
           → Σ[ M ∈ NetProc ] (decMed (med (toSys r)) ─[ τ ]─► M)
           → isStable (radec r ∖ hidden blkA) → ⊥
medτMove-⊥ r (_ , sM) sta =
  stable-no-τ sta
    (TLH.Hide-τ (hidden blkA) (radec r)
      (lift-med-whole-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) sM))

-- the `empty` arm's enabled move, packaged and PAYLOAD-GENERIC: an UNBROKEN link
-- with an EMPTY BlockFetch `hi` cell accepts the wire-send its own server offers,
-- and the two SYNC into a hidden τ (medium side `medOfferIn`, nodes side the
-- caller's ladder).  `medOfferIn` and `iomem-in` are both generic in the payload
-- (`LiveIoIntro:1134-1140`, `:1258-1260`), so nothing here is `MsgBlock`-specific —
-- which is what lets §4's PRE-region arm reuse it at the `MsgStartBatch` wire-send.
srvSendMove-at-⊥ : (r : RState) (i : Link) (x : Payload)
                 → broken (med (toSys r)) i ≡ false
                 → phase (med (toSys r)) i hi N2N_BlockFetch ≡ empty
                 → IoOffers (absNodesOf (toSys r)) (input i hi N2N_BlockFetch) x
                 → isStable (radec r ∖ hidden blkA) → ⊥
srvSendMove-at-⊥ r i x hbrk he nOff sta =
  ioMove-⊥ r (iomem-in i hi N2N_BlockFetch x)
    (medOfferIn (med (toSys r)) i x hbrk he) nOff sta

-- … and its `MsgBlock` instance, the one §2's streaming arms take
srvSendMove-⊥ : (r : RState) (i : Link) (b : Block₃)
              → broken (med (toSys r)) i ≡ false
              → phase (med (toSys r)) i hi N2N_BlockFetch ≡ empty
              → IoOffers (absNodesOf (toSys r)) (input i hi N2N_BlockFetch) (blkPayload b)
              → isStable (radec r ∖ hidden blkA) → ⊥
srvSendMove-⊥ r i b = srvSendMove-at-⊥ r i (blkPayload b)

------------------------------------------------------------------------
-- §2  THE ENTRY BRIDGE, AND THE FOUR FACTS.
--
-- `chanInv⇒h19` is gated on `SrvStr sa` — the invariant's own streaming region —
-- and what a server POSITION gives is `SrvHas⁺ blkA`.  The bridge between them is
-- three lines and `refl`-shaped, because `coarsenBFs (bsBlk1 b) = bsWblk b`
-- (`SysStep.agda:543`) and `SrvStr (bsWblk b) = ⊤` (`LiveChanInv.agda:225`).
--
-- THE LEG DISPATCH IS ON AN EXPLICIT `TwoLegs` ARGUMENT (never a `with`), and it
-- has to be: every arm needs the hop's accessors REDUCED to a literal link and a
-- literal peer — `cellUp legBD s` is `phase (med s) linkAB hi N2N_BlockFetch` only
-- after the leg is a constructor, and the ladder instance is that link's own.
------------------------------------------------------------------------

-- *** THE ENTRY BRIDGE. ***  a server holding the token is in the invariant's
-- STREAMING region (it has wire-sent its `MsgStartBatch` and not yet its
-- `MsgBatchDone` — `bsBlk1 b` coarsens to `bsWblk b`, which is one of the three
-- positions `SrvStr` accepts)
srvHas⁺⇒str : (b : Block₃) (q : SN.BFsPos) → SrvHas⁺ b q → SrvStr (coarsenBFs q)
srvHas⁺⇒str b .(SN.bsBlk1 b) refl = tt

-- *** ARM `lpUpSrv`, BOTH LEGS. ***  A stable configuration cannot have the token
-- sitting in the leg's UP BF server (node A's, on the leg's up link): whatever the
-- up cell's phase is, H19 hands out an enabled move — the server's own wire-send
-- into an empty cell, the reader's delivery out of a full one, or the medium's
-- drain τ out of a draining one — and the fourth, escape state is refuted by the
-- token exclusion.
srvOpen-up : (l : TwoLegs) (r : RState)
           → broken (med (toSys r)) (upLink l) ≡ false
           → ChanUp l (toSys r) → NoTwoTokens l (toSys r)
           → RefutedAt l lpUpSrv blkA r
srvOpen-up legBD r hbrk ivU ntt at sta =
  arms (chanInv⇒h19 linkAB (coarsenBFs (upSrv legBD (toSys r))) (cellUp legBD (toSys r))
         (coarsenBFc (upClient legBD (toSys r))) ivU
         (srvHas⁺⇒str blkA (upSrv legBD (toSys r)) (proj₁ at)))
  where
  arms : H19 linkAB (cellUp legBD (toSys r)) (coarsenBFc (upClient legBD (toSys r))) → ⊥
  arms (inj₁ he) =
    srvSendMove-⊥ r linkAB blkA hbrk he
      (srvInNodes-A-AB (toSys r) (blkPayload blkA) (SN.bsHead BF.stStreaming)
        (bfs-in-step linkAB hi (upSrv legBD (toSys r)) blkA
          (cong coarsenBFs (proj₁ at))))
      sta
  arms (inj₂ (inj₁ (x , hf , inj₁ acc)))  = cellFull-up-⊥ legBD r x hbrk hf acc sta
  arms (inj₂ (inj₁ (x , hf , inj₂ hold))) =
    nUpSrvCli ntt (srvHas⁺⇒hasBlk blkA (upSrv legBD (toSys r)) (proj₁ at))
      (holdA⇒hasBlk (upClient legBD (toSys r)) hold)
  arms (inj₂ (inj₂ (x , hd))) =
    medτMove-⊥ r (medDrainτ (med (toSys r)) linkAB x hbrk hd) sta
srvOpen-up legCD r hbrk ivU ntt at sta =
  arms (chanInv⇒h19 linkAC (coarsenBFs (upSrv legCD (toSys r))) (cellUp legCD (toSys r))
         (coarsenBFc (upClient legCD (toSys r))) ivU
         (srvHas⁺⇒str blkA (upSrv legCD (toSys r)) (proj₁ at)))
  where
  arms : H19 linkAC (cellUp legCD (toSys r)) (coarsenBFc (upClient legCD (toSys r))) → ⊥
  arms (inj₁ he) =
    srvSendMove-⊥ r linkAC blkA hbrk he
      (srvInNodes-A-AC (toSys r) (blkPayload blkA) (SN.bsHead BF.stStreaming)
        (bfs-in-step linkAC hi (upSrv legCD (toSys r)) blkA
          (cong coarsenBFs (proj₁ at))))
      sta
  arms (inj₂ (inj₁ (x , hf , inj₁ acc)))  = cellFull-up-⊥ legCD r x hbrk hf acc sta
  arms (inj₂ (inj₁ (x , hf , inj₂ hold))) =
    nUpSrvCli ntt (srvHas⁺⇒hasBlk blkA (upSrv legCD (toSys r)) (proj₁ at))
      (holdA⇒hasBlk (upClient legCD (toSys r)) hold)
  arms (inj₂ (inj₂ (x , hd))) =
    medτMove-⊥ r (medDrainτ (med (toSys r)) linkAC x hbrk hd) sta

-- *** ARM `lpDnSrv`, BOTH LEGS. ***  … and not in the leg's DOWN BF server
-- either: there the sender is the RELAY's own server (node B on leg BD, node C on
-- leg CD) and the reader is node D's client on that link.
srvOpen-dn : (l : TwoLegs) (r : RState)
           → broken (med (toSys r)) (dnLink l) ≡ false
           → ChanDn l (toSys r) → NoTwoTokens l (toSys r)
           → RefutedAt l lpDnSrv blkA r
srvOpen-dn legBD r hbrk ivD ntt at sta =
  arms (chanInv⇒h19 linkBD (coarsenBFs (dnSrv legBD (toSys r))) (cellDn legBD (toSys r))
         (coarsenBFc (dnClient legBD (toSys r))) ivD
         (srvHas⁺⇒str blkA (dnSrv legBD (toSys r)) (proj₁ at)))
  where
  arms : H19 linkBD (cellDn legBD (toSys r)) (coarsenBFc (dnClient legBD (toSys r))) → ⊥
  arms (inj₁ he) =
    srvSendMove-⊥ r linkBD blkA hbrk he
      (srvInNodes-B-BD (toSys r) (blkPayload blkA) (SN.bsHead BF.stStreaming)
        (bfs-in-step linkBD hi (dnSrv legBD (toSys r)) blkA
          (cong coarsenBFs (proj₁ at))))
      sta
  arms (inj₂ (inj₁ (x , hf , inj₁ acc)))  = cellFull-dn-⊥ legBD r x hbrk hf acc sta
  arms (inj₂ (inj₁ (x , hf , inj₂ hold))) =
    nDnSrvCli ntt (srvHas⁺⇒hasBlk blkA (dnSrv legBD (toSys r)) (proj₁ at))
      (holdA⇒hasBlk (dnClient legBD (toSys r)) hold)
  arms (inj₂ (inj₂ (x , hd))) =
    medτMove-⊥ r (medDrainτ (med (toSys r)) linkBD x hbrk hd) sta
srvOpen-dn legCD r hbrk ivD ntt at sta =
  arms (chanInv⇒h19 linkCD (coarsenBFs (dnSrv legCD (toSys r))) (cellDn legCD (toSys r))
         (coarsenBFc (dnClient legCD (toSys r))) ivD
         (srvHas⁺⇒str blkA (dnSrv legCD (toSys r)) (proj₁ at)))
  where
  arms : H19 linkCD (cellDn legCD (toSys r)) (coarsenBFc (dnClient legCD (toSys r))) → ⊥
  arms (inj₁ he) =
    srvSendMove-⊥ r linkCD blkA hbrk he
      (srvInNodes-C-CD (toSys r) (blkPayload blkA) (SN.bsHead BF.stStreaming)
        (bfs-in-step linkCD hi (dnSrv legCD (toSys r)) blkA
          (cong coarsenBFs (proj₁ at))))
      sta
  arms (inj₂ (inj₁ (x , hf , inj₁ acc)))  = cellFull-dn-⊥ legCD r x hbrk hf acc sta
  arms (inj₂ (inj₁ (x , hf , inj₂ hold))) =
    nDnSrvCli ntt (srvHas⁺⇒hasBlk blkA (dnSrv legCD (toSys r)) (proj₁ at))
      (holdA⇒hasBlk (dnClient legCD (toSys r)) hold)
  arms (inj₂ (inj₂ (x , hd))) =
    medτMove-⊥ r (medDrainτ (med (toSys r)) linkCD x hbrk hd) sta

------------------------------------------------------------------------
-- §3  *** THE PRE-REGION SHARPENING (cross-node api campaign, T2) — the `pp5`
-- arm's other half. ***
--
-- `LiveDrvBF`'s carried coupling can only pin the leg's down BF server to the
-- REGION `{bsWsb, bsStream}` at the relay driver's `pp5` sub-phase: the api step
-- that enters `pp5` is the driver's own `sendBFStartBatch`, which lands the server
-- at `bsWsb`, and only the server's WIRE-SEND (an io hop past the api one) carries
-- it on to `bsStream` (`NodeSpecs.bfSnxt`: in at `:604-605`, on at `:610-613`).  The
-- residual's own equation is the SINGLETON `≡ bsStream`, so something has to close
-- the `bsWsb` half — and what closes it is STABILITY, exactly as the four io fields
-- close their positions.
--
-- *** WHY THIS IS CHEAP NOW AND WAS NOT BEFORE. ***  The obstruction the campaign's
-- gate recorded was polarity: `H19` is gated on `SrvStr`, and `SrvStr bsWsb = ⊥`
-- (`LiveChanInv:229`), while the old `cvQui` gave only the NEGATIVE `¬ RespFull` —
-- which admits `full (rrPayload r)` and pins no cell phase at all.  T2 strengthened
-- `cvQui` to the POSITIVE `CellPreQ` (`LiveChanInv` §2, preserved at every step
-- class off the existing `cvPre`), and the pre region then has its own two-armed
-- disjunction: empty (the server's own wire-send fires) or draining (the medium's
-- drain τ fires).  Both arms are §1's kits verbatim; no third arm exists, because a
-- `full` cell is what `CellPreQ` excludes.
--
-- (H1) is the same link-unbrokenness these facts always need — a broken link's
-- medium offers nothing — and it is why the two api fields of `InFlightOpen` gained
-- the leg's DOWN-link antecedent when this landed.
------------------------------------------------------------------------

-- RUNG 1 AT THE PRE REGION: any fine position coarsening to `bsWsb` offers the
-- wire-send of its `MsgStartBatch` (`ceqBFs09` is that row; `absBFs l d q` depends
-- on `q` only through `coarsenBFs q`).  *** KEEP IN SYNC with
-- `LiveIoIntro.bfs-in-step` (`:1269-1279`), which is this same shape at `ceqBFs11`
-- and `blkPayload`; the target position is the same `bsHead stStreaming`, because
-- both rows land at `bsStream`. ***
bfs-in-step-sb : (i : Link) (d : Dir) (q : SN.BFsPos)
               → coarsenBFs q ≡ NS.bsWsb
               → absBFs i d q
                   ─[ ev (evl (evLabel Payload (input i d N2N_BlockFetch) sbPayload)) ]─►
                 absBFs i d (SN.bsHead BF.stStreaming)
bfs-in-step-sb i d q pin =
  aBFs i d q (SN.bsHead BF.stStreaming)
    (subst (λ z → NS.bfSfin z ≡ false) (sym pin) refl)
    (subst (λ z → NS.bfSnxt i d z (Payload , input i d N2N_BlockFetch) sbPayload
                  ≡ just NS.bsStream)
           (sym pin) (ceqBFs09 i d))

-- *** THE SHARPENING ITSELF. ***  A stable configuration cannot have the leg's DOWN
-- BF server holding its `MsgStartBatch` back.  The leg dispatch is on an EXPLICIT
-- `TwoLegs` argument for §2's reason: the accessors reduce to a literal link and a
-- literal peer only once the leg is a constructor, and the ladder instance is that
-- link's own.
srvWsb-⊥ : (l : TwoLegs) (r : RState)
         → broken (med (toSys r)) (dnLink l) ≡ false
         → ChanDn l (toSys r)
         → coarsenBFs (dnSrv l (toSys r)) ≡ NS.bsWsb
         → isStable (radec r ∖ hidden blkA) → ⊥
srvWsb-⊥ legBD r hbrk ivD pin sta =
  arms (cvQui ivD (subst SrvPre (sym pin) tt))
  where
  arms : CellPreQ (cellDn legBD (toSys r)) → ⊥
  arms (inj₁ he) =
    srvSendMove-at-⊥ r linkBD sbPayload hbrk he
      (srvInNodes-B-BD (toSys r) sbPayload (SN.bsHead BF.stStreaming)
        (bfs-in-step-sb linkBD hi (dnSrv legBD (toSys r)) pin))
      sta
  arms (inj₂ (x , hd)) =
    medτMove-⊥ r (medDrainτ (med (toSys r)) linkBD x hbrk hd) sta
srvWsb-⊥ legCD r hbrk ivD pin sta =
  arms (cvQui ivD (subst SrvPre (sym pin) tt))
  where
  arms : CellPreQ (cellDn legCD (toSys r)) → ⊥
  arms (inj₁ he) =
    srvSendMove-at-⊥ r linkCD sbPayload hbrk he
      (srvInNodes-C-CD (toSys r) sbPayload (SN.bsHead BF.stStreaming)
        (bfs-in-step-sb linkCD hi (dnSrv legCD (toSys r)) pin))
      sta
  arms (inj₂ (x , hd)) =
    medτMove-⊥ r (medDrainτ (med (toSys r)) linkCD x hbrk hd) sta

------------------------------------------------------------------------
-- §4  (H1) OFF THE WINDOW — the same interface layering the cell facts have.
--
-- `LiveCellOpen` §4 recorded that the two cell fields as banked were window-FREE
-- and that closing that inch was an INTERFACE edit in `LiveStableOffer`, not more
-- proof.  *** THAT EDIT LANDED AT TASK 4, in the window-FREE direction: *** all
-- FOUR io fields (both cells AND both servers) now carry the leg's own link
-- antecedent (`LiveStableOffer:1554-1566`), which is character-for-character §2's
-- hypothesis above, and `parked-of`/`parked-at` thread the window's
-- `wLink1`/`wLink2` into them (`:1630`, `:1581`).  So `LivenessProof.ifo-of`
-- (`:281-306`) consumes §2's RAW pair, and the two window-taking corollaries
-- below are kept as the natural interface for a window-HOLDING caller (see the
-- six-corollary deliberate-keep note at the end of `LiveCellOpen`) — for the same
-- reason as before: `window-BD` / `window-CD` produce
-- `Window legBD (toSys r) linkAB linkBD` / `Window legCD (toSys r) linkAC linkCD`,
-- whose two link fields ARE `upLink l` / `dnLink l` unbroken.
------------------------------------------------------------------------

-- *** §3's FALSIFICATION (T2), arity-preserving, RED, reverted. ***
--
-- (F21  THE SHARPENING'S LADDER IS THE LEG'S OWN)  `srvWsb-⊥`'s `legBD` clause fires
--      the `empty` arm at `linkCD` instead of `linkBD` — same arity, both links in
--      scope, and the nodes-side ladder instance is left at leg BD's, so only the
--      MEDIUM side moves.
--      *** RED ***: `:360.41-45: [UnequalTerms] Data.Fin.Base.Fin.zero !=
--      (Data.Fin.Base.Fin.suc (Data.Fin.Base.fromℕ< _)) of type Fin 2 … when checking
--      that the expression hbrk has type broken (med (toSys r)) linkCD ≡ false`,
--      EXIT=42.  So the wire-send is exhibited on the hop the coupling names, and the
--      leg's own unbrokenness hypothesis is what licenses it — a co-leg link cannot
--      stand in, which is the property the two api fields' new antecedent encodes.

-- the UP server arm, with (H1) taken off the leg's window
srvOpen-up-w : (l : TwoLegs) (r : RState)
             → Window l (toSys r) (upLink l) (dnLink l)
             → ChanUp l (toSys r) → NoTwoTokens l (toSys r)
             → RefutedAt l lpUpSrv blkA r
srvOpen-up-w l r w = srvOpen-up l r (wLink1 w)

-- … and the DOWN server arm, off the window's SECOND link field
srvOpen-dn-w : (l : TwoLegs) (r : RState)
             → Window l (toSys r) (upLink l) (dnLink l)
             → ChanDn l (toSys r) → NoTwoTokens l (toSys r)
             → RefutedAt l lpDnSrv blkA r
srvOpen-dn-w l r w = srvOpen-dn l r (wLink2 w)

------------------------------------------------------------------------
-- §5  (T6c) *** THE `csWar` STABILITY REFUTATION — the `srvWsb-⊥` twin, and the
-- fact `pp2`'s sharpening turns on. ***
--
-- Same three-line shape as §3's: take the coarse pin, read `CellPreQ` off the
-- CARRIED ChainSync channel invariant (`chanCSDn-war`, which is `ccQui` at `csWar`),
-- and dispatch on its two arms — the `empty` one pairs the medium's offer with the
-- nodes' (`srvInNodes-dnCS`, rungs 1-4 composed, which is what `LiveIoIntroCS`
-- landed), the `draining` one is the medium's solo τ.  `medτMove-⊥` is
-- channel-generic and is reused verbatim; only the io-sync kit needed a CS instance,
-- and that instance is `srvSendMove-at-⊥`'s body with `medOfferInCS` and the channel
-- moved from `N2N_BlockFetch` to `N2N_ChainSync` (`iomem-in` is already
-- channel-generic, `LiveIoIntro:1259`).
--
-- Unlike §3's BF twin this needs NO leg dispatch: the leg-level CS kits
-- (`LiveIoIntroCS` §3) already do it, so both legs share one body.
------------------------------------------------------------------------

-- *** KEEP IN SYNC WITH `srvSendMove-at-⊥` (`:179-186`), TWO HUNDRED AND SEVENTY
-- LINES ABOVE IN THIS FILE, LINE BY LINE. ***  This is that lemma VERBATIM modulo the
-- channel: the signature with `N2N_BlockFetch → N2N_ChainSync` at both occurrences,
-- and the body with `medOfferIn → medOfferInCS` (`iomem-in` is already
-- channel-generic, `LiveIoIntro:1259`).  The marker earns its keep here more than
-- anywhere: falsification F40 mutated exactly this line back to `medOfferIn` and
-- thereby made the lemma a BYTE-IDENTICAL copy of its twin, so the revert-by-string
-- found two occurrences and had to be done by line index.  A collapse onto the twin
-- is the hazard; prose provenance does not flag it.
--
-- the `empty` arm's enabled move on the CHAINSYNC channel
srvSendMoveCS-at-⊥ : (r : RState) (i : Link) (x : Payload)
                   → broken (med (toSys r)) i ≡ false
                   → phase (med (toSys r)) i hi N2N_ChainSync ≡ empty
                   → IoOffers (absNodesOf (toSys r)) (input i hi N2N_ChainSync) x
                   → isStable (radec r ∖ hidden blkA) → ⊥
srvSendMoveCS-at-⊥ r i x hbrk he nOff sta =
  ioMove-⊥ r (iomem-in i hi N2N_ChainSync x)
    (medOfferInCS (med (toSys r)) i x hbrk he) nOff sta

-- *** THE REFUTATION. ***  a STABLE configuration cannot have its leg's DOWN
-- ChainSync server at `csWar` on an unbroken link
csWar-⊥ : (l : TwoLegs) (r : RState)
        → broken (med (toSys r)) (dnLink l) ≡ false
        → ChanCSDn l (toSys r)
        → coarsenCSs (dnCSsOf l (toSys r)) ≡ NS.csWar
        → isStable (radec r ∖ hidden blkA) → ⊥
csWar-⊥ l r hbrk ivD pin sta = arms (chanCSDn-war l (toSys r) ivD pin)
  where
  arms : CellPreQCS (cellCSDn l (toSys r)) → ⊥
  arms (inj₁ he) =
    srvSendMoveCS-at-⊥ r (dnLink l) arPayload hbrk he
      (srvInNodes-dnCS l (toSys r) pin) sta
  arms (inj₂ (x , hd)) =
    medτMove-⊥ r (medDrainτCS-dn l (toSys r) x hbrk hd) sta

------------------------------------------------------------------------
-- §6  (T8c-ii) *** THE THREE `csIdle` EXCLUSIONS — the three `⊥`-premises of
-- `LiveDrvCSD.dnFresh⇒areq`, discharged. ***
--
-- The `cp6`/`pp0` arms say "at a STABLE state the leg's down CS server is at
-- `csAreq`", and `LiveDrvCSD`'s freshness clause narrows the alternatives to ONE:
-- `csIdle`.  Refuting `csIdle` splits on the hop's CELL, whose three fresh arms are
-- `empty`, `draining x` and `ReqOnly` (an unread `MsgCSRequestNext`), and each arm
-- names one enabled move:
--
--   (1) `draining x` — the MEDIUM's own solo τ.  One line, on the op T6b landed;
--       this arm needs no nodes-side ladder at all, exactly as §5's does not.
--   (2) `ReqOnly` — the SERVER's own wire READ.  §1c's medium half at a FULL cell
--       paired with §2b(b)'s reader ladder.  *** THE ONE PREMISE THAT NEEDS THE
--       SERVER's POSITION: *** the read row is `csIdle → csAreq`, so the arm is
--       stated with the coarse pin as a hypothesis, which is why `dnFresh⇒areq`'s
--       second premise carries the `≡ csIdle` antecedent.
--   (3) `empty` with node D's CLIENT at `ccWreq` — the CLIENT's own wire WRITE.
--       §2b(a)'s ladder, the first client-side io intro on the CS axis.
--
-- *** ALL THREE ARE `csWar-⊥`'s SHAPE (§5), AND DELIBERATELY SO. ***  Take a coarse
-- pin (or a cell equation), pair the medium's move with the nodes', and let
-- `ioMove-⊥` / `medτMove-⊥` turn the sync into the τ a stable configuration cannot
-- perform.  What is new is only WHICH peer fires and at WHICH polarity — and neither
-- needs a leg dispatch, because the leg-level CS kits (`LiveIoIntroCS` §3) do it.
------------------------------------------------------------------------

-- *** KEEP IN SYNC WITH `srvSendMoveCS-at-⊥` (§5), LINE BY LINE. ***  This is that
-- lemma at the READER's polarity: `input → output` at both occurrences, `empty →
-- full x` in the cell premise, `medOfferInCS → medOfferOutCS` and `iomem-in →
-- iomem-out` in the body.  The collapse hazard §5's own marker names applies here
-- too — a mutation back to the `input` kit makes this a byte-identical copy of its
-- twin, so a revert-by-string would find two occurrences
srvReadMoveCS-at-⊥ : (r : RState) (i : Link) (x : Payload)
                   → broken (med (toSys r)) i ≡ false
                   → phase (med (toSys r)) i hi N2N_ChainSync ≡ full x
                   → IoOffers (absNodesOf (toSys r)) (output i hi N2N_ChainSync) x
                   → isStable (radec r ∖ hidden blkA) → ⊥
srvReadMoveCS-at-⊥ r i x hbrk hf nOff sta =
  ioMove-⊥ r (iomem-out i hi N2N_ChainSync x)
    (medOfferOutCS (med (toSys r)) i x hbrk hf) nOff sta

-- (1) *** THE DRAINING ARM. ***  a STABLE configuration cannot have the leg's down
-- ChainSync cell mid-drain on an unbroken link.  `csWar-⊥`'s second arm, promoted to
-- a lemma of its own because `dnFresh⇒areq` takes it as a premise rather than
-- reaching it through a `CellPreQCS`
cellDrainCS-⊥ : (l : TwoLegs) (r : RState) (x : Payload)
              → broken (med (toSys r)) (dnLink l) ≡ false
              → cellCSDn l (toSys r) ≡ draining x
              → isStable (radec r ∖ hidden blkA) → ⊥
cellDrainCS-⊥ l r x hbrk hd sta =
  medτMove-⊥ r (medDrainτCS-dn l (toSys r) x hbrk hd) sta

-- (2) *** THE UNREAD-REQUEST ARM. ***  a STABLE configuration cannot have the leg's
-- down ChainSync cell holding a `MsgCSRequestNext` its own server has not read: the
-- server is at `csIdle` by hypothesis and `csIdle` is exactly where the read row
-- lives.  The payload's three lenient components travel from `LiveChanCS.FullMsg`
cellReqCS-⊥ : (l : TwoLegs) (r : RState) (t : Time) (md : Mode) (ln : Length)
            → broken (med (toSys r)) (dnLink l) ≡ false
            → coarsenCSs (dnCSsOf l (toSys r)) ≡ NS.csIdle
            → cellCSDn l (toSys r) ≡ full (t , md , ln , chainSync MsgCSRequestNext)
            → isStable (radec r ∖ hidden blkA) → ⊥
cellReqCS-⊥ l r t md ln hbrk hidl hf sta =
  srvReadMoveCS-at-⊥ r (dnLink l) (t , md , ln , chainSync MsgCSRequestNext) hbrk hf
    (srvOutNodes-dnCS l (toSys r) t md ln hidl) sta

-- (3) *** THE PENDING-WRITE ARM. ***  a STABLE configuration cannot have node D's
-- own down-hop CS client at `ccWreq` facing an EMPTY cell: the client's request
-- write is enabled.  `srvSendMoveCS-at-⊥` is payload-generic and peer-agnostic — it
-- only wants the nodes' offer — so the CLIENT's ladder rides the same kit as the
-- server's, despite the name
cliWreqCS-⊥ : (l : TwoLegs) (r : RState)
            → broken (med (toSys r)) (dnLink l) ≡ false
            → cellCSDn l (toSys r) ≡ empty
            → coarsenCSc (dnCScOf l (toSys r)) ≡ NS.ccWreq
            → isStable (radec r ∖ hidden blkA) → ⊥
cliWreqCS-⊥ l r hbrk he hcw sta =
  srvSendMoveCS-at-⊥ r (dnLink l) rnPayload hbrk he
    (cliInNodes-dnCS l (toSys r) hcw) sta

------------------------------------------------------------------------
-- §6b  (T8c-ii) §6's FALSIFICATIONS — FOUR, one per novel family of the slice: the
-- reader rung's LANDING, node D's ladder's OPERAND, the collapse hazard the §5
-- marker names, and the positional fold's own DISEQUALITY.  All arity-preserving,
-- all RUN, all RED, all reverted by STRING INVERSION with `git status` verified
-- clean after each.  Line numbers are as-run at `2731b98`.
--
-- (F70  *** THE READER RUNG's LANDING (`LiveIoIntroCS.css-out-step`). ***)  return
--      the step at `SN.ssDone1` instead of `SN.ssReqNext1` — both are fine CS-server
--      positions, both are one hop out of `csIdle` in the table, and the mutation
--      an author transcribing `css-in-step` would make.  *** RED ***
--      `LiveIoIntroCS.agda:923.3-930.50: error: [UnequalTerms] NS.csDdone !=
--      NS.csAreq of type NS.CSsPos …`.  What it establishes: the rung's target is
--      pinned by `ceqCSs01`'s own landing, so the ladder cannot be aimed at the
--      `MsgCSDone` row by accident — which matters because that row leaves `csIdle`
--      too and would take the server OUT of the fresh region.
--
-- (F71  *** NODE D's LADDER's BUNDLE OPERAND (`cliInNodeD-BD`). ***)  lift the BD
--      bundle's offer through `⦀-ev-R` instead of `⦀-ev-L`.  *** This is the exact
--      mistake the transcription invites: *** §2's node-B rung uses `⦀-ev-R`, because
--      node B's tracked bundle is its SECOND operand, while node D's BD bundle is its
--      FIRST.  *** RED ***  `LiveIoIntroCS.agda:833.10-836.55: error: [UnequalTerms]
--      fzero != fsuc (Data.Fin.fromℕ< _) of type Fin 2 …`.  What it establishes: the
--      operand order is load-bearing and the error is at the LINK level, so a
--      cross-wired node-D ladder cannot typecheck.
--
-- (F72  *** THE COLLAPSE HAZARD, RUN THIS TIME. ***)  §5's marker warns that a
--      mutation of `srvReadMoveCS-at-⊥`'s medium call back to the `input` kit makes
--      the lemma a byte-identical copy of its twin; F40 ran that mutation one axis
--      over.  Here: `medOfferInCS` for `medOfferOutCS`.  *** RED ***
--      `LiveSrvOpen.agda:545.44-46: error: [UnequalTerms] (full x) != empty of type
--      CopyPhase … when checking that the expression hf has type phase (med (toSys
--      r)) i hi N2N_ChainSync ≡ empty`.  What it establishes: the two kits are
--      separated by the CELL PHASE in the premise, not merely by the label — so the
--      collapse is caught by the hypothesis and not only by the conclusion.
--
-- (F73  *** THE POSITIONAL FOLD's OWN DISEQUALITY (`fold-offers-out-cs`). ***)  swap
--      the `dv` (direction) and `iv` (protocol id) refusals at the two cells
--      flanking the fired one — arity-preserving (both take the same five
--      arguments), and the mutation a transcriber reading the nest top-down would
--      make.  *** RED ***  `LiveIoIntroCS.agda:364.69-70: error: [ShouldBeEmpty]
--      N2N_ChainSync ≡ N2N_ChainSync should be empty, but the following constructor
--      patterns are valid: refl …`.  What it establishes: each of the three
--      before-cells is refused for its OWN reason (`lo` differs in DIRECTION, the
--      KeepAlive `hi` cell in PROTOCOL ID), so the position-3 nest really is
--      positional and a re-ordered `uniformCfg` breaks it HERE rather than silently.
--
-- *** RE-AIMING NOTES. ***  F70/F71/F73 are aimed at `LiveIoIntroCS`; they are
-- recorded HERE because this file is where the three ladders are CONSUMED, the
-- F64/F65 convention.  If `LiveIoIntroCS` §2b(a) is ever generalised to both
-- directions (its `hi` is fixed, exactly as §1b's note says), F71 must be re-aimed at
-- the generalised rung rather than deleted.  F72 dies only if the two kits are merged
-- into one polarity-parametric lemma — in which case the merged lemma is a new family
-- and wants its own guard.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §7  (T11) *** THE THREE `bsIdle` EXCLUSIONS — the first three `⊥`-premises of
-- `LiveDrvBFD.bfFresh⇒areq`, discharged. ***
--
-- §6 one PROTOCOL over.  The `pp3` arm says "at a STABLE state the leg's down BF
-- server is at `bsAreq rg`", and `LiveDrvBFD`'s freshness clause narrows the
-- alternatives to ONE: `bsIdle`.  Refuting `bsIdle` splits on the hop's CELL,
-- whose three fresh arms are `empty`, `draining x` and `RngOnly` (an unread
-- `MsgRequestRange`), and each arm names one enabled move:
--
--   (1) `draining x` — the MEDIUM's own solo τ, `medDrainτ` + `medτMove-⊥`.  No
--       nodes-side ladder at all, exactly as §6(1) and §2's fourth arm.
--   (2) `RngOnly` — the SERVER's own wire READ.  *** THE ONE PREMISE THAT NEEDS
--       THE SERVER's POSITION: *** the read row is `bsIdle → bsAreq r`, so the
--       arm is stated with the coarse pin as a hypothesis, which is why
--       `bfFresh⇒areq`'s second premise carries the `≡ bsIdle` antecedent.  Its
--       nodes side is §10's new `srvOutNodes-*` ladder.
--   (3) `empty` with node D's CLIENT at `bcWrr r` — the CLIENT's own wire WRITE,
--       on §10's other new ladder.  `srvSendMove-at-⊥` is payload-generic and
--       peer-agnostic — it only wants the nodes' offer — so the CLIENT's ladder
--       rides the same kit as the server's, despite the name (§6(3)'s note at
--       the other protocol).
--
-- The reader-polarity kit is NEW here only in the sense that §1 never needed it:
-- `medOfferOut` is `LiveIoIntro` §4's and `LiveChanRead.cellFull-dn-⊥` calls it
-- with the CLIENT as the offerer.  `srvReadMove-at-⊥` below is that lemma with
-- the offer left as an argument, which is what lets the SERVER be the reader.
------------------------------------------------------------------------

-- *** KEEP IN SYNC WITH `srvSendMove-at-⊥` (§1), LINE BY LINE. ***  This is that
-- lemma at the READER's polarity: `input → output` at both occurrences, `empty →
-- full x` in the cell premise, `medOfferIn → medOfferOut` and `iomem-in →
-- iomem-out` in the body.  The collapse hazard is the one `LiveSrvOpen` §5's
-- marker names: a mutation back to the `input` kit makes this a byte-identical
-- copy of its twin, so a revert-by-string would find two occurrences
srvReadMove-at-⊥ : (r : RState) (i : Link) (x : Payload)
                 → broken (med (toSys r)) i ≡ false
                 → phase (med (toSys r)) i hi N2N_BlockFetch ≡ full x
                 → IoOffers (absNodesOf (toSys r)) (output i hi N2N_BlockFetch) x
                 → isStable (radec r ∖ hidden blkA) → ⊥
srvReadMove-at-⊥ r i x hbrk hf nOff sta =
  ioMove-⊥ r (iomem-out i hi N2N_BlockFetch x)
    (medOfferOut (med (toSys r)) i x hbrk hf) nOff sta

-- (1) *** THE DRAINING ARM. ***  a STABLE configuration cannot have the leg's
-- down BlockFetch cell mid-drain on an unbroken link.  `srvOpen-up`'s fourth arm,
-- promoted to a lemma of its own because `bfFresh⇒areq` takes it as a premise
-- rather than reaching it through an `H19`
cellDrainBF-dn-⊥ : (l : TwoLegs) (r : RState) (x : Payload)
                 → broken (med (toSys r)) (dnLink l) ≡ false
                 → cellDn l (toSys r) ≡ draining x
                 → isStable (radec r ∖ hidden blkA) → ⊥
cellDrainBF-dn-⊥ legBD r x hbrk hd sta =
  medτMove-⊥ r (medDrainτ (med (toSys r)) linkBD x hbrk hd) sta
cellDrainBF-dn-⊥ legCD r x hbrk hd sta =
  medτMove-⊥ r (medDrainτ (med (toSys r)) linkCD x hbrk hd) sta

-- (2) *** THE UNREAD-REQUEST ARM. ***  a STABLE configuration cannot have the
-- leg's down BlockFetch cell holding a `MsgRequestRange` its own server has not
-- read: the server is at `bsIdle` by hypothesis and `bsIdle` is exactly where the
-- read row lives.  The payload's three lenient components travel from
-- `LiveDrvBFD.RngOnly`, which is `ceqBFs01`'s own leniency
cellRngBF-dn-⊥ : (l : TwoLegs) (r : RState)
                 (t0 : Time) (md : Mode) (ln : Length) (rg : ChainRange)
               → broken (med (toSys r)) (dnLink l) ≡ false
               → coarsenBFs (dnSrv l (toSys r)) ≡ NS.bsIdle
               → cellDn l (toSys r) ≡ full (t0 , md , ln , blockFetch (MsgRequestRange rg))
               → isStable (radec r ∖ hidden blkA) → ⊥
cellRngBF-dn-⊥ legBD r t0 md ln rg hbrk hidl hf sta =
  srvReadMove-at-⊥ r linkBD (t0 , md , ln , blockFetch (MsgRequestRange rg)) hbrk hf
    (srvOutNodes-B-BD (toSys r) (t0 , md , ln , blockFetch (MsgRequestRange rg))
      (SN.bsReq1 rg)
      (bfs-out-step linkBD hi (dnSrv legBD (toSys r)) t0 md ln rg hidl))
    sta
cellRngBF-dn-⊥ legCD r t0 md ln rg hbrk hidl hf sta =
  srvReadMove-at-⊥ r linkCD (t0 , md , ln , blockFetch (MsgRequestRange rg)) hbrk hf
    (srvOutNodes-C-CD (toSys r) (t0 , md , ln , blockFetch (MsgRequestRange rg))
      (SN.bsReq1 rg)
      (bfs-out-step linkCD hi (dnSrv legCD (toSys r)) t0 md ln rg hidl))
    sta

-- (3) *** THE PENDING-WRITE ARM. ***  a STABLE configuration cannot have node D's
-- own down-hop BF client at `bcWrr rg` facing an EMPTY cell: the client's request
-- write is enabled.  The payload is PINNED here where (2)'s is lenient, because
-- the writer's own row tests the tuple (`ceqBFc07`)
cliWrrBF-dn-⊥ : (l : TwoLegs) (r : RState) (rg : ChainRange)
              → broken (med (toSys r)) (dnLink l) ≡ false
              → cellDn l (toSys r) ≡ empty
              → coarsenBFc (dnClient l (toSys r)) ≡ NS.bcWrr rg
              → isStable (radec r ∖ hidden blkA) → ⊥
cliWrrBF-dn-⊥ legBD r rg hbrk he hcw sta =
  srvSendMove-at-⊥ r linkBD
    (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange rg)) hbrk he
    (cliInNodes-D-BD (toSys r)
      (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange rg))
      (SN.bcHead BF.stBusy)
      (bfc-in-step linkBD hi (dnClient legBD (toSys r)) rg hcw))
    sta
cliWrrBF-dn-⊥ legCD r rg hbrk he hcw sta =
  srvSendMove-at-⊥ r linkCD
    (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange rg)) hbrk he
    (cliInNodes-D-CD (toSys r)
      (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange rg))
      (SN.bcHead BF.stBusy)
      (bfc-in-step linkCD hi (dnClient legCD (toSys r)) rg hcw))
    sta

------------------------------------------------------------------------
-- §7b  (T11) §7's FALSIFICATION — ONE, at the novel family of the slice: the
-- reader-polarity BlockFetch ladder's LANDING.  Arity-preserving, RUN, RED,
-- reverted by string inversion with `git diff` verified clean.  Recorded HERE
-- rather than at `LiveIoIntro` because this file is where the ladder is CONSUMED
-- (the F64/F65 convention, and F70/F71's own precedent one protocol over).
--
-- (F95  *** THE READER RUNG's LANDING (`LiveIoIntro.bfs-out-step`). ***)  return
--      the step at `SN.bsDone1` instead of `SN.bsReq1 r` — both are fine BF-server
--      positions, both are ONE HOP out of `bsIdle` in the table (`bfSnxt bsIdle`'s
--      two rows are the range request and the client-done), and it is the mutation
--      an author transcribing the sibling rung would make.
--      *** RED ***: `LiveIoIntro.agda:1508.3-1513.55: [UnequalTerms] NS.bsDdone !=
--      NS.bsAreq r of type NS.BFsPos`, EXIT=42.  What it establishes: the rung's
--      target is pinned by `ceqBFs01`'s own landing, so the ladder cannot be aimed
--      at the `MsgClientDone` row by accident — which MATTERS here for the same
--      reason F70's did on the ChainSync axis: that row leaves `bsIdle` too, and
--      its target `bsDdone` is OUTSIDE `LiveDrvBFD.SrvFreshBF`, so a mis-aimed
--      ladder would refute a step the freshness region needs to keep excluded by
--      its CELL conjunct instead.
--
-- *** (T11 FIX ROUND) F98 — THE SAME GUARD ONE PROTOCOL OVER, at §8's own novel
-- family: the CHAINSYNC reader ladder's landing. ***  (T11 review's I-3: §2c is a
-- NEW io direction and was unguarded — F95's exact analogue was owed.)
--
-- (F98  *** THE CS READER ARM's LANDING (`cliAwaitAr-⊥`). ***)  return the client's
--      read step at `SN.csHead CS.stIdle` instead of `SN.csHead CS.stMustReply` —
--      both are fine CS-client head positions and the mutation a transcriber
--      reading the four `ceqCSc*` rows in a column would make.  Arity-preserving.
--      *** RED ***: `LiveSrvOpen.agda:839.8-842.61: [UnequalTerms] NS.ccMust !=
--      NS.ccIdle of type NS.CScPos … when checking that the inferred type of an
--      application NS.csCnxt (dnLink l) hi _y (Payload , output (dnLink l) hi
--      N2N_ChainSync) (t , md , ln , chainSync MsgCSAwaitReply) ≡ just NS.ccMust`,
--      EXIT=42.  What it establishes: the reader ladder is TARGET-GENERIC (§2c takes
--      `csc′` and a step), so nothing but `ceqCSc06`'s OWN landing pins the
--      successor — the ladder cannot be aimed at a neighbouring position by
--      accident.  Reverted by string inversion, `git status` clean after.
------------------------------------------------------------------------

------------------------------------------------------------------------
-- §8  (T11) *** THE DOWN CS CELL's READER-SIDE REFUTATIONS — what every
-- full-cell case of the `pp3` arm's `cp1` LEAF turns on. ***
--
-- §6 refuted a full down-CS cell holding node D's own REQUEST, by the SERVER's
-- read.  The leaf's cases are the mirror: the cell holds a RESPONDER payload the
-- relay's server wrote, and the enabled move is node D's CLIENT's own delivery.
-- The ladder is `LiveIoIntroCS` §2c — the fourth and last ChainSync direction,
-- landed for exactly this — and the medium half is §6's `medOfferOutCS`, so the
-- kit here is `srvReadMoveCS-at-⊥` again: *** it is peer-AGNOSTIC (it only wants
-- the nodes' offer), so the CLIENT rides the lemma named for the server, exactly
-- as §6(3)'s write arm does. ***
--
-- THREE arms, one per (client position × payload) pair the leaf's cell conjunct
-- can present: `ccAwait` reading the `MsgCSAwaitReply`, `ccAwait` reading the
-- `MsgCSRollForward` and `ccMust` reading it.  The two rollback rows
-- (`ceqCSc05`/`ceqCSc08`) are deliberately NOT instantiated: `produce` never
-- fires `sendCSRollBackward`, so no rollback payload can be in the cell, and the
-- leaf's `ccArb` member is an EXCLUSION rather than a refutation (T9's item
-- (iii)) — instantiating them here would suggest otherwise.
------------------------------------------------------------------------

-- the generic reader kit: an unbroken link, a FULL down CS cell and a step of node
-- D's own client on that link refute stability
cliReadCS-dn-⊥ : (l : TwoLegs) (r : RState) (x : Payload) (csc′ : SN.CScPos)
               → broken (med (toSys r)) (dnLink l) ≡ false
               → cellCSDn l (toSys r) ≡ full x
               → absCSc (dnLink l) hi (dnCScOf l (toSys r))
                   ─[ ev (evl (evLabel Payload (output (dnLink l) hi N2N_ChainSync) x)) ]─►
                 absCSc (dnLink l) hi csc′
               → isStable (radec r ∖ hidden blkA) → ⊥
cliReadCS-dn-⊥ l r x csc′ hbrk hf cStep sta =
  srvReadMoveCS-at-⊥ r (dnLink l) x hbrk hf
    (cliOutNodes-dnCS l (toSys r) x csc′ cStep) sta

-- (1) an AWAITING client facing the server's unread `MsgCSAwaitReply`
cliAwaitAr-⊥ : (l : TwoLegs) (r : RState) (t : Time) (md : Mode) (ln : Length)
             → broken (med (toSys r)) (dnLink l) ≡ false
             → coarsenCSc (dnCScOf l (toSys r)) ≡ NS.ccAwait
             → cellCSDn l (toSys r) ≡ full (t , md , ln , chainSync MsgCSAwaitReply)
             → isStable (radec r ∖ hidden blkA) → ⊥
cliAwaitAr-⊥ l r t md ln hbrk hci hf sta =
  cliReadCS-dn-⊥ l r (t , md , ln , chainSync MsgCSAwaitReply)
    (SN.csHead CS.stMustReply) hbrk hf
    (aCSc (dnLink l) hi (dnCScOf l (toSys r)) (SN.csHead CS.stMustReply)
      (subst (λ z → NS.csCfin z ≡ false) (sym hci) refl)
      (subst (λ z → NS.csCnxt (dnLink l) hi z
                      (Payload , output (dnLink l) hi N2N_ChainSync)
                      (t , md , ln , chainSync MsgCSAwaitReply) ≡ just NS.ccMust)
             (sym hci) (ceqCSc06 {t} {md} {ln} (dnLink l) hi)))
    sta

-- (2) … and facing the unread `MsgCSRollForward` (the payload the `pp3` arm's own
-- api step put on the wire one step earlier)
cliAwaitRfw-⊥ : (l : TwoLegs) (r : RState) (t : Time) (md : Mode) (ln : Length)
                (h : Header) (tp : Tip)
              → broken (med (toSys r)) (dnLink l) ≡ false
              → coarsenCSc (dnCScOf l (toSys r)) ≡ NS.ccAwait
              → cellCSDn l (toSys r)
                  ≡ full (t , md , ln , chainSync (MsgCSRollForward h tp))
              → isStable (radec r ∖ hidden blkA) → ⊥
cliAwaitRfw-⊥ l r t md ln h tp hbrk hci hf sta =
  cliReadCS-dn-⊥ l r (t , md , ln , chainSync (MsgCSRollForward h tp))
    (SN.csRF1 h tp) hbrk hf
    (aCSc (dnLink l) hi (dnCScOf l (toSys r)) (SN.csRF1 h tp)
      (subst (λ z → NS.csCfin z ≡ false) (sym hci) refl)
      (subst (λ z → NS.csCnxt (dnLink l) hi z
                      (Payload , output (dnLink l) hi N2N_ChainSync)
                      (t , md , ln , chainSync (MsgCSRollForward h tp))
                    ≡ just (NS.ccArf (h , tp)))
             (sym hci) (ceqCSc04 {t} {md} {ln} {h} {tp} (dnLink l) hi)))
    sta

-- (3) … and a MUST-REPLY client facing it (the client that has already consumed
-- the `MsgCSAwaitReply`) — the `ccMust` row, `ceqCSc07`
cliMustRfw-⊥ : (l : TwoLegs) (r : RState) (t : Time) (md : Mode) (ln : Length)
               (h : Header) (tp : Tip)
             → broken (med (toSys r)) (dnLink l) ≡ false
             → coarsenCSc (dnCScOf l (toSys r)) ≡ NS.ccMust
             → cellCSDn l (toSys r)
                 ≡ full (t , md , ln , chainSync (MsgCSRollForward h tp))
             → isStable (radec r ∖ hidden blkA) → ⊥
cliMustRfw-⊥ l r t md ln h tp hbrk hci hf sta =
  cliReadCS-dn-⊥ l r (t , md , ln , chainSync (MsgCSRollForward h tp))
    (SN.csRF1 h tp) hbrk hf
    (aCSc (dnLink l) hi (dnCScOf l (toSys r)) (SN.csRF1 h tp)
      (subst (λ z → NS.csCfin z ≡ false) (sym hci) refl)
      (subst (λ z → NS.csCnxt (dnLink l) hi z
                      (Payload , output (dnLink l) hi N2N_ChainSync)
                      (t , md , ln , chainSync (MsgCSRollForward h tp))
                    ≡ just (NS.ccArf (h , tp)))
             (sym hci) (ceqCSc07 {t} {md} {ln} {h} {tp} (dnLink l) hi)))
    sta

-- (4) *** THE `csWrf` WRITE ARM — the SERVER's own pending rollforward. ***  a
-- STABLE configuration cannot have the relay's down CS server at `csWrf ht`
-- facing an EMPTY cell: its wire-send is enabled.  `csWar-⊥`'s shape at the
-- position the `pp3` arm's server sits in, on `LiveIoIntroCS` §3's new position
-- instance (the 12-22-line rung the T9 verification measured off `ceqCSs14`).
-- The payload is PINNED (`time₀`/`FromResponder`/`length₀`) because the writer's
-- own row tests the tuple
srvWrf-⊥ : (l : TwoLegs) (r : RState) (h : Header) (tp : Tip)
         → broken (med (toSys r)) (dnLink l) ≡ false
         → coarsenCSs (dnCSsOf l (toSys r)) ≡ NS.csWrf (h , tp)
         → cellCSDn l (toSys r) ≡ empty
         → isStable (radec r ∖ hidden blkA) → ⊥
srvWrf-⊥ l r h tp hbrk pin he sta =
  srvSendMoveCS-at-⊥ r (dnLink l)
    (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h tp)) hbrk he
    (srvInNodesRfw-dnCS l (toSys r) h tp pin) sta

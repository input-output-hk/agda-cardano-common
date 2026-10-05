{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the per-leg BLOCK-VALUE invariant `PipeVal`
-- (`Praos.PipeValInv`), the SESSION-35 Phase-2 statement layer.
--
-- WHY.  `FourNodeDiamondLiveness.arrivedD` is payload-AGNOSTIC: the `a ≡ b`
-- conjunct that `producedA` carries was dropped because the delivered block
-- `b″` could not be tied to the produced one.  Two links are missing:
-- `b ≡ blkA` (available at the produce frame — node A's driver `!`-pins the
-- value) and `b″ ≡ blkA` (a copy-cell VALUE invariant).  This module states the
-- second, at the SAME per-leg granularity `PipeInv`/`PipeSrvInv` use, so it can
-- ride the existing `PipeInvS` fold as a rider rather than a rewrite.
--
-- THE GATE PASSED (`Praos.PipeValGate`, session 35): every edge of the value
-- chain is machine-checked value-TIGHT, so the eight clauses below are TRUE.
--
-- SHAPE.  A LEAF beside `PipeInv`/`PipeSrvInv` (base modules stay READ-ONLY),
-- deliberately OVER-PROVISIONED: it carries the two SERVER slots and the two
-- CLIENT slots and the relay slot and the D-consumer slot, even though the
-- headline only needs the last two — a carried-but-unused clause costs nothing,
-- a dropped one costs a session (this campaign's own `DReport` under-provision
-- is the live example; see the ANCHORING note at the bottom).
--
-- ECONOMY (measured against the alternative of value-refining `PipeInv` in
-- place).  `PipeInv.MsgIsBlk`/`BFcHasBlk`/`BFsHasBlk` occur in NEGATIVE position
-- inside `Coupled`/`SrvCoupled` (they are ANTECEDENTS of the phase-coupling
-- implications), so strengthening them WEAKENS those invariants instead of
-- delivering the value fact — the value clauses must be POSITIVE and therefore
-- must be new. Adding them as a parallel leaf also keeps the blast radius at
-- zero for the 137-module closure: nothing existing changes type.
--
-- The `ConsPh` value clause is deliberately VACUOUS before `cp4`: the block a
-- consume driver carries at `cp2`/`cp3` came from the ChainSync `RollForward`
-- header, so demanding `≡ blkA` there would drag the whole ChainSync chain (CS
-- cell + CS client + CS server positions) into the invariant.  It is not
-- needed: the DELIVERED value is rebound at the `cp3 → cp4` hop from the BF
-- CLIENT's held block (`PipeValGate.cons-cp3-rebind` + `.cli-ablk-pins`), which
-- clause (7) already covers.  Same for the relay's `consuming` arm.
--
-- No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Product using ( _×_; _,_; proj₁; proj₂ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Data p
  using ( Messages; blockFetch; MsgBlock )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; nD; initial )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; empty; full; draining )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN
  using ( ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; CPPh; consuming; producing
        ; ConsDPh; consD; cblk; cph
        ; BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
        ; BFsPos; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1
        ; bsBatchDone1; bsSil )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD; phOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( cellUp; cellDn; upClient; dnClient; relayOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv; dnSrv )

------------------------------------------------------------------------
-- The per-component value classifiers.  Each is TOTAL and `⊤` everywhere a
-- `Block₃` is not being held, so the invariant is vacuous off the pipeline.
------------------------------------------------------------------------

-- a wire message that carries a block carries `blkA` (every other message,
-- BlockFetch or not, is unconstrained)
MsgValOK : Messages → Set
MsgValOK (blockFetch (MsgBlock b)) = b ≡ blkA
MsgValOK _                         = ⊤

-- a medium copy cell holding a block holds `blkA` (`draining` counts: the
-- post-`output` transient still names the delivered payload)
CellValOK : CopyPhase → Set
CellValOK empty                      = ⊤
CellValOK (full     (_ , _ , _ , m)) = MsgValOK m
CellValOK (draining (_ , _ , _ , m)) = MsgValOK m

-- a BF SERVER peer holding a block for its wire-send holds `blkA`
SrvValOK : BFsPos → Set
SrvValOK (bsBlk1 b)   = b ≡ blkA
SrvValOK (bsHead _)   = ⊤
SrvValOK (bsReq1 _)   = ⊤
SrvValOK bsDone1      = ⊤
SrvValOK bsStart1     = ⊤
SrvValOK bsNoBlk1     = ⊤
SrvValOK bsBatchDone1 = ⊤
SrvValOK (bsSil _)    = ⊤

-- a BF CLIENT peer holding a received block (offering `recvBFBlock !`) holds
-- `blkA` — this is the clause the DELIVERED value is read off
CliValOK : BFcPos → Set
CliValOK (bcBlk1 b) = b ≡ blkA
CliValOK (bcHead _) = ⊤
CliValOK (bcReq1 _) = ⊤
CliValOK bcDone1    = ⊤
CliValOK (bcSil _)  = ⊤

-- a consume-driver phase's recorded block, constrained only from `cp4` on (the
-- phase at which the `recvBFBlock` hop has rebound it from the BF client);
-- before that the field is the ChainSync-derived placeholder and is unread
ConsValAt : Block₃ → ConsPh → Set
ConsValAt b cp0 = ⊤
ConsValAt b cp1 = ⊤
ConsValAt b cp2 = ⊤
ConsValAt b cp3 = ⊤
ConsValAt b cp4 = b ≡ blkA
ConsValAt b cp5 = b ≡ blkA
ConsValAt b cp6 = b ≡ blkA

-- the RELAY driver's block: constrained past the receive hop on the consume
-- arm, and always on the produce arm (a relay only starts producing with the
-- block it consumed — `PipeValGate.relay-handoff`)
RelayValOK : CPPh → Set
RelayValOK (consuming b cp) = ConsValAt b cp
RelayValOK (producing b _)  = b ≡ blkA

-- node D's consume-driver slot
ConsDValOK : ConsDPh → Set
ConsDValOK (consD b ph) = ConsValAt b ph

-- the block a RELAY phase carries, on either arm (SESSION-44: the accessor the
-- value-carrying relay classifier `PipeValRelay.cpStepKindL-of⁺` reports at)
relayBlk : CPPh → Block₃
relayBlk (consuming b _) = b
relayBlk (producing b _) = b

------------------------------------------------------------------------
-- Per-leg accessor for node D's consume slot (mirrors `WalkPr.phOf`, but
-- returning the WHOLE `ConsDPh` — `phOf l s ≡ cph (consOf l s)` by `refl`).
------------------------------------------------------------------------

-- the leg's node-D consume-driver slot (block + phase)
consOf : TwoLegs → SysState → ConsDPh
consOf legBD s = SN.NodeStateD.cons-BD (nD s)
consOf legCD s = SN.NodeStateD.cons-CD (nD s)

-- `phOf` is the phase component of `consOf` (definitional)
phOf-consOf : (l : TwoLegs) (s : SysState) → phOf l s ≡ cph (consOf l s)
phOf-consOf legBD s = refl
phOf-consOf legCD s = refl

------------------------------------------------------------------------
-- THE INVARIANT.  Eight clauses along the leg's value chain, in flow order:
--
--   A's BF server → cell-l → relay's BF client → relay driver
--                 → relay's BF server → cell-lD → D's BF client → D's driver
------------------------------------------------------------------------

-- the per-leg block-VALUE invariant: every block anywhere on the leg is `blkA`
PipeVal : TwoLegs → SysState → Set
PipeVal l s =
    SrvValOK   (upSrv    l s)   -- (1) node A's sender holds `blkA`
  × CellValOK  (cellUp   l s)   -- (2) the upstream cell carries `blkA`
  × CliValOK   (upClient l s)   -- (3) the relay's receiver holds `blkA`
  × RelayValOK (relayOf  l s)   -- (4) the relay driver relays `blkA`
  × SrvValOK   (dnSrv    l s)   -- (5) the relay's sender holds `blkA`
  × CellValOK  (cellDn   l s)   -- (6) the downstream cell carries `blkA`
  × CliValOK   (dnClient l s)   -- (7) node D's receiver holds `blkA`
  × ConsDValOK (consOf   l s)   -- (8) node D's driver recorded `blkA`

------------------------------------------------------------------------
-- BASE.  At `initial` every peer is at its idle loop head, both cells are
-- `empty`, and the three driver slots sit at `cp0`/`pp0` with the `blkA`
-- placeholder — so every clause is `⊤` (or the placeholder's own `refl`).
------------------------------------------------------------------------

-- the invariant holds at the initial config, on both legs
pipeVal-init : (l : TwoLegs) → PipeVal l initial
pipeVal-init legBD = tt , tt , tt , tt , tt , tt , tt , tt
pipeVal-init legCD = tt , tt , tt , tt , tt , tt , tt , tt

------------------------------------------------------------------------
-- FRAME.  `PipeVal l` reads exactly eight components, so any transition that
-- leaves those eight fixed — the OTHER leg, the eight inert peers, the break
-- budget, the other-leg cells, every ChainSync position — preserves it by a
-- component-wise `subst`.  This is the leverage that isolates the real work to
-- the leg-`l` step cases (mirror of `PipeInv.pipeInv-frame`).
------------------------------------------------------------------------

-- component-wise transport of the value invariant
pipeVal-frame : (l : TwoLegs) (s s′ : SysState)
  → upSrv    l s ≡ upSrv    l s′ → cellUp   l s ≡ cellUp   l s′
  → upClient l s ≡ upClient l s′ → relayOf  l s ≡ relayOf  l s′
  → dnSrv    l s ≡ dnSrv    l s′ → cellDn   l s ≡ cellDn   l s′
  → dnClient l s ≡ dnClient l s′ → consOf   l s ≡ consOf   l s′
  → PipeVal l s → PipeVal l s′
pipeVal-frame l s s′ e1 e2 e3 e4 e5 e6 e7 e8 (h1 , h2 , h3 , h4 , h5 , h6 , h7 , h8) =
    subst SrvValOK   e1 h1 , subst CellValOK  e2 h2
  , subst CliValOK   e3 h3 , subst RelayValOK e4 h4
  , subst SrvValOK   e5 h5 , subst CellValOK  e6 h6
  , subst CliValOK   e7 h7 , subst ConsDValOK e8 h8

------------------------------------------------------------------------
-- THE CASH-OUTS.  Two shapes, so whichever tie-point the delivering-step
-- report ends up exposing is covered (the over-provisioning note above).
------------------------------------------------------------------------

-- (a) via node D's RECEIVER: the block D's BF client is offering on
--     `recvBFBlock` — this is the value the delivering api event carries,
--     because `bcBlk1 b` `!`-pins the api to `b` (`PipeValGate.cli-ablk-pins`)
pipeVal⇒client : (l : TwoLegs) (s : SysState) {b : Block₃}
               → PipeVal l s → dnClient l s ≡ bcBlk1 b → b ≡ blkA
pipeVal⇒client l s (_ , _ , _ , _ , _ , _ , h7 , _) eq = subst CliValOK eq h7

-- (b) via node D's DRIVER at the delivering successor: once the `cp3 → cp4`
--     hop has fired, the recorded block IS the fired value
--     (`PipeValGate.cons-cp3-rebind`), so the invariant at `s′` pins it
pipeVal⇒recorded : (l : TwoLegs) (s : SysState)
                 → PipeVal l s → phOf l s ≡ cp4 → cblk (consOf l s) ≡ blkA
pipeVal⇒recorded l s h8all eq = go l s (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ (proj₂ h8all))))))) eq
  where
  -- read the value clause off the slot once its phase is known to be `cp4`
  go : (l : TwoLegs) (s : SysState) → ConsDValOK (consOf l s)
     → phOf l s ≡ cp4 → cblk (consOf l s) ≡ blkA
  go legBD s h eq with SN.NodeStateD.cons-BD (nD s)
  go legBD s h refl | consD b .cp4 = h
  go legCD s h eq with SN.NodeStateD.cons-CD (nD s)
  go legCD s h refl | consD b .cp4 = h

------------------------------------------------------------------------
-- ANCHORING NOTE (the session-35 interface finding, recorded here because the
-- fix belongs to whoever builds the preservation).
--
-- `WalkDExpose.DReport`'s delivering constructors `dBD`/`dCD` produce
--
--     cph (cons-BD (nD s)) ≡ cp3
--       → Σ[ b″ ∈ Block₃ ] evLabel X e a ≡ evLabel Block₃ (apiBF linkBD hi recvBFBlock) b″
--
-- with `b″` EXISTENTIAL and tied to NOTHING in the state.  So neither cash-out
-- above can reach it: `PipeVal` pins `dnClient`/`consOf`, and `DReport` drops
-- the connection.  The `DReport` (and `WalkPr.DeliverSig`, which re-exports the
-- same `b″`) must be ANCHORED — one extra conjunct, either
--
--     dnClient c s ≡ bcBlk1 b″           (source-side: the client's held block)
--   or  cblk (cons-BD (nD s′)) ≡ b″       (target-side: the recorded block)
--
-- is enough, and both are already available where `dBD` is built (the api sync
-- pins the value on both sides).  This is exactly the "over-provision the
-- interface" lesson: the field was there for free and was dropped.
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — a MACHINE-CHECKED REFUTATION of `PipeInv.Coupled`'s two
-- CELL clauses (`Praos.PipeCellFalse`).
--
-- SESSION-28 FINDING.  `PipeInv.Coupled` reads
--
--     (CellNE    (cellUp   l s) → ProdSent (prodOf  l s))     -- (1)
--   × (BFcHasBlk (upClient l s) → ProdSent (prodOf  l s))     -- (2)
--   × (CellNE    (cellDn   l s) → RelayFwd (relayOf l s))     -- (3)
--   × (BFcHasBlk (dnClient l s) → RelayFwd (relayOf l s))     -- (4)
--
-- Clauses (1) and (3) are **FALSE** on the reachable state space, so
-- `PipeInv⁺ = PipeInv × Coupled` is NOT an invariant and the `FillSource`
-- obligation of `PipeStepEmit` (which is exactly the step-level content of (1)
-- and (3)) is NOT dischargeable — not by `PipeSrvInv.SrvCoupled`, and not by
-- anything else, because the statement is untrue.
--
-- REASON.  A leg cell is keyed only by `(link, dir, IDs)` — ONE copy cell per
-- link/direction/mini-protocol — so EVERY BlockFetch wire message on that
-- (link, dir) passes through the SAME cell, not just `MsgBlock`.  The producer
-- driver `decProd` fires `apiBF l hi sendBFStartBatch` at `pp4 → pp5`, which
-- drives node A's BF SERVER to its wire-send position, and the server then
-- performs the io `input l hi N2N_BlockFetch` carrying `MsgStartBatch`.  That
-- io FILLS `cellUp` while `prod-Al` is still `pp5` — and `ProdSent pp5 = ⊥`.
--
-- WORSE THAN "merely reachable": the BF server does NOT offer the api
-- `sendBFBlock` at the wire-send position (`bfSnxt … bsWsb (apiBF … sendBFBlock)
-- ≡ nothing`), so the producer at `pp5` is BLOCKED until the `MsgStartBatch`
-- io fill has happened.  The violating configuration therefore lies on EVERY
-- run that ever delivers a block — i.e. on every run the liveness theorem is
-- about.
--
-- The four facts below are each `refl` (or a two-line `subst`) on the R2
-- abstract BF-server table `NodeSpecs.bfSnxt` and on `PipeInv`'s own phase
-- logic.  Nothing here depends on the reachability relation.
--
-- THE FIX (APPLIED in `PipeInv` by session 28): clauses (1) and (3) are
-- PAYLOAD-REFINED — `CellNE` (cell non-empty) must become "the cell holds a
-- BlockFetch `MsgBlock`".  Under that refinement a `MsgStartBatch` fill is
-- vacuous, a `MsgBlock` fill forces the server to `bsBlk1` (whence
-- `PipeSrvInv.SrvCoupled` supplies `ProdSent`), and the drain cores keep
-- working because a client only enters `bcBlk1` by reading a `MsgBlock`.
--
-- Imported by nothing.  No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Maybe using ( Maybe; just; nothing )
open import Data.Product using ( _×_; _,_ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
import Data.Unit as U
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeCellFalse (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; linkAB )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Block; time₀; length₀ )
open import CSP.Examples.Cardano_network.Base
  using ( hi; N2N_BlockFetch; FromResponder )
open import CSP.Examples.Cardano_network.Data p
  using ( Payload; Messages; blockFetch; MsgStartBatch )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; input; apiBF; sendBFStartBatch; sendBFBlock )

import CSP.Examples.Cardano_network.NetworkVerification.Praos.NodeSpecs blkA as NS
open NS using ( bfSnxt; bsBusy; bsWsb; bsStream )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( CopyPhase; empty; full; draining )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA
  using ( BFsPos; bsStart1; pp5 )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
  using ( coarsenBFs )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( legBD )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeInv blkA
  using ( PipeInv⁺; cellUp; prodOf; CellHasBlk; ProdSent )

------------------------------------------------------------------------
-- The offending wire payload: the `MsgStartBatch` node A's BF server writes
-- into leg-`legBD`'s UPSTREAM cell `(linkAB, hi, N2N_BlockFetch)` = `cellUp`.
------------------------------------------------------------------------

-- the BlockFetch `MsgStartBatch` wire payload of the (AB, hi) responder
sbPayload : Payload
sbPayload = time₀ , FromResponder , length₀ , blockFetch MsgStartBatch

------------------------------------------------------------------------
-- (a) The producer driver's `pp4 → pp5` api event (`sendBFStartBatch`) puts
--     node A's BF server at the concrete wire-send position `bsStart1`, whose
--     abstract coarsening is `bsWsb`.
------------------------------------------------------------------------

-- the api `sendBFStartBatch` edge of the abstract BF server: `bsBusy → bsWsb`
srv-api-startBatch :
  bfSnxt linkAB hi bsBusy (_ , apiBF linkAB hi sendBFStartBatch) U.tt ≡ just bsWsb
srv-api-startBatch = refl

-- the concrete `bsStart1` IS the abstract wire-send position `bsWsb`
bsStart1-coarse : coarsenBFs bsStart1 ≡ bsWsb
bsStart1-coarse = refl

------------------------------------------------------------------------
-- (b) At that wire-send position the server FILLS the cell with a payload that
--     is NOT a block — the io `input (AB, hi, N2N_BlockFetch) ! MsgStartBatch`.
------------------------------------------------------------------------

-- the abstract BF server at `bsWsb` fires the cell-FILLING io with `MsgStartBatch`
srv-io-fills-with-startBatch :
  bfSnxt linkAB hi bsWsb (_ , input linkAB hi N2N_BlockFetch) sbPayload ≡ just bsStream
srv-io-fills-with-startBatch = refl

------------------------------------------------------------------------
-- (c) The fill is UNAVOIDABLE: at `bsWsb` the server offers NO api
--     `sendBFBlock`, so the producer driver stuck at `pp5` cannot advance to
--     `pp6` (`ProdSent`) until the `MsgStartBatch` io fill above has fired.
------------------------------------------------------------------------

-- the abstract BF server at `bsWsb` does NOT offer the api `sendBFBlock`
srv-no-sendBlock-at-wsb : (b : Block)
  → bfSnxt linkAB hi bsWsb (_ , apiBF linkAB hi sendBFBlock) b ≡ nothing
srv-no-sendBlock-at-wsb b = refl

------------------------------------------------------------------------
-- (d) THE REFUTATION, against the SUPERSEDED predicate.  `CellNE-old` is the
--     session-≤27 `PipeInv.CellNE` (mere non-emptiness) reproduced verbatim, so
--     the refutation stays checkable after the fix landed in `PipeInv`.  Any
--     state whose leg-`legBD` upstream cell holds the `MsgStartBatch` payload
--     while the producer is still at `pp5` falsifies the OLD first coupling
--     clause; by (a)-(c) every block-delivering run passes through such a state.
------------------------------------------------------------------------

-- the SUPERSEDED cell predicate: a copy cell is merely non-empty
CellNE-old : CopyPhase → Set
CellNE-old empty        = ⊥
CellNE-old (full _)     = ⊤
CellNE-old (draining _) = ⊤

-- the SUPERSEDED first coupling clause of `PipeInv.Coupled`
Coupled₁-old : SysState → Set
Coupled₁-old s = CellNE-old (cellUp legBD s) → ProdSent (prodOf legBD s)

-- the `MsgStartBatch` fill at producer phase `pp5` REFUTES the old clause
coupled₁-old-⊥ : (s : SysState)
  → cellUp legBD s ≡ full sbPayload
  → prodOf legBD s ≡ pp5
  → Coupled₁-old s → ⊥
coupled₁-old-⊥ s ceq peq cu = subst ProdSent peq (cu (subst CellNE-old (sym ceq) tt))

------------------------------------------------------------------------
-- (e) THE FIX, checked.  `PipeInv.CellHasBlk` — the payload-refined antecedent
--     now in force — is uninhabited at the `MsgStartBatch` fill, so the
--     corrected clause is vacuous exactly where the old one was false.
------------------------------------------------------------------------

-- the refined antecedent does NOT fire on a `MsgStartBatch` fill
cellHasBlk-startBatch-⊥ : CellHasBlk (full sbPayload) → ⊥
cellHasBlk-startBatch-⊥ ()

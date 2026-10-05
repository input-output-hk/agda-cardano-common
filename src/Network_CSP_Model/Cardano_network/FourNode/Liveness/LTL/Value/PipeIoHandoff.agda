{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the FOUR hidden-io HAND-OFF `PipeInv⁺`-preservation
-- cores (`Praos.PipeIoHandoff`).
--
-- SESSION-15 FINDING (the `stepEmit` interface gap, evidence-backed).  A walk
-- step is a WEAK visible move `radec r ═[ ev l ]═► t′ = wev (τ*) (visible)
-- (τ*)` with ARBITRARY τ* padding on BOTH sides (`Semantics.WeakBisim.wev`).
-- The three leg-`l` DRIVER phases (prod / relay / cons) are τ-STABLE — they
-- move only on the visible api-CSBF middle (`top-nodes-abs-expose` keeps the
-- medium FIXED on the visible node step, and the τ-reflectors keep the drivers
-- `pcFix`/`rcFix`/`DFix`).  But the FOUR leg-`l` cell/client components
-- (`cellUp`/`cellDn`/`upClient`/`dnClient`) are τ-MOBILE: the medium copy cells
-- fill/drain and the BF client peers advance on the HIDDEN io τ's that pad every
-- weak move (`PipeClassCell.cell-{drain,fill}-class`, `PipeNodeFix`'s
-- `clAdv (adv-of …)`).
--
-- NONE of the eight `PipeStep⁺` ctors covers a step that keeps the drivers
-- FIXED yet moves a cell/client: they either fix ALL SEVEN components
-- (`psFrame`) or free a cell/client only ALONGSIDE a specific driver ADVANCE
-- (`psProdSend` frees `cellUp`/`upClient`; `psRelayFwd` frees
-- `cellDn`/`dnClient`).  So a weak move whose τ-padding performs a pure io
-- hand-off (with no co-driver advance) has no matching single ctor.
--
-- These FOUR cores discharge exactly those hidden-io hand-offs as
-- `PipeInv⁺`-preserving transitions (drivers fixed, one cell/client moves),
-- using the `Coupled` component of the INPUT `PipeInv⁺ s` PLUS the io-SOURCE
-- fact each hand-off carries (a FILL fires only from a SENT producer /
-- FORWARDED relay; a DRAIN reads a NON-EMPTY cell).  They are the SOUND half of
-- the interface fix the session-15 report describes.  Pure phase logic,
-- importing only the LIGHT `PipeInv` (no oracle).  No postulate/hole/meta.
------------------------------------------------------------------------

open import Data.Product using ( _,_ )
open import Data.Empty using ( ⊥-elim )
open import Relation.Binary.PropositionalEquality using ( _≡_; subst )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeIoHandoff (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( empty )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; phOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf; relayOf; cellUp; cellDn; upClient; dnClient
        ; CellHasBlk; BFcHasBlk; ProdSent; RelayFwd
        ; PipeInv⁺; pipeInv-frame; transImp )

------------------------------------------------------------------------
-- (1) UPSTREAM cell FILL — node-A's BF server writes `cell-l` (`cellUp`
-- advances empty → full).  Everything else fixed.  The server only outputs the
-- block AFTER the producer has fired `sendBFBlock`, so the fill carries the
-- io-source fact `ProdSent (prodOf l s)`; the two upstream `Coupled` clauses
-- then hold outright and the two downstream ones transport (relay fixed).
------------------------------------------------------------------------
pipeInv⁺-up-fill : (l : TwoLegs) (s s′ : SysState)
  → prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
  → phOf     l s ≡ phOf     l s′
  → cellDn   l s ≡ cellDn   l s′ → upClient l s ≡ upClient l s′
  → dnClient l s ≡ dnClient l s′
  → ProdSent (prodOf l s)              -- io-source: the fill came from a sent producer
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-up-fill l s s′ pe re ce cde ue de hSent (pinv , cu , uc , cd , dc)
  = pipeInv-frame l s s′ pe re ce pinv
  , (λ _ → subst ProdSent pe hSent)
  , (λ _ → subst ProdSent pe hSent)
  , transImp CellHasBlk    RelayFwd cde re cd
  , transImp BFcHasBlk RelayFwd de  re dc

------------------------------------------------------------------------
-- (2) UPSTREAM cell DRAIN — the relay's BF client reads `cell-l` (`cellUp`
-- drains AND `upClient` advances to `bcBlk1`, holding the block).  Everything
-- else fixed.  A drain reads a NON-EMPTY cell (`hNE`), so by the INPUT coupling
-- `cu` the producer had already SENT — which re-establishes both upstream
-- clauses (`cellUp` now empty / `upClient` now holding, both coupled to sent).
------------------------------------------------------------------------
pipeInv⁺-up-drain : (l : TwoLegs) (s s′ : SysState)
  → prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
  → phOf     l s ≡ phOf     l s′
  → cellDn   l s ≡ cellDn   l s′ → dnClient l s ≡ dnClient l s′
  → CellHasBlk (cellUp l s)                -- io-source: the drain reads a non-empty cell
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-up-drain l s s′ pe re ce cde de hNE (pinv , cu , uc , cd , dc)
  = pipeInv-frame l s s′ pe re ce pinv
  , (λ _ → subst ProdSent pe (cu hNE))
  , (λ _ → subst ProdSent pe (cu hNE))
  , transImp CellHasBlk    RelayFwd cde re cd
  , transImp BFcHasBlk RelayFwd de  re dc

------------------------------------------------------------------------
-- (3) DOWNSTREAM cell FILL — the relay's BF server writes `cell-lD` (`cellDn`
-- advances empty → full).  Everything else fixed.  The relay only outputs the
-- block AFTER it has forwarded (`sendBFBlock` onward), so the fill carries
-- `RelayFwd (relayOf l s)`; the two downstream clauses hold outright and the
-- two upstream ones transport (producer fixed).
------------------------------------------------------------------------
pipeInv⁺-dn-fill : (l : TwoLegs) (s s′ : SysState)
  → prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
  → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → upClient l s ≡ upClient l s′
  → dnClient l s ≡ dnClient l s′
  → RelayFwd (relayOf l s)             -- io-source: the fill came from a forwarded relay
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-dn-fill l s s′ pe re ce cue ue de hFwd (pinv , cu , uc , cd , dc)
  = pipeInv-frame l s s′ pe re ce pinv
  , transImp CellHasBlk    ProdSent cue pe cu
  , transImp BFcHasBlk ProdSent ue  pe uc
  , (λ _ → subst RelayFwd re hFwd)
  , (λ _ → subst RelayFwd re hFwd)

------------------------------------------------------------------------
-- (4) DOWNSTREAM cell DRAIN — nodeD's BF client reads `cell-lD` (`cellDn`
-- drains AND `dnClient` advances to `bcBlk1`).  Everything else fixed.  A drain
-- reads a NON-EMPTY cell, so by the INPUT coupling `cd` the relay had already
-- FORWARDED — re-establishing both downstream clauses.
------------------------------------------------------------------------
pipeInv⁺-dn-drain : (l : TwoLegs) (s s′ : SysState)
  → prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
  → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → upClient l s ≡ upClient l s′
  → CellHasBlk (cellDn l s)                -- io-source: the drain reads a non-empty cell
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-dn-drain l s s′ pe re ce cue ue hNE (pinv , cu , uc , cd , dc)
  = pipeInv-frame l s s′ pe re ce pinv
  , transImp CellHasBlk    ProdSent cue pe cu
  , transImp BFcHasBlk ProdSent ue  pe uc
  , (λ _ → subst RelayFwd re (cd hNE))
  , (λ _ → subst RelayFwd re (cd hNE))

------------------------------------------------------------------------
-- (5) UPSTREAM cell autonomous DRAIN-TO-EMPTY — a medium-τ step flips a
-- `draining` `cell-l` to `empty` (`flipCell`, no node moves).  Everything else
-- fixed (drivers, both clients, the downstream cell).  No io-source is needed:
-- the emptied upstream cell makes its coupling clause VACUOUS (`CellHasBlk empty`
-- is uninhabited); the other three clauses transport across the fixed drivers.
------------------------------------------------------------------------
pipeInv⁺-up-empty : (l : TwoLegs) (s s′ : SysState)
  → prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
  → phOf     l s ≡ phOf     l s′
  → cellDn   l s ≡ cellDn   l s′ → upClient l s ≡ upClient l s′
  → dnClient l s ≡ dnClient l s′
  → cellUp l s′ ≡ empty                -- the medium-τ drained the upstream cell empty
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-up-empty l s s′ pe re ce cde ue de cuz (pinv , cu , uc , cd , dc)
  = pipeInv-frame l s s′ pe re ce pinv
  , (λ h → ⊥-elim (subst CellHasBlk cuz h))
  , transImp BFcHasBlk ProdSent ue pe uc
  , transImp CellHasBlk    RelayFwd cde re cd
  , transImp BFcHasBlk RelayFwd de  re dc

------------------------------------------------------------------------
-- (6) DOWNSTREAM cell autonomous DRAIN-TO-EMPTY — the mirror of (5) for
-- `cell-lD`: a medium-τ step flips a `draining` downstream cell to `empty`,
-- everything else fixed.  The emptied downstream cell's clause is vacuous.
------------------------------------------------------------------------
pipeInv⁺-dn-empty : (l : TwoLegs) (s s′ : SysState)
  → prodOf   l s ≡ prodOf   l s′ → relayOf  l s ≡ relayOf  l s′
  → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → upClient l s ≡ upClient l s′
  → dnClient l s ≡ dnClient l s′
  → cellDn l s′ ≡ empty                -- the medium-τ drained the downstream cell empty
  → PipeInv⁺ l s → PipeInv⁺ l s′
pipeInv⁺-dn-empty l s s′ pe re ce cue ue de cdz (pinv , cu , uc , cd , dc)
  = pipeInv-frame l s s′ pe re ce pinv
  , transImp CellHasBlk    ProdSent cue pe cu
  , transImp BFcHasBlk ProdSent ue  pe uc
  , (λ h → ⊥-elim (subst CellHasBlk cdz h))
  , transImp BFcHasBlk RelayFwd de  re dc

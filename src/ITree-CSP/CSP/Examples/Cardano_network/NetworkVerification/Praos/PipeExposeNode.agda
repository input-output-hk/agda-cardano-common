{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the NODE per-peer BF-CLIENT phase-advance exposure leaf
-- (`Praos.PipeExposeNode`).
--
-- The MEDIUM analogue (`PipeExposeCell`) exposes, across a hidden τ-run, how the
-- leg cells move (`AllCellAdv`, from `medium-ev-inv-wt`'s `setCell` form).  The
-- NODE side needs the counterpart: how a leg's BF-CLIENT peer phase (`bfC-l`, a
-- `BFcPos`) advances across the same io-sync paddings — in particular the FILL
-- transition `bcHead stStreaming --receiveBF (MsgBlock b)--> bcBlk1 b` that lands
-- the block in the client (`BFcHasBlk`, the delivery gate the `PipeInv⁺` coupling
-- reads).
--
-- This is the FIRST piece of that: the phase-class leaf `client-io-adv`.  It is
-- the exact BF-client analogue of `PipeExposeCell.cell-fill-read` — it reuses the
-- FROZEN io-drop leaf `WalkConvIoDrop.decBFc-ev-io-drop` (which already returns
-- the CONCRETE successor phase `pos′` — e.g. `bcBlk1 b` on the fill) and attaches
-- a `ClientAdv` advance record classifying whether the io delivered the block
-- (`cGetBlk`) or made another move (`cAdv`).  Because `decBFc-ev-io-drop` already
-- hands back `pos′` concretely, the client phase is NOT buried — this leaf is
-- LIGHT (it pulls only the io-drop leaf, not the node dispatch cone).
--
-- `ClientAdv` is the reflexive-transitive closure of a single io move `Client1`,
-- so it composes across a τ-run exactly like `PipeExposeCell.CellAdv`.  No
-- postulate/hole/meta.  All base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_ )
open import Relation.Binary.PropositionalEquality using ( _≡_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.PipeExposeNode (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir )
import CSP.Examples.Cardano_network.BlockFetch p as BF
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιBF )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using ( EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_ )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA
  using ( BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil; decBFc )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
  using ( NetProc; absBFc )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkConvIoDrop blkA
  using ( decBFc-ev-io-drop )

------------------------------------------------------------------------
-- The BF-client phase-advance algebra.  `Client1` is one legal single io move
-- of a client peer: either it delivered a block (landing `bcBlk1 b` — the
-- `BFcHasBlk` gate), or it made some other io advance (`cAdv`, target read
-- separately from the reflected state).  `ClientAdv` is its reflexive-transitive
-- closure, so a whole hidden io-run composes (mirror `PipeExposeCell.CellAdv`).
------------------------------------------------------------------------

-- one legal client io transition (target-classified: block-gain vs other move)
data Client1 : BFcPos → BFcPos → Set where
  cGetBlk : ∀ {q b}  → Client1 q (bcBlk1 b)   -- io landed the block (bcBlk1)
  cAdv    : ∀ {q q′} → Client1 q q′            -- some other io move

-- the reflexive-transitive closure: a client peer's phase across a whole io-run
data ClientAdv : BFcPos → BFcPos → Set where
  cl-refl : ∀ {q}     → ClientAdv q q
  cl-step : ∀ {q r s} → Client1 q r → ClientAdv r s → ClientAdv q s

-- `ClientAdv` composes (transitive), so it threads across a τ-run
cl-trans : ∀ {q r s} → ClientAdv q r → ClientAdv r s → ClientAdv q s
cl-trans cl-refl          g = g
cl-trans (cl-step x rest) g = cl-step x (cl-trans rest g)

------------------------------------------------------------------------
-- The pure classify: any concrete successor phase yields a one-step `ClientAdv`
-- (the block-delivery target `bcBlk1` is flagged as `cGetBlk`; every other move
-- is `cAdv`).  This is total on the successor and needs no weight bookkeeping —
-- unlike the cell, the BF-client weight does NOT determine the phase class
-- (`bcBlk1` shares weight 0 with several non-block phases), so the exposure
-- reads the CONCRETE successor `pos′` that `decBFc-ev-io-drop` already returns.
------------------------------------------------------------------------

-- one io move as a `ClientAdv`, classified by the concrete successor phase
adv-of : (q q′ : BFcPos) → ClientAdv q q′
adv-of q (bcHead st) = cl-step cAdv cl-refl
adv-of q (bcReq1 r)  = cl-step cAdv cl-refl
adv-of q bcDone1     = cl-step cAdv cl-refl
adv-of q (bcBlk1 b)  = cl-step cGetBlk cl-refl
adv-of q (bcSil st)  = cl-step cAdv cl-refl

------------------------------------------------------------------------
-- The BF-client phase-class leaf (`client-io-adv`): STRENGTHENS the frozen
-- io-drop leaf `decBFc-ev-io-drop` to ALSO expose the client's `ClientAdv`
-- advance.  Exact analogue of `PipeExposeCell.cell-fill-read` (which turns the
-- medium inversion's `setCell` into a `CellAdv`).  Reuses the frozen leaf's
-- concrete successor `pos′`, weak step, and `M ≡ absBFc` equation verbatim; the
-- discarded weight-drop field is replaced by the phase-class advance.
------------------------------------------------------------------------

-- an io-sync at a BF-client peer at phase `pos` reaches a concrete successor
-- `pos′` with an exposed `ClientAdv pos pos′` (block-gain flagged)
client-io-adv : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιBF e₁) a
  → absBFc l d pos ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M
  → Σ[ pos′ ∈ BFcPos ] (decBFc l d pos ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFc l d pos′)
      × (M ≡ absBFc l d pos′)
      × ClientAdv pos pos′
client-io-adv l d pos iomem step with decBFc-ev-io-drop l d pos iomem step
... | pos′ , stp , meq , _ = pos′ , stp , meq , adv-of pos pos′

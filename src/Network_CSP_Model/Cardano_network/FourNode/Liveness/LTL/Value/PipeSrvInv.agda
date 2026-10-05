{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the per-leg SERVER-COUPLING invariant
-- (`Praos.PipeSrvInv`), the `FillSource` substrate.
--
-- Session-26 finding: `FillSource`'s FILL case (`cellUp empty→full ⇒
-- ProdSent`) is NOT per-step enabledness — the io-fill fire pins the BF
-- SERVER to `bsBlk1`, but "server holds ⇒ producer sent" is itself a
-- reachability invariant, and `PipeInv⁺`'s `Coupled` covers cells + CLIENTS
-- only.  THIS leaf states the missing SERVER coupling, threaded BESIDE
-- `PipeInv⁺` (never editing `PipeInv`):
--
--   `SrvCoupled l s` =  upstream  BF server holds ⇒ producer has SENT
--                    ×  downstream BF server holds ⇒ relay has FORWARDED
--
-- (upstream server = node A's `bfS-AB`/`bfS-AC`; downstream = node B's
-- `bfS-BD` / node C's `bfS-CD` — the senders that FILL the leg's two cells).
-- A server ENTERS `bsBlk1` only via the api `sendBFBlock` fire, which is the
-- SAME api sync as the co-firing driver's `a56` (producer `pp5→pp6` /
-- relay-produce `pp5→pp6`) — so on the entering step the coupling consequent
-- becomes true SIMULTANEOUSLY.  `PipeBundleEvo.BfsSucc` carries exactly this
-- (¬-block, or entered-`bsBlk1`-via-`sendBFBlock` with the label pin).
--
-- This module is the pure PHASE-LOGIC side: the invariant, its base/frame,
-- the two monotone maps, and the three-arm preservation cores the future
-- server-aware peel (`NodeADrv` re-mirror + `LegDriverStep` extension) will
-- feed.  No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( _×_; _,_ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Unit.Polymorphic using ( tt )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial; nA; nB; nC )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( BFsPos )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ProdAdv; a01; a12; a23; a34; a45; a56; a67; a78; a89 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf; relayOf; ProdSent; RelayFwd; relayPre-fwd-⊥ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriver blkA
  using ( RelayStepKind; rMove; rFwd; rRecv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )

------------------------------------------------------------------------
-- Per-leg BF SERVER accessors: the senders that fill the leg's two cells.
------------------------------------------------------------------------

-- the leg's UPSTREAM BF server (node A's sender filling `cell-l`)
upSrv : TwoLegs → SysState → BFsPos
upSrv legBD s = SN.NodeStateA.bfS-AB (nA s)
upSrv legCD s = SN.NodeStateA.bfS-AC (nA s)

-- the leg's DOWNSTREAM BF server (the relay node's sender filling `cell-lD`)
dnSrv : TwoLegs → SysState → BFsPos
dnSrv legBD s = SN.NodeStateB.bfS-BD (nB s)
dnSrv legCD s = SN.NodeStateC.bfS-CD (nC s)

------------------------------------------------------------------------
-- The SERVER coupling: a holding upstream server forces the producer SENT;
-- a holding downstream server forces the relay FORWARDED.
------------------------------------------------------------------------

-- the per-leg server-coupling invariant (threaded BESIDE `PipeInv⁺`)
SrvCoupled : TwoLegs → SysState → Set
SrvCoupled l s =
    (BFsHasBlk (upSrv l s) → ProdSent (prodOf  l s))
  × (BFsHasBlk (dnSrv l s) → RelayFwd (relayOf l s))

-- BASE — at `initial` every BF server sits at its idle head (¬-block), so
-- both antecedents are uninhabited
srvCoupled-init : (l : TwoLegs) → SrvCoupled l initial
srvCoupled-init legBD = (λ ()) , (λ ())
srvCoupled-init legCD = (λ ()) , (λ ())

-- FRAME — all four read components fixed carries the coupling across
srvCoupled-frame : (l : TwoLegs) (s s′ : SysState)
  → prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′
  → upSrv  l s ≡ upSrv  l s′ → dnSrv   l s ≡ dnSrv   l s′
  → SrvCoupled l s → SrvCoupled l s′
srvCoupled-frame l s s′ pe re ue de (uc , dc) =
    (λ h → subst ProdSent pe (uc (subst BFsHasBlk (sym ue) h)))
  , (λ h → subst RelayFwd re (dc (subst BFsHasBlk (sym de) h)))

------------------------------------------------------------------------
-- Monotonicity of the two consequents along the genuine driver advances:
-- a producer never un-sends, a relay never un-forwards.
------------------------------------------------------------------------

-- `ProdSent` is monotone along a single producer adjacency
padv-sent-mono : ∀ {a b} → ProdAdv a b → ProdSent a → ProdSent b
padv-sent-mono a01 ()
padv-sent-mono a12 ()
padv-sent-mono a23 ()
padv-sent-mono a34 ()
padv-sent-mono a45 ()
padv-sent-mono a56 _ = tt
padv-sent-mono a67 _ = tt
padv-sent-mono a78 _ = tt
padv-sent-mono a89 _ = tt

-- `RelayFwd` is monotone along a single relay step kind (a receive starts
-- from `RelayPre`, which excludes `RelayFwd`)
rk-fwd-mono : ∀ {a b} → RelayStepKind a b → RelayFwd a → RelayFwd b
rk-fwd-mono (rMove _ _ fF _)  = fF
rk-fwd-mono (rFwd _ hFwd _)   = λ _ → hFwd
rk-fwd-mono (rRecv hPre _)    = λ hF → ⊥-elim (relayPre-fwd-⊥ _ hPre hF)

------------------------------------------------------------------------
-- The three-arm PRESERVATION cores.  The server-aware peel supplies, per
-- visible step, the server EVOLUTION in the maximal three-arm form
--
--   fixed  ⊎  ¬-holding successor  ⊎  consequent-already-true at s′
--
-- (the third arm is what the peel derives from `PipeBundleEvo.BfsSucc`'s
-- entered-`bsBlk1` label pin: the co-firing driver's `sendBFBlock` IS the
-- `a56` crossing, so `ProdSent`/`RelayFwd` holds at s′ outright).
------------------------------------------------------------------------

-- the maximal upstream-server evolution witness across one step
UpSrvEvo : TwoLegs → SysState → SysState → Set
UpSrvEvo l s s′ =
  (upSrv l s ≡ upSrv l s′) ⊎ ((BFsHasBlk (upSrv l s′) → ⊥) ⊎ ProdSent (prodOf l s′))

-- the maximal downstream-server evolution witness across one step
DnSrvEvo : TwoLegs → SysState → SysState → Set
DnSrvEvo l s s′ =
  (dnSrv l s ≡ dnSrv l s′) ⊎ ((BFsHasBlk (dnSrv l s′) → ⊥) ⊎ RelayFwd (relayOf l s′))

-- preservation of the upstream clause: consequent-monotone map + evolution
srv-pres-up : (l : TwoLegs) (s s′ : SysState)
  → (ProdSent (prodOf l s) → ProdSent (prodOf l s′))
  → UpSrvEvo l s s′
  → (BFsHasBlk (upSrv l s) → ProdSent (prodOf l s))
  → BFsHasBlk (upSrv l s′) → ProdSent (prodOf l s′)
srv-pres-up l s s′ mono (inj₁ eq)          uc h = mono (uc (subst BFsHasBlk (sym eq) h))
srv-pres-up l s s′ mono (inj₂ (inj₁ ¬blk)) uc h = ⊥-elim (¬blk h)
srv-pres-up l s s′ mono (inj₂ (inj₂ sent)) uc h = sent

-- preservation of the downstream clause
srv-pres-dn : (l : TwoLegs) (s s′ : SysState)
  → (RelayFwd (relayOf l s) → RelayFwd (relayOf l s′))
  → DnSrvEvo l s s′
  → (BFsHasBlk (dnSrv l s) → RelayFwd (relayOf l s))
  → BFsHasBlk (dnSrv l s′) → RelayFwd (relayOf l s′)
srv-pres-dn l s s′ mono (inj₁ eq)          dc h = mono (dc (subst BFsHasBlk (sym eq) h))
srv-pres-dn l s s′ mono (inj₂ (inj₁ ¬blk)) dc h = ⊥-elim (¬blk h)
srv-pres-dn l s s′ mono (inj₂ (inj₂ fwd))  dc h = fwd

-- whole-coupling preservation: both consequent-monotone maps + both evolutions
srvCoupled-pres : (l : TwoLegs) (s s′ : SysState)
  → (ProdSent (prodOf l s) → ProdSent (prodOf l s′))
  → (RelayFwd (relayOf l s) → RelayFwd (relayOf l s′))
  → UpSrvEvo l s s′ → DnSrvEvo l s s′
  → SrvCoupled l s → SrvCoupled l s′
srvCoupled-pres l s s′ pmono rmono ue de (uc , dc) =
    srv-pres-up l s s′ pmono ue uc
  , srv-pres-dn l s s′ rmono de dc

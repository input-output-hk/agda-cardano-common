{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — `locate`: the START reachability of the delivery walk
-- (`Praos.WalkLocate`).
--
-- `WalkEngine.walkPosFrom`'s `locate` parameter turns a `producedA b` frame at
-- position `n` of a `WTrace` of `abstractSystem` into a REACHABLE `Pr`-config:
--
--   locate : (b) (tr) (n) → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
--          → Σ[ r0 ∈ RState ] (dropIdx n tr ≡ radec r0) × Pr b r0
--
-- It has TWO halves:
--
--   (1) REACHABILITY — `WalkCausal.walkReach′` walks the `n`-step prefix from
--       `rinit` (`abstractSystem ≡ radec rinit`, `radec-init`) and certifies
--       `dropIdx n tr ≡ radec r0` for a reachable `r0`.  This half is BUILT
--       and green (enabledness-free; the `√`/terminal frames are handled by
--       the `producedA` hypothesis + `drop`-stuttering, see `WalkCausal`).
--
--   (2) The PENDING CAUSAL CONE — from the `producedA b` frame at the reachable
--       `r0` (node A still OFFERING `apiBF (linkAB|linkAC) hi sendBFBlock`, i.e.
--       the block NOT yet handed to the BF pipeline) conclude the corresponding
--       D-consumer leg is pre-`recvBFBlock` (`InCp03`), i.e. `Pr b r0`.  This is
--       the PER-LEG PROVENANCE invariant: `cons-lD` reaches `cp4` ONLY AFTER
--       `prod-Al` fired `sendBFBlock` (`cp3→cp4` needs `recvBFBlock ⇐` block in
--       `cell-lD ⇐` relay sent `⇐` relay received `⇐` `prod-Al` fired).  It is a
--       MULTI-COMPONENT pipeline reachability invariant over the FUNCTION-typed
--       medium (`prod-Al → cell-l → relay(B/C) → cell-lD → cons-lD`); its
--       inductive proof over `Reachable` must decode the transition system per
--       pipeline component (oracle-scale, no existing harvest).  It is therefore
--       taken here as the MODULE PREMISE `pcone` — exactly as `WalkDeliver`
--       takes the weak-progress premise `wprog` — isolating it as the single
--       remaining R3 obligation while keeping `locate` green, 0-postulate, and
--       matching `walkPosFrom`'s parameter type EXACTLY.
--
-- No postulate/hole/meta.  `wprog` is NOT used here.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Nat using ( ℕ )
open import Data.Product using ( Σ; Σ-syntax; _,_; _×_ )
open import Relation.Binary.PropositionalEquality using ( _≡_; sym )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkLocate (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p; Block₃ )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysReach blkA
  using ( NetProc; RState; radec; toSys; rinit; radec-init )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.AbstractSystem blkA
  using ( abstractSystem )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkPr blkA
  using ( Pr )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.WalkCausal blkA
  using ( walkReach′ )

open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( LTLᵗ; atom )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; ⟦_⟧ᵂ; drop; dropIdx; frameOf )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondLiveness
  using ( producedA )

------------------------------------------------------------------------
-- The PENDING CAUSAL CONE premise (half (2)): a `producedA b` frame at a
-- reachable config `r0` witnesses that `r0` is a PENDING config (`Pr b r0` =
-- SOME D-consumer leg is pre-`recvBFBlock`).  Stated in the generalised
-- start-equality form (matching `WalkCausal.walkReach′`) so it applies to
-- `drop n tr` at `dropIdx n tr ≡ radec r0` with NO transport.
------------------------------------------------------------------------

module _
  (pcone : (b : Block₃) (r0 : RState) {t : NetProc} (w : WTrace (⊤ {0ℓ}) t)
         → t ≡ radec r0 → producedA b (frameOf w) → Pr b r0)
  where

  ------------------------------------------------------------------------
  -- `locate` — the reachability walk composed with the pending cone.  Matches
  -- `WalkEngine.walkPosFrom`'s `locate` parameter type EXACTLY.
  ------------------------------------------------------------------------

  locate : (b : Block₃) (tr : WTrace (⊤ {0ℓ}) abstractSystem) (n : ℕ)
         → ⟦ atom (producedA b) ⟧ᵂ (drop n tr)
         → Σ[ r0 ∈ RState ] (dropIdx n tr ≡ radec r0) × Pr b r0
  locate b tr n prod with walkReach′ b rinit (sym radec-init) tr n prod
  ... | r0 , eq0 = r0 , eq0 , pcone b r0 (drop n tr) eq0 prod

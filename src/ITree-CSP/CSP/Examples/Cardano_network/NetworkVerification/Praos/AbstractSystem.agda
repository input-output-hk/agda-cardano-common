{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 — `abstractSystem` target (`Praos.AbstractSystem`).
--
-- `abstractSystem` is the RHS of the R2 divergence-respecting bisimulation
--   `systemBroken ≈DR abstractSystem`
-- (`systemBroken` = `⟦ initial ⟧` from `Praos.SysDecode`, the R1 LHS).  It is
-- the four-node broken system with each node replaced by its τ-free ≈DR
-- table-spec, the breakable medium and the io-gated skeleton kept verbatim:
--
--   abstractSystem =
--     (CopySpecBreakableA ∥⇘ ioES ⇙
--        (nodeASpec ⦀ (nodeBSpec ⦀ (nodeCSpec ⦀ nodeDSpec)))) ∖ ioES
--
--   where the four `nodeXSpec` come from `Praos.NodeSpecs` (rebuilt IN THE
--   PRAOS NAMESPACE from the τ-free `specBundle`/`specBundleFlip` table
--   specs).  R2 REBUILDS these here rather than re-exporting the concrete
--   `Liveness.System.abstractSystem`: importing the route-1 node modules
--   transitively rebuilds the heavy `PipePairPeers*` ≈DR proof modules
--   (>480 s / timed out) — SLOW, not red — so the τ-free node specs were
--   copied into `Praos.NodeSpecs` (see that module's header for sources).
--
--   Each `nodeXSpec` is the 8-PEER (KA/CS/BF/TS client+server) τ-free table
--   spec.  The two inert non-Praos peers per direction (LN/LF) are api-gated
--   by drivers that never offer their api events, hence observationally
--   inert and correctly ABSENT from the abstraction (no LN/LF factor added).
--
-- The `⦀`/`∥⇘ ioES ⇙`/`∖ ioES` skeleton MATCHES `Praos.SysDecode.⟦_⟧`
-- (SysDecode:85-90) and `systemBroken` exactly, including the node `⦀`
-- association `nodeA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD))` — so Task 5's dec-init
-- rewrite (`⟦ initial ⟧ ≡ systemBroken`) reconciles with this RHS shape.
--
-- No postulates, holes, or `--allow-unsolved-metas`.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using (p)
open import CSP.Examples.Cardano_network.Net p using (Net_Api; Net_Api-≟)
open import CSP.Examples.Cardano_network.Data p using (Payload)

-- the breakable medium + the io sync set (shared verbatim with `systemBroken`)
open import CSP.Examples.Cardano_network.NetCommon p
  using ( CopySpecBreakableA; ioES )

-- the four τ-free node specs (Praos-namespace rebuild)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.NodeSpecs
  using ( nodeASpec; nodeBSpec; nodeCSpec; nodeDSpec )

-- Net_Api operators (the whole-system alphabet): top io-gated stack + node ⦀
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_ )

module CSP.Examples.Cardano_network.NetworkVerification.Praos.AbstractSystem where

-- the whole-system process type (same alias as `Praos.SysDecode.NetProc` and
-- `systemBroken`): abstractSystem inhabits this type — it is R2's bisim RHS
NetProc : Set₁
NetProc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- R2's bisim RHS: the four τ-free node specs under the breakable medium and
-- the io-gated skeleton, matching `⟦_⟧`/`systemBroken`'s exact shape
abstractSystem : NetProc
abstractSystem =
  (CopySpecBreakableA
    ∥⇘ ioES ⇙
    (nodeASpec ⦀ (nodeBSpec ⦀ (nodeCSpec ⦀ nodeDSpec))))
  ∖ ioES

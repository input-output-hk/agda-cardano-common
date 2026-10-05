{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- FourNode liveness campaign — M4: `breakableSystem ≈DR abstractSystem`
-- (`Liveness.System`).  This module fixes the M4 TARGET `abstractSystem`
-- (the four-node broken system with each node replaced by its M2/M3
-- ≈DR-spec, medium kept verbatim) and records — in full — WHY the planned
-- congruence assembly is BLOCKED by a genuine semantic obstruction.
--
-- ==================== THE M4 TARGET (as designed) ====================
-- The intended proof (controller crux analysis) was:
--
--   system≈DR = cong-∖ ioES
--                 (cong-Par⊤ ioES (drbisim-refl CopySpecBreakableA)
--                    (cong-⦀ nodeA≈DR (cong-⦀ nodeB≈DR (cong-⦀ nodeC≈DR nodeD≈DR))))
--
-- substituting the four node specs under `cong-⦀`/`cong-Par⊤`/`cong-∖`.
--
-- ==================== WHY IT IS BLOCKED ==============================
-- The INNER node-`⦀` step `cong-⦀ nodeA≈DR (…)` requires (from the only
-- available interleaving congruence, `cong-⦀ = cong-Par⊤ ∅ES`, whose
-- `evBoth` case is discharged ONLY by `⊥-elim (Sep.now …)`) a `Sep ∅ES`
-- between each node and the interleaving of the rest.  For `∅ES` this is
-- FULL disjointness of the two operands' offered visible events.
--
-- That disjointness is **FALSE** for every diamond-EDGE node pair
-- (A-B share linkAB, A-C share linkAC, B-D share linkBD, C-D share linkCD):
-- on a shared link `l` the two nodes sit on opposite protocol ROLES —
-- e.g. on linkAB node A runs the CS/BF/… CLIENT at dir lo and node B runs
-- the CS/BF/… SERVER at dir lo (`miniProtocols linkAB lo hi` vs
-- `miniProtocols linkAB hi lo`; see `NetworkPar.miniProtocols`).  BUT both
-- ROLES are FULL-DUPLEX over the shared copy medium: BOTH the client peer
-- AND the server peer fire `input l d <proto>` with an UNCONSTRAINED
-- payload (machine-checked in the committed edge tables — e.g.
-- `NodeDOffers.cs-c-edge-link … ccWreq (_ , input l′ d′ N2N_ChainSync) a`
-- and `NodeDOffers.cs-s-edge-link … (csWrf ht) (_ , input l′ d′
-- N2N_ChainSync) a`, likewise BF `bcWrr`/`bsWsb`, KA, TS).  Hence node A
-- and node B BOTH offer the SAME event `input(linkAB, lo, N2N_ChainSync, ·)`.
--
-- This is NOT a granularity gap: no `Alpha` (however finely keyed by
-- link / dir / role / message) can separate a single event that BOTH
-- trees genuinely offer.  `Disj α β` with the shared `input` event in
-- both `α` and `β` is impossible.  So `Sep ∅ES nodeX nodeY` is refuted,
-- not merely unprovable.
--
-- No re-bracketing of the node `⦀` avoids it: the overlap graph on the
-- four nodes IS the diamond (edges A-B, A-C, B-D, C-D; only A-D and B-C
-- are link-disjoint), and no ordering places every node non-adjacent to
-- all later nodes (each node is adjacent to two others), so every
-- caterpillar `cong-⦀` nesting confronts an overlapping head-vs-tail pair.
--
-- ==================== WHAT WOULD UNBLOCK IT ==========================
--  (a) a NEW interleaving congruence `cong-⦀` that matches the `evBoth`
--      overlap node on the left with the `evBoth` overlap node on the
--      right (symmetric both-offer: commit-L↔commit-L, commit-R↔commit-R)
--      instead of refuting it via `Sep` — substantial NEW core
--      bisimulation machinery, beyond M4's "congruence-only glue"; or
--  (b) a `∥⇘⇙`/`⦀` restructuring law that brings the medium's io-sync
--      INSIDE the node interleaving, turning `input`/`output` into SYNC
--      events (so they need not be `Sep`-disjoint) — a law that does not
--      exist in `CSP/Laws/` (M2 confirmed no such interchange law).
--
-- The MEDIUM-vs-nodes `cong-Par⊤ ioES` step and the `cong-∖` step are
-- both sound in principle (medium offers break(∉ioES)+io(∈ioES); nodes
-- offer api/done(∉ioES)+io(∈ioES); the only non-sync clash break-vs-api
-- IS disjoint by channel; cong-∖ pulls the pre-existing certified König /
-- modA-transfer baseline), but they are gated on the inner ≈DR premise
-- that cannot be produced.  See `.superpowers/sdd/m4-report.md`.
--
-- `abstractSystem` below is therefore the ONLY green artefact of M4; the
-- milestone theorem `system≈DR` is intentionally ABSENT (a hole/postulate
-- would violate the campaign no-holes constraint).
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using (p)
open import CSP.Examples.Cardano_network.Net p using (Net_Api; Net_Api-≟)
open import CSP.Examples.Cardano_network.Data p using (Payload)
open import CSP.Examples.Cardano_network.NetCommon p
  using ( CopySpecBreakableA; ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_ )

-- the four node specs (M2/M3): each `nodeX ≈DR nodeXSpec` is proved
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeA
  using ( nodeASpec )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeBC
  using ( nodeBSpec; nodeCSpec )
open import CSP.Examples.Cardano_network.NetworkVerification.Liveness.NodeD
  using ( nodeDSpec )

module CSP.Examples.Cardano_network.NetworkVerification.Liveness.System where

------------------------------------------------------------------------
-- The M4 target: `breakableSystem` with each node replaced by its ≈DR spec,
-- the breakable medium and the `∥⇘ioES⇙ … ∖ ioES` skeleton kept verbatim.
------------------------------------------------------------------------

-- the abstract broken system: the four node specs over the breakable medium
abstractSystem : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
abstractSystem =
  (CopySpecBreakableA ∥⇘ ioES ⇙ (nodeASpec ⦀ (nodeBSpec ⦀ (nodeCSpec ⦀ nodeDSpec)))) ∖ ioES

-- NOTE (M4 BLOCKED): `system≈DR : breakableSystem ≈DR abstractSystem` is NOT
-- provable via the planned congruence assembly — the inner node-`⦀`
-- `cong-⦀` needs `Sep ∅ES` between diamond-adjacent nodes, which is FALSE
-- (both nodes offer the same `input(sharedLink, dir, proto, ·)` event).
-- See the header and `.superpowers/sdd/m4-report.md` for the full analysis
-- and the two candidate unblockers.

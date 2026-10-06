{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Leios no-livelock, Stage C/L, premise (b): the ASSEMBLY of
-- `τ-AccReach` of the system over a medium from the leaf facts (peers,
-- node logic) and the medium's own τ-accessibility, over the instance
-- family.  The leaves are parameters of a nested module (their types
-- mention `pP`), so the assembly is checked once, independently of them;
-- `Tau2` plugs in the REAL medium theorem `NetworkLinkA-τ-AccReach`; `Tau3` plugs in
-- `NetworkLinkBreakableA-τ-AccReach` for the breakable medium.
------------------------------------------------------------------------

open import Data.Nat using (ℕ)
open import Data.Fin using (Fin)
open import Cardano_network.Parametric.Topology using (Topology; module Topology)
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF)

module Cardano_network.Parametric.Leios.NoLivelock.TauAssembly
  (k m : ℕ) (tP : Topology (pL k m)) (vo : Topology.Node tP → Fin m) where

-- the family member this module is about
pP = pL k m
-- its Leios parameters
lpP = lpF k m
open Topology tP using (Node)

open import Process_Trees using (ExtI)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Bool using (Bool; if_then_else_; true; false)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Class.DecEq using (_≟_)
open import Cardano_network.Base
open import Cardano_network.Net pP
open import Cardano_network.Data pP using (Payload)
open import Cardano_network.ApiAlphabet pP using (apiES)
open import Cardano_network.Parametric.Leios.PeersP pP using (clientPeerP; serverPeerP; nodeBundleP)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (∅ES; Skip; _∥⇘_⇙_; ⦀Fin⁺)
open import Semantics.DivergenceFree {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using (τ-AccReach)
open import CSP.Laws.DivFree.ModAcc (Net_Api-≟ {Payload}) using (MAccR; MAccR-mono; MAccR→τ-AccReach; τ-AccReach→MAccR∅)
open import CSP.Laws.DivFree.Reach (Net_Api-≟ {Payload}) using (MAccR-∥; MAccR-⦀; MAccR-⦀Fin⁺; MAccR-⦀⋆; MAccR-⦀⁺; MAccR-Skip; −∅)
open import CSP.Laws.DivFree.ReachExtra (Net_Api-≟ {Payload}) using (MAccR-if)
open import Cardano_network.NetCommon pP using (ioES)
open import Cardano_network.Parametric.Node pP tP apiES using (Proc; nodeWith; linkBundlesWith; bundleAtWith)
open import Cardano_network.Parametric.Topology using (opposite)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open NLL.Generic pP lpP tP apiES vo using (nodeLogicL; st₀)
open Topology tP using (endpointsOf)

-- `All` over a `map` (the deferred convenience)
All-map : ∀ {A : Set} {ℓp} {P : Proc → Set ℓp} (f : A → Proc) → (∀ x → P (f x)) → ∀ xs → All P (map f xs)
All-map f pf []       = []
All-map f pf (x ∷ xs) = pf x ∷ All-map f pf xs

-- the assembly, from the peer leaves and the node-logic leaf
module _
  (peerC  : ∀ l d id → MAccR ∅ES (clientPeerP l d id))
  (peerS  : ∀ l d id → MAccR ∅ES (serverPeerP l d id))
  (logicR : ∀ n → MAccR ∅ES (nodeLogicL n st₀)) where

  -- one configured instance, dispatched by direction
  pk : ∀ l cl sv d id → MAccR ∅ES (if ⌊ d ≟ cl ⌋ then clientPeerP l d id
                                    else if ⌊ d ≟ sv ⌋ then serverPeerP l d id else Skip)
  pk l cl sv d id = MAccR-if ⌊ d ≟ cl ⌋ (peerC l d id) (MAccR-if ⌊ d ≟ sv ⌋ (peerS l d id) MAccR-Skip)

  -- one endpoint's prototype bundle: the twelve configured instances, interleaved
  bundle-R : ∀ l cl sv → MAccR ∅ES (nodeBundleP l cl sv)
  bundle-R l cl sv =
    MAccR-⦀ ∅ES (pk′ lo N2N_KeepAlive)    (MAccR-⦀ ∅ES (pk′ hi N2N_KeepAlive)
    (MAccR-⦀ ∅ES (pk′ lo N2N_ChainSync)   (MAccR-⦀ ∅ES (pk′ hi N2N_ChainSync)
    (MAccR-⦀ ∅ES (pk′ lo N2N_BlockFetch)  (MAccR-⦀ ∅ES (pk′ hi N2N_BlockFetch)
    (MAccR-⦀ ∅ES (pk′ lo N2N_TxSubmission) (MAccR-⦀ ∅ES (pk′ hi N2N_TxSubmission)
    (MAccR-⦀ ∅ES (pk′ lo N2N_LeiosNotify) (MAccR-⦀ ∅ES (pk′ hi N2N_LeiosNotify)
    (MAccR-⦀ ∅ES (pk′ lo N2N_LeiosFetch)  (MAccR-⦀ ∅ES (pk′ hi N2N_LeiosFetch) MAccR-Skip)))))))))))
    where
      -- the instance at (d , id) on this link
      pk′ = pk l cl sv

  -- one incident endpoint's bundle
  bundleAt-R : ∀ ld → MAccR ∅ES (bundleAtWith nodeBundleP ld)
  bundleAt-R ld = bundle-R (proj₁ ld) (proj₂ ld) (opposite (proj₂ ld))

  -- one node's link bundles
  bundles-R : ∀ n → MAccR ∅ES (linkBundlesWith nodeBundleP n)
  bundles-R n = MAccR-⦀⁺ ∅ES (bundleAt-R (proj₁ (endpointsOf n)))
                  (All-map (bundleAtWith nodeBundleP) bundleAt-R (proj₂ (endpointsOf n)))

  -- one node
  node-R : ∀ n → MAccR ∅ES (nodeWith nodeBundleP n (nodeLogicL n st₀))
  node-R n = MAccR-∥ apiES ∅ES (bundles-R n) (MAccR-mono (−∅′) (logicR n))
    where
      -- `∅ES −H apiES` is inside `∅ES` (the right premise of the asymmetric parallel)
      −∅′ = λ at a m → proj₁ m

  -- THE ASSEMBLY: premise (b) of `noLivelockT` for the system over a τ-accessible medium
  sys-τ : ∀ {med} → τ-AccReach med → τ-AccReach (med ∥⇘ ioES ⇙ ⦀Fin⁺ (Topology.numNodes-1 tP) (λ n → nodeWith nodeBundleP n (nodeLogicL n st₀)))
  sys-τ mt = MAccR→τ-AccReach
    (MAccR-∥ _ ∅ES (τ-AccReach→MAccR∅ mt)
       (MAccR-mono (λ at a m → proj₁ m) (MAccR-⦀Fin⁺ ∅ES (Topology.numNodes-1 tP) node-R)))

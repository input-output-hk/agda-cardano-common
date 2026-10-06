{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE TWO-NODE LINEAR-LEIOS INSTANCE of the
-- no-livelock work (Stage C, spec §3.2): `leiosLParams` cut down to ONE
-- link and TWO voters, the two-node line over it, the UNHIDDEN composite
-- `rawSys2` (medium ∥ nodes, nothing hidden) and the hidden set `H2`
-- (every channel except `env` and `break`).
--
-- `p2` is the instance family `LeiosInstanceP.pL` at one link and two voters
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.LeiosInstance2 where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using ([]; _∷_)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Cardano_network.Params using (Params)
open import Cardano_network.Base
open import Cardano_network.Parametric.Topology using (Topology; mkTopology)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF; HP)

-- `leiosLParams` with ONE link and TWO voters: the instance family at (1 , 2)
p2 : Params
p2 = pL 1 2

-- `leiosLP` carried over to `p2` (same oracle, body table and certificate attribute)
lp2 : LeiosP.LeiosParams p2
lp2 = lpF 1 2

open import Cardano_network.Net p2
open import Cardano_network.Data p2 using (Payload)
open import Cardano_network.NetCommon p2 using (NetworkLinkA; ioES)
open import Cardano_network.ApiAlphabet p2 using (apiES)
open import Cardano_network.Parametric.Leios.PeersP p2 using (nodeBundleP)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload})
  using (EventSet; _∥⇘_⇙_; ⦀Fin⁺)

-- the two-node line: link 0 joins node 0 (lo end) to node 1 (hi end)
line2 : Topology p2
line2 = mkTopology 1 (λ _ → fzero , fsuc fzero) (λ _ ())
          (λ { fzero → (fzero , lo) , refl ; (fsuc fzero) → (fzero , hi) , refl })

open import Cardano_network.Parametric.Node p2 line2 apiES
  using (Proc; nodeWith)
open NLL.Generic p2 lp2 line2 apiES (λ n → n) public
  using (StateL; nodeLogicL; st₀)

-- one node of the line: its prototype peer bundle synchronised with its logic
node2 : Fin 2 → Proc
node2 n = nodeWith nodeBundleP n (nodeLogicL n st₀)

-- THE UNHIDDEN TWO-NODE SYSTEM: the medium against both nodes on `ioES`
rawSys2 : Proc
rawSys2 = NetworkLinkA ∥⇘ ioES ⇙ ⦀Fin⁺ 1 node2

-- THE HIDDEN SET: every api, store and io event (full H, spec §1)
H2 : EventSet
H2 = HP 1 2

open import Data.Fin using (Fin)
open import Cardano_network.Parametric.Topology using (module Topology)

-- node 0's only endpoint is (link 0 , lo)
eps0 : Topology.endpointsOf line2 fzero ≡ ((fzero , lo) , [])
eps0 = refl

-- node 1's only endpoint is (link 0 , hi)
eps1 : Topology.endpointsOf line2 (fsuc fzero) ≡ ((fzero , hi) , [])
eps1 = refl

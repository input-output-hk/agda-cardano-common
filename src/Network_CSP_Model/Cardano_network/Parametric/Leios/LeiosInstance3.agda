{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the bridge from the SHIPPED three-node
-- Linear-Leios instance (`LeiosInstanceL`) to the no-livelock work's
-- instance FAMILY (`LeiosInstanceP`): both shipped instances are members
-- of the family BY DEFINITION, and the shipped system `leiosSystemL` is
-- the io-hiding of the family's raw composite at `pL 2 3`.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.LeiosInstance3 where

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_,_)
open import Data.List using ([]; _∷_)
open import Cardano_network.Base
open import Cardano_network.Parametric.Leios.LeiosInstanceP
open import Cardano_network.Parametric.Leios.LeiosInstance2 using (p2; lp2; line2)
open import Cardano_network.Parametric.Leios.LeiosInstanceL
  using (leiosLParams; leiosLP; leiosLLine; leiosSystemL)
open import Cardano_network.Parametric.Topology using (module Topology)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
open import Cardano_network.Net (pL 2 3) using (Net_Api; Net_Api-≟)
open import Cardano_network.Data (pL 2 3) using (Payload)
open import Cardano_network.NetCommon (pL 2 3) using (NetworkLinkBreakableA; ioES)
open import Cardano_network.ApiAlphabet (pL 2 3) using (apiES)
open import Cardano_network.Parametric.Leios.PeersP (pL 2 3) using (nodeBundleP)
open import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_∥⇘_⇙_; ⦀Fin⁺; _∖_; EventSet)
open import Cardano_network.Parametric.Node (pL 2 3) leiosLLine apiES using (Proc; nodeWith)
open NLL.Generic (pL 2 3) (lpF 2 3) leiosLLine apiES (λ n → n) using (nodeLogicL; st₀)

-- the two-node instance is the family at one link, two voters
p2≡ : p2 ≡ pL 1 2
p2≡ = refl

-- … and so are its Leios parameters
lp2≡ : lp2 ≡ lpF 1 2
lp2≡ = refl

-- the shipped three-node instance is the family at two links, three voters
pLL≡ : leiosLParams ≡ pL 2 3
pLL≡ = refl

-- … and so are its Leios parameters
lpL≡ : leiosLP ≡ lpF 2 3
lpL≡ = refl

-- THE UNHIDDEN THREE-NODE SYSTEM: the breakable medium against all three nodes on `ioES`
rawL : Proc
rawL = NetworkLinkBreakableA ∥⇘ ioES ⇙ ⦀Fin⁺ 2 (λ n → nodeWith nodeBundleP n (nodeLogicL n st₀))

-- the shipped system is the io-hiding of `rawL`, by definition
sysL≡ : leiosSystemL ≡ rawL ∖ ioES
sysL≡ = refl

-- node B (the middle node) has TWO endpoints, A and C one each
epsB : Topology.endpointsOf leiosLLine (fsuc fzero) ≡ ((fzero , hi) , (fsuc fzero , lo) ∷ [])
epsB = refl

-- THE HIDDEN SET of spec §3.3: every channel except `env` and `break`, at the shipped line
HL : EventSet
HL = HP 2 3

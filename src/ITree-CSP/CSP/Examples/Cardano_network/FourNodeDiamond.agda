{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — four nodes in a diamond topology over ONE
-- shared `NetworkA`.  Edges: A–B, A–C, B–D, C–D (no A–D, no B–C).
--
--        A
--       / \
--      B   C
--       \ /
--        D
--
-- The single `NetworkA` is the network medium/multiplexer (it already runs an
-- independent loop per `(protocol, Conn id)`, so `numConns = 8` ⇒ 8 concurrent
-- connections — not one TCP connection for everything).  A link is realised by
-- the two endpoints' mini-protocol bundles sharing the link's `Conn` ids
-- (swapped, so each side's client pairs with the other side's server).
------------------------------------------------------------------------

import Data.Unit as U
open import Data.Fin using (#_)
open import Relation.Nullary using (yes)
open import Relation.Binary.PropositionalEquality using (refl)
open import Class.DecEq using (DecEq)

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Process_Trees using (PTree; AnyTypes; ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base

module CSP.Examples.Cardano_network.FourNodeDiamond where

-- trivial decidable equality for the ⊤ data domains
instance
  decEq⊤ : DecEq U.⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

-- concrete scenario: 8 connections per protocol; opaque data domains ⊤
p : Params
p = record
  { Cookie = U.⊤ ; Block = U.⊤ ; Txid = U.⊤ ; LSlot = U.⊤
  ; VoterId = U.⊤ ; LFBitmap = U.⊤ ; VoteBlob = U.⊤
  ; numConns = λ _ → 8
  ; decCookie = decEq⊤ ; decBlock = decEq⊤ ; decTxid = decEq⊤
  ; decLSlot = decEq⊤ ; decVoterId = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤
  ; Time = U.⊤ ; Length = U.⊤ ; time₀ = U.tt ; length₀ = U.tt
  ; decTime = decEq⊤ ; decLength = decEq⊤ }

open import CSP.Examples.Cardano_network.Net p using (Conn; Net_Api; Net_Api-≟)
open import CSP.Examples.Cardano_network.Data p using (Payload)
open import CSP.Examples.Cardano_network.NetCommon p using (NetworkA; ioES)
open import CSP.Examples.Cardano_network.NetworkPar p
  using (miniProtocols)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Par⊤; _∥⇘_⇙_; _⦀_; _∖_; Skip)

-- directional link ids (`Conn N2N_KeepAlive` = `Fin 8`).  A–B: ab/ba,
-- A–C: ac/ca, B–D: bd/db, C–D: cd/dc.
ab ba ac ca bd db cd dc : Conn N2N_KeepAlive
ab = # 0
ba = # 1
ac = # 2
ca = # 3
bd = # 4
db = # 5
cd = # 6
dc = # 7

-- a uniform link bundle: every protocol's client on `cl`, server on `sv`
mp : Conn N2N_KeepAlive → Conn N2N_KeepAlive
   → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
mp cl sv = miniProtocols cl sv cl sv cl sv cl sv

-- node A: links to B (ab/ba) and C (ac/ca); NodeLogic stubbed as Skip
nodeA : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeA = (mp ab ba ⦀ mp ac ca) ⦀ Skip

-- node B: the other end of A–B (ids swapped) and link to D (bd/db)
nodeB : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeB = (mp ba ab ⦀ mp bd db) ⦀ Skip

-- node C: the other end of A–C and link to D (cd/dc)
nodeC : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeC = (mp ca ac ⦀ mp cd dc) ⦀ Skip

-- node D: the other ends of B–D and C–D
nodeD : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeD = (mp db bd ⦀ mp dc cd) ⦀ Skip

-- the whole network: one shared `NetworkA` carrying all links, io hidden
system : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
system = (NetworkA ∥⇘ ioES ⇙ (nodeA ⦀ (nodeB ⦀ (nodeC ⦀ nodeD)))) ∖ ioES

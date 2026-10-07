{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE DOZEN DEVNET: the Leios demo devnet as a
-- concrete Linear-Leios topology, and the seven network-wide safety
-- theorems S0–S5 instantiated at it, premise-free.
--
-- TOPOLOGY.  Three block producers BP1–BP3, each behind its own three
-- relays (relay11–13, relay21–23, relay31–33): twelve nodes.  Each BP
-- links to its own three relays (9 links) and the nine relays form a
-- complete mesh K9 (36 links): 45 links in all.  Mempool monitors,
-- tx-firehoses, RTT and bandwidth are out of scope (node-to-client and
-- untimed respectively).
--
-- NODE NUMBERING (`Fin 12`).  Nodes 0, 1, 2 are BP1, BP2, BP3; node
-- `3 + 3b + r` is relay (b+1)(r+1), so relay11 = 3, …, relay33 = 11.
-- Links 0–8 are the BP–relay links, links 9–44 the relay pairs `i < j`
-- in lexicographic order; each link's `lo` end is its smaller node.
--
-- PARAMETERS.  No new `Params`: the instance is the Stage-L family
-- member `pL 45 12` / `lpF 45 12` of `LeiosInstanceP` (every link
-- carries `leiosLCfg`, one voter per node).
--
-- `voterOf = id` OVER-APPROXIMATES THE DEVNET: in reality relays do not
-- vote, here every node may.  The theorems below are about THIS model.
-- That they carry over to a model where only the BPs vote is an informal
-- argument (S0–S5 are trace-safety claims, and extra voters should only
-- add behaviour), NOT something proved here.
--
-- NOT PROVIDED: no-livelock.  Stage L's bounds (`NoLivelock/BoundL`
-- etc.) are hand-written for the three-node line and do not transfer.
------------------------------------------------------------------------

module Cardano_network.Parametric.Leios.LeiosInstanceDozen where

open import Data.Fin using (Fin; #_)
import Data.Fin.Properties as FinProp
open import Data.List using (length)
open import Data.List.Relation.Unary.Any using (Any; satisfied) renaming (any? to anyL?)
open import Data.Product using (_×_; _,_; proj₁; proj₂; Σ-syntax)
open import Data.Vec using (Vec; []; _∷_; lookup)
open import Relation.Nullary using (Dec)
open import Relation.Nullary.Decidable using (from-yes; ¬?)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)

open import Process_Trees using (ExtI)
open import Cardano_network.Params using (Params)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Parametric.Topology
  using (Topology; mkTopology; endAtOf; ownedBy?; allEndpoints)
import Cardano_network.Parametric.Leios.LeiosParams as LeiosP
open import Cardano_network.Parametric.Leios.LeiosInstanceP using (pL; lpF)
import Cardano_network.Parametric.Leios.NodeLogicL as NLL
import Cardano_network.Parametric.AnnounceSafe as AS
import Cardano_network.Parametric.AnnounceSafeConcrete as ASCon
import Cardano_network.Parametric.Leios.BodyOrigin as BodyO
import Cardano_network.Parametric.Leios.VoteSound as VS
import Cardano_network.Parametric.Leios.BlobOrigin as BlobO
import Cardano_network.Parametric.Leios.CertSound as CS
import Cardano_network.Parametric.Leios.CertRbOrigin as CRO
import Cardano_network.Parametric.Leios.TxOrigin as TO
open import Cardano_network.Parametric.Leios.VoteSound using (any-mono)
import Cardano_network.Parametric.Leios.AnnounceSystemL as AnnSys
import Cardano_network.Parametric.Leios.BodySystemL as BodySys
import Cardano_network.Parametric.Leios.VoteSystemL as VoteSys
import Cardano_network.Parametric.Leios.BlobSystemL as BlobSys
import Cardano_network.Parametric.Leios.CertSystemL as CertSys
import Cardano_network.Parametric.Leios.CertRbSystemL as CertRbSys
import Cardano_network.Parametric.Leios.TxSystemL as TxSys

------------------------------------------------------------------------
-- Parameters and topology
------------------------------------------------------------------------

-- the devnet's `Params`: the Linear-Leios family at 45 links and 12 voters
pDozen : Params
pDozen = pL 45 12

-- the devnet's Leios parameters: the family's oracle, body table and certificate attribute
lpDozen : LeiosP.LeiosParams pDozen
lpDozen = lpF 45 12

-- the 45 links as (lo-end , hi-end) node pairs: BP–relay links first, then the K9 relay mesh
dozenEdges : Vec (Fin 12 × Fin 12) 45
dozenEdges =
  -- BP1–relay1x, BP2–relay2x, BP3–relay3x
    (# 0 , # 3) ∷ (# 0 , # 4)  ∷ (# 0 , # 5)
  ∷ (# 1 , # 6) ∷ (# 1 , # 7)  ∷ (# 1 , # 8)
  ∷ (# 2 , # 9) ∷ (# 2 , # 10) ∷ (# 2 , # 11)
  -- the relay mesh: every pair i < j of relays 3 … 11
  ∷ (# 3 , # 4) ∷ (# 3 , # 5) ∷ (# 3 , # 6) ∷ (# 3 , # 7) ∷ (# 3 , # 8)
  ∷ (# 3 , # 9) ∷ (# 3 , # 10) ∷ (# 3 , # 11)
  ∷ (# 4 , # 5) ∷ (# 4 , # 6) ∷ (# 4 , # 7) ∷ (# 4 , # 8) ∷ (# 4 , # 9)
  ∷ (# 4 , # 10) ∷ (# 4 , # 11)
  ∷ (# 5 , # 6) ∷ (# 5 , # 7) ∷ (# 5 , # 8) ∷ (# 5 , # 9) ∷ (# 5 , # 10) ∷ (# 5 , # 11)
  ∷ (# 6 , # 7) ∷ (# 6 , # 8) ∷ (# 6 , # 9) ∷ (# 6 , # 10) ∷ (# 6 , # 11)
  ∷ (# 7 , # 8) ∷ (# 7 , # 9) ∷ (# 7 , # 10) ∷ (# 7 , # 11)
  ∷ (# 8 , # 9) ∷ (# 8 , # 10) ∷ (# 8 , # 11)
  ∷ (# 9 , # 10) ∷ (# 9 , # 11)
  ∷ (# 10 , # 11)
  ∷ []

-- the (lo-end , hi-end) pair of each link, read off the edge table
dozenEnds : Fin 45 → Fin 12 × Fin 12
dozenEnds = lookup dozenEdges

-- "no link is a self-loop", decided over all 45 links
dozenIrr? : Dec (∀ l → proj₁ (dozenEnds l) ≢ proj₂ (dozenEnds l))
dozenIrr? = FinProp.all? (λ l → ¬? (proj₁ (dozenEnds l) FinProp.≟ proj₂ (dozenEnds l)))

-- no link is a self-loop (the decision above, run)
dozenIrr : ∀ l → proj₁ (dozenEnds l) ≢ proj₂ (dozenEnds l)
dozenIrr = from-yes dozenIrr?

-- "every node owns some endpoint", decided over the 90 (link , direction) pairs
dozenCover? : Dec (∀ n → Any (λ ld → endAtOf dozenEnds (proj₁ ld) (proj₂ ld) ≡ n) (allEndpoints 45))
dozenCover? = FinProp.all? (λ n → anyL? (ownedBy? dozenEnds n) (allEndpoints 45))

-- no node is isolated: a witness endpoint for every node (the decision above, run)
dozenCover : ∀ n → Σ[ ld ∈ Fin 45 × Dir ] (endAtOf dozenEnds (proj₁ ld) (proj₂ ld) ≡ n)
dozenCover n = satisfied (from-yes dozenCover? n)

-- the dozen devnet as a `Topology`, derived by `mkTopology`
dozenTopo : Topology pDozen
dozenTopo = mkTopology 11 dozenEnds dozenIrr dozenCover

------------------------------------------------------------------------
-- Sanity checks (all by `refl`)
------------------------------------------------------------------------

-- twelve nodes
dozenNodes : Topology.numNodes-1 dozenTopo ≡ 11
dozenNodes = refl

-- BP1 has exactly its three own relay links
dozenBP1-deg : length (Topology.endpointsList dozenTopo (# 0)) ≡ 3
dozenBP1-deg = refl

-- BP2 has exactly its three own relay links
dozenBP2-deg : length (Topology.endpointsList dozenTopo (# 1)) ≡ 3
dozenBP2-deg = refl

-- BP3 has exactly its three own relay links
dozenBP3-deg : length (Topology.endpointsList dozenTopo (# 2)) ≡ 3
dozenBP3-deg = refl

-- relay11 has its BP link plus eight mesh links
dozenRelay11-deg : length (Topology.endpointsList dozenTopo (# 3)) ≡ 9
dozenRelay11-deg = refl

------------------------------------------------------------------------
-- The system
------------------------------------------------------------------------

open import Cardano_network.Net pDozen using (Net_Api)
open import Cardano_network.Data pDozen using (Payload)
open import Cardano_network.NetCommon pDozen using (NetworkLinkBreakableA)
open import Cardano_network.ApiAlphabet pDozen using (apiES)
open import Cardano_network.Parametric.Leios.PeersP pDozen using (nodeBundleP)
open import Cardano_network.Parametric.Node pDozen dozenTopo apiES
  using (Proc; nodeWith; systemOfWithNode)
open NLL.Generic pDozen lpDozen dozenTopo apiES (λ n → n) using (nodeLogicL; st₀)
open import Semantics.Failures {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⊑T_)

-- THE DEVNET: all twelve nodes running the Linear-Leios logic from empty stores over the
-- PROTOTYPE peer bundle and the concrete per-link multiplexer, io hidden
dozenSystem : Proc
dozenSystem =
  systemOfWithNode (nodeWith nodeBundleP) NetworkLinkBreakableA (λ n → nodeLogicL n st₀)

------------------------------------------------------------------------
-- S0–S5 at the devnet, premise-free
------------------------------------------------------------------------

-- every link carries the literal `leiosLCfg`, so the shipped line's decided `LinkCfgWf`
-- at one of its links is the premise at every devnet link
dozenLCfgWf : ASCon.LinkCfgWf pDozen
dozenLCfgWf _ = AnnSys.leiosLCfgWf (# 0)

-- S0: no devnet node announces a ranking block whose announced EB hash was not forged
dozenAnnSafeT : AS.Generic.AnnounceSpecT pDozen dozenTopo apiES ⊑T dozenSystem
dozenAnnSafeT = AnnSys.annSafeLT pDozen lpDozen dozenTopo (λ n → n) dozenLCfgWf

-- S1's discipline at the devnet
module BodyD = BodyO.Generic pDozen lpDozen dozenTopo apiES (λ n → n)

-- S1: no devnet node deposits an EB body it neither forged nor asked for at its own endpoints
dozenBodySoundT : BodyD.BodySpecT ⊑T dozenSystem
dozenBodySoundT = BodySys.bodySoundLT pDozen lpDozen dozenTopo (λ n → n)

-- S2's discipline at the devnet
module VoteD = VS.Generic pDozen lpDozen dozenTopo apiES (λ n → n)

-- S2: no devnet node deposits a vote blob it was neither delivered nor able to vouch for
dozenVoteSoundT : VoteD.VoteSpecT ⊑T dozenSystem
dozenVoteSoundT = VoteSys.voteSoundLT pDozen lpDozen dozenTopo (λ n → n)

-- S2′'s discipline at the devnet: `VoterId = Node`, voter map and inverse both the identity
module BlobD = BlobO.Generic pDozen lpDozen dozenTopo apiES (λ n → n) (λ u → u) (λ n → refl)

-- S2′: no devnet node deposits another voter's blob unless a Notify delivery carried it
dozenBlobSoundT : BlobD.BlobSpecT ⊑T dozenSystem
dozenBlobSoundT =
  BlobSys.blobSoundLT pDozen lpDozen dozenTopo (λ n → n) (λ u → u) (λ n → refl)

-- S3's discipline at the devnet
module CertD = CS.Generic pDozen lpDozen dozenTopo apiES (λ n → n)

-- the devnet oracle ("some held blob names that RB") is monotone: `any` is `⊆`-monotone
dozenCertMono : CertD.CertifiesMono
dozenCertMono sub r eq = any-mono _ sub eq

-- S3's proof module at the devnet, the premise discharged
module CertDS = CertD.Sound dozenCertMono

-- S3: no devnet node issues a certificate its oracle does not grant on its own vote blobs
dozenCertSoundT : CertDS.CertSpecT ⊑T dozenSystem
dozenCertSoundT = CertSys.certSoundLT pDozen lpDozen dozenTopo (λ n → n) dozenCertMono

-- S4's discipline at the devnet
module CertRbD = CRO.Generic pDozen lpDozen dozenTopo apiES (λ n → n)

-- S4: no devnet node stores a certificate RB its own vote store did not certify or its
-- own endpoints did not deliver (forge-route scoped, see `CertRbSystemL`'s header)
dozenCertRbSoundT : CertRbD.CertRbSpecT ⊑T dozenSystem
dozenCertRbSoundT = CertRbSys.certRbSoundLT pDozen lpDozen dozenTopo (λ n → n)

-- S5's discipline at the devnet
module TxD = TO.Generic pDozen lpDozen dozenTopo apiES (λ n → n)

-- S5: no devnet node admits a transaction it was neither submitted nor asked for
dozenTxSoundT : TxD.TxSpecT ⊑T dozenSystem
dozenTxSoundT = TxSys.txSoundLT pDozen lpDozen dozenTopo (λ n → n)

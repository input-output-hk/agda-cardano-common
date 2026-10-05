{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the REQUEST-REPORTING peer bundle, for the
-- Linear-Leios node logic.
--
-- `NetworkPar.serverPeer` wires the stock producers, whose LeiosFetch and
-- TxSubmission members answer a request (resp. swallow a reply) without
-- telling the application what was asked for (resp. what arrived).  A
-- Linear-Leios node has to serve exactly the EB body that was requested
-- and has to put the transactions it receives in its mempool, so it needs
-- the reporting variants `LeiosFetch.LFserverStClientR` and
-- `TxSubmission.TSserverStClientR`.
--
-- This module is ADDITIVE: it re-renames just those two peers, swaps them
-- into a copy of `serverPeer`/`nodeBundle`, and touches nothing existing.
-- The stock `serverStep`s stay byte-identical, so every hand-written
-- bisimulation in `FourNode/Liveness/R2_Bisim/*` (whose spec tables step
-- straight from the wire receive to the busy state) keeps holding.
--
-- `Parametric.Node` already abstracts the builder — `nodeWith mk`,
-- `systemOfWithNode mk med lg` — so the Linear-Leios system is
-- `systemOfWithNode (nodeWith nodeBundleR) …` with no edit to `Node.agda`.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.Parametric.Leios.PeersR (p : Params) where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Bool using (if_then_else_)
open import Data.List using (map)
open import Data.Product using (_,_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Class.DecEq using (_≟_)

open import Process_Trees using (PTree; ExtI)

open import Cardano_network.Base using (Dir; IDs; N2N_TxSubmission; N2N_LeiosFetch)
open Params p using (linkConfig)
open import Cardano_network.Net p using (Link; Net_Api; Net_Api-≟)
open import Cardano_network.Data p using (Payload)
open import Cardano_network.TxSubmission p using (TSEv; TSserverStClientR)
open import Cardano_network.LeiosFetch p using (LFEv; LFserverStClientR)
-- the ι-renames and the stock bundle builder are all public in `NetworkPar`
open import Cardano_network.NetworkPar p
  using ( ιTS; ιTS⁻¹; ιTS-linv; ιLF; ιLF⁻¹; ιLF-linv; clientPeer; serverPeer )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Skip; ⦀⋆)

-- the process type of every peer and bundle below (the one `Parametric.Node` uses)
Proc : Set₁
Proc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the same `TSEv ↪ Net_Api Payload` rename `NetworkPar` applies to the stock peers
import CSP.Rename {E₁ = TSEv} {E₂ = Net_Api Payload} ιTS ιTS⁻¹ ιTS-linv as RenTSR
-- the same `LFEv ↪ Net_Api Payload` rename `NetworkPar` applies to the stock peers
import CSP.Rename {E₁ = LFEv} {E₂ = Net_Api Payload} ιLF ιLF⁻¹ ιLF-linv as RenLFR

-- the renamed reply-reporting TxSubmission requester on link `l`, direction `d`
TSserverRA : Link → Dir → Proc
TSserverRA l d = RenTSR.renameMap (TSserverStClientR l d)

-- the renamed request-reporting LeiosFetch producer on link `l`, direction `d`
LFserverRA : Link → Dir → Proc
LFserverRA l d = RenLFR.renameMap (LFserverStClientR l d)

-- the server peer for one instance `(l, d, id)`, reporting on the two Leios-relevant
-- protocols and stock everywhere else; total on `IDs`
serverPeerR : Link → Dir → IDs → Proc
serverPeerR l d N2N_TxSubmission = TSserverRA l d
serverPeerR l d N2N_LeiosFetch   = LFserverRA l d
serverPeerR l d id               = serverPeer l d id

-- one node's REPORTING peer bundle on link `l`: `NetworkPar.nodeBundle` with
-- `serverPeerR` in the server slot; client peers and the config are unchanged
nodeBundleR : (l : Link) (cl sv : Dir) → Proc
nodeBundleR l cl sv =
  ⦀⋆ (map (λ { (d , id) →
              if ⌊ d ≟ cl ⌋ then clientPeer l d id
              else if ⌊ d ≟ sv ⌋ then serverPeerR l d id
              else Skip })
          (linkConfig l))

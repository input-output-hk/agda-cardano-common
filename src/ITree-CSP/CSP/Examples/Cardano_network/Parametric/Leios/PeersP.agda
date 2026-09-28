{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the LEIOS-PROTOTYPE peer bundle.
--
-- This module models the Leios mini-protocol as implemented on the `leios-prototype`
-- branch of ouroboros-consensus (`LeiosDemoOnlyTest{Notify,Fetch}.hs`, protocol numbers
-- 18/19), which adapts the CIP-164 draft of July 2026.  Messages, payload types, state
-- machine and agency follow the prototype exactly, with two payload abstractions recorded
-- in the ADR `docs/superpowers/decisions/2026-09-21-leios-tx-closure-and-object-identities.md`
-- (`TxBitmap` is a concrete offset set; `MsgLeiosBlockTxs` is an offset-indexed map without
-- a bitmap echo); pipelining and credits, vote weights, deadlines, equivocation and
-- freshness are abstracted (peers are depth-1 alternating machines; the oracles
-- `certifies`, `ebSize`, `ebTxs` stand in for validation).  The older CIP-draft model
-- (`LeiosNotify.agda`/`LeiosFetch.agda`, `apiLN`/`apiLF`) stays beside this one: both ride
-- the same protocol ids and wire channels, and a node runs one or the other by the bundle
-- builder passed to `Node.nodeWith` (`nodeBundle` / `nodeBundleR` versus `nodeBundleP`).
-- Theorems about the old peers (`announceSafeT`, `bfOverLf`, the four-node liveness estate)
-- are untouched by this module.
--
-- "Protocol numbers 18/19" is the PROTOTYPE's numbering: the model's `Base.IDs` is a plain
-- six-constructor enum (`N2N_LeiosNotify`, `N2N_LeiosFetch`) and carries no numeric tag.
--
-- `NetworkPar` itself is untouched: everything it exports is public, and
-- `82ca4056` (`PeersR.agda`) proved the additive pattern.  `Parametric.Node`
-- already abstracts the builder — `nodeWith mk`, `systemOfWithNode mk med lg`
-- — so the prototype system is `systemOfWithNode (nodeWith nodeBundleP) …`
-- with no edit to `Node.agda`.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.Parametric.Leios.PeersP (p : Params) where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Bool using (if_then_else_)
open import Data.List using (map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Class.DecEq using (_≟_)

open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.Base
  using (Dir; IDs; N2N_LeiosNotify; N2N_LeiosFetch; N2N_TxSubmission)
open Params p using (linkConfig)
open import CSP.Examples.Cardano_network.Net p
  using (Link; Net_Api; Net_Api-≟; apiLP; input; output; done)
open import CSP.Examples.Cardano_network.Data p using (Payload)
-- both prototype peers name their api constructor `apiLPev`, so they are imported
-- QUALIFIED: opening either unqualified would make that name ambiguous
import CSP.Examples.Cardano_network.LeiosNotifyP p as LNP
import CSP.Examples.Cardano_network.LeiosFetchP  p as LFP
-- the stock builders stay in charge of the Praos protocols
open import CSP.Examples.Cardano_network.NetworkPar p using (clientPeer; serverPeer)
-- …except TxSubmission's requester, which is taken from `PeersR` rather than re-renamed
-- here, so `nodeBundleP` and `nodeBundleR` hold the SAME term in that slot
open import CSP.Examples.Cardano_network.Parametric.Leios.PeersR p using (TSserverRA)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Skip; ⦀⋆)

-- the process type of every peer and bundle below (the one `Parametric.Node` uses)
Proc : Set₁
Proc = PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})

-- the prototype LeiosNotify alphabet lands on the SAME wire channels the old peer uses
ιLNP : ∀ {A} → LNP.LNPEv A → Net_Api Payload A
ιLNP (LNP.sendLNP    l d)   = input  l d N2N_LeiosNotify
ιLNP (LNP.receiveLNP l d)   = output l d N2N_LeiosNotify
ιLNP (LNP.apiLPev    l d m) = apiLP  l d m
ιLNP (LNP.doneLNP    l d)   = done   l d N2N_LeiosNotify

-- the partial inverse of `ιLNP`.  It maps `apiLP l d m` even though `ιLFP⁻¹` does too:
-- each rename is used ONLY inside its own peer's `renameMap`, and `CSP.Rename` needs the
-- left-inverse law on its own `E₁` alone.
ιLNP⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (LNP.LNPEv A)
ιLNP⁻¹ (input  l d N2N_LeiosNotify) = just (LNP.sendLNP    l d)
ιLNP⁻¹ (output l d N2N_LeiosNotify) = just (LNP.receiveLNP l d)
ιLNP⁻¹ (apiLP  l d m)               = just (LNP.apiLPev    l d m)
ιLNP⁻¹ (done   l d N2N_LeiosNotify) = just (LNP.doneLNP    l d)
ιLNP⁻¹ _                            = nothing

-- `ιLNP⁻¹` really is a left inverse of `ιLNP`
ιLNP-linv : ∀ {A} (e : LNP.LNPEv A) → ιLNP⁻¹ (ιLNP e) ≡ just e
ιLNP-linv (LNP.sendLNP    _ _)   = refl
ιLNP-linv (LNP.receiveLNP _ _)   = refl
ιLNP-linv (LNP.apiLPev    _ _ _) = refl
ιLNP-linv (LNP.doneLNP    _ _)   = refl

-- the `LNPEv ↪ Net_Api Payload` rename this module applies to the prototype Notify peers
import CSP.Rename {E₁ = LNP.LNPEv} {E₂ = Net_Api Payload} ιLNP ιLNP⁻¹ ιLNP-linv as RenLNP

-- the prototype LeiosFetch alphabet lands on the SAME wire channels the old peer uses
ιLFP : ∀ {A} → LFP.LFPEv A → Net_Api Payload A
ιLFP (LFP.sendLFP    l d)   = input  l d N2N_LeiosFetch
ιLFP (LFP.receiveLFP l d)   = output l d N2N_LeiosFetch
ιLFP (LFP.apiLPev    l d m) = apiLP  l d m
ιLFP (LFP.doneLFP    l d)   = done   l d N2N_LeiosFetch

-- the partial inverse of `ιLFP`.  It maps `apiLP l d m` even though `ιLNP⁻¹` does too:
-- each rename is used ONLY inside its own peer's `renameMap`, and `CSP.Rename` needs the
-- left-inverse law on its own `E₁` alone.
ιLFP⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (LFP.LFPEv A)
ιLFP⁻¹ (input  l d N2N_LeiosFetch) = just (LFP.sendLFP    l d)
ιLFP⁻¹ (output l d N2N_LeiosFetch) = just (LFP.receiveLFP l d)
ιLFP⁻¹ (apiLP  l d m)              = just (LFP.apiLPev    l d m)
ιLFP⁻¹ (done   l d N2N_LeiosFetch) = just (LFP.doneLFP    l d)
ιLFP⁻¹ _                           = nothing

-- `ιLFP⁻¹` really is a left inverse of `ιLFP`
ιLFP-linv : ∀ {A} (e : LFP.LFPEv A) → ιLFP⁻¹ (ιLFP e) ≡ just e
ιLFP-linv (LFP.sendLFP    _ _)   = refl
ιLFP-linv (LFP.receiveLFP _ _)   = refl
ιLFP-linv (LFP.apiLPev    _ _ _) = refl
ιLFP-linv (LFP.doneLFP    _ _)   = refl

-- the `LFPEv ↪ Net_Api Payload` rename this module applies to the prototype Fetch peers
import CSP.Rename {E₁ = LFP.LFPEv} {E₂ = Net_Api Payload} ιLFP ιLFP⁻¹ ιLFP-linv as RenLFP

-- the renamed prototype LeiosNotify consumer on link `l`, direction `d`
LNPclientA : Link → Dir → Proc
LNPclientA l d = RenLNP.renameMap (LNP.LNPclientStClient l d)

-- the renamed prototype LeiosNotify producer on link `l`, direction `d`
LNPserverA : Link → Dir → Proc
LNPserverA l d = RenLNP.renameMap (LNP.LNPserverStClient l d)

-- the renamed prototype LeiosFetch consumer on link `l`, direction `d`
LFPclientA : Link → Dir → Proc
LFPclientA l d = RenLFP.renameMap (LFP.LFPclientStClient l d)

-- the renamed prototype LeiosFetch producer (request-reporting) on link `l`, direction `d`
LFPserverA : Link → Dir → Proc
LFPserverA l d = RenLFP.renameMap (LFP.LFPserverStClient l d)

-- the client peer for one instance `(l, d, id)`: the prototype peers on the two Leios
-- ids, the stock `NetworkPar.clientPeer` on the four Praos ids; total on `IDs`.
-- TxSubmission needs NO reporting variant here: the stock submitter `TSclientStClient`
-- already emits `recvTSRequestTxIds` / `recvTSRequestTxs` off the wire before it waits for
-- the application's reply (`TxSubmission.agda:192-199`), so the serving side already sees
-- exactly what was asked for.  Only the requester (server) side was deaf — see below.
clientPeerP : Link → Dir → IDs → Proc
clientPeerP l d N2N_LeiosNotify = LNPclientA l d
clientPeerP l d N2N_LeiosFetch  = LFPclientA l d
clientPeerP l d id              = clientPeer l d id

-- the server peer for one instance, likewise — plus the REPLY-REPORTING TxSubmission
-- requester: `Tx` is opaque (`txData` is gone), so a transaction can only be SERVED, never
-- rebuilt from its hash, and a puller that is handed the stock requester can never observe
-- the reply at all.  The catch-all stays last, so coverage is still typechecker-enforced.
serverPeerP : Link → Dir → IDs → Proc
serverPeerP l d N2N_LeiosNotify = LNPserverA l d
serverPeerP l d N2N_LeiosFetch  = LFPserverA l d
serverPeerP l d N2N_TxSubmission = TSserverRA l d
serverPeerP l d id              = serverPeer l d id

-- one node's PROTOTYPE peer bundle on link `l`: `NetworkPar.nodeBundle`'s body with
-- `clientPeerP`/`serverPeerP` in both slots.  KEEP IN SYNC with `NetworkPar.nodeBundle`
-- and `PeersR.nodeBundleR`: the three differ only in which peer builders they call.
nodeBundleP : (l : Link) (cl sv : Dir) → Proc
nodeBundleP l cl sv =
  ⦀⋆ (map (λ { (d , id) →
              if ⌊ d ≟ cl ⌋ then clientPeerP l d id
              else if ⌊ d ≟ sv ⌋ then serverPeerP l d id
              else Skip })
          (linkConfig l))

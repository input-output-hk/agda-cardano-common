{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the per-protocol `Network` compositions for
-- the node-to-node mini-protocols, merged into one module.  Each protocol
-- renames its peers (`XXEv ↪ Net_Api Payload`) and composes them with the
-- shared (renamed) `Network` multiplexer `NetworkA` over the
-- `{| input, output |}` sync set `ioES`, both from `NetCommon`.
--
-- `Net_Api` carries all of `Net`'s channels (so the renamed `Network`
-- never deadlocks on a hidden message/ack τ that `Rename` pulls back
-- through `ι⁻¹`); only `input`/`output` (plus each peer-local `apiXX`/`done`)
-- are observable after composition.
--
-- Sections: KeepAlive, BlockFetch, ChainSync.  (Formerly the separate
-- modules KeepAliveNetworkPar / BlockFetchNetworkPar / ChainSyncNetworkPar.)
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.NetworkPar (p : Params) where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Bool using (if_then_else_)
open import Data.List using (List; map)
open import Data.Product using (_,_)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (_≟_)

open import Process_Trees using (PTree; AnyTypes; ExtI)

open import CSP.Examples.Cardano_network.Base
-- `Cookie` is an abstract data domain (for `KAserverA`); `linkConfig`
-- assigns each link its active (direction, protocol) instances.
open Params p using (Cookie; linkConfig)
-- `Net p` brings `Net`, `Net_Api`, `Link`, `Net_Api-≟` and the channel
-- constructors `input`/`output`/`apiXX`/`done`/… of both `Net` and `Net_Api`.
open import CSP.Examples.Cardano_network.Net p
-- `Data p` provides the shared `Payload` and its `DecEq`.
open import CSP.Examples.Cardano_network.Data p using (Payload; DecEq-Payload)
-- the three peer families, over their small per-protocol event types
open import CSP.Examples.Cardano_network.KeepAlive p
  using (KAEv; sendKA; receiveKA; apiKAev; doneKA; KAclientStClient; KAserverStClient)
open import CSP.Examples.Cardano_network.BlockFetch p
  using (BFEv; sendBF; receiveBF; apiBFev; doneBF; BFclientStClient; BFserverStClient)
open import CSP.Examples.Cardano_network.ChainSync p
  using (CSEv; sendCS; receiveCS; apiCSev; doneCS; CSclientStClient; CSserverStClient)
open import CSP.Examples.Cardano_network.TxSubmission p
  using (TSEv; sendTS; receiveTS; apiTSev; doneTS; TSclientStClient; TSserverStClient)
open import CSP.Examples.Cardano_network.LeiosNotify p
  using (LNEv; sendLN; receiveLN; apiLNev; doneLN; LNclientStClient; LNserverStClient)
open import CSP.Examples.Cardano_network.LeiosFetch p
  using (LFEv; sendLF; receiveLF; apiLFev; doneLF; LFclientStClient; LFserverStClient)
-- the shared (renamed) Network multiplexer and `{| input, output |}` sync set
open import CSP.Examples.Cardano_network.NetCommon p using (NetworkA; ioES; withNet; clientServerNet)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Par⊤; _∥⇘_⇙_; _⦀_; _∖_; Skip; ⦀⋆)

------------------------------------------------------------------------
-- KeepAlive:  KAEv ↪ Net_Api Payload
--
-- sendKA↦input, receiveKA↦output, apiKAev↦apiKA, doneKA↦done (on
-- `N2N_KeepAlive`).  Injective, so the left inverse holds.
------------------------------------------------------------------------

-- KeepAlive peer events become the `N2N_KeepAlive` channels / `apiKA` / `done`
-- on the same link `l` and direction `d`
ιKA : ∀ {A} → KAEv A → Net_Api Payload A
ιKA (sendKA    l d)   = input  l d N2N_KeepAlive
ιKA (receiveKA l d)   = output l d N2N_KeepAlive
ιKA (apiKAev   l d a) = apiKA  l d a
ιKA (doneKA    l d)   = done   l d N2N_KeepAlive

-- partial inverse (only the KA-tagged channels map back)
ιKA⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (KAEv A)
ιKA⁻¹ (input  l d N2N_KeepAlive) = just (sendKA    l d)
ιKA⁻¹ (output l d N2N_KeepAlive) = just (receiveKA l d)
ιKA⁻¹ (apiKA  l d a)             = just (apiKAev   l d a)
ιKA⁻¹ (done   l d N2N_KeepAlive) = just (doneKA    l d)
ιKA⁻¹ _                          = nothing

-- left inverse
ιKA-linv : ∀ {A} (e : KAEv A) → ιKA⁻¹ (ιKA e) ≡ just e
ιKA-linv (sendKA    _ _)   = refl
ιKA-linv (receiveKA _ _)   = refl
ιKA-linv (apiKAev   _ _ _) = refl
ιKA-linv (doneKA    _ _)   = refl

import CSP.Rename {E₁ = KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv as RenKA

-- the renamed KeepAlive client peer on link `l`, direction `d`
KAclientA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
KAclientA l d = RenKA.renameMap (KAclientStClient l d)

-- The KeepAlive *server* peer renamed into the shared `Net_Api` alphabet,
-- via the same `ιKA` injection, on link `l`, direction `d`.  The `Cookie`
-- is the server's nominal request cookie (unused — the real one is bound
-- from the wire — but retained for call-site symmetry).
KAserverA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
KAserverA l d = RenKA.renameMap (KAserverStClient l d)

-- the whole `Network` synchronised with one KeepAlive client on `(l, d)`
clientNetWithKA : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientNetWithKA l d = withNet (KAclientA l d)

-- the whole `Network` synchronised with one KeepAlive server on `(l, d)`
serverNetWithKA : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
serverNetWithKA l d = withNet (KAserverA l d)

-- the client-with-network and server-with-network interleaved (no shared
-- events; each `Network` is a self-contained loopback).  Client on
-- `(lc, dc)`, server on `(ls, ds)`.
clientServerNetWithKA : Link → Dir → Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientServerNetWithKA lc dc ls ds = clientServerNet (KAclientA lc dc) (KAserverA ls ds)

------------------------------------------------------------------------
-- BlockFetch:  BFEv ↪ Net_Api Payload
------------------------------------------------------------------------

-- BlockFetch peer events become the `N2N_BlockFetch` channels / `apiBF` / `done`
-- on the same link `l` and direction `d`
ιBF : ∀ {A} → BFEv A → Net_Api Payload A
ιBF (sendBF    l d)   = input  l d N2N_BlockFetch
ιBF (receiveBF l d)   = output l d N2N_BlockFetch
ιBF (apiBFev   l d m) = apiBF  l d m
ιBF (doneBF    l d)   = done   l d N2N_BlockFetch

-- partial inverse (only the BF-tagged channels map back)
ιBF⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (BFEv A)
ιBF⁻¹ (input  l d N2N_BlockFetch) = just (sendBF    l d)
ιBF⁻¹ (output l d N2N_BlockFetch) = just (receiveBF l d)
ιBF⁻¹ (apiBF  l d m)              = just (apiBFev   l d m)
ιBF⁻¹ (done   l d N2N_BlockFetch) = just (doneBF    l d)
ιBF⁻¹ _                           = nothing

-- left inverse
ιBF-linv : ∀ {A} (e : BFEv A) → ιBF⁻¹ (ιBF e) ≡ just e
ιBF-linv (sendBF    _ _)   = refl
ιBF-linv (receiveBF _ _)   = refl
ιBF-linv (apiBFev   _ _ _) = refl
ιBF-linv (doneBF    _ _)   = refl

import CSP.Rename {E₁ = BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv as RenBF

-- the renamed BlockFetch client peer on link `l`, direction `d`
BFclientA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
BFclientA l d = RenBF.renameMap (BFclientStClient l d)

-- the renamed BlockFetch server peer on link `l`, direction `d`
BFserverA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
BFserverA l d = RenBF.renameMap (BFserverStClient l d)

-- the whole `Network` synchronised with one BlockFetch client on `(l, d)`
clientNetWithBF : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientNetWithBF l d = withNet (BFclientA l d)

-- the whole `Network` synchronised with one BlockFetch server on `(l, d)`
serverNetWithBF : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
serverNetWithBF l d = withNet (BFserverA l d)

-- the client-with-network and server-with-network interleaved (no shared
-- events; each `Network` is a self-contained loopback).  Client on
-- `(lc, dc)`, server on `(ls, ds)`.
clientServerNetWithBF : Link → Dir → Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientServerNetWithBF lc dc ls ds = clientServerNet (BFclientA lc dc) (BFserverA ls ds)

------------------------------------------------------------------------
-- ChainSync:  CSEv ↪ Net_Api Payload
------------------------------------------------------------------------

-- ChainSync peer events become the `N2N_ChainSync` channels / `apiCS` / `done`
-- on the same link `l` and direction `d`
ιCS : ∀ {A} → CSEv A → Net_Api Payload A
ιCS (sendCS    l d)   = input  l d N2N_ChainSync
ιCS (receiveCS l d)   = output l d N2N_ChainSync
ιCS (apiCSev   l d m) = apiCS  l d m
ιCS (doneCS    l d)   = done   l d N2N_ChainSync

-- partial inverse (only the CS-tagged channels map back)
ιCS⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (CSEv A)
ιCS⁻¹ (input  l d N2N_ChainSync) = just (sendCS    l d)
ιCS⁻¹ (output l d N2N_ChainSync) = just (receiveCS l d)
ιCS⁻¹ (apiCS  l d m)             = just (apiCSev   l d m)
ιCS⁻¹ (done   l d N2N_ChainSync) = just (doneCS    l d)
ιCS⁻¹ _                          = nothing

-- left inverse
ιCS-linv : ∀ {A} (e : CSEv A) → ιCS⁻¹ (ιCS e) ≡ just e
ιCS-linv (sendCS    _ _)   = refl
ιCS-linv (receiveCS _ _)   = refl
ιCS-linv (apiCSev   _ _ _) = refl
ιCS-linv (doneCS    _ _)   = refl

import CSP.Rename {E₁ = CSEv} {E₂ = Net_Api Payload} ιCS ιCS⁻¹ ιCS-linv as RenCS

-- the renamed ChainSync client peer on link `l`, direction `d`
CSclientA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
CSclientA l d = RenCS.renameMap (CSclientStClient l d)

-- the renamed ChainSync server peer on link `l`, direction `d`
CSserverA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
CSserverA l d = RenCS.renameMap (CSserverStClient l d)

-- the whole `Network` synchronised with one ChainSync client on `(l, d)`
clientNetWithCS : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientNetWithCS l d = withNet (CSclientA l d)

-- the whole `Network` synchronised with one ChainSync server on `(l, d)`
serverNetWithCS : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
serverNetWithCS l d = withNet (CSserverA l d)

-- the client-with-network and server-with-network interleaved (no shared
-- events; each `Network` is a self-contained loopback).  Client on
-- `(lc, dc)`, server on `(ls, ds)`.
clientServerNetWithCS : Link → Dir → Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientServerNetWithCS lc dc ls ds = clientServerNet (CSclientA lc dc) (CSserverA ls ds)

------------------------------------------------------------------------
-- TxSubmission2:  TSEv ↪ Net_Api Payload
------------------------------------------------------------------------

-- TxSubmission peer events become the `N2N_TxSubmission` channels / `apiTS` / `done`
-- on the same link `l` and direction `d`
ιTS : ∀ {A} → TSEv A → Net_Api Payload A
ιTS (sendTS    l d)   = input  l d N2N_TxSubmission
ιTS (receiveTS l d)   = output l d N2N_TxSubmission
ιTS (apiTSev   l d m) = apiTS  l d m
ιTS (doneTS    l d)   = done   l d N2N_TxSubmission

-- partial inverse (only the TS-tagged channels map back)
ιTS⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (TSEv A)
ιTS⁻¹ (input  l d N2N_TxSubmission) = just (sendTS    l d)
ιTS⁻¹ (output l d N2N_TxSubmission) = just (receiveTS l d)
ιTS⁻¹ (apiTS  l d m)                = just (apiTSev   l d m)
ιTS⁻¹ (done   l d N2N_TxSubmission) = just (doneTS    l d)
ιTS⁻¹ _                              = nothing

-- left inverse
ιTS-linv : ∀ {A} (e : TSEv A) → ιTS⁻¹ (ιTS e) ≡ just e
ιTS-linv (sendTS    _ _)   = refl
ιTS-linv (receiveTS _ _)   = refl
ιTS-linv (apiTSev   _ _ _) = refl
ιTS-linv (doneTS    _ _)   = refl

import CSP.Rename {E₁ = TSEv} {E₂ = Net_Api Payload} ιTS ιTS⁻¹ ιTS-linv as RenTS

-- the renamed TxSubmission submitter (client) peer on link `l`, direction `d`
TSclientA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
TSclientA l d = RenTS.renameMap (TSclientStClient l d)

-- the renamed TxSubmission requester (server) peer on link `l`, direction `d`
TSserverA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
TSserverA l d = RenTS.renameMap (TSserverStClient l d)

-- the whole `Network` synchronised with one TxSubmission submitter on `(l, d)`
clientNetWithTS : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientNetWithTS l d = withNet (TSclientA l d)

-- the whole `Network` synchronised with one TxSubmission requester on `(l, d)`
serverNetWithTS : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
serverNetWithTS l d = withNet (TSserverA l d)

-- the submitter-with-network and requester-with-network interleaved (no shared
-- events; each `Network` is a self-contained loopback).  Submitter on
-- `(lc, dc)`, requester on `(ls, ds)`.
clientServerNetWithTS : Link → Dir → Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientServerNetWithTS lc dc ls ds = clientServerNet (TSclientA lc dc) (TSserverA ls ds)

------------------------------------------------------------------------
-- LeiosNotify:  LNEv ↪ Net_Api Payload
------------------------------------------------------------------------

-- LeiosNotify peer events become the `N2N_LeiosNotify` channels / `apiLN` /
-- `done` on the same link `l` and direction `d`
ιLN : ∀ {A} → LNEv A → Net_Api Payload A
ιLN (sendLN    l d)   = input  l d N2N_LeiosNotify
ιLN (receiveLN l d)   = output l d N2N_LeiosNotify
ιLN (apiLNev   l d m) = apiLN  l d m
ιLN (doneLN    l d)   = done   l d N2N_LeiosNotify

-- partial inverse (only the LN-tagged channels map back)
ιLN⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (LNEv A)
ιLN⁻¹ (input  l d N2N_LeiosNotify) = just (sendLN    l d)
ιLN⁻¹ (output l d N2N_LeiosNotify) = just (receiveLN l d)
ιLN⁻¹ (apiLN  l d m)               = just (apiLNev   l d m)
ιLN⁻¹ (done   l d N2N_LeiosNotify) = just (doneLN    l d)
ιLN⁻¹ _                            = nothing

-- left inverse
ιLN-linv : ∀ {A} (e : LNEv A) → ιLN⁻¹ (ιLN e) ≡ just e
ιLN-linv (sendLN    _ _)   = refl
ιLN-linv (receiveLN _ _)   = refl
ιLN-linv (apiLNev   _ _ _) = refl
ιLN-linv (doneLN    _ _)   = refl

import CSP.Rename {E₁ = LNEv} {E₂ = Net_Api Payload} ιLN ιLN⁻¹ ιLN-linv as RenLN

-- the renamed LeiosNotify consumer peer on link `l`, direction `d`
LNclientA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
LNclientA l d = RenLN.renameMap (LNclientStClient l d)

-- the renamed LeiosNotify producer peer on link `l`, direction `d`
LNserverA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
LNserverA l d = RenLN.renameMap (LNserverStClient l d)

-- the whole `Network` synchronised with one LeiosNotify consumer on `(l, d)`
clientNetWithLN : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientNetWithLN l d = withNet (LNclientA l d)

-- the whole `Network` synchronised with one LeiosNotify producer on `(l, d)`
serverNetWithLN : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
serverNetWithLN l d = withNet (LNserverA l d)

-- the consumer-with-network and producer-with-network interleaved (no shared
-- events; each `Network` is a self-contained loopback).  Consumer on
-- `(lc, dc)`, producer on `(ls, ds)`.
clientServerNetWithLN : Link → Dir → Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientServerNetWithLN lc dc ls ds = clientServerNet (LNclientA lc dc) (LNserverA ls ds)

------------------------------------------------------------------------
-- LeiosFetch:  LFEv ↪ Net_Api Payload
------------------------------------------------------------------------

-- LeiosFetch peer events become the `N2N_LeiosFetch` channels / `apiLF` /
-- `done` on the same link `l` and direction `d`
ιLF : ∀ {A} → LFEv A → Net_Api Payload A
ιLF (sendLF    l d)   = input  l d N2N_LeiosFetch
ιLF (receiveLF l d)   = output l d N2N_LeiosFetch
ιLF (apiLFev   l d m) = apiLF  l d m
ιLF (doneLF    l d)   = done   l d N2N_LeiosFetch

-- partial inverse (only the LF-tagged channels map back)
ιLF⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (LFEv A)
ιLF⁻¹ (input  l d N2N_LeiosFetch) = just (sendLF    l d)
ιLF⁻¹ (output l d N2N_LeiosFetch) = just (receiveLF l d)
ιLF⁻¹ (apiLF  l d m)              = just (apiLFev   l d m)
ιLF⁻¹ (done   l d N2N_LeiosFetch) = just (doneLF    l d)
ιLF⁻¹ _                           = nothing

-- left inverse
ιLF-linv : ∀ {A} (e : LFEv A) → ιLF⁻¹ (ιLF e) ≡ just e
ιLF-linv (sendLF    _ _)   = refl
ιLF-linv (receiveLF _ _)   = refl
ιLF-linv (apiLFev   _ _ _) = refl
ιLF-linv (doneLF    _ _)   = refl

import CSP.Rename {E₁ = LFEv} {E₂ = Net_Api Payload} ιLF ιLF⁻¹ ιLF-linv as RenLF

-- the renamed LeiosFetch consumer peer on link `l`, direction `d`
LFclientA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
LFclientA l d = RenLF.renameMap (LFclientStClient l d)

-- the renamed LeiosFetch producer peer on link `l`, direction `d`
LFserverA : Link → Dir → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
LFserverA l d = RenLF.renameMap (LFserverStClient l d)

-- the whole `Network` synchronised with one LeiosFetch consumer on `(l, d)`
clientNetWithLF : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientNetWithLF l d = withNet (LFclientA l d)

-- the whole `Network` synchronised with one LeiosFetch producer on `(l, d)`
serverNetWithLF : Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
serverNetWithLF l d = withNet (LFserverA l d)

-- the consumer-with-network and producer-with-network interleaved (no shared
-- events; each `Network` is a self-contained loopback).  Consumer on
-- `(lc, dc)`, producer on `(ls, ds)`.
clientServerNetWithLF : Link → Dir → Link → Dir
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientServerNetWithLF lc dc ls ds = clientServerNet (LFclientA lc dc) (LFserverA ls ds)

------------------------------------------------------------------------
-- Config-driven peer bundle: a node's set of running peers on a link `l`
-- is read off `linkConfig l : List (Dir × IDs)`.  A node plays CLIENT on
-- direction `cl` and SERVER on direction `sv` (its two roles across the
-- link's instances); the Leios ids have no peer implementation yet.
------------------------------------------------------------------------

-- the client peer for one instance `(l, d, id)`; Leios ids have no peer ⇒ Skip
clientPeer : Link → Dir → IDs → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientPeer l d N2N_KeepAlive    = KAclientA l d
clientPeer l d N2N_ChainSync    = CSclientA l d
clientPeer l d N2N_BlockFetch   = BFclientA l d
clientPeer l d N2N_TxSubmission = TSclientA l d
clientPeer l d N2N_LeiosNotify  = LNclientA l d
clientPeer l d N2N_LeiosFetch   = LFclientA l d

-- the server peer for one instance `(l, d, id)`; Leios ids have no peer ⇒ Skip
serverPeer : Link → Dir → IDs → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
serverPeer l d N2N_KeepAlive    = KAserverA l d
serverPeer l d N2N_ChainSync    = CSserverA l d
serverPeer l d N2N_BlockFetch   = BFserverA l d
serverPeer l d N2N_TxSubmission = TSserverA l d
serverPeer l d N2N_LeiosNotify  = LNserverA l d
serverPeer l d N2N_LeiosFetch   = LFserverA l d

-- one node's peer bundle on link `l`: it is CLIENT for the direction `cl`
-- and SERVER for the direction `sv`, over exactly the instances configured
-- on `l` (those in `linkConfig l`); any other direction contributes `Skip`.
nodeBundle : (l : Link) (cl sv : Dir)
           → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeBundle l cl sv =
  ⦀⋆ (map (λ { (d , id) →
              if ⌊ d ≟ cl ⌋ then clientPeer l d id
              else if ⌊ d ≟ sv ⌋ then serverPeer l d id
              else Skip })
          (linkConfig l))

-- uniform bundle: every protocol, client on `cl`, server on `sv` (faithful
-- port of the original fixed-arity `miniProtocols`, independent of `linkConfig`)
miniProtocols : (l : Link) (cl sv : Dir)
              → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
miniProtocols l cl sv =
  KAclientA l cl ⦀ (KAserverA l sv
    ⦀ (CSclientA l cl ⦀ (CSserverA l sv
    ⦀ (BFclientA l cl ⦀ (BFserverA l sv
    ⦀ (TSclientA l cl ⦀ TSserverA l sv))))))

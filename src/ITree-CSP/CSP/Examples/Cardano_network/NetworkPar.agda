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
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (PTree; AnyTypes; ExtI)

open import CSP.Examples.Cardano_network.Base
-- `Cookie` is an abstract data domain — a field of `Params` (for `KAserverA`).
open Params p using (Cookie)
-- `Net p` brings `Net`, `Net_Api`, `Conn`, `Net_Api-≟` and the channel
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
-- the shared (renamed) Network multiplexer and `{| input, output |}` sync set
open import CSP.Examples.Cardano_network.NetCommon p using (NetworkA; ioES; withNet; clientServerNet)

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (Par⊤; _∥⇘_⇙_; _⦀_; _∖_; Skip)

------------------------------------------------------------------------
-- KeepAlive:  KAEv ↪ Net_Api Payload
--
-- sendKA↦input, receiveKA↦output, apiKAev↦apiKA, doneKA↦done (on
-- `N2N_KeepAlive`).  Injective, so the left inverse holds.
------------------------------------------------------------------------

-- KeepAlive peer events become the `N2N_KeepAlive` channels / `apiKA` / `done`
ιKA : ∀ {A} → KAEv A → Net_Api Payload A
ιKA (sendKA    c)   = input  N2N_KeepAlive c
ιKA (receiveKA c)   = output N2N_KeepAlive c
ιKA (apiKAev   c a) = apiKA  c a
ιKA (doneKA    c)   = done   N2N_KeepAlive c

-- partial inverse (only the KA-tagged channels map back)
ιKA⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (KAEv A)
ιKA⁻¹ (input  N2N_KeepAlive c) = just (sendKA    c)
ιKA⁻¹ (output N2N_KeepAlive c) = just (receiveKA c)
ιKA⁻¹ (apiKA  c a)             = just (apiKAev   c a)
ιKA⁻¹ (done   N2N_KeepAlive c) = just (doneKA    c)
ιKA⁻¹ _                        = nothing

-- left inverse
ιKA-linv : ∀ {A} (e : KAEv A) → ιKA⁻¹ (ιKA e) ≡ just e
ιKA-linv (sendKA    _)   = refl
ιKA-linv (receiveKA _)   = refl
ιKA-linv (apiKAev   _ _) = refl
ιKA-linv (doneKA    _)   = refl

import CSP.Rename {E₁ = KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv as RenKA

-- the renamed KeepAlive client peer
KAclientA : Conn N2N_KeepAlive → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
KAclientA c = RenKA.renameMap (KAclientStClient c)

-- The KeepAlive *server* peer renamed into the shared `Net_Api` alphabet,
-- via the same `ιKA` injection.  The `Cookie` is the server's nominal
-- request cookie (unused — the real one is bound from the wire — but
-- retained for call-site symmetry).
KAserverA : Conn N2N_KeepAlive → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
KAserverA c = RenKA.renameMap (KAserverStClient c)

-- the whole `Network` synchronised with one KeepAlive client on `c`
clientNetWithKA : Conn N2N_KeepAlive
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientNetWithKA c = withNet (KAclientA c)

-- the whole `Network` synchronised with one KeepAlive server on `c` (cookie `ck`)
serverNetWithKA : Conn N2N_KeepAlive
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
serverNetWithKA c = withNet (KAserverA c)

-- the client-with-network and server-with-network interleaved (no shared
-- events; each `Network` is a self-contained loopback).  Client on `cc`,
-- server on `cs` (nominal cookie `ck`).
clientServerNetWithKA : Conn N2N_KeepAlive → Conn N2N_KeepAlive
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientServerNetWithKA cc cs = clientServerNet (KAclientA cc) (KAserverA cs)

------------------------------------------------------------------------
-- BlockFetch:  BFEv ↪ Net_Api Payload
------------------------------------------------------------------------

-- BlockFetch peer events become the `N2N_BlockFetch` channels / `apiBF` / `done`
ιBF : ∀ {A} → BFEv A → Net_Api Payload A
ιBF (sendBF    c)   = input  N2N_BlockFetch c
ιBF (receiveBF c)   = output N2N_BlockFetch c
ιBF (apiBFev   c m) = apiBF  c m
ιBF (doneBF    c)   = done   N2N_BlockFetch c

-- partial inverse (only the BF-tagged channels map back)
ιBF⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (BFEv A)
ιBF⁻¹ (input  N2N_BlockFetch c) = just (sendBF    c)
ιBF⁻¹ (output N2N_BlockFetch c) = just (receiveBF c)
ιBF⁻¹ (apiBF  c m)              = just (apiBFev   c m)
ιBF⁻¹ (done   N2N_BlockFetch c) = just (doneBF    c)
ιBF⁻¹ _                         = nothing

-- left inverse
ιBF-linv : ∀ {A} (e : BFEv A) → ιBF⁻¹ (ιBF e) ≡ just e
ιBF-linv (sendBF    _)   = refl
ιBF-linv (receiveBF _)   = refl
ιBF-linv (apiBFev   _ _) = refl
ιBF-linv (doneBF    _)   = refl

import CSP.Rename {E₁ = BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv as RenBF

-- the renamed BlockFetch client peer
BFclientA : Conn N2N_BlockFetch → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
BFclientA c = RenBF.renameMap (BFclientStClient c)

-- the renamed BlockFetch server peer
BFserverA : Conn N2N_BlockFetch → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
BFserverA c = RenBF.renameMap (BFserverStClient c)

-- the whole `Network` synchronised with one BlockFetch client on `c`
clientNetWithBF : Conn N2N_BlockFetch
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientNetWithBF c = withNet (BFclientA c)

-- the whole `Network` synchronised with one BlockFetch server on `c`
serverNetWithBF : Conn N2N_BlockFetch
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
serverNetWithBF c = withNet (BFserverA c)

-- the client-with-network and server-with-network interleaved (no shared
-- events; each `Network` is a self-contained loopback).  Client on `cc`,
-- server on `cs`.
clientServerNetWithBF : Conn N2N_BlockFetch → Conn N2N_BlockFetch
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientServerNetWithBF cc cs = clientServerNet (BFclientA cc) (BFserverA cs)

------------------------------------------------------------------------
-- ChainSync:  CSEv ↪ Net_Api Payload
------------------------------------------------------------------------

-- ChainSync peer events become the `N2N_ChainSync` channels / `apiCS` / `done`
ιCS : ∀ {A} → CSEv A → Net_Api Payload A
ιCS (sendCS    c)   = input  N2N_ChainSync c
ιCS (receiveCS c)   = output N2N_ChainSync c
ιCS (apiCSev   c m) = apiCS  c m
ιCS (doneCS    c)   = done   N2N_ChainSync c

-- partial inverse (only the CS-tagged channels map back)
ιCS⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (CSEv A)
ιCS⁻¹ (input  N2N_ChainSync c) = just (sendCS    c)
ιCS⁻¹ (output N2N_ChainSync c) = just (receiveCS c)
ιCS⁻¹ (apiCS  c m)             = just (apiCSev   c m)
ιCS⁻¹ (done   N2N_ChainSync c) = just (doneCS    c)
ιCS⁻¹ _                        = nothing

-- left inverse
ιCS-linv : ∀ {A} (e : CSEv A) → ιCS⁻¹ (ιCS e) ≡ just e
ιCS-linv (sendCS    _)   = refl
ιCS-linv (receiveCS _)   = refl
ιCS-linv (apiCSev   _ _) = refl
ιCS-linv (doneCS    _)   = refl

import CSP.Rename {E₁ = CSEv} {E₂ = Net_Api Payload} ιCS ιCS⁻¹ ιCS-linv as RenCS

-- the renamed ChainSync client peer
CSclientA : Conn N2N_ChainSync → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
CSclientA c = RenCS.renameMap (CSclientStClient c)

-- the renamed ChainSync server peer
CSserverA : Conn N2N_ChainSync → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
CSserverA c = RenCS.renameMap (CSserverStClient c)

-- the whole `Network` synchronised with one ChainSync client on `c`
clientNetWithCS : Conn N2N_ChainSync
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientNetWithCS c = withNet (CSclientA c)

-- the whole `Network` synchronised with one ChainSync server on `c`
serverNetWithCS : Conn N2N_ChainSync
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
serverNetWithCS c = withNet (CSserverA c)

-- the client-with-network and server-with-network interleaved (no shared
-- events; each `Network` is a self-contained loopback).  Client on `cc`,
-- server on `cs`.
clientServerNetWithCS : Conn N2N_ChainSync → Conn N2N_ChainSync
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientServerNetWithCS cc cs = clientServerNet (CSclientA cc) (CSserverA cs)

------------------------------------------------------------------------
-- TxSubmission2:  TSEv ↪ Net_Api Payload
------------------------------------------------------------------------

-- TxSubmission peer events become the `N2N_TxSubmission` channels / `apiTS` / `done`
ιTS : ∀ {A} → TSEv A → Net_Api Payload A
ιTS (sendTS    c)   = input  N2N_TxSubmission c
ιTS (receiveTS c)   = output N2N_TxSubmission c
ιTS (apiTSev   c m) = apiTS  c m
ιTS (doneTS    c)   = done   N2N_TxSubmission c

-- partial inverse (only the TS-tagged channels map back)
ιTS⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (TSEv A)
ιTS⁻¹ (input  N2N_TxSubmission c) = just (sendTS    c)
ιTS⁻¹ (output N2N_TxSubmission c) = just (receiveTS c)
ιTS⁻¹ (apiTS  c m)                = just (apiTSev   c m)
ιTS⁻¹ (done   N2N_TxSubmission c) = just (doneTS    c)
ιTS⁻¹ _                           = nothing

-- left inverse
ιTS-linv : ∀ {A} (e : TSEv A) → ιTS⁻¹ (ιTS e) ≡ just e
ιTS-linv (sendTS    _)   = refl
ιTS-linv (receiveTS _)   = refl
ιTS-linv (apiTSev   _ _) = refl
ιTS-linv (doneTS    _)   = refl

import CSP.Rename {E₁ = TSEv} {E₂ = Net_Api Payload} ιTS ιTS⁻¹ ιTS-linv as RenTS

-- the renamed TxSubmission submitter (client) peer
TSclientA : Conn N2N_TxSubmission → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
TSclientA c = RenTS.renameMap (TSclientStClient c)

-- the renamed TxSubmission requester (server) peer
TSserverA : Conn N2N_TxSubmission → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
TSserverA c = RenTS.renameMap (TSserverStClient c)

-- the whole `Network` synchronised with one TxSubmission submitter on `c`
clientNetWithTS : Conn N2N_TxSubmission
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientNetWithTS c = withNet (TSclientA c)

-- the whole `Network` synchronised with one TxSubmission requester on `c`
serverNetWithTS : Conn N2N_TxSubmission
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
serverNetWithTS c = withNet (TSserverA c)

-- the submitter-with-network and requester-with-network interleaved (no shared
-- events; each `Network` is a self-contained loopback).  Submitter on `cc`,
-- requester on `cs`.
clientServerNetWithTS : Conn N2N_TxSubmission → Conn N2N_TxSubmission
          → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientServerNetWithTS cc cs = clientServerNet (TSclientA cc) (TSserverA cs)

------------------------------------------------------------------------
-- Example: a node running two TCP connections to two other nodes.
--
-- Each *connection* is the client AND server side of all four mini-protocols
-- (KeepAlive, ChainSync, BlockFetch, TxSubmission2), interleaved.  Within a
-- connection each protocol's client runs on connection id `…c` and its server
-- on `…s` (distinct ids, so the two roles do not collide on the same `Network`
-- channel).  A node's network is ONE shared `NetworkA` synchronised with the
-- interleaving of its connection bundles, with the io alphabet then hidden.
------------------------------------------------------------------------

-- the mini-protocol peer bundle for one connection/link: the client AND
-- server of all four protocols interleaved (NO `NetworkA` — the single shared
-- `NetworkA` is applied once at the node/system level).  Each protocol's
-- client runs on id `…c`, its server on `…s`.
miniProtocols : (kc ks : Conn N2N_KeepAlive)
                (sc ss : Conn N2N_ChainSync)
                (bc bs : Conn N2N_BlockFetch)
                (tc ts : Conn N2N_TxSubmission)
              → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
miniProtocols kc ks sc ss bc bs tc ts =
  KAclientA kc ⦀ (KAserverA ks
    ⦀ (CSclientA sc ⦀ (CSserverA ss
    ⦀ (BFclientA bc ⦀ (BFserverA bs
    ⦀ (TSclientA tc ⦀ TSserverA ts))))))

-- a single node's network: ONE shared `NetworkA` synchronised on
-- `{| input, output |}` with the node's two connection bundles interleaved,
-- then the io alphabet hidden (network traffic internal).
nodeNetwork : (kc1 ks1 : Conn N2N_KeepAlive)
              (sc1 ss1 : Conn N2N_ChainSync)
              (bc1 bs1 : Conn N2N_BlockFetch)
              (tc1 ts1 : Conn N2N_TxSubmission)
              (kc2 ks2 : Conn N2N_KeepAlive)
              (sc2 ss2 : Conn N2N_ChainSync)
              (bc2 bs2 : Conn N2N_BlockFetch)
              (tc2 ts2 : Conn N2N_TxSubmission)
            → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
nodeNetwork kc1 ks1 sc1 ss1 bc1 bs1 tc1 ts1
            kc2 ks2 sc2 ss2 bc2 bs2 tc2 ts2 =
  withNet (miniProtocols kc1 ks1 sc1 ss1 bc1 bs1 tc1 ts1
      ⦀ miniProtocols kc2 ks2 sc2 ss2 bc2 bs2 tc2 ts2) ∖ ioES

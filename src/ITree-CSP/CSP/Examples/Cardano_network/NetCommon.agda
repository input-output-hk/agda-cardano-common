{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — shared `Net Payload ↪ Net_Api Payload`
-- renaming, the renamed `Network` multiplexer, and the `{| input, output |}`
-- synchronisation set.  Factored out of the per-protocol `*NetworkPar`
-- modules (KeepAlive / BlockFetch / ChainSync), which all lift `Network`
-- and synchronise their peer on `input`/`output` identically.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Params using (Params)

module CSP.Examples.Cardano_network.NetCommon (p : Params) where

open import Level using (0ℓ)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (PTree; AnyTypes; ExtI)

open import CSP.Examples.Cardano_network.Base
open import CSP.Examples.Cardano_network.Net p
open import CSP.Examples.Cardano_network.Data p using (Payload; DecEq-Payload)
open import CSP.Examples.Cardano_network.Network p Payload using (Network)

------------------------------------------------------------------------
-- Net Payload ↪ Net_Api Payload   (identity on channel names)
------------------------------------------------------------------------

-- inject the eight `Net` channels into their `Net_Api` namesakes
ιNet : ∀ {A} → Net Payload A → Net_Api Payload A
ιNet (input  id c) = input  id c
ιNet (output id c) = output id c
ιNet (sndmsg id c) = sndmsg id c
ιNet (rcvmsg id c) = rcvmsg id c
ιNet (tx     id c) = tx     id c
ιNet (sndack id c) = sndack id c
ιNet (rcvack id c) = rcvack id c
ιNet (ack    id c) = ack    id c

-- partial inverse: the eight real channels back, all api/done ↦ nothing
ιNet⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (Net Payload A)
ιNet⁻¹ (input  id c) = just (input  id c)
ιNet⁻¹ (output id c) = just (output id c)
ιNet⁻¹ (sndmsg id c) = just (sndmsg id c)
ιNet⁻¹ (rcvmsg id c) = just (rcvmsg id c)
ιNet⁻¹ (tx     id c) = just (tx     id c)
ιNet⁻¹ (sndack id c) = just (sndack id c)
ιNet⁻¹ (rcvack id c) = just (rcvack id c)
ιNet⁻¹ (ack    id c) = just (ack    id c)
ιNet⁻¹ (done  _ _) = nothing
ιNet⁻¹ (apiCS _ _) = nothing
ιNet⁻¹ (apiBF _ _) = nothing
ιNet⁻¹ (apiTS _ _) = nothing
ιNet⁻¹ (apiKA _ _) = nothing
ιNet⁻¹ (apiLN _ _) = nothing
ιNet⁻¹ (apiLF _ _) = nothing

-- left inverse on the eight channels
ιNet-linv : ∀ {A} (e : Net Payload A) → ιNet⁻¹ (ιNet e) ≡ just e
ιNet-linv (input  _ _) = refl
ιNet-linv (output _ _) = refl
ιNet-linv (sndmsg _ _) = refl
ιNet-linv (rcvmsg _ _) = refl
ιNet-linv (tx     _ _) = refl
ιNet-linv (sndack _ _) = refl
ιNet-linv (rcvack _ _) = refl
ιNet-linv (ack    _ _) = refl

import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload} ιNet ιNet⁻¹ ιNet-linv as RenNet

-- the renamed Network multiplexer over the Net_Api alphabet
NetworkA : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
NetworkA = RenNet.renameMap Network

------------------------------------------------------------------------
-- The `{| input, output |}` synchronisation set.
------------------------------------------------------------------------

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (chanSet; EventSet; _∥⇘_⇙_; _⦀_)

-- sync set {| input, output |} (membership by channel, ignoring payload)
ioSet : AnyTypes (Net_Api Payload) → Set
ioSet (_ , input  _ _) = ⊤
ioSet (_ , output _ _) = ⊤
ioSet _                = ⊥

-- decidability of the sync-set membership
ioSet-dec : (at : AnyTypes (Net_Api Payload)) → Dec (ioSet at)
ioSet-dec (_ , input  _ _) = yes tt
ioSet-dec (_ , output _ _) = yes tt
ioSet-dec (_ , sndmsg _ _) = no λ ()
ioSet-dec (_ , rcvmsg _ _) = no λ ()
ioSet-dec (_ , tx     _ _) = no λ ()
ioSet-dec (_ , sndack _ _) = no λ ()
ioSet-dec (_ , rcvack _ _) = no λ ()
ioSet-dec (_ , ack    _ _) = no λ ()
ioSet-dec (_ , done   _ _) = no λ ()
ioSet-dec (_ , apiCS  _ _) = no λ ()
ioSet-dec (_ , apiBF  _ _) = no λ ()
ioSet-dec (_ , apiTS  _ _) = no λ ()
ioSet-dec (_ , apiKA  _ _) = no λ ()
ioSet-dec (_ , apiLN  _ _) = no λ ()
ioSet-dec (_ , apiLF  _ _) = no λ ()

-- the {| input, output |} event set
ioES : EventSet
ioES = chanSet ioSet ioSet-dec

-- a process composed with the network medium, synchronised on the io channels {| input, output |}
withNet : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
        → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
withNet q = NetworkA ∥⇘ ioES ⇙ q

-- a client and a server, each composed with the medium, then interleaved
clientServerNet : (client server : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ}))
                → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
clientServerNet cl sv = withNet cl ⦀ withNet sv

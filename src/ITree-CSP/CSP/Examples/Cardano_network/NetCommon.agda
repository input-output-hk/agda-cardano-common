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

open Params p using (numLinks)
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
open import CSP.Examples.Cardano_network.Network p Payload using (Network; CopySpec; linkCopy)

------------------------------------------------------------------------
-- Net Payload ↪ Net_Api Payload   (identity on channel names)
------------------------------------------------------------------------

-- inject the eight `Net` channels into their `Net_Api` namesakes, threading
-- the link `l` and direction `d` through unchanged
ιNet : ∀ {A} → Net Payload A → Net_Api Payload A
ιNet (input  l d id) = input  l d id
ιNet (output l d id) = output l d id
ιNet (sndmsg l d id) = sndmsg l d id
ιNet (rcvmsg l d id) = rcvmsg l d id
ιNet (tx     l d id) = tx     l d id
ιNet (sndack l d id) = sndack l d id
ιNet (rcvack l d id) = rcvack l d id
ιNet (ack    l d id) = ack    l d id

-- partial inverse: the eight real channels back, all api/done ↦ nothing
ιNet⁻¹ : ∀ {A} → Net_Api Payload A → Maybe (Net Payload A)
ιNet⁻¹ (input  l d id) = just (input  l d id)
ιNet⁻¹ (output l d id) = just (output l d id)
ιNet⁻¹ (sndmsg l d id) = just (sndmsg l d id)
ιNet⁻¹ (rcvmsg l d id) = just (rcvmsg l d id)
ιNet⁻¹ (tx     l d id) = just (tx     l d id)
ιNet⁻¹ (sndack l d id) = just (sndack l d id)
ιNet⁻¹ (rcvack l d id) = just (rcvack l d id)
ιNet⁻¹ (ack    l d id) = just (ack    l d id)
ιNet⁻¹ (done  _ _ _) = nothing
ιNet⁻¹ (apiCS _ _ _) = nothing
ιNet⁻¹ (apiBF _ _ _) = nothing
ιNet⁻¹ (apiTS _ _ _) = nothing
ιNet⁻¹ (apiKA _ _ _) = nothing
ιNet⁻¹ (apiLN _ _ _) = nothing
ιNet⁻¹ (apiLF _ _ _) = nothing
ιNet⁻¹ (break _)     = nothing

-- left inverse on the eight channels
ιNet-linv : ∀ {A} (e : Net Payload A) → ιNet⁻¹ (ιNet e) ≡ just e
ιNet-linv (input  _ _ _) = refl
ιNet-linv (output _ _ _) = refl
ιNet-linv (sndmsg _ _ _) = refl
ιNet-linv (rcvmsg _ _ _) = refl
ιNet-linv (tx     _ _ _) = refl
ιNet-linv (sndack _ _ _) = refl
ιNet-linv (rcvack _ _ _) = refl
ιNet-linv (ack    _ _ _) = refl

import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload} ιNet ιNet⁻¹ ιNet-linv as RenNet

-- the renamed Network multiplexer over the Net_Api alphabet
NetworkA : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
NetworkA = RenNet.renameMap Network

-- the renamed CopySpec (input.c ? d → output.c ! d copy medium) over the
-- Net_Api alphabet; the FD-equivalent (`NetworkA ≈FD CopySpec`) drop-in for NetworkA
CopySpecA : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
CopySpecA = RenNet.renameMap CopySpec

------------------------------------------------------------------------
-- The `{| input, output |}` synchronisation set.
------------------------------------------------------------------------

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using (chanSet; EventSet; _∥⇘_⇙_; _⦀_; _△_; Prefix₀; Skip; ⦀Fin)

-- sync set {| input, output |} (membership by channel, ignoring link/dir/payload)
ioSet : AnyTypes (Net_Api Payload) → Set
ioSet (_ , input  _ _ _) = ⊤
ioSet (_ , output _ _ _) = ⊤
ioSet _                  = ⊥

-- decidability of the sync-set membership
ioSet-dec : (at : AnyTypes (Net_Api Payload)) → Dec (ioSet at)
ioSet-dec (_ , input  _ _ _) = yes tt
ioSet-dec (_ , output _ _ _) = yes tt
ioSet-dec (_ , sndmsg _ _ _) = no λ ()
ioSet-dec (_ , rcvmsg _ _ _) = no λ ()
ioSet-dec (_ , tx     _ _ _) = no λ ()
ioSet-dec (_ , sndack _ _ _) = no λ ()
ioSet-dec (_ , rcvack _ _ _) = no λ ()
ioSet-dec (_ , ack    _ _ _) = no λ ()
ioSet-dec (_ , done   _ _ _) = no λ ()
ioSet-dec (_ , apiCS  _ _ _) = no λ ()
ioSet-dec (_ , apiBF  _ _ _) = no λ ()
ioSet-dec (_ , apiTS  _ _ _) = no λ ()
ioSet-dec (_ , apiKA  _ _ _) = no λ ()
ioSet-dec (_ , apiLN  _ _ _) = no λ ()
ioSet-dec (_ , apiLF  _ _ _) = no λ ()
ioSet-dec (_ , break  _)     = no λ ()

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

------------------------------------------------------------------------
-- The breakable copy medium: each link's copy bundle, interrupted by its
-- own `break` fault-injection event.
------------------------------------------------------------------------

-- one link's copy bundle, renamed into the Net_Api alphabet
linkMediumA : Link → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
linkMediumA l = RenNet.renameMap (linkCopy l)

-- link l runs normally until its `break l` fires, then terminates (Skip, √) —
-- the break event marks the link broken
breakableLinkA : Link → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
breakableLinkA l = linkMediumA l △ (break l ⟶₀ Skip)

-- the breakable copy medium: every link independently breakable by its break event
CopySpecBreakableA : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) (⊤ {0ℓ})
CopySpecBreakableA = ⦀Fin numLinks breakableLinkA

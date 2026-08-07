{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Closing the demo of `CSP.Laws.FD.FrozenComponent` at the REAL
-- synchronisation set of the four-node diamond.
--
-- `LeafSpecs.FrozenKAclient` leaves two hypotheses open: `Δ ⊆ A` and
-- `Partner Δ A D`.  This module discharges the FIRST at `A := apiES`,
-- which is the alphabet-level, ONE-TIME cost (one clause per `Net_Api`
-- channel, reusable by every frozen peer kind), and records the second
-- as the genuinely PER-NODE obligation it is.
--
-- Only `apiES` is taken from `FourNodeDiamond`.  No composite (`nodeB`,
-- `nodeC`, `nodeD`, the systems) is mentioned, so nothing is forced.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.FourNode.FrozenPeersDemo where

open import Level using (0ℓ)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic using () renaming (tt to ttᵖ)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; apiES )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; Net_Api-≟
        ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack; done
        ; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF; break )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open import CSP.Examples.Cardano_network.LeafSpecs.FrozenKAclient p using ( ΔKA )

-- `Δ ⊆ apiES`: the `apiKA` channel is inside `apiES`
-- (`apiSet (_ , apiKA _ _ _) = ⊤`), and `ΔKA` is `⊥` on every other channel, so the
-- remaining fifteen clauses are absurd.  ONE-TIME, alphabet-level, peer-independent.
ΔKA⊆apiES : ∀ {X : Set} {f : Net_Api Payload X} {a : X}
          → ΔKA (X , f) a → Op.EventSet.mem apiES (X , f) a
ΔKA⊆apiES {f = apiKA  _ _ _} _  = ttᵖ
ΔKA⊆apiES {f = input  _ _ _} ()
ΔKA⊆apiES {f = output _ _ _} ()
ΔKA⊆apiES {f = sndmsg _ _ _} ()
ΔKA⊆apiES {f = rcvmsg _ _ _} ()
ΔKA⊆apiES {f = tx     _ _ _} ()
ΔKA⊆apiES {f = sndack _ _ _} ()
ΔKA⊆apiES {f = rcvack _ _ _} ()
ΔKA⊆apiES {f = ack    _ _ _} ()
ΔKA⊆apiES {f = done   _ _ _} ()
ΔKA⊆apiES {f = apiCS  _ _ _} ()
ΔKA⊆apiES {f = apiBF  _ _ _} ()
ΔKA⊆apiES {f = apiTS  _ _ _} ()
ΔKA⊆apiES {f = apiLN  _ _ _} ()
ΔKA⊆apiES {f = apiLF  _ _ _} ()
ΔKA⊆apiES {f = break  _}     ()

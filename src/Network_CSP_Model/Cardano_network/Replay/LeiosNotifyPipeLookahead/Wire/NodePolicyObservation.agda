{-# OPTIONS --guardedness #-}

-- Lossless ordered observations transport the full node policy and its actual native paths.
-- Raw text decoding, record selection and physical logger fidelity are separate obligations.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodePolicyObservation where

open import Level using (Level; 0ℓ; suc; _⊔_)
open import Data.List using (List; map)
open import Data.List.Properties using (map-∘)
open import Data.Maybe using (Maybe; just)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Relation.Nullary using (Dec; yes; no)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Net exactParams using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (Notification)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as Client
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as Server
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.PairedAdapter as Encoding
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodePairedAdapter as Policy
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.LoggerObservation as Typed
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverDecideNative exactParams as Native

-- A partial observation function always leaves every supplied position in its parser-outcome input.
module ForMapping {ℓ : Level} {Raw : Set ℓ} (normalize : Raw → Maybe Log.E) where

  -- Failure remains Nothing at that position; there is no filtering or sorting here.
  input : List Raw → Policy.Input
  input = map normalize

  -- The existing generic relation records one exact successful summary per supplied raw value.
  Observation : List Raw → List Log.E → Set ℓ
  Observation = Typed.Mapped normalize

  -- Every observed position retains the same full-policy acceptance predicate in either direction.
  transport : ∀ {cr sr clientRaw serverRaw clientEvents serverEvents} →
    Observation clientRaw clientEvents → Observation serverRaw serverEvents →
    (Policy.Accepted cr (input clientRaw) sr (input serverRaw) →
     Policy.Accepted cr (Policy.present clientEvents) sr (Policy.present serverEvents)) ×
    (Policy.Accepted cr (Policy.present clientEvents) sr (Policy.present serverEvents) →
     Policy.Accepted cr (input clientRaw) sr (input serverRaw))
  transport clientObserved serverObserved
    rewrite Typed.mapped-equation clientObserved | Typed.mapped-equation serverObserved =
      (λ witness → witness) , (λ witness → witness)

  -- This independent observed language retains the whole input lists and an original full node run.
  Accepted : Log.Role → List Raw → Log.Role → List Raw → Set ℓ
  Accepted cr clientRaw sr serverRaw = Σ[ clientEvents ∈ List Log.E ] Σ[ serverEvents ∈ List Log.E ]
    (Observation clientRaw clientEvents × Observation serverRaw serverEvents ×
     Policy.Accepted cr (Policy.present clientEvents) sr (Policy.present serverEvents))

  -- Any accepted adapter input reconstructs actual successful observations for every original row.
  recover : ∀ {cr sr clientRaw serverRaw} →
    Policy.Accepted cr (input clientRaw) sr (input serverRaw) → Accepted cr clientRaw sr serverRaw
  recover original@(client , server , valid , source) =
    map (λ row → Client.encode (Encoding.clientWire row)) client ,
    map (λ row → Server.encode (Encoding.serverWire row)) server ,
    clientObserved , serverObserved , proj₁ (transport clientObserved serverObserved) original
    where
    -- Exact existing re-encoding reconstructs the complete ordered client observation.
    clientObserved = Typed.equation-mapped
      (trans (sym (Policy.client-roundtrip valid)) (map-∘ client))
    -- The independent server order is recovered without selecting a cross-endpoint merge.
    serverObserved = Typed.equation-mapped
      (trans (sym (Policy.server-roundtrip valid)) (map-∘ server))

  -- Erasing explicit observation witnesses changes no input position or source execution.
  forget : ∀ {cr sr clientRaw serverRaw} → Accepted cr clientRaw sr serverRaw →
    Policy.Accepted cr (input clientRaw) sr (input serverRaw)
  forget (clientEvents , serverEvents , clientObserved , serverObserved , source) =
    proj₂ (transport clientObserved serverObserved) source

  -- Observed compatibility and existing full-policy adaptation are exactly the same finite language.
  equivalence : ∀ cr clientRaw sr serverRaw →
    (Policy.Accepted cr (input clientRaw) sr (input serverRaw) → Accepted cr clientRaw sr serverRaw) ×
    (Accepted cr clientRaw sr serverRaw → Policy.Accepted cr (input clientRaw) sr (input serverRaw))
  equivalence cr clientRaw sr serverRaw = recover , forget

  -- A negative result excludes every exact ordered observation and every compatible full source run.
  decide : (cr : Log.Role) (clientRaw : List Raw) (sr : Log.Role) (serverRaw : List Raw) →
    Dec (Accepted cr clientRaw sr serverRaw)
  decide cr clientRaw sr serverRaw with Policy.decide cr (input clientRaw) sr (input serverRaw)
  ... | yes source = yes (recover source)
  ... | no absent = no λ observed → absent (forget observed)

-- Typed logger hooks use the previously proved namespace/direction/message schema unchanged.
module Logger = ForMapping Typed.normalize

-- Native coordinates are fixed independently of normalized capture declarations.
module At (cl sl : Link) (cd sd : Dir) where
  module N = Native.At cl sl cd sd

  -- Native acceptance retains exact adaptation and an actual path of the unchanged full-policy tree.
  Accepted : Log.Role → Policy.Input → Log.Role → Policy.Input → Set₁
  Accepted cr ci sr si = Σ[ client ∈ List Rows.ClientRow ] Σ[ server ∈ List Rows.ServerRow ]
    (Policy.Valid cr ci sr si client server × N.NativePair client server)

  -- Source acceptance realizes all erased external inputs as actual native visible actions.
  realize : ∀ {cr ci sr si} → Policy.Accepted cr ci sr si → Accepted cr ci sr si
  realize (client , server , valid , source) = client , server , valid , N.source-to-native source

  -- Arbitrary actual native paths reconstruct original full-policy source rules and exact rows.
  sound : ∀ {cr ci sr si} → Accepted cr ci sr si → Policy.Accepted cr ci sr si
  sound (client , server , valid , native) = client , server , valid , N.native-to-source native

  -- Native and source normalized languages coincide without assuming injectivity of coinductive trees.
  equivalence : ∀ cr ci sr si →
    (Policy.Accepted cr ci sr si → Accepted cr ci sr si) ×
    (Accepted cr ci sr si → Policy.Accepted cr ci sr si)
  equivalence cr ci sr si = realize , sound

  -- This decision excludes every matching native realization on a negative source result.
  decide : (cr : Log.Role) (ci : Policy.Input) (sr : Log.Role) (si : Policy.Input) → Dec (Accepted cr ci sr si)
  decide cr ci sr si with Policy.decide cr ci sr si
  ... | yes source = yes (realize source)
  ... | no absent = no λ native → absent (sound native)

  -- Future frontends may reuse this same transport after proving their own ordered mapping relation.
  module WithMapping {ℓ : Level} {Raw : Set ℓ} (normalize : Raw → Maybe Log.E) where
    module M = ForMapping normalize

    -- Observed native acceptance retains every original input and its actual full-policy PTree path.
    Observed : Log.Role → List Raw → Log.Role → List Raw → Set (ℓ ⊔ suc 0ℓ)
    Observed cr clientRaw sr serverRaw = Σ[ clientEvents ∈ List Log.E ] Σ[ serverEvents ∈ List Log.E ]
      (M.Observation clientRaw clientEvents × M.Observation serverRaw serverEvents ×
       Accepted cr (Policy.present clientEvents) sr (Policy.present serverEvents))

    -- Every observed source witness supplies the same actual native path without extra decoding assumptions.
    observed-realize : ∀ {cr clientRaw sr serverRaw} → M.Accepted cr clientRaw sr serverRaw →
      Observed cr clientRaw sr serverRaw
    observed-realize (clientEvents , serverEvents , clientObserved , serverObserved , source) =
      clientEvents , serverEvents , clientObserved , serverObserved , realize source

    -- Native inversion retains the original successful observation witnesses and all supplied positions.
    observed-sound : ∀ {cr clientRaw sr serverRaw} → Observed cr clientRaw sr serverRaw →
      M.Accepted cr clientRaw sr serverRaw
    observed-sound (clientEvents , serverEvents , clientObserved , serverObserved , native) =
      clientEvents , serverEvents , clientObserved , serverObserved , sound native

    -- Full observed native compatibility is decidable through the unchanged full-policy source checker.
    observed-decide : (cr : Log.Role) (clientRaw : List Raw) (sr : Log.Role) (serverRaw : List Raw) →
      Dec (Observed cr clientRaw sr serverRaw)
    observed-decide cr clientRaw sr serverRaw with M.decide cr clientRaw sr serverRaw
    ... | yes source = yes (observed-realize source)
    ... | no absent = no λ native → absent (observed-sound native)

  -- Exact typed-hook native observations specialize the reusable mapping transport.
  module LoggerNative = WithMapping Typed.normalize

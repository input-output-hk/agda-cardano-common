{-# OPTIONS --guardedness #-}

-- Canonical full-packet realization for the endpoint-tagged native driver alphabet.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverEventsBridge (p : Params) (Return : Set) where

open import Data.Maybe using (just; nothing; map)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import Cardano_network.Base using (Dir)
open import Cardano_network.Data p using (Payload; DecEq-Payload)
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p Return as N

-- Exact equality makes each canonical packet pass its complete-envelope check.
checked-self : ∀ {Message : Set} (encode : Message → Payload) (msg : Message) →
  map proj₁ (N.checkedPacket encode msg (encode msg)) ≡ just msg
checked-self encode msg with encode msg ≟ encode msg
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)

-- Request and Quit decode to their original command without changing metadata.
commands-self : ∀ msg → map proj₁ (N.commands (N.clientPacket msg)) ≡ just msg
commands-self D.request = checked-self N.clientPacket D.request
commands-self D.quit = checked-self N.clientPacket D.quit

-- All normal reply kinds, cancellation and Done have exact full-packet representatives.
responses-self : ∀ msg → map proj₁ (N.responses (N.serverPacket msg)) ≡ just msg
responses-self D.done = checked-self N.serverPacket D.done
responses-self (D.reply S.canceled) = checked-self N.serverPacket (D.reply S.canceled)
responses-self (D.reply (S.normal (announcement h))) = checked-self N.serverPacket (D.reply (S.normal (announcement h)))
responses-self (D.reply (S.normal (offer pt size))) = checked-self N.serverPacket (D.reply (S.normal (offer pt size)))
responses-self (D.reply (S.normal (txsOffer pt))) = checked-self N.serverPacket (D.reply (S.normal (txsOffer pt)))
responses-self (D.reply (S.normal (votes vs))) = checked-self N.serverPacket (D.reply (S.normal (votes vs)))

-- Attach a command's actor/record tag after preserving its exact packet decoding.
command-record : (tag : D.ClientMessage → D.Event) (msg : D.ClientMessage) →
  map (λ x → tag (proj₁ x)) (N.commands (N.clientPacket msg)) ≡ just (tag msg)
command-record tag msg with N.commands (N.clientPacket msg) | commands-self msg
... | nothing | ()
... | just (_ , _) | refl = refl

-- Responder actor/record tags retain the same selected native packet at both ends.
response-record : (tag : D.ServerMessage → D.Event) (msg : D.ServerMessage) →
  map (λ x → tag (proj₁ x)) (N.responses (N.serverPacket msg)) ≡ just (tag msg)
response-record tag msg with N.responses (N.serverPacket msg) | responses-self msg
... | nothing | ()
... | just (_ , _) | refl = refl

-- Each endpoint's coordinates remain explicit throughout native record realization.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  open N.At contract cl sl cd sd

  -- Reflexive endpoint checks accept precisely the supplied expected coordinates.
  endpoint-self : ∀ link dir row → endpoint link dir link dir row ≡ row
  endpoint-self link dir row with link ≟ link | dir ≟ dir
  ... | yes _ | yes _ = refl
  ... | no neq | _ = ⊥-elim (neq refl)
  ... | _ | no neq = ⊥-elim (neq refl)

  -- Every exact paired source row has a native event that decodes to that same row.
  decode-encode : ∀ row → decode (encode row) ≡ just row
  decode-encode (D.clientSend msg) rewrite command-record D.clientSend msg = endpoint-self cl cd (just (D.clientSend msg))
  decode-encode (D.serverRecv msg) rewrite command-record D.serverRecv msg = endpoint-self sl sd (just (D.serverRecv msg))
  decode-encode (D.serverSend msg) rewrite response-record D.serverSend msg = endpoint-self sl sd (just (D.serverSend msg))
  decode-encode (D.clientRecv msg) rewrite response-record D.clientRecv msg = endpoint-self cl cd (just (D.clientRecv msg))

  -- Distinct actors, record directions or selected payloads cannot collapse in encoding.
  encode-injective : ∀ {a b} → encode a ≡ encode b → a ≡ b
  encode-injective {a} {b} eq = just-injective
    (trans (sym (decode-encode a)) (trans (cong decode eq) (decode-encode b)))

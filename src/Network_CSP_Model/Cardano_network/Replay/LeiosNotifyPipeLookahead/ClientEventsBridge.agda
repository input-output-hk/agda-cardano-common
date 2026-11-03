{-# OPTIONS --guardedness #-}

-- Exact native realization, partitioned into visible events and declared callbacks.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientEventsBridge (p : Params) (Return : Set) where

open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Data.Maybe.Properties using (just-injective)
open import Class.DecEq using (_≟_)
open import Cardano_network.Base using (Dir; FromInitiator; FromResponder)
open import Cardano_network.Data p
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyP p using (sendLNP; receiveLNP; apiLPev)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.ClientNetwork p Return as N
import Cardano_network.LeiosNotifyPipeLookahead.ClientEvents p Return N.Branches as E
import Cardano_network.LeiosNotifyPipeLookahead.ServerEvents p as Packets

-- Fixed endpoint realization preserves payloads while classifying erased operations.
module At (l : Link) (d : Dir) where
  open E.At l d

  -- Reflexive endpoint equality accepts every recognized client action.
  endpoint-self : ∀ action → endpoint l d action ≡ action
  endpoint-self action with l ≟ l | d ≟ d
  ... | yes _ | yes _ = refl
  ... | no neq | _ = ⊥-elim (neq refl)
  ... | _ | no neq = ⊥-elim (neq refl)

  -- Canonical request metadata passes the native initiator Send gate.
  outgoing-request : E.outgoing (Packets.packet FromInitiator MsgLNPRequestNext) ≡ just C.sendRequest
  outgoing-request with Packets.packet FromInitiator MsgLNPRequestNext ≟ Packets.packet FromInitiator MsgLNPRequestNext
  ... | yes _ = refl
  ... | no neq = ⊥-elim (neq refl)

  -- Canonical Quit has the same exact-metadata check and distinct action.
  outgoing-quit : E.outgoing (Packets.packet FromInitiator MsgLNPQuit) ≡ just C.sendQuit
  outgoing-quit with Packets.packet FromInitiator MsgLNPQuit ≟ Packets.packet FromInitiator MsgLNPQuit
  ... | yes _ = refl
  ... | no neq = ⊥-elim (neq refl)

  -- All five per-request reply kinds preserve their full exact payload.
  incoming-reply : ∀ reply → E.incoming (Packets.replyMessage reply) ≡ just (C.recvReply reply)
  incoming-reply (S.normal (announcement h)) = refl
  incoming-reply (S.normal (offer pt size)) = refl
  incoming-reply (S.normal (txsOffer pt)) = refl
  incoming-reply (S.normal (votes vs)) = refl
  incoming-reply S.canceled = refl

  -- The view makes callback erasure and native event realizability explicit alternatives.
  data View (a : C.Action) : Set₁ where
    quiet : E.Hidden a → observe a ≡ nothing → View a
    emitted : (event : N.LTS.Event) → observe a ≡ just event → decode event ≡ just a → View a

  -- Canonical request records recover their original source action.
  request-decodes : decode (N.LTS.evLabel _ (sendLNP l d) (Packets.packet FromInitiator MsgLNPRequestNext)) ≡ just C.sendRequest
  request-decodes rewrite outgoing-request = endpoint-self (just C.sendRequest)

  -- Canonical Quit records preserve the source's shutdown action.
  quit-decodes : decode (N.LTS.evLabel _ (sendLNP l d) (Packets.packet FromInitiator MsgLNPQuit)) ≡ just C.sendQuit
  quit-decodes rewrite outgoing-quit = endpoint-self (just C.sendQuit)

  -- Canonical receive events distinguish replies from the final Done response.
  reply-decodes : ∀ reply → decode
    (N.LTS.evLabel _ (receiveLNP l d) (Packets.packet FromResponder (Packets.replyMessage reply))) ≡
    just (C.recvReply reply)
  reply-decodes reply rewrite incoming-reply reply = endpoint-self (just (C.recvReply reply))

  -- Every source action is either explicitly hidden or realized by an exact native event.
  view : (a : C.Action) → View a
  view (C.continue _) = quiet E.checking refl
  view (C.terminate _) = quiet E.stopping refl
  view (C.handled S.canceled) = quiet E.canceledHandler refl
  view C.sendRequest = emitted _ refl request-decodes
  view C.sendQuit = emitted _ refl quit-decodes
  view C.recvDone = emitted _ refl (endpoint-self (just C.recvDone))
  view (C.recvReply reply) = emitted _ refl (reply-decodes reply)
  view (C.handled (S.normal (announcement h))) = emitted _ refl
    (endpoint-self (just (C.handled (S.normal (announcement h)))))
  view (C.handled (S.normal (offer pt size))) = emitted _ refl
    (endpoint-self (just (C.handled (S.normal (offer pt size)))))
  view (C.handled (S.normal (txsOffer pt))) = emitted _ refl
    (endpoint-self (just (C.handled (S.normal (txsOffer pt)))))
  view (C.handled (S.normal (votes vs))) = emitted _ refl
    (endpoint-self (just (C.handled (S.normal (votes vs)))))

  -- Every retained native event decodes to its exact source action and payload.
  decode-observe : ∀ {a e} → observe a ≡ just e → decode e ≡ just a
  decode-observe {a} observed with view a
  ... | quiet h erased with trans (sym erased) observed
  ...   | ()
  decode-observe {a} observed | emitted e canonical decoded
    with just-injective (trans (sym canonical) observed)
  ... | refl = decoded

  -- Visible observation cannot collapse distinct normal payloads or wire actions.
  observe-injective : ∀ {a b e} → observe a ≡ just e → observe b ≡ just e → a ≡ b
  observe-injective observedA observedB = just-injective
    (trans (sym (decode-observe observedA)) (decode-observe observedB))

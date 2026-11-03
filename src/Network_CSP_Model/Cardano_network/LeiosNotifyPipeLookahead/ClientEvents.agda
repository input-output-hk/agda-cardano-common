{-# OPTIONS --guardedness #-}

-- Native client observation: wire messages and successful normal API deliveries.
-- checkDone and successful generic Canceled handling are internal operations.
open import Cardano_network.Params using (Params)
module Cardano_network.LeiosNotifyPipeLookahead.ClientEvents
  (p : Params) (Return : Set) (I : Set → Set₁) where

open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Process_Trees using (ExtI)
open import Cardano_network.Base using (Dir; FromInitiator; FromResponder)
open import Cardano_network.Data p
open import Cardano_network.Net p
open import Cardano_network.LeiosNotifyP p using (LNPEv; sendLNP; receiveLNP; apiLPev)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.ServerEvents p as Packets
import Semantics.LTS {E = LNPEv} {I = I} as LTS

-- Only these successful source callback actions are hidden by this observation.
data Hidden : C.Action → Set where
  checking : ∀ {k} → Hidden (C.continue k)
  stopping : ∀ {x} → Hidden (C.terminate x)
  canceledHandler : Hidden (C.handled S.canceled)

-- The classifier prevents wire records and normal API deliveries becoming silent.
classify : (a : C.Action) → Maybe (Hidden a)
classify (C.continue _) = just checking
classify (C.terminate _) = just stopping
classify (C.handled S.canceled) = just canceledHandler
classify _ = nothing

-- The per-request receiver accepts normal replies and cancellation, never commands.
replyOf : MessageLeiosNotifyP → Maybe S.Reply
replyOf (MsgLNPBlockAnnouncement h) = just (S.normal (announcement h))
replyOf (MsgLNPBlockOffer pt size) = just (S.normal (offer pt size))
replyOf (MsgLNPBlockTxsOffer pt) = just (S.normal (txsOffer pt))
replyOf (MsgLNPVotes vs) = just (S.normal (votes vs))
replyOf MsgLNPCanceled = just S.canceled
replyOf _ = nothing

-- Done is received by the main thread after the response receivers are drained.
incoming : MessageLeiosNotifyP → Maybe C.Action
incoming MsgLNPDone = just C.recvDone
incoming msg = map C.recvReply (replyOf msg)

-- Only canonical initiator RequestNext and Quit packets are client Send records.
outgoing : Payload → Maybe C.Action
outgoing value@(_ , _ , _ , leiosNotifyP msg) with value ≟ Packets.packet FromInitiator msg
... | no _ = nothing
... | yes _ with msg
...   | MsgLNPRequestNext = just C.sendRequest
...   | MsgLNPQuit = just C.sendQuit
...   | _ = nothing
outgoing _ = nothing

-- Native decode is fixed to one endpoint and preserves exact normal-handler payloads.
module At (l : Link) (d : Dir) where
  -- A record from another endpoint cannot operate this local client.
  endpoint : Link → Dir → Maybe C.Action → Maybe C.Action
  endpoint l′ d′ action with l′ ≟ l | d′ ≟ d
  ... | yes _ | yes _ = action
  ... | _ | _ = nothing

  -- Existing unit request/quit APIs do not stand in for a checkDone result.
  decode : LTS.Event → Maybe C.Action
  decode (LTS.evLabel _ (sendLNP l′ d′) value) = endpoint l′ d′ (outgoing value)
  decode (LTS.evLabel _ (receiveLNP l′ d′) (_ , FromResponder , _ , leiosNotifyP msg)) =
    endpoint l′ d′ (incoming msg)
  decode (LTS.evLabel _ (apiLPev l′ d′ lnpRecvBlockAnnouncement) h) =
    endpoint l′ d′ (just (C.handled (S.normal (announcement h))))
  decode (LTS.evLabel _ (apiLPev l′ d′ lnpRecvBlockOffer) (pt , size)) =
    endpoint l′ d′ (just (C.handled (S.normal (offer pt size))))
  decode (LTS.evLabel _ (apiLPev l′ d′ lnpRecvBlockTxsOffer) pt) =
    endpoint l′ d′ (just (C.handled (S.normal (txsOffer pt))))
  decode (LTS.evLabel _ (apiLPev l′ d′ lnpRecvVotes) vs) =
    endpoint l′ d′ (just (C.handled (S.normal (votes vs))))
  decode _ = nothing

  -- Canonical representatives erase precisely the declared callback choices.
  observe : C.Action → Maybe LTS.Event
  observe (C.continue _) = nothing
  observe (C.terminate _) = nothing
  observe (C.handled S.canceled) = nothing
  observe C.sendRequest = just (LTS.evLabel _ (sendLNP l d) (Packets.packet FromInitiator MsgLNPRequestNext))
  observe C.sendQuit = just (LTS.evLabel _ (sendLNP l d) (Packets.packet FromInitiator MsgLNPQuit))
  observe C.recvDone = just (LTS.evLabel _ (receiveLNP l d) (Packets.packet FromResponder MsgLNPDone))
  observe (C.recvReply reply) =
    just (LTS.evLabel _ (receiveLNP l d) (Packets.packet FromResponder (Packets.replyMessage reply)))
  observe (C.handled (S.normal (announcement h))) = just (LTS.evLabel _ (apiLPev l d lnpRecvBlockAnnouncement) h)
  observe (C.handled (S.normal (offer pt size))) = just (LTS.evLabel _ (apiLPev l d lnpRecvBlockOffer) (pt , size))
  observe (C.handled (S.normal (txsOffer pt))) = just (LTS.evLabel _ (apiLPev l d lnpRecvBlockTxsOffer) pt)
  observe (C.handled (S.normal (votes vs))) = just (LTS.evLabel _ (apiLPev l d lnpRecvVotes) vs)

  -- Projection preserves native event order and keeps every normal delivery and wire row.
  project : List C.Action → List LTS.Event
  project [] = []
  project (a ∷ as) with observe a
  ... | nothing = project as
  ... | just e = e ∷ project as

{-# OPTIONS --guardedness #-}

-- Canonical native representatives of the source server's exact visible actions.
-- Observation proofs belong to Replay; this module imports only protocol definitions.
open import Cardano_network.Params using (Params)
module Cardano_network.LeiosNotifyPipeLookahead.ServerEvents (p : Params) where

open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Process_Trees using (ExtI)
open import Cardano_network.Base using (Dir; Mode; FromInitiator; FromResponder)
open import Cardano_network.Data p
open import Cardano_network.Net p
open import Cardano_network.LeiosNotifyP p using (LNPEv; receiveLNP; sendLNP; apiLPev)
import Cardano_network.LeiosNotifyPipe p as Payloads
open import Cardano_network.LeiosNotifyPipeLookahead.Model Payloads.Notification
open Params p
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS

-- Replies keep all application payloads, including vote order and duplicates.
replyMessage : Reply → MessageLeiosNotifyP
replyMessage (normal m) = Payloads.message m
replyMessage canceled = MsgLNPCanceled

-- Canonical metadata chooses representatives without changing retained message fields.
packet : Mode → MessageLeiosNotifyP → Payload
packet mode msg = time₀ , mode , length₀ , leiosNotifyP msg

-- Fixed endpoint representatives preserve every source action without omitting APIs.
encode : Link → Dir → Action → LTS.Event
encode l d recvRequest = LTS.evLabel _ (receiveLNP l d) (packet FromInitiator MsgLNPRequestNext)
encode l d recvQuit = LTS.evLabel _ (receiveLNP l d) (packet FromInitiator MsgLNPQuit)
encode l d sendDone = LTS.evLabel _ (sendLNP l d) (packet FromResponder MsgLNPDone)
encode l d (sendReply reply) = LTS.evLabel _ (sendLNP l d) (packet FromResponder (replyMessage reply))
encode l d (nextReply (normal (Payloads.announcement h))) =
  LTS.evLabel _ (apiLPev l d lnpSendBlockAnnouncement) h
encode l d (nextReply (normal (Payloads.offer pt size))) =
  LTS.evLabel _ (apiLPev l d lnpSendBlockOffer) (pt , size)
encode l d (nextReply (normal (Payloads.txsOffer pt))) =
  LTS.evLabel _ (apiLPev l d lnpSendBlockTxsOffer) pt
encode l d (nextReply (normal (Payloads.votes votes))) =
  LTS.evLabel _ (apiLPev l d lnpSendVotes) votes
encode l d (nextReply canceled) = LTS.evLabel _ (apiLPev l d lnpSendCanceled) tt

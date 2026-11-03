{-# OPTIONS --guardedness #-}

-- Source-aligned lookahead producer for consensus 2416493 and driver 9b46272.
-- Wire labels describe local driver records, not channel-commit events.
open import Cardano_network.Params using (Params)
module Cardano_network.LeiosNotifyPipeLookahead (p : Params) where

open import Data.Nat using (ℕ)
import Data.Nat.Properties as Nat
open import Data.Bool using (Bool; true; false)
open import Data.List using (length)
import Data.List as List
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_,_; proj₁)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Process_Trees using (PTree; ExtI; AnyTypes; ContinueType; ret; react; fin)
open import Cardano_network.Base using (Dir; FromInitiator; FromResponder)
open import Cardano_network.Data p
open import Cardano_network.Net p
open import Cardano_network.LeiosNotifyP p using (LNPEv; receiveLNP; sendLNP; apiLPev)
import Cardano_network.LeiosNotifyPipeLookahead.Model
import Cardano_network.LeiosNotifyPipeLookahead.ClientTree
import Cardano_network.LeiosNotifyPipeLookahead.DriverTree
import Cardano_network.LeiosNotifyPipeLookahead.ClientNetwork
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork
import Cardano_network.LeiosNotifyPipe p as Old
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as LTS
open Params p

-- Native notification constructors preserve all selected application payloads.
open Old using (Notification; announcement; offer; txsOffer; votes; message)

-- Shared payload equality keeps the existing public names and definitions.
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
  using (message-injective; notificationEq) public

-- The operational reference remains independent of process-tree semantics.
module Reference = Cardano_network.LeiosNotifyPipeLookahead.Model Notification

-- The tree uses the same proof-carrying visible lookup as the reference rules.
module Execute = Reference.Executable notificationEq

-- Admission failure is an abnormal result, never a successful Done exchange.
data Result : Set where
  success excessiveRequests : Result

-- This producer preserves the native network alphabet with an explicit result.
Proc : Set₁
Proc = PTree LNPEv (ExtI LNPEv) Result

-- Fixed link/direction and callback contract select one peer instance.
module Machine (contract : Reference.Contract) (l : Link) (d : Dir) where
  -- Other endpoints cannot operate this local state machine.
  endpoint : Link → Dir → Maybe Reference.Action → Maybe Reference.Action
  endpoint l′ d′ action with l′ ≟ l | d′ ≟ d
  ... | yes _ | yes _ = action
  ... | _ | _ = nothing

  -- Ordinary responder messages and Canceled are the only per-request replies.
  replyOf : MessageLeiosNotifyP → Maybe Reference.Reply
  replyOf (MsgLNPBlockAnnouncement h) = just (Reference.normal (announcement h))
  replyOf (MsgLNPBlockOffer pt sz) = just (Reference.normal (offer pt sz))
  replyOf (MsgLNPBlockTxsOffer pt) = just (Reference.normal (txsOffer pt))
  replyOf (MsgLNPVotes vs) = just (Reference.normal (votes vs))
  replyOf MsgLNPCanceled = just Reference.canceled
  replyOf _ = nothing

  -- Send metadata is canonical, as in the existing bounded peer.
  packet : MessageLeiosNotifyP → Payload
  packet m = time₀ , FromResponder , length₀ , leiosNotifyP m

  -- Sending retains the exact selected native message and responder agency.
  outgoing : Payload → Maybe Reference.Action
  outgoing a@(_ , _ , _ , leiosNotifyP m) with a ≟ packet m
  ... | no _ = nothing
  ... | yes _ with m
  ...   | MsgLNPDone = just Reference.sendDone
  ...   | other = map Reference.sendReply (replyOf other)
  outgoing _ = nothing

  -- API reply readiness and wire operations are separate observable channels.
  decode : LTS.Event → Maybe Reference.Action
  decode (LTS.evLabel _ (receiveLNP l′ d′) (_ , FromInitiator , _ , leiosNotifyP MsgLNPRequestNext)) =
    endpoint l′ d′ (just Reference.recvRequest)
  decode (LTS.evLabel _ (receiveLNP l′ d′) (_ , FromInitiator , _ , leiosNotifyP MsgLNPQuit)) =
    endpoint l′ d′ (just Reference.recvQuit)
  decode (LTS.evLabel _ (sendLNP l′ d′) a) = endpoint l′ d′ (outgoing a)
  decode (LTS.evLabel _ (apiLPev l′ d′ lnpSendBlockAnnouncement) h) =
    endpoint l′ d′ (just (Reference.nextReply (Reference.normal (announcement h))))
  decode (LTS.evLabel _ (apiLPev l′ d′ lnpSendBlockOffer) (pt , sz)) =
    endpoint l′ d′ (just (Reference.nextReply (Reference.normal (offer pt sz))))
  decode (LTS.evLabel _ (apiLPev l′ d′ lnpSendBlockTxsOffer) pt) =
    endpoint l′ d′ (just (Reference.nextReply (Reference.normal (txsOffer pt))))
  decode (LTS.evLabel _ (apiLPev l′ d′ lnpSendVotes) vs) =
    endpoint l′ d′ (just (Reference.nextReply (Reference.normal (votes vs))))
  decode (LTS.evLabel _ (apiLPev l′ d′ lnpSendCanceled) _) =
    endpoint l′ d′ (just (Reference.nextReply Reference.canceled))
  decode _ = nothing

  -- The executable state transition preserves its operational Step witness.
  next : Reference.State → LTS.Event → Maybe Reference.State
  next s e with decode e
  ... | nothing = nothing
  ... | just a = Execute.next contract s a

  -- Internal branch decoding is computed before constructing a continuation.
  internalNext : (s : Reference.State) (at : AnyTypes (ExtI LNPEv)) →
    ContinueType at (Maybe Reference.State)
  internalNext s (_ , fin {n = n}) (lift i) with n Nat.≟ length (Reference.internalMoves s)
  ... | yes refl = just (proj₁ (List.lookup (Reference.internalMoves s) i))
  ... | no _ = nothing
  internalNext _ _ _ = nothing

  -- Forward declarations keep the coinductive tree productive.
  tree : Reference.State → Proc
  offers : (s : Reference.State) (at : AnyTypes LNPEv) → ContinueType at (Maybe Proc)
  branches : (s : Reference.State) (at : AnyTypes (ExtI LNPEv)) → ContinueType at (Maybe Proc)

  -- Both visible operations and scheduling steps coexist in one react node.
  PTree.force (tree (Reference.state Reference.closed _ _ _ _)) = ret success
  PTree.force (tree (Reference.state Reference.failed _ _ _ _)) = ret excessiveRequests
  PTree.force (tree s) = react (offers s) (branches s)

  -- Pending sends do not remove the independent reader's receive offers.
  offers s (X , ch) value with next s (LTS.evLabel X ch value)
  ... | nothing = nothing
  ... | just t = just (tree t)

  -- Exactly the finite list of operational hidden choices is exposed internally.
  branches s at value with internalNext s at value
  ... | nothing = nothing
  ... | just t = just (tree t)

-- Source-level lookahead server, with no invented symmetric wire-credit bound.
server : Reference.Contract → Link → Dir → Proc
server contract l d = Machine.tree contract l d Reference.initial

-- The detailed client exposes exact source operations; LNPEv lifting remains separate.
module PipelinedClient (Return : Set) =
  Cardano_network.LeiosNotifyPipeLookahead.ClientTree Notification Return notificationEq

-- The paired source tree uses endpoint-tagged driver records and hidden channel commits.
module PairedDriver (Return : Set) =
  Cardano_network.LeiosNotifyPipeLookahead.DriverTree Notification Return notificationEq

-- The native client uses LNPEv and keeps dynamic checkDone results as internal choices.
module NetworkClient (Return : Set) =
  Cardano_network.LeiosNotifyPipeLookahead.ClientNetwork p Return

-- Fresh native pipelined client with the caller's exact return carrier.
client : (Return : Set) → Link → Dir → NetworkClient.Proc Return
client Return l d = NetworkClient.At.client Return l d

-- The native paired driver retains hidden commits and endpoint-tagged wire records.
module NetworkDriver (Return : Set) =
  Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork p Return

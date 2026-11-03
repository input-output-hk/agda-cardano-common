{-# OPTIONS --guardedness #-}

-- Native paired driver product: hidden channel commits precede visible trace records.
-- Endpoint tags wrap existing LNPEv channels; APIs are hidden at this wire profile.
open import Cardano_network.Params using (Params)
module Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork (p : Params) (Return : Set) where

open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Data.Empty using (⊥)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import Process_Trees using (PTree; AnyTypes; ContinueType; react)
open import Cardano_network.Base using (Dir; FromInitiator; FromResponder)
open import Cardano_network.Data p
open import Cardano_network.Net p using (Link)
open import Cardano_network.LeiosNotifyP p using (LNPEv; sendLNP; receiveLNP)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications p
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution Notification Return notificationEq as Exec
import Cardano_network.LeiosNotifyPipeLookahead.ServerEvents p as Packets
import Semantics.LTS
import Semantics.Deadlock

-- Native message representations preserve the entire selected application payload.
clientMessage : D.ClientMessage → MessageLeiosNotifyP
clientMessage D.request = MsgLNPRequestNext
clientMessage D.quit = MsgLNPQuit

-- Replies and final Done retain their distinct responder message constructors.
serverMessage : D.ServerMessage → MessageLeiosNotifyP
serverMessage (D.reply r) = Packets.replyMessage r
serverMessage D.done = MsgLNPDone

-- Canonical initiator packets are shared by commit, Send and receive realization.
clientPacket : D.ClientMessage → Payload
clientPacket msg = Packets.packet FromInitiator (clientMessage msg)

-- The same full responder packet is shared at both endpoints.
serverPacket : D.ServerMessage → Payload
serverPacket msg = Packets.packet FromResponder (serverMessage msg)

-- Packet decoding returns an equality certificate for the complete native envelope.
checkedPacket : ∀ {Message : Set} (encode : Message → Payload) (msg : Message) (value : Payload) →
  Maybe (Σ[ decoded ∈ Message ] value ≡ encode decoded)
checkedPacket encode msg value with value ≟ encode msg
... | yes eq = just (msg , eq)
... | no _ = nothing

-- Only properly tagged native requests and Quit can decode as initiator packets.
commands : (value : Payload) → Maybe (Σ[ msg ∈ D.ClientMessage ] value ≡ clientPacket msg)
commands value@(_ , FromInitiator , _ , leiosNotifyP MsgLNPRequestNext) = checkedPacket clientPacket D.request value
commands value@(_ , FromInitiator , _ , leiosNotifyP MsgLNPQuit) = checkedPacket clientPacket D.quit value
commands _ = nothing

-- Reply payloads, order and duplicates are retained before any paired transition runs.
responses : (value : Payload) → Maybe (Σ[ msg ∈ D.ServerMessage ] value ≡ serverPacket msg)
responses value@(_ , FromResponder , _ , leiosNotifyP (MsgLNPBlockAnnouncement h)) =
  checkedPacket serverPacket (D.reply (S.normal (announcement h))) value
responses value@(_ , FromResponder , _ , leiosNotifyP (MsgLNPBlockOffer pt size)) =
  checkedPacket serverPacket (D.reply (S.normal (offer pt size))) value
responses value@(_ , FromResponder , _ , leiosNotifyP (MsgLNPBlockTxsOffer pt)) =
  checkedPacket serverPacket (D.reply (S.normal (txsOffer pt))) value
responses value@(_ , FromResponder , _ , leiosNotifyP (MsgLNPVotes vs)) =
  checkedPacket serverPacket (D.reply (S.normal (votes vs))) value
responses value@(_ , FromResponder , _ , leiosNotifyP MsgLNPCanceled) =
  checkedPacket serverPacket (D.reply S.canceled) value
responses value@(_ , FromResponder , _ , leiosNotifyP MsgLNPDone) = checkedPacket serverPacket D.done value
responses _ = nothing

-- Explicit actor tags prevent accidentally merging distinct endpoint log records.
data Events (A : Set) : Set where
  atClient atServer : LNPEv A → Events A

-- The product retains data-only selectors for callbacks, decode, commits and scheduling.
data Branches : Set → Set₁ where
  schedule : Branches Exec.Choice

-- Paired prefix semantics retains endpoint return values in state and has no global tick.
Proc : Set₁
Proc = PTree Events Branches ⊥

-- Native paired labels use their own explicit endpoint-tagged alphabet.
module LTS = Semantics.LTS {E = Events} {I = Branches}
module Traces = Semantics.Deadlock {E = Events} {I = Branches}

-- Both endpoint coordinates are explicit, as in the existing paired model interface.
module At (contract : S.Contract) (cl sl : Link) (cd sd : Dir) where
  -- Recognized local rows cannot migrate to another link or direction.
  endpoint : Link → Dir → Link → Dir → Maybe D.Event → Maybe D.Event
  endpoint observedLink observedDir expectedLink expectedDir event
    with observedLink ≟ expectedLink | observedDir ≟ expectedDir
  ... | yes _ | yes _ = event
  ... | _ | _ = nothing

  -- The raw-driver observation includes exactly wire records, with canonical full packets.
  decode : LTS.Event → Maybe D.Event
  decode (LTS.evLabel _ (atClient (sendLNP l d)) value) =
    endpoint l d cl cd (map (λ x → D.clientSend (proj₁ x)) (commands value))
  decode (LTS.evLabel _ (atClient (receiveLNP l d)) value) =
    endpoint l d cl cd (map (λ x → D.clientRecv (proj₁ x)) (responses value))
  decode (LTS.evLabel _ (atServer (sendLNP l d)) value) =
    endpoint l d sl sd (map (λ x → D.serverSend (proj₁ x)) (responses value))
  decode (LTS.evLabel _ (atServer (receiveLNP l d)) value) =
    endpoint l d sl sd (map (λ x → D.serverRecv (proj₁ x)) (commands value))
  decode _ = nothing

  -- Canonical native realization retains each actor, record direction and full packet.
  encode : D.Event → LTS.Event
  encode (D.clientSend msg) = LTS.evLabel _ (atClient (sendLNP cl cd)) (clientPacket msg)
  encode (D.clientRecv msg) = LTS.evLabel _ (atClient (receiveLNP cl cd)) (serverPacket msg)
  encode (D.serverSend msg) = LTS.evLabel _ (atServer (sendLNP sl sd)) (serverPacket msg)
  encode (D.serverRecv msg) = LTS.evLabel _ (atServer (receiveLNP sl sd)) (clientPacket msg)

  -- Visible trace hooks advance their endpoint only after a matching pending record.
  next : D.State → LTS.Event → Maybe D.State
  next state event with decode event
  ... | nothing = nothing
  ... | just row = Exec.next contract state row

  -- Forward declarations keep visible record offers and hidden transport progress concurrent.
  tree : D.State → Proc
  offers : (state : D.State) (at : AnyTypes Events) → ContinueType at (Maybe Proc)
  branches : (state : D.State) (at : AnyTypes Branches) → ContinueType at (Maybe Proc)

  -- A prefix product remains reactive even when its endpoint states have returned.
  PTree.force (tree state) = react (offers state) (branches state)

  -- Record emission uses the original certified paired visible transition.
  offers state (X , channel) value with next state (LTS.evLabel X channel value)
  ... | nothing = nothing
  ... | just target = just (tree target)

  -- Hidden commits and decodes update FIFOs independently of later record emission.
  branches state (_ , schedule) choice with Exec.hidden contract state choice
  ... | nothing = nothing
  ... | just (target , pr) = just (tree target)

  -- Fresh paired execution starts with both peers initial and all transport/records empty.
  driver : Proc
  driver = tree D.initial

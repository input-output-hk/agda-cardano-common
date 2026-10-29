{-# OPTIONS --guardedness #-}

-- Compatible erased payload witnesses for both original TxSubmission2 peers.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.TxSubmission2PairedCanonical (p : Params) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; _∷ʳ_; map)
open import Data.List.Properties using (map-++)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Maybe using (just)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong)
open import Class.DecEq using (_≟_)
open import Cardano_network.Base
open import Cardano_network.Data p
open import Cardano_network.Net p using (Link)
open Params p
open import Cardano_network.Replay.Common
open import Cardano_network.Replay.TxSubmission2PairedModel p using (queues)
open import Cardano_network.Replay.TxSubmission2PairedPackets p using (Packet; packets; clientPacket; serverPacket)
import Cardano_network.Replay.TxSubmission2Session as T
open T using (init; requestBlocking; requestNonBlocking; replyIdsEmpty;
  replyIdsNonEmpty; requestTxs; replyTxs; doneK)
import Cardano_network.Replay.TxSubmission2StepView as View
import Cardano_network.Replay.TxSubmission2PairedSession as Paired
import Cardano_network.Replay.TxSubmission2ClientBridge p as C
import Cardano_network.Replay.TxSubmission2ServerBridge p as S

module _ (h₀ : TxHash) where
  -- A shared canonical message for each control kind, independent of endpoint.
  message : T.Kind → MessageTxSubmission2
  message T.init = MsgTSInit
  message T.requestBlocking = MsgTSRequestTxIds Blocking 0 1
  message T.requestNonBlocking = MsgTSRequestTxIds NonBlocking 0 1
  message T.replyIdsEmpty = MsgTSReplyTxIds []
  message T.replyIdsNonEmpty = MsgTSReplyTxIds (h₀ ∷ [])
  message T.requestTxs = MsgTSRequestTxs []
  message T.replyTxs = MsgTSReplyTxs []
  message T.doneK = MsgTSDone

  -- The submitter initiates the protocol but the server sends all requests.
  sender : T.Kind → Mode
  sender T.requestBlocking = FromResponder
  sender T.requestNonBlocking = FromResponder
  sender T.requestTxs = FromResponder
  sender _ = FromInitiator

  -- Full time, mode, length and message payload agree at send and receive.
  payload : T.Kind → Payload
  payload m = time₀ , sender m , length₀ , txSubmission (message m)

  -- A local event's concrete packet uses the shared payload witness.
  packet : T.E → Packet
  packet (d , m) = d , payload m

  -- Canonical payload queues retain the exact abstract FIFO ordering.
  queue : List T.Kind → List Payload
  queue = map payload

  -- Both endpoints make the same reflexive receive-equality decision.
  client-receive : ∀ m cs sc → clientPacket (Recv , payload m)
    (queues (queue cs) (payload m ∷ queue sc)) ≡ just (queues (queue cs) (queue sc))
  client-receive m cs sc with payload m ≟ payload m
  ... | yes _ = refl
  ... | no bad = ⊥-elim (bad refl)

  -- The corresponding equality for a server-consuming request.
  server-receive : ∀ m cs sc → serverPacket (Recv , payload m)
    (queues (payload m ∷ queue cs) (queue sc)) ≡ just (queues (queue cs) (queue sc))
  server-receive m cs sc with payload m ≟ payload m
  ... | yes _ = refl
  ... | no bad = ⊥-elim (bad refl)

  module _ (k : ℕ) where
    module R = Paired k

    -- Every abstract client step passes the corresponding full-payload gate.
    client-gate : ∀ {c s c′ s′ cs sc cs′ sc′ e} →
      R.Step (R.paired c s cs sc) (client , e) (R.paired c′ s′ cs′ sc′) →
      clientPacket (packet e) (queues (queue cs) (queue sc)) ≡ just (queues (queue cs′) (queue sc′))
    client-gate (R.clientSend {cs = cs} {m = m} pr) = cong (λ qs → just (queues qs _)) (sym (map-++ payload cs (m ∷ [])))
    client-gate (R.clientRecv {cs = cs} {sc = sc} {m = m} pr) = client-receive m cs sc

    -- The server gate uses the identical canonical payloads in the other direction.
    server-gate : ∀ {c s c′ s′ cs sc cs′ sc′ e} →
      R.Step (R.paired c s cs sc) (server , e) (R.paired c′ s′ cs′ sc′) →
      serverPacket (packet e) (queues (queue cs) (queue sc)) ≡ just (queues (queue cs′) (queue sc′))
    server-gate (R.serverSend {sc = sc} {m = m} pr) = cong (λ qs → just (queues _ qs)) (sym (map-++ payload sc (m ∷ [])))
    server-gate (R.serverRecv {cs = cs} {sc = sc} {m = m} pr) = server-receive m cs sc

    module _ (l : Link) (d : Dir) where
      -- Each existing submitter completeness macro uses the shared full packet.
      client-packet : ∀ {T s s′ e} (r : C.RelC k l d T s) (pr : T.Spec.Step k client s e s′) →
        packets (proj₁ (proj₂ (C.co-ev k l d h₀ r tt pr))) ≡ packet e ∷ []
      client-packet {e = Send , init} C.cstInit refl = refl
      client-packet {e = Send , requestBlocking} C.cstInit ()
      client-packet {e = Send , requestNonBlocking} C.cstInit ()
      client-packet {e = Send , replyIdsEmpty} C.cstInit ()
      client-packet {e = Send , replyIdsNonEmpty} C.cstInit ()
      client-packet {e = Send , requestTxs} C.cstInit ()
      client-packet {e = Send , replyTxs} C.cstInit ()
      client-packet {e = Send , doneK} C.cstInit ()
      client-packet {e = Recv , init} C.cstInit ()
      client-packet {e = Recv , requestBlocking} C.cstInit ()
      client-packet {e = Recv , requestNonBlocking} C.cstInit ()
      client-packet {e = Recv , replyIdsEmpty} C.cstInit ()
      client-packet {e = Recv , replyIdsNonEmpty} C.cstInit ()
      client-packet {e = Recv , requestTxs} C.cstInit ()
      client-packet {e = Recv , replyTxs} C.cstInit ()
      client-packet {e = Recv , doneK} C.cstInit ()
      client-packet {e = Send , init} C.cstIdle ()
      client-packet {e = Send , requestBlocking} C.cstIdle ()
      client-packet {e = Send , requestNonBlocking} C.cstIdle ()
      client-packet {e = Send , replyIdsEmpty} C.cstIdle ()
      client-packet {e = Send , replyIdsNonEmpty} C.cstIdle ()
      client-packet {e = Send , requestTxs} C.cstIdle ()
      client-packet {e = Send , replyTxs} C.cstIdle ()
      client-packet {e = Send , doneK} C.cstIdle ()
      client-packet {e = Recv , init} C.cstIdle ()
      client-packet {e = Recv , requestBlocking} C.cstIdle refl = refl
      client-packet {e = Recv , requestNonBlocking} C.cstIdle refl = refl
      client-packet {e = Recv , replyIdsEmpty} C.cstIdle ()
      client-packet {e = Recv , replyIdsNonEmpty} C.cstIdle ()
      client-packet {e = Recv , requestTxs} C.cstIdle refl = refl
      client-packet {e = Recv , replyTxs} C.cstIdle ()
      client-packet {e = Recv , doneK} C.cstIdle ()
      client-packet {e = Send , init} C.cstTxIdsBlocking ()
      client-packet {e = Send , requestBlocking} C.cstTxIdsBlocking ()
      client-packet {e = Send , requestNonBlocking} C.cstTxIdsBlocking ()
      client-packet {e = Send , replyIdsEmpty} C.cstTxIdsBlocking ()
      client-packet {e = Send , replyIdsNonEmpty} C.cstTxIdsBlocking refl = refl
      client-packet {e = Send , requestTxs} C.cstTxIdsBlocking ()
      client-packet {e = Send , replyTxs} C.cstTxIdsBlocking ()
      client-packet {e = Send , doneK} C.cstTxIdsBlocking refl = refl
      client-packet {e = Recv , init} C.cstTxIdsBlocking ()
      client-packet {e = Recv , requestBlocking} C.cstTxIdsBlocking ()
      client-packet {e = Recv , requestNonBlocking} C.cstTxIdsBlocking ()
      client-packet {e = Recv , replyIdsEmpty} C.cstTxIdsBlocking ()
      client-packet {e = Recv , replyIdsNonEmpty} C.cstTxIdsBlocking ()
      client-packet {e = Recv , requestTxs} C.cstTxIdsBlocking ()
      client-packet {e = Recv , replyTxs} C.cstTxIdsBlocking ()
      client-packet {e = Recv , doneK} C.cstTxIdsBlocking ()
      client-packet {e = Send , init} C.cstTxIdsNonBlocking ()
      client-packet {e = Send , requestBlocking} C.cstTxIdsNonBlocking ()
      client-packet {e = Send , requestNonBlocking} C.cstTxIdsNonBlocking ()
      client-packet {e = Send , replyIdsEmpty} C.cstTxIdsNonBlocking refl = refl
      client-packet {e = Send , replyIdsNonEmpty} C.cstTxIdsNonBlocking refl = refl
      client-packet {e = Send , requestTxs} C.cstTxIdsNonBlocking ()
      client-packet {e = Send , replyTxs} C.cstTxIdsNonBlocking ()
      client-packet {e = Send , doneK} C.cstTxIdsNonBlocking ()
      client-packet {e = Recv , init} C.cstTxIdsNonBlocking ()
      client-packet {e = Recv , requestBlocking} C.cstTxIdsNonBlocking ()
      client-packet {e = Recv , requestNonBlocking} C.cstTxIdsNonBlocking ()
      client-packet {e = Recv , replyIdsEmpty} C.cstTxIdsNonBlocking ()
      client-packet {e = Recv , replyIdsNonEmpty} C.cstTxIdsNonBlocking ()
      client-packet {e = Recv , requestTxs} C.cstTxIdsNonBlocking ()
      client-packet {e = Recv , replyTxs} C.cstTxIdsNonBlocking ()
      client-packet {e = Recv , doneK} C.cstTxIdsNonBlocking ()
      client-packet {e = Send , init} C.cstTxs ()
      client-packet {e = Send , requestBlocking} C.cstTxs ()
      client-packet {e = Send , requestNonBlocking} C.cstTxs ()
      client-packet {e = Send , replyIdsEmpty} C.cstTxs ()
      client-packet {e = Send , replyIdsNonEmpty} C.cstTxs ()
      client-packet {e = Send , requestTxs} C.cstTxs ()
      client-packet {e = Send , replyTxs} C.cstTxs refl = refl
      client-packet {e = Send , doneK} C.cstTxs ()
      client-packet {e = Recv , init} C.cstTxs ()
      client-packet {e = Recv , requestBlocking} C.cstTxs ()
      client-packet {e = Recv , requestNonBlocking} C.cstTxs ()
      client-packet {e = Recv , replyIdsEmpty} C.cstTxs ()
      client-packet {e = Recv , replyIdsNonEmpty} C.cstTxs ()
      client-packet {e = Recv , requestTxs} C.cstTxs ()
      client-packet {e = Recv , replyTxs} C.cstTxs ()
      client-packet {e = Recv , doneK} C.cstTxs ()
      client-packet {e = Send , init} C.cstDone ()
      client-packet {e = Send , requestBlocking} C.cstDone ()
      client-packet {e = Send , requestNonBlocking} C.cstDone ()
      client-packet {e = Send , replyIdsEmpty} C.cstDone ()
      client-packet {e = Send , replyIdsNonEmpty} C.cstDone ()
      client-packet {e = Send , requestTxs} C.cstDone ()
      client-packet {e = Send , replyTxs} C.cstDone ()
      client-packet {e = Send , doneK} C.cstDone ()
      client-packet {e = Recv , init} C.cstDone ()
      client-packet {e = Recv , requestBlocking} C.cstDone ()
      client-packet {e = Recv , requestNonBlocking} C.cstDone ()
      client-packet {e = Recv , replyIdsEmpty} C.cstDone ()
      client-packet {e = Recv , replyIdsNonEmpty} C.cstDone ()
      client-packet {e = Recv , requestTxs} C.cstDone ()
      client-packet {e = Recv , replyTxs} C.cstDone ()
      client-packet {e = Recv , doneK} C.cstDone ()

      -- Requester macros use exactly the same request parameters and reply lists.
      server-packet : ∀ {T s s′ e} (r : S.RelC k l d T s) (v : View.View k s e s′) →
        packets (proj₁ (proj₂ (S.co-view k l d h₀ r v))) ≡ packet e ∷ []
      server-packet S.cInit View.start = refl
      server-packet (S.cHead S.emptyQ) View.block = refl
      server-packet (S.cHead S.emptyQ) (View.askIds lt) = refl
      server-packet (S.cHead (S.idsQ qs)) (View.askIds lt) = refl
      server-packet (S.cHead (S.txsQ qs)) (View.askIds lt) = refl
      server-packet (S.cHead S.emptyQ) (View.askTxs lt) = refl
      server-packet (S.cHead (S.idsQ qs)) (View.askTxs lt) = refl
      server-packet (S.cHead (S.txsQ qs)) (View.askTxs lt) = refl
      server-packet (S.cHead (S.idsQ qs)) View.emptyIds = refl
      server-packet (S.cHead (S.idsQ qs)) View.nonemptyIds = refl
      server-packet (S.cHead (S.txsQ qs)) View.transactions = refl
      server-packet S.cBlock View.unblock = refl
      server-packet S.cBlock View.close = refl
      server-packet S.cEnd ()

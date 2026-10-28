{-# OPTIONS --guardedness #-}

-- Shared exact-field native witnesses coordinate both endpoints and their FIFOs.
open import Cardano_network.Replay.LeiosNotifyExactParams renaming (exactParams to p)
module Cardano_network.Replay.LeiosNotifyExactCanonical where

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
open import Cardano_network.Params using (Params)
open Params p using (time₀; length₀)
open import Cardano_network.Data p
open import Cardano_network.Net p using (Link)
open import Cardano_network.Replay.Common
open import Cardano_network.Replay.LeiosNotifyPairedModel p using (queues)
open import Cardano_network.Replay.LeiosNotifyExactPackets using (Packet; packets; clientPacket; serverPacket)
import Cardano_network.Replay.LeiosNotifyPipeline as N
import Cardano_network.Replay.LeiosNotifyPairedSession as Paired
import Cardano_network.Replay.LeiosNotifyExactLocal as LocalBridge
import Cardano_network.Replay.LeiosNotifyExactObservation as O
open import Cardano_network.LeiosNotifyPipe p using (consumer; producer; openN; closed)
import Cardano_network.Replay.LeiosNotifySession as Log

-- Encode each retained field in its corresponding native message carrier.
message : N.Msg → MessageLeiosNotifyP
message Log.RequestNext = MsgLNPRequestNext
message (Log.BlockAnnouncement a) = MsgLNPBlockAnnouncement (header a)
message (Log.BlockOffer h s z) = MsgLNPBlockOffer (h , s) z
message (Log.BlockTxsOffer h s) = MsgLNPBlockTxsOffer (h , s)
message (Log.Votes vs) = MsgLNPVotes vs
message Log.Done = MsgLNPDone

-- The native mode is fixed by protocol agency and shared at both endpoints.
sender : N.Msg → Mode
sender Log.RequestNext = FromInitiator
sender Log.Done = FromInitiator
sender _ = FromResponder

-- Full time, mode, length and message payload agree at send and receive.
payload : N.Msg → Payload
payload m = time₀ , sender m , length₀ , leiosNotifyP (message m)

-- A local event's concrete packet uses the shared payload witness.
packet : N.E → Packet
packet (d , m) = d , payload m

-- Canonical payload queues retain the exact abstract FIFO ordering.
queue : List N.Msg → List Payload
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
    module B = LocalBridge k l d

    -- The exact local macro emits one shared packet, including its full envelope.
    one-packet : ∀ {r T q q′ e} (rel : B.CoRel r T q)
      (pr : N.Spec.Step k (B.role r) q e q′) →
      packets (proj₁ (proj₂ (B.coEv rel tt pr))) ≡ packet e ∷ []
    one-packet {consumer} {e = N.Send , Log.RequestNext} (B.headC {openN n}) pr with B.issue-inv n pr
    ... | credit , refl = refl
    one-packet {consumer} {e = N.Send , Log.Done} (B.headC {openN 0}) refl = refl
    one-packet {consumer} {e = N.Send , Log.Done} (B.headC {openN (suc n)}) ()
    one-packet {producer} {e = N.Recv , Log.RequestNext} (B.headC {openN n}) pr with B.issue-inv n pr
    ... | credit , refl = refl
    one-packet {producer} {e = N.Recv , Log.Done} (B.headC {openN 0}) refl = refl
    one-packet {producer} {e = N.Recv , Log.Done} (B.headC {openN (suc n)}) ()
    one-packet {consumer} {e = N.Recv , (Log.BlockAnnouncement x)} (B.headC {openN 0}) ()
    one-packet {consumer} {e = N.Recv , (Log.BlockAnnouncement x)} (B.headC {openN (suc n)}) refl = refl
    one-packet {consumer} {e = N.Recv , (Log.BlockOffer h sl z)} (B.headC {openN 0}) ()
    one-packet {consumer} {e = N.Recv , (Log.BlockOffer h sl z)} (B.headC {openN (suc n)}) refl = refl
    one-packet {consumer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (B.headC {openN 0}) ()
    one-packet {consumer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (B.headC {openN (suc n)}) refl = refl
    one-packet {consumer} {e = N.Recv , (Log.Votes vs)} (B.headC {openN 0}) ()
    one-packet {consumer} {e = N.Recv , (Log.Votes vs)} (B.headC {openN (suc n)}) refl = refl
    one-packet {producer} {e = N.Send , (Log.BlockAnnouncement x)} (B.headC {openN 0}) ()
    one-packet {producer} {e = N.Send , (Log.BlockAnnouncement x)} (B.headC {openN (suc n)}) refl = refl
    one-packet {producer} {e = N.Send , (Log.BlockOffer h sl z)} (B.headC {openN 0}) ()
    one-packet {producer} {e = N.Send , (Log.BlockOffer h sl z)} (B.headC {openN (suc n)}) refl = refl
    one-packet {producer} {e = N.Send , (Log.BlockTxsOffer h sl)} (B.headC {openN 0}) ()
    one-packet {producer} {e = N.Send , (Log.BlockTxsOffer h sl)} (B.headC {openN (suc n)}) refl = refl
    one-packet {producer} {e = N.Send , (Log.Votes vs)} (B.headC {openN 0}) ()
    one-packet {producer} {e = N.Send , (Log.Votes vs)} (B.headC {openN (suc n)}) refl = refl
    one-packet {consumer} {e = N.Recv , Log.RequestNext} (B.headC {openN 0}) ()
    one-packet {consumer} {e = N.Recv , Log.RequestNext} (B.headC {openN (suc n)}) ()
    one-packet {consumer} {e = N.Recv , Log.Done} (B.headC {openN 0}) ()
    one-packet {consumer} {e = N.Recv , Log.Done} (B.headC {openN (suc n)}) ()
    one-packet {producer} {e = N.Send , Log.RequestNext} (B.headC {openN 0}) ()
    one-packet {producer} {e = N.Send , Log.RequestNext} (B.headC {openN (suc n)}) ()
    one-packet {producer} {e = N.Send , Log.Done} (B.headC {openN 0}) ()
    one-packet {producer} {e = N.Send , Log.Done} (B.headC {openN (suc n)}) ()
    one-packet {consumer} {e = N.Send , (Log.BlockAnnouncement x)} (B.headC {openN 0}) ()
    one-packet {consumer} {e = N.Send , (Log.BlockAnnouncement x)} (B.headC {openN (suc n)}) ()
    one-packet {consumer} {e = N.Send , (Log.BlockOffer h sl z)} (B.headC {openN 0}) ()
    one-packet {consumer} {e = N.Send , (Log.BlockOffer h sl z)} (B.headC {openN (suc n)}) ()
    one-packet {consumer} {e = N.Send , (Log.BlockTxsOffer h sl)} (B.headC {openN 0}) ()
    one-packet {consumer} {e = N.Send , (Log.BlockTxsOffer h sl)} (B.headC {openN (suc n)}) ()
    one-packet {consumer} {e = N.Send , (Log.Votes vs)} (B.headC {openN 0}) ()
    one-packet {consumer} {e = N.Send , (Log.Votes vs)} (B.headC {openN (suc n)}) ()
    one-packet {producer} {e = N.Recv , (Log.BlockAnnouncement x)} (B.headC {openN 0}) ()
    one-packet {producer} {e = N.Recv , (Log.BlockAnnouncement x)} (B.headC {openN (suc n)}) ()
    one-packet {producer} {e = N.Recv , (Log.BlockOffer h sl z)} (B.headC {openN 0}) ()
    one-packet {producer} {e = N.Recv , (Log.BlockOffer h sl z)} (B.headC {openN (suc n)}) ()
    one-packet {producer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (B.headC {openN 0}) ()
    one-packet {producer} {e = N.Recv , (Log.BlockTxsOffer h sl)} (B.headC {openN (suc n)}) ()
    one-packet {producer} {e = N.Recv , (Log.Votes vs)} (B.headC {openN 0}) ()
    one-packet {producer} {e = N.Recv , (Log.Votes vs)} (B.headC {openN (suc n)}) ()
    one-packet {consumer} (B.headC {closed}) ()
    one-packet {producer} (B.headC {closed}) ()

-- Encoding and observing any parsed message is an exact field-for-field retraction.
observe-message : ∀ m → O.canonical (message m) ≡ m
observe-message Log.RequestNext = refl
observe-message (Log.BlockAnnouncement a) = refl
observe-message (Log.BlockOffer h s z) = refl
observe-message (Log.BlockTxsOffer h s) = refl
observe-message (Log.Votes vs) = refl
observe-message Log.Done = refl

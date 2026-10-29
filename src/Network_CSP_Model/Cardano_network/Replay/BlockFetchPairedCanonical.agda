{-# OPTIONS --guardedness #-}

-- Compatible erased payload witnesses for both original BlockFetch peers.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.BlockFetchPairedCanonical (p : Params) where

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
open import Cardano_network.Replay.BlockFetchPairedModel p using (queues)
open import Cardano_network.Replay.BlockFetchPairedPackets p using (Packet; packets; clientPacket; serverPacket)
import Cardano_network.Replay.BlockFetchClientSession as Ctl
import Cardano_network.Replay.BlockFetchServerSession as ServerCtl
import Cardano_network.Replay.BlockFetchPairedSession as Paired
import Cardano_network.Replay.BlockFetchClientBridge p as C
import Cardano_network.Replay.BlockFetchServerBridge p as S

module _ (b₀ : Block) where
  -- A shared canonical message for each control kind, independent of endpoint.
  message : Ctl.Kind → MessageBlockFetch
  message Ctl.request = MsgRequestRange (chainRange (point b₀) (point b₀))
  message Ctl.startBatch = MsgStartBatch
  message Ctl.noBlocks = MsgNoBlocks
  message Ctl.block = MsgBlock b₀
  message Ctl.batchDone = MsgBatchDone
  message Ctl.clientDone = MsgClientDone

  -- Range requests and ClientDone originate at the client; batches at the server.
  sender : Ctl.Kind → Mode
  sender Ctl.request = FromInitiator
  sender Ctl.clientDone = FromInitiator
  sender _ = FromResponder

  -- Full time, mode, length and message payload agree at send and receive.
  payload : Ctl.Kind → Payload
  payload m = time₀ , sender m , length₀ , blockFetch (message m)

  -- A local event's concrete packet uses the shared payload witness.
  packet : Ctl.E → Packet
  packet (d , m) = d , payload m

  -- Canonical payload queues retain the exact abstract FIFO ordering.
  queue : List Ctl.Kind → List Payload
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
      -- Client completeness macros use the shared range and block witnesses.
      client-packet : ∀ {T s s′ e} (r : C.RelC k l d T s) (pr : Ctl.Step k s e s′) →
        packets (proj₁ (proj₂ (C.co-ev k l d b₀ r tt pr))) ≡ packet e ∷ []
      client-packet (C.cWait qs) (Ctl.issue lt) = refl
      client-packet (C.cStream qs) (Ctl.issue lt) = refl
      client-packet (C.cWait C.emptyQ) Ctl.close = refl
      client-packet (C.cWait (C.consQ r qs)) Ctl.start = refl
      client-packet (C.cWait (C.consQ r qs)) Ctl.none = refl
      client-packet (C.cStream (C.consQ r qs)) Ctl.body = refl
      client-packet (C.cStream (C.consQ r qs)) Ctl.end = refl
      client-packet C.cEnd ()

      -- Server completeness emits precisely the corresponding concrete packet.
      server-packet : ∀ {T s s′ e} (r : S.RelC l d T s) (pr : ServerCtl.Step s e s′) →
        packets (proj₁ (proj₂ (S.co-ev l d b₀ r tt pr))) ≡ packet e ∷ []
      server-packet S.cIdle ServerCtl.receive = refl
      server-packet S.cIdle ServerCtl.close = refl
      server-packet S.cBusy ServerCtl.start = refl
      server-packet S.cBusy ServerCtl.none = refl
      server-packet S.cStreaming ServerCtl.body = refl
      server-packet S.cStreaming ServerCtl.end = refl
      server-packet S.cClosed ()

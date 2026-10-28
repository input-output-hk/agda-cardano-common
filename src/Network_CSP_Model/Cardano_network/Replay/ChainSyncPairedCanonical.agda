{-# OPTIONS --guardedness #-}

-- Compatible erased payload witnesses for both original ChainSync peers.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.ChainSyncPairedCanonical (p : Params) where

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
open import Cardano_network.Replay.ChainSyncPairedModel p using (queues)
open import Cardano_network.Replay.ChainSyncPairedPackets p using (Packet; packets; clientPacket; serverPacket)
import Cardano_network.Replay.ChainSyncSession as CS
import Cardano_network.Replay.ChainSyncStepView as View
import Cardano_network.Replay.ChainSyncPairedSession as Paired
import Cardano_network.Replay.ChainSyncClientBridge p as C
import Cardano_network.Replay.ChainSyncServerBridge p as S

module _ (b₀ : Block) where
  -- A shared canonical message for each control kind, independent of endpoint.
  message : CS.Kind → MessageChainSync
  message CS.requestNext = MsgCSRequestNext
  message CS.awaitReply = MsgCSAwaitReply
  message CS.rollForward = MsgCSRollForward (header b₀) (tip b₀)
  message CS.rollBackward = MsgCSRollBackward (point b₀) (tip b₀)
  message CS.findIntersect = MsgCSFindIntersect []
  message CS.intersectFound = MsgCSIntersectFound (point b₀) (tip b₀)
  message CS.intersectNotFound = MsgCSIntersectNotFound (tip b₀)
  message CS.doneK = MsgCSDone

  -- All control kinds have a fixed protocol sender, including wire Done.
  sender : CS.Kind → Mode
  sender CS.requestNext = FromInitiator
  sender CS.findIntersect = FromInitiator
  sender CS.doneK = FromInitiator
  sender _ = FromResponder

  -- Full time, mode, length and message payload agree at send and receive.
  payload : CS.Kind → Payload
  payload m = time₀ , sender m , length₀ , chainSync (message m)

  -- A local event's concrete packet uses the shared payload witness.
  packet : CS.E → Packet
  packet (d , m) = d , payload m

  -- Canonical payload queues retain the exact abstract FIFO ordering.
  queue : List CS.Kind → List Payload
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
      -- The existing client completeness construction emits exactly this packet.
      client-packet : ∀ {T s s′ e} (r : C.RelC k l d T s) (v : View.View k s e s′) →
        packets (proj₁ (proj₂ (C.co-view k l d b₀ r v))) ≡ packet e ∷ []
      client-packet (C.cCan n) (View.request lt) = refl
      client-packet (C.cMust n) (View.request lt) = refl
      client-packet (C.cCan zero) View.find = refl
      client-packet (C.cCan zero) View.close = refl
      client-packet (C.cCan (suc n)) View.await = refl
      client-packet (C.cCan (suc n)) View.forward = refl
      client-packet (C.cMust (suc n)) View.forward = refl
      client-packet (C.cCan (suc n)) View.backward = refl
      client-packet (C.cMust (suc n)) View.backward = refl
      client-packet C.cIntersect View.found = refl
      client-packet C.cIntersect View.notFound = refl
      client-packet C.cEnd ()

      -- The original server completeness construction uses those same packets.
      server-packet : ∀ {T s s′ e} (r : S.RelC k l d T s) (pr : CS.Spec.Step k server s e s′) →
        packets (proj₁ (proj₂ (S.co-ev k l d b₀ r tt pr))) ≡ packet e ∷ []
      server-packet {e = Send , CS.requestNext} S.cstIdle ()
      server-packet {e = Send , CS.awaitReply} S.cstIdle ()
      server-packet {e = Send , CS.rollForward} S.cstIdle ()
      server-packet {e = Send , CS.rollBackward} S.cstIdle ()
      server-packet {e = Send , CS.findIntersect} S.cstIdle ()
      server-packet {e = Send , CS.intersectFound} S.cstIdle ()
      server-packet {e = Send , CS.intersectNotFound} S.cstIdle ()
      server-packet {e = Send , CS.doneK} S.cstIdle ()
      server-packet {e = Recv , CS.requestNext} S.cstIdle refl = refl
      server-packet {e = Recv , CS.awaitReply} S.cstIdle ()
      server-packet {e = Recv , CS.rollForward} S.cstIdle ()
      server-packet {e = Recv , CS.rollBackward} S.cstIdle ()
      server-packet {e = Recv , CS.findIntersect} S.cstIdle refl = refl
      server-packet {e = Recv , CS.intersectFound} S.cstIdle ()
      server-packet {e = Recv , CS.intersectNotFound} S.cstIdle ()
      server-packet {e = Recv , CS.doneK} S.cstIdle refl = refl
      server-packet {e = Send , CS.requestNext} S.cstCanAwait ()
      server-packet {e = Send , CS.awaitReply} S.cstCanAwait refl = refl
      server-packet {e = Send , CS.rollForward} S.cstCanAwait refl = refl
      server-packet {e = Send , CS.rollBackward} S.cstCanAwait refl = refl
      server-packet {e = Send , CS.findIntersect} S.cstCanAwait ()
      server-packet {e = Send , CS.intersectFound} S.cstCanAwait ()
      server-packet {e = Send , CS.intersectNotFound} S.cstCanAwait ()
      server-packet {e = Send , CS.doneK} S.cstCanAwait ()
      server-packet {e = Recv , CS.requestNext} S.cstCanAwait ()
      server-packet {e = Recv , CS.awaitReply} S.cstCanAwait ()
      server-packet {e = Recv , CS.rollForward} S.cstCanAwait ()
      server-packet {e = Recv , CS.rollBackward} S.cstCanAwait ()
      server-packet {e = Recv , CS.findIntersect} S.cstCanAwait ()
      server-packet {e = Recv , CS.intersectFound} S.cstCanAwait ()
      server-packet {e = Recv , CS.intersectNotFound} S.cstCanAwait ()
      server-packet {e = Recv , CS.doneK} S.cstCanAwait ()
      server-packet {e = Send , CS.requestNext} S.cstMustReply ()
      server-packet {e = Send , CS.awaitReply} S.cstMustReply ()
      server-packet {e = Send , CS.rollForward} S.cstMustReply refl = refl
      server-packet {e = Send , CS.rollBackward} S.cstMustReply refl = refl
      server-packet {e = Send , CS.findIntersect} S.cstMustReply ()
      server-packet {e = Send , CS.intersectFound} S.cstMustReply ()
      server-packet {e = Send , CS.intersectNotFound} S.cstMustReply ()
      server-packet {e = Send , CS.doneK} S.cstMustReply ()
      server-packet {e = Recv , CS.requestNext} S.cstMustReply ()
      server-packet {e = Recv , CS.awaitReply} S.cstMustReply ()
      server-packet {e = Recv , CS.rollForward} S.cstMustReply ()
      server-packet {e = Recv , CS.rollBackward} S.cstMustReply ()
      server-packet {e = Recv , CS.findIntersect} S.cstMustReply ()
      server-packet {e = Recv , CS.intersectFound} S.cstMustReply ()
      server-packet {e = Recv , CS.intersectNotFound} S.cstMustReply ()
      server-packet {e = Recv , CS.doneK} S.cstMustReply ()
      server-packet {e = Send , CS.requestNext} S.cstIntersect ()
      server-packet {e = Send , CS.awaitReply} S.cstIntersect ()
      server-packet {e = Send , CS.rollForward} S.cstIntersect ()
      server-packet {e = Send , CS.rollBackward} S.cstIntersect ()
      server-packet {e = Send , CS.findIntersect} S.cstIntersect ()
      server-packet {e = Send , CS.intersectFound} S.cstIntersect refl = refl
      server-packet {e = Send , CS.intersectNotFound} S.cstIntersect refl = refl
      server-packet {e = Send , CS.doneK} S.cstIntersect ()
      server-packet {e = Recv , CS.requestNext} S.cstIntersect ()
      server-packet {e = Recv , CS.awaitReply} S.cstIntersect ()
      server-packet {e = Recv , CS.rollForward} S.cstIntersect ()
      server-packet {e = Recv , CS.rollBackward} S.cstIntersect ()
      server-packet {e = Recv , CS.findIntersect} S.cstIntersect ()
      server-packet {e = Recv , CS.intersectFound} S.cstIntersect ()
      server-packet {e = Recv , CS.intersectNotFound} S.cstIntersect ()
      server-packet {e = Recv , CS.doneK} S.cstIntersect ()
      server-packet {e = Send , CS.requestNext} S.cstDone ()
      server-packet {e = Send , CS.awaitReply} S.cstDone ()
      server-packet {e = Send , CS.rollForward} S.cstDone ()
      server-packet {e = Send , CS.rollBackward} S.cstDone ()
      server-packet {e = Send , CS.findIntersect} S.cstDone ()
      server-packet {e = Send , CS.intersectFound} S.cstDone ()
      server-packet {e = Send , CS.intersectNotFound} S.cstDone ()
      server-packet {e = Send , CS.doneK} S.cstDone ()
      server-packet {e = Recv , CS.requestNext} S.cstDone ()
      server-packet {e = Recv , CS.awaitReply} S.cstDone ()
      server-packet {e = Recv , CS.rollForward} S.cstDone ()
      server-packet {e = Recv , CS.rollBackward} S.cstDone ()
      server-packet {e = Recv , CS.findIntersect} S.cstDone ()
      server-packet {e = Recv , CS.intersectFound} S.cstDone ()
      server-packet {e = Recv , CS.intersectNotFound} S.cstDone ()
      server-packet {e = Recv , CS.doneK} S.cstDone ()

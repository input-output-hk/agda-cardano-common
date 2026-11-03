{-# OPTIONS --safe #-}

-- Inhabited callback-composition schedules and negative agency/queue controls.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeTests where

open import Data.Bool using (Bool; true; false)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (nothing; just)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool Bool as C
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Bool 1 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeProperties Bool 1 as P
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Bool Bool as Client
open import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Bool 1

-- A depth-one credit guard accepts two requests if eligible inputs reserve both credits.
two-reserved : Σ[ es ∈ List Action ] Run initial es (P.backlog true 2)
two-reserved = P.backlog-reachable true (λ ()) 2

-- That witness has two deferred jobs and queue entries with a zero free counter.
two-reserved-counts : (S.waiting (peer (P.backlog true 2)) ≡ 2) ×
  (length (Q.queued (queue (P.backlog true 2))) ≡ 2) ×
  (Q.free (queue (P.backlog true 2)) ≡ 0)
two-reserved-counts = P.backlog-counts true 2

-- Without a reserving application input, the second request fails at the exact limit.
limit-without-reservation : Run initial
  (wire S.recvRequest ∷ wire S.recvRequest ∷ [])
  (node (S.state S.failed 1 S.idle 0 false) (Q.credits 1 []))
limit-without-reservation =
  visible (peerRecord request (S.receiveRequest S.atFirst)) $
  internal (admitAccepted (Q.admitted (λ ()))) $
  internal (schedule S.registered refl) $
  visible (peerRecord request (S.receiveRequest S.atNext)) $
  internal (admitExcessive (Q.excessive refl)) $
  internal (schedule S.abort refl) stop

-- A callback cannot dequeue a different packet from the FIFO head.
wrong-queue-head : Q.Step (Q.credits 0 (true ∷ false ∷ [])) (Q.take false)
  (Q.credits 0 (false ∷ [])) → ⊥
wrong-queue-head ()

-- Empty next blocks rather than producing a fabricated notification.
empty-next : ∀ {m q} → Q.Step (Q.credits 0 []) (Q.take m) q → ⊥
empty-next ()

-- The generic server admission choice cannot bypass the production credit callback.
no-unbound-admission : routine (S.admitted {w = 0} {s = S.idle} {c = 0} {q = false}) ≡ true → ⊥
no-unbound-admission ()

-- This partial client state is before the receiver observes its first reply.
beforeReply : C.State
beforeReply = C.client C.poll C.awaiting [] [] 1 (+ 0) false nothing

-- The pinned callback throws if Canceled reaches a handler that read the false flag.
unexpected-cancel : Client.Run (Client.running beforeReply)
  (Client.wire (C.recvReply S.canceled) ∷ Client.handlerRejectedCancel ∷ [])
  (Client.unexpectedCancel (C.client C.poll (C.handling S.canceled) [] [] 1 (+ 0) false nothing))
unexpected-cancel =
  Client.visible (Client.wireRecord Client.reply (C.receivedReply refl)) $
  Client.internal (Client.schedule (C.keepReply refl)) $
  Client.visible (Client.rejectedCancel refl refl) Client.stop

-- Once draining is observed, the same packet is discarded without calling that handler.
draining-cancel : Client.Run
  (Client.running (C.client C.draining C.awaiting [] [] 1 (+ 0) true (just true)))
  (Client.wire (C.recvReply S.canceled) ∷ [])
  (Client.running (C.client C.draining C.idle [] (C.responseToken ∷ []) 1 (+ 1) true (just true)))
draining-cancel =
  Client.visible (Client.wireRecord Client.reply (C.receivedReply refl)) $
  Client.internal (Client.schedule (C.discardReply refl)) $
  Client.internal (Client.schedule (C.countArrival refl)) $
  Client.internal (Client.schedule (C.publishResponse refl)) Client.stop

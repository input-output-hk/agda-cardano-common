{-# OPTIONS --guardedness #-}

-- Actual peer/FIFO executions and exact-packet negative controls.
module Cardano_network.Replay.LeiosNotifyPairedModelTests where
open import Data.Fin using (zero)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (∃-syntax; _×_; _,_)
open import Data.Unit using (tt)
open import Level using (lift)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees using (ExtI)
open import Cardano_network.Base using (hi; FromInitiator; FromResponder)
open import Cardano_network.Replay.ReplayParams using (replayParams)
open import Cardano_network.Data replayParams
open import Cardano_network.Net replayParams using (lnpSendRequestNext; lnpSendBlockOffer; lnpRecvBlockOffer)
open import Cardano_network.LeiosNotifyP replayParams using (LNPEv; sendLNP; receiveLNP; apiLPev; LNPclientStClient; LNPserverStClient)
import Cardano_network.Replay.LeiosNotifyPairedModel replayParams as M
import Cardano_network.Replay.LeiosNotifyPairedTrace replayParams as T
import Semantics.LTS {E = LNPEv} {I = ExtI LNPEv} as Local
import Semantics.LTS {E = M.PairEv} {I = M.PairI} as Pair
open import Semantics.Deadlock {E = M.PairEv} {I = M.PairI}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-ev; ∖√-τ)

-- The exact packet sent by the real peer after the request API handoff.
request : Payload
request = tt , FromInitiator , tt , leiosNotifyP MsgLNPRequestNext

-- The client API, its send, and the opposite peer's matching receive are inhabited.
request-events : List Pair.Event
request-events = Pair.evLabel _ (M.atClient (apiLPev zero hi lnpSendRequestNext)) tt ∷
  Pair.evLabel _ (M.atClient (sendLNP zero hi)) request ∷
  Pair.evLabel _ (M.atServer (receiveLNP zero hi)) request ∷ []

-- This witness uses the actual supplied peer trees, rather than replay-generated trees.
request-run : ∃[ end ] M.system zero zero hi hi ⟹∖√⟨ request-events ⟩ end
request-run = _ , ∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl) ∖√-refl))

-- The checked generic inversion recovers actual local steps and queue updates.
request-components : ∃[ end ] T.Run
  (T.state (LNPclientStClient zero hi)
    (LNPserverStClient zero hi) M.empty)
  request-events end
request-components with request-run
... | end , run with T.sound run
...   | residual , components , _ = residual , components

-- Two packets with the same reply kind still have different concrete payloads.
reply otherReply : Payload
reply = tt , FromResponder , tt , leiosNotifyP (MsgLNPBlockOffer (1 , 3) tt)
otherReply = tt , FromResponder , tt , leiosNotifyP (MsgLNPBlockOffer (2 , 3) tt)

-- A receiver may consume precisely the transmitted packet.
exact-receive : M.clientGate (Local.evLabel _ (receiveLNP zero hi) reply)
  (M.queues [] (reply ∷ [])) ≡ just M.empty
exact-receive = refl

-- Kind agreement cannot justify changing the received hash or point.
wrong-payload : M.clientGate (Local.evLabel _ (receiveLNP zero hi) otherReply)
  (M.queues [] (reply ∷ [])) ≡ nothing
wrong-payload = refl

-- The medium rejects an uncaptured receive at a fresh boundary.
missing-send : M.serverGate (Local.evLabel _ (receiveLNP zero hi) request) M.empty ≡ nothing
missing-send = refl

-- A full notification handoff exercises both independent loop-back τ branches.
round-events : List Pair.Event
round-events = Pair.evLabel _ (M.atClient (apiLPev zero hi lnpSendRequestNext)) tt ∷
  Pair.evLabel _ (M.atClient (sendLNP zero hi)) request ∷
  Pair.evLabel _ (M.atServer (receiveLNP zero hi)) request ∷
  Pair.evLabel _ (M.atServer (apiLPev zero hi lnpSendBlockOffer)) ((1 , 3) , tt) ∷
  Pair.evLabel _ (M.atServer (sendLNP zero hi)) reply ∷
  Pair.evLabel _ (M.atClient (receiveLNP zero hi)) reply ∷
  Pair.evLabel _ (M.atClient (apiLPev zero hi lnpRecvBlockOffer)) ((1 , 3) , tt) ∷ []

-- Both original peers run, with one transmitted packet consumed in each direction.
round-run : ∃[ end ] M.system zero zero hi hi ⟹∖√⟨ round-events ⟩ end
round-run = _ , ∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl)
  (∖√-τ (Pair.sTau {i = _ , M.clientI M.silence} {a = lift tt} refl refl)
  (∖√-τ (Pair.sTau {i = _ , M.serverI M.silence} {a = lift tt} refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl) ∖√-refl))))))))

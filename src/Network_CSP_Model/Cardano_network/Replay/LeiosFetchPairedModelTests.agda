{-# OPTIONS --guardedness #-}

-- Actual peer/FIFO executions and exact-packet negative controls.
module Cardano_network.Replay.LeiosFetchPairedModelTests where
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
open import Cardano_network.Net replayParams using (lfpSendBlockRequest; lfpReqBlockRequest; lfpSendBlock; lfpRecvBlock)
open import Cardano_network.LeiosFetchP replayParams using (LFPEv; sendLFP; receiveLFP; apiLPev; LFPclientStClient; LFPserverStClient)
import Cardano_network.LeiosFetchPipe replayParams as Pipe
import Cardano_network.Replay.LeiosFetchPairedModel replayParams as M
import Cardano_network.Replay.LeiosFetchPairedTrace replayParams as T
import Semantics.LTS {E = LFPEv} {I = ExtI LFPEv} as Local
import Semantics.LTS {E = M.PairEv} {I = M.PairI} as Pair
open import Semantics.Deadlock {E = M.PairEv} {I = M.PairI}
  using (_⟹∖√⟨_⟩_; ∖√-refl; ∖√-ev; ∖√-τ)

-- The exact packet sent by the real peer after the request API handoff.
request : Payload
request = tt , FromInitiator , tt , leiosFetchP (MsgLFPBlockRequest (1 , 3))

-- The client API, its send, and the opposite peer's matching receive are inhabited.
request-events : List Pair.Event
request-events = Pair.evLabel _ (M.atClient (apiLPev zero hi lfpSendBlockRequest)) (1 , 3) ∷
  Pair.evLabel _ (M.atClient (sendLFP zero hi)) request ∷
  Pair.evLabel _ (M.atServer (receiveLFP zero hi)) request ∷ []

-- This witness uses the actual supplied peer trees, rather than replay-generated trees.
request-run : ∃[ end ] M.system 2 zero zero hi hi ⟹∖√⟨ request-events ⟩ end
request-run = _ , ∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl) ∖√-refl))

-- The checked generic inversion recovers actual local steps and queue updates.
request-components : ∃[ end ] T.Run
  (T.state (Pipe.pipe 2 zero hi)
    (LFPserverStClient zero hi) M.empty)
  request-events end
request-components with request-run
... | end , run with T.sound run
...   | residual , components , _ = residual , components

-- Two packets with the same reply kind still have different concrete payloads.
reply otherReply : Payload
reply = tt , FromResponder , tt , leiosFetchP (MsgLFPBlock 1)
otherReply = tt , FromResponder , tt , leiosFetchP (MsgLFPBlock 2)

-- A receiver may consume precisely the transmitted packet.
exact-receive : M.clientGate (Local.evLabel _ (receiveLFP zero hi) reply)
  (M.queues [] (reply ∷ [])) ≡ just M.empty
exact-receive = refl

-- Kind agreement cannot justify changing the received hash or point.
wrong-payload : M.clientGate (Local.evLabel _ (receiveLFP zero hi) otherReply)
  (M.queues [] (reply ∷ [])) ≡ nothing
wrong-payload = refl

-- The medium rejects an uncaptured receive at a fresh boundary.
missing-send : M.serverGate (Local.evLabel _ (receiveLFP zero hi) request) M.empty ≡ nothing
missing-send = refl

-- Request reporting precedes application service in the actual producer.
round-events : List Pair.Event
round-events = Pair.evLabel _ (M.atClient (apiLPev zero hi lfpSendBlockRequest)) (1 , 3) ∷
  Pair.evLabel _ (M.atClient (sendLFP zero hi)) request ∷
  Pair.evLabel _ (M.atServer (receiveLFP zero hi)) request ∷
  Pair.evLabel _ (M.atServer (apiLPev zero hi lfpReqBlockRequest)) (1 , 3) ∷
  Pair.evLabel _ (M.atServer (apiLPev zero hi lfpSendBlock)) 1 ∷
  Pair.evLabel _ (M.atServer (sendLFP zero hi)) reply ∷
  Pair.evLabel _ (M.atClient (receiveLFP zero hi)) reply ∷
  Pair.evLabel _ (M.atClient (apiLPev zero hi lfpRecvBlock)) 1 ∷ []

-- The checked pipelined client and original sequential producer complete a round.
round-run : ∃[ end ] M.system 2 zero zero hi hi ⟹∖√⟨ round-events ⟩ end
round-run = _ , ∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl)
  (∖√-τ (Pair.sTau {i = _ , M.clientI M.silence} {a = lift tt} refl refl)
  (∖√-τ (Pair.sTau {i = _ , M.serverI M.silence} {a = lift tt} refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl) ∖√-refl)))))))))

-- An unconstrained application may supply hash 2 after the server reports hash 1.
wrong-server-events : List Pair.Event
wrong-server-events = Pair.evLabel _ (M.atClient (apiLPev zero hi lfpSendBlockRequest)) (1 , 3) ∷
  Pair.evLabel _ (M.atClient (sendLFP zero hi)) request ∷
  Pair.evLabel _ (M.atServer (receiveLFP zero hi)) request ∷
  Pair.evLabel _ (M.atServer (apiLPev zero hi lfpReqBlockRequest)) (1 , 3) ∷
  Pair.evLabel _ (M.atServer (apiLPev zero hi lfpSendBlock)) 2 ∷
  Pair.evLabel _ (M.atServer (sendLFP zero hi)) otherReply ∷ []

-- This actual composed run refutes using the bare server as the checker bridge target.
wrong-server-run : ∃[ end ] M.system 2 zero zero hi hi ⟹∖√⟨ wrong-server-events ⟩ end
wrong-server-run = _ , ∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl)
  (∖√-ev (Pair.sVis refl refl)
  (∖√-τ (Pair.sTau {i = _ , M.serverI M.silence} {a = lift tt} refl refl)
  (∖√-ev (Pair.sVis refl refl) (∖√-ev (Pair.sVis refl refl) ∖√-refl))))))

import Cardano_network.Replay.LeiosFetchSession as F
import Cardano_network.Replay.LeiosFetchDecide as Decide
open import Semantics.Replay using (module Traces)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (toWitnessFalse)
module Spec = Traces (F.Spec.leiosFetch 2)
module Check = Decide.Cert 2

-- The existing replay spec correctly rejects that very server-side hash sequence.
wrong-server-rejected : ¬ Spec.HasTrace F.server₀
  ((F.Recv , F.MsgLeiosBlockRequest 1 3) ∷ (F.Send , F.MsgLeiosBlock 2 0) ∷ [])
wrong-server-rejected = toWitnessFalse {a? = Check.hasTrace? Check.server-cert
  ((F.Recv , F.MsgLeiosBlockRequest 1 3) ∷ (F.Send , F.MsgLeiosBlock 2 0) ∷ [])} tt

{-# OPTIONS --safe #-}

-- Typecheck-time tests of the replay decision procedure on the LeiosFetch
-- session spec (trace-replay Phase 4), pipelining bound k = 4. Every
-- `False` test is a proof of non-membership (`toWitnessFalse` turns it into
-- `¬ HasTrace s₀ trace`); every `True` test re-confirms a Phase 3 trace.
module Cardano_network.Replay.LeiosFetchDecideTests where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Nullary using (¬_)
open import Relation.Nullary.Decidable using (True; False; toWitnessFalse)

open import Semantics.Replay using (module Traces)
open import Cardano_network.Replay.LeiosFetchSession
open import Cardano_network.Replay.LeiosFetchDecide

open Spec 4 using (leiosFetch)
open Traces leiosFetch using (HasTrace)
open Cert 4 using (hasTrace?; client-cert; server-cert)

-- a bitmap: word 0 with its low 8 bits set
bm : List (ℕ × ℕ)
bm = (0 , 255) ∷ []

------------------------------------------------------------------------
-- Positive: the decider agrees with the Phase 3 fuel checker

-- server plain cycle (each reply after one τ)
_ : True (hasTrace? server-cert
      ( (Recv , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlock 1 5000)
      ∷ (Recv , MsgLeiosBlockTxsRequest 1 10 8 bm)
      ∷ (Send , MsgLeiosBlockTxs 1 10 8 9000 bm)
      ∷ []))
_ = tt

-- client pipelined depth 4 (= k), FIFO answers
_ : True (hasTrace? client-cert
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlockRequest 2 11)
      ∷ (Send , MsgLeiosBlockTxsRequest 1 10 3 bm)
      ∷ (Send , MsgLeiosBlockRequest 4 13)
      ∷ (Recv , MsgLeiosBlock 1 100)
      ∷ (Recv , MsgLeiosBlock 2 200)
      ∷ (Recv , MsgLeiosBlockTxs 1 10 3 300 bm)
      ∷ (Recv , MsgLeiosBlock 4 400)
      ∷ []))
_ = tt

-- client interleaving r1 r2 a1 r3 a2 a3
_ : True (hasTrace? client-cert
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlockTxsRequest 2 11 5 bm)
      ∷ (Recv , MsgLeiosBlock 1 100)
      ∷ (Send , MsgLeiosBlockRequest 3 12)
      ∷ (Recv , MsgLeiosBlockTxs 2 11 5 500 bm)
      ∷ (Recv , MsgLeiosBlock 3 300)
      ∷ []))
_ = tt

------------------------------------------------------------------------
-- Negative: proofs of non-membership

-- client: response without a request
_ : False (hasTrace? client-cert ((Recv , MsgLeiosBlock 1 100) ∷ []))
_ = tt

-- server: response without a request
_ : False (hasTrace? server-cert ((Send , MsgLeiosBlock 1 100) ∷ []))
_ = tt

-- client: duplicated response (one request, two Blocks)
_ : False (hasTrace? client-cert
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Recv , MsgLeiosBlock 1 100)
      ∷ (Recv , MsgLeiosBlock 1 100)
      ∷ []))
_ = tt

-- server: duplicated response (one request, two Blocks)
_ : False (hasTrace? server-cert
      ( (Recv , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlock 1 100)
      ∷ (Send , MsgLeiosBlock 1 100)
      ∷ []))
_ = tt

-- client: response for an EB never requested (wrong ebHash)
_ : False (hasTrace? client-cert
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Recv , MsgLeiosBlock 2 100)
      ∷ []))
_ = tt

-- server: reply for an EB never requested (wrong ebHash)
_ : False (hasTrace? server-cert
      ( (Recv , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlock 2 100)
      ∷ []))
_ = tt

-- client: two pipelined requests answered in reverse order
_ : False (hasTrace? client-cert
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlockRequest 2 11)
      ∷ (Recv , MsgLeiosBlock 2 200)
      ∷ (Recv , MsgLeiosBlock 1 100)
      ∷ []))
_ = tt

-- client: BlockTxs response with the wrong slot
_ : False (hasTrace? client-cert
      ( (Send , MsgLeiosBlockTxsRequest 1 10 8 bm)
      ∷ (Recv , MsgLeiosBlockTxs 1 11 8 9000 bm)
      ∷ []))
_ = tt

-- server: BlockTxs reply with the wrong slot
_ : False (hasTrace? server-cert
      ( (Recv , MsgLeiosBlockTxsRequest 1 10 8 bm)
      ∷ (Send , MsgLeiosBlockTxs 1 11 8 9000 bm)
      ∷ []))
_ = tt

-- client: a fifth outstanding request exceeds k = 4
_ : False (hasTrace? client-cert
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlockRequest 2 11)
      ∷ (Send , MsgLeiosBlockRequest 3 12)
      ∷ (Send , MsgLeiosBlockRequest 4 13)
      ∷ (Send , MsgLeiosBlockRequest 5 14)
      ∷ []))
_ = tt

-- client: Done with a request outstanding
_ : False (hasTrace? client-cert
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosDone)
      ∷ []))
_ = tt

-- server: Done with a request outstanding
_ : False (hasTrace? server-cert
      ( (Recv , MsgLeiosBlockRequest 1 10)
      ∷ (Recv , MsgLeiosDone)
      ∷ []))
_ = tt

-- server: a second request before the first is answered
_ : False (hasTrace? server-cert
      ( (Recv , MsgLeiosBlockRequest 1 10)
      ∷ (Recv , MsgLeiosBlockRequest 2 11)
      ∷ []))
_ = tt

------------------------------------------------------------------------
-- Replica of the real FIFO-skip sessions (relay leios1-rel-a-1, session
-- 172.31.40.28:3001 ↔ 52.58.138.208:3001, client role, 2026-09-27): the
-- client queue was empty just before 14:43:35, so the session state there
-- is client₀. The BlockRequest for 203b94b7… (slot 1781013) is never
-- answered; the next Block answers the following request 322074c6… (slot
-- 1781049, 99975 bytes).

-- the logged event sequence from the empty queue
fifoSkip : List E
fifoSkip =
    (Send , MsgLeiosBlockRequest
       0x203b94b7bc9ec85d9c41f64fcb1bfc4ae81f52251359b64bbd1e5e0b8f111592 1781013)
  ∷ (Send , MsgLeiosBlockRequest
       0x322074c685b9aa591cfc461d269faf8bfa05889020b55c05a7e2bc61470d2f34 1781049)
  ∷ (Recv , MsgLeiosBlock
       0x322074c685b9aa591cfc461d269faf8bfa05889020b55c05a7e2bc61470d2f34 99975)
  ∷ []

-- the decider rejects it
_ : False (hasTrace? client-cert fifoSkip)
_ = tt

-- ... which is a proof that the FIFO spec has no run on it
fifoSkip-rejected : ¬ HasTrace client₀ fifoSkip
fifoSkip-rejected = toWitnessFalse {a? = hasTrace? client-cert fifoSkip} tt

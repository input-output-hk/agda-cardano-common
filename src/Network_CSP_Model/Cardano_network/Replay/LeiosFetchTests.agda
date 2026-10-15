{-# OPTIONS --safe #-}

-- Typecheck-time replay tests for the LeiosFetch session spec (Phase 3),
-- with pipelining bound k = 4. Each positive test is accepted by the fuel
-- checker, so it carries a weak-trace witness. Fuel = number of τ steps
-- allowed on the whole run (one per server reply, none for the client).
module Cardano_network.Replay.LeiosFetchTests where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Semantics.Replay.Fuel
open import Cardano_network.Replay.LeiosFetchSession

open Spec 4 using (leiosFetch)
open Checker leiosFetch

-- a bitmap: word 0 with its low 8 bits set
bm : List (ℕ × ℕ)
bm = (0 , 255) ∷ []

-- 1. client plain cycle: one Block and one BlockTxs exchange
_ : IsAccept (check 0 client₀
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Recv , MsgLeiosBlock 1 5000)
      ∷ (Send , MsgLeiosBlockTxsRequest 1 10 8 bm)
      ∷ (Recv , MsgLeiosBlockTxs 1 10 8 9000 bm)
      ∷ []))
_ = tt

-- 2. server plain cycle: each reply needs one τ (unlogged application)
_ : IsAccept (check 2 server₀
      ( (Recv , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlock 1 5000)
      ∷ (Recv , MsgLeiosBlockTxsRequest 1 10 8 bm)
      ∷ (Send , MsgLeiosBlockTxs 1 10 8 9000 bm)
      ∷ []))
_ = tt

-- 3a. client pipelined depth 2, FIFO answers
_ : IsAccept (check 0 client₀
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlockRequest 2 11)
      ∷ (Recv , MsgLeiosBlock 1 100)
      ∷ (Recv , MsgLeiosBlock 2 200)
      ∷ []))
_ = tt

-- 3b. client pipelined depth 3, mixed kinds, FIFO answers
_ : IsAccept (check 0 client₀
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlockTxsRequest 2 11 3 bm)
      ∷ (Send , MsgLeiosBlockRequest 3 12)
      ∷ (Recv , MsgLeiosBlock 1 100)
      ∷ (Recv , MsgLeiosBlockTxs 2 11 3 300 bm)
      ∷ (Recv , MsgLeiosBlock 3 200)
      ∷ []))
_ = tt

-- 3c. client pipelined depth 4 (= k), FIFO answers
_ : IsAccept (check 0 client₀
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

-- 4. interleaving: send r1, send r2, recv a1, send r3, recv a2, recv a3
_ : IsAccept (check 0 client₀
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlockTxsRequest 2 11 5 bm)
      ∷ (Recv , MsgLeiosBlock 1 100)
      ∷ (Send , MsgLeiosBlockRequest 3 12)
      ∷ (Recv , MsgLeiosBlockTxs 2 11 5 500 bm)
      ∷ (Recv , MsgLeiosBlock 3 300)
      ∷ []))
_ = tt

-- 5. server: the same EB's txs requested three times in one session
_ : IsAccept (check 3 server₀
      ( (Recv , MsgLeiosBlockTxsRequest 7 20 2 bm)
      ∷ (Send , MsgLeiosBlockTxs 7 20 2 64 bm)
      ∷ (Recv , MsgLeiosBlockTxsRequest 7 20 2 bm)
      ∷ (Send , MsgLeiosBlockTxs 7 20 2 64 bm)
      ∷ (Recv , MsgLeiosBlockTxsRequest 7 20 2 bm)
      ∷ (Send , MsgLeiosBlockTxs 7 20 2 64 bm)
      ∷ []))
_ = tt

-- 6a. client session ending in Done
_ : IsAccept (check 0 client₀
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Recv , MsgLeiosBlock 1 100)
      ∷ (Send , MsgLeiosDone)
      ∷ []))
_ = tt

-- 6b. server session ending in Done
_ : IsAccept (check 1 server₀
      ( (Recv , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlock 1 100)
      ∷ (Recv , MsgLeiosDone)
      ∷ []))
_ = tt

-- 7. a full-size 256-bit hash (64 hex digits) still computes
_ : IsAccept (check 0 client₀
      ( (Send , MsgLeiosBlockRequest
           0x428cdfbf00112233445566778899aabbccddeeff00112233445566778899aabb 1781013)
      ∷ (Recv , MsgLeiosBlock
           0x428cdfbf00112233445566778899aabbccddeeff00112233445566778899aabb 5000)
      ∷ []))
_ = tt

-- SANITY ONLY (fuel exhausted / no run found within the fuel; NOT proofs of
-- non-membership, which are Phase 4):

-- response without a request
_ : check 5 client₀ ((Recv , MsgLeiosBlock 1 100) ∷ []) ≡ unknown
_ = refl

-- response for a different EB than the oldest request
_ : check 5 client₀
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Recv , MsgLeiosBlock 2 100)
      ∷ []) ≡ unknown
_ = refl

-- answers out of FIFO order
_ : check 5 client₀
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlockRequest 2 11)
      ∷ (Recv , MsgLeiosBlock 2 200)
      ∷ []) ≡ unknown
_ = refl

-- a fifth outstanding request exceeds k = 4
_ : check 5 client₀
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosBlockRequest 2 11)
      ∷ (Send , MsgLeiosBlockRequest 3 12)
      ∷ (Send , MsgLeiosBlockRequest 4 13)
      ∷ (Send , MsgLeiosBlockRequest 5 14)
      ∷ []) ≡ unknown
_ = refl

-- Done with an outstanding request
_ : check 5 client₀
      ( (Send , MsgLeiosBlockRequest 1 10)
      ∷ (Send , MsgLeiosDone)
      ∷ []) ≡ unknown
_ = refl

-- server: second request before the first is answered
_ : check 5 server₀
      ( (Recv , MsgLeiosBlockRequest 1 10)
      ∷ (Recv , MsgLeiosBlockRequest 2 11)
      ∷ []) ≡ unknown
_ = refl

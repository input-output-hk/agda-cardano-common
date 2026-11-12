{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — a DEPTH-k PIPELINED LeiosFetch CLIENT
-- (trace-replay Phase 5, amendment B2).
--
-- `LeiosFetchP.LFPclientStClient` is a depth-1 alternating machine and
-- accepts any Block reply. This client keeps a FIFO queue of pending requests
-- (oldest first): it sends a request while fewer than k are pending, answers
-- a reply only against the queue head (Block: the hash; BlockTxs: the
-- stored bitmap count). A silent stop drains replies by kind without application
-- callbacks, then sends Done with an empty queue.  Same alphabet
-- (`LFPEv`) and the same `iter` structure as `clientStepP`; the checking
-- menu fuses visible offers with the silent stop.
-- It is written from the replay spec, so the client bridge mainly certifies
-- the transcription.
-- Invariant 1 (B7a): checked with `agda --safe` on the command line.
------------------------------------------------------------------------

open import Cardano_network.Params using (Params)

module Cardano_network.LeiosFetchPipe (p : Params) where

open import Data.Nat using (ℕ)
open import Relation.Nullary.Decidable using (T?)
open import Cardano_network.Replay.LeiosFetchWire using (maxTxs)
open import Cardano_network.Replay.LeiosFetchWords using (canonical)
open import Data.Nat.Properties using (_<?_; _≤?_)
open import Data.List using (List; []; _∷_; _∷ʳ_; length; zip)
open import Data.Product using (_×_; _,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Class.DecEq using (_≟_)

open import Process_Trees
open import Cardano_network.Base
open import Cardano_network.Data p
open import Cardano_network.Net p
open Params p
open import Cardano_network.LeiosFetchP p
  using (LFPEv; sendLFP; receiveLFP; apiLPev; LFPEv-≟; Rr)

import CSP.Operators {E = LFPEv} as LFPOps
open LFPOps LFPEv-≟

-- a pending request: which kind, its point, and the requested tx offsets
data Pend : Set where
  -- an outstanding BlockRequest
  blk : EBHash × LSlot → Pend
  -- an outstanding BlockTxsRequest
  txs : EBHash × LSlot → TxBitmap → Pend

-- the client's process type: loop state = pending queue, oldest first
PipeT : Set₁
PipeT = PTree LFPEv (ExtI LFPEv) (List Pend ⊎ Rr)

-- the client sends wire message `m`, then hands `r` back to the loop
sendM : Link → Dir → MessageLeiosFetchP → List Pend ⊎ Rr → PipeT
sendM l d m r = sendLFP l d ! (time₀ , FromInitiator , length₀ , leiosFetchP m) ⟶ Ret r

-- the client hands Block `eb` to the application, then loops with queue `q`
delB : Link → Dir → EB → List Pend → PipeT
delB l d eb q = apiLPev l d lfpRecvBlock ! eb ⟶ Ret (inj₁ q)

-- Pair the positional transactions with the stored offsets for the application.
delT : Link → Dir → EBHash × LSlot → TxBitmap → List Tx → List Pend → PipeT
delT l d pt bm ts q = Output ⦃ DecEq-TxsReply ⦄ (apiLPev l d lfpRecvBlockTxs) (pt , zip bm ts) (Ret (inj₁ q))

-- the offer map of one client step at queue `q` with pipelining bound `k`
pipeV : ℕ → Link → Dir → List Pend
      → (at : AnyTypes LFPEv) → ContinueType at (Maybe PipeT)
-- the application asks for a body: send the request if fewer than k are pending
pipeV k l d q (_ , apiLPev l′ d′ lfpSendBlockRequest) pt
  with l′ ≟ l | d′ ≟ d | length q <? k
... | yes refl | yes refl | yes _ = just (sendM l d (MsgLFPBlockRequest pt) (inj₁ (q ∷ʳ blk pt)))
... | _        | _        | _     = nothing
-- The application requests a canonical tx closure while below the queue bound.
pipeV k l d q (_ , apiLPev l′ d′ lfpSendBlockTxsRequest) (pt , bm)
  with l′ ≟ l | d′ ≟ d | length q <? k | T? (canonical bm)
... | yes refl | yes refl | yes _ | yes _ = just (sendM l d (MsgLFPBlockTxsRequest pt bm) (inj₁ (q ∷ʳ txs pt bm)))
... | _        | _        | _     | _ = nothing
-- the application ends the session: only with nothing pending
pipeV k l d [] (_ , apiLPev l′ d′ lfpSendDone) _ with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (sendM l d MsgLFPDone (inj₂ _))
... | _        | _        = nothing
-- a Block answers the head only if the head is a BlockRequest for its hash
pipeV k l d (blk (h , _) ∷ q) (_ , receiveLFP l′ d′) (_ , _ , _ , leiosFetchP (MsgLFPBlock eb))
  with l′ ≟ l | d′ ≟ d | ebHash eb ≟ h
... | yes refl | yes refl | yes _ = just (delB l d eb q)
... | _        | _        | _     = nothing
-- A positional BlockTxs answers the head only when its count matches the stored bitmap.
pipeV k l d (txs pt bm ∷ q) (_ , receiveLFP l′ d′)
      (_ , _ , _ , leiosFetchP (MsgLFPBlockTxs ts))
  with l′ ≟ l | d′ ≟ d | length ts ≟ length bm
... | yes refl | yes refl | yes _ = just (delT l d pt bm ts q)
... | _        | _        | _     = nothing
pipeV k l d q _ _ = nothing

-- The drain receives a Block by kind and discards it without calling the application.
drainBlockV : Link → Dir → PipeT
            → (at : AnyTypes LFPEv) → ContinueType at (Maybe PipeT)
drainBlockV l d next (_ , receiveLFP l′ d′)
  (_ , _ , _ , leiosFetchP (MsgLFPBlock _)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just next
... | _        | _        = nothing
drainBlockV _ _ _ _ _ = nothing

-- The drain discards transactions by kind only within the wire decoder cap.
drainTxsV : Link → Dir → PipeT
          → (at : AnyTypes LFPEv) → ContinueType at (Maybe PipeT)
drainTxsV l d next (_ , receiveLFP l′ d′)
  (_ , _ , _ , leiosFetchP (MsgLFPBlockTxs ts)) with l′ ≟ l | d′ ≟ d | length ts ≤? maxTxs
... | yes refl | yes refl | yes _ = just next
... | _        | _        | _ = nothing
drainTxsV _ _ _ _ _ = nothing

-- Drain each outstanding reply by kind, then send Done; structural recursion on the queue.
drainStep : Link → Dir → List Pend → PipeT
drainStep l d [] = sendM l d MsgLFPDone (inj₂ _)
drainStep l d (blk _ ∷ q) = ptree (react (drainBlockV l d (drainStep l d q)) ∅t)
drainStep l d (txs _ _ ∷ q) = ptree (react (drainTxsV l d (drainStep l d q)) ∅t)

-- One checking step offers requests/replies and a silent stop into the drain.
pipeStep : ℕ → Link → Dir → List Pend → PipeT
pipeStep k l d q = ptree (react (pipeV k l d q) (oneτ (drainStep l d q)))

-- the depth-k pipelined client on link `l`, direction `d`, nothing pending
pipe : ℕ → Link → Dir → PTree LFPEv (ExtI LFPEv) Rr
pipe k l d = iter (pipeStep k l d) []

{-# OPTIONS --guardedness #-}

-- TxSubmission2 pipelines on the requester/server, not the submitter/client.
open import Cardano_network.Params using (Params)
module Cardano_network.TxSubmission2Pipe (p : Params) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_<?_)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Product using (_,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Class.DecEq using (_≟_)
import Class.DecEq.Instances as DI
open import Process_Trees
open import Cardano_network.Base
open import Cardano_network.Data p
open Params p
open import Cardano_network.Net p
import Cardano_network.TxSubmission p as T
open T using (TSEv; sendTS; receiveTS; apiTSev; TSEv-≟; Rr; TSState;
  stInit; stIdle; stTxIdsBlocking; stDone; DecEq-ListTxHash)
import CSP.Operators {E = TSEv} as Ops
open Ops TSEv-≟

-- The sequential submitter preserves the original API but enforces nonempty
-- blocking ID replies, as required by the prototype's BlockingReplyList type.
submitterStep : Link → Dir → TSState → PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)
submitterStep l d stTxIdsBlocking = pchoice v
  where
  v : (at : AnyTypes TSEv) → ContinueType at (Maybe (PTree TSEv (ExtI TSEv) (TSState ⊎ Rr)))
  v (_ , apiTSev l′ d′ sendTSReplyTxIds) (x ∷ xs) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
    (sendTS l d ! (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds (x ∷ xs))) ⟶ Ret (inj₁ stIdle))
  ... | _ | _ = nothing
  v (_ , apiTSev l′ d′ sendTSDone) _ with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = just
    (sendTS l d ! (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) ⟶ Ret (inj₁ stDone))
  ... | _ | _ = nothing
  v _ _ = nothing
submitterStep l d s = T.clientStep l d s

-- The client auto-sends Init and processes one request at a time.
client : Link → Dir → PTree TSEv (ExtI TSEv) Rr
client l d = iter (submitterStep l d) stInit

-- FIFO entries retain the expected response type for each pipelined operation.
data Reply : Set where
  ids txs : Reply

-- Blocking requests are exclusive; completed results consume sender credit.
data State : Set where
  awaitingInit blocking : State
  pending : List Reply → ℕ → State

-- Requester loop bodies continue with a state or return successfully.
Body : Set₁
Body = PTree TSEv (ExtI TSEv) (State ⊎ Rr)

-- Emit a responder-role request before advancing the requester loop.
send : Link → Dir → MessageTxSubmission2 → State → Body
send l d m s = sendTS l d ! (time₀ , FromResponder , length₀ , txSubmission m) ⟶ Ret (inj₁ s)

-- Request and reply offers share a node while the FIFO has available capacity.
menu : ℕ → Link → Dir → State → (at : AnyTypes TSEv) → ContinueType at (Maybe Body)
menu k l d awaitingInit (_ , receiveTS l′ d′)
  (_ , FromInitiator , _ , txSubmission MsgTSInit) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (Ret (inj₁ (pending [] 0)))
... | _ | _ = nothing
menu k l d (pending [] zero) (_ , apiTSev l′ d′ sendTSRequestTxIdsBlocking) (a , r)
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (send l d (MsgTSRequestTxIds Blocking a r) blocking)
... | _ | _ = nothing
menu k l d (pending q c) (_ , apiTSev l′ d′ sendTSRequestTxIdsPipelined) (a , r)
  with l′ ≟ l | d′ ≟ d | (length q + c) <? k
... | yes refl | yes refl | yes _ = just
  (send l d (MsgTSRequestTxIds NonBlocking a r) (pending (q ∷ʳ ids) c))
... | _ | _ | _ = nothing
menu k l d (pending q c) (_ , apiTSev l′ d′ sendTSRequestTxsPipelined) xs
  with l′ ≟ l | d′ ≟ d | (length q + c) <? k
... | yes refl | yes refl | yes _ = just
  (send l d (MsgTSRequestTxs xs) (pending (q ∷ʳ txs) c))
... | _ | _ | _ = nothing
menu k l d (pending (ids ∷ q) c) (_ , receiveTS l′ d′)
  (_ , FromInitiator , _ , txSubmission (MsgTSReplyTxIds xs)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just
  (Output ⦃ DecEq-ListTxHash ⦄ (apiTSev l d recvTSReplyTxIds) xs (Ret (inj₁ (pending q (suc c)))))
... | _ | _ = nothing
menu k l d (pending (txs ∷ q) c) (_ , receiveTS l′ d′)
  (_ , FromInitiator , _ , txSubmission (MsgTSReplyTxs xs)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just
  (Output ⦃ DI.DecEq-List ⦄ (apiTSev l d recvTSReplyTxs) xs (Ret (inj₁ (pending q (suc c)))))
... | _ | _ = nothing
menu k l d blocking (_ , receiveTS l′ d′)
  (_ , FromInitiator , _ , txSubmission (MsgTSReplyTxIds (x ∷ xs))) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just
  (Output ⦃ DecEq-ListTxHash ⦄ (apiTSev l d recvTSReplyTxIds) (x ∷ xs) (Ret (inj₁ (pending [] 0))))
... | _ | _ = nothing
menu k l d blocking (_ , receiveTS l′ d′)
  (_ , FromInitiator , _ , txSubmission MsgTSDone) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (Ret (inj₂ _))
... | _ | _ = nothing
menu _ _ _ _ _ _ = nothing

-- Collect one completed pipeline result to release sender credit.
collect : State → Maybe Body
collect (pending q (suc c)) = just (Ret (inj₁ (pending q c)))
collect _ = nothing

-- Visible offers coexist with silent result collection.
step : ℕ → Link → Dir → State → Body
step k l d s = ptree (react (menu k l d s) (λ _ _ → collect s))

-- k bounds asynchronous requests; synchronous blocking requests need no credit.
server : ℕ → Link → Dir → PTree TSEv (ExtI TSEv) Rr
server k l d = iter (step k l d) awaitingInit

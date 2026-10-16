{-# OPTIONS --guardedness #-}

-- Structural inversion and forward steps for the existing pipelined PTree.
open import Cardano_network.Params using (Params)
module Cardano_network.Replay.TxSubmission2ServerParts (p : Params) where

open import Data.Nat using (ℕ; zero; suc; _<_; _+_)
open import Data.Nat.Properties using (_<?_)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
import Class.DecEq.Instances as DI
open import Class.DecEq using (DecEq; _≟_)
open import Process_Trees using (PTree; ExtI; react; base)
open import Cardano_network.Base
open import Cardano_network.Data p
open import Cardano_network.Net p
open Params p
open import Cardano_network.TxSubmission p
  using (TSEv; sendTS; receiveTS; apiTSev; doneTS; TSEv-≟; Rr; DecEq-ListTxHash)
open import Cardano_network.TxSubmission2Pipe p
open import CSP.Operators TSEv-≟ using (Ret; Output; ∅t; iter-bind)
open import Semantics.LTS {E = TSEv} {I = ExtI TSEv}
  using (Event; evLabel; _─[_]─►_; ev; evl; τ; sVis; sSil; sTau)
open import CSP.Laws.DivFree.Loop TSEv-≟ using (iter-τ-elim; iter-ev-elim; itτ; itBack)
open import CSP.Laws.Bisim.IterCong TSEv-≟ using (iter-bind-ev; iter-bind-τ)
open import Cardano_network.Replay.LeiosFetchServerParts using (module OutInv)
open OutInv TSEv-≟ using (out-ev)

-- The pipelined requester's process carrier.
Proc : Set₁
Proc = PTree TSEv (ExtI TSEv) Rr

module _ (k : ℕ) (l : Link) (d : Dir) where
  -- Keep the original iteration body around a residual round.
  It : Body → Proc
  It t = iter-bind t (step k l d)

  -- Application observation at this endpoint.
  apiE : (m : ApiTSTag) → ApiTSCar m → Event
  apiE m v = evLabel _ (apiTSev l d m) v

  -- Wire reception at this endpoint.
  rcvE : Payload → Event
  rcvE a = evLabel _ (receiveTS l d) a

  -- Deliver an ID reply before re-entering the requester loop.
  deliverIds : List TxHash → State → Body
  deliverIds xs s = Output ⦃ DecEq-ListTxHash ⦄ (apiTSev l d recvTSReplyTxIds) xs (Ret (inj₁ s))

  -- Deliver a transaction reply before re-entering the requester loop.
  deliverTxs : List Tx → State → Body
  deliverTxs xs s = Output ⦃ DI.DecEq-List ⦄ (apiTSev l d recvTSReplyTxs) xs (Ret (inj₁ s))

  -- Exact successful offers of the original pipelined requester.
  data HeadV (s : State) : Event → Body → Set₁ where
    hInit : ∀ {tm ln} → s ≡ awaitingInit → HeadV s (rcvE (tm , FromInitiator , ln , txSubmission (MsgTSInit))) (Ret (inj₁ (pending [] 0)))
    hBlock : ∀ a r → s ≡ pending [] zero → HeadV s (apiE sendTSRequestTxIdsBlocking (a , r)) (send l d (MsgTSRequestTxIds Blocking a r) blocking)
    hIds : ∀ {q c} a r → s ≡ pending q c → length q + c < k → HeadV s (apiE sendTSRequestTxIdsPipelined (a , r)) (send l d (MsgTSRequestTxIds NonBlocking a r) (pending (q ∷ʳ ids) c))
    hTxs : ∀ {q c} xs → s ≡ pending q c → length q + c < k → HeadV s (apiE sendTSRequestTxsPipelined (xs)) (send l d (MsgTSRequestTxs xs) (pending (q ∷ʳ txs) c))
    hReplyIds : ∀ {q c tm ln} xs → s ≡ pending (ids ∷ q) c → HeadV s (rcvE (tm , FromInitiator , ln , txSubmission (MsgTSReplyTxIds xs))) (deliverIds xs (pending q (suc c)))
    hReplyTxs : ∀ {q c tm ln} xs → s ≡ pending (txs ∷ q) c → HeadV s (rcvE (tm , FromInitiator , ln , txSubmission (MsgTSReplyTxs xs))) (deliverTxs xs (pending q (suc c)))
    hUnblock : ∀ {tm ln} x xs → s ≡ blocking → HeadV s (rcvE (tm , FromInitiator , ln , txSubmission (MsgTSReplyTxIds (x ∷ xs)))) (deliverIds (x ∷ xs) (pending [] 0))
    hDone : ∀ {tm ln} → s ≡ blocking → HeadV s (rcvE (tm , FromInitiator , ln , txSubmission (MsgTSDone))) (Ret (inj₂ _))

  -- Invert enabled offers and preserve their capacity and endpoint guards.
  headV : ∀ {s x t} → step k l d s ─[ ev (evl x) ]─► t → HeadV s x t
  headV {awaitingInit} (sVis {at = _ , receiveTS l′ d′} {a = _ , FromInitiator , _ , txSubmission (MsgTSInit)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hInit  refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending [] zero} (sVis {at = _ , apiTSev l′ d′ sendTSRequestTxIdsBlocking} {a = a , r} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hBlock a r refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending [] zero} (sVis {at = _ , apiTSev l′ d′ sendTSRequestTxIdsPipelined} {a = a , r} refl br) with l′ ≟ l | d′ ≟ d | (length {A = Reply} [] + zero) <? k
  ... | yes refl | yes refl | yes lt = subst (HeadV _ _) (just-injective br) (hIds a r refl lt)
  ... | no _ | _ | _ with () ← br
  ... | yes refl | no _ | _ with () ← br
  ... | yes refl | yes refl | no _ with () ← br
  headV {pending [] (suc c)} (sVis {at = _ , apiTSev l′ d′ sendTSRequestTxIdsPipelined} {a = a , r} refl br) with l′ ≟ l | d′ ≟ d | (length {A = Reply} [] + (suc c)) <? k
  ... | yes refl | yes refl | yes lt = subst (HeadV _ _) (just-injective br) (hIds a r refl lt)
  ... | no _ | _ | _ with () ← br
  ... | yes refl | no _ | _ with () ← br
  ... | yes refl | yes refl | no _ with () ← br
  headV {pending (x ∷ q) c} (sVis {at = _ , apiTSev l′ d′ sendTSRequestTxIdsPipelined} {a = a , r} refl br) with l′ ≟ l | d′ ≟ d | (length (x ∷ q) + c) <? k
  ... | yes refl | yes refl | yes lt = subst (HeadV _ _) (just-injective br) (hIds a r refl lt)
  ... | no _ | _ | _ with () ← br
  ... | yes refl | no _ | _ with () ← br
  ... | yes refl | yes refl | no _ with () ← br
  headV {pending [] zero} (sVis {at = _ , apiTSev l′ d′ sendTSRequestTxsPipelined} {a = xs} refl br) with l′ ≟ l | d′ ≟ d | (length {A = Reply} [] + zero) <? k
  ... | yes refl | yes refl | yes lt = subst (HeadV _ _) (just-injective br) (hTxs xs refl lt)
  ... | no _ | _ | _ with () ← br
  ... | yes refl | no _ | _ with () ← br
  ... | yes refl | yes refl | no _ with () ← br
  headV {pending [] (suc c)} (sVis {at = _ , apiTSev l′ d′ sendTSRequestTxsPipelined} {a = xs} refl br) with l′ ≟ l | d′ ≟ d | (length {A = Reply} [] + (suc c)) <? k
  ... | yes refl | yes refl | yes lt = subst (HeadV _ _) (just-injective br) (hTxs xs refl lt)
  ... | no _ | _ | _ with () ← br
  ... | yes refl | no _ | _ with () ← br
  ... | yes refl | yes refl | no _ with () ← br
  headV {pending (x ∷ q) c} (sVis {at = _ , apiTSev l′ d′ sendTSRequestTxsPipelined} {a = xs} refl br) with l′ ≟ l | d′ ≟ d | (length (x ∷ q) + c) <? k
  ... | yes refl | yes refl | yes lt = subst (HeadV _ _) (just-injective br) (hTxs xs refl lt)
  ... | no _ | _ | _ with () ← br
  ... | yes refl | no _ | _ with () ← br
  ... | yes refl | yes refl | no _ with () ← br
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS l′ d′} {a = _ , FromInitiator , _ , txSubmission (MsgTSReplyTxIds xs)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hReplyIds xs refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS l′ d′} {a = _ , FromInitiator , _ , txSubmission (MsgTSReplyTxs xs)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hReplyTxs xs refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {blocking} (sVis {at = _ , receiveTS l′ d′} {a = _ , FromInitiator , _ , txSubmission (MsgTSReplyTxIds (x ∷ xs))} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hUnblock x xs refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {blocking} (sVis {at = _ , receiveTS l′ d′} {a = _ , FromInitiator , _ , txSubmission (MsgTSDone)} refl br) with l′ ≟ l | d′ ≟ d
  ... | yes refl | yes refl = subst (HeadV _ _) (just-injective br) (hDone  refl)
  ... | no _ | _ with () ← br
  ... | yes refl | no _ with () ← br
  headV {awaitingInit} (sVis {at = _ , apiTSev _ _ sendTSReplyTxIds} refl ())
  headV {awaitingInit} (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
  headV {awaitingInit} (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
  headV {awaitingInit} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
  headV {awaitingInit} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsPipelined} refl ())
  headV {awaitingInit} (sVis {at = _ , apiTSev _ _ sendTSRequestTxsPipelined} refl ())
  headV {awaitingInit} (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
  headV {awaitingInit} (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
  headV {awaitingInit} (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
  headV {awaitingInit} (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
  headV {awaitingInit} (sVis {at = _ , sendTS _ _} refl ())
  headV {awaitingInit} (sVis {at = _ , doneTS _ _} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromResponder , _ , _} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSRequestTxIds _ _ _)} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSReplyTxIds [])} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSReplyTxIds (_ ∷ _))} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSRequestTxs _)} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSReplyTxs _)} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSDone)} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , keepAlive _} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , chainSync _} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , blockFetch _} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosNotify _} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosFetch _} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosNotifyP _} refl ())
  headV {awaitingInit} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosFetchP _} refl ())
  headV {blocking} (sVis {at = _ , apiTSev _ _ sendTSReplyTxIds} refl ())
  headV {blocking} (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
  headV {blocking} (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
  headV {blocking} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
  headV {blocking} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsPipelined} refl ())
  headV {blocking} (sVis {at = _ , apiTSev _ _ sendTSRequestTxsPipelined} refl ())
  headV {blocking} (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
  headV {blocking} (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
  headV {blocking} (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
  headV {blocking} (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
  headV {blocking} (sVis {at = _ , sendTS _ _} refl ())
  headV {blocking} (sVis {at = _ , doneTS _ _} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromResponder , _ , _} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSInit)} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSRequestTxIds _ _ _)} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSReplyTxIds [])} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSRequestTxs _)} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSReplyTxs _)} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , keepAlive _} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , chainSync _} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , blockFetch _} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosNotify _} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosFetch _} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosNotifyP _} refl ())
  headV {blocking} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosFetchP _} refl ())
  headV {pending [] zero} (sVis {at = _ , apiTSev _ _ sendTSReplyTxIds} refl ())
  headV {pending [] zero} (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
  headV {pending [] zero} (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
  headV {pending [] zero} (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
  headV {pending [] zero} (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
  headV {pending [] zero} (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
  headV {pending [] zero} (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
  headV {pending [] zero} (sVis {at = _ , sendTS _ _} refl ())
  headV {pending [] zero} (sVis {at = _ , doneTS _ _} refl ())
  headV {pending [] zero} (sVis {at = _ , receiveTS _ _} refl ())
  headV {pending [] (suc c)} (sVis {at = _ , apiTSev _ _ sendTSReplyTxIds} refl ())
  headV {pending [] (suc c)} (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
  headV {pending [] (suc c)} (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
  headV {pending [] (suc c)} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
  headV {pending [] (suc c)} (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
  headV {pending [] (suc c)} (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
  headV {pending [] (suc c)} (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
  headV {pending [] (suc c)} (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
  headV {pending [] (suc c)} (sVis {at = _ , sendTS _ _} refl ())
  headV {pending [] (suc c)} (sVis {at = _ , doneTS _ _} refl ())
  headV {pending [] (suc c)} (sVis {at = _ , receiveTS _ _} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , apiTSev _ _ sendTSReplyTxIds} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , sendTS _ _} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , doneTS _ _} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromResponder , _ , _} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSInit)} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSRequestTxIds _ _ _)} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSRequestTxs _)} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSReplyTxs _)} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSDone)} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , keepAlive _} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , chainSync _} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , blockFetch _} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosNotify _} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosFetch _} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosNotifyP _} refl ())
  headV {pending (ids ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosFetchP _} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , apiTSev _ _ sendTSReplyTxIds} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , apiTSev _ _ sendTSReplyTxs} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , apiTSev _ _ sendTSDone} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , apiTSev _ _ sendTSRequestTxIdsBlocking} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , apiTSev _ _ recvTSRequestTxIds} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , apiTSev _ _ recvTSRequestTxs} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , apiTSev _ _ recvTSReplyTxIds} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , apiTSev _ _ recvTSReplyTxs} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , sendTS _ _} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , doneTS _ _} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromResponder , _ , _} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSInit)} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSRequestTxIds _ _ _)} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSReplyTxIds [])} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSReplyTxIds (_ ∷ _))} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSRequestTxs _)} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , txSubmission (MsgTSDone)} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , keepAlive _} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , chainSync _} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , blockFetch _} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosNotify _} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosFetch _} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosNotifyP _} refl ())
  headV {pending (txs ∷ q) c} (sVis {at = _ , receiveTS _ _} {a = _ , FromInitiator , _ , leiosFetchP _} refl ())

  -- Lift head inversion through the iteration wrapper.
  head-inv : ∀ {s x M} → It (step k l d s) ─[ ev (evl x) ]─► M →
    Σ[ t ∈ Body ] (HeadV s x t × M ≡ It t)
  head-inv {s} st with iter-ev-elim (step k l d s) (step k l d) st
  ... | t , st′ , refl = t , headV st′ , refl

  -- Output residuals expose exactly their selected value.
  out-inv : ∀ {B} {dd : DecEq B} {ch : TSEv B} {v a x M} →
    It (Output ⦃ dd ⦄ ch v (Ret a)) ─[ ev (evl x) ]─► M →
    x ≡ evLabel B ch v × M ≡ It (Ret a)
  out-inv {dd = dd} {ch} {v} {a} st
    with iter-ev-elim (Output ⦃ dd ⦄ ch v (Ret a)) (step k l d) st
  ... | _ , st′ , refl with out-ev ⦃ dd ⦄ st′
  ... | refl , refl = refl , refl

  -- Return residuals cannot produce visible events.
  ret-noev : ∀ {a x M} → ¬ (It (Ret a) ─[ ev (evl x) ]─► M)
  ret-noev {a} st with iter-ev-elim (Ret a) (step k l d) st
  ... | _ , sVis () _ , _

  -- Output continuations are stable until their visible event fires.
  noτ : ∀ {t v M} → PTree.force t ≡ react v ∅t → ¬ (It t ─[ τ ]─► M)
  noτ {t} eq st with iter-τ-elim t (step k l d) st
  ... | itτ _ (sSil eq′) _ = case trans (sym eq) eq′ of λ ()
  ... | itBack _ eq′ _ = case trans (sym eq) eq′ of λ ()
  ... | itτ _ (sTau eq′ br) _ with trans (sym eq) eq′
  ... | refl = case br of λ ()

  -- A returned next state silently re-enters its loop head.
  back-inv : ∀ {s M} → It (Ret (inj₁ s)) ─[ τ ]─► M → M ≡ It (step k l d s)
  back-inv {s} st with iter-τ-elim (Ret (inj₁ s)) (step k l d) st
  ... | itτ _ (sSil ()) _
  ... | itτ _ (sTau () _) _
  ... | itBack _ refl refl = refl

  -- A final return has no silent successor.
  end-noτ : ∀ {u M} → ¬ (It (Ret (inj₂ u)) ─[ τ ]─► M)
  end-noτ {u} st with iter-τ-elim (Ret (inj₂ u)) (step k l d) st
  ... | itτ _ (sSil ()) _
  ... | itτ _ (sTau () _) _
  ... | itBack _ () _

  -- The only silent head transition collects one completed receiver result.
  collect-inv : ∀ {rs c M} → It (step k l d (pending rs c)) ─[ τ ]─► M →
    Σ[ c′ ∈ ℕ ] (c ≡ suc c′ × M ≡ It (Ret (inj₁ (pending rs c′))))
  collect-inv {rs} {c} st with iter-τ-elim (step k l d (pending rs c)) (step k l d) st
  ... | itBack _ () _
  ... | itτ _ (sSil ()) _
  collect-inv {rs} {zero} st | itτ _ (sTau refl ()) _
  collect-inv {rs} {suc c} st | itτ _ (sTau refl br) refl
    with refl ← just-injective br = c , refl , refl

  -- Lift a visible round transition through iteration.
  fire : ∀ {t t′ x} → t ─[ ev (evl x) ]─► t′ → It t ─[ ev (evl x) ]─► It t′
  fire {t} = iter-bind-ev (step k l d) t

  -- The loop-back is a single silent step.
  back : ∀ {s} → It (Ret (inj₁ s)) ─[ τ ]─► It (step k l d s)
  back = sSil refl

  -- Collection is available at every head with a completed result.
  collect-fire : ∀ {rs c} → It (step k l d (pending rs (suc c))) ─[ τ ]─►
    It (Ret (inj₁ (pending rs c)))
  collect-fire {rs} {c} = iter-bind-τ (step k l d) _
    (sTau {i = _ , base (sendTS l d)} {a = time₀ , FromInitiator , length₀ , txSubmission MsgTSInit} refl refl)

  -- Init and blocking rounds have no completed asynchronous result.
  init-noτ : ∀ {M} → ¬ (It (step k l d awaitingInit) ─[ τ ]─► M)
  init-noτ = noτ refl

  -- Blocking requests exclude asynchronous collection.
  blocking-noτ : ∀ {M} → ¬ (It (step k l d blocking) ─[ τ ]─► M)
  blocking-noτ = noτ refl

  -- Construct the Init offer at this endpoint.
  fire-Init : step k l d (awaitingInit) ─[ ev (evl (rcvE (time₀ , FromInitiator , length₀ , txSubmission (MsgTSInit)))) ]─► (Ret (inj₁ (pending [] 0)))
  fire-Init  = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (awaitingInit) (_ , receiveTS l d) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSInit)) ≡ just (Ret (inj₁ (pending [] 0)))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the Block offer at this endpoint.
  fire-Block : ∀ a r → step k l d (pending [] zero) ─[ ev (evl (apiE sendTSRequestTxIdsBlocking (a , r))) ]─► (send l d (MsgTSRequestTxIds Blocking a r) blocking)
  fire-Block a r = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (pending [] zero) (_ , apiTSev l d sendTSRequestTxIdsBlocking) (a , r) ≡ just (send l d (MsgTSRequestTxIds Blocking a r) blocking)
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the Ids offer at this endpoint.
  fire-Ids : ∀ {q c} a r → length q + c < k → step k l d (pending q c) ─[ ev (evl (apiE sendTSRequestTxIdsPipelined (a , r))) ]─► (send l d (MsgTSRequestTxIds NonBlocking a r) (pending (q ∷ʳ ids) c))
  fire-Ids {[]} {zero} a r lt = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (pending [] zero) (_ , apiTSev l d sendTSRequestTxIdsPipelined) (a , r) ≡ just (send l d (MsgTSRequestTxIds NonBlocking a r) (pending ([] ∷ʳ ids) zero))
    br with l ≟ l | d ≟ d | (length {A = Reply} [] + zero) <? k
    ... | yes refl | yes refl | yes _ = refl
    ... | no bad | _ | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | yes refl | no bad = ⊥-elim (bad lt)

  fire-Ids {[]} {(suc c)} a r lt = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (pending [] (suc c)) (_ , apiTSev l d sendTSRequestTxIdsPipelined) (a , r) ≡ just (send l d (MsgTSRequestTxIds NonBlocking a r) (pending ([] ∷ʳ ids) (suc c)))
    br with l ≟ l | d ≟ d | (length {A = Reply} [] + (suc c)) <? k
    ... | yes refl | yes refl | yes _ = refl
    ... | no bad | _ | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | yes refl | no bad = ⊥-elim (bad lt)

  fire-Ids {(x ∷ q)} {c} a r lt = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (pending (x ∷ q) c) (_ , apiTSev l d sendTSRequestTxIdsPipelined) (a , r) ≡ just (send l d (MsgTSRequestTxIds NonBlocking a r) (pending ((x ∷ q) ∷ʳ ids) c))
    br with l ≟ l | d ≟ d | (length (x ∷ q) + c) <? k
    ... | yes refl | yes refl | yes _ = refl
    ... | no bad | _ | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | yes refl | no bad = ⊥-elim (bad lt)


  -- Construct the Txs offer at this endpoint.
  fire-Txs : ∀ {q c} xs → length q + c < k → step k l d (pending q c) ─[ ev (evl (apiE sendTSRequestTxsPipelined (xs))) ]─► (send l d (MsgTSRequestTxs xs) (pending (q ∷ʳ txs) c))
  fire-Txs {[]} {zero} xs lt = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (pending [] zero) (_ , apiTSev l d sendTSRequestTxsPipelined) (xs) ≡ just (send l d (MsgTSRequestTxs xs) (pending ([] ∷ʳ txs) zero))
    br with l ≟ l | d ≟ d | (length {A = Reply} [] + zero) <? k
    ... | yes refl | yes refl | yes _ = refl
    ... | no bad | _ | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | yes refl | no bad = ⊥-elim (bad lt)

  fire-Txs {[]} {(suc c)} xs lt = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (pending [] (suc c)) (_ , apiTSev l d sendTSRequestTxsPipelined) (xs) ≡ just (send l d (MsgTSRequestTxs xs) (pending ([] ∷ʳ txs) (suc c)))
    br with l ≟ l | d ≟ d | (length {A = Reply} [] + (suc c)) <? k
    ... | yes refl | yes refl | yes _ = refl
    ... | no bad | _ | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | yes refl | no bad = ⊥-elim (bad lt)

  fire-Txs {(x ∷ q)} {c} xs lt = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (pending (x ∷ q) c) (_ , apiTSev l d sendTSRequestTxsPipelined) (xs) ≡ just (send l d (MsgTSRequestTxs xs) (pending ((x ∷ q) ∷ʳ txs) c))
    br with l ≟ l | d ≟ d | (length (x ∷ q) + c) <? k
    ... | yes refl | yes refl | yes _ = refl
    ... | no bad | _ | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | yes refl | no bad = ⊥-elim (bad lt)


  -- Construct the ReplyIds offer at this endpoint.
  fire-ReplyIds : ∀ {q c} xs → step k l d (pending (ids ∷ q) c) ─[ ev (evl (rcvE (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds xs)))) ]─► (deliverIds xs (pending q (suc c)))
  fire-ReplyIds {q} {c} xs = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (pending (ids ∷ q) c) (_ , receiveTS l d) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds xs)) ≡ just (deliverIds xs (pending q (suc c)))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the ReplyTxs offer at this endpoint.
  fire-ReplyTxs : ∀ {q c} xs → step k l d (pending (txs ∷ q) c) ─[ ev (evl (rcvE (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs xs)))) ]─► (deliverTxs xs (pending q (suc c)))
  fire-ReplyTxs {q} {c} xs = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (pending (txs ∷ q) c) (_ , receiveTS l d) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs xs)) ≡ just (deliverTxs xs (pending q (suc c)))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the Unblock offer at this endpoint.
  fire-Unblock : ∀ x xs → step k l d (blocking) ─[ ev (evl (rcvE (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds (x ∷ xs))))) ]─► (deliverIds (x ∷ xs) (pending [] 0))
  fire-Unblock x xs = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (blocking) (_ , receiveTS l d) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds (x ∷ xs))) ≡ just (deliverIds (x ∷ xs) (pending [] 0))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

  -- Construct the Done offer at this endpoint.
  fire-Done : step k l d (blocking) ─[ ev (evl (rcvE (time₀ , FromInitiator , length₀ , txSubmission (MsgTSDone)))) ]─► (Ret (inj₂ _))
  fire-Done  = sVis refl br
    where
    -- Endpoint reflexivity and the supplied guard enable this branch.
    br : menu k l d (blocking) (_ , receiveTS l d) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSDone)) ≡ just (Ret (inj₂ _))
    br with l ≟ l | d ≟ d
    ... | yes refl | yes refl = refl
    ... | no bad | _ = ⊥-elim (bad refl)
    ... | yes refl | no bad = ⊥-elim (bad refl)

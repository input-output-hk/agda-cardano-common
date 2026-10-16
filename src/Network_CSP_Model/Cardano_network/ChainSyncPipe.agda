{-# OPTIONS --guardedness #-}

-- Bounded RequestNext pipelining over the existing ChainSync alphabet.
open import Cardano_network.Params using (Params)
module Cardano_network.ChainSyncPipe (p : Params) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_<?_)
open import Data.Product using (_,_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (refl)
open import Class.DecEq using (_≟_)
open import Process_Trees
open import Cardano_network.Base
open import Cardano_network.Data p
open Params p
open import Cardano_network.Net p
open import Cardano_network.ChainSync p
  using (CSEv; sendCS; receiveCS; apiCSev; CSEv-≟; Rr;
         DecEq-Header×Tip; DecEq-Point×Tip; CSserverStClient)
import CSP.Operators {E = CSEv} as Ops
open Ops CSEv-≟

-- AwaitReply changes only the oldest request's response phase.
data Phase : Set where
  canAwait mustReply : Phase

-- Completed results consume credit until collected; intersection is exclusive.
data State : Set where
  pending : ℕ → Phase → ℕ → State
  intersect : State

-- Every generation starts empty.
initial : State
initial = pending 0 canAwait 0

-- Loop bodies continue or terminate successfully.
Body : Set₁
Body = PTree CSEv (ExtI CSEv) (State ⊎ Rr)

-- Emit the initiator message before advancing the state.
send : Link → Dir → MessageChainSync → State ⊎ Rr → Body
send l d m s = sendCS l d ! (time₀ , FromInitiator , length₀ , chainSync m) ⟶ Ret s

-- Reception and new requests coexist whenever sender credit permits.
menu : ℕ → Link → Dir → State →
  (at : AnyTypes CSEv) → ContinueType at (Maybe Body)
menu k l d (pending n ph c) (_ , apiCSev l′ d′ sendCSRequestNext) _
  with l′ ≟ l | d′ ≟ d | (n + c) <? k
... | yes refl | yes refl | yes _ = just
  (send l d MsgCSRequestNext (inj₁ (pending (suc n) ph c)))
... | _ | _ | _ = nothing
menu k l d (pending zero canAwait zero) (_ , apiCSev l′ d′ sendCSFindIntersect) pts
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (send l d (MsgCSFindIntersect pts) (inj₁ intersect))
... | _ | _ = nothing
menu k l d (pending zero canAwait zero) (_ , apiCSev l′ d′ sendCSDone) _
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (send l d MsgCSDone (inj₂ _))
... | _ | _ = nothing
menu k l d (pending (suc n) canAwait c) (_ , receiveCS l′ d′)
  (_ , FromResponder , _ , chainSync MsgCSAwaitReply) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (Ret (inj₁ (pending (suc n) mustReply c)))
... | _ | _ = nothing
menu k l d (pending (suc n) ph c) (_ , receiveCS l′ d′)
  (_ , FromResponder , _ , chainSync (MsgCSRollForward h t)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just
  (apiCSev l d recvCSRollforward ! (h , t) ⟶ Ret (inj₁ (pending n canAwait (suc c))))
... | _ | _ = nothing
menu k l d (pending (suc n) ph c) (_ , receiveCS l′ d′)
  (_ , FromResponder , _ , chainSync (MsgCSRollBackward pt t)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just
  (apiCSev l d recvCSRollback ! (pt , t) ⟶ Ret (inj₁ (pending n canAwait (suc c))))
... | _ | _ = nothing
menu k l d intersect (_ , receiveCS l′ d′)
  (_ , FromResponder , _ , chainSync (MsgCSIntersectFound pt t)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just
  (apiCSev l d recvCSIntersectFound ! (pt , t) ⟶ Ret (inj₁ initial))
... | _ | _ = nothing
menu k l d intersect (_ , receiveCS l′ d′)
  (_ , FromResponder , _ , chainSync (MsgCSIntersectNotFound t)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just
  (apiCSev l d recvCSIntersectNotFound ! t ⟶ Ret (inj₁ initial))
... | _ | _ = nothing
menu _ _ _ _ _ _ = nothing

-- Collection releases credit without consuming a wire event.
collect : State → Maybe Body
collect (pending n ph (suc c)) = just (Ret (inj₁ (pending n ph c)))
collect _ = nothing

-- Keep visible offers and silent collection in one react node.
step : ℕ → Link → Dir → State → Body
step k l d s = ptree (react (menu k l d s) (λ _ _ → collect s))

-- k bounds outstanding plus completed-uncollected requests.
client : ℕ → Link → Dir → PTree CSEv (ExtI CSEv) Rr
client k l d = iter (step k l d) initial

-- The producer consumes requests sequentially, as in the pinned prototype.
server : Link → Dir → PTree CSEv (ExtI CSEv) Rr
server = CSserverStClient

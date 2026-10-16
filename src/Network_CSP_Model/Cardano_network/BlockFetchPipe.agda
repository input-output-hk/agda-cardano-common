{-# OPTIONS --guardedness #-}

-- Bounded request pipelining over the existing BlockFetch peer alphabet.
open import Cardano_network.Params using (Params)
module Cardano_network.BlockFetchPipe (p : Params) where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Properties using (_<?_)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
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
open import Cardano_network.BlockFetch p
  using (BFEv; sendBF; receiveBF; apiBFev; BFEv-≟; Rr; BFserverStClient)
import CSP.Operators {E = BFEv} as Ops
open Ops BFEv-≟

-- Phase of the oldest unanswered range.
data Phase : Set where
  waiting streaming : Phase

-- Completed receiver results consume sender credit until collected.
record State : Set where
  constructor pending
  field
    ranges : List ChainRange
    phase : Phase
    completed : ℕ
open State public

-- Empty initial pipeline.
initial : State
initial = pending [] waiting 0

-- Credit includes unanswered ranges and completed, uncollected results.
occupancy : State → ℕ
occupancy s = length (ranges s) + completed s

-- Loop bodies return a state or successful termination.
Body : Set₁
Body = PTree BFEv (ExtI BFEv) (State ⊎ Rr)

-- Emit an initiator message before advancing the loop.
send : Link → Dir → MessageBlockFetch → State ⊎ Rr → Body
send l d m s = sendBF l d ! (time₀ , FromInitiator , length₀ , blockFetch m) ⟶ Ret s

-- Requests coexist with the oldest response while sender credit permits.
-- Receive checks include link, direction, and responder payload agency.
menu : ℕ → Link → Dir → State
     → (at : AnyTypes BFEv) → ContinueType at (Maybe Body)
menu k l d s (_ , apiBFev l′ d′ sendBFRequestRange) r
  with l′ ≟ l | d′ ≟ d | occupancy s <? k
... | yes refl | yes refl | yes _ = just
  (send l d (MsgRequestRange r)
    (inj₁ (pending (ranges s ∷ʳ r) (phase s) (completed s))))
... | _ | _ | _ = nothing
menu k l d (pending [] waiting zero) (_ , apiBFev l′ d′ sendBFClientDone) _
  with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (send l d MsgClientDone (inj₂ _))
... | _ | _ = nothing
menu k l d (pending (r ∷ rs) waiting c) (_ , receiveBF l′ d′)
  (_ , FromResponder , _ , blockFetch MsgStartBatch) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (Ret (inj₁ (pending (r ∷ rs) streaming c)))
... | _ | _ = nothing
menu k l d (pending (r ∷ rs) waiting c) (_ , receiveBF l′ d′)
  (_ , FromResponder , _ , blockFetch MsgNoBlocks) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (Ret (inj₁ (pending rs waiting (suc c))))
... | _ | _ = nothing
menu k l d (pending (r ∷ rs) streaming c) (_ , receiveBF l′ d′)
  (_ , FromResponder , _ , blockFetch (MsgBlock b)) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just
  (apiBFev l d recvBFBlock ! b ⟶ Ret (inj₁ (pending (r ∷ rs) streaming c)))
... | _ | _ = nothing
menu k l d (pending (r ∷ rs) streaming c) (_ , receiveBF l′ d′)
  (_ , FromResponder , _ , blockFetch MsgBatchDone) with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = just (Ret (inj₁ (pending rs waiting (suc c))))
... | _ | _ = nothing
menu k l d s _ _ = nothing

-- Collect a completed receiver result silently, releasing one sender credit.
collect : State → Maybe Body
collect (pending rs ph zero) = nothing
collect (pending rs ph (suc c)) = just (Ret (inj₁ (pending rs ph c)))

-- Visible offers coexist with silent collection in the same react node.
-- Every internal branch index denotes the same collection continuation.
step : ℕ → Link → Dir → State → Body
step k l d s = ptree (react (menu k l d s) (λ _ _ → collect s))

-- The bounded client starts empty; k=0 permits only termination.
client : ℕ → Link → Dir → PTree BFEv (ExtI BFEv) Rr
client k l d = iter (step k l d) initial

-- As in the prototype, the server processes one complete range at a time.
server : Link → Dir → PTree BFEv (ExtI BFEv) Rr
server = BFserverStClient

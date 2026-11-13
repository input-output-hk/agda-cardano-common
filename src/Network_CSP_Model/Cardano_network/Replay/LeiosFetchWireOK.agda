{-# OPTIONS --safe #-}

-- Client receive-side summary limits are independent of session order.
module Cardano_network.Replay.LeiosFetchWireOK where

open import Data.Bool using (T)
open import Data.List using (List)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Nat using (_≤_)
open import Data.Unit using (⊤; tt)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Cardano_network.Replay.LeiosFetchWire using (validᵇ; popcount; maxTxs; txsCap; ebCap)
open import Cardano_network.Replay.LeiosFetchSession

-- Requests need no extra premise; only received replies have decoder limits.
WireMsg : E → Set
WireMsg (_ , MsgLeiosBlockRequest _ _) = ⊤
WireMsg (Send , MsgLeiosBlock _ _) = ⊤
WireMsg (Recv , MsgLeiosBlock _ z) = z ≤ ebCap
WireMsg (_ , MsgLeiosBlockTxsRequest _ _ _ _) = ⊤
WireMsg (Send , MsgLeiosBlockTxs _ _) = ⊤
WireMsg (Recv , MsgLeiosBlockTxs n z) = n ≤ maxTxs × z ≤ txsCap
WireMsg (_ , MsgLeiosDone) = ⊤

-- Receive-side admissibility constrains logged byte sizes and reply counts.
WireOK : List E → Set
WireOK = All WireMsg

module _ (k : Data.Nat.ℕ) where
  open Spec k
  open import Semantics.Replay using (module Traces)
  open Traces leiosFetch

  -- Every legal visible session step satisfies its message's decoder checks.
  step-wire : ∀ {s e s′} → s -[ e ]→ s′ → WireMsg e
  step-wire (cSendBlockReq _) = tt
  step-wire (cSendTxsReq _ valid count _) = tt
  step-wire (cRecvBlock cap) = cap
  step-wire (cRecvTxs cap bytes) = cap , bytes
  step-wire cSendDone = tt
  step-wire (cDrainBlock cap) = cap
  step-wire (cDrainTxs cap bytes) = cap , bytes
  step-wire cDrainDone = tt
  step-wire sRecvBlockReq = tt
  step-wire (sRecvTxsReq valid count) = tt
  step-wire sSendBlock = tt
  step-wire sSendTxs = tt
  step-wire sRecvDone = tt

  -- Silent service and stop choices preserve message-wise admissibility.
  trace-wire : ∀ {s es s′} → s ⇒⟨ es ⟩ s′ → WireOK es
  trace-wire done = []
  trace-wire (tau _ run) = trace-wire run
  trace-wire (vis step run) = step-wire step ∷ trace-wire run

  -- Both roles' accepted traces carry the premise used in soundness.
  accepted-wire : ∀ {s es} → HasTrace s es → WireOK es
  accepted-wire (_ , run) = trace-wire run

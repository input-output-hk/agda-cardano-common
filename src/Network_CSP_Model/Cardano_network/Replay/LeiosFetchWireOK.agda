{-# OPTIONS --safe #-}

-- Decoder admissibility is independent of session order and observation.
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

-- Each logged message satisfies its own wire checks, with no agency assumption.
WireMsg : E → Set
WireMsg (_ , MsgLeiosBlockRequest _ _) = ⊤
WireMsg (_ , MsgLeiosBlock _ z) = z ≤ ebCap
WireMsg (_ , MsgLeiosBlockTxsRequest _ _ n b) = T (validᵇ b) × n ≡ popcount b
WireMsg (_ , MsgLeiosBlockTxs n z) = n ≤ maxTxs × z ≤ txsCap
WireMsg (_ , MsgLeiosDone) = ⊤

-- Admissibility retains sizes and bitmap validity that observation forgets.
WireOK : List E → Set
WireOK = All WireMsg

module _ (k : Data.Nat.ℕ) where
  open Spec k
  open import Semantics.Replay using (module Traces)
  open Traces leiosFetch

  -- Every legal visible session step satisfies its message's decoder checks.
  step-wire : ∀ {s e s′} → s -[ e ]→ s′ → WireMsg e
  step-wire (cSendBlockReq _) = tt
  step-wire (cSendTxsReq _ valid count _) = valid , count
  step-wire (cRecvBlock cap) = cap
  step-wire (cRecvTxs cap bytes) = cap , bytes
  step-wire cSendDone = tt
  step-wire (cDrainBlock cap) = cap
  step-wire (cDrainTxs cap bytes) = cap , bytes
  step-wire cDrainDone = tt
  step-wire sRecvBlockReq = tt
  step-wire (sRecvTxsReq valid count) = valid , count
  step-wire (sSendBlock cap) = cap
  step-wire (sSendTxs cap bytes) = cap , bytes
  step-wire sRecvDone = tt

  -- Silent service and stop choices preserve message-wise admissibility.
  trace-wire : ∀ {s es s′} → s ⇒⟨ es ⟩ s′ → WireOK es
  trace-wire done = []
  trace-wire (tau _ run) = trace-wire run
  trace-wire (vis step run) = step-wire step ∷ trace-wire run

  -- Both roles' accepted traces carry the premise used in soundness.
  accepted-wire : ∀ {s es} → HasTrace s es → WireOK es
  accepted-wire (_ , run) = trace-wire run

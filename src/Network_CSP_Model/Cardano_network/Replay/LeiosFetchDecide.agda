{-# OPTIONS --safe #-}

-- τ-accessibility certificate for the LeiosFetch session spec (trace-replay
-- Phase 4): sServe, sThrow and cStop all target τ-stable states, so
-- every τ-path has length at most 1. Hence
-- the decider applies from both initial states. Constructive, no measure.
module Cardano_network.Replay.LeiosFetchDecide where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.String using (String; _++_)

open import Semantics.Replay.Decide
open import Cardano_network.Replay.LeiosFetchSession

-- The certificate for pipelining bound k.
module Cert (k : ℕ) where
  open Spec k
  open Decider leiosFetch public

  -- Every τ-successor is τ-stable (ready, thrown, or draining).
  τ-succ-acc : ∀ {s s′} → s -τ→ s′ → τAcc s′
  τ-succ-acc sServe = acc λ ()
  τ-succ-acc sThrow = acc λ ()
  τ-succ-acc cStop = acc λ ()

  -- τ is well-founded on every state.
  τAcc-all : ∀ s → τAcc s
  τAcc-all _ = acc τ-succ-acc

  -- Reachable-state hypothesis for a client-role session.
  client-cert : τAccReach client₀
  client-cert = τAccReach-all τAcc-all client₀

  -- Reachable-state hypothesis for a server-role session.
  server-cert : τAccReach server₀
  server-cert = τAccReach-all τAcc-all server₀

  -- The checked path always serves the server and never stops the client.
  checkedState : St → St
  checkedState (sBusy r) = sReady r
  checkedState st = st

  -- Explain when a failed client check could only have been silently drained.
  drainNote : St → E → String
  drainNote (cOpen q) e with after (cDrain q) e
  ... | [] = ""
  ... | _ ∷ _ = " (accepted only by a draining client; a later event rules that out)"
  drainNote _ _ = ""

  -- Retain the checked failure index, reason, and rejection-only drain qualification.
  checkedFailure : St → ℕ → List E → Maybe (ℕ × String × String)
  checkedFailure st i [] = nothing
  checkedFailure st i (e ∷ es) with after (checkedState st) e
  ... | [] = just (i , whyRejected (checkedState st) e , drainNote (checkedState st) e)
  ... | st′ ∷ _ = checkedFailure st′ (suc i) es

  -- Rejections use the initial checked history, independent of drain/throw witnesses.
  -- The defensive fallback is a real state diagnostic, never the success sentinel.
  rejectionReason : St → St → List E → String
  rejectionReason initial witness es with checkedFailure initial 1 es
  ... | just (i , reason , note) = reason ++ " at index " ++ showℕ i ++ note
  ... | nothing = noStepWhy witness

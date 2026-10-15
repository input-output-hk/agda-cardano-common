{-# OPTIONS --safe #-}

-- τ-accessibility certificate for the LeiosFetch session spec (trace-replay
-- Phase 4): the only τ step is `sServe : sBusy r -τ→ sReady r`, and
-- `sReady r` has no τ step, so every τ-path has length at most 1. Hence
-- the decider applies from both initial states. Constructive, no measure.
module Cardano_network.Replay.LeiosFetchDecide where

open import Data.Nat using (ℕ)

open import Semantics.Replay.Decide
open import Cardano_network.Replay.LeiosFetchSession

-- The certificate for pipelining bound k.
module Cert (k : ℕ) where
  open Spec k
  open Decider leiosFetch public

  -- Every τ-successor is τ-stable (sReady has no τ step).
  τ-succ-acc : ∀ {s s′} → s -τ→ s′ → τAcc s′
  τ-succ-acc sServe = acc λ ()

  -- τ is well-founded on every state.
  τAcc-all : ∀ s → τAcc s
  τAcc-all _ = acc τ-succ-acc

  -- Reachable-state hypothesis for a client-role session.
  client-cert : τAccReach client₀
  client-cert = τAccReach-all τAcc-all client₀

  -- Reachable-state hypothesis for a server-role session.
  server-cert : τAccReach server₀
  server-cert = τAccReach-all τAcc-all server₀

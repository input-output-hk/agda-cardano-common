{-# OPTIONS --safe #-}

-- Arithmetic shared by pipeline-to-wire control abstractions.
module Cardano_network.Replay.PipelineBounds where

open import Data.Nat using (ℕ; zero; suc; _+_; _<_; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans)

-- Completed but uncollected results can only increase occupied credit.
left≤sum : ∀ n c → n ≤ n + c
left≤sum zero c = z≤n
left≤sum (suc n) c = s≤s (left≤sum n c)

-- Forgetting completed results preserves an upper bound on unanswered work.
wire-bound : ∀ {n c k} → n + c < k → n < k
wire-bound {n} {c} lt = ≤-trans (s≤s (left≤sum n c)) lt

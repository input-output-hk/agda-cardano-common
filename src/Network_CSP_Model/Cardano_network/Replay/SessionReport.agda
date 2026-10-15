{-# OPTIONS --safe #-}

-- Pure reporting for the single interleaved-session replay model.
module Cardano_network.Replay.SessionReport where

open import Data.List using (List; []; _∷_; length; take; drop)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _≤ᵇ_)
open import Data.Nat.DivMod using (_/_)
open import Data.Bool using (true; false)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product using (_,_)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Cardano_network.Replay.Sessions
open import Cardano_network.Replay.ParseSessions

-- Locate the first rejection and display the targeted session's prior state.
scan : (k depth : ℕ) (rs : List Session) → List (Events rs) → ℕ →
       States rs → List (Events rs) → String
scan k depth rs es i st [] = "accepted (" ++ showℕ i ++ " events)"
scan k depth rs es i st (e ∷ rest) with checkWithDepth k depth rs (take (suc i) es)
... | yes (st′ , _) = scan k depth rs es (suc i) st′ rest
... | no _ = "rejected at index " ++ showℕ (suc i) ++
             " (session " ++ showℕ (index e) ++ "): " ++ showEvent e ++
             "\nmodel session state after " ++ showℕ i ++ " events: " ++ componentState st e

-- Binary search between an accepted and rejected prefix; fuel ensures termination.
-- Prefix closure makes rejection monotone. Each split strictly shrinks a gap > 1.
firstRejected : (k depth : ℕ) (rs : List Session) → List (Events rs) → ℕ → ℕ → ℕ → ℕ
firstRejected k depth rs es zero lo hi = hi
firstRejected k depth rs es (suc fuel) lo hi with hi ≤ᵇ suc lo
... | true = hi
... | false with checkWithDepth k depth rs (take ((lo + hi) / 2) es)
...   | yes _ = firstRejected k depth rs es fuel ((lo + hi) / 2) hi
...   | no _ = firstRejected k depth rs es fuel lo ((lo + hi) / 2)

-- Verify the preceding accepted prefix and report its residual component state.
-- Falling back to the sequential scan keeps diagnostics total without assumptions.
rejection : (k depth : ℕ) (rs : List Session) → List (Events rs) → ℕ → String
rejection k depth rs es i with checkWithDepth k depth rs (take (i ∸ 1) es) | drop (i ∸ 1) es
... | yes (st , _) | e ∷ _ = "rejected at index " ++ showℕ i ++
  " (session " ++ showℕ (index e) ++ "): " ++ showEvent e ++
  "\nmodel session state after " ++ showℕ (i ∸ 1) ++ " events: " ++ componentState st e
... | _ | _ = scan k depth rs es 0 (initial rs) es

-- Decide the complete global trace before scanning rejected prefixes.
verdict : (k depth : ℕ) (rs : List Session) → List (Events rs) → String
verdict k depth rs es with checkWithDepth k depth rs es
... | yes _ = "accepted (" ++ showℕ (length es) ++ " events, " ++ showℕ (length rs) ++ " sessions)"
... | no _ = rejection k depth rs es (firstRejected k depth rs es (length es) 0 (length es))

-- Parse and check one interleaved file.
reportWithDepth : ℕ → ℕ → String → String
reportWithDepth k depth s with parse s
... | inj₁ (l , txt) = "parse error at line " ++ showℕ l ++ ": " ++ txt
... | inj₂ (rs , es) = verdict k depth rs es

-- Check a standalone Notify session through the same certified product.
reportNotifyWithDepth : ℕ → String → String
reportNotifyWithDepth depth s with parseNotify s
... | inj₁ (l , txt) = "parse error at line " ++ showℕ l ++ ": " ++ txt
... | inj₂ (rs , es) = verdict 4 depth rs es

-- Legacy interleaved calls retain depth one for Notify.
report : ℕ → String → String
report k = reportWithDepth k 1

-- Legacy standalone calls retain depth one for Notify.
reportNotify : String → String
reportNotify = reportNotifyWithDepth 1

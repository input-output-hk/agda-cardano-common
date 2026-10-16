{-# OPTIONS --safe #-}

-- Pure reporting for the single interleaved-session replay model.
module Cardano_network.Replay.LeiosFetchInterleavedReport where

open import Data.List using (List; []; _∷_; length; take)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product using (_,_)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Cardano_network.Replay.LeiosFetchParse using (Role; showEvent)
open import Cardano_network.Replay.LeiosFetchInterleaved
open import Cardano_network.Replay.LeiosFetchParseInterleaved

-- Locate the first rejection and display the targeted session's prior state.
scan : (k : ℕ) (rs : List Role) → List (Events (length rs)) → ℕ →
       States (length rs) → List (Events (length rs)) → String
scan k rs es i st [] = "accepted (" ++ showℕ i ++ " events)"
scan k rs es i st (e ∷ rest) with check k rs (take (suc i) es)
... | yes (st′ , _) = scan k rs es (suc i) st′ rest
... | no _ = "rejected at index " ++ showℕ (suc i) ++
             " (session " ++ showℕ (index e) ++ "): " ++ showEvent (localEvent e) ++
             "\nmodel session state after " ++ showℕ i ++ " events: " ++ componentState st e

-- Decide the complete global trace before scanning rejected prefixes.
verdict : (k : ℕ) (rs : List Role) → List (Events (length rs)) → String
verdict k rs es with check k rs es
... | yes _ = "accepted (" ++ showℕ (length es) ++ " events, " ++ showℕ (length rs) ++ " sessions)"
... | no _ = scan k rs es 0 (initial rs) es

-- Parse and check one interleaved file.
report : ℕ → String → String
report k s with parse s
... | inj₁ (l , txt) = "parse error at line " ++ showℕ l ++ ": " ++ txt
... | inj₂ (rs , es) = verdict k rs es

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
scanWithProtocolDepths : (k depth bfDepth csDepth tsDepth : ℕ) (rs : List Session) → List (Events rs) → ℕ →
       States rs → List (Events rs) → String
scanWithProtocolDepths k depth bfDepth csDepth tsDepth rs es i st [] = "accepted (" ++ showℕ i ++ " events)"
scanWithProtocolDepths k depth bfDepth csDepth tsDepth rs es i st (e ∷ rest) with checkWithProtocolDepths k depth bfDepth csDepth tsDepth rs (take (suc i) es)
... | yes (st′ , _) = scanWithProtocolDepths k depth bfDepth csDepth tsDepth rs es (suc i) st′ rest
... | no _ = "rejected at index " ++ showℕ (suc i) ++
             " (session " ++ showℕ (index e) ++ "): " ++ showEvent e ++
             "\nmodel session state after " ++ showℕ i ++ " events: " ++ componentState st e

-- Binary search between an accepted and rejected prefix; fuel ensures termination.
-- Prefix closure makes rejection monotone. Each split strictly shrinks a gap > 1.
firstRejectedWithProtocolDepths : (k depth bfDepth csDepth tsDepth : ℕ) (rs : List Session) → List (Events rs) → ℕ → ℕ → ℕ → ℕ
firstRejectedWithProtocolDepths k depth bfDepth csDepth tsDepth rs es zero lo hi = hi
firstRejectedWithProtocolDepths k depth bfDepth csDepth tsDepth rs es (suc fuel) lo hi with hi ≤ᵇ suc lo
... | true = hi
... | false with checkWithProtocolDepths k depth bfDepth csDepth tsDepth rs (take ((lo + hi) / 2) es)
...   | yes _ = firstRejectedWithProtocolDepths k depth bfDepth csDepth tsDepth rs es fuel ((lo + hi) / 2) hi
...   | no _ = firstRejectedWithProtocolDepths k depth bfDepth csDepth tsDepth rs es fuel lo ((lo + hi) / 2)

-- Verify the preceding accepted prefix and report its residual component state.
-- Falling back to the sequential scan keeps diagnostics total without assumptions.
rejectionWithProtocolDepths : (k depth bfDepth csDepth tsDepth : ℕ) (rs : List Session) → List (Events rs) → ℕ → String
rejectionWithProtocolDepths k depth bfDepth csDepth tsDepth rs es i with checkWithProtocolDepths k depth bfDepth csDepth tsDepth rs (take (i ∸ 1) es) | drop (i ∸ 1) es
... | yes (st , _) | e ∷ _ = "rejected at index " ++ showℕ i ++
  " (session " ++ showℕ (index e) ++ "): " ++ showEvent e ++
  "\nmodel session state after " ++ showℕ (i ∸ 1) ++ " events: " ++ componentState st e
... | _ | _ = scanWithProtocolDepths k depth bfDepth csDepth tsDepth rs es 0 (initial rs) es

-- Decide the complete global trace before scanning rejected prefixes.
verdictWithProtocolDepths : (k depth bfDepth csDepth tsDepth : ℕ) (rs : List Session) → List (Events rs) → String
verdictWithProtocolDepths k depth bfDepth csDepth tsDepth rs es with checkWithProtocolDepths k depth bfDepth csDepth tsDepth rs es
... | yes _ = "accepted (" ++ showℕ (length es) ++ " events, " ++ showℕ (length rs) ++ " sessions)"
... | no _ = rejectionWithProtocolDepths k depth bfDepth csDepth tsDepth rs es (firstRejectedWithProtocolDepths k depth bfDepth csDepth tsDepth rs es (length es) 0 (length es))

-- Preserve the four-bound scan with TxSubmission2 requester capacity four.
scanWithAllDepths : (k depth bfDepth csDepth : ℕ) (rs : List Session) → List (Events rs) → ℕ →
  States rs → List (Events rs) → String
scanWithAllDepths k depth bfDepth csDepth = scanWithProtocolDepths k depth bfDepth csDepth 4

-- Compatibility binary search for existing callers.
firstRejectedWithAllDepths : (k depth bfDepth csDepth : ℕ) (rs : List Session) → List (Events rs) → ℕ → ℕ → ℕ → ℕ
firstRejectedWithAllDepths k depth bfDepth csDepth = firstRejectedWithProtocolDepths k depth bfDepth csDepth 4

-- Compatibility rejection diagnostics for existing callers.
rejectionWithAllDepths : (k depth bfDepth csDepth : ℕ) (rs : List Session) → List (Events rs) → ℕ → String
rejectionWithAllDepths k depth bfDepth csDepth = rejectionWithProtocolDepths k depth bfDepth csDepth 4

-- Compatibility verdict with the default TxSubmission2 bound.
verdictWithAllDepths : (k depth bfDepth csDepth : ℕ) (rs : List Session) → List (Events rs) → String
verdictWithAllDepths k depth bfDepth csDepth = verdictWithProtocolDepths k depth bfDepth csDepth 4

-- Preserve existing three-bound reporting APIs with ChainSync depth 300.
scanWithDepths : (k depth bfDepth : ℕ) (rs : List Session) → List (Events rs) → ℕ →
  States rs → List (Events rs) → String
scanWithDepths k depth bfDepth = scanWithAllDepths k depth bfDepth 300

-- Compatibility prefix search with the default ChainSync bound.
firstRejectedWithDepths : (k depth bfDepth : ℕ) (rs : List Session) → List (Events rs) → ℕ → ℕ → ℕ → ℕ
firstRejectedWithDepths k depth bfDepth = firstRejectedWithAllDepths k depth bfDepth 300

-- Compatibility rejection diagnostics.
rejectionWithDepths : (k depth bfDepth : ℕ) (rs : List Session) → List (Events rs) → ℕ → String
rejectionWithDepths k depth bfDepth = rejectionWithAllDepths k depth bfDepth 300

-- Compatibility verdict retaining the existing three bounds.
verdictWithDepths : (k depth bfDepth : ℕ) (rs : List Session) → List (Events rs) → String
verdictWithDepths k depth bfDepth = verdictWithAllDepths k depth bfDepth 300

-- Preserve the two-bound diagnostic scan API.
scan : (k depth : ℕ) (rs : List Session) → List (Events rs) → ℕ →
       States rs → List (Events rs) → String
scan k depth = scanWithDepths k depth 100

-- Preserve the two-bound prefix search API.
firstRejected : (k depth : ℕ) (rs : List Session) → List (Events rs) → ℕ → ℕ → ℕ → ℕ
firstRejected k depth = firstRejectedWithDepths k depth 100

-- Preserve the two-bound rejection report API.
rejection : (k depth : ℕ) (rs : List Session) → List (Events rs) → ℕ → String
rejection k depth = rejectionWithDepths k depth 100

-- Preserve the two-bound verdict API.
verdict : (k depth : ℕ) (rs : List Session) → List (Events rs) → String
verdict k depth = verdictWithDepths k depth 100

-- Parse and check all five protocols with independent pipeline bounds.
reportWithProtocolDepths : ℕ → ℕ → ℕ → ℕ → ℕ → String → String
reportWithProtocolDepths k depth bfDepth csDepth tsDepth s with parse s
... | inj₁ (l , txt) = "parse error at line " ++ showℕ l ++ ": " ++ txt
... | inj₂ (rs , es) = verdictWithProtocolDepths k depth bfDepth csDepth tsDepth rs es

-- Existing four-bound callers use TxSubmission2 capacity four.
reportWithAllDepths : ℕ → ℕ → ℕ → ℕ → String → String
reportWithAllDepths k depth bfDepth csDepth = reportWithProtocolDepths k depth bfDepth csDepth 4

-- Role-selected TxSubmission2 checker; the bound affects only requesters.
reportTxSubmission2 : ℕ → String → String
reportTxSubmission2 tsDepth s with parseTxSubmission2 s
... | inj₁ (l , txt) = "parse error at line " ++ showℕ l ++ ": " ++ txt
... | inj₂ (rs , es) = verdictWithProtocolDepths 4 1 100 300 tsDepth rs es

-- Existing three-bound callers retain ChainSync depth 300.
reportWithDepths : ℕ → ℕ → ℕ → String → String
reportWithDepths k depth bfDepth = reportWithAllDepths k depth bfDepth 300

-- Select the client/server ChainSync checker from the role header.
reportChainSync : ℕ → String → String
reportChainSync csDepth s with parseChainSync s
... | inj₁ (l , txt) = "parse error at line " ++ showℕ l ++ ": " ++ txt
... | inj₂ (rs , es) = verdictWithAllDepths 4 1 100 csDepth rs es

-- Existing interleaved callers retain BlockFetch's default depth of 100.
reportWithDepth : ℕ → ℕ → String → String
reportWithDepth k depth = reportWithDepths k depth 100

-- Check a standalone Notify session through the same certified product.
reportNotifyWithDepth : ℕ → String → String
reportNotifyWithDepth depth s with parseNotify s
... | inj₁ (l , txt) = "parse error at line " ++ showℕ l ++ ": " ++ txt
... | inj₂ (rs , es) = verdict 4 depth rs es

-- Select the BlockFetch client/server checker from the file's role header.
-- The bound affects clients only; the server model remains sequential.
reportBlockFetch : ℕ → String → String
reportBlockFetch bfDepth s with parseBlockFetch s
... | inj₁ (l , txt) = "parse error at line " ++ showℕ l ++ ": " ++ txt
... | inj₂ (rs , es) = verdictWithDepths 4 1 bfDepth rs es

-- Legacy interleaved calls retain depth one for Notify.
report : ℕ → String → String
report k = reportWithDepth k 1

-- Legacy standalone calls retain depth one for Notify.
reportNotify : String → String
reportNotify = reportNotifyWithDepth 1

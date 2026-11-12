{-# OPTIONS --safe #-}

-- Pure reporting for the single interleaved-session replay model.
module Cardano_network.Replay.LeiosFetchInterleavedReport where

open import Data.Maybe using (just; nothing)
open import Data.List using (List; []; _∷_; length; take; partitionSums)
open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Cardano_network.Replay.LeiosFetchParse using (Role; showEvent)
open import Cardano_network.Replay.LeiosFetchInterleaved
import Cardano_network.Replay.LeiosFetchSession as F
import Cardano_network.Replay.LeiosFetchDecide as Decide
open import Cardano_network.Replay.LeiosFetchParseInterleaved

-- Project the first session's events without changing their local order.
leftEvents : ∀ {A B : Set} → List (A Data.Sum.⊎ B) → List A
leftEvents es = proj₁ (partitionSums es)

-- Drop the first session's events while retaining every remaining tag.
rightEvents : ∀ {A B : Set} → List (A Data.Sum.⊎ B) → List B
rightEvents es = proj₂ (partitionSums es)

-- Acceptance notes use checked history, independently of the chosen drain witness.
checkedNote : ℕ → ℕ → Role → List F.E → String
checkedNote k session r es with Decide.Cert.checkedFailure k (start r) 1 es
... | nothing = ""
... | just (i , reason , _) =
  "\nnote: checked reading fails at index " ++ showℕ i ++
  " (session " ++ showℕ session ++ ", local event): " ++ reason ++
  "; accepted only as a draining client"

-- Inspect each accepted session separately so queues never cross session boundaries.
-- Advance the session index with suc while projecting events left/right.
acceptedNotes : (k session : ℕ) (rs : List Role) → List (Events (length rs)) → String
acceptedNotes k session [] es = ""
acceptedNotes k session (r ∷ rs) es =
  checkedNote k session r (leftEvents es) ++
  acceptedNotes k (suc session) rs (rightEvents es)

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
... | yes _ = "accepted (" ++ showℕ (length es) ++ " events, " ++ showℕ (length rs) ++ " sessions)" ++ acceptedNotes k 0 rs es
... | no _ = scan k rs es 0 (initial rs) es

-- Parse and check one interleaved file.
report : ℕ → String → String
report k s with parse s
... | inj₁ (l , txt) = "parse error at line " ++ showℕ l ++ ": " ++ txt
... | inj₂ (rs , es) = verdict k rs es

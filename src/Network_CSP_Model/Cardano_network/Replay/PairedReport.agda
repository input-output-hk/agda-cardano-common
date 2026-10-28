{-# OPTIONS --safe #-}

-- Paired protocol verdicts and a source-mapped witness merge for accepted inputs.
open import Data.String.Base using (String)
open import Data.Maybe.Base using (Maybe)
open import Data.Product using (_×_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Cardano_network.Replay.Common using (Role; Direction)
module Cardano_network.Replay.PairedReport
  (S M : Set) (messageEq : DecidableEquality M)
  (localNext : Role → S → Direction × M → Maybe S)
  (clientInitial serverInitial : S) (protocol scope : String)
  (parseEvent : String → Maybe (Direction × M))
  (showEvent : Direction × M → String) where

open import Data.Nat using (ℕ)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Product using (proj₂; _,_)
open import Data.String using (String; _++_)
open import Data.Sum using (inj₁; inj₂)
open import Relation.Nullary using (yes; no)
open import Cardano_network.Replay.PairedParse (Direction × M) protocol parseEvent
open import Cardano_network.Replay.Paired S M messageEq localNext
open import Cardano_network.Replay.PairedDecide S M messageEq localNext

-- The caller supplies the two fresh protocol states; channels start empty.
initial : State
initial = fresh clientInitial serverInitial

-- Render the witness by consuming each original source row exactly once.
module Render where

  -- The indexed witness makes unmatched source-map cases impossible.
  rows : ∀ {s} (cs ss : List Row) → Compatible s (map proj₂ cs) (map proj₂ ss) → String
  rows [] [] finished = ""
  rows ((n , e) ∷ cs) [] (takeClient st run) =
    "client source-line " ++ showℕ n ++ " " ++ showEvent e ++ "\n" ++ rows cs [] run
  rows [] ((n , e) ∷ ss) (takeServer st run) =
    "server source-line " ++ showℕ n ++ " " ++ showEvent e ++ "\n" ++ rows [] ss run
  rows ((n , e) ∷ cs) ((m , f) ∷ ss) (takeClient st run) =
    "client source-line " ++ showℕ n ++ " " ++ showEvent e ++ "\n" ++ rows cs ((m , f) ∷ ss) run
  rows ((n , e) ∷ cs) ((m , f) ∷ ss) (takeServer st run) =
    "server source-line " ++ showℕ m ++ " " ++ showEvent f ++ "\n" ++ rows ((n , e) ∷ cs) ss run

  -- Print acceptance with unresolved queues and the order-preserving merge.
  verdict : Input → String
  verdict i with compatible? initial (map proj₂ (clientRows i)) (map proj₂ (serverRows i))
  ... | no _ = "rejected paired trace: no order-preserving merge under the declared fresh-session capture and FIFO model"
  ... | yes run with merge-run run
  ...   | end , _ =
    "accepted paired prefix (" ++ scope ++ "; client " ++ showℕ (length (clientRows i)) ++
    " rows, server " ++ showℕ (length (serverRows i)) ++ " rows)\n" ++
    "pair " ++ connectionKey i ++ " " ++ sessionKey i ++ "\n" ++
    "client source " ++ source (clientInfo i) ++ "\nserver source " ++ source (serverInfo i) ++
    "\nin-flight client-to-server " ++ showℕ (length (clientToServer end)) ++
    "; server-to-client " ++ showℕ (length (serverToClient end)) ++ "\nwitness merge:\n" ++
    rows (clientRows i) (serverRows i) run

-- An input-evidence failure is distinct from a certified protocol-model rejection.
report : String → String
report text with parseFile text
... | inj₁ (line , reason) = "insufficient evidence or malformed paired input at line " ++ showℕ line ++ ": " ++ reason
... | inj₂ i = Render.verdict i

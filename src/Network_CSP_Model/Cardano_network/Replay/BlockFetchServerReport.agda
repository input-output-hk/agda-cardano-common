{-# OPTIONS --safe #-}

-- Standalone reporting for sequential BlockFetch server control traces.
module Cardano_network.Replay.BlockFetchServerReport where

open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; words; lines; _++_)
open import Relation.Nullary using (yes; no)
open import Cardano_network.Replay.BlockFetchServerSession
open import Cardano_network.Replay.BlockFetchReport using (parseRows; showEvent)

-- Reuse the exact kind/namespace grammar, but require the server role.
parseFile : String → (ℕ × String) ⊎ List E
parseFile s with lines s
... | [] = inj₁ (1 , "missing role server header")
... | h ∷ rest with words h
...   | "role" ∷ "server" ∷ [] = parseRows 2 rest
...   | _ = inj₁ (1 , h)

-- Explain the protocol phase before a rejected observation.
showState : St → String
showState idle = "idle (awaiting RequestRange or ClientDone)"
showState busy = "busy (must send StartBatch or NoBlocks)"
showState streaming = "streaming (must send Block or BatchDone)"
showState closed = "closed"

-- Scan deterministic successors only to locate a certified rejection.
scan : ℕ → St → List E → String
scan i s [] = "accepted (" ++ showℕ i ++ " events; BlockFetch server control only)"
scan i s (e ∷ es) with after s e
... | [] = "rejected at index " ++ showℕ (suc i) ++ ": " ++ showEvent e ++
  "\nmodel state after " ++ showℕ i ++ " events: " ++ showState s
... | t ∷ _ = scan (suc i) t es

-- Acceptance is obtained from the certified sequential-server decider.
report : String → String
report txt with parseFile txt
... | inj₁ (n , s) = "parse error at line " ++ showℕ n ++ ": " ++ s
... | inj₂ es with check es
...   | yes _ = "accepted (" ++ showℕ (length es) ++ " events; BlockFetch server control only)"
...   | no _ = scan 0 idle es

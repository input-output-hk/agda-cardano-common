{-# OPTIONS --safe #-}

-- Strict, explicitly control-only normalized BlockFetch client logs.
module Cardano_network.Replay.BlockFetchReport where

open import Data.Nat using (ℕ; suc)
open import Data.Nat.Show renaming (show to showℕ)
open import Data.List using (List; []; _∷_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.String using (String; words; lines; _++_)
open import Relation.Nullary using (yes; no)
open import Cardano_network.Replay.BlockFetchClientSession

-- Parse one of the six exact message kind names.
parseKind : String → Maybe Kind
parseKind "RequestRange" = just request
parseKind "StartBatch" = just startBatch
parseKind "NoBlocks" = just noBlocks
parseKind "Block" = just block
parseKind "BatchDone" = just batchDone
parseKind "ClientDone" = just clientDone
parseKind _ = nothing

-- Recognise directions explicitly, including invalid-agency events for checking.
parsePair : String → Kind → Maybe E
parsePair "Send" m = just (Send , m)
parsePair "Recv" m = just (Recv , m)
parsePair _ _ = nothing

-- Preserve exact BlockFetch tracer namespaces when normalizing control-only logs.
expand : List String → List String
expand ("BlockFetch.Remote.Send.RequestRange" ∷ xs) = "Send" ∷ "RequestRange" ∷ xs
expand ("BlockFetch.Remote.Send.StartBatch" ∷ xs) = "Send" ∷ "StartBatch" ∷ xs
expand ("BlockFetch.Remote.Send.NoBlocks" ∷ xs) = "Send" ∷ "NoBlocks" ∷ xs
expand ("BlockFetch.Remote.Send.Block" ∷ xs) = "Send" ∷ "Block" ∷ xs
expand ("BlockFetch.Remote.Send.BatchDone" ∷ xs) = "Send" ∷ "BatchDone" ∷ xs
expand ("BlockFetch.Remote.Send.ClientDone" ∷ xs) = "Send" ∷ "ClientDone" ∷ xs
expand ("BlockFetch.Remote.Receive.RequestRange" ∷ xs) = "Recv" ∷ "RequestRange" ∷ xs
expand ("BlockFetch.Remote.Receive.StartBatch" ∷ xs) = "Recv" ∷ "StartBatch" ∷ xs
expand ("BlockFetch.Remote.Receive.NoBlocks" ∷ xs) = "Recv" ∷ "NoBlocks" ∷ xs
expand ("BlockFetch.Remote.Receive.Block" ∷ xs) = "Recv" ∷ "Block" ∷ xs
expand ("BlockFetch.Remote.Receive.BatchDone" ∷ xs) = "Recv" ∷ "BatchDone" ∷ xs
expand ("BlockFetch.Remote.Receive.ClientDone" ∷ xs) = "Recv" ∷ "ClientDone" ∷ xs
expand xs = xs

-- Kind-only input deliberately rejects extra, supposedly validated payloads.
parseEvent : String → Maybe E
parseEvent s with expand (words s)
... | d ∷ m ∷ [] with parseKind m
...   | just k = parsePair d k
...   | nothing = nothing
parseEvent s | _ = nothing

-- Display canonical normalized event syntax.
showKind : Kind → String
showKind request = "RequestRange"
showKind startBatch = "StartBatch"
showKind noBlocks = "NoBlocks"
showKind block = "Block"
showKind batchDone = "BatchDone"
showKind clientDone = "ClientDone"

-- Direction in the logging client's viewpoint.
showDir : Direction → String
showDir Send = "Send"
showDir Recv = "Recv"

-- Canonical event for rejection diagnostics.
showEvent : E → String
showEvent (d , m) = showDir d ++ " " ++ showKind m

-- State diagnostics expose the response count and head phase.
showState : St → String
showState (openS n waiting) = "outstanding " ++ showℕ n ++ ", waiting for batch"
showState (openS n streaming) = "outstanding " ++ showℕ n ++ ", streaming"
showState closed = "closed"

-- Parse every row and preserve its one-based source line number on failure.
parseRows : ℕ → List String → (ℕ × String) ⊎ List E
parseRows n [] = inj₂ []
parseRows n (s ∷ ss) with parseEvent s
... | nothing = inj₁ (n , s)
... | just e with parseRows (suc n) ss
...   | inj₁ err = inj₁ err
...   | inj₂ es = inj₂ (e ∷ es)

-- This entry point only checks the pipelined client, not a reversed server log.
parseFile : String → (ℕ × String) ⊎ List E
parseFile s with lines s
... | [] = inj₁ (1 , "missing role client header")
... | h ∷ rest with words h
...   | "role" ∷ "client" ∷ [] = parseRows 2 rest
...   | _ = inj₁ (1 , h)

-- Find the first failed transition after a certified negative verdict.
scan : ℕ → ℕ → St → List E → String
scan k i s [] = "accepted (" ++ showℕ i ++ " events; BlockFetch client control only)"
scan k i s (e ∷ es) with after k s e
... | [] = "rejected at index " ++ showℕ (suc i) ++ ": " ++ showEvent e ++
  "\nmodel state after " ++ showℕ i ++ " events: " ++ showState s
... | t ∷ _ = scan k (suc i) t es

-- Acceptance comes from the certified decision procedure, not the diagnostic scan.
report : ℕ → String → String
report k txt with parseFile txt
... | inj₁ (n , s) = "parse error at line " ++ showℕ n ++ ": " ++ s
... | inj₂ es with Spec.check k es
...   | yes _ = "accepted (" ++ showℕ (length es) ++ " events; BlockFetch client control only)"
...   | no _ = scan k 0 initial es

{-# OPTIONS --guardedness #-}

-- InformationChannel.hs:35-54 at network 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d.
-- Pure FIFO transaction results. Callers commit a returned queue atomically;
-- nothing denotes retry, with no partial queue exposed as a successor.
module ConnectionManagement.Rules.InformationChannel where

open import Data.Nat using (ℕ; suc; _≤?_)
open import Data.List using (List; []; _∷_; _++_; length)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)

capacity : ℕ
capacity = 100

writeMessage : ∀ {Message : Set} → Message → List Message → Maybe (List Message)
writeMessage message queue with suc (length queue) ≤? capacity
... | no _ = nothing
... | yes _ = just (queue ++ (message ∷ []))

readMessage : ∀ {Message : Set} → List Message → Maybe (Message × List Message)
readMessage [] = nothing
readMessage (message ∷ queue) = just (message , queue)

-- flushTBQueue succeeds on an empty queue too; waiting for a nonempty batch is
-- a separate guard in the IG loop, not part of InformationChannel.readMessages.
readMessages : ∀ {Message : Set} → List Message → List Message × List Message
readMessages queue = queue , []

-- Multiple writeMessage calls inside ONE source STM transaction. This helper
-- models queue effects only; associated responder-counter writes must commit in
-- that same future tracer rule. It must not be scheduled as individual writes.
writeBurst : ∀ {Message : Set} → List Message → List Message → Maybe (List Message)
writeBurst [] queue = just queue
writeBurst (message ∷ messages) queue with writeMessage message queue
... | nothing = nothing
... | just proposed = writeBurst messages proposed

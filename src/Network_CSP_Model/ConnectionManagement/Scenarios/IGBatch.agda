{-# OPTIONS --guardedness #-}

-- Tests of source-derived queue/batch boundaries. Test events stand for already
-- computed payloads; these are not integrated IG or whole-source traces.
module ConnectionManagement.Scenarios.IGBatch where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; replicate)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Rules.InformationChannel
open import ConnectionManagement.Rules.IGBatch

data Event : Set where
  newConnection terminated demoted waitIdle matured commit timeout : Event

queue : List Event
queue = newConnection ∷ terminated ∷ []

fifo-read : readMessage queue ≡ just (newConnection , terminated ∷ [])
fifo-read = refl

flush-empty-succeeds : readMessages {Event} [] ≡ ([] , [])
flush-empty-succeeds = refl

flush-preserves-order : readMessages queue ≡ (queue , [])
flush-preserves-order = refl

full-retries : writeMessage newConnection (replicate 100 terminated) ≡ nothing
full-retries = refl

-- A clean last-hot-responder completion can enqueue three events atomically.
burst : List Event
burst = terminated ∷ demoted ∷ waitIdle ∷ []

burst-fits : writeBurst burst (replicate 97 newConnection) ≡ just (replicate 97 newConnection ++ burst)
burst-fits = refl

burst-retries-as-a-whole : writeBurst burst (replicate 98 newConnection) ≡ nothing
burst-retries-as-a-whole = refl

-- Splitting that source transaction would expose this prefix, even though the
-- full transaction cannot commit. This is a negative control for a model shortcut.
split-prefix-would-fit : writeBurst (terminated ∷ demoted ∷ []) (replicate 98 newConnection) ≡
  just (replicate 98 newConnection ++ (terminated ∷ demoted ∷ []))
split-prefix-would-fit = refl

maturity-wins : selectBatch (just matured) (just commit) true timeout queue ≡
  just (selected maturity (matured ∷ queue) [])
maturity-wins = refl

commit-before-queue : selectBatch nothing (just commit) true timeout queue ≡
  just (selected peerCommit (commit ∷ queue) [])
commit-before-queue = refl

queue-before-timeout : selectBatch nothing nothing true timeout queue ≡
  just (selected queued queue [])
queue-before-timeout = refl

timeout-only-when-others-retry : selectBatch nothing nothing true timeout [] ≡
  just (selected inactivity (timeout ∷ []) [])
timeout-only-when-others-retry = refl

all-retry : selectBatch nothing nothing false timeout [] ≡ nothing
all-retry = refl

-- Once the batch transaction has drained the queue, producers may enqueue while
-- the IG still processes the retained batch; the two lists have separate lives.
write-after-flush : writeBurst burst (Selection.remaining (selected queued queue [])) ≡ just burst
write-after-flush = refl

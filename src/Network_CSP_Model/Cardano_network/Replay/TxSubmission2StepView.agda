{-# OPTIONS --safe #-}

-- Inductive inversion of the unchanged TxSubmission2 replay function.
module Cardano_network.Replay.TxSubmission2StepView where

open import Data.Nat using (ℕ; _<_; _<ᵇ_)
open import Data.Nat.Properties using (<ᵇ⇒<; <⇒<ᵇ)
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.Product using (_,_)
open import Data.Maybe using (just)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.TxSubmission2Session

-- Propositional capacity implies successful functional admission.
issue-ok : ∀ {k q r} → length q < k → issue k q r ≡ just (pending (q ∷ʳ r))
issue-ok {k} {q} lt with length q <ᵇ k | <⇒<ᵇ lt
... | true | _ = refl
... | false | ()

-- All and only requester transitions, including the FIFO response family.
data View (k : ℕ) : St → E → St → Set where
  start : View k awaitingInit (Recv , init) (pending [])
  block : View k (pending []) (Send , requestBlocking) blocking
  askIds : ∀ {q} → length q < k → View k (pending q) (Send , requestNonBlocking) (pending (q ∷ʳ ids))
  askTxs : ∀ {q} → length q < k → View k (pending q) (Send , requestTxs) (pending (q ∷ʳ txs))
  emptyIds : ∀ {q} → View k (pending (ids ∷ q)) (Recv , replyIdsEmpty) (pending q)
  nonemptyIds : ∀ {q} → View k (pending (ids ∷ q)) (Recv , replyIdsNonEmpty) (pending q)
  transactions : ∀ {q} → View k (pending (txs ∷ q)) (Recv , replyTxs) (pending q)
  unblock : View k blocking (Recv , replyIdsNonEmpty) (pending [])
  close : View k blocking (Recv , doneK) closed

-- Expose the original capacity test when inverting an asynchronous request.
ids-view : ∀ {k q t} → issue k q ids ≡ just t → View k (pending q) (Send , requestNonBlocking) t
ids-view {k} {q} eq with length q <ᵇ k | <ᵇ⇒< (length q) k
... | true | lt with refl ← eq = askIds (lt tt)
... | false | _ with () ← eq

-- The corresponding inversion for a transaction-body request.
txs-view : ∀ {k q t} → issue k q txs ≡ just t → View k (pending q) (Send , requestTxs) t
txs-view {k} {q} eq with length q <ᵇ k | <ᵇ⇒< (length q) k
... | true | lt with refl ← eq = askTxs (lt tt)
... | false | _ with () ← eq

-- Exhaustively invert successful updates of the existing checker.
view : ∀ {k s e t} → nextServer k s e ≡ just t → View k s e t
view {s = awaitingInit} {Send , init} ()
view {s = awaitingInit} {Send , requestBlocking} ()
view {s = awaitingInit} {Send , requestNonBlocking} ()
view {s = awaitingInit} {Send , replyIdsEmpty} ()
view {s = awaitingInit} {Send , replyIdsNonEmpty} ()
view {s = awaitingInit} {Send , requestTxs} ()
view {s = awaitingInit} {Send , replyTxs} ()
view {s = awaitingInit} {Send , doneK} ()
view {s = awaitingInit} {Recv , init} refl = start
view {s = awaitingInit} {Recv , requestBlocking} ()
view {s = awaitingInit} {Recv , requestNonBlocking} ()
view {s = awaitingInit} {Recv , replyIdsEmpty} ()
view {s = awaitingInit} {Recv , replyIdsNonEmpty} ()
view {s = awaitingInit} {Recv , requestTxs} ()
view {s = awaitingInit} {Recv , replyTxs} ()
view {s = awaitingInit} {Recv , doneK} ()
view {s = blocking} {Send , init} ()
view {s = blocking} {Send , requestBlocking} ()
view {s = blocking} {Send , requestNonBlocking} ()
view {s = blocking} {Send , replyIdsEmpty} ()
view {s = blocking} {Send , replyIdsNonEmpty} ()
view {s = blocking} {Send , requestTxs} ()
view {s = blocking} {Send , replyTxs} ()
view {s = blocking} {Send , doneK} ()
view {s = blocking} {Recv , init} ()
view {s = blocking} {Recv , requestBlocking} ()
view {s = blocking} {Recv , requestNonBlocking} ()
view {s = blocking} {Recv , replyIdsEmpty} ()
view {s = blocking} {Recv , replyIdsNonEmpty} refl = unblock
view {s = blocking} {Recv , requestTxs} ()
view {s = blocking} {Recv , replyTxs} ()
view {s = blocking} {Recv , doneK} refl = close
view {s = pending []} {Send , init} ()
view {s = pending []} {Send , requestBlocking} refl = block
view {s = pending []} {Send , requestNonBlocking} eq = ids-view eq
view {s = pending []} {Send , replyIdsEmpty} ()
view {s = pending []} {Send , replyIdsNonEmpty} ()
view {s = pending []} {Send , requestTxs} eq = txs-view eq
view {s = pending []} {Send , replyTxs} ()
view {s = pending []} {Send , doneK} ()
view {s = pending []} {Recv , init} ()
view {s = pending []} {Recv , requestBlocking} ()
view {s = pending []} {Recv , requestNonBlocking} ()
view {s = pending []} {Recv , replyIdsEmpty} ()
view {s = pending []} {Recv , replyIdsNonEmpty} ()
view {s = pending []} {Recv , requestTxs} ()
view {s = pending []} {Recv , replyTxs} ()
view {s = pending []} {Recv , doneK} ()
view {s = pending (ids ∷ q)} {Send , init} ()
view {s = pending (ids ∷ q)} {Send , requestBlocking} ()
view {s = pending (ids ∷ q)} {Send , requestNonBlocking} eq = ids-view eq
view {s = pending (ids ∷ q)} {Send , replyIdsEmpty} ()
view {s = pending (ids ∷ q)} {Send , replyIdsNonEmpty} ()
view {s = pending (ids ∷ q)} {Send , requestTxs} eq = txs-view eq
view {s = pending (ids ∷ q)} {Send , replyTxs} ()
view {s = pending (ids ∷ q)} {Send , doneK} ()
view {s = pending (ids ∷ q)} {Recv , init} ()
view {s = pending (ids ∷ q)} {Recv , requestBlocking} ()
view {s = pending (ids ∷ q)} {Recv , requestNonBlocking} ()
view {s = pending (ids ∷ q)} {Recv , replyIdsEmpty} refl = emptyIds
view {s = pending (ids ∷ q)} {Recv , replyIdsNonEmpty} refl = nonemptyIds
view {s = pending (ids ∷ q)} {Recv , requestTxs} ()
view {s = pending (ids ∷ q)} {Recv , replyTxs} ()
view {s = pending (ids ∷ q)} {Recv , doneK} ()
view {s = pending (txs ∷ q)} {Send , init} ()
view {s = pending (txs ∷ q)} {Send , requestBlocking} ()
view {s = pending (txs ∷ q)} {Send , requestNonBlocking} eq = ids-view eq
view {s = pending (txs ∷ q)} {Send , replyIdsEmpty} ()
view {s = pending (txs ∷ q)} {Send , replyIdsNonEmpty} ()
view {s = pending (txs ∷ q)} {Send , requestTxs} eq = txs-view eq
view {s = pending (txs ∷ q)} {Send , replyTxs} ()
view {s = pending (txs ∷ q)} {Send , doneK} ()
view {s = pending (txs ∷ q)} {Recv , init} ()
view {s = pending (txs ∷ q)} {Recv , requestBlocking} ()
view {s = pending (txs ∷ q)} {Recv , requestNonBlocking} ()
view {s = pending (txs ∷ q)} {Recv , replyIdsEmpty} ()
view {s = pending (txs ∷ q)} {Recv , replyIdsNonEmpty} ()
view {s = pending (txs ∷ q)} {Recv , requestTxs} ()
view {s = pending (txs ∷ q)} {Recv , replyTxs} refl = transactions
view {s = pending (txs ∷ q)} {Recv , doneK} ()
view {s = closed} {Send , init} ()
view {s = closed} {Send , requestBlocking} ()
view {s = closed} {Send , requestNonBlocking} ()
view {s = closed} {Send , replyIdsEmpty} ()
view {s = closed} {Send , replyIdsNonEmpty} ()
view {s = closed} {Send , requestTxs} ()
view {s = closed} {Send , replyTxs} ()
view {s = closed} {Send , doneK} ()
view {s = closed} {Recv , init} ()
view {s = closed} {Recv , requestBlocking} ()
view {s = closed} {Recv , requestNonBlocking} ()
view {s = closed} {Recv , replyIdsEmpty} ()
view {s = closed} {Recv , replyIdsNonEmpty} ()
view {s = closed} {Recv , requestTxs} ()
view {s = closed} {Recv , replyTxs} ()
view {s = closed} {Recv , doneK} ()

{-# OPTIONS --safe #-}

-- An inductive view of the existing functional replay transitions.
module Cardano_network.Replay.ChainSyncStepView where

open import Data.Nat using (ℕ; zero; suc; _<_; _<ᵇ_)
open import Data.Nat.Properties using (<ᵇ⇒<; <⇒<ᵇ)
open import Data.Bool using (true; false)
open import Data.Product using (_,_)
open import Data.Maybe using (just)
open import Data.Unit using (tt)
open import Data.Empty using (⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Replay.ChainSyncSession

-- Successful bounded admission is equivalent to the propositional guard.
issue-ok : ∀ {k n ph} → n < k → issue k n ph ≡ just (pending (suc n) ph)
issue-ok {k} {n} lt with n <ᵇ k | <⇒<ᵇ lt
... | true | _ = refl
... | false | ()

-- All and only the client transitions of nextClient.
data View (k : ℕ) : St → E → St → Set where
  request : ∀ {n ph} → n < k → View k (pending n ph) (Send , requestNext) (pending (suc n) ph)
  find : View k initial (Send , findIntersect) intersect
  close : View k initial (Send , doneK) closed
  await : ∀ {n} → View k (pending (suc n) canAwait) (Recv , awaitReply) (pending (suc n) mustReply)
  forward : ∀ {n ph} → View k (pending (suc n) ph) (Recv , rollForward) (pending n canAwait)
  backward : ∀ {n ph} → View k (pending (suc n) ph) (Recv , rollBackward) (pending n canAwait)
  found : View k intersect (Recv , intersectFound) initial
  notFound : View k intersect (Recv , intersectNotFound) initial

-- Each view constructor is a transition of the unchanged replay model.
valid : ∀ {k s e t} → View k s e t → nextClient k s e ≡ just t
valid (request lt) = issue-ok lt
valid find = refl
valid close = refl
valid await = refl
valid (forward {ph = canAwait}) = refl
valid (forward {ph = mustReply}) = refl
valid (backward {ph = canAwait}) = refl
valid (backward {ph = mustReply}) = refl
valid found = refl
valid notFound = refl

-- Successful admission exposes its original guard and exact successor.
issue-view : ∀ {k n ph t} → issue k n ph ≡ just t → View k (pending n ph) (Send , requestNext) t
issue-view {k} {n} eq with n <ᵇ k | <ᵇ⇒< n k
... | true | lt with refl ← eq = request (lt tt)
... | false | _ with () ← eq

-- Exhaustively invert the existing function; no alternate checker is used.
view : ∀ {k s e t} → nextClient k s e ≡ just t → View k s e t
view {s = pending n ph} {Send , requestNext} eq = issue-view eq
view {s = pending zero canAwait} {Send , awaitReply} ()
view {s = pending zero canAwait} {Send , rollForward} ()
view {s = pending zero canAwait} {Send , rollBackward} ()
view {s = pending zero canAwait} {Send , findIntersect} refl = find
view {s = pending zero canAwait} {Send , intersectFound} ()
view {s = pending zero canAwait} {Send , intersectNotFound} ()
view {s = pending zero canAwait} {Send , doneK} refl = close
view {s = pending zero canAwait} {Recv , requestNext} ()
view {s = pending zero canAwait} {Recv , awaitReply} ()
view {s = pending zero canAwait} {Recv , rollForward} ()
view {s = pending zero canAwait} {Recv , rollBackward} ()
view {s = pending zero canAwait} {Recv , findIntersect} ()
view {s = pending zero canAwait} {Recv , intersectFound} ()
view {s = pending zero canAwait} {Recv , intersectNotFound} ()
view {s = pending zero canAwait} {Recv , doneK} ()
view {s = pending zero mustReply} {Send , awaitReply} ()
view {s = pending zero mustReply} {Send , rollForward} ()
view {s = pending zero mustReply} {Send , rollBackward} ()
view {s = pending zero mustReply} {Send , findIntersect} ()
view {s = pending zero mustReply} {Send , intersectFound} ()
view {s = pending zero mustReply} {Send , intersectNotFound} ()
view {s = pending zero mustReply} {Send , doneK} ()
view {s = pending zero mustReply} {Recv , requestNext} ()
view {s = pending zero mustReply} {Recv , awaitReply} ()
view {s = pending zero mustReply} {Recv , rollForward} ()
view {s = pending zero mustReply} {Recv , rollBackward} ()
view {s = pending zero mustReply} {Recv , findIntersect} ()
view {s = pending zero mustReply} {Recv , intersectFound} ()
view {s = pending zero mustReply} {Recv , intersectNotFound} ()
view {s = pending zero mustReply} {Recv , doneK} ()
view {s = pending (suc n) canAwait} {Send , awaitReply} ()
view {s = pending (suc n) canAwait} {Send , rollForward} ()
view {s = pending (suc n) canAwait} {Send , rollBackward} ()
view {s = pending (suc n) canAwait} {Send , findIntersect} ()
view {s = pending (suc n) canAwait} {Send , intersectFound} ()
view {s = pending (suc n) canAwait} {Send , intersectNotFound} ()
view {s = pending (suc n) canAwait} {Send , doneK} ()
view {s = pending (suc n) canAwait} {Recv , requestNext} ()
view {s = pending (suc n) canAwait} {Recv , awaitReply} refl = await
view {s = pending (suc n) canAwait} {Recv , rollForward} refl = forward
view {s = pending (suc n) canAwait} {Recv , rollBackward} refl = backward
view {s = pending (suc n) canAwait} {Recv , findIntersect} ()
view {s = pending (suc n) canAwait} {Recv , intersectFound} ()
view {s = pending (suc n) canAwait} {Recv , intersectNotFound} ()
view {s = pending (suc n) canAwait} {Recv , doneK} ()
view {s = pending (suc n) mustReply} {Send , awaitReply} ()
view {s = pending (suc n) mustReply} {Send , rollForward} ()
view {s = pending (suc n) mustReply} {Send , rollBackward} ()
view {s = pending (suc n) mustReply} {Send , findIntersect} ()
view {s = pending (suc n) mustReply} {Send , intersectFound} ()
view {s = pending (suc n) mustReply} {Send , intersectNotFound} ()
view {s = pending (suc n) mustReply} {Send , doneK} ()
view {s = pending (suc n) mustReply} {Recv , requestNext} ()
view {s = pending (suc n) mustReply} {Recv , awaitReply} ()
view {s = pending (suc n) mustReply} {Recv , rollForward} refl = forward
view {s = pending (suc n) mustReply} {Recv , rollBackward} refl = backward
view {s = pending (suc n) mustReply} {Recv , findIntersect} ()
view {s = pending (suc n) mustReply} {Recv , intersectFound} ()
view {s = pending (suc n) mustReply} {Recv , intersectNotFound} ()
view {s = pending (suc n) mustReply} {Recv , doneK} ()
view {s = intersect} {Send , requestNext} ()
view {s = intersect} {Send , awaitReply} ()
view {s = intersect} {Send , rollForward} ()
view {s = intersect} {Send , rollBackward} ()
view {s = intersect} {Send , findIntersect} ()
view {s = intersect} {Send , intersectFound} ()
view {s = intersect} {Send , intersectNotFound} ()
view {s = intersect} {Send , doneK} ()
view {s = intersect} {Recv , requestNext} ()
view {s = intersect} {Recv , awaitReply} ()
view {s = intersect} {Recv , rollForward} ()
view {s = intersect} {Recv , rollBackward} ()
view {s = intersect} {Recv , findIntersect} ()
view {s = intersect} {Recv , intersectFound} refl = found
view {s = intersect} {Recv , intersectNotFound} refl = notFound
view {s = intersect} {Recv , doneK} ()
view {s = closed} {Send , requestNext} ()
view {s = closed} {Send , awaitReply} ()
view {s = closed} {Send , rollForward} ()
view {s = closed} {Send , rollBackward} ()
view {s = closed} {Send , findIntersect} ()
view {s = closed} {Send , intersectFound} ()
view {s = closed} {Send , intersectNotFound} ()
view {s = closed} {Send , doneK} ()
view {s = closed} {Recv , requestNext} ()
view {s = closed} {Recv , awaitReply} ()
view {s = closed} {Recv , rollForward} ()
view {s = closed} {Recv , rollBackward} ()
view {s = closed} {Recv , findIntersect} ()
view {s = closed} {Recv , intersectFound} ()
view {s = closed} {Recv , intersectNotFound} ()
view {s = closed} {Recv , doneK} ()

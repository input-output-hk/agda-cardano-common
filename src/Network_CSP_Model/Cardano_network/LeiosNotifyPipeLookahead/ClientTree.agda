{-# OPTIONS --guardedness #-}

-- Productive source-operation PTree for the unchanged generic pipelined client.
-- Its actions retain callback decisions; native LNPEv lifting is a separate boundary.
open import Relation.Binary.Definitions using (DecidableEquality)
module Cardano_network.LeiosNotifyPipeLookahead.ClientTree
  (Notification Return : Set) (notificationEq : DecidableEquality Notification) where

open import Data.Nat using (ℕ)
open import Data.Bool using (true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return
import Cardano_network.LeiosNotifyPipeLookahead.ClientExecution Notification Return notificationEq as Exec
open import Cardano_network.LeiosNotifyPipeLookahead.Selection using (select; select-complete)
import Cardano_network.LeiosNotifyPipeLookahead.OperationalTree

-- Only the closed client can return its checkDone result; active states keep running.
outcome : State → Maybe Return
outcome s with active (main s)
... | true = nothing
... | false = returnValue s

-- An active main thread cannot have a returned outcome.
active-live : ∀ {s} → active (main s) ≡ true → outcome s ≡ nothing
active-live {s} pr rewrite pr = refl

-- All independent visible rules originate in non-returned client states.
step-live : ∀ {s a t} → Step s a t → outcome s ≡ nothing
step-live continueZero = refl
step-live (continueBelow _) = refl
step-live (continueFull _ _) = refl
step-live stopRequested = refl
step-live sentRequest = refl
step-live sentQuitIdle = refl
step-live sentQuitBusy = refl
step-live (receivedReply pr) = active-live pr
step-live (delivered pr) = active-live pr
step-live receivedDone = refl

-- All independent hidden rules likewise originate in non-returned client states.
tau-live : ∀ {s t} → Tau s t → outcome s ≡ nothing
tau-live registerResponse = refl
tau-live setStopIdle = refl
tau-live setStopBusy = refl
tau-live registerMarker = refl
tau-live optionalEmpty = refl
tau-live optionalResult = refl
tau-live blockingResult = refl
tau-live adjustArrival = refl
tau-live drainResult = refl
tau-live drained = refl
tau-live (startResponse pr) = active-live pr
tau-live (startMarker pr) = active-live pr
tau-live (keepReply pr) = active-live pr
tau-live (discardReply pr) = active-live pr
tau-live (countArrival pr) = active-live pr
tau-live (publishResponse pr) = active-live pr
tau-live (publishMarker pr) = active-live pr

-- The tree uses executable choices certified against independent Step/Tau rules.
module Native = Cardano_network.LeiosNotifyPipeLookahead.OperationalTree
  State Action ℕ Return Step Tau (λ s a → Exec.lookup a s)
  (λ s n → select (Exec.internalMoves s) n)
  Exec.next-complete (λ pr → select-complete (Exec.target-complete pr))
  outcome step-live tau-live

-- Fresh client entry point before the first checkDone transaction.
clientTree : Native.Proc
clientTree = Native.tree initial

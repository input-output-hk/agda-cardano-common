{-# OPTIONS --safe #-}

-- Fresh production-policy full-pipe prefixes; the server may remain unscheduled.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ResourceFixtures (Notification : Set) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ; zero; suc; _≤_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-refl; ≤-pred; m≤n⇒m≤1+n; <-irrefl)
open import Data.Integer using (+_; +<+)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ-syntax; _,_; _×_)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary.Decidable using (Dec; does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Data.Integer.Properties as Int
open import Data.Integer.Properties using () renaming (_<?_ to compareInteger)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as N
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeQueueBounds Notification as Queue
import Cardano_network.LeiosNotifyPipeLookahead.ResourceBounds Notification as Resources

-- Queue construction matches the driver's append operations without reordering jobs.
copies : ∀ {A : Set} → A → ℕ → List A
copies x zero = []
copies x (suc n) = copies x n ∷ʳ x

-- Each request is physically queued while the unscheduled server retains its initial state.
filled : ℕ → N.State
filled n = N.nodeDriver
  (D.pair (C.client C.poll C.idle (copies C.responseJob n) [] n (+ 0) false nothing)
    S.initial (copies D.request n) [] nothing nothing nothing nothing)
  Q.initial true true false

-- A proof-bearing comparison has exactly its stated Boolean result.
comparison-true : ∀ {A : Set} (d : Dec A) → A → does d ≡ true
comparison-true (yes _) pr = refl
comparison-true (no deny) pr = ⊥-elim (deny pr)

-- Positive below-depth control first attempts the optional collect, then may issue.
one-more : (n : ℕ) → suc n ≤ 1000 →
  N.Run (filled n) (N.wire (D.clientSend D.request) ∷ []) (filled (suc n))
one-more zero bound =
  N.internal (N.continueReady (Client.continueAtDepth C.continueZero))
  (N.internal (N.clientSchedule (Client.schedule C.registerResponse))
  (N.internal (N.transport (D.commitClient C.sentRequest) refl)
  (N.visible (N.clientRecord N.sent (D.clientSent C.sentRequest)) N.stop)))
one-more (suc n) bound =
  N.internal (N.continueReady (Client.continueAtDepth (C.continueBelow
    (comparison-true (compareInteger (+ (suc n)) (+ 1000)) (+<+ bound)))))
  (N.internal (N.clientSchedule (Client.schedule C.optionalEmpty))
  (N.internal (N.clientSchedule (Client.schedule C.registerResponse))
  (N.internal (N.transport (D.commitClient C.sentRequest) refl)
  (N.visible (N.clientRecord N.sent (D.clientSent C.sentRequest)) N.stop))))

-- Any occupancy up to the production depth is freshly reachable without server progress.
fill : (n : ℕ) → n ≤ 1000 → Σ[ actions ∈ List N.Action ] N.Run N.initial actions (filled n)
fill zero bound = N.setForecast true ∷ [] , N.visible N.forecastInput N.stop
fill (suc n) bound with fill n (m≤n⇒m≤1+n (≤-pred bound))
... | actions , prefix = actions ++ (N.wire (D.clientSend D.request) ∷ []) ,
  Queue.append prefix (one-more n bound)

abstract
  -- Keep the large inductive prefix opaque when a later proof opens its dependent pair.
  full-prefix : Σ[ actions ∈ List N.Action ] N.Run N.initial actions (filled 1000)
  full-prefix = fill 1000 ≤-refl

-- The full-pipe Quit marker adds one receiver and one FIFO command to the fresh state.
quitFilled : ℕ → N.State
quitFilled n = N.nodeDriver
  (D.pair (C.client C.draining C.idle (copies C.responseJob n ∷ʳ C.quitMarker) [] (suc n)
    (+ 0) true (just tt)) S.initial (copies D.request n ∷ʳ D.quit) []
    nothing nothing nothing nothing) Q.initial true true true

-- Sending Quit does not wait for any of the thousand request replies.
quit-full : (n : ℕ) → N.Run (filled (suc n))
  (N.setTerminate true ∷ N.wire (D.clientSend D.quit) ∷ []) (quitFilled (suc n))
quit-full n = N.visible N.terminateInput
  (N.internal (N.terminateReady (Client.terminate C.stopRequested))
  (N.internal (N.clientSchedule (Client.schedule C.setStopBusy))
  (N.internal (N.clientSchedule (Client.schedule C.registerMarker))
  (N.internal (N.transport (D.commitClient C.sentQuitBusy) refl)
  (N.visible (N.clientRecord N.sent (D.clientSent C.sentQuitBusy)) N.stop)))))

-- Retain an actual fresh history rather than an arbitrary hand-constructed oversized state.
fresh-quit : Σ[ actions ∈ List N.Action ] N.Run N.initial actions (quitFilled 1000)
fresh-quit with full-prefix
... | actions , prefix = actions ++ (N.setTerminate true ∷ N.wire (D.clientSend D.quit) ∷ []) ,
  Queue.append prefix (quit-full 999)

-- The claimed depth-only inFlight bound is false during this legitimate marker drain.
marker-refutes-depth : C.inFlight (D.clientState (N.driverState (quitFilled 1000))) ≤ 1000 → ⊥
marker-refutes-depth impossible = <-irrefl refl impossible

-- Conservative live-resource bounds remain valid at the same counterexample endpoint.
marker-bounds : Resources.Bounds (N.driverState (quitFilled 1000))
marker-bounds with fresh-quit
... | actions , prefix = Resources.initial-bounds prefix

-- Credit/notification inventory is also bounded throughout that fresh policy execution.
marker-queue : Queue.Budget (quitFilled 1000)
marker-queue with fresh-quit
... | actions , prefix = Queue.initial-budget prefix

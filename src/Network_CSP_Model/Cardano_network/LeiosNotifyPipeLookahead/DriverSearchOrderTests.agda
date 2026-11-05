{-# OPTIONS --safe #-}

-- Concrete ordering gates retain all hidden alternatives while favoring shutdown and exact payloads.
module Cardano_network.LeiosNotifyPipeLookahead.DriverSearchOrderTests where

open import Data.Bool using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.Integer using (+_)
open import Data.List using ([]; _∷_; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as R
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Bool ⊤ (false ∷ true ∷ []) as B
import Cardano_network.LeiosNotifyPipeLookahead.DriverSearchOrder Bool Bool._≟_ (false ∷ true ∷ []) as Order

-- The generic helper keeps all occurrences, including equal-priority duplicate values.
stable-duplicates : Order.sort (λ n → n) (2 ∷ 1 ∷ 2 ∷ 0 ∷ []) ≡ (0 ∷ 1 ∷ 2 ∷ 2 ∷ [])
stable-duplicates = refl

-- A tagged payload makes the equal-score stability requirement directly observable.
stable-tags : Order.sort (λ (pair : ℕ × Bool) → Data.Product.proj₁ pair)
  ((1 , false) ∷ (0 , true) ∷ (1 , true) ∷ []) ≡ ((0 , true) ∷ (1 , false) ∷ (1 , true) ∷ [])
stable-tags = refl

-- The requested shutdown branch stores the actual successful unit callback value.
stopInitial : D.State
stopInitial = D.pair
  (C.client C.stopPending C.idle [] [] 0 (+ 0) false (just tt))
  S.initial [] [] nothing nothing nothing nothing

-- Initial Quit chooses termination before the otherwise earlier speculative continue callback.
quit-first : Order.orderedTargets S.nodeNext D.initial (R.sendCommand D.quit ∷ []) [] ≡
  (stopInitial ∷ D.pair (C.client C.issue C.idle [] [] 0 (+ 0) false nothing)
    S.initial [] [] nothing nothing nothing nothing ∷ [])
quit-first = refl

-- The demoted continuation remains present with its independent source certificate.
continue-retained : D.pair (C.client C.issue C.idle [] [] 0 (+ 0) false nothing)
  S.initial [] [] nothing nothing nothing nothing ∈
  Order.orderedTargets S.nodeNext D.initial (R.sendCommand D.quit ∷ []) []
continue-retained = Order.target-complete {p = S.nodeNext} {s = D.initial} {client = R.sendCommand D.quit ∷ []} {server = []} (B.clientCallback (D.continue {k = + 0}) C.continueZero)

-- Changing only the requested command reverses callback preference without changing source semantics.
request-first : Order.orderedTargets S.nodeNext D.initial (R.sendCommand D.request ∷ []) [] ≡
  (D.pair (C.client C.issue C.idle [] [] 0 (+ 0) false nothing)
    S.initial [] [] nothing nothing nothing nothing ∷ stopInitial ∷ [])
request-first = refl

-- Readiness starts with no pending normal value and a registered receiver awaiting the result.
claimed : D.State
claimed = D.pair
  (C.client C.writingRequest C.awaiting [] [] 0 (+ 0) false nothing)
  (S.state S.awaitNext 0 S.claimed 0 false)
  [] [] (just D.request) nothing nothing nothing

-- Choosing the expected exact normal value beats the fallback basis value and generic Canceled.
exact-payload-first : Order.orderedTargets S.genericNext claimed
  (R.receiveResponse (D.reply (S.normal true)) ∷ [])
  (R.sendResponse (D.reply (S.normal true)) ∷ []) ≡
  (D.pair (D.clientState claimed) (S.state S.awaitNext 0 (S.selected (S.normal true)) 0 false)
    [] [] (just D.request) nothing nothing nothing ∷
   D.pair (D.clientState claimed) (S.state S.awaitNext 0 (S.selected (S.normal false)) 0 false)
    [] [] (just D.request) nothing nothing nothing ∷
   D.pair (D.clientState claimed) (S.state S.awaitNext 0 (S.selected S.canceled) 0 false)
    [] [] (just D.request) nothing nothing nothing ∷ [])
exact-payload-first = refl

-- A different exact next payload selects the corresponding different callback preference.
changed-payload-first : Order.orderedTargets S.nodeNext claimed
  (R.receiveResponse (D.reply (S.normal false)) ∷ [])
  (R.sendResponse (D.reply (S.normal false)) ∷ []) ≡
  (D.pair (D.clientState claimed) (S.state S.awaitNext 0 (S.selected (S.normal false)) 0 false)
    [] [] (just D.request) nothing nothing nothing ∷
   D.pair (D.clientState claimed) (S.state S.awaitNext 0 (S.selected (S.normal true)) 0 false)
    [] [] (just D.request) nothing nothing nothing ∷ [])
changed-payload-first = refl

-- Generic cancellation is retained even when a different normal is the next expected packet.
canceled-retained : D.pair (D.clientState claimed) (S.state S.awaitNext 0 (S.selected S.canceled) 0 false)
  [] [] (just D.request) nothing nothing nothing ∈
  Order.orderedTargets S.genericNext claimed [] (R.sendResponse (D.reply (S.normal true)) ∷ [])
canceled-retained = Order.target-complete {p = S.genericNext} {s = claimed}
  {client = []} {server = R.sendResponse (D.reply (S.normal true)) ∷ []} (B.serverCallback B.allowCanceled (S.choose refl refl))

-- Fault admission remains a real alternative even though it is deliberately explored after normal registration.
fault-retained : ∀ {p c w sender completed flag cs sc pc ps rc rs} →
  D.pair c (S.state S.raising w sender completed flag) cs sc pc ps rc rs ∈
  Order.orderedTargets p (D.pair c (S.state S.admit w sender completed flag) cs sc pc ps rc rs) [] []
fault-retained = Order.target-complete (B.serverInternal S.excessive)

-- All ordered candidates remain independently justified for every contract/state/input suffix.
all-state-sound : ∀ {p state client server target} →
  target ∈ Order.orderedTargets p state client server → B.Tau p state target
all-state-sound = Order.target-sound

-- All independent hidden source moves remain in the ordered list for arbitrary input suffixes.
all-state-complete : ∀ {p state client server target} →
  B.Tau p state target → target ∈ Order.orderedTargets p state client server
all-state-complete = Order.target-complete

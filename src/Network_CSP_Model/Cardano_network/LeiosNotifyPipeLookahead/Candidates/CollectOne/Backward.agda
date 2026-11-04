{-# OPTIONS --safe #-}

-- Baseline source traces are realized by a candidate with no greater completed count.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Backward
  (Notification : Set) where

open import Data.Bool using (Bool; true)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _<_; z≤n; s≤s)
open import Data.Nat.Properties using (≤-trans; n≤1+n)
open import Data.List using ([]; _∷_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as B
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification as C

-- Stable shared phases use the same reader; admission normalization handles the extra phases.
reader : B.Reader → C.Reader
reader B.first = C.first
reader B.admit = C.admit
reader B.register = C.register
reader B.awaitNext = C.awaitNext
reader B.signalQuit = C.signalQuit
reader B.flushing = C.flushing
reader B.doneReady = C.doneReady
reader B.closed = C.closed
reader B.raising = C.raising
reader B.failed = C.failed

-- Both models permit exactly the same sender activity in aligned shared phases.
active-reader : ∀ r → B.active r ≡ C.active (reader r)
active-reader B.first = refl
active-reader B.admit = refl
active-reader B.register = refl
active-reader B.awaitNext = refl
active-reader B.signalQuit = refl
active-reader B.flushing = refl
active-reader B.doneReady = refl
active-reader B.closed = refl
active-reader B.raising = refl
active-reader B.failed = refl

-- Aligned states preserve pending jobs, payload and flag, allowing only fewer candidate completions.
data Related : C.State → B.State → Set where
  aligned : ∀ {r w sender candidate baseline flag} → candidate ≤ baseline →
    Related (C.state (reader r) w sender candidate flag) (B.state r w sender baseline flag)

-- Positive right-hand work remains positive when other resources are added.
positive-right : ∀ m {n} → 0 < n → 0 < m + n
positive-right zero positive = positive
positive-right (suc m) positive = s≤s z≤n

-- An empty completed counter with old work takes the actual miss guard, never a blocking flush.
miss : ∀ {p w sender flag} → 0 < w + (C.activeJob sender + 0) →
  C.Run p (C.state C.inspect w sender 0 flag) [] (C.state C.register w sender 0 flag)
miss positive = C.internal (C.inspectPositive positive) (C.internal (C.pollMiss positive) C.stop)

-- Complete one mandatory inspection/poll without interleaving extra sender operations.
prepare : ∀ {p w sender completed flag} →
  Σ[ remaining ∈ ℕ ] (remaining ≤ completed ×
    C.Run p (C.state C.inspect w sender completed flag) [] (C.state C.register w sender remaining flag))
prepare {w = zero} {sender = C.idle} {completed = zero} =
  0 , z≤n , C.internal (C.inspectZero refl) C.stop
prepare {w = zero} {sender = C.claimed} {completed = zero} = 0 , z≤n , miss (s≤s z≤n)
prepare {w = zero} {sender = C.selected _} {completed = zero} = 0 , z≤n , miss (s≤s z≤n)
prepare {w = zero} {sender = C.sent} {completed = zero} = 0 , z≤n , miss (s≤s z≤n)
prepare {w = suc w} {completed = zero} = 0 , z≤n , miss (s≤s z≤n)
prepare {w = w} {sender = sender} {completed = suc completed} =
  completed , n≤1+n completed , C.internal
    (C.inspectPositive (positive-right w (positive-right (C.activeJob sender) (s≤s z≤n))))
    (C.internal C.pollHit C.stop)

-- Every baseline hidden move has a candidate hidden realization and preserves alignment.
tau : ∀ {p c b next} → Related c b → B.Tau b next →
  Σ[ after ∈ C.State ] (C.Run p c [] after × Related after next)
tau (aligned {w = w} {sender = sender} {candidate = completed} {flag = flag} bound) B.admitted
  with prepare {w = w} {sender = sender} {completed = completed} {flag = flag}
... | remaining , less , prefix = _ , C.internal C.admitted prefix , aligned (≤-trans less bound)
tau (aligned bound) B.excessive = _ , C.internal C.excessive C.stop , aligned bound
tau (aligned bound) B.registered = _ , C.internal C.registered C.stop , aligned bound
tau (aligned bound) B.setQuit = _ , C.internal C.setQuit C.stop , aligned bound
tau (aligned bound) (B.claim {r = r} live) = _ ,
  C.internal (C.claim (trans (sym (active-reader r)) live)) C.stop , aligned bound
tau (aligned bound) (B.cancel {r = r} live) = _ ,
  C.internal (C.cancel (trans (sym (active-reader r)) live)) C.stop , aligned bound
tau (aligned bound) (B.retire {r = r} live) = _ ,
  C.internal (C.retire (trans (sym (active-reader r)) live)) C.stop , aligned (s≤s bound)
tau (aligned z≤n) B.flush = _ , C.stop , aligned z≤n
tau (aligned (s≤s bound)) B.flush = _ , C.internal C.flush C.stop , aligned bound
tau (aligned z≤n) B.drained = _ , C.internal C.drained C.stop , aligned z≤n
tau (aligned bound) B.abort = _ , C.internal C.abort C.stop , aligned bound

-- Shared reading phases admit the same RequestNext/Quit action.
reading : ∀ {r} → B.Reading r → C.Reading (reader r)
reading B.atFirst = C.atFirst
reading B.atNext = C.atNext

-- Baseline visible actions keep their exact payload and source order in the candidate.
visible : ∀ {p c b a next} → Related c b → B.Step p b a next →
  Σ[ after ∈ C.State ] (C.Run p c (a ∷ []) after × Related after next)
visible (aligned bound) (B.receiveRequest canRead) = _ ,
  C.visible (C.receiveRequest (reading canRead)) C.stop , aligned bound
visible (aligned bound) (B.receiveQuit canRead) = _ ,
  C.visible (C.receiveQuit (reading canRead)) C.stop , aligned bound
visible (aligned bound) (B.choose {r = r} live allowed) = _ ,
  C.visible (C.choose (trans (sym (active-reader r)) live) allowed) C.stop , aligned bound
visible (aligned bound) (B.send {r = r} live) = _ ,
  C.visible (C.send (trans (sym (active-reader r)) live)) C.stop , aligned bound
visible (aligned z≤n) B.finish = _ , C.visible C.finish C.stop , aligned z≤n

-- Structural induction realizes every finite baseline source run from an aligned candidate.
run : ∀ {p c b actions target} → Related c b → B.Run p b actions target →
  Σ[ final ∈ C.State ] (C.Run p c actions final × Related final target)
run relation B.stop = _ , C.stop , relation
run relation (B.internal step rest) with tau relation step
... | after , prefix , alignedAfter with run alignedAfter rest
...   | final , suffix , alignedFinal = final , C.append prefix suffix , alignedFinal
run relation (B.visible step rest) with visible relation step
... | after , prefix , alignedAfter with run alignedAfter rest
...   | final , suffix , alignedFinal = final , C.append prefix suffix , alignedFinal

-- Fresh baseline source traces are candidate source traces without extra assumptions.
from-initial : ∀ {p actions target} → B.Run p B.initial actions target →
  Σ[ final ∈ C.State ] (C.Run p C.initial actions final × Related final target)
from-initial execution = run (aligned z≤n) execution

{-# OPTIONS --safe #-}

-- Exact accounting includes receiver registration before RequestNext/Quit Send records.
module Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting
  (Notification Return : Set) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _∷ʳ_; length)
open import Data.List.Properties using (length-++)
open import Data.Nat using (ℕ; suc; _+_)
open import Data.Nat.Properties using (+-suc; +-identityʳ; suc-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; cong₂; sym; trans)
open import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return

-- Registered work precedes the source counter increment at the Send trace hook.
registered : Main → ℕ
registered writingRequest = 1
registered (writingQuit true) = 1
registered _ = 0

-- A running receiver owns one job until its result is published, including markers.
busy : Receiver → ℕ
busy idle = 0
busy _ = 1

-- Jobs, the current receiver and published results are disjoint unfinished resources.
work : State → ℕ
work c = length (jobs c) + (busy (receiver c) + length (results c))

-- The source inFlight counter is corrected only for the one registered pending Send.
Accounted : State → Set
Accounted c = inFlight c + registered (main c) ≡ work c

-- Appending one queue element adds exactly one occurrence, independently of its value.
snoc-length : ∀ {A : Set} (xs : List A) x → length (xs ∷ʳ x) ≡ suc (length xs)
snoc-length xs x = trans (length-++ xs {ys = x ∷ []})
  (trans (+-suc (length xs) 0) (cong suc (+-identityʳ (length xs))))

-- Registration adds a job before its corresponding counter increment.
add-job : ∀ {n : ℕ} {r : Receiver} {js : List Job} {rs : List Token} (job : Job) →
  n + 0 ≡ length js + (busy r + length rs) →
  n + 1 ≡ length (js ∷ʳ job) + (busy r + length rs)
add-job {n} {r} {js} {rs} job accounted = trans (+-suc n 0)
  (trans (cong suc accounted) (sym (cong (_+ (busy r + length rs)) (snoc-length js job))))

-- Collection consumes one published result and decrements inFlight together.
collect : ∀ {n : ℕ} {r : Receiver} {js : List Job} {rs : List Token} →
  suc n + 0 ≡ length js + (busy r + suc (length rs)) →
  n + 0 ≡ length js + (busy r + length rs)
collect {n} {r} {js} {rs} accounted = suc-injective
  (trans accounted (trans (cong (length js +_) (+-suc (busy r) (length rs)))
    (+-suc (length js) (busy r + length rs))))

-- Every visible source operation preserves the corrected inventory, including Done.
step-accounted : ∀ {s a t} → Step s a t → Accounted s → Accounted t
step-accounted continueZero accounted = accounted
step-accounted (continueBelow _) accounted = accounted
step-accounted (continueFull _ _) accounted = accounted
step-accounted stopRequested accounted = accounted
step-accounted (sentRequest {n = n}) accounted = trans (sym (+-suc n 0)) accounted
step-accounted sentQuitIdle accounted = accounted
step-accounted (sentQuitBusy {n = n}) accounted = trans (sym (+-suc n 0)) accounted
step-accounted (receivedReply _) accounted = accounted
step-accounted (delivered _) accounted = accounted
step-accounted receivedDone accounted = accounted

-- Scheduling only transfers work between the three resources or accounts for registration.
tau-accounted : ∀ {s t} → Tau s t → Accounted s → Accounted t
tau-accounted (registerResponse {r = r} {js = js} {rs = rs} {n = n}) accounted =
  add-job {n} {r} {js} {rs} responseJob accounted
tau-accounted setStopIdle accounted = accounted
tau-accounted setStopBusy accounted = accounted
tau-accounted (registerMarker {r = r} {js = js} {rs = rs} {n = n}) accounted =
  add-job {n} {r} {js} {rs} quitMarker accounted
tau-accounted optionalEmpty accounted = accounted
tau-accounted (optionalResult {r = r} {js = js} {rs = rs} {n = n}) accounted = collect {n} {r} {js} {rs} accounted
tau-accounted (blockingResult {r = r} {js = js} {rs = rs} {n = n}) accounted = collect {n} {r} {js} {rs} accounted
tau-accounted adjustArrival accounted = accounted
tau-accounted (drainResult {r = r} {js = js} {rs = rs} {n = n}) accounted = collect {n} {r} {js} {rs} accounted
tau-accounted drained accounted = accounted
tau-accounted (startResponse {js = js} {rs = rs} _) accounted =
  trans accounted (sym (+-suc (length js) (length rs)))
tau-accounted (startMarker {js = js} {rs = rs} _) accounted =
  trans accounted (sym (+-suc (length js) (length rs)))
tau-accounted (keepReply _) accounted = accounted
tau-accounted (discardReply _) accounted = accounted
tau-accounted (countArrival _) accounted = accounted
tau-accounted (publishResponse {js = js} {rs = rs} _) accounted =
  trans accounted (cong (length js +_) (sym (snoc-length rs responseToken)))
tau-accounted (publishMarker {js = js} {rs = rs} _) accounted =
  trans accounted (cong (length js +_) (sym (snoc-length rs markerToken)))

-- The corrected equation holds throughout every finite source execution.
run-accounted : ∀ {s actions t} → Run s actions t → Accounted s → Accounted t
run-accounted stop accounted = accounted
run-accounted (internal pr run) accounted = run-accounted run (tau-accounted pr accounted)
run-accounted (visible pr run) accounted = run-accounted run (step-accounted pr accounted)

-- Fresh client state has no invented jobs, receivers or results.
initial-accounted : ∀ {actions t} → Run initial actions t → Accounted t
initial-accounted run = run-accounted run refl

-- All three client-side work locations have emptied, not just the scalar counter.
record Empty (c : State) : Set where
  constructor empty
  field
    jobs-empty : jobs c ≡ []
    receiver-idle : receiver c ≡ idle
    results-empty : results c ≡ []
open Empty public

-- Zero total inventory constructively empties every resource.
empty-work : (c : State) → work c ≡ 0 → Empty c
empty-work (client m r (_ ∷ _) rs n a q v) ()
empty-work (client m idle [] [] n a q v) _ = empty refl refl refl
empty-work (client m idle [] (_ ∷ _) n a q v) ()
empty-work (client m awaiting [] rs n a q v) ()
empty-work (client m (inspect _) [] rs n a q v) ()
empty-work (client m (handling _) [] rs n a q v) ()
empty-work (client m bumpArrival [] rs n a q v) ()
empty-work (client m (publish _) [] rs n a q v) ()

-- A zero source counter implies empty work only when no registered Send is pending.
empty-at-zero : ∀ {c} → Accounted c → inFlight c ≡ 0 → registered (main c) ≡ 0 → Empty c
empty-at-zero {c} accounted zero-counter no-registration =
  empty-work c (trans (sym accounted) (cong₂ _+_ zero-counter no-registration))

{-# OPTIONS --safe #-}

-- Constructive source realizations require an explicitly supplied successful return value.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientComplete
  (Notification Return : Set) (returnValue : Return) where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥-elim)
open import Data.Integer using (ℤ; +_; _+_; +<+)
open import Data.Integer.Properties using () renaming (_<?_ to compareInteger)
open import Data.List using (List; []; _∷_; _∷ʳ_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat.Properties as Nat
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; subst; sym; trans)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (does)
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Notification as Q
open Q.Observation Return

-- Replicated unclaimed receivers give a canonical unbounded generic client schedule.
jobs : ℕ → List C.Job
jobs zero = []
jobs (suc n) = C.responseJob ∷ jobs n

-- Registering a fresh receiver extends precisely this canonical FIFO.
jobs-snoc : ∀ n → jobs n ∷ʳ C.responseJob ≡ jobs (suc n)
jobs-snoc zero = refl
jobs-snoc (suc n) = cong (C.responseJob ∷_) (jobs-snoc n)

-- Before Quit, completed responses are promptly collected in this chosen realization.
openState : ℕ → C.State
openState n = C.client C.poll C.idle (jobs n) [] n (+ 0) false nothing

-- The pending Send may finish only after its already received reply was published.
leadState : C.State
leadState = C.client C.writingRequest C.idle [] (C.responseToken ∷ []) 0 (+ 1) false nothing

-- The dummy Quit receiver is retained until all response receivers preceding it finish.
quitState : ℕ → ℤ → C.State
quitState n a = C.client C.draining C.idle (jobs n ∷ʳ C.quitMarker) [] (suc n) a true (just returnValue)

-- Idle Quit has no dummy receiver; both paths use an actual inhabited stored return.
awaitState : ℤ → C.State
awaitState a = C.client C.awaitDone C.idle [] [] 0 a true (just returnValue)

-- Completion retains the successful callback return and no unprocessed receiver resources.
closedState : ℤ → C.State
closedState a = C.client C.closed C.idle [] [] 0 a true (just returnValue)

-- Canonical representatives are witnesses for realizability, not restrictions on soundness.
data Canonical : Q.State → C.State → Set where
  fresh : ∀ {n} → Canonical (Q.Open n) (openState n)
  lead : Canonical Q.Lead leadState
  busyQuit : ∀ {n a} → Canonical (Q.QuitSeen n) (quitState n a)
  idleQuit : ∀ {a} → Canonical (Q.QuitSeen 0) (awaitState a)
  closed : ∀ {a} → Canonical Q.Closed (closedState a)

-- Concrete projected runs preserve their exact source action witness.
record Segment (s : C.State) (rows : List Q.Wire) (t : C.State) : Set where
  constructor segment
  field
    actions : List C.Action
    run : C.Run s actions t
    projected : wire actions ≡ rows
open Segment public

-- Empty source execution emits no driver hook.
empty : ∀ {s} → Segment s [] s
empty = segment [] C.stop refl

-- Hidden source operations prefix a segment without changing its driver records.
tau : ∀ {s t u rows} → C.Tau s t → Segment t rows u → Segment s rows u
tau pr (segment actions run eq) = segment actions (C.internal pr run) eq

-- Successful callback actions are erased, while their original values remain in the witness.
callback : ∀ {s t u a rows} → C.Step s a t → observe a ≡ nothing → Segment t rows u → Segment s rows u
callback {a = C.continue _} pr refl (segment actions run eq) = segment (_ ∷ actions) (C.visible pr run) eq
callback {a = C.terminate _} pr refl (segment actions run eq) = segment (_ ∷ actions) (C.visible pr run) eq
callback {a = C.handled _} pr refl (segment actions run eq) = segment (_ ∷ actions) (C.visible pr run) eq

-- Driver-visible actions prefix exactly their own message, with the complete reply payload.
hook : ∀ {s t u a row rows} → C.Step s a t → observe a ≡ just row → Segment t rows u → Segment s (row ∷ rows) u
hook {a = C.sendRequest} pr refl (segment actions run eq) = segment (_ ∷ actions) (C.visible pr run) (cong (_ ∷_) eq)
hook {a = C.sendQuit} pr refl (segment actions run eq) = segment (_ ∷ actions) (C.visible pr run) (cong (_ ∷_) eq)
hook {a = C.recvReply _} pr refl (segment actions run eq) = segment (_ ∷ actions) (C.visible pr run) (cong (_ ∷_) eq)
hook {a = C.recvDone} pr refl (segment actions run eq) = segment (_ ∷ actions) (C.visible pr run) (cong (_ ∷_) eq)

-- Source execution concatenation retains internal transitions and source callback records.
run-append : ∀ {s t u xs ys} → C.Run s xs t → C.Run t ys u → C.Run s (xs ++ ys) u
run-append C.stop rest = rest
run-append (C.internal pr run) rest = C.internal pr (run-append run rest)
run-append (C.visible pr run) rest = C.visible pr (run-append run rest)

-- Segments compose with the exact projection equation rather than a kind-only abstraction.
append : ∀ {s t u xs ys} → Segment s xs t → Segment t ys u → Segment s (xs ++ ys) u
append (segment as pr eq) (segment bs rest eq′) = segment (as ++ bs) (run-append pr rest)
  (trans (wire-append as bs) (cong₂-append eq eq′))
  where
  -- Equality transports each projected part without changing the concatenation order.
  cong₂-append : ∀ {xs ys zs ws : List Q.Wire} → xs ≡ ys → zs ≡ ws → xs ++ zs ≡ ys ++ ws
  cong₂-append refl refl = refl

-- A true comparison witness determines the Boolean branch used by the source.
comparison-true : ∀ {A : Set} (d : Dec A) → A → does d ≡ true
comparison-true (yes _) pr = refl
comparison-true (no deny) pr = ⊥-elim (deny pr)

-- A chosen depth one above the current counter always enables the generic below branch.
high : ∀ n → C.below n (+ (suc n)) ≡ true
high n = comparison-true (compareInteger (+ n) (+ suc n)) (+<+ Nat.≤-refl)

-- Start an additional response receiver using an unconstrained successful generic callback.
issue : ∀ n → Segment (openState n) [] (C.client C.issue C.idle (jobs n) [] n (+ 0) false nothing)
issue zero = callback (C.continueZero {k = + 0}) refl empty
issue (suc n) = callback (C.continueBelow {k = + suc (suc n)} (high (suc n))) refl (tau C.optionalEmpty empty)

-- Prompt collection restores the canonical pre-Quit counter and arrived count.
collect : ∀ n → Segment
  (C.client C.poll C.idle (jobs n) (C.responseToken ∷ []) (suc n) (+ 1) false nothing)
  [] (openState n)
collect n = callback (C.continueBelow {k = + suc (suc n)} (high (suc n))) refl (tau C.optionalResult (tau C.adjustArrival empty))

-- Every independently admitted wire rule has a concrete exact source realization.
realize : ∀ {q row q′ s} → Canonical q s → Q.Step q row q′ →
  Σ[ t ∈ C.State ] (Segment s (row ∷ []) t × Canonical q′ t)
realize (fresh {n}) Q.sendRequest = _ ,
  subst (Segment (openState n) (Q.request ∷ []))
    (cong (λ js → C.client C.poll C.idle js [] (suc n) (+ 0) false nothing) (jobs-snoc n))
    (append (issue n) (tau C.registerResponse (hook C.sentRequest refl empty))) , fresh
realize lead Q.finishRequest = _ , hook C.sentRequest refl (collect 0) , fresh
realize (fresh {suc n}) (Q.receiveReply {m = value}) = _ ,
  tau (C.startResponse refl) (hook (C.receivedReply refl) refl
    (tau (C.keepReply refl) (callback (C.delivered refl) refl
      (tau (C.countArrival refl) (tau (C.publishResponse refl) (collect n)))))) , fresh
realize (fresh {zero}) (Q.earlyReply {m = value}) = _ ,
  append (issue 0) (tau C.registerResponse (tau (C.startResponse refl)
    (hook (C.receivedReply refl) refl (tau (C.keepReply refl)
      (callback (C.delivered refl) refl (tau (C.countArrival refl)
        (tau (C.publishResponse refl) empty))))))) , lead
realize (fresh {zero}) Q.sendQuit = _ , callback (C.stopRequested {x = returnValue}) refl
  (tau C.setStopIdle (hook C.sentQuitIdle refl empty)) , idleQuit
realize (fresh {suc n}) Q.sendQuit = _ , callback (C.stopRequested {x = returnValue}) refl
  (tau C.setStopBusy (tau C.registerMarker (hook C.sentQuitBusy refl empty))) , busyQuit
realize (busyQuit {n = suc n} {a}) (Q.drainReply {m = value}) = _ ,
  tau (C.startResponse refl) (hook (C.receivedReply refl) refl
    (tau (C.discardReply refl) (tau (C.countArrival refl)
      (tau (C.publishResponse refl) (tau C.drainResult empty))))) , busyQuit
realize (idleQuit {a}) Q.receiveDone = _ , hook C.receivedDone refl empty , closed
realize (busyQuit {n = zero} {a}) Q.receiveDone = _ ,
  tau (C.startMarker refl) (tau (C.publishMarker refl)
    (tau C.drainResult (tau C.drained (hook C.receivedDone refl empty)))) , closed

-- Induction realizes every finite quotient prefix, including unfinished and receive-ahead EOF.
complete : ∀ {q rows q′ s} → Canonical q s → Q.Run q rows q′ →
  Σ[ t ∈ C.State ] (Segment s rows t × Canonical q′ t)
complete canonical Q.stop = _ , empty , canonical
complete canonical (Q.step pr rest) with realize canonical pr
... | middle , prefix , next with complete next rest
...   | last , suffix , final = last , append prefix suffix , final

-- Every admitted initial prefix has a source witness with an explicitly inhabited return type.
initial-complete : ∀ {rows} → Q.HasTrace Q.initial rows →
  Σ[ actions ∈ List C.Action ] (Σ[ t ∈ C.State ] (C.Run C.initial actions t × wire actions ≡ rows))
initial-complete (_ , run) with complete fresh run
... | last , segment actions pr eq , final = actions , last , pr , eq

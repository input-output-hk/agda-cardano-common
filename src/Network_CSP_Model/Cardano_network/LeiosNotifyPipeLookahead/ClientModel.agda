{-# OPTIONS --safe #-}

-- Pipelined-client control and receiver/collect queues from consensus 2416493.
-- Successful callback/channel operations and non-overflowing arithmetic are abstracted.
module Cardano_network.LeiosNotifyPipeLookahead.ClientModel
  (Notification Return : Set) where

open import Data.Nat using (ℕ; zero; suc)
open import Data.Integer using (ℤ; +_; _+_; _-_)
import Data.Integer.Properties as Int
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _∷ʳ_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (does)
open import Cardano_network.LeiosNotifyPipeLookahead.Model Notification using (Reply)

-- Sender control follows the peer continuation, including its dummy Quit receiver.
data Main : Set where
  poll issue writingRequest stopPending registerQuit collectingMaybe collectingWait
    adjustCollected draining awaitDone closed : Main
  writingQuit : (hasMarker : Bool) → Main

-- Receiver processing and result publication are separate operations.
data Receiver : Set where
  idle awaiting bumpArrival : Receiver
  inspect handling : Reply → Receiver
  publish : (isMarker : Bool) → Receiver

-- The Quit receiver returns immediately and never consumes a wire response.
data Job : Set where
  responseJob quitMarker : Job

-- Completed receiver results are FIFO; only normal collection adjusts arrived.
data Token : Set where
  responseToken markerToken : Token

-- Retained return values distinguish termination requests from successful completion.
record State : Set where
  constructor client
  field
    main : Main
    receiver : Receiver
    jobs : List Job
    results : List Token
    inFlight : ℕ
    arrived : ℤ
    stopFlag : Bool
    returnValue : Maybe Return
open State public

-- The initial go Zero has no receiver registered or result available.
initial : State
initial = client poll idle [] [] 0 (+ 0) false nothing

-- The source compares signed maximum depth against the nonnegative Nat counter.
below : ℕ → ℤ → Bool
below n k = does ((+ n) Int.<? k)

-- A positive arrived count can precede actual collect-queue publication.
positive : ℤ → Bool
positive n = does ((+ 0) Int.<? n)

-- Successful return stops both driver loops in this abstraction.
active : Main → Bool
active closed = false
active _ = true

-- Callback decisions and delivery are explicit operations, distinct from wire records.
data Action : Set where
  continue : ℤ → Action
  terminate : Return → Action
  handled recvReply : Reply → Action
  sendRequest sendQuit recvDone : Action

-- Independent visible rules preserve the source's Zero and full-pipe branches.
data Step : State → Action → State → Set where
  continueZero : ∀ {r js rs a q v k} →
    Step (client poll r js rs zero a q v) (continue k)
      (client issue r js rs zero a q v)
  continueBelow : ∀ {r js rs n a q v k} → below (suc n) k ≡ true →
    Step (client poll r js rs (suc n) a q v) (continue k)
      (client collectingMaybe r js rs (suc n) a q v)
  continueFull : ∀ {r js rs n a q v k} → below (suc n) k ≡ false → positive a ≡ true →
    Step (client poll r js rs (suc n) a q v) (continue k)
      (client collectingWait r js rs (suc n) a q v)
  stopRequested : ∀ {r js rs n a q v x} →
    Step (client poll r js rs n a q v) (terminate x)
      (client stopPending r js rs n a q (just x))
  sentRequest : ∀ {r js rs n a q v} →
    Step (client writingRequest r js rs n a q v) sendRequest
      (client poll r js rs (suc n) a q v)
  sentQuitIdle : ∀ {r js rs a x} →
    Step (client (writingQuit false) r js rs zero a true (just x)) sendQuit
      (client awaitDone r js rs zero a true (just x))
  sentQuitBusy : ∀ {r js rs n a x} →
    Step (client (writingQuit true) r js rs n a true (just x)) sendQuit
      (client draining r js rs (suc n) a true (just x))
  receivedReply : ∀ {m js rs n a q v reply} → active m ≡ true →
    Step (client m awaiting js rs n a q v) (recvReply reply)
      (client m (inspect reply) js rs n a q v)
  delivered : ∀ {m js rs n a q v reply} → active m ≡ true →
    Step (client m (handling reply) js rs n a q v) (handled reply)
      (client m bumpArrival js rs n a q v)
  receivedDone : ∀ {r js rs a x} →
    Step (client awaitDone r js rs zero a true (just x)) recvDone
      (client closed r js rs zero a true (just x))

-- Hidden operations mirror registration, source STM effects and driver publication.
data Tau : State → State → Set where
  registerResponse : ∀ {r js rs n a q v} →
    Tau (client issue r js rs n a q v)
      (client writingRequest r (js ∷ʳ responseJob) rs n a q v)
  setStopIdle : ∀ {r js rs a q x} →
    Tau (client stopPending r js rs zero a q (just x))
      (client (writingQuit false) r js rs zero a true (just x))
  setStopBusy : ∀ {r js rs n a q x} →
    Tau (client stopPending r js rs (suc n) a q (just x))
      (client registerQuit r js rs (suc n) a true (just x))
  registerMarker : ∀ {r js rs n a x} →
    Tau (client registerQuit r js rs n a true (just x))
      (client (writingQuit true) r (js ∷ʳ quitMarker) rs n a true (just x))
  optionalEmpty : ∀ {r js n a q v} →
    Tau (client collectingMaybe r js [] (suc n) a q v)
      (client issue r js [] (suc n) a q v)
  optionalResult : ∀ {r js rs n a q v} →
    Tau (client collectingMaybe r js (responseToken ∷ rs) (suc n) a q v)
      (client adjustCollected r js rs n a q v)
  blockingResult : ∀ {r js rs n a q v} →
    Tau (client collectingWait r js (responseToken ∷ rs) (suc n) a q v)
      (client adjustCollected r js rs n a q v)
  adjustArrival : ∀ {r js rs n a q v} →
    Tau (client adjustCollected r js rs n a q v)
      (client poll r js rs n (a - (+ 1)) q v)
  drainResult : ∀ {r js rs n a x token} →
    Tau (client draining r js (token ∷ rs) (suc n) a true (just x))
      (client draining r js rs n a true (just x))
  drained : ∀ {r js rs a x} →
    Tau (client draining r js rs zero a true (just x))
      (client awaitDone r js rs zero a true (just x))
  startResponse : ∀ {m js rs n a q v} → active m ≡ true →
    Tau (client m idle (responseJob ∷ js) rs n a q v)
      (client m awaiting js rs n a q v)
  startMarker : ∀ {m js rs n a q v} → active m ≡ true →
    Tau (client m idle (quitMarker ∷ js) rs n a q v)
      (client m (publish true) js rs n a q v)
  keepReply : ∀ {m js rs n a v reply} → active m ≡ true →
    Tau (client m (inspect reply) js rs n a false v)
      (client m (handling reply) js rs n a false v)
  discardReply : ∀ {m js rs n a v reply} → active m ≡ true →
    Tau (client m (inspect reply) js rs n a true v)
      (client m bumpArrival js rs n a true v)
  countArrival : ∀ {m js rs n a q v} → active m ≡ true →
    Tau (client m bumpArrival js rs n a q v)
      (client m (publish false) js rs n (a + (+ 1)) q v)
  publishResponse : ∀ {m js rs n a q v} → active m ≡ true →
    Tau (client m (publish false) js rs n a q v)
      (client m idle js (rs ∷ʳ responseToken) n a q v)
  publishMarker : ∀ {m js rs n a q v} → active m ≡ true →
    Tau (client m (publish true) js rs n a q v)
      (client m idle js (rs ∷ʳ markerToken) n a q v)

-- Source-model executions expose callback decisions but preserve every wire record.
data Run : State → List Action → State → Set where
  stop : ∀ {s} → Run s [] s
  internal : ∀ {s t u es} → Tau s t → Run t es u → Run s es u
  visible : ∀ {s t u act es} → Step s act t → Run t es u → Run s (act ∷ es) u

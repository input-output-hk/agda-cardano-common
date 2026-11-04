{-# OPTIONS --safe #-}

-- Independent CollectOne reference: mathematical successful operations and explicit admission rejection.
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model
  (Notification : Set) where

open import Data.Bool using (Bool; false; true)
open import Data.Nat using (ℕ; zero; suc; _+_; _<_)
open import Data.List using (List; []; _∷_; _++_)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as Base
open Base public using (Contract; genericNext; nodeNext; Reply; normal; canceled;
  Sender; idle; claimed; selected; sent; Action; recvRequest; recvQuit;
  nextReply; sendReply; sendDone; allowed; unsent)

-- Inspect evaluates the old index; poll is exactly one optional FlushSender transaction.
data Reader : Set where
  first admit inspect poll register awaitNext signalQuit flushing doneReady closed raising failed : Reader

-- The current unregistered request is separate from all old registered jobs.
record State : Set where
  constructor state
  field
    reader : Reader
    waiting : ℕ
    sender : Sender
    completed : ℕ
    quitFlag : Bool
open State public

-- The first ordinary Await has no registered jobs or selected replies.
initial : State
initial = state first 0 idle 0 false

-- Only ordinary Await and post-registration AwaitLookahead can receive a command.
data Reading : Reader → Set where
  atFirst : Reading first
  atNext : Reading awaitNext

-- Joined local return/failure ends successful sender operations at this abstraction boundary.
active : Reader → Bool
active closed = false
active failed = false
active _ = true

-- Count the active sender even after its Send record but before retirement.
activeJob : Sender → ℕ
activeJob idle = 0
activeJob _ = 1

-- This is the Nat-index inventory at inspect/poll, before the current registration.
registeredJobs : State → ℕ
registeredJobs s = waiting s + (activeJob (sender s) + completed s)

-- Every admitted/current request stays unregistered throughout inspection and polling.
unregistered : Reader → ℕ
unregistered admit = 1
unregistered inspect = 1
unregistered poll = 1
unregistered register = 1
unregistered raising = 1
unregistered failed = 1
unregistered _ = 0

-- Completed/unretired resources remain distinct from wire replies still owed.
owed : State → ℕ
owed s = unregistered (reader s) + (waiting s + unsent (sender s))

-- The visible alphabet retains source callbacks; wire observation is defined separately.
data Step (contract : Contract) : State → Action → State → Set where
  receiveRequest : ∀ {r w sender c} → Reading r →
    Step contract (state r w sender c false) recvRequest (state admit w sender c false)
  receiveQuit : ∀ {r w sender c} → Reading r →
    Step contract (state r w sender c false) recvQuit (state signalQuit w sender c false)
  choose : ∀ {r w c m} → active r ≡ true → allowed contract m ≡ true →
    Step contract (state r w claimed c false) (nextReply m)
      (state r w (selected m) c false)
  send : ∀ {r w c q m} → active r ≡ true →
    Step contract (state r w (selected m) c q) (sendReply m)
      (state r w sent c q)
  finish : Step contract (state doneReady 0 idle 0 true) sendDone
    (state closed 0 idle 0 true)

-- Independent guards follow the pinned index case and atomic doneVar decision.
data Tau : State → State → Set where
  admitted : ∀ {w sender c q} →
    Tau (state admit w sender c q) (state inspect w sender c q)
  excessive : ∀ {w sender c q} →
    Tau (state admit w sender c q) (state raising w sender c q)
  inspectZero : ∀ {w sender c q} → w + (activeJob sender + c) ≡ 0 →
    Tau (state inspect w sender c q) (state register w sender c q)
  inspectPositive : ∀ {w sender c q} → 0 < w + (activeJob sender + c) →
    Tau (state inspect w sender c q) (state poll w sender c q)
  pollHit : ∀ {w sender c q} →
    Tau (state poll w sender (suc c) q) (state register w sender c q)
  pollMiss : ∀ {w sender q} → 0 < w + (activeJob sender + 0) →
    Tau (state poll w sender 0 q) (state register w sender 0 q)
  registered : ∀ {w sender c q} →
    Tau (state register w sender c q) (state awaitNext (suc w) sender c q)
  setQuit : ∀ {w sender c} →
    Tau (state signalQuit w sender c false) (state flushing w sender c true)
  claim : ∀ {r w c q} → active r ≡ true →
    Tau (state r (suc w) idle c q) (state r w claimed c q)
  cancel : ∀ {r w c} → active r ≡ true →
    Tau (state r w claimed c true) (state r w (selected canceled) c true)
  retire : ∀ {r w c q} → active r ≡ true →
    Tau (state r w sent c q) (state r w idle (suc c) q)
  flush : ∀ {w sender c q} →
    Tau (state flushing w sender (suc c) q) (state flushing w sender c q)
  drained : Tau (state flushing 0 idle 0 true) (state doneReady 0 idle 0 true)
  abort : ∀ {w sender c q} →
    Tau (state raising w sender c q) (state failed w sender c q)

-- Source prefixes retain every independently specified visible/internal operation.
data Run (contract : Contract) : State → List Action → State → Set where
  stop : ∀ {s} → Run contract s [] s
  internal : ∀ {s t u es} → Tau s t → Run contract t es u → Run contract s es u
  visible : ∀ {s t u a es} → Step contract s a t → Run contract t es u →
    Run contract s (a ∷ es) u

-- Concatenation records a chosen source schedule without adding transition rules.
append : ∀ {p s t u es fs} → Run p s es t → Run p t fs u → Run p s (es ++ fs) u
append stop suffix = suffix
append (internal pr run) suffix = internal pr (append run suffix)
append (visible pr run) suffix = visible pr (append run suffix)

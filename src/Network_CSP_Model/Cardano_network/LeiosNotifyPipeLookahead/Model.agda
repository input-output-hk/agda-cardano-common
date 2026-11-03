{-# OPTIONS --safe #-}

-- Operational server transcription of consensus 2416493 and typed-protocols 9b46272.
-- Callback readiness is an environment action; admission and scheduling are internal.
-- Mathematical counts correspond to the Int-backed runtime Nat only without overflow.
module Cardano_network.LeiosNotifyPipeLookahead.Model
  (Notification : Set) where

import Data.Bool.Properties as Bool
open import Relation.Nullary using (Dec; yes; no)
import Relation.Binary.Definitions
open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

-- Generic next may return cancellation; the pinned node queue returns normal replies.
data Contract : Set where
  genericNext nodeNext : Contract

-- A selected reply retains its payload until that exact reply is sent.
data Reply : Set where
  normal : Notification → Reply
  canceled : Reply

-- The reader runs independently of the sender, including while a send is pending.
data Reader : Set where
  first admit register awaitNext signalQuit flushing doneReady closed raising failed : Reader

-- Sent is before the driver's completion-counter increment.
data Sender : Set where
  idle claimed sent : Sender
  selected : Reply → Sender

-- Jobs waiting, active and completed are distinct driver resources.
record State : Set where
  constructor state
  field
    reader : Reader
    waiting : ℕ
    sender : Sender
    completed : ℕ
    quitFlag : Bool
open State public

-- First Await has no deferred sender and no completion tokens.
initial : State
initial = state first 0 idle 0 false

-- Only these two reader phases can consume another wire command.
data Reading : Reader → Set where
  atFirst : Reading first
  atNext : Reading awaitNext

-- Fault cancellation and normal completion stop both threads.
active : Reader → Bool
active closed = false
active failed = false
active _ = true

-- Runtime callback policy, separate from protocol agency.
allowed : Contract → Reply → Bool
allowed _ (normal _) = true
allowed genericNext canceled = true
allowed nodeNext canceled = false

-- Callback results are explicit model actions, erased by a later wire observation.
data Action : Set where
  recvRequest recvQuit sendDone : Action
  nextReply sendReply : Reply → Action

-- Visible operational steps are independently specified before the interpreter.
data Step (contract : Contract) : State → Action → State → Set where
  receiveRequest : ∀ {r w s c} → Reading r →
    Step contract (state r w s c false) recvRequest (state admit w s c false)
  receiveQuit : ∀ {r w s c} → Reading r →
    Step contract (state r w s c false) recvQuit (state signalQuit w s c false)
  choose : ∀ {r w c m} → active r ≡ true → allowed contract m ≡ true →
    Step contract (state r w claimed c false) (nextReply m)
      (state r w (selected m) c false)
  send : ∀ {r w c q m} → active r ≡ true →
    Step contract (state r w (selected m) c q) (sendReply m)
      (state r w sent c q)
  finish : Step contract (state doneReady 0 idle 0 true) sendDone
    (state closed 0 idle 0 true)

-- Independent hidden transitions preserve source program order and fault paths.
data Tau : State → State → Set where
  admitted : ∀ {w s c q} →
    Tau (state admit w s c q) (state register w s c q)
  excessive : ∀ {w s c q} →
    Tau (state admit w s c q) (state raising w s c q)
  registered : ∀ {w s c q} →
    Tau (state register w s c q) (state awaitNext (suc w) s c q)
  setQuit : ∀ {w s c} →
    Tau (state signalQuit w s c false) (state flushing w s c true)
  claim : ∀ {r w c q} → active r ≡ true →
    Tau (state r (suc w) idle c q) (state r w claimed c q)
  cancel : ∀ {r w c} → active r ≡ true →
    Tau (state r w claimed c true) (state r w (selected canceled) c true)
  retire : ∀ {r w c q} → active r ≡ true →
    Tau (state r w sent c q) (state r w idle (suc c) q)
  flush : ∀ {w s c q} →
    Tau (state flushing w s (suc c) q) (state flushing w s c q)
  drained : Tau (state flushing 0 idle 0 true) (state doneReady 0 idle 0 true)
  abort : ∀ {w s c q} →
    Tau (state raising w s c q) (state failed w s c q)

-- One wire request is unregistered until admission and sender registration finish.
unregistered : Reader → ℕ
unregistered admit = 1
unregistered register = 1
unregistered raising = 1
unregistered failed = 1
unregistered _ = 0

-- A job stops owing its reply at the Send observation, before retirement.
unsent : Sender → ℕ
unsent claimed = 1
unsent (selected _) = 1
unsent _ = 0

-- Completed but unflushed jobs do not contribute to unanswered wire requests.
owed : State → ℕ
owed (state r w s c q) = unregistered r + (w + unsent s)

-- Concrete sequential runs include both scheduling steps and callback results.
data Run (contract : Contract) : State → List Action → State → Set where
  stop : ∀ {s} → Run contract s [] s
  internal : ∀ {s t u es} → Tau s t → Run contract t es u → Run contract s es u
  visible : ∀ {s t u a es} → Step contract s a t → Run contract t es u →
    Run contract s (a ∷ es) u

-- Join finite operational executions without changing their observations.
append : ∀ {contract s t u es fs} → Run contract s es t → Run contract t fs u →
  Run contract s (es ++ fs) u
append stop q = q
append (internal t p) q = internal t (append p q)
append (visible t p) q = visible t (append p q)

-- Observable wire actions omit only application reply-selection results.
wireActions : List Action → List Action
wireActions [] = []
wireActions (nextReply _ ∷ xs) = wireActions xs
wireActions (x ∷ xs) = x ∷ wireActions xs

-- A proof-carrying internal successor supports executable tree construction.
Internal : State → Set
Internal s = Σ[ t ∈ State ] Tau s t

-- Reader transitions are enumerated without serializing the independent sender.
readerMoves : (s : State) → List (Internal s)
readerMoves (state admit w s c q) =
  (_ , admitted) ∷ (_ , excessive) ∷ []
readerMoves (state register w s c q) = (_ , registered) ∷ []
readerMoves (state signalQuit w s c false) = (_ , setQuit) ∷ []
readerMoves (state flushing w s (suc c) q) = (_ , flush) ∷ []
readerMoves (state flushing zero idle zero true) = (_ , drained) ∷ []
readerMoves (state raising w s c q) = (_ , abort) ∷ []
readerMoves _ = []

-- A guarded hidden transition retains its independent Tau certificate.
internalWhen : ∀ {s t} {P : Set} → Dec P → (P → Tau s t) → List (Internal s)
internalWhen {t = t} (yes pr) build = (t , build pr) ∷ []
internalWhen (no _) _ = []

-- Sender transitions stay available while the reader handles Quit or an exception.
senderMoves : (s : State) → List (Internal s)
senderMoves (state r w claimed c true) =
  internalWhen (active r Bool.≟ true) cancel
senderMoves (state r w sent c q) =
  internalWhen (active r Bool.≟ true) retire
senderMoves (state r (suc w) idle c q) =
  internalWhen (active r Bool.≟ true) claim
senderMoves _ = []

-- At most three hidden choices are enabled; no polling self-loops are added.
internalMoves : (s : State) → List (Internal s)
internalMoves s = readerMoves s ++ senderMoves s

-- Executable visible steps retain their independent Step certificate.
module Executable
  (notificationEq : Relation.Binary.Definitions.DecidableEquality Notification) where
  open import Relation.Binary.Definitions using (DecidableEquality)
  open import Relation.Nullary using (Dec; yes; no)
  open import Relation.Nullary.Decidable using (_×-dec_)
  open import Data.Empty using (⊥-elim)
  open import Data.Maybe using (map)

  -- Equality compares the payload already selected by the sender.
  replyEq : DecidableEquality Reply
  replyEq canceled canceled = yes refl
  replyEq canceled (normal _) = no λ ()
  replyEq (normal _) canceled = no λ ()
  replyEq (normal a) (normal b) with notificationEq a b
  ... | yes refl = yes refl
  ... | no neq = no λ { refl → neq refl }

  -- A successful guard packages the independently specified operational rule.
  checked : ∀ {p s a t} {P : Set} → Dec P → (P → Step p s a t) →
    Maybe (Σ[ u ∈ State ] Step p s a u)
  checked {t = t} (yes pr) build = just (t , build pr)
  checked (no _) _ = nothing

  -- Target computation does not depend on which evidence proved the guard.
  checked-target : ∀ {p s a t} {P : Set} (dec : Dec P)
    {build : P → Step p s a t} → P →
    map proj₁ (checked dec build) ≡ just t
  checked-target (yes _) _ = refl
  checked-target (no noP) pr = ⊥-elim (noP pr)

  -- Selection is guarded by the flag when the callback transaction runs.
  lookupNext : (p : Contract) (s : State) (m : Reply) →
    Maybe (Σ[ t ∈ State ] Step p s (nextReply m) t)
  lookupNext p (state r w claimed c false) m =
    checked ((active r Bool.≟ true) ×-dec (allowed p m Bool.≟ true))
      (λ { (ar , am) → choose ar am })
  lookupNext _ _ _ = nothing

  -- Sending compares against the previously selected payload.
  lookupSend : (p : Contract) (s : State) (m : Reply) →
    Maybe (Σ[ t ∈ State ] Step p s (sendReply m) t)
  lookupSend p (state r w (selected m) c q) m′ =
    checked ((active r Bool.≟ true) ×-dec replyEq m m′)
      (λ { (ar , refl) → send ar })
  lookupSend _ _ _ = nothing

  -- Lookup checks reader and sender independently rather than locking the peer.
  lookup : (p : Contract) (s : State) (a : Action) →
    Maybe (Σ[ t ∈ State ] Step p s a t)
  lookup p s (nextReply m) = lookupNext p s m
  lookup p s (sendReply m) = lookupSend p s m
  lookup p (state first w s c false) recvRequest = just (_ , receiveRequest atFirst)
  lookup p (state awaitNext w s c false) recvRequest = just (_ , receiveRequest atNext)
  lookup p (state first w s c false) recvQuit = just (_ , receiveQuit atFirst)
  lookup p (state awaitNext w s c false) recvQuit = just (_ , receiveQuit atNext)
  lookup p (state doneReady zero idle zero true) sendDone = just (_ , finish)
  lookup _ _ _ = nothing

  -- Erase only the lookup certificate, preserving the exact target state.
  next : Contract → State → Action → Maybe State
  next p s a = map proj₁ (lookup p s a)

  -- Every independent operational rule is implemented by the executable lookup.
  next-complete : ∀ {p s a t} → Step p s a t → next p s a ≡ just t
  next-complete (receiveRequest atFirst) = refl
  next-complete (receiveRequest atNext) = refl
  next-complete (receiveQuit atFirst) = refl
  next-complete (receiveQuit atNext) = refl
  next-complete {p = p} (choose {r = r} {m = m} ar am) =
    checked-target ((active r Bool.≟ true) ×-dec (allowed p m Bool.≟ true))
      (ar , am)
  next-complete (send {r = r} {m = m} ar) =
    checked-target ((active r Bool.≟ true) ×-dec replyEq m m)
      (ar , refl)
  next-complete finish = refl

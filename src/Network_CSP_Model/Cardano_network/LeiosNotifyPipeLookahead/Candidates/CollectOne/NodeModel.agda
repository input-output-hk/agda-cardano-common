{-# OPTIONS --safe #-}

-- CollectOne producer coupled to the pinned node's admission and notification queue.
-- Inputs are notifications already eligible under application/ledger/relay checks.
open import Data.Nat using (ℕ)
module Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.NodeModel
  (Notification : Set) (limit : ℕ) where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym)
import Cardano_network.LeiosNotifyPipeLookahead.Candidates.CollectOne.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification limit as Q

-- The callback queue and server's deferred jobs are different resources.
record State : Set where
  constructor node
  field
    peer : S.State
    queue : Q.State
open State public

-- Both parts have the initialization used by the pinned node.
initial : State
initial = node S.initial Q.initial

-- Sharing wire/eligibility data does not identify the independently specified node rules.
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification limit as Alphabet
open Alphabet public using (Wire; request; quit; reply; done; Action; wire; offer)

-- Visible transactions preserve exact queue data and local peer agency.
data Step : State → Action → State → Set where
  peerRecord : ∀ {s s′ q a} → Wire a → S.Step S.nodeNext s a s′ →
    Step (node s q) (wire a) (node s′ q)
  applicationOffer : ∀ {s q q′ m} → S.active (S.reader s) ≡ true →
    Q.Step q (Q.offer m) q′ → Step (node s q) (offer m) (node s q′)

-- Admission must be interpreted by the actual credit callback, not chosen freely.
routine : ∀ {s t} → S.Tau s t → Bool
routine S.admitted = false
routine S.excessive = false
routine _ = true

-- Atomic callback transactions update queue/accounting and peer state together.
data Tau : State → State → Set where
  schedule : ∀ {s s′ q} (pr : S.Tau s s′) → routine pr ≡ true →
    Tau (node s q) (node s′ q)
  admitAccepted : ∀ {w sender c flag q q′} → Q.Step q Q.admitAccepted q′ →
    Tau (node (S.state S.admit w sender c flag) q)
      (node (S.state S.inspect w sender c flag) q′)
  admitExcessive : ∀ {w sender c flag q q′} → Q.Step q Q.admitExcessive q′ →
    Tau (node (S.state S.admit w sender c flag) q)
      (node (S.state S.raising w sender c flag) q′)
  nextQueued : ∀ {s s′ q q′ m} → Q.Step q (Q.take m) q′ →
    S.Step S.nodeNext s (S.nextReply (S.normal m)) s′ →
    Tau (node s q) (node s′ q′)

-- Source schedules expose eligible offers and driver records without hiding either.
data Run : State → List Action → State → Set where
  stop : ∀ {s} → Run s [] s
  internal : ∀ {s t u es} → Tau s t → Run t es u → Run s es u
  visible : ∀ {s t u a es} → Step s a t → Run t es u → Run s (a ∷ es) u

-- Concatenate joint source schedules with their queue state intact.
append : ∀ {s t u es fs} → Run s es t → Run t fs u → Run s (es ++ fs) u
append stop q = q
append (internal st run) q = internal st (append run q)
append (visible st run) q = visible st (append run q)

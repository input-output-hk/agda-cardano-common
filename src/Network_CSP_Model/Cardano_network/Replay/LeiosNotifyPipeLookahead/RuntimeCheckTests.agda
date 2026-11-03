{-# OPTIONS --safe #-}

-- Negative controls for supplied hints, including node-policy bypass attempts.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeCheckTests where

open import Data.Bool using (true; false)
open import Data.Integer using (+_)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (nothing; just)
open import Data.Nat using (ℕ)
import Data.Nat.Properties as Nat
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model ℕ as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel ℕ ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel ℕ ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution ℕ ⊤ Nat._≟_ as DE
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel ℕ 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel ℕ as Node
open import Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeCheck ℕ Nat._≟_

-- No supplied continue hint can invent forecast readiness.
forecast-blocked : evaluate Node.initial (hidden continue ∷ []) ≡ nothing
forecast-blocked = refl

-- Generic successful callbacks cannot pass through the restricted transport selector.
callback-bypass : evaluate Node.initial
  (hidden (transport (DE.decide (C.continue (+ 1000)))) ∷ []) ≡ nothing
callback-bypass = refl

-- Admission requires an actual received request before its callback phase.
admission-before-request : hidden-step Node.initial accept ≡ nothing
admission-before-request = refl

-- Queue selection cannot manufacture an eligible notification.
empty-next : hidden-step Node.initial queued ≡ nothing
empty-next = refl

-- A record cannot complete a channel operation that has not committed.
uncommitted-record : visible-step Node.initial (Node.wire (D.clientSend D.request)) ≡ nothing
uncommitted-record = refl

-- Unavailable schedule indices fail instead of falling back to another operation.
bad-selector : hidden-step Node.initial (client 100) ≡ nothing
bad-selector = refl

-- This explicit partial state isolates FIFO checking without asserting fresh reachability.
queuedState : Node.State
queuedState = Node.nodeDriver
  (D.pair C.initial (S.state S.awaitNext 0 S.claimed 0 false) [] [] nothing nothing nothing nothing)
  (Q.credits 0 (7 ∷ 9 ∷ [])) true false false

-- Selection binds the exact head; a supplied send hint cannot skip to the second item.
skip-head : evaluate queuedState
  (hidden queued ∷ hidden (transport (DE.writeServer (D.reply (S.normal 9)))) ∷ []) ≡ nothing
skip-head = refl

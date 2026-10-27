{-# OPTIONS --guardedness #-}

-- Dynamic registration of success invocations; identities are never recycled.
module ConnectionManagement.Rules.OriginRegistry where

open import Data.Bool using (Bool; true; false; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.OriginMonitor as Single
open Single using (Target; target; workerId; handleId; Phase; awaitingAllocation)
open import ConnectionManagement.Rules.AttributedOrigin using (Action; allocate; dispatch; erase; ordinary)
import ConnectionManagement.Rules.AttributedOrigin as Attributed

record Entry : Set where
  constructor entry
  field targetId : Target
        phase : Phase
open Entry public

record State : Set where
  constructor registry
  field machine : Open.Configuration
        entries : List Entry
open State public

hasWorker : WorkerId → List Entry → Bool
hasWorker w [] = false
hasWorker w (e ∷ es) with w ≟ workerId (targetId e)
... | yes _ = true
... | no _ = hasWorker w es
hasHandle : HandleId → List Entry → Bool
hasHandle hid [] = false
hasHandle hid (e ∷ es) with hid ≟ handleId (targetId e)
... | yes _ = true
... | no _ = hasHandle hid es

-- Only publication and attachment require an already registered invocation.
requiredWorker : Open.Action → Maybe WorkerId
requiredWorker (Open.handlerPublication w _ _) = just w
requiredWorker (Open.handlerStep w (L.attach _)) = just w
requiredWorker _ = nothing

-- Allocate registers a fresh pair before the same event checks its captured key.
-- Publication and attachment require prior registration, including on empty lists.
-- ordinary rejects raw inbound and unsupported outbound allocation alike.
prepare : Action → List Entry → Maybe (List Entry)
prepare (allocate w hid mid k ps f) es with hasWorker w es ∨ hasHandle hid es
... | true = nothing
... | false = just (entry (target w hid) awaitingAllocation ∷ es)
prepare (dispatch a) es with ordinary a | requiredWorker a
... | false | _ = nothing
... | true | nothing = just es
... | true | just w with hasWorker w es
...   | false = nothing
...   | true = just es

-- Check every registered invocation against the same pre-action machine state.
-- Each accepted single monitor computes the same underlying machine transition.
drive : Action → Open.Configuration → List Entry → Maybe (List Entry)
drive a c [] = just []
drive a c (e ∷ es) with Attributed.step (targetId e) a (Single.observed c (phase e))
... | nothing = nothing
... | just s with drive a c es
...   | nothing = nothing
...   | just rest = just (entry (targetId e) (Single.phase s) ∷ rest)

-- Commit registration, phases and the machine endpoint atomically.
step : Action → State → Maybe State
step a (registry c es) with prepare a es
... | nothing = nothing
... | just ready with Open.advance (erase a) c
...   | nothing = nothing
...   | just c′ with drive a c ready
...     | nothing = nothing
...     | just es′ = just (registry c′ es′)

data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂

start : Open.Configuration → State
start c = registry c []

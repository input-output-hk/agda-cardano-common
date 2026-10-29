{-# OPTIONS --guardedness #-}

-- Selection of an ignored initiator trace retains the real source resources.
-- This is a finite-step safety statement, not a tracer progress assumption.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.MuxInitiatorTrace (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Properties.MuxDeltaQ as DeltaFacts
module Facts = DeltaFacts isBearerClosed
module D = Facts.D
module R = D.R
module Base = Facts.Base

-- Captured owner, startup PC and callback come from the existing selector.
fault-selection : ∀ w result s {plan} → D.initiatorFaultPlan w result s ≡ just plan →
  Base.Selection w result (λ _ _ → just R.poolBody) (D.base s) plan
fault-selection w result s eq with lookup w (D.tickets s)
... | nothing = case eq of λ ()
... | just t with D.phase t | D.initiatorReady w t s
...   | D.muxInvoked | true = Base.selection-observation w result (λ _ _ → just R.poolBody) (D.base s) eq
...   | D.muxInvoked | false = case eq of λ ()
...   | D.captured | _ = case eq of λ ()
...   | D.muxReturned | _ = case eq of λ ()
...   | D.invoked | _ = case eq of λ ()
...   | D.returned | _ = case eq of λ ()
...   | D.throwing | _ = case eq of λ ()

-- Observing a local exception does not manufacture source or pool cleanup.
throw-keeps-underlying : ∀ w result s {s′} → D.throwInitiator w result false s ≡ just s′ →
  R.base (D.base s′) ≡ R.base (D.base s)
throw-keeps-underlying w result s eq with D.initiatorFaultPlan w result s in planned
... | nothing = case eq of λ ()
... | just plan with fault-selection w result s planned
...   | selected rewrite Base.Selection.plan-shape selected = Facts.apply-local-keeps-underlying w _ s eq

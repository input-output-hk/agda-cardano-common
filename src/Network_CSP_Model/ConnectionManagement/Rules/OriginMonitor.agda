{-# OPTIONS --guardedness #-}

-- A single-invocation success-contract filter over the unchanged open machine.
-- The observer supplies the worker/handle association absent from installHandle.
module ConnectionManagement.Rules.OriginMonitor where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (Protocol; handlers; handlerKey; HandshakeResult; negotiated)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Machine as Open
open Open using (PublicationOutcome; resultWritten)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L

record Target : Set where
  constructor target
  field workerId : WorkerId
        handleId : HandleId
open Target public
record Ticket : Set where
  constructor ticket
  field muxId : MuxId
        protocols : List Protocol
        flow : DataFlow
open Ticket public

data Phase : Set where
  awaitingAllocation : Phase
  awaitingPublication published : Ticket → Phase
record State : Set where
  constructor observed
  field machine : Open.Configuration
        phase : Phase
open State public

-- Classification distinguishes this target from unrelated dispatcher actions.
data Event : Set where
  allocation : MuxId → ConnectionKey → List Protocol → DataFlow → Event
  publication : HandshakeResult → PublicationOutcome → Event
  attachment other : Event
classify : Target → Open.Action → Event
classify t (Open.igStep (IG.installHandle hid mid k ps f)) with hid ≟ handleId t
... | yes _ = allocation mid k ps f
... | no _ = other
classify t (Open.handlerPublication w r o) with w ≟ workerId t
... | yes _ = publication r o
... | no _ = other
classify t (Open.handlerStep w (L.attach err)) with w ≟ workerId t
... | yes _ = attachment
... | no _ = other
classify t _ = other

-- The branch covers successful negotiation only. Query/error/duplicate outcomes
-- for the target need separate profiles; they are not accepted as successes.
match-flow : DataFlow → DataFlow → Ticket → Maybe Phase
match-flow unidirectional unidirectional tk = just (published tk)
match-flow duplex duplex tk = just (published tk)
match-flow _ _ tk = nothing
check : Target → Event → State → Maybe Phase
check t (allocation mid k ps f) (observed c awaitingAllocation) with lookup (workerId t) (handlers (Open.world c))
... | nothing = nothing
... | just h with k ≟ handlerKey h
...   | yes _ = just (awaitingPublication (ticket mid ps f))
...   | no _ = nothing
check t (allocation _ _ _ _) _ = nothing
check t (publication (negotiated hid f) resultWritten) (observed c (awaitingPublication tk)) with hid ≟ handleId t
... | yes _ = match-flow f (flow tk) tk
... | no _ = nothing
check t (publication _ _) _ = nothing
check t attachment (observed c (published tk)) = just (published tk)
check t attachment _ = nothing
check t other s = just (phase s)

-- Commit monitor state only when the original dispatcher also succeeds.
step : Target → Open.Action → State → Maybe State
step t a s with check t (classify t a) s
... | nothing = nothing
... | just ph with Open.advance a (machine s)
...   | nothing = nothing
...   | just c′ = just (observed c′ ph)

data Executes (t : Target) : State → List Open.Action → State → Set where
  done : ∀ {s} → Executes t s [] s
  next : ∀ {s s₁ s₂ a as} → step t a s ≡ just s₁ → Executes t s₁ as s₂ → Executes t s (a ∷ as) s₂

-- Start a fresh observation; arbitrary pre-seeded phases are not certified.
start : Open.Configuration → State
start c = observed c awaitingAllocation

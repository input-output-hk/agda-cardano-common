{-# OPTIONS --guardedness #-}

-- Explicit inbound observer attribution; the tag is not source-ownership evidence.
module ConnectionManagement.Rules.AttributedOrigin where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (Protocol)
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Rules.OriginMonitor using (Target; State; workerId; handleId)
import ConnectionManagement.Rules.OriginMonitor as Single

-- Allocation carries the invoking worker. Other machine actions keep their shape.
data Action : Set where
  allocate : WorkerId → HandleId → MuxId → ConnectionKey → List Protocol → DataFlow → Action
  dispatch : Open.Action → Action

erase : Action → Open.Action
erase (allocate w hid mid k ps f) = Open.igStep (IG.installHandle hid mid k ps f)
erase (dispatch a) = a

-- Raw allocation cannot bypass attribution, even for an unrelated handle.
ordinary : Open.Action → Bool
ordinary (Open.igStep (IG.installHandle _ _ _ _ _)) = false
-- Outbound allocation has no attributed constructor in this inbound profile.
ordinary (Open.igStep (IG.installOutboundHandle _ _ _ _ _)) = false
ordinary _ = true

-- The selected worker and handle must occur together. Other pairs remain outside
-- the single-target contract, pending an explicit multi-worker registry.
attributed : Target → WorkerId → HandleId → Bool
attributed t w hid with w ≟ workerId t | hid ≟ handleId t
... | yes _ | yes _ = true
... | no _ | no _ = true
... | _ | _ = false
allowed : Target → Action → Bool
allowed t (allocate w hid mid k ps f) = attributed t w hid
allowed t (dispatch a) = ordinary a

-- Attribution and the original monitor must both accept before state changes.
step : Target → Action → State → Maybe State
step t a s with allowed t a
... | false = nothing
... | true = Single.step t (erase a) s

data Executes (t : Target) : State → List Action → State → Set where
  done : ∀ {s} → Executes t s [] s
  next : ∀ {s s₁ s₂ a as} → step t a s ≡ just s₁ → Executes t s₁ as s₂ → Executes t s (a ∷ as) s₂

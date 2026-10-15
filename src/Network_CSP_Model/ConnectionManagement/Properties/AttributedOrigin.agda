{-# OPTIONS --guardedness #-}

-- Erasure transports the existing monitor invariant without changing its scope.
module ConnectionManagement.Properties.AttributedOrigin where

import Data.Empty
open import Data.Bool using (true; false)
open import Data.List using (map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Function using (case_of_)
open import ConnectionManagement.Domain
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Rules.OriginMonitor using (Target; State; start; workerId; handleId)
import ConnectionManagement.Rules.OriginMonitor as Single
open import ConnectionManagement.Rules.AttributedOrigin
open import ConnectionManagement.Properties.HandlerResources using (Resources)
open import ConnectionManagement.Properties.OriginMonitorInvariant using (Invariant; reachable-invariant)

step-projects : ∀ t a s {s′} → step t a s ≡ just s′ → Single.step t (erase a) s ≡ just s′
step-projects t a s eq with allowed t a
... | false = case eq of λ ()
... | true = eq

exec-projects : ∀ {t s as s′} → Executes t s as s′ → Single.Executes t s (map erase as) s′
exec-projects done = Single.done
exec-projects (next {s = s} {a = a} eq rest) = Single.next (step-projects _ a s eq) (exec-projects rest)

-- A selected-handle allocation cannot be labelled as another worker's action.
selected-owner : ∀ t w mid k ps f s {s′} →
  step t (allocate w (handleId t) mid k ps f) s ≡ just s′ → w ≡ workerId t
selected-owner t w mid k ps f s eq with w ≟ workerId t | handleId t ≟ handleId t
... | yes same | yes _ = same
... | yes same | no _ = same
... | no _ | yes _ = case eq of λ ()
... | no _ | no neq = Data.Empty.⊥-elim (neq refl)

-- A selected worker likewise cannot allocate a different handle unnoticed.
selected-handle : ∀ t hid mid k ps f s {s′} →
  step t (allocate (workerId t) hid mid k ps f) s ≡ just s′ → hid ≡ handleId t
selected-handle t hid mid k ps f s eq with workerId t ≟ workerId t | hid ≟ handleId t
... | yes _ | yes same = same
... | no _ | yes same = same
... | yes _ | no _ = case eq of λ ()
... | no neq | no _ = Data.Empty.⊥-elim (neq refl)

-- Resources remain an initial premise; attribution adds no source identity axiom.
reachable : ∀ {t c as s′} → Executes t (start c) as s′ →
  Resources (workerId t) (Open.world c) → Invariant t s′
reachable path = reachable-invariant (exec-projects path)

-- No target or monitor phase permits an unlabelled allocation through dispatch.
raw-allocation-refused : ∀ t hid mid k ps f s →
  step t (dispatch (Open.igStep (IG.installHandle hid mid k ps f))) s ≡ nothing
raw-allocation-refused t hid mid k ps f s = refl

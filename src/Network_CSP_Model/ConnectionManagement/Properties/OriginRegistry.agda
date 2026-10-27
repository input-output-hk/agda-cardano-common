{-# OPTIONS --guardedness #-}

-- All registered invocations retain resources and exact ticket descriptors.
module ConnectionManagement.Properties.OriginRegistry where

open import Data.Bool using (true; false; _∨_)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Relation.Unary.All using (All; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym)
open import Function using (case_of_)
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.OriginMonitor as Single
open import ConnectionManagement.Rules.AttributedOrigin using (Action; allocate; dispatch; erase; ordinary)
import ConnectionManagement.Rules.AttributedOrigin as Attributed
import ConnectionManagement.Properties.AttributedOrigin as AP
import ConnectionManagement.Properties.OriginMonitor as SP
import ConnectionManagement.Properties.OriginMonitorInvariant as SI
open import ConnectionManagement.Properties.HandlerResources using (Resources)
open import ConnectionManagement.Rules.OriginRegistry

-- New allocations require evidence for their invoking worker at that point.
-- This proof premise is not an executable resource check or source attribution.
Evidence : Action → Open.Configuration → Set
Evidence (allocate w _ _ _ _ _) c = Resources w (Open.world c)
Evidence (dispatch _) c = ⊤

Certified : Open.Configuration → List Entry → Set
Certified c es = All (λ e → SI.Invariant (targetId e) (Single.observed c (phase e))) es
Invariant : State → Set
Invariant s = Certified (machine s) (entries s)

prepare-certified : ∀ a c es {ready} → prepare a es ≡ just ready →
  Evidence a c → Certified c es → Certified c ready
prepare-certified (allocate w hid mid k ps f) c es eq evidence inv with hasWorker w es ∨ hasHandle hid es
... | true = case eq of λ ()
... | false with just-injective eq
...   | refl = (evidence , tt) ∷ inv
prepare-certified (dispatch a) c es eq evidence inv with ordinary a | requiredWorker a
... | false | _ = case eq of λ ()
... | true | nothing with just-injective eq
...   | refl = inv
prepare-certified (dispatch a) c es eq evidence inv | true | just w with hasWorker w es
... | false = case eq of λ ()
... | true with just-injective eq
...   | refl = inv

-- All local monitors share the same machine endpoint by deterministic erasure.
drive-certified : ∀ a c {c′} es {es′} → Open.advance (erase a) c ≡ just c′ →
  drive a c es ≡ just es′ → Certified c es → Certified c′ es′
drive-certified a c [] advanced eq [] with just-injective eq
... | refl = []
drive-certified a c (e ∷ es) advanced eq (inv ∷ invs)
  with Attributed.step (targetId e) a (Single.observed c (phase e)) in stepped
... | nothing = case eq of λ ()
... | just s with drive a c es in driven
...   | nothing = case eq of λ ()
...   | just rest with just-injective eq
...     | refl with just-injective (trans (sym (SP.step-projects (targetId e) (erase a)
    (Single.observed c (phase e)) (AP.step-projects (targetId e) a (Single.observed c (phase e)) stepped))) advanced)
...       | refl = SI.invariant-step (targetId e) (erase a) (Single.observed c (phase e))
    (AP.step-projects (targetId e) a (Single.observed c (phase e)) stepped) inv ∷
    drive-certified a c es advanced driven invs

step-projects : ∀ a s {s′} → step a s ≡ just s′ → Open.advance (erase a) (machine s) ≡ just (machine s′)
step-projects a (registry c es) eq with prepare a es
... | nothing = case eq of λ ()
... | just ready with Open.advance (erase a) c
...   | nothing = case eq of λ ()
...   | just c′ with drive a c ready
...     | nothing = case eq of λ ()
...     | just es′ with just-injective eq
...       | refl = refl

invariant-step : ∀ a s {s′} → step a s ≡ just s′ → Evidence a (machine s) → Invariant s → Invariant s′
invariant-step a (registry c es) eq evidence inv with prepare a es in prepared
... | nothing = case eq of λ ()
... | just ready with Open.advance (erase a) c in advanced
...   | nothing = case eq of λ ()
...   | just c′ with drive a c ready in driven
...     | nothing = case eq of λ ()
...     | just es′ with just-injective eq
...       | refl = drive-certified a c ready advanced driven (prepare-certified a c es prepared evidence inv)

exec-projects : ∀ {s as s′} → Executes s as s′ → Open.Executes (machine s) (map erase as) (machine s′)
exec-projects done = Open.done
exec-projects (next {s = s} {a = a} eq path) = Open.next (step-projects a s eq) (exec-projects path)

-- Evidence accompanies each newly registered invocation, including later forks.
data Supported : ∀ {s as s′} → Executes s as s′ → Set where
  done : ∀ {s} → Supported (done {s})
  next : ∀ {s s₁ s₂ a as} {eq : step a s ≡ just s₁} {path : Executes s₁ as s₂} →
    Evidence a (machine s) → Supported path → Supported (ConnectionManagement.Rules.OriginRegistry.next {s = s} {a = a} eq path)

invariant-exec : ∀ {s as s′} (path : Executes s as s′) → Supported path → Invariant s → Invariant s′
invariant-exec done done inv = inv
invariant-exec (next {s = s} {a = a} eq path) (next evidence supported) inv =
  invariant-exec path supported (invariant-step a s eq evidence inv)

reachable : ∀ {c as s′} (path : Executes (start c) as s′) → Supported path → Invariant s′
reachable path supported = invariant-exec path supported []

-- Outbound allocation is outside the registry's attributed inbound profile,
-- regardless of its current entries or the selected handle identity.
raw-outbound-allocation-refused : ∀ hid mid k ps f s →
  step (dispatch (Open.igStep (IG.installOutboundHandle hid mid k ps f))) s ≡ nothing
raw-outbound-allocation-refused hid mid k ps f (registry c es) = refl

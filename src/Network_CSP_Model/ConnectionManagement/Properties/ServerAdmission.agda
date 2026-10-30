{-# OPTIONS --guardedness #-}

-- Owned Server cleanup does not cancel/join its raw admission Asyncs. The
-- statement covers finite scope interleavings, including actual IG writes.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.ServerAdmission (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; map)
import Data.List.Relation.Unary.All as All
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)
open import Function using (case_of_)
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.MuxPublicationUnwind as Publication
private
  module S = Server isBearerClosed
  module N = Publication isBearerClosed

enact-preserves-workers : ∀ p s {t} → S.enactScope p s ≡ just t → S.workers t ≡ S.workers s
enact-preserves-workers p s eq with S.physicalAction p
... | nothing = cong S.workers (sym (just-injective eq))
... | just a with N.step a (S.base s)
...   | nothing = case eq of λ ()
...   | just n = cong S.workers (sym (just-injective eq))
scope-preserves-workers : ∀ a s {t} → S.scopeAdvance a s ≡ just t → S.workers t ≡ S.workers s
scope-preserves-workers a s eq with S.chooseScope a s
... | nothing = case eq of λ ()
... | just p = enact-preserves-workers p s eq

data ScopeOnly : S.Action → Set where
  owned : ∀ a → ScopeOnly (S.scope a)

-- Other actors may independently finish workers, so the action premise is
-- explicit: a scope-only run itself supplies no admission-result certificate.
scopes-retain-workers : ∀ {s as t} → All.All ScopeOnly as → S.Executes s as t → S.workers t ≡ S.workers s
scopes-retain-workers All.[] S.done = refl
scopes-retain-workers (owned a All.∷ kinds) (S.next {s = s} eq rest) =
  trans (scopes-retain-workers kinds rest) (scope-preserves-workers a s eq)

inherit-preserves-workers : ∀ a s {t} → S.inherit a s ≡ just t → S.workers t ≡ S.workers s
inherit-preserves-workers a s eq with S.allowed a s
... | false = case eq of λ ()
... | true with N.step a (S.base s)
...   | nothing = case eq of λ ()
...   | just n = cong S.workers (sym (just-injective eq))

-- Reuse already checked physical executions without normalizing their whole
-- dispatchers again. Permission is checked separately for each actual label.
lift-step : ∀ a n n′ ts st listener →
  S.allowed a (S.serverState n ts st listener) ≡ true → N.step a n ≡ just n′ →
  S.step (S.run a) (S.serverState n ts st listener) ≡ just (S.serverState n′ ts st listener)
lift-step a n n′ ts st listener allowed advanced rewrite allowed | advanced = refl
lift-run : ∀ {n as n′} ts st listener →
  All.All (λ a → ∀ current → S.allowed a (S.serverState current ts st listener) ≡ true) as →
  N.Executes n as n′ → S.Executes (S.serverState n ts st listener) (map S.run as) (S.serverState n′ ts st listener)
lift-run ts st listener All.[] N.done = S.done
lift-run ts st listener (permitted All.∷ permissions) (N.next {s = n} {s₁ = next} {a = a} eq rest) =
  S.next (lift-step a n next ts st listener (permitted n) eq) (lift-run ts st listener permissions rest)

-- The guarded raw-machine path is exactly the path used by the public builder.
machine-action-roundtrip : ∀ a → S.machineAction (S.runMachine a) ≡ just a
machine-action-roundtrip a = refl

{-# OPTIONS --guardedness #-}

-- Pre-attachment preservation for caller publication/counters and all handshake
-- consumers. Actor identities are unrestricted; coverage remains explicit.
module ConnectionManagement.Properties.HandlerInterference where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; sym; cong; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Entries using (Present)
open import ConnectionManagement.Properties.HandlerResources
open import ConnectionManagement.Properties.HandlerEstablishment using (Prepared)
open import ConnectionManagement.Properties.HandlerReferences using (Chain)
open import ConnectionManagement.Properties.HandlerHandshake using (from-effect)
open import ConnectionManagement.Properties.HandlerConsumerEffects
import ConnectionManagement.Rules.Server as S
import ConnectionManagement.Rules.Handshake as H
import ConnectionManagement.Rules.IGRegistration as IG

-- The original handler value is unchanged, so installation keys stay tied to it.
resources-effect : ∀ {w s s′} → Effect s s′ → Resources w s → Resources w s′
resources-effect eff r = record
  { original = original r
  ; found = trans (cong (lookup _) (handlersSame eff)) (found r)
  ; entryExists = entriesRetained eff _ (entryExists r)
  ; socketExists = subst (Present _) (sym (socketsSame eff)) (socketExists r) }

prepared-effect : ∀ {w hid mid s s′ ig} → Effect s s′ →
  Prepared w hid mid s ig → Prepared w hid mid s′ ig
prepared-effect eff p = record
  { resources = resources-effect eff (Prepared.resources p)
  ; hd = Prepared.hd p; mx = Prepared.mx p
  ; handleFound = Prepared.handleFound p; handleMux = Prepared.handleMux p
  ; muxFound = Prepared.muxFound p; keyMatches = Prepared.keyMatches p }

data Covered : Action → Set where
  parent : ∀ {w a} → ParentAction a → Covered (admissionStep w a)
  consumer : ∀ {w a} → Covered (handshakeStep w a)

-- Both action families update only the world, leaving the IG engine intact.
step-effect : ∀ a → Covered a → ∀ c {c′} → advance a c ≡ just c′ →
  Effect (world c) (world c′) × (inboundGovernor c′ ≡ inboundGovernor c)
step-effect .(admissionStep w a) (parent {w} {a} covered) c eq with lookup w (admissions (world c))
... | nothing = case eq of λ ()
... | just a₀ with S.stepWorker w a₀ a (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ with just-injective eq
...     | refl = parent-worker a covered w a₀ (world c) stepped , refl
step-effect .(handshakeStep w a) (consumer {w} {a}) c eq with lookup w (admissions (world c))
... | nothing = case eq of λ ()
... | just a₀ with H.stepWorker (responder c) w a₀ a (world c) in stepped
...   | nothing = case eq of λ ()
...   | just s′ with just-injective eq
...     | refl = worker-effect a (responder c) w a₀ (world c) stepped , refl

resources-step : ∀ a → Covered a → ∀ c {c′ w} → advance a c ≡ just c′ →
  Resources w (world c) → Resources w (world c′)
resources-step a covered c eq = resources-effect (proj₁ (step-effect a covered c eq))

prepared-step : ∀ a → Covered a → ∀ c {c′ w hid mid} → advance a c ≡ just c′ →
  Prepared w hid mid (world c) (inboundGovernor c) → Prepared w hid mid (world c′) (inboundGovernor c′)
prepared-step a covered c eq p with step-effect a covered c eq
... | eff , refl = prepared-effect eff p

chain-step : ∀ a → Covered a → ∀ c {c′ w mid} → advance a c ≡ just c′ →
  Chain w mid (world c) (inboundGovernor c) → Chain w mid (world c′) (inboundGovernor c′)
chain-step a covered c eq ch with step-effect a covered c eq
... | eff , refl = from-effect eff ch

-- No promise, publication availability or lifecycle frame is required here.
data Interference : List Action → Set where
  empty : Interference []
  more : ∀ {a as} → Covered a → Interference as → Interference (a ∷ as)

resources-exec : ∀ {c as c′ w} → Interference as → Executes c as c′ →
  Resources w (world c) → Resources w (world c′)
resources-exec empty done r = r
resources-exec (more {a} covered rest) (next {c = c} eq path) r =
  resources-exec rest path (resources-step a covered c eq r)

prepared-exec : ∀ {c as c′ w hid mid} → Interference as → Executes c as c′ →
  Prepared w hid mid (world c) (inboundGovernor c) → Prepared w hid mid (world c′) (inboundGovernor c′)
prepared-exec empty done p = p
prepared-exec (more {a} covered rest) (next {c = c} eq path) p =
  prepared-exec rest path (prepared-step a covered c eq p)

chain-exec : ∀ {c as c′ w mid} → Interference as → Executes c as c′ →
  Chain w mid (world c) (inboundGovernor c) → Chain w mid (world c′) (inboundGovernor c′)
chain-exec empty done ch = ch
chain-exec (more {a} covered rest) (next {c = c} eq path) ch =
  chain-exec rest path (chain-step a covered c eq ch)

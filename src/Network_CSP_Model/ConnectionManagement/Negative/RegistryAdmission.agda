{-# OPTIONS --guardedness #-}

-- Ownership substitution is refused after real model admissions and allocations.
module ConnectionManagement.Negative.RegistryAdmission where

open import Data.List using ([]; _∷_; _++_; map; take)
open import Data.Maybe using (nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Process_Trees
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
open import ConnectionManagement.Rules.AttributedOrigin using (Action; dispatch)
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.CSP.OriginRegistry
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import ConnectionManagement.CSP.RegistryAdmission
open import ConnectionManagement.Scenarios.Admission using (child₀)
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)
import ConnectionManagement.Negative.OriginRegistry

swap : Action
swap = dispatch (Open.handlerPublication child₀ (S.negotiated (ident 1) duplex) Open.resultWritten)
swap-refused : step swap s16 ≡ nothing
swap-refused = refl
no-swap-after-admissions : ¬ traces (Process s0) (map label (take 16 schedule ++ (swap ∷ [])))
no-swap-after-admissions = refused-extension allocation-prefix swap-refused

-- The first invocation cannot be allocated a second time after the second fork.
repeat-refused : step allocation₁ s15 ≡ nothing
repeat-refused = refl
no-repeat-after-second-admission : ¬ traces (Process s0) (map label (take 15 schedule ++ (allocation₁ ∷ [])))
no-repeat-after-second-admission = refused-extension second-admission-prefix repeat-refused

{-# OPTIONS --guardedness #-}

-- Atomic frontend source effects retain the exact primitive computation of
-- each origin-creating writer. There is no unbounded composition constructor.
module ConnectionManagement.Properties.InboundOriginEffect where

open import Data.Bool using (false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Function using (case_of_)
open import ConnectionManagement.Domain using (WorkerId)
open import ConnectionManagement.Store using (put)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Properties.InboundOriginCore as Core

-- Creation tags identify one actual source operation at these exact endpoints.
Source : ∀ {before after : M.Configuration} → Core.Change (M.world before) (M.world after) → Set
Source (Core.same unchanged) = ⊤
Source (Core.reset worker row outside changed) = ⊤
Source {before} {after} (Core.allocated worker request saved owned changed) =
  M.advance (M.admissionStep worker Admission.allocatePromise) before ≡ just after
Source {before} {after} (Core.selected worker request saved promise entry owned changed) =
  M.advance (M.admissionStep worker Admission.chooseEntry) before ≡ just after

record Effect (before after : M.Configuration) : Set where
 constructor effect
 field
  change : Core.Change (M.world before) (M.world after)
  source : Source {before} {after} change
open Effect public

-- Foreign metadata and non-origin continuations need no primitive equation.
same : ∀ {before after} → S.admissions (M.world after) ≡ S.admissions (M.world before) → Effect before after
same unchanged = effect (Core.same unchanged) tt
reset : ∀ {before after} worker row → Core.relevant (S.pc row) ≡ false →
  S.admissions (M.world after) ≡ put worker row (S.admissions (M.world before)) → Effect before after
reset worker row outside changed = effect (Core.reset worker row outside changed) tt

-- Framing uses actual core equalities, including wrapper-only bookkeeping.
reframe : ∀ {before after nextBefore nextAfter} → nextBefore ≡ before → nextAfter ≡ after →
  Effect before after → Effect nextBefore nextAfter
reframe refl refl observed = observed

private
 machine-source : ∀ action before {after} (actual : M.advance action before ≡ just after)
   (changed : Core.Change (M.world before) (M.world after)) → Core.Cause action changed → Source {before} {after} changed
 machine-source action before actual (Core.same unchanged) cause = tt
 machine-source action before actual (Core.reset worker row outside changed) cause = tt
 machine-source action before actual (Core.allocated worker request saved owned changed) cause =
   trans (cong (λ selected → M.advance selected before) (sym cause)) actual
 machine-source action before actual (Core.selected worker request saved promise entry owned changed) cause =
   trans (cong (λ selected → M.advance selected before) (sym cause)) actual

 -- An actual inbound outbound-machine call invokes exactly this primitive.
 inbound-source : ∀ action before {after} → O.advance (O.inbound action) before ≡ just after →
   M.advance action (O.core before) ≡ just (O.core after)
 inbound-source action before actual with M.advance action (O.core before) in stepped
 ... | nothing = case actual of λ ()
 ... | just next = case just-injective actual of λ { refl → refl }

 outbound-source : ∀ action before {after} (actual : O.advance action before ≡ just after)
   (changed : Core.Change (M.world (O.core before)) (M.world (O.core after))) →
   Core.OutboundCause action changed → Source {O.core before} {O.core after} changed
 outbound-source action before actual (Core.same unchanged) cause = tt
 outbound-source action before actual (Core.reset worker row outside changed) cause = tt
 outbound-source action before actual (Core.allocated worker request saved owned changed) cause =
   inbound-source (M.admissionStep worker Admission.allocatePromise) before
     (trans (cong (λ selected → O.advance selected before) (sym cause)) actual)
 outbound-source action before actual (Core.selected worker request saved promise entry owned changed) cause =
   inbound-source (M.admissionStep worker Admission.chooseEntry) before
     (trans (cong (λ selected → O.advance selected before) (sym cause)) actual)

-- Source classification supplies both the atomic tag and its exact cause.
machine-effect : ∀ action before {after} → M.advance action before ≡ just after → Effect before after
machine-effect action before actual = effect (Core.machine-effect action before actual)
  (machine-source action before actual (Core.machine-effect action before actual) (Core.machine-cause action before actual))
outbound-effect : ∀ action before {after} → O.advance action before ≡ just after → Effect (O.core before) (O.core after)
outbound-effect action before actual = effect (Core.outbound-effect action before actual)
  (outbound-source action before actual (Core.outbound-effect action before actual) (Core.outbound-cause action before actual))

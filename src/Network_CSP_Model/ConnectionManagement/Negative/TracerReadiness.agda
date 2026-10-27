{-# OPTIONS --guardedness #-}

-- Pure readiness/source-order controls. These do not assert that commitTracer
-- uses the helper: dispatcher integration and its regressions are separate.
module ConnectionManagement.Negative.TracerReadiness where

open import Data.Bool using (true; false)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes
open import ConnectionManagement.Rules.TracerReadiness using (prefixReady)
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.InformationChannel as Channel
open import ConnectionManagement.Scenarios.Admission using (key₀)

-- Empty descriptor maps model a same-key replacement missing the traced number.
missingView expiredMissingView : M.View
missingView = M.view (ident 0) [] duplex false
expiredMissingView = M.view (ident 0) [] duplex true
zeroCounters nonzeroCounters : M.Counters
zeroCounters = M.counters (+ 0) (+ 0)
nonzeroCounters = M.counters (+ 1) (+ 0)
fullQueue almostFullQueue : List IGEvent
fullQueue = replicate Channel.capacity (muxFinished key₀)
almostFullQueue = replicate 99 (muxFinished key₀)

-- Expiry precedes descriptor inspection even with space and a missing number.
expired-start-prefix-blocked : prefixReady key₀ (M.started 99)
  (just expiredMissingView) (just zeroCounters) [] ≡ false
expired-start-prefix-blocked = refl

-- A full initial AwakeRemote blocks before any missing-descriptor exception.
full-awake-prefix-blocked : prefixReady key₀ (M.started 99)
  (just missingView) (just zeroCounters) fullQueue ≡ false
full-awake-prefix-blocked = refl

-- Once that preliminary write could succeed, descriptor classification may run.
drained-prefix-ready : prefixReady key₀ (M.started 99)
  (just missingView) (just zeroCounters) [] ≡ true
drained-prefix-ready = refl
one-slot-prefix-ready : prefixReady key₀ (M.started 99)
  (just missingView) (just zeroCounters) almostFullQueue ≡ true
one-slot-prefix-ready = refl

-- Nonzero counters skip AwakeRemote, so full capacity does not defer the fault.
nonzero-prefix-ready : prefixReady key₀ (M.started 99)
  (just missingView) (just nonzeroCounters) fullQueue ≡ true
nonzero-prefix-ready = refl

-- Both clean/error completion payloads force their strict descriptor before a
-- queue write; RemoteIdle expiry is not a completion-tracer retry condition.
clean-completion-prefix-ready : prefixReady key₀ (M.completed 99 clean)
  (just expiredMissingView) (just zeroCounters) fullQueue ≡ true
clean-completion-prefix-ready = refl
error-completion-prefix-ready : prefixReady key₀ (M.completed 99 (errored (errorId 0)))
  (just expiredMissingView) (just zeroCounters) fullQueue ≡ true
error-completion-prefix-ready = refl

-- Missing registration/counters follow the existing counter-clearing branch.
no-registration-prefix-ready : prefixReady key₀ (M.started 99)
  nothing (just zeroCounters) fullQueue ≡ true
no-registration-prefix-ready = refl
no-counters-prefix-ready : prefixReady key₀ (M.started 99)
  (just expiredMissingView) nothing fullQueue ≡ true
no-counters-prefix-ready = refl

-- Prefix readiness is not readiness of the final atomic tracer transaction.
-- A last-slot AwakeRemote would fit, but this hot start needs two messages.
hotView : M.View
hotView = M.view (ident 0) (protocol 1 hot onDemand ∷ []) duplex false
hot-burst-retries : M.traceSTM key₀ (M.started 1)
  (just hotView) (just zeroCounters) almostFullQueue ≡ nothing
hot-burst-retries = refl
hot-burst-and-counters-commit : M.traceSTM key₀ (M.started 1)
  (just hotView) (just zeroCounters) [] ≡
  just (just (M.counters (+ 1) (+ 0)) , awakeRemote key₀ ∷ remotePromotedToHot key₀ ∷ [])
hot-burst-and-counters-commit = refl

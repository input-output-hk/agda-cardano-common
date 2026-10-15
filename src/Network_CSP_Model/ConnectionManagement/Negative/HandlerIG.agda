{-# OPTIONS --guardedness #-}

-- Reference preservation does not bypass event-loop phase and readiness guards.
module ConnectionManagement.Negative.HandlerIG where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerLifecycle using (tracked)
open import ConnectionManagement.CSP.HandlerIG using (exitEnd)
import ConnectionManagement.CSP.IGRuntime as Runtime
import ConnectionManagement.Rules.HandlerLifecycle as L
import ConnectionManagement.Rules.IGRegistration as IG
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

backward-clock-refused : advance (igStep (IG.captureTime 9)) (tracked L.monitoring Runtime.m₀) ≡ nothing
backward-clock-refused = refl
no-backward-clock-trace : ¬ traces (Process (tracked L.monitoring Runtime.m₀)) (map label (igStep (IG.captureTime 9) ∷ []))
no-backward-clock-trace = refused-extension {as = []} done backward-clock-refused

running-mux-refused : advance (igStep (IG.pollStopped)) (tracked L.monitoring Runtime.waitingForMux) ≡ nothing
running-mux-refused = refl
no-running-mux-trace : ¬ traces (Process (tracked L.monitoring Runtime.waitingForMux)) (map label (igStep (IG.pollStopped) ∷ []))
no-running-mux-trace = refused-extension {as = []} done running-mux-refused

repeat-deactivation-refused : advance (igStep (IG.deactivateIG)) (tracked L.monitoring Runtime.exiting) ≡ nothing
repeat-deactivation-refused = refl
no-repeat-deactivation-trace : ¬ traces (Process (tracked L.monitoring Runtime.exiting)) (map label (igStep (IG.deactivateIG) ∷ []))
no-repeat-deactivation-trace = refused-extension {as = []} done repeat-deactivation-refused

repeat-flush-refused : advance (igStep (IG.flushOnExit)) (exitEnd) ≡ nothing
repeat-flush-refused = refl
no-repeat-flush-trace : ¬ traces (Process (exitEnd)) (map label (igStep (IG.flushOnExit) ∷ []))
no-repeat-flush-trace = refused-extension {as = []} done repeat-flush-refused

unconsumed-batch-refused : advance (igStep (IG.finishBatch)) (tracked L.monitoring Runtime.m₃) ≡ nothing
unconsumed-batch-refused = refl
no-unconsumed-batch-trace : ¬ traces (Process (tracked L.monitoring Runtime.m₃)) (map label (igStep (IG.finishBatch) ∷ []))
no-unconsumed-batch-trace = refused-extension {as = []} done unconsumed-batch-refused


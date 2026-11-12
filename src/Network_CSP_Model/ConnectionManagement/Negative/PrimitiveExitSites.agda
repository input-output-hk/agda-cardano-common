{-# OPTIONS --guardedness #-}

-- G1 local classifier of blocked post-mux operations. Existing initialized
-- Negative/MuxExitCancellation histories supply actual dispatch witnesses.
-- A pure classification stage is not a provider, tracer or throwTo receipt.
module ConnectionManagement.Negative.PrimitiveExitSites where

open import Data.Bool using (false)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.MuxExitCancellation as Cancellation
import ConnectionManagement.MuxHandlerExit as Exit
module X = Cancellation (λ _ → false)
module W = Exit (λ _ → false)

buffer-enabled : ∀ e out → X.target X.bufferBlock e (W.bufferScope out) ≡ just (W.bufferScope (W.G.asyncExit e))
buffer-enabled e out = refl
buffer-wrong-phase-refused : ∀ e old → X.target X.bufferBlock e (W.classifying old) ≡ nothing
buffer-wrong-phase-refused e old = refl
trace-enabled : ∀ e old cmd → X.target X.errorTraceBlock e (W.errorTracing old cmd) ≡ just (W.bodyExited (W.asyncException e))
trace-enabled e old cmd = refl
trace-wrong-phase-refused : ∀ e old → X.target X.errorTraceBlock e (W.classifying old) ≡ nothing
trace-wrong-phase-refused e old = refl
send-enabled : ∀ e old → X.target X.nodeSendBlock e (W.nodeDelivery old) ≡ just (W.bodyExited (W.asyncException e))
send-enabled e old = refl
send-before-policy-refused : ∀ e old → X.target X.nodeSendBlock e (W.classifying old) ≡ nothing
send-before-policy-refused e old = refl

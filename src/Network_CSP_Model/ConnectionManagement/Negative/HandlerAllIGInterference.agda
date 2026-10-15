{-# OPTIONS --guardedness #-}

-- Pre-attachment evidence does not bypass either freshness or phase guards.
module ConnectionManagement.Negative.HandlerAllIGInterference where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerAllIGInterference
import ConnectionManagement.CSP.HandlerInterference as Caller
import ConnectionManagement.CSP.HandlerIGBoundary as Boundary
import ConnectionManagement.CSP.IGRegistration as G
open import ConnectionManagement.Scenarios.Admission using (key₁)
import ConnectionManagement.Rules.IGRegistration as IG
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

occupiedHandle occupiedMux : Action
occupiedHandle = igStep (IG.installHandle (ident 0) Boundary.newMux key₁ (G.proto ∷ []) duplex)
occupiedMux = igStep (IG.installHandle Boundary.newHandle G.mid key₁ (G.proto ∷ []) duplex)
handle-refused : advance occupiedHandle Caller.waiting ≡ nothing
handle-refused = refl
mux-refused : advance occupiedMux Caller.waiting ≡ nothing
mux-refused = refl
no-handle-overwrite : ¬ traces (Process Caller.waiting) (map label (occupiedHandle ∷ []))
no-handle-overwrite = refused-extension {as = []} done handle-refused
no-mux-overwrite : ¬ traces (Process Caller.waiting) (map label (occupiedMux ∷ []))
no-mux-overwrite = refused-extension {as = []} done mux-refused
second-decision-refused : advance (igStep IG.commitDecision) decisionOutput ≡ nothing
second-decision-refused = refl
no-second-decision : ¬ traces (Process decisionOutput) (map label (igStep IG.commitDecision ∷ []))
no-second-decision = refused-extension {as = []} done second-decision-refused

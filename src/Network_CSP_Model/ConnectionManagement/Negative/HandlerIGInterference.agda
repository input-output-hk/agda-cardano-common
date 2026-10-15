{-# OPTIONS --guardedness #-}

-- Successful reference retention does not make a stale clock sample executable.
module ConnectionManagement.Negative.HandlerIGInterference where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerIGInterference
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.Rules.IGRegistration as IG
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- Finish the batch first, so refusal is caused by the monotonic-time guard.
nextSample : Configuration
nextSample = record G.registered { inboundGovernor = IG.setPC IG.sampleTime (inboundGovernor G.registered) }
finish-path : Executes G.registered (igStep IG.finishBatch ∷ []) nextSample
finish-path = next refl done
stale-time-refused : advance (igStep (IG.captureTime 9)) nextSample ≡ nothing
stale-time-refused = refl
no-stale-sample : ¬ traces (Process G.registered)
  (map label (igStep IG.finishBatch ∷ igStep (IG.captureTime 9) ∷ []))
no-stale-sample = refused-extension finish-path stale-time-refused

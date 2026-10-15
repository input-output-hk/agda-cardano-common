{-# OPTIONS --guardedness #-}

-- Unrestricted preservation neither overwrites a result nor creates tracking.
module ConnectionManagement.Negative.HandlerDispatcherInterference where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.State using (query)
open import ConnectionManagement.Domain
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.HandlerReferences using (TrackedChain)
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerDispatcherInterference
import ConnectionManagement.Negative.HandlerAll as Earlier
open import ConnectionManagement.Scenarios.Admission using (w₁; child₀)
import ConnectionManagement.Rules.Server as S
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

occupied-child-refused : advance (admissionStep w₁ S.fork) (untracked Earlier.reusedChild) ≡ nothing
occupied-child-refused = refl
no-occupied-child : ¬ traces (Process (untracked Earlier.reusedChild)) (map label (admissionStep w₁ S.fork ∷ []))
no-occupied-child = refused-extension {as = []} done occupied-child-refused
no-implicit-tracking : ¬ TrackedChain child₀ secondEnd
no-implicit-tracking (f , () , ch)
overwrite-refused : advance (handlerPublication child₀ query resultWritten) secondEnd ≡ nothing
overwrite-refused = refl
no-result-overwrite : ¬ traces (Process secondEnd) (map label (handlerPublication child₀ query resultWritten ∷ []))
no-result-overwrite = refused-extension {as = []} done overwrite-refused
faulted-retry-refused : advance (handlerPublication child₀ query duplicateWrite) faulted ≡ nothing
faulted-retry-refused = refl
no-faulted-retry : ¬ traces (Process faulted) (map label (handlerPublication child₀ query duplicateWrite ∷ []))
no-faulted-retry = refused-extension {as = []} done faulted-retry-refused

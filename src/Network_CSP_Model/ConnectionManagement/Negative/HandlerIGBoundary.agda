{-# OPTIONS --guardedness #-}

-- Both allocation identities must be fresh; publication remains phase guarded.
module ConnectionManagement.Negative.HandlerIGBoundary where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerAttachment using (newlyAttached)
open import ConnectionManagement.CSP.HandlerIGBoundary using (newHandle; newMux; unregistered)
open import ConnectionManagement.CSP.IGRegistration using (proto; mid)
open import ConnectionManagement.Scenarios.Admission using (key₁)
import ConnectionManagement.Rules.IGRegistration as IG
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

occupiedHandle occupiedMux : Action
occupiedHandle = igStep (IG.installHandle (ident 0) newMux key₁ (proto ∷ []) duplex)
occupiedMux = igStep (IG.installHandle newHandle mid key₁ (proto ∷ []) duplex)
handle-overwrite-refused : advance occupiedHandle newlyAttached ≡ nothing
handle-overwrite-refused = refl
mux-overwrite-refused : advance occupiedMux newlyAttached ≡ nothing
mux-overwrite-refused = refl
second-publication-refused : advance (igStep IG.commitDecision) unregistered ≡ nothing
second-publication-refused = refl

no-handle-overwrite : ¬ traces (Process newlyAttached) (map label (occupiedHandle ∷ []))
no-handle-overwrite = refused-extension {as = []} done handle-overwrite-refused
no-mux-overwrite : ¬ traces (Process newlyAttached) (map label (occupiedMux ∷ []))
no-mux-overwrite = refused-extension {as = []} done mux-overwrite-refused
no-second-publication : ¬ traces (Process unregistered) (map label (igStep IG.commitDecision ∷ []))
no-second-publication = refused-extension {as = []} done second-publication-refused

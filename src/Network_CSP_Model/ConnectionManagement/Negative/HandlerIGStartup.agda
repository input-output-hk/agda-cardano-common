{-# OPTIONS --guardedness #-}

-- Failed startup cannot skip its stop request; successful earlier starts remain.
module ConnectionManagement.Negative.HandlerIGStartup where

open import Data.List using (map; []; _∷_)
open import Data.Maybe using (nothing; just)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence using (refused-extension)
open import ConnectionManagement.CSP.HandlerIGStartup using (afterFailure; afterStart; restartFailed)
import ConnectionManagement.CSP.IGRuntime as Runtime
import ConnectionManagement.CSP.IGRegistration as G
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

partial-start-retained : M.commands Runtime.partial ≡ M.startCommand G.proto ∷ []
partial-start-retained = refl
failed-start-unregistered : IG.connections (IG.publishedState (inboundGovernor afterFailure)) ≡ []
failed-start-unregistered = refl
cannot-skip-stop-request : advance (igStep IG.finishBatch) afterFailure ≡ nothing
cannot-skip-stop-request = refl
cannot-start-twice : advance (igStep IG.runResponders) afterStart ≡ nothing
cannot-start-twice = refl
cannot-restart-twice-after-failure : advance (igStep IG.restart) restartFailed ≡ nothing
cannot-restart-twice-after-failure = refl

no-stop-request-skip : ¬ traces (Process afterFailure) (map label (igStep IG.finishBatch ∷ []))
no-stop-request-skip = refused-extension {as = []} done cannot-skip-stop-request
no-repeated-start : ¬ traces (Process afterStart) (map label (igStep IG.runResponders ∷ []))
no-repeated-start = refused-extension {as = []} done cannot-start-twice
no-repeated-failed-restart : ¬ traces (Process restartFailed) (map label (igStep IG.restart ∷ []))
no-repeated-failed-restart = refused-extension {as = []} done cannot-restart-twice-after-failure

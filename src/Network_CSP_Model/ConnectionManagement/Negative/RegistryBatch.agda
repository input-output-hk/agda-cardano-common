{-# OPTIONS --guardedness #-}

-- A consumed notification cannot be replayed from the exhausted batch.
module ConnectionManagement.Negative.RegistryBatch where

open import Data.List using ([]; _∷_; _++_; map)
open import Data.Maybe using (nothing)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
import ConnectionManagement.State as S
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.IGRegistration as IG
open import ConnectionManagement.Rules.OriginRegistry
open import ConnectionManagement.Rules.AttributedOrigin using (dispatch)
open import ConnectionManagement.CSP.OriginRegistry using (Process; refused-extension)
open import ConnectionManagement.CSP.AttributedOrigin using (Channel; label)
open import ConnectionManagement.CSP.RegistryBatch
import ConnectionManagement.CSP.Fixtures as F
import ConnectionManagement.Negative.RegistryReturn
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces)

-- Selection drains the queue, while readEvent skips the absent registration.
queue-drained : S.inboundInfo (Open.world (machine selected)) ≡ []
queue-drained = refl
skip-without-CM : IG.continuation (Open.inboundGovernor (machine consumed)) ≡ IG.readNext 12 []
skip-without-CM = refl
no-release-frame : Open.inboundRelease (machine consumed) ≡ nothing
no-release-frame = refl
registration-stays-absent : IG.connections (IG.publishedState (Open.inboundGovernor (machine ready))) ≡ []
registration-stays-absent = refl
batch-boundary : IG.continuation (Open.inboundGovernor (machine ready)) ≡ IG.sampleTime
batch-boundary = refl
read-refused : step (dispatch (Open.igStep IG.readEvent)) ready ≡ nothing
read-refused = refl
no-replay : ¬ traces (Process (start F.start))
  (map label (schedule ++ (dispatch (Open.igStep IG.readEvent) ∷ [])))
no-replay = refused-extension path read-refused
poll-refused : step (dispatch (Open.igStep IG.pollStopped)) consumed ≡ nothing
poll-refused = refl

{-# OPTIONS --safe #-}

-- Finite callback targets preserve arbitrary depths and exact selected values.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ClientCallbackBasisTests where

open import Data.Bool using (Bool; true; false)
open import Data.Empty using (⊥)
open import Data.Integer using (+_; -[1+_])
open import Data.List using ([]; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (nothing; just)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.ClientCallbackBasis Bool as Basis
open import Cardano_network.LeiosNotifyPipeLookahead.Model Bool using (normal; canceled; nodeNext)

-- The Zero branch ignores even a negative supplied maximum depth.
negative-zero : C.client C.issue C.idle [] [] 0 (+ 0) false nothing ∈ Basis.targets C.initial
negative-zero = Basis.complete (C.continue -[1+ 9 ] , D.continue , C.continueZero)

-- Large positive depth choices map to the same exact below-bound target.
large-depth : C.client C.collectingMaybe C.awaiting [] [] 1 (+ 0) false nothing ∈
  Basis.targets (C.client C.poll C.awaiting [] [] 1 (+ 0) false nothing)
large-depth = Basis.complete (C.continue (+ 1000000) , D.continue , C.continueBelow refl)

-- A negative depth can select full collection when arrival is already positive.
negative-full : C.client C.collectingWait C.awaiting [] [] 1 (+ 1) false nothing ∈
  Basis.targets (C.client C.poll C.awaiting [] [] 1 (+ 1) false nothing)
negative-full = Basis.complete (C.continue -[1+ 20 ] , D.continue , C.continueFull refl refl)

-- Unit termination remains available while a handler has already started.
termination-during-handler : C.client C.stopPending (C.handling (normal true)) [] []
  1 (+ 0) false (just tt) ∈
  Basis.targets (C.client C.poll (C.handling (normal true)) [] [] 1 (+ 0) false nothing)
termination-during-handler = Basis.complete (C.terminate tt , D.terminate , C.stopRequested)

-- The receiver alternative retains its exact normal payload beside termination.
exact-normal-handler : C.client C.poll C.bumpArrival [] [] 1 (+ 0) false nothing ∈
  Basis.targets (C.client C.poll (C.handling (normal false)) [] [] 1 (+ 0) false nothing)
exact-normal-handler = Basis.complete (C.handled (normal false) , D.handled , C.delivered refl)

-- Generic successful Canceled handling is supported without claiming node policy.
generic-canceled-handler : C.client C.poll C.bumpArrival [] [] 1 (+ 0) false nothing ∈
  Basis.targets (C.client C.poll (C.handling canceled) [] [] 1 (+ 0) false nothing)
generic-canceled-handler = Basis.complete (C.handled canceled , D.handled , C.delivered refl)

-- A listed exact state is backed by an actual callback, not just an abstract bucket.
reconstruct-callback : Basis.Callback C.initial
  (C.client C.issue C.idle [] [] 0 (+ 0) false nothing)
reconstruct-callback = Basis.sound negative-zero

-- A full-collection state is not invented when the arrival guard is false.
no-full-without-arrival : C.client C.collectingWait C.awaiting [] [] 1 (+ 0) false nothing ∈
  Basis.targets (C.client C.poll C.awaiting [] [] 1 (+ 0) false nothing) → ⊥
no-full-without-arrival (here ())
no-full-without-arrival (there (here ()))
no-full-without-arrival (there (there ()))

-- Successful return has no further callbacks, even with a forged pending handler.
closed-callbacks : Basis.targets
  (C.client C.closed (C.handling (normal true)) [] [] 0 (+ 0) true (just tt)) ≡ []
closed-callbacks = refl

-- The finite callback target also embeds at the actual paired-driver boundary.
paired-continue : D.pair (C.client C.issue C.idle [] [] 0 (+ 0) false nothing)
  (D.serverState D.initial) [] [] nothing nothing nothing nothing ∈
  Basis.driverTargets nodeNext D.initial
paired-continue = Basis.driver-complete {contract = nodeNext}
  {action = C.continue (+ 0)} D.continue C.continueZero

-- Reconstruct a real hidden driver move from that finite-menu membership.
paired-witness : D.Tau nodeNext D.initial
  (D.pair (C.client C.issue C.idle [] [] 0 (+ 0) false nothing)
    (D.serverState D.initial) [] [] nothing nothing nothing nothing)
paired-witness = Basis.driver-sound paired-continue

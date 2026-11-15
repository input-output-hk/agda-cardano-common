{-# OPTIONS --guardedness #-}

-- Small computational controls at the real initializer: all seven relays
-- actions, both kinds of cutoff, depth-one branching, and a refused action.
module ConnectionManagement.Exploration.Controls where

open import Data.Bool using (true)
open import Data.List using ([]; _∷_; map)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Negative.OutboundCleanLifecycleSupport as Support
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Rules.PoolRelays as Relays
import ConnectionManagement.Exploration.Supervised as Supervised
module M = Supervised I.bearerClosed Support.classify Support.capability
module O = M.O
module B = M.B
open import Process_Trees using (ExtI)
open import Semantics.LTS {E = B.Channel} {I = ExtI B.Channel} using (Event√; √)
module W = M.Witness Support.initial Support.initial []
module Find = M.Search W.relaysActions
start = W.start
failure = O.relaysAct (Relays.threadAct Relays.beginFailure)
after = O.outer Support.initial (Relays.relaysState (Data.Maybe.just Relays.bodyUnwinding) Relays.inside)

only-enabled : Find.enabled start ≡ ((failure , after) ∷ [])
only-enabled = refl
refused-finish : O.outerStep (O.relaysAct Relays.finish) start ≡ nothing
refused-finish = refl
initial-allocation : M.allocated start ≡ 1
initial-allocation = refl
one-step : Find.reach 1 1 start ≡ (([] , start) ∷ ((failure ∷ []) , after) ∷ [])
one-step = refl
allocation-frontier : Find.frontiers 1 0 start ≡ (([] , start , Find.allocation-cutoff) ∷ [])
allocation-frontier = refl
depth-frontier : Find.frontiers 0 1 start ≡ (([] , start , Find.depth-cutoff) ∷ [])
depth-frontier = refl
-- Tick is rejected by the existing decoder; every typed action survives.
decoder-control : M.A.decodeAlphabet (√ tt ∷ map B.label W.relaysActions) ≡ W.relaysActions
decoder-control = refl

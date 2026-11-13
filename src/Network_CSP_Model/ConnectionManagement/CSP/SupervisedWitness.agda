{-# OPTIONS --guardedness #-}

-- The committed 109-event initialized inbound G2 witness, with its exact
-- endpoint, lifted through the real outer runtime and both trace renderings.
module ConnectionManagement.CSP.SupervisedWitness where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ; _,_; _×_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_)
open import Process_Trees using (ExtI)
open import ConnectionManagement.Negative.InboundCleanLifecycleSupport
  using (initial; classify; capability; exit)
import ConnectionManagement.Negative.InboundCleanLifecycleSupport as Support
import ConnectionManagement.Negative.InboundCleanLifecycle as Run
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.CSP.Supervised as Bridge
import ConnectionManagement.CSP.SupervisedInner as InnerBridge
import ConnectionManagement.CSP.ResultTrace as Result
import ConnectionManagement.CSP.RuntimeMonitor as Monitor
import ConnectionManagement.Rules.PoolRelays as Pool
module V = Support.V
module W = Support.W
module B = Bridge I.bearerClosed classify capability
module Inner = InnerBridge I.bearerClosed classify capability
module O = B.O
module Values = Result O.Outer O.OuterAction O.outerStep
module Replay = Monitor O.Outer O.OuterAction O.outerStep
import Semantics.Failures as Failures
open import Semantics.Failures {E = B.Channel} {I = ExtI B.Channel} using (traces)

start end : O.Outer
start = O.outer initial (Pool.initial true)
end = O.outer Run.s24 (Pool.initial true)
schedule : List O.OuterAction
schedule = map O.innerAct (Run.schedule ++ Run.completionActions)

-- Only structural induction on the existing proof; no whole-run normalization.
abstract
  outer-run : O.Executes start schedule end
  outer-run = B.lift-run (just Pool.running) Run.initialized-to-completion
  rendered-trace : traces (B.Process start) (map B.label schedule)
  rendered-trace = B.trace-intro outer-run
  value-complete-trace : Σ (List Values.Observation) (λ os →
    map Values.action os ≡ schedule × Values.Recorded start os end)
  value-complete-trace = Values.record-run (B.to-raw outer-run)

-- The terminal snapshot in value-complete-trace includes this physical result.
-- All other return stores, captured observations and frontend cells are retained.
terminal-result : W.resultOf A.child₀ (Run.handlerState (O.inner end)) ≡
  just (W.asyncException (Support.errorId 42))
terminal-result = Run.physical-result

-- Keep a real initialized refused-extension control, rather than treating
-- absence of a legacy origin diagnostic as success of a monitor.
pre-result-schedule : List V.Event
pre-result-schedule = Run.schedule ++
  (Run.a10 ∷ Run.a11 ∷ Run.a12 ∷ Run.a13 ∷ Run.a14 ∷ Run.a15 ∷ Run.a16 ∷ Run.a17 ∷ [])
abstract
  pre-result-run : V.Runs initial pre-result-schedule Run.s17
  pre-result-run = Run.append Run.initialized-to-obstruction
    (V.more Run.e10 (V.more Run.e11 (V.more Run.e12 (V.more Run.e13
    (V.more Run.e14 (V.more Run.e15 (V.more Run.e16 (V.more Run.e17 V.stop))))))))
  premature-result-refused : ¬ traces (B.Process start)
    (map B.label (map O.innerAct pre-result-schedule ++
      (O.innerAct (exit (W.publishAsyncResult A.child₀)) ∷ [])))
  premature-result-refused = B.refused-extension (B.lift-run (just Pool.running) pre-result-run)
    disabled
    where
    disabled : O.outerStep (O.innerAct (exit (W.publishAsyncResult A.child₀)))
      (O.outer Run.s17 (Pool.initial true)) ≡ nothing
    disabled rewrite Run.no-result-before-timewait-finally = refl

-- Current-alphabet replay validation is transported from the committed run.
-- This proof follows the run; it is not a newly claimed explorer search.
abstract
  replay-accepted : Replay.Accepted
    (Replay.replay (Data.List.length schedule) start (map Replay.event schedule))
  replay-accepted = Replay.replay-run (B.to-raw outer-run)

-- The same original proof also instantiates the native frontend renderer.
module InnerTraces = Failures {E = Inner.Channel} {I = ExtI Inner.Channel}
abstract
  inner-rendered-trace : InnerTraces.traces (Inner.Process initial)
    (map Inner.label (Run.schedule ++ Run.completionActions))
  inner-rendered-trace = Inner.trace-intro Run.initialized-to-completion

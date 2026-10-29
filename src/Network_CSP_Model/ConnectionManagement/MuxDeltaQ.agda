{-# OPTIONS --guardedness #-}

-- Explicit bearer TraceEmitDeltaQ callback over the physical mux/handler chain.
-- Pin: Mux.hs:454-464. Normal return and observed sync/async throwing are distinct;
-- no delivery, tracer, provider or shutdown progress is assumed.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.MuxDeltaQ (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain hiding (local; mux)
open import ConnectionManagement.IGTypes using (clean; errored)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.MuxStartupUnwind as Unwind
module R = Unwind isBearerClosed
import ConnectionManagement.MuxExitCancellation as Cancel
module X = Cancel isBearerClosed
import ConnectionManagement.MuxHandlerExit as Exit
module W = Exit isBearerClosed
module G = W.G
module M = G.M
module P = G.P
module U = G.U
module Pool = G.Pool
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.OutboundMachine as O

data Phase : Set where
  captured muxInvoked muxReturned invoked returned throwing : Phase
record Ticket : Set where
  constructor ticket
  field payload : Types.TypedResult
        phase : Phase
open Ticket public
record State : Set where
  constructor deltaQState
  field base : R.State
        tickets : Store WorkerId Ticket
open State public
initial : O.Configuration → Maybe State
initial c with R.initial c
... | nothing = nothing
... | just r = just (deltaQState r [])
source : State → O.Configuration
source s = R.source (base s)
poolAt : WorkerId → State → Pool.State
poolAt w s = R.poolAt w (base s)
monitor : State → M.State
monitor s = G.base (W.base (R.base (base s)))
mark : WorkerId → Ticket → Phase → State → State
mark w t pc s = record s { tickets = put w (record t { phase = pc }) (tickets s) }

-- The ticket comes from a successful actual typed FIFO pop, never from a
-- current protocol-number lookup or a fabricated completion observation.
note : R.Action → R.State → Store WorkerId Ticket → Store WorkerId Ticket
note (R.run (X.run (W.run (G.run (M.consume w))))) r ts with M.pcAt w (G.base (W.base (R.base r)))
... | M.selected item = put w (ticket item captured) ts
... | _ = ts
note _ _ ts = ts
wrapMonitor : M.Action → R.Action
wrapMonitor action = R.run (X.run (W.run (G.run action)))

-- Independent child publication/removal and unrelated owners remain enabled.
-- Only the invoked owner's controller is held across this callback.
actorP : P.Action → Maybe WorkerId
actorP (P.control w _) = just w
actorP (P.forkResponder w _ _) = just w
actorP (P.forkInitiator w _ _ _) = just w
actorP (P.run (U.startupStep w _)) = just w
actorP _ = nothing
actorM : M.Action → Maybe WorkerId
actorM (M.run action) = actorP action
actorM (M.consume w) = just w
actorM (M.handleSelected w) = just w
actorM (M.sampleTracer w) = just w
actorM (M.commitTracer w) = just w
actorM (M.finishProtocolTrace w) = just w
actorM (M.beginDead w) = just w
actorM (M.finishDead w) = just w
actorG : G.Action → Maybe WorkerId
actorG (G.run action) = actorM action
actorG action = R.controller action
actorW : W.Action → Maybe WorkerId
actorW (W.run action) = actorG action
actorW (W.beginExit w) = just w
actorW _ = nothing
actor : R.Action → State → Maybe WorkerId
actor (R.run (X.run action)) s = actorW action
actor (R.observeFailure w _ _) s = just w
actor (R.observeCancellation w _ _) s = just w
actor (R.deliverShutdown _ _) s with Close.phase (W.shutdown (R.base (base s)))
... | Close.awaitDelivery _ w = just w
... | _ = nothing
actor _ s = nothing
free : WorkerId → State → Bool
free w s with lookup w (tickets s)
... | just t with phase t
...   | invoked = false
...   | muxInvoked = false
...   | _ = true
free w s | nothing = true

-- The earlier component's successful DeltaQ-return observation cannot bypass
-- the explicit callback in this adapter. Infrastructure Dead has no DeltaQ.
protocolFinishAllowed : WorkerId → State → Bool
protocolFinishAllowed w s with M.pcAt w (monitor s)
... | M.responderTracing clean = false
... | M.initiatorTracing _ = false
... | _ = true
deadFinishAllowed : WorkerId → State → Bool
deadFinishAllowed w s with lookup w (tickets s)
... | nothing = false
... | just t with payload t
...   | Types.infraMuxer _ = true
...   | Types.infraDemuxer _ = true
...   | Types.protocolCompletion _ _ _ _ = false
-- Legacy observed failures of an ignored initiator trace must also use its
-- explicit invocation in this adapter; responder trace guards remain intact.
legacyTraceAllowed : WorkerId → State → Bool
legacyTraceAllowed w s with M.pcAt w (monitor s)
... | M.initiatorTracing _ = false
... | _ = true
finishAllowed : R.Action → State → Bool
finishAllowed (R.run (X.run (W.run (G.run (M.finishProtocolTrace w))))) s = protocolFinishAllowed w s
finishAllowed (R.run (X.run (W.run (G.run (M.finishDead w))))) s = deadFinishAllowed w s
finishAllowed (R.observeFailure w R.monitorTrace _) s = legacyTraceAllowed w s
finishAllowed _ s = true
allowed : R.Action → State → Bool
allowed action s with actor action s
... | nothing = finishAllowed action s
... | just w = free w s ∧ finishAllowed action s
inherit : R.Action → State → Maybe State
inherit action s with allowed action s
... | false = nothing
... | true with R.step action (base s)
...   | nothing = nothing
...   | just r = just (deltaQState r (note action r (tickets s)))

-- Match direction and captured completion outcome. Protocol-error DeltaQ is
-- reached only AFTER the ordinary Dead callback returned at the original Failed.
point : Types.TypedResult → M.PC → Mux.Status → Bool
point (Types.protocolCompletion Mux.responderJob _ _ clean) (M.responderTracing clean) Mux.ready = true
point (Types.protocolCompletion Mux.initiatorJob _ _ clean) (M.initiatorTracing clean) Mux.ready = true
point (Types.protocolCompletion _ _ _ (errored err)) (M.deadTracing (M.failed actual)) status =
  P.sameOutcome (errored err) (errored actual) ∧ M.finishMatches (M.failed err) status
point _ _ _ = false
-- A callback PC alone cannot adopt a partial startup or an already closed pool.
callbackPoolOpen : Pool.State → Bool
callbackPoolOpen p with Pool.phase p
... | Pool.openPool = true
... | _ = false
-- The initiator-direction completion trace is ignored by IG but still calls
-- the caller's mux tracer. Its return must precede clean DeltaQ or error Dead.
initiatorPoint : Types.TypedResult → M.PC → Mux.Status → Bool
initiatorPoint (Types.protocolCompletion Mux.initiatorJob _ _ clean) (M.initiatorTracing actual) Mux.ready = P.sameOutcome clean actual
initiatorPoint (Types.protocolCompletion Mux.initiatorJob _ _ (errored err)) (M.initiatorTracing actual) status =
  P.sameOutcome (errored err) actual ∧ M.finishMatches (M.failed err) status
initiatorPoint _ _ _ = false
atPoint : WorkerId → Ticket → (Types.TypedResult → M.PC → Mux.Status → Bool) → State → Bool
atPoint w t site s with R.owner w (base s)
... | nothing = false
... | just f with U.progress f
...   | U.promisePublished _ mid with P.muxAt mid (R.protocols (base s))
...     | nothing = false
...     | just m with Mux.callback m
...       | Mux.returned = R.free w (base s) ∧ R.normalControl w (base s) ∧ P.monitoring f ∧
          callbackPoolOpen (P.Startup.pool (U.startup f)) ∧ site (payload t) (M.pcAt w (monitor s)) (Mux.status m)
...       | _ = false
atPoint w t site s | just f | _ = false
ready : WorkerId → Ticket → State → Bool
ready w t s = atPoint w t point s
initiatorReady : WorkerId → Ticket → State → Bool
initiatorReady w t s = atPoint w t initiatorPoint s
entryPhase : Ticket → Bool
entryPhase t with payload t | phase t
... | Types.protocolCompletion Mux.responderJob _ _ _ | captured = true
... | Types.protocolCompletion Mux.initiatorJob _ _ _ | muxReturned = true
... | _ | _ = false
begin : WorkerId → State → Maybe State
begin w s with lookup w (tickets s)
... | just t with entryPhase t ∧ ready w t s
...   | true = just (mark w t invoked s)
...   | false = nothing
begin w s | nothing = nothing
beginInitiator : WorkerId → State → Maybe State
beginInitiator w s with lookup w (tickets s)
... | just t with phase t | initiatorReady w t s
...   | captured | true = just (mark w t muxInvoked s)
...   | _ | _ = nothing
beginInitiator w s | nothing = nothing
-- Clean return leaves the old monitor PC held until explicit DeltaQ. Error
-- return performs the real error-trace-to-Dead continuation, before DeltaQ.
returnInitiator : WorkerId → State → Maybe State
returnInitiator w s with lookup w (tickets s)
... | just t with phase t | initiatorReady w t s
...   | muxInvoked | true with payload t
...     | Types.protocolCompletion Mux.initiatorJob _ _ clean = just (mark w t muxReturned s)
...     | Types.protocolCompletion Mux.initiatorJob _ _ (errored _) with R.step (wrapMonitor (M.finishProtocolTrace w)) (base s)
...       | nothing = nothing
...       | just r = just (mark w t muxReturned (record s { base = r }))
returnInitiator w s | just t | muxInvoked | true | _ = nothing
returnInitiator w s | just t | muxInvoked | false = nothing
returnInitiator w s | just t | captured | _ = nothing
returnInitiator w s | just t | muxReturned | _ = nothing
returnInitiator w s | just t | invoked | _ = nothing
returnInitiator w s | just t | returned | _ = nothing
returnInitiator w s | just t | throwing | _ = nothing
returnInitiator w s | nothing = nothing
finishAction : WorkerId → Types.TypedResult → R.Action
finishAction w (Types.protocolCompletion _ _ _ clean) = wrapMonitor (M.finishProtocolTrace w)
finishAction w _ = wrapMonitor (M.finishDead w)
complete : WorkerId → State → Maybe State
complete w s with lookup w (tickets s)
... | just t with phase t | ready w t s
...   | invoked | true with R.step (finishAction w (payload t)) (base s)
...     | nothing = nothing
...     | just r = just (mark w t returned (record s { base = r }))
complete w s | just t | _ | _ = nothing
complete w s | nothing = nothing

-- The named observation is throwing from an invoked bearer tracer, before
-- normal continuation. Existing fault selection captures the original resources
-- and its real source callback; all subsequent pool/handler guards are retained.
faultPlan : WorkerId → R.Exception → State → Maybe R.Plan
faultPlan w result s with lookup w (tickets s)
... | just t with phase t | ready w t s
...   | invoked | true = R.start w result (λ _ _ → just R.poolBody) (base s)
...   | _ | _ = nothing
faultPlan w result s | nothing = nothing
initiatorFaultPlan : WorkerId → R.Exception → State → Maybe R.Plan
initiatorFaultPlan w result s with lookup w (tickets s)
... | just t with phase t | initiatorReady w t s
...   | muxInvoked | true = R.start w result (λ _ _ → just R.poolBody) (base s)
...   | _ | _ = nothing
initiatorFaultPlan w result s | nothing = nothing
delivery : Bool → R.Plan → R.Plan
delivery true p = R.acknowledge p
delivery false p = p
applyFault : WorkerId → R.Plan → Bool → State → Maybe State
applyFault w plan acknowledge s with lookup w (tickets s)
... | nothing = nothing
... | just t with R.enact (delivery acknowledge plan) (base s)
...   | nothing = nothing
...   | just r = just (mark w t throwing (record s { base = r }))
throw : WorkerId → R.Exception → Bool → State → Maybe State
throw w result acknowledge s with faultPlan w result s
... | nothing = nothing
... | just plan = applyFault w plan acknowledge s

throwInitiator : WorkerId → R.Exception → Bool → State → Maybe State
throwInitiator w result acknowledge s with initiatorFaultPlan w result s
... | nothing = nothing
... | just plan = applyFault w plan acknowledge s

data Action : Set where
  run : R.Action → Action
  beginDeltaQ observeReturn beginInitiatorTrace observeInitiatorReturn : WorkerId → Action
  observeException observeInitiatorException : WorkerId → R.Exception → Action
  deliverShutdown deliverInitiatorShutdown : ErrorId → Action
step : Action → State → Maybe State
step (run action) s = inherit action s
step (beginDeltaQ w) s = begin w s
step (observeReturn w) s = complete w s
step (observeException w err) s = throw w err false s
step (beginInitiatorTrace w) s = beginInitiator w s
step (observeInitiatorReturn w) s = returnInitiator w s
step (observeInitiatorException w err) s = throwInitiator w err false s
step (deliverShutdown err) s with Close.phase (W.shutdown (R.base (base s)))
... | Close.awaitDelivery _ w = throw w (R.async err) true s
... | _ = nothing
step (deliverInitiatorShutdown err) s with Close.phase (W.shutdown (R.base (base s)))
... | Close.awaitDelivery _ w = throwInitiator w (R.async err) true s
... | _ = nothing

data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂

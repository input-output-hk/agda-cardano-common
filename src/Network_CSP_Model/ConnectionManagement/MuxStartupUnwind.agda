{-# OPTIONS --guardedness #-}

-- Post-publication setup/startup and synchronous mux-tracer failure. Preserve
-- the actual incomplete startup phase and close only a pool whose bracket was
-- entered. No fake monitoring/ScopeDone/normal-result bridge is introduced.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.MuxStartupUnwind (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_; _∨_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain hiding (local; mux)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as Machine
import ConnectionManagement.MuxExitCancellation as Cancellation
import ConnectionManagement.MuxHandlerExit as Exit
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close
private
  module X = Cancellation isBearerClosed
  module W = Exit isBearerClosed
  module G = W.G
  module M = G.M
  module P = G.P
  module U = G.U
  module S = G.Startup
  module Pool = G.Pool

data Site : Set where
  bufferAcquire bearerSetup startingTrace egressSetup poolAcquire firstFork secondFork
    matureTrace timeoutSetup monitorTrace stoppingTrace stoppedTrace : Site
data Route : Set where
  beforeBuffer bufferOnly poolBody : Route
data Exception : Set where
  sync async : ErrorId → Exception
asOutcome : Exception → G.Outcome
asOutcome (sync err) = G.failedExit err
asOutcome (async err) = G.asyncExit err
data PC : Set where
  readyBody readyBuffer awaitingClose closing poolClosed asyncStatus asyncDead handedOff : PC
record Fault : Set where
  constructor fault
  field captured : Shared.HandlerStart
        mux : MuxId
        startupAtFailure : S.PC
        callbackAtFailure : Mux.Callback
        scope : Route
        outcome : Exception
        phase : PC
open Fault public
record State : Set where
  constructor unwinding
  field base : X.State
        faults : Store WorkerId Fault
open State public
initial : O.Configuration → Maybe State
initial c with X.initial c
... | nothing = nothing
... | just x = just (unwinding x [])
source : State → O.Configuration
source s = X.source (base s)
poolAt : WorkerId → State → Pool.State
poolAt w s = X.poolAt w (base s)
protocols : State → P.State
protocols s = G.protocolState (W.base (base s))
owner : WorkerId → State → Maybe U.Frame
owner w s = lookup w (U.frames (P.base (protocols s)))
setSource : O.Configuration → State → State
setSource c s = record s { base = W.setSource c (base s) }
setPool : WorkerId → U.Frame → Pool.State → State → State
setPool w f p s = record s { base = record (base s) { base = G.setPool w f p (W.base (base s)) } }
setPhase : WorkerId → Fault → PC → State → Store WorkerId Fault
setPhase w f pc s = put w (record f { phase = pc }) (faults s)
free : WorkerId → State → Bool
free w s with lookup w (faults s)
... | nothing = true
... | just _ = false
traceLive : Mux.Callback → Bool
traceLive (Mux.readActive _) = true
traceLive (Mux.tracerFailed _) = true
traceLive _ = false
-- The custom tracer is the first leg, before the IG active read. A later
-- IG descriptor failure must already be recorded by the real interpreter;
-- pending commitTrace can still retry and is not evidence of an exception.
deadThrowPoint : Mux.Mux → Bool
deadThrowPoint m with Mux.tracerAttachment m | Mux.callback m
... | Mux.noIGTracer | Mux.returned = true
... | _ | callback = traceLive callback
ignoredInitiatorTrace : M.PC → Bool
ignoredInitiatorTrace (M.initiatorTracing _) = true
ignoredInitiatorTrace _ = false
normalControl : WorkerId → State → Bool
normalControl w s = G.sameStage G.idle (G.phase (G.frameAt w (W.base (base s))))

-- Sync failure sites are observed throwing operations, not free failure of
-- arbitrary pure stages. Fork failure is BEFORE birth; masked insertion gaps
-- have no such site. TraceStarting/egress/pool acquisition precede the catch.
siteRoute : WorkerId → Site → U.Frame → Mux.Mux → State → Maybe Route
siteRoute w bufferAcquire f m s with S.phase (U.startup f)
... | S.published = just beforeBuffer
... | _ = nothing
siteRoute w bearerSetup f m s with S.phase (U.startup f)
... | S.bufferReady = just bufferOnly
... | _ = nothing
siteRoute w startingTrace f m s with S.phase (U.startup f)
... | S.runEntered = just bufferOnly
... | _ = nothing
siteRoute w egressSetup f m s with S.phase (U.startup f)
... | S.startingTraced = just bufferOnly
... | _ = nothing
siteRoute w poolAcquire f m s with S.phase (U.startup f)
... | S.egressReady = just bufferOnly
... | _ = nothing
siteRoute w firstFork f m s with S.phase (U.startup f)
... | S.poolReady = just poolBody
... | _ = nothing
siteRoute w secondFork f m s with S.phase (U.startup f)
... | S.muxerRegistered _ = just poolBody
... | _ = nothing
siteRoute w matureTrace f m s with S.phase (U.startup f)
... | S.demuxerRegistered _ _ = just poolBody
... | _ = nothing
siteRoute w timeoutSetup f m s with S.phase (U.startup f)
... | S.matureTraced _ _ = just poolBody
... | _ = nothing
siteRoute w monitorTrace f m s with P.monitoring f | traceLive (Mux.callback m) | ignoredInitiatorTrace (M.pcAt w (G.base (W.base (base s))))
... | true | true | _ = just poolBody
... | true | _ | true = just poolBody
... | _ | _ | _ = nothing
siteRoute w stoppingTrace f m s with G.phase (G.frameAt w (W.base (base s)))
... | G.shutdownSelected = just poolBody
... | _ = nothing
siteRoute w stoppedTrace f m s with G.phase (G.frameAt w (W.base (base s)))
... | G.stoppedTrace = just poolBody
... | G.stoppedTracing with traceLive (Mux.callback m)
...   | true = just poolBody
...   | false = nothing
siteRoute w stoppedTrace f m s | _ = nothing
siteControl : WorkerId → Site → State → Bool
siteControl w stoppingTrace s = true
siteControl w stoppedTrace s = true
siteControl w _ s = normalControl w s

data DeliverySite : Set where
  blockedBufferAcquire blockedBearer unmaskedStartup unmaskedMuxCallback : DeliverySite
asyncRoute : DeliverySite → S.PC → Maybe Route
asyncRoute blockedBufferAcquire S.published = just beforeBuffer
asyncRoute blockedBearer S.bufferReady = just bufferOnly
asyncRoute unmaskedStartup S.runEntered = just bufferOnly
asyncRoute unmaskedStartup S.startingTraced = just bufferOnly
asyncRoute unmaskedStartup S.egressReady = just bufferOnly
asyncRoute unmaskedStartup S.poolReady = just poolBody
asyncRoute unmaskedStartup (S.muxerRegistered _) = just poolBody
asyncRoute unmaskedStartup (S.demuxerRegistered _ _) = just poolBody
asyncRoute unmaskedStartup (S.matureTraced _ _) = just poolBody
asyncRoute _ _ = nothing
deliveryRoute : DeliverySite → U.Frame → Mux.Mux → Maybe Route
deliveryRoute unmaskedMuxCallback f m with P.monitoring f | Mux.interruptibleCallback (Mux.callback m)
... | true | true = just poolBody
... | _ | _ = nothing
deliveryRoute site f m = asyncRoute site (S.phase (U.startup f))
routePC : Route → PC
routePC beforeBuffer = readyBody
routePC bufferOnly = readyBuffer
routePC poolBody = awaitingClose

data Plan : Set where
  local : Store WorkerId Fault → Plan
  machine : O.Action → Store WorkerId Fault → Plan
  pool : WorkerId → U.Frame → Pool.Action → Store WorkerId Fault → Plan
  inherited : X.Action → Plan
  transfer : WorkerId → W.Frame → Store WorkerId Fault → Plan
  acknowledge : Plan → Plan

-- Capture the immutable published owner, actual partial startup/callback and
-- throwing outcome. Registry insertion must already be settled.
start : WorkerId → Exception → (U.Frame → Mux.Mux → Maybe Route) → State → Maybe Plan
start w result route s with free w s | owner w s | lookup w (W.exits (base s)) | P.noParent (poolAt w s)
... | true | just f | nothing | true with U.progress f
...   | U.promisePublished hid mid with P.muxAt mid (protocols s)
...     | just m with route f m
...       | just r = just (local (put w (fault (U.captured f) mid (S.phase (U.startup f)) (Mux.callback m) r result (routePC r)) (faults s)))
...       | nothing = nothing
start w result route s | true | just f | nothing | true | U.promisePublished hid mid | nothing = nothing
start w result route s | true | just f | nothing | true | _ = nothing
start w result route s | _ | _ | _ | _ = nothing

-- The corrected graceful TraceStopped callback is still inside the pool body.
-- Its pending callback uses the same explicit async observation, not the old
-- graceful abort helper whose successful-return guard must remain intact.
deliveryControl : WorkerId → DeliverySite → State → Bool
deliveryControl w unmaskedMuxCallback s = normalControl w s ∨
  G.sameStage G.stoppedTracing (G.phase (G.frameAt w (W.base (base s))))
deliveryControl w _ s = normalControl w s
cancellationPlan : WorkerId → DeliverySite → ErrorId → State → Maybe Plan
cancellationPlan w site err s with deliveryControl w site s
... | true = start w (async err) (λ f m → deliveryRoute site f m) s
... | false = nothing

-- Once selected, only this owner's controller is sealed; physical children,
-- other owners and the post-handoff provider/CM finalizer retain their guards.
allowedP : P.Action → State → Bool
allowedP (P.control w _) s = free w s
allowedP (P.forkResponder w _ _) s = free w s
allowedP (P.forkInitiator w _ _ _) s = free w s
allowedP (P.run (U.startupStep w _)) s = free w s
allowedP _ s = true
allowedM : M.Action → State → Bool
allowedM (M.run action) s = allowedP action s
allowedM (M.consume w) s = free w s
allowedM (M.handleSelected w) s = free w s
allowedM (M.sampleTracer w) s = free w s
allowedM (M.commitTracer w) s = free w s
allowedM (M.finishProtocolTrace w) s = free w s
allowedM (M.beginDead w) s = free w s
allowedM (M.finishDead w) s = free w s
controller : G.Action → Maybe WorkerId
controller (G.selectShutdown w) = just w
controller (G.observeStoppingTrace w) = just w
controller (G.writeStopping w) = just w
controller (G.captureGroup w _) = just w
controller (G.requestGroupCancel w) = just w
controller (G.deliverGroup w) = just w
controller (G.joinGroup w) = just w
controller (G.finishGroup w) = just w
controller (G.drainEmpty w) = just w
controller (G.timeout2Elapsed w) = just w
controller (G.writeStopped w) = just w
controller (G.observeTraceStopped w) = just w
controller (G.sampleStoppedTracer w) = just w
controller (G.commitStoppedTracer w) = just w
controller (G.finishStoppedTrace w) = just w
controller (G.abortOwner w _) = just w
controller (G.beginWholeClose w _) = just w
controller (G.requestWholeCancel w) = just w
controller (G.deliverWhole w) = just w
controller (G.joinWhole w) = just w
controller (G.finishWholeClose w) = just w
controller (G.finishNormalScope w) = just w
controller (G.writeAsyncFailure w) = just w
controller (G.beginAsyncDead w) = just w
controller (G.sampleAsyncTracer w) = just w
controller (G.commitAsyncTracer w) = just w
controller (G.finishAsyncDead w) = just w
controller _ = nothing
allowedG : G.Action → State → Bool
allowedG (G.run action) s = allowedM action s
allowedG action s with controller action
... | nothing = true
... | just w = free w s
allowedW : W.Action → State → Bool
allowedW (W.run action) s = allowedG action s
allowedW (W.beginExit w) s = free w s
allowedW (W.deliverShutdownMux _) s with Close.phase (W.shutdown (base s))
... | Close.awaitDelivery e w = free w s
... | _ = true
allowedW _ s = true
guarded : X.Action → State → Bool
guarded (X.run action) s = allowedW action s
guarded _ s = true
-- With no selected fault every owner is free; this equivalent fast path keeps
-- inherited initializer proofs from specializing the entire controller.
allowed : X.Action → State → Bool
allowed action s with faults s
... | [] = true
... | _ ∷ _ = guarded action s

sameClose : PC → PC → Bool
sameClose awaitingClose awaitingClose = true
sameClose closing closing = true
sameClose _ _ = false
withPool : WorkerId → PC → Pool.Action → PC → State → Maybe Plan
withPool w before action after s with lookup w (faults s) | owner w s
... | just f | just u with sameClose before (phase f)
...   | true = just (pool w u action (setPhase w f after s))
...   | false = nothing
withPool w before action after s | _ | _ = nothing

-- Existing helpers keep their successful-return guards. Only a captured
-- interrupted callback uses the separate source-catch operations.
failureAction : Fault → ErrorId → IG.IGAction
failureAction f err with Mux.interruptibleCallback (callbackAtFailure f)
... | true = IG.recordInterruptedMuxFailure (mux f) err
... | false = IG.recordAsyncMuxFailure (mux f) err
deadAction : Fault → IG.IGAction
deadAction f with Mux.interruptibleCallback (callbackAtFailure f)
... | true = IG.traceInterruptedMuxDead (mux f)
... | false = IG.traceMuxDead (mux f)

data Action : Set where
  run : X.Action → Action
  observeFailure : WorkerId → Site → ErrorId → Action
  observeCancellation : WorkerId → DeliverySite → ErrorId → Action
  deliverShutdown : DeliverySite → ErrorId → Action
  beginClose : WorkerId → List JobId → Action
  requestCancel deliverCancel join finishClose continueSync writeAsyncFailure beginDead sampleDead commitDead finishDead handoff : WorkerId → Action
  observeDeadTraceException : WorkerId → ErrorId → Action

choose : Action → State → Maybe Plan
choose (run action) s with allowed action s
... | true = just (inherited action)
... | false = nothing
choose (observeFailure w site err) s with siteControl w site s
... | true = start w (sync err) (λ f m → siteRoute w site f m s) s
... | false = nothing
choose (observeCancellation w site err) s = cancellationPlan w site err s
choose (deliverShutdown site err) s with Close.phase (W.shutdown (base s))
... | Close.awaitDelivery e w with cancellationPlan w site err s
...   | just p = just (acknowledge p)
...   | nothing = nothing
choose (deliverShutdown site err) s | _ = nothing
choose (beginClose w order) s = withPool w awaitingClose (Pool.beginClose order) closing s
choose (requestCancel w) s = withPool w closing Pool.requestCancel closing s
choose (join w) s = withPool w closing Pool.join closing s
choose (finishClose w) s = withPool w closing Pool.finishClose poolClosed s
choose (deliverCancel w) s with lookup w (faults s) | owner w s | Pool.phase (poolAt w s)
... | just f | just u | Pool.cancelPending j with phase f | G.wholeDeliverable w j u (W.base (base s))
...   | closing | true = just (pool w u Pool.deliverCancel (faults s))
...   | _ | _ = nothing
choose (deliverCancel w) s | _ | _ | _ = nothing
choose (continueSync w) s with lookup w (faults s) | Pool.phase (poolAt w s)
... | just f | Pool.closedPool with phase f | outcome f
...   | poolClosed | sync err = just (local (setPhase w f readyBuffer s))
...   | _ | _ = nothing
choose (continueSync w) s | _ | _ = nothing
choose (writeAsyncFailure w) s with lookup w (faults s) | Pool.phase (poolAt w s)
... | just f | Pool.closedPool with phase f | outcome f
...   | poolClosed | async err = just (machine (O.inbound (Machine.igStep (failureAction f err))) (setPhase w f asyncStatus s))
...   | _ | _ = nothing
choose (writeAsyncFailure w) s | _ | _ = nothing
choose (beginDead w) s with lookup w (faults s)
... | just f with phase f
...   | asyncStatus = just (machine (O.inbound (Machine.igStep (deadAction f))) (setPhase w f asyncDead s))
...   | _ = nothing
choose (beginDead w) s | nothing = nothing
choose (sampleDead w) s with lookup w (faults s)
... | just f with phase f
...   | asyncDead = just (machine (O.inbound (Machine.igStep (IG.sampleTracer (mux f)))) (faults s))
...   | _ = nothing
choose (sampleDead w) s | nothing = nothing
choose (commitDead w) s with lookup w (faults s)
... | just f with phase f
...   | asyncDead = just (machine (O.inbound (Machine.igStep (IG.commitTracer (mux f)))) (faults s))
...   | _ = nothing
choose (commitDead w) s | nothing = nothing
choose (finishDead w) s with lookup w (faults s)
... | just f with phase f | outcome f | P.muxAt (mux f) (protocols s)
...   | asyncDead | async err | just m with Mux.callback m | M.finishMatches (M.failed err) (Mux.status m)
...     | Mux.returned | true = just (local (setPhase w f readyBuffer s))
...     | _ | _ = nothing
choose (finishDead w) s | just f | _ | _ | _ = nothing
choose (finishDead w) s | nothing = nothing
choose (observeDeadTraceException w err) s with lookup w (faults s)
... | just f with phase f | P.muxAt (mux f) (protocols s)
...   | asyncDead | just m with deadThrowPoint m
...     | true = just (local (put w (record f { outcome = sync err; phase = readyBuffer }) (faults s)))
...     | false = nothing
choose (observeDeadTraceException w err) s | just f | _ | _ = nothing
choose (observeDeadTraceException w err) s | nothing = nothing
choose (handoff w) s with lookup w (faults s) | lookup w (W.exits (base s))
... | just f | nothing with phase f | outcome f
...   | readyBuffer | result = just (transfer w (W.exitFrame (captured f) (W.bufferScope (asOutcome result)) nothing) (setPhase w f handedOff s))
...   | readyBody | sync err = just (transfer w (W.exitFrame (captured f) (W.classifying err) nothing) (setPhase w f handedOff s))
...   | readyBody | async err = just (transfer w (W.exitFrame (captured f) (W.bodyExited (W.asyncException err)) nothing) (setPhase w f handedOff s))
...   | _ | _ = nothing
choose (handoff w) s | _ | _ = nothing

enact : Plan → State → Maybe State
enact (local fs) s = just (record s { faults = fs })
enact (machine action fs) s with O.advance action (source s)
... | nothing = nothing
... | just c = just (record (setSource c s) { faults = fs })
enact (pool w u action fs) s with Pool.step action (poolAt w s)
... | nothing = nothing
... | just p = just (record (setPool w u p s) { faults = fs })
enact (inherited action) s with X.step action (base s)
... | nothing = nothing
... | just x = just (record s { base = x })
enact (transfer w f fs) s = just (record s { base = record (base s) { exits = put w f (W.exits (base s)) }; faults = fs })
enact (acknowledge plan) s with enact plan s
... | nothing = nothing
... | just next with W.control Close.acknowledgeDelivery (base next)
...   | nothing = nothing
...   | just x = just (record next { base = x })
step : Action → State → Maybe State
step action s with choose action s
... | nothing = nothing
... | just plan = enact plan s

data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂

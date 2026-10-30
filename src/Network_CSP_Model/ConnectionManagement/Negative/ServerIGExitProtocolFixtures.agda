{-# OPTIONS --guardedness #-}

-- Data-only mux startup/notification snapshots on the initialized inbound
-- source. A shallow record holds data; render builds one flat adapter stack.
module ConnectionManagement.Negative.ServerIGExitProtocolFixtures where

open import Data.Bool using (true; false)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import ConnectionManagement.Domain hiding (worker; local; mux; job)
open import ConnectionManagement.Store using (Store; put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Scenarios.Admission as A
private
  module S = Server I.bearerClosed
  module E = Exit I.bearerClosed
  module N = Publication I.bearerClosed
  module C = N.C
  module D = N.D
  module R = N.R
  module W = N.W
  module G = N.G
  module M = N.M
  module P = N.P
  module U = N.U
  module T = N.S
  module Pool = P.Pool
module F = X.F

record Model : Set where
  constructor model
  field world : Shared.State
        governor : IG.Runtime
        cmRelease : Maybe Release.Frame
        cmRemote : Maybe Remote.Frame
        startup : T.State
        jobs : Store JobId Types.ProtocolJob
        pending : Store WorkerId (List JobId)
        monitors : Store WorkerId M.PC
        tickets : Store WorkerId D.Ticket
open Model public
wrap : M.State → Store WorkerId D.Ticket → N.State
wrap monitor ts = N.publicationState (C.catchState (D.deltaQState (R.unwinding
  (W.handlerExitState (G.shutdownState monitor []) []) []) ts) []) []
configuration : Model → O.Configuration
configuration m = record (S.source F.s11) { core = record (O.core (S.source F.s11))
  { world = world m; inboundGovernor = governor m; inboundRelease = cmRelease m; remoteCall = cmRemote m } }
render : Model → E.State
render m = E.igExitState (S.serverState (wrap (M.monitorState (P.protocolState
  (U.supervised (B.supervised (configuration m) ((A.child₀ , H.handlerThread I.captured H.handshaking) ∷ []) Close.initialState)
    ((A.child₀ , inbound) ∷ [])
    ((A.child₀ , U.frame I.captured inbound I.ps duplex (U.promisePublished (ident 0) (ident 0)) (startup m)) ∷ []))
  (jobs m) (pending m)) (monitors m)) (tickets m)) (S.workers F.s11) S.serving true) E.emptyExit
baseWorld : Shared.ConnectionState → List Shared.IGEvent → Shared.State
baseWorld st queue = record (S.shared F.s11) { inboundInfo = queue
  ; cm = Shared.cmStore (Shared.full F.binding) ((ident 0 , st) ∷ []) 1 }
idle active : Shared.ConnectionState
idle = Shared.inboundIdle A.key₀ A.child₀ (ident 0) duplex
active = Shared.inboundActive A.key₀ A.child₀ (ident 0) duplex
root : Model
root = model (baseWorld idle []) (IG.runtimeState X.registeredState 2 IG.sampleTime X.e₄) nothing nothing
  (T.startupState T.published Pool.initial) [] [] [] []

-- The real startup creates/registers both infrastructure Async handles.
p1 p2 p3 engines : Pool.State
p1 = record Pool.initial { handles = (ident 0 , Pool.bodyRunning) ∷ []; parentFork = just (ident 0) }
p2 = record p1 { registered = ident 0 ∷ []; parentFork = nothing }
p3 = record p2 { handles = (ident 0 , Pool.bodyRunning) ∷ (ident 1 , Pool.bodyRunning) ∷ []; parentFork = just (ident 1) }
engines = record p3 { registered = ident 1 ∷ ident 0 ∷ []; parentFork = nothing }
stage : T.PC → Pool.State → Model
stage pc pool = record root { startup = T.startupState pc pool }
s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 : Model
s1 = stage T.bufferReady Pool.initial
s2 = stage T.bearerReady Pool.initial
s3 = stage T.runEntered Pool.initial
s4 = stage T.startingTraced Pool.initial
s5 = stage T.egressReady Pool.initial
s6 = stage T.poolReady Pool.initial
s7 = stage (T.muxerForked (ident 0)) p1
s8 = stage (T.muxerRegistered (ident 0)) p2
s9 = stage (T.demuxerForked (ident 0) (ident 1)) p3
s10 = stage (T.demuxerRegistered (ident 0) (ident 1)) engines
s11 = stage (T.matureTraced (ident 0) (ident 1)) engines
s12 = stage (T.monitoring (ident 0) (ident 1)) engines
withMux : Mux.Mux → IG.Runtime → IG.Runtime
withMux m ig = IG.setMux (ident 0) m ig
sourceMux : Mux.Mux → List Shared.IGEvent → Model → Model
sourceMux mux queue m = record m { world = record (world m) { inboundInfo = queue }; governor = withMux mux (governor m) }
messages : List Shared.IGEvent
messages = Shared.awakeRemote A.key₀ ∷ Shared.remotePromotedToHot A.key₀ ∷ []
m1 m2 m3 m4 m5 m6 : Mux.Mux
m1 = record X.armedMux { commands = []; waiting = (1 , IG.onDemand) ∷ [] }
m2 = record X.armedMux { commands = []; callback = Mux.readActive (Mux.started 1) }
m3 = record m2 { callback = Mux.commitTrace true (Mux.started 1) }
m4 = record X.armedMux { commands = []; traceCounters = just (Mux.counters (+ 1) (+ 0)); callback = Mux.afterStart 1 }
m5 = record m4 { protocols = (1 , Mux.running) ∷ []; callback = Mux.forkPending 1 }
m6 = record m5 { runningJobs = 1 ∷ []; callback = Mux.returned }
a1 a2 a3 a4 : Model
a1 = sourceMux m1 [] s12
a2 = sourceMux m2 [] s12
a3 = sourceMux m3 [] s12
a4 = sourceMux m4 messages s12

-- IG consumes the ACTUAL startup-tracer messages, then enters masked promotion.
promotionEngine : IG.Engine
promotionEngine = record X.e₄ { lastTime = 11; muxes = (ident 0 , m4) ∷ [] }
promotionTimers : IG.Engine
promotionTimers = record promotionEngine { timers = (ident 0 , ticking) ∷ (ident 1 , ticking) ∷ (ident 2 , ticking) ∷ [] }
g1 g2 g3 g4 g5 g6 g7 g8 g9 g10 g11 g12 g13 : Model
g1 = record a4 { governor = IG.runtimeState X.registeredState 2 (IG.armInactivity 11) promotionEngine }
g2 = record a4 { governor = IG.runtimeState X.registeredState 3 (IG.awaitBatch 11 (ident 2)) promotionTimers }
g3 = record g2 { world = baseWorld idle []; governor = IG.runtimeState X.registeredState 3 (IG.readNext 11 messages) promotionTimers }
g4 = record g3 { governor = IG.runtimeState X.registeredState 3
  (IG.needsCM 11 (Shared.remotePromotedToHot A.key₀ ∷ []) (Shared.awakeRemote A.key₀) X.registeredState) promotionTimers }
promoteFrame promotedFrame : Remote.Frame
promoteFrame = Remote.frame Remote.promote A.key₀ 11 (Shared.remotePromotedToHot A.key₀ ∷ []) X.registeredState
  Remote.transaction (Remote.unsupported nothing) false []
promotedFrame = record promoteFrame { pc = Remote.assertion; outcome = Remote.success idle }
g5 = record g3 { governor = IG.runtimeState X.registeredState 3 IG.inCM promotionTimers; cmRemote = just promoteFrame }
g6 = record g5 { world = baseWorld active []; cmRemote = just promotedFrame }
g7 = record g6 { cmRemote = just (record promotedFrame { pc = Remote.counters }) }
g8 = record g6 { cmRemote = just (record promotedFrame { pc = Remote.returning }) }
warmState hotState : IG.Published
warmState = IG.setRemote A.key₀ IG.remoteWarm X.registeredState
hotState = IG.setRemote A.key₀ IG.remoteHot warmState
g9 = record g6 { cmRemote = nothing; governor = IG.runtimeState X.registeredState 3
  (IG.publishDecision 11 (Shared.remotePromotedToHot A.key₀ ∷ []) warmState) promotionTimers }
g10 = record g9 { governor = IG.runtimeState warmState 3 (IG.readNext 11 (Shared.remotePromotedToHot A.key₀ ∷ [])) promotionTimers }
g11 = record g9 { governor = IG.runtimeState warmState 3 (IG.publishDecision 11 [] hotState) promotionTimers }
g12 = record g9 { governor = IG.runtimeState hotState 3 (IG.readNext 11 []) promotionTimers }
g13 = record g9 { governor = IG.runtimeState hotState 3 IG.sampleTime promotionTimers }

-- A physical responder then produces the real clean-completion notifications.
job : Types.BodyPhase → Types.ProtocolJob
job pc = Types.protocolJob A.child₀ (ident 0) Mux.responderJob 1 (ident 0) pc
payload : Types.TypedResult
payload = Types.protocolCompletion Mux.responderJob 1 (ident 0) IG.clean
forkPool registeredPool returnedPool publishedPool consumedPool : Pool.State
forkPool = record engines { handles = Pool.handles engines ++ ((ident 10 , Pool.bodyRunning) ∷ []); parentFork = just (ident 10) }
registeredPool = record forkPool { registered = ident 10 ∷ ident 1 ∷ ident 0 ∷ []; parentFork = nothing }
returnedPool = record registeredPool { handles = put (ident 10) (Pool.bodyReturned payload) (Pool.handles registeredPool) }
publishedPool = record returnedPool { handles = put (ident 10) (Pool.deregisterPending Pool.normalExit) (Pool.handles returnedPool); completions = payload ∷ [] }
consumedPool = record publishedPool { completions = [] }
poolAt : Pool.State → Model → Model
poolAt pool m = record m { startup = T.startupState (T.monitoring (ident 0) (ident 1)) pool }
cleanMux resultMux selectedMux sampledMux completedMux restartedMux : Mux.Mux
cleanMux = record m6 { protocols = (1 , Mux.idle) ∷ []; runningJobs = []; finishedJobs = (1 , IG.clean) ∷ [] }
resultMux = record cleanMux { finishedJobs = []; completions = Mux.jobResult Mux.responderJob 1 IG.clean ∷ [] }
selectedMux = record cleanMux { finishedJobs = []; callback = Mux.readActive (Mux.completed 1 IG.clean) }
sampledMux = record selectedMux { callback = Mux.commitTrace true (Mux.completed 1 IG.clean) }
completedMux = record selectedMux { callback = Mux.returned; traceCounters = just (Mux.counters (+ 0) (+ 0)) }
restartedMux = record completedMux { protocols = (1 , Mux.demand) ∷ []; commands = Mux.startCommand (IG.protocol 1 IG.hot IG.onDemand) ∷ [] }
terminated : Shared.Terminated
terminated = Shared.terminatedProtocol A.key₀ (ident 0) (IG.protocol 1 IG.hot IG.onDemand) duplex IG.clean
completionMessages : List Shared.IGEvent
completionMessages = Shared.miniProtocolTerminated terminated ∷ Shared.remoteDemotedToWarm A.key₀ ∷ Shared.waitIdleRemote A.key₀ ∷ []
j1 j2 j3 j4 j5 j6 j7 j8 j9 j10 j11 j12 j13 : Model
j1 = sourceMux m5 [] g13
j2 = record (poolAt forkPool (sourceMux m6 [] g13)) { jobs = (ident 10 , job Types.executing) ∷ [] }
j3 = record (poolAt registeredPool j2) { jobs = (ident 10 , job Types.executing) ∷ [] }
j4 = record j3 { jobs = (ident 10 , job Types.waitingEgress) ∷ [] }
j5 = record (sourceMux cleanMux [] j3) { jobs = (ident 10 , job (Types.resultCaptured IG.clean)) ∷ []; pending = (A.child₀ , ident 10 ∷ []) ∷ [] }
j6 = poolAt returnedPool j5
j7 = record (poolAt publishedPool (sourceMux resultMux [] j5)) { pending = (A.child₀ , []) ∷ [] }
j8 = record (poolAt consumedPool j7) { monitors = (A.child₀ , M.selected payload) ∷ []
  ; tickets = (A.child₀ , D.ticket payload D.captured) ∷ [] }
j9 = record (sourceMux selectedMux [] j8) { monitors = (A.child₀ , M.responderTracing IG.clean) ∷ [] }
j10 = sourceMux sampledMux [] j9
j11 = sourceMux completedMux completionMessages j9
j12 = record j11 { tickets = (A.child₀ , D.ticket payload D.invoked) ∷ [] }
j13 = record j11 { monitors = (A.child₀ , M.waiting) ∷ []; tickets = (A.child₀ , D.ticket payload D.returned) ∷ [] }

-- Consume clean completion, publish RemoteWarm, then enter unmasked demotion.
demotionEngine demotionTimers restartedEngine : IG.Engine
demotionEngine = record (IG.execution (governor j13)) { lastTime = 12 }
demotionTimers = record demotionEngine { timers = (ident 0 , ticking) ∷ (ident 1 , ticking) ∷ (ident 2 , ticking) ∷ (ident 3 , ticking) ∷ [] }
restartedEngine = record demotionTimers { muxes = (ident 0 , restartedMux) ∷ [] }
d1 d2 d3 d4 d5 d6 d7 d8 d9 d10 d11 : Model
d1 = record j13 { governor = IG.runtimeState hotState 3 (IG.armInactivity 12) demotionEngine }
d2 = record j13 { governor = IG.runtimeState hotState 4 (IG.awaitBatch 12 (ident 3)) demotionTimers }
d3 = record d2 { world = baseWorld active []; governor = IG.runtimeState hotState 4 (IG.readNext 12 completionMessages) demotionTimers }
d4 = record d3 { governor = IG.runtimeState hotState 4 (IG.restartResponder 12
  (Shared.remoteDemotedToWarm A.key₀ ∷ Shared.waitIdleRemote A.key₀ ∷ []) terminated) demotionTimers }
d5 = record d3 { governor = IG.runtimeState hotState 4 (IG.readNext 12 (Shared.remoteDemotedToWarm A.key₀ ∷ Shared.waitIdleRemote A.key₀ ∷ [])) restartedEngine }
d6 = record d3 { governor = IG.runtimeState hotState 4 (IG.publishDecision 12 (Shared.waitIdleRemote A.key₀ ∷ []) warmState) restartedEngine }
d7 = record d3 { governor = IG.runtimeState warmState 4 (IG.readNext 12 (Shared.waitIdleRemote A.key₀ ∷ [])) restartedEngine }
d8 = record d3 { governor = IG.runtimeState warmState 4 (IG.needsCM 12 [] (Shared.waitIdleRemote A.key₀) warmState) restartedEngine }
demoteFrame demotedFrame : Remote.Frame
demoteFrame = Remote.frame Remote.demote A.key₀ 12 [] warmState Remote.transaction (Remote.unsupported nothing) false []
demotedFrame = record demoteFrame { pc = Remote.assertion; outcome = Remote.success active }
d9 = record d3 { governor = IG.runtimeState warmState 4 IG.inCM restartedEngine; cmRemote = just demoteFrame }
d10 = record d9 { world = baseWorld idle []; cmRemote = just demotedFrame }
d11 = record d10 { cmRemote = just (record demotedFrame { pc = Remote.counters }) }

{-# OPTIONS --guardedness #-}

-- Initialized typed physical-pool acceptance. The responder restart frontend
-- injection below is explicitly conditional; observed initiator forks exercise
-- the new component contract, not an old PeerActions.startProtocol trace claim.
module ConnectionManagement.Negative.MuxProtocolJobs where

open import Data.Bool using (true; false)
open import Data.Nat using (ℕ)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (job; worker; mux)
open import ConnectionManagement.IGTypes using (RunResult; clean; errored; awakeRemote; remotePromotedToHot; onDemand)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.MuxProtocolJobs as W
module U = W.U
module S = W.Startup
module Pool = W.Pool
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Properties.MuxProtocolJobs as Facts
import ConnectionManagement.Properties.OutboundRuntimeCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeSupply as Supply
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as M
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Negative.MuxProtocolFixtures as Old
module Prior = Old.Prior
module Fixture = Old.Fixture
module F = Old.F
module G = Old.G
open import ConnectionManagement.Scenarios.Admission using (key₀)

owner : WorkerId
owner = Fixture.child
mid : MuxId
mid = ident 0
j₀ j₁ j₁₀ j₁₁ j₁₂ j₂₀ : JobId
j₀ = ident 0
j₁ = ident 1
j₁₀ = ident 10
j₁₁ = ident 11
j₁₂ = ident 12
j₂₀ = ident 20
r₀ r₁ r₂ r₃ : RunId
r₀ = ident 0
r₁ = ident 1
r₂ = ident 2
r₃ = ident 3
err : ErrorId
err = errorId 77

-- Reuse only nongeneric source/physical-handler snapshots, then prove every
-- new typed wrapper step from its own initializer. No physical mux is adopted.
birthSnapshot : Old.U.State → W.State
birthSnapshot old = W.protocolState (U.supervised (Old.U.base old) (Old.U.origins old) []) [] []
b0 : W.State
b0 = birthSnapshot Old.q₀
b1 : W.State
b1 = birthSnapshot Old.q1
b2 : W.State
b2 = birthSnapshot Old.q2
b3 : W.State
b3 = birthSnapshot Old.q3
b4 : W.State
b4 = birthSnapshot Old.q4
b5 : W.State
b5 = birthSnapshot Old.q5
b6 : W.State
b6 = birthSnapshot Old.q6
b7 : W.State
b7 = birthSnapshot Old.q7
b8 : W.State
b8 = birthSnapshot Old.q8
b9 : W.State
b9 = birthSnapshot Old.q9
b10 : W.State
b10 = birthSnapshot Old.q10
b11 : W.State
b11 = birthSnapshot Old.q11
b12 : W.State
b12 = birthSnapshot Old.q12
actual-initializer : W.initial (O.initial F.start) ≡ just b0
actual-initializer = refl
birth1 : W.step (W.run (U.run (B.outbound (O.beginAcquire Fixture.caller Fixture.req)))) b0 ≡ just b1
birth1 = refl
birth2 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller (A.select nothing))))) b1 ≡ just b2
birth2 = refl
birth3 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.readCounters)))) b2 ≡ just b3
birth3 = refl
birth4 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.newPromise)))) b3 ≡ just b4
birth4 = refl
birth5 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.openOK)))) b4 ≡ just b5
birth5 = refl
birth6 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.configureOK)))) b5 ≡ just b6
birth6 = refl
birth7 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.connectOK)))) b6 ≡ just b7
birth7 = refl
birth8 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller (A.gotLocal (local key₀)))))) b7 ≡ just b8
birth8 = refl
birth9 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.updateLocalAddress)))) b8 ≡ just b9
birth9 = refl
birth10 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.forkOK)))) b9 ≡ just b10
birth10 = refl
birth11 : W.step (W.run (U.run (B.handler (H.enterHandshake owner)))) b10 ≡ just b11
birth11 = refl
birth12 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.commitConnected)))) b11 ≡ just b12
birth12 = refl
birthPathActions : List W.Action
birthPathActions = (W.run (U.run (B.outbound (O.beginAcquire Fixture.caller Fixture.req)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller (A.select nothing))))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.readCounters)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.newPromise)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.openOK)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.configureOK)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.connectOK)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller (A.gotLocal (local key₀)))))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.updateLocalAddress)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.forkOK)))) ∷ (W.run (U.run (B.handler (H.enterHandshake owner)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.commitConnected)))) ∷ []
birthPath : W.Executes b0 birthPathActions b12
birthPath = W.next birth1 (W.next birth2 (W.next birth3 (W.next birth4 (W.next birth5 (W.next birth6 (W.next birth7 (W.next birth8 (W.next birth9 (W.next birth10 (W.next birth11 (W.next birth12 (W.done))))))))))))
publishedFrame : S.State → U.Frame
publishedFrame stage = U.frame Prior.captured outbound Old.ps duplex (U.promisePublished (ident 0) mid) stage
at : O.Configuration → S.State → Store JobId T.ProtocolJob → Store WorkerId (List JobId) → W.State
at c stage jobs pending = W.protocolState
  (U.supervised (record Old.publishedBase { source = c }) Old.born ((owner , publishedFrame stage) ∷ [])) jobs pending
publishedStage : S.State
publishedStage = S.startupState S.published Pool.initial
b13 b14 b15 : W.State
b13 = W.protocolState (U.supervised Prior.p12 Old.born
  ((owner , U.frame Prior.captured outbound Old.ps duplex U.returnedSuccess S.initial) ∷ [])) [] []
b14 = W.protocolState (U.supervised Old.allocatedBase Old.born
  ((owner , U.frame Prior.captured outbound Old.ps duplex (U.handleAllocated (ident 0) mid) S.initial) ∷ [])) [] []
b15 = at (Old.U.source Old.q15) publishedStage [] []
success13 : W.step (W.run (U.negotiate owner Old.ps duplex)) b12 ≡ just b13
success13 = refl
success14 : W.step (W.run (U.allocateHandle owner (ident 0) mid)) b13 ≡ just b14
success14 = refl
success15 : W.step (W.run (U.publishSuccess owner)) b14 ≡ just b15
success15 = refl
publicationPathActions : List W.Action
publicationPathActions = (W.run (U.negotiate owner Old.ps duplex)) ∷ (W.run (U.allocateHandle owner (ident 0) mid)) ∷ (W.run (U.publishSuccess owner)) ∷ []
publicationPath : W.Executes b12 publicationPathActions b15
publicationPath = W.next success13 (W.next success14 (W.next success15 (W.done)))
c1 : W.State
c1 = at (Old.U.source Old.c1) publishedStage [] []
c2 : W.State
c2 = at (Old.U.source Old.c2) publishedStage [] []
c3 : W.State
c3 = at (Old.U.source Old.c3) publishedStage [] []
c4 : W.State
c4 = at (Old.U.source Old.c4) publishedStage [] []
c5 : W.State
c5 = at (Old.U.source Old.c5) publishedStage [] []
c6 : W.State
c6 = at (Old.U.source Old.c6) publishedStage [] []
c7 : W.State
c7 = at (Old.U.source Old.c7) publishedStage [] []
c8 : W.State
c8 = at (Old.U.source Old.c8) publishedStage [] []
c9 : W.State
c9 = at (Old.U.source Old.c9) publishedStage [] []
c10 : W.State
c10 = at (Old.U.source Old.c10) publishedStage [] []
c11 : W.State
c11 = at (Old.U.source Old.c11) publishedStage [] []
caller1 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.readCounters)))) b15 ≡ just c1
caller1 = refl
caller2 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.readResult)))) c1 ≡ just c2
caller2 = refl
caller3 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.commitHandshake)))) c2 ≡ just c3
caller3 = refl
caller4 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.readCounters)))) c3 ≡ just c4
caller4 = refl
caller5 : W.step (W.run (U.run (B.outbound (O.acquire Fixture.caller A.returnResult)))) c4 ≡ just c5
caller5 = refl
caller6 : W.step (W.run (U.run (B.handler (H.run (M.igStep (IG.captureTime 0)))))) c5 ≡ just c6
caller6 = refl
caller7 : W.step (W.run (U.run (B.handler (H.run (M.igStep IG.registerInactivity))))) c6 ≡ just c7
caller7 = refl
caller8 : W.step (W.run (U.run (B.handler (H.run (M.igStep IG.selectBatch))))) c7 ≡ just c8
caller8 = refl
caller9 : W.step (W.run (U.run (B.handler (H.run (M.igStep IG.readEvent))))) c8 ≡ just c9
caller9 = refl
caller10 : W.step (W.run (U.run (B.handler (H.run (M.igStep IG.registerIdleTimer))))) c9 ≡ just c10
caller10 = refl
caller11 : W.step (W.run (U.run (B.handler (H.run (M.igStep IG.runResponders))))) c10 ≡ just c11
caller11 = refl
callerPathActions : List W.Action
callerPathActions = (W.run (U.run (B.outbound (O.acquire Fixture.caller A.readCounters)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.readResult)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.commitHandshake)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.readCounters)))) ∷ (W.run (U.run (B.outbound (O.acquire Fixture.caller A.returnResult)))) ∷ (W.run (U.run (B.handler (H.run (M.igStep (IG.captureTime 0)))))) ∷ (W.run (U.run (B.handler (H.run (M.igStep IG.registerInactivity))))) ∷ (W.run (U.run (B.handler (H.run (M.igStep IG.selectBatch))))) ∷ (W.run (U.run (B.handler (H.run (M.igStep IG.readEvent))))) ∷ (W.run (U.run (B.handler (H.run (M.igStep IG.registerIdleTimer))))) ∷ (W.run (U.run (B.handler (H.run (M.igStep IG.runResponders))))) ∷ []
callerPath : W.Executes b15 callerPathActions c11
callerPath = W.next caller1 (W.next caller2 (W.next caller3 (W.next caller4 (W.next caller5 (W.next caller6 (W.next caller7 (W.next caller8 (W.next caller9 (W.next caller10 (W.next caller11 (W.done)))))))))))
firstFork firstRegistered secondFork engines : Pool.State
firstFork = record Pool.initial { handles = (j₀ , Pool.bodyRunning) ∷ []; parentFork = just j₀ }
firstRegistered = record firstFork { registered = j₀ ∷ []; parentFork = nothing }
secondFork = record firstRegistered { handles = (j₀ , Pool.bodyRunning) ∷ (j₁ , Pool.bodyRunning) ∷ []; parentFork = just j₁ }
engines = record secondFork { registered = j₁ ∷ j₀ ∷ []; parentFork = nothing }
s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 s12 s13 : S.State
s1 = publishedStage
s2 = S.startupState S.bufferReady Pool.initial
s3 = S.startupState S.bearerReady Pool.initial
s4 = S.startupState S.runEntered Pool.initial
s5 = S.startupState S.startingTraced Pool.initial
s6 = S.startupState S.egressReady Pool.initial
s7 = S.startupState S.poolReady Pool.initial
s8 = S.startupState (S.muxerForked j₀) firstFork
s9 = S.startupState (S.muxerRegistered j₀) firstRegistered
s10 = S.startupState (S.demuxerForked j₀ j₁) secondFork
s11 = S.startupState (S.demuxerRegistered j₀ j₁) engines
s12 = S.startupState (S.matureTraced j₀ j₁) engines
s13 = S.startupState (S.monitoring j₀ j₁) engines
z1 : W.State
z1 = at (Old.U.source Old.c11) s2 [] []
z2 : W.State
z2 = at (Old.U.source Old.c11) s3 [] []
z3 : W.State
z3 = at (Old.U.source Old.c11) s4 [] []
z4 : W.State
z4 = at (Old.U.source Old.c11) s5 [] []
z5 : W.State
z5 = at (Old.U.source Old.c11) s6 [] []
z6 : W.State
z6 = at (Old.U.source Old.c11) s7 [] []
z7 : W.State
z7 = at (Old.U.source Old.c11) s8 [] []
z8 : W.State
z8 = at (Old.U.source Old.c11) s9 [] []
z9 : W.State
z9 = at (Old.U.source Old.c11) s10 [] []
z10 : W.State
z10 = at (Old.U.source Old.c11) s11 [] []
z11 : W.State
z11 = at (Old.U.source Old.c11) s12 [] []
z12 : W.State
z12 = at (Old.U.source Old.c11) s13 [] []
startup1 : W.step (W.run (U.startupStep owner (S.allocateBuffer))) c11 ≡ just z1
startup1 = refl
startup2 : W.step (W.run (U.startupStep owner (S.createBearer))) z1 ≡ just z2
startup2 = refl
startup3 : W.step (W.run (U.startupStep owner (S.enterRun))) z2 ≡ just z3
startup3 = refl
startup4 : W.step (W.run (U.startupStep owner (S.traceStarting))) z3 ≡ just z4
startup4 = refl
startup5 : W.step (W.run (U.startupStep owner (S.allocateEgress))) z4 ≡ just z5
startup5 = refl
startup6 : W.step (W.run (U.startupStep owner (S.openPool))) z5 ≡ just z6
startup6 = refl
startup7 : W.step (W.run (U.startupStep owner (S.forkMuxer j₀))) z6 ≡ just z7
startup7 = refl
startup8 : W.step (W.run (U.startupStep owner (S.registerMuxer))) z7 ≡ just z8
startup8 = refl
startup9 : W.step (W.run (U.startupStep owner (S.forkDemuxer j₁))) z8 ≡ just z9
startup9 = refl
startup10 : W.step (W.run (U.startupStep owner (S.registerDemuxer))) z9 ≡ just z10
startup10 = refl
startup11 : W.step (W.run (U.startupStep owner (S.traceMature))) z10 ≡ just z11
startup11 = refl
startup12 : W.step (W.run (U.startupStep owner (S.enterMonitor))) z11 ≡ just z12
startup12 = refl
startupPathActions : List W.Action
startupPathActions = (W.run (U.startupStep owner (S.allocateBuffer))) ∷ (W.run (U.startupStep owner (S.createBearer))) ∷ (W.run (U.startupStep owner (S.enterRun))) ∷ (W.run (U.startupStep owner (S.traceStarting))) ∷ (W.run (U.startupStep owner (S.allocateEgress))) ∷ (W.run (U.startupStep owner (S.openPool))) ∷ (W.run (U.startupStep owner (S.forkMuxer j₀))) ∷ (W.run (U.startupStep owner (S.registerMuxer))) ∷ (W.run (U.startupStep owner (S.forkDemuxer j₁))) ∷ (W.run (U.startupStep owner (S.registerDemuxer))) ∷ (W.run (U.startupStep owner (S.traceMature))) ∷ (W.run (U.startupStep owner (S.enterMonitor))) ∷ []
startupPath : W.Executes c11 startupPathActions z12
startupPath = W.next startup1 (W.next startup2 (W.next startup3 (W.next startup4 (W.next startup5 (W.next startup6 (W.next startup7 (W.next startup8 (W.next startup9 (W.next startup10 (W.next startup11 (W.next startup12 (W.done))))))))))))
append : ∀ {p as q bs r} → W.Executes p as q → W.Executes q bs r → W.Executes p (as ++ bs) r
append W.done tail = tail
append (W.next eq path) tail = W.next eq (append path tail)
startActions : List W.Action
startActions = ((birthPathActions ++ publicationPathActions) ++ callerPathActions) ++ startupPathActions
abstract
  initialized-start : W.Executes b0 startActions z12
  initialized-start = append (append (append birthPath publicationPath) callerPath) startupPath

-- Flat source/pool snapshots keep runtime normalization bounded. The same
-- startup pool holds engines and all later protocol generations.
physical : JobId → Pool.ThreadPhase → Pool.State → Pool.State
physical j phase p = record p { handles = put j phase (Pool.handles p) }
snapshot : O.Configuration → Pool.State → Store JobId T.ProtocolJob → Store WorkerId (List JobId) → W.State
snapshot c p jobs pending = at c (S.startupState (S.monitoring j₀ j₁) p) jobs pending
sourceMux : Mux.Mux → List Shared.IGEvent → O.Configuration
sourceMux m queue = record (Old.U.source Old.c11) { core = record (O.core (Old.U.source Old.c11))
  { inboundGovernor = IG.setMux mid m (M.inboundGovernor (O.core (Old.U.source Old.c11)))
  ; world = record (M.world (O.core (Old.U.source Old.c11))) { inboundInfo = queue } } }
messages : List Shared.IGEvent
messages = awakeRemote key₀ ∷ remotePromotedToHot key₀ ∷ []
m1 m2 m3 m4 m5 m6 cleanMux publishedMux : Mux.Mux
m1 = record G.armedMux { commands = []; waiting = (1 , onDemand) ∷ [] }
m2 = record G.armedMux { commands = []; callback = Mux.readActive (Mux.started 1) }
m3 = record m2 { callback = Mux.commitTrace true (Mux.started 1) }
m4 = record G.armedMux { commands = []; traceCounters = just (Mux.counters (+ 1) (+ 0)); callback = Mux.afterStart 1 }
m5 = record m4 { protocols = (1 , Mux.running) ∷ []; callback = Mux.forkPending 1 }
m6 = record m5 { runningJobs = 1 ∷ []; callback = Mux.returned }
cleanMux = record m6 { protocols = (1 , Mux.idle) ∷ []; runningJobs = []; finishedJobs = (1 , clean) ∷ [] }
publishedMux = record cleanMux { finishedJobs = []; completions = Mux.jobResult Mux.responderJob 1 clean ∷ [] }
rJob : T.BodyPhase → T.ProtocolJob
rJob phase = T.protocolJob owner mid Mux.responderJob 1 r₀ phase
rPayload : T.TypedResult
rPayload = T.protocolCompletion Mux.responderJob 1 r₀ clean
rFork rReturned rPublished rInserted rRemoved rTerminal : Pool.State
rFork = record (physical j₁₀ Pool.bodyRunning engines) { parentFork = just j₁₀ }
rReturned = physical j₁₀ (Pool.bodyReturned rPayload) rFork
rPublished = record (physical j₁₀ (Pool.deregisterPending Pool.normalExit) rReturned) { completions = rPayload ∷ [] }
rInserted = record rPublished { registered = j₁₀ ∷ j₁ ∷ j₀ ∷ []; parentFork = nothing }
rRemoved = record (physical j₁₀ (Pool.deregistered Pool.normalExit) rInserted) { registered = j₁ ∷ j₀ ∷ [] }
rTerminal = physical j₁₀ (Pool.resultAvailable Pool.normalExit) rRemoved
r1 r2 r3 r4 r5 r6 r7 r8 r9 r10 r11 r12 r13 : W.State
r1 = snapshot (sourceMux m1 []) engines [] []
r2 = snapshot (sourceMux m2 []) engines [] []
r3 = snapshot (sourceMux m3 []) engines [] []
r4 = snapshot (sourceMux m4 messages) engines [] []
r5 = snapshot (sourceMux m5 messages) engines [] []
r6 = snapshot (sourceMux m6 messages) rFork ((j₁₀ , rJob T.executing) ∷ []) []
r7 = snapshot (sourceMux m6 messages) rFork ((j₁₀ , rJob T.waitingEgress) ∷ []) []
r8 = snapshot (sourceMux cleanMux messages) rFork ((j₁₀ , rJob (T.resultCaptured clean)) ∷ []) ((owner , j₁₀ ∷ []) ∷ [])
r9 = snapshot (sourceMux cleanMux messages) rReturned ((j₁₀ , rJob (T.resultCaptured clean)) ∷ []) ((owner , j₁₀ ∷ []) ∷ [])
r10 = snapshot (sourceMux publishedMux messages) rPublished ((j₁₀ , rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])
r11 = snapshot (sourceMux publishedMux messages) rInserted ((j₁₀ , rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])
r12 = snapshot (sourceMux publishedMux messages) rRemoved ((j₁₀ , rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])
r13 = snapshot (sourceMux publishedMux messages) rTerminal ((j₁₀ , rJob (T.resultCaptured clean)) ∷ []) ((owner , []) ∷ [])
responder1 : W.step (W.control owner W.selectCommand) z12 ≡ just r1
responder1 = refl
responder2 : W.step (W.control owner (W.demand 1)) r1 ≡ just r2
responder2 = refl
responder3 : W.step (W.control owner W.sampleTracer) r2 ≡ just r3
responder3 = refl
responder4 : W.step (W.control owner W.commitTracer) r3 ≡ just r4
responder4 = refl
responder5 : W.step (W.control owner W.finishStart) r4 ≡ just r5
responder5 = refl
responder6 : W.step (W.forkResponder owner j₁₀ r₀) r5 ≡ just r6
responder6 = refl
responder7 : W.step (W.protocolReturned j₁₀) r6 ≡ just r7
responder7 = refl
responder8 : W.step (W.commitClean j₁₀) r7 ≡ just r8
responder8 = refl
responder9 : W.step (W.returnProtocol j₁₀) r8 ≡ just r9
responder9 = refl
responder10 : W.step (W.publishProtocol j₁₀) r9 ≡ just r10
responder10 = refl
responder11 : W.step (W.registerProtocol j₁₀) r10 ≡ just r11
responder11 = refl
responder12 : W.step (W.deregisterProtocol j₁₀) r11 ≡ just r12
responder12 = refl
responder13 : W.step (W.asyncProtocolResult j₁₀) r12 ≡ just r13
responder13 = refl
responderPathActions : List W.Action
responderPathActions = (W.control owner W.selectCommand) ∷ (W.control owner (W.demand 1)) ∷ (W.control owner W.sampleTracer) ∷ (W.control owner W.commitTracer) ∷ (W.control owner W.finishStart) ∷ (W.forkResponder owner j₁₀ r₀) ∷ (W.protocolReturned j₁₀) ∷ (W.commitClean j₁₀) ∷ (W.returnProtocol j₁₀) ∷ (W.publishProtocol j₁₀) ∷ (W.registerProtocol j₁₀) ∷ (W.deregisterProtocol j₁₀) ∷ (W.asyncProtocolResult j₁₀) ∷ []
responderPath : W.Executes z12 responderPathActions r13
responderPath = W.next responder1 (W.next responder2 (W.next responder3 (W.next responder4 (W.next responder5 (W.next responder6 (W.next responder7 (W.next responder8 (W.next responder9 (W.next responder10 (W.next responder11 (W.next responder12 (W.next responder13 (W.done)))))))))))))
abstract
  initialized-fast-responder : W.Executes b0 (startActions ++ responderPathActions) r13
  initialized-fast-responder = append initialized-start responderPath
initialized-source-and-pools : Facts.Paths b0 r13
initialized-source-and-pools = Facts.exec-projects initialized-fast-responder
initialized-same-pool : Facts.PTrace Pool.initial (W.poolAt owner r13)
initialized-same-pool = Facts.pool-from-initial actual-initializer initialized-fast-responder owner
initialized-captures : Capture.Captures (W.source r13)
initialized-captures = Facts.from-initial-captures actual-initializer initialized-fast-responder
initialized-supply : Supply.Valid (W.source r13)
initialized-supply = Facts.from-initial-supply actual-initializer Prior.initial-bounds initialized-fast-responder
return-observation : Facts.BodyReturn j₁₀ r8 r9
return-observation = Facts.return-observation j₁₀ r8 responder9
publication-observation : Facts.Publication j₁₀ r9 r10
publication-observation = Facts.publication-observation j₁₀ r9 responder10

no-outcome-before-physical-fork : W.step (W.protocolReturned j₁₀) r5 ≡ nothing
no-outcome-before-physical-fork = refl
no-source-status-as-physical-fork : lookup j₁₀ (Pool.handles (W.poolAt owner r5)) ≡ nothing
no-source-status-as-physical-fork = refl
no-clean-before-returned-action : W.step (W.commitClean j₁₀) r6 ≡ nothing
no-clean-before-returned-action = refl
commit-keeps-physical-body-running : lookup j₁₀ (Pool.handles (W.poolAt owner r8)) ≡ just Pool.bodyRunning
commit-keeps-physical-body-running = refl
commit-frees-responder-slot : W.active owner Mux.responderJob 1 (W.jobs r8) ≡ false
commit-frees-responder-slot = refl
no-publication-before-job-body-return : W.step (W.publishProtocol j₁₀) r8 ≡ nothing
no-publication-before-job-body-return = refl
no-second-body-return : W.step (W.returnProtocol j₁₀) r9 ≡ nothing
no-second-body-return = refl
no-deregister-before-registration : W.step (W.deregisterProtocol j₁₀) r10 ≡ nothing
no-deregister-before-registration = refl
no-async-result-before-deregister : W.step (W.asyncProtocolResult j₁₀) r11 ≡ nothing
no-async-result-before-deregister = refl
monitor-blocked-by-parent-insertion : W.step (W.control owner W.sampleTracer) r6 ≡ nothing
monitor-blocked-by-parent-insertion = refl
no-raw-responder-fork : W.step (W.run (U.run (B.handler (H.run (M.igStep (IG.forkResponder mid)))))) r5 ≡ nothing
no-raw-responder-fork = refl
no-raw-protocol-outcome : W.step (W.run (U.run (B.handler (H.run (M.igStep (IG.finishProtocol mid 1 clean)))))) r6 ≡ nothing
no-raw-protocol-outcome = refl
no-raw-number-publication : W.step (W.run (U.run (B.handler (H.run (M.igStep (IG.publishJobResult mid 1)))))) r9 ≡ nothing
no-raw-number-publication = refl
no-raw-occurrence-publication : W.step (W.run (U.run (B.handler (H.run (M.igStep (IG.publishJobOccurrence mid 0)))))) r9 ≡ nothing
no-raw-occurrence-publication = refl
no-raw-physical-result-consumption : W.step (W.run (U.run (B.handler (H.run (M.igStep (IG.monitorCompletion mid)))))) r10 ≡ nothing
no-raw-physical-result-consumption = refl
no-arbitrary-startup-result : W.step (W.run (U.startupStep owner (S.child (S.bodyReturned j₀ rPayload)))) z12 ≡ nothing
no-arbitrary-startup-result = refl
same-pool-keeps-engines : Pool.registered (W.poolAt owner r13) ≡ j₁ ∷ j₀ ∷ []
same-pool-keeps-engines = refl
no-separate-protocol-pool : lookup j₁₀ (Pool.handles (W.poolAt owner r13)) ≡ just (Pool.resultAvailable Pool.normalExit)
no-separate-protocol-pool = refl
no-foreign-owner : W.step (W.forkInitiator (ident 999) j₁₁ r₁ 1) z12 ≡ nothing
no-foreign-owner = refl
no-foreign-result : W.step (W.returnProtocol j₂₀) r8 ≡ nothing
no-foreign-result = refl

-- Observed initiator forks share the same physical pool but keep a distinct
-- (direction,number) slot. Clean frees it before the old body returns; errors
-- retain it even after publication. These are the stated new-component events.
iOld iNew : RunResult → T.TypedResult
iOld result = T.protocolCompletion Mux.initiatorJob 1 r₁ result
iNew result = T.protocolCompletion Mux.initiatorJob 1 r₂ result
iJob : RunId → T.BodyPhase → T.ProtocolJob
iJob gen phase = T.protocolJob owner mid Mux.initiatorJob 1 gen phase
rRegistered : Pool.State
rRegistered = record rFork { registered = j₁₀ ∷ j₁ ∷ j₀ ∷ []; parentFork = nothing }
iFork iRegistered nFork nRegistered nReturned nPublished oldReturned oldPublished mixedReturned mixedPublished : Pool.State
iFork = record (physical j₁₁ Pool.bodyRunning rRegistered) { parentFork = just j₁₁ }
iRegistered = record iFork { registered = j₁₁ ∷ j₁₀ ∷ j₁ ∷ j₀ ∷ []; parentFork = nothing }
nFork = record (physical j₁₂ Pool.bodyRunning iRegistered) { parentFork = just j₁₂ }
nRegistered = record nFork { registered = j₁₂ ∷ j₁₁ ∷ j₁₀ ∷ j₁ ∷ j₀ ∷ []; parentFork = nothing }
nReturned = physical j₁₂ (Pool.bodyReturned (iNew (errored err))) nRegistered
nPublished = record (physical j₁₂ (Pool.deregisterPending Pool.normalExit) nReturned) { completions = iNew (errored err) ∷ [] }
oldReturned = physical j₁₁ (Pool.bodyReturned (iOld clean)) nPublished
oldPublished = record (physical j₁₁ (Pool.deregisterPending Pool.normalExit) oldReturned)
  { completions = iNew (errored err) ∷ iOld clean ∷ [] }
mixedReturned = physical j₀ (Pool.bodyReturned (T.infraMuxer (errorId 88))) oldPublished
mixedPublished = record (physical j₀ (Pool.deregisterPending Pool.normalExit) mixedReturned)
  { completions = iNew (errored err) ∷ iOld clean ∷ T.infraMuxer (errorId 88) ∷ [] }
rJobs iJobs iWait iClean newJobs newError : Store JobId T.ProtocolJob
rJobs = (j₁₀ , rJob T.executing) ∷ []
iJobs = put j₁₁ (iJob r₁ T.executing) rJobs
iWait = put j₁₁ (iJob r₁ T.waitingEgress) rJobs
iClean = put j₁₁ (iJob r₁ (T.resultCaptured clean)) rJobs
newJobs = put j₁₂ (iJob r₂ T.executing) iClean
newError = put j₁₂ (iJob r₂ (T.resultCaptured (errored err))) iClean
x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W.State
x0 = snapshot (sourceMux m6 messages) rRegistered rJobs []
x1 = snapshot (sourceMux m6 messages) iFork iJobs []
x2 = snapshot (sourceMux m6 messages) iRegistered iJobs []
x3 = snapshot (sourceMux m6 messages) iRegistered iWait []
x4 = snapshot (sourceMux m6 messages) iRegistered iClean []
x5 = snapshot (sourceMux m6 messages) nFork newJobs []
x6 = snapshot (sourceMux m6 messages) nRegistered newJobs []
x7 = snapshot (sourceMux m6 messages) nRegistered newError []
x8 = snapshot (sourceMux m6 messages) nReturned newError []
x9 = snapshot (sourceMux m6 messages) nPublished newError []
x10 = snapshot (sourceMux m6 messages) oldReturned newError []
x11 = snapshot (sourceMux m6 messages) oldPublished newError []
x12 = snapshot (sourceMux m6 messages) mixedReturned newError []
x13 = snapshot (sourceMux m6 messages) mixedPublished newError []
cross0 : W.step (W.registerProtocol j₁₀) r6 ≡ just x0
cross0 = refl
cross1 : W.step (W.forkInitiator owner j₁₁ r₁ 1) x0 ≡ just x1
cross1 = refl
cross2 : W.step (W.registerProtocol j₁₁) x1 ≡ just x2
cross2 = refl
cross3 : W.step (W.protocolReturned j₁₁) x2 ≡ just x3
cross3 = refl
cross4 : W.step (W.commitClean j₁₁) x3 ≡ just x4
cross4 = refl
cross5 : W.step (W.forkInitiator owner j₁₂ r₂ 1) x4 ≡ just x5
cross5 = refl
cross6 : W.step (W.registerProtocol j₁₂) x5 ≡ just x6
cross6 = refl
cross7 : W.step (W.protocolException j₁₂ err) x6 ≡ just x7
cross7 = refl
cross8 : W.step (W.returnProtocol j₁₂) x7 ≡ just x8
cross8 = refl
cross9 : W.step (W.publishProtocol j₁₂) x8 ≡ just x9
cross9 = refl
cross10 : W.step (W.returnProtocol j₁₁) x9 ≡ just x10
cross10 = refl
cross11 : W.step (W.publishProtocol j₁₁) x10 ≡ just x11
cross11 = refl
cross12 : W.step (W.infrastructureReturn owner T.muxer (errorId 88)) x11 ≡ just x12
cross12 = refl
cross13 : W.step (W.publishInfra owner T.muxer) x12 ≡ just x13
cross13 = refl
crossPathActions : List W.Action
crossPathActions = (W.registerProtocol j₁₀) ∷ (W.forkInitiator owner j₁₁ r₁ 1) ∷ (W.registerProtocol j₁₁) ∷ (W.protocolReturned j₁₁) ∷ (W.commitClean j₁₁) ∷ (W.forkInitiator owner j₁₂ r₂ 1) ∷ (W.registerProtocol j₁₂) ∷ (W.protocolException j₁₂ err) ∷ (W.returnProtocol j₁₂) ∷ (W.publishProtocol j₁₂) ∷ (W.returnProtocol j₁₁) ∷ (W.publishProtocol j₁₁) ∷ (W.infrastructureReturn owner T.muxer (errorId 88)) ∷ (W.publishInfra owner T.muxer) ∷ []
crossPath : W.Executes r6 crossPathActions x13
crossPath = W.next cross0 (W.next cross1 (W.next cross2 (W.next cross3 (W.next cross4 (W.next cross5 (W.next cross6 (W.next cross7 (W.next cross8 (W.next cross9 (W.next cross10 (W.next cross11 (W.next cross12 (W.next cross13 (W.done))))))))))))))
firstForkPathActions : List W.Action
firstForkPathActions = (W.control owner W.selectCommand) ∷ (W.control owner (W.demand 1)) ∷ (W.control owner W.sampleTracer) ∷ (W.control owner W.commitTracer) ∷ (W.control owner W.finishStart) ∷ (W.forkResponder owner j₁₀ r₀) ∷ []
firstForkPath : W.Executes z12 firstForkPathActions r6
firstForkPath = W.next responder1 (W.next responder2 (W.next responder3 (W.next responder4 (W.next responder5 (W.next responder6 (W.done))))))
abstract
  initialized-mixed-generations : W.Executes b0 ((startActions ++ firstForkPathActions) ++ crossPathActions) x13
  initialized-mixed-generations = append (append initialized-start firstForkPath) crossPath
mixed-source-and-pools : Facts.Paths b0 x13
mixed-source-and-pools = Facts.exec-projects initialized-mixed-generations
same-number-both-directions-active : W.active owner Mux.responderJob 1 (W.jobs x2) ≡ true
same-number-both-directions-active = refl
same-number-initiator-independently-active : W.active owner Mux.initiatorJob 1 (W.jobs x2) ≡ true
same-number-initiator-independently-active = refl
old-clean-still-running-when-new-forked : lookup j₁₁ (Pool.handles (W.poolAt owner x5)) ≡ just Pool.bodyRunning
old-clean-still-running-when-new-forked = refl
error-slot-stays-busy-after-publication : W.active owner Mux.initiatorJob 1 (W.jobs x11) ≡ true
error-slot-stays-busy-after-publication = refl
newer-init-publishes-before-older : Pool.completions (W.poolAt owner x11) ≡ iNew (errored err) ∷ iOld clean ∷ []
newer-init-publishes-before-older = refl
initiator-publication-source-stutters : W.source x11 ≡ W.source x2
initiator-publication-source-stutters = refl
initiator-does-not-populate-responder-pending : W.pending x11 ≡ []
initiator-does-not-populate-responder-pending = refl
infra-and-protocol-share-queue : Pool.completions (W.poolAt owner x13) ≡ iNew (errored err) ∷ iOld clean ∷ T.infraMuxer (errorId 88) ∷ []
infra-and-protocol-share-queue = refl
no-engine-jobid-reuse : W.step (W.forkInitiator owner j₀ r₁ 1) x0 ≡ nothing
no-engine-jobid-reuse = refl
no-generation-reuse-across-directions : W.step (W.forkInitiator owner j₁₁ r₀ 1) x0 ≡ nothing
no-generation-reuse-across-directions = refl
no-historical-protocol-jobid-reuse : W.fresh j₁₁ r₃ x11 ≡ false
no-historical-protocol-jobid-reuse = refl
no-unconfigured-initiator : W.step (W.forkInitiator owner j₁₁ r₁ 99) x0 ≡ nothing
no-unconfigured-initiator = refl
no-engine-protocol-return : W.step (W.returnProtocol j₀) x0 ≡ nothing
no-engine-protocol-return = refl
no-engine-protocol-registration : W.step (W.registerProtocol j₁) x0 ≡ nothing
no-engine-protocol-registration = refl
errorWithoutQueue : W.State
errorWithoutQueue = snapshot (sourceMux m6 messages) (record oldPublished { completions = [] }) newError []
error-busy-even-without-queue-priority : W.step (W.forkInitiator owner j₂₀ r₃ 1) errorWithoutQueue ≡ nothing
error-busy-even-without-queue-priority = refl

-- Infrastructure can return/publish before parent registration. Complete the
-- remaining real startup and show that only the typed queue prevents selecting
-- an otherwise enabled legacy command (the legacy responder queue is empty).
eReturned eQueued eRegistered eSecond eBoth : Pool.State
eReturned = physical j₀ (Pool.bodyReturned (T.infraMuxer (errorId 88))) firstFork
eQueued = record (physical j₀ (Pool.deregisterPending Pool.normalExit) eReturned) { completions = T.infraMuxer (errorId 88) ∷ [] }
eRegistered = record eQueued { registered = j₀ ∷ []; parentFork = nothing }
eSecond = record (physical j₁ Pool.bodyRunning eRegistered) { parentFork = just j₁ }
eBoth = record eSecond { registered = j₁ ∷ j₀ ∷ []; parentFork = nothing }
e1 e2 e3 e4 e5 e6 e7 : W.State
e1 = at (Old.U.source Old.c11) (S.startupState (S.muxerForked j₀) eReturned) [] []
e2 = at (Old.U.source Old.c11) (S.startupState (S.muxerForked j₀) eQueued) [] []
e3 = at (Old.U.source Old.c11) (S.startupState (S.muxerRegistered j₀) eRegistered) [] []
e4 = at (Old.U.source Old.c11) (S.startupState (S.demuxerForked j₀ j₁) eSecond) [] []
e5 = at (Old.U.source Old.c11) (S.startupState (S.demuxerRegistered j₀ j₁) eBoth) [] []
e6 = at (Old.U.source Old.c11) (S.startupState (S.matureTraced j₀ j₁) eBoth) [] []
e7 = at (Old.U.source Old.c11) (S.startupState (S.monitoring j₀ j₁) eBoth) [] []
earlyInfra1 : W.step (W.infrastructureReturn owner T.muxer (errorId 88)) z7 ≡ just e1
earlyInfra1 = refl
earlyInfra2 : W.step (W.publishInfra owner T.muxer) e1 ≡ just e2
earlyInfra2 = refl
earlyInfra3 : W.step (W.run (U.startupStep owner S.registerMuxer)) e2 ≡ just e3
earlyInfra3 = refl
earlyInfra4 : W.step (W.run (U.startupStep owner (S.forkDemuxer j₁))) e3 ≡ just e4
earlyInfra4 = refl
earlyInfra5 : W.step (W.run (U.startupStep owner S.registerDemuxer)) e4 ≡ just e5
earlyInfra5 = refl
earlyInfra6 : W.step (W.run (U.startupStep owner S.traceMature)) e5 ≡ just e6
earlyInfra6 = refl
earlyInfra7 : W.step (W.run (U.startupStep owner S.enterMonitor)) e6 ≡ just e7
earlyInfra7 = refl
earlyInfraPathActions : List W.Action
earlyInfraPathActions = (W.infrastructureReturn owner T.muxer (errorId 88)) ∷ (W.publishInfra owner T.muxer) ∷ (W.run (U.startupStep owner S.registerMuxer)) ∷ (W.run (U.startupStep owner (S.forkDemuxer j₁))) ∷ (W.run (U.startupStep owner S.registerDemuxer)) ∷ (W.run (U.startupStep owner S.traceMature)) ∷ (W.run (U.startupStep owner S.enterMonitor)) ∷ []
earlyInfraPath : W.Executes z7 earlyInfraPathActions e7
earlyInfraPath = W.next earlyInfra1 (W.next earlyInfra2 (W.next earlyInfra3 (W.next earlyInfra4 (W.next earlyInfra5 (W.next earlyInfra6 (W.next earlyInfra7 (W.done)))))))
early-deregister-refused : W.step (W.deregisterInfra owner T.muxer) e2 ≡ nothing
early-deregister-refused = refl
role-not-yet-forked-refused : W.step (W.infrastructureReturn owner T.demuxer (errorId 88)) z7 ≡ nothing
role-not-yet-forked-refused = refl
physical-infra-head-blocks-command : W.step (W.control owner W.selectCommand) e7 ≡ nothing
physical-infra-head-blocks-command = refl
legacy-source-alone-could-select : O.advance (O.inbound (M.igStep (IG.monitorCommand mid))) (W.source e7) ≡ just (sourceMux m1 [])
legacy-source-alone-could-select = refl
lateReturned lateQueued lateFork : Pool.State
lateReturned = physical j₀ (Pool.bodyReturned (T.infraMuxer (errorId 88))) engines
lateQueued = record (physical j₀ (Pool.deregisterPending Pool.normalExit) lateReturned) { completions = T.infraMuxer (errorId 88) ∷ [] }
lateFork = record (physical j₁₀ Pool.bodyRunning lateQueued) { parentFork = just j₁₀ }
l1 l2 l3 l4 : W.State
l1 = snapshot (sourceMux m4 messages) lateReturned [] []
l2 = snapshot (sourceMux m4 messages) lateQueued [] []
l3 = snapshot (sourceMux m5 messages) lateQueued [] []
l4 = snapshot (sourceMux m6 messages) lateFork rJobs []
selectedLate1 : W.step (W.infrastructureReturn owner T.muxer (errorId 88)) r4 ≡ just l1
selectedLate1 = refl
selectedLate2 : W.step (W.publishInfra owner T.muxer) l1 ≡ just l2
selectedLate2 = refl
selectedLate3 : W.step (W.control owner W.finishStart) l2 ≡ just l3
selectedLate3 = refl
selectedLate4 : W.step (W.forkResponder owner j₁₀ r₀) l3 ≡ just l4
selectedLate4 = refl
selectedLatePathActions : List W.Action
selectedLatePathActions = (W.infrastructureReturn owner T.muxer (errorId 88)) ∷ (W.publishInfra owner T.muxer) ∷ (W.control owner W.finishStart) ∷ (W.forkResponder owner j₁₀ r₀) ∷ []
selectedLatePath : W.Executes r4 selectedLatePathActions l4
selectedLatePath = W.next selectedLate1 (W.next selectedLate2 (W.next selectedLate3 (W.next selectedLate4 (W.done))))
selected-command-fork-keeps-ready-result : Pool.completions (W.poolAt owner l4) ≡ T.infraMuxer (errorId 88) ∷ []
selected-command-fork-keeps-ready-result = refl

-- CONDITIONAL responder-frontend input: the actual older clean commit made
-- StatusIdle visible. We inject a faithful runMiniProtocolSTM start request;
-- this suffix is not claimed reachable through the current IG driver, whose
-- restart callback would ordinarily require consuming the old queued result.
olderRegistered : W.State
olderRegistered = snapshot (sourceMux cleanMux messages) rRegistered
  ((j₁₀ , rJob (T.resultCaptured clean)) ∷ []) ((owner , j₁₀ ∷ []) ∷ [])
older-registers-after-commit : W.step (W.registerProtocol j₁₀) r8 ≡ just olderRegistered
older-registers-after-commit = refl
again aMux1 aMux2 aMux3 aMux4 aMux5 aMux6 errorMux newPublishedMux allPublishedMux : Mux.Mux
again = record cleanMux { protocols = (1 , Mux.demand) ∷ []; commands = Mux.startCommand G.proto ∷ [] }
aMux1 = record again { commands = []; waiting = (1 , onDemand) ∷ [] }
aMux2 = record again { commands = []; callback = Mux.readActive (Mux.started 1) }
aMux3 = record aMux2 { callback = Mux.commitTrace true (Mux.started 1) }
aMux4 = record again { commands = []; traceCounters = just (Mux.counters (+ 2) (+ 0)); callback = Mux.afterStart 1 }
aMux5 = record aMux4 { protocols = (1 , Mux.running) ∷ []; callback = Mux.forkPending 1 }
aMux6 = record aMux5 { runningJobs = 1 ∷ []; callback = Mux.returned }
errorMux = record aMux6 { runningJobs = []; finishedJobs = (1 , clean) ∷ (1 , errored err) ∷ [] }
newPublishedMux = record errorMux { finishedJobs = (1 , clean) ∷ []; completions = Mux.jobResult Mux.responderJob 1 (errored err) ∷ [] }
allPublishedMux = record newPublishedMux { finishedJobs = []; completions = Mux.jobResult Mux.responderJob 1 (errored err) ∷ Mux.jobResult Mux.responderJob 1 clean ∷ [] }
newRJob : T.BodyPhase → T.ProtocolJob
newRJob phase = T.protocolJob owner mid Mux.responderJob 1 r₃ phase
newRPayload : T.TypedResult
newRPayload = T.protocolCompletion Mux.responderJob 1 r₃ (errored err)
oldJobs newRJobs bothCaptured : Store JobId T.ProtocolJob
oldJobs = (j₁₀ , rJob (T.resultCaptured clean)) ∷ []
newRJobs = put j₂₀ (newRJob T.executing) oldJobs
bothCaptured = put j₂₀ (newRJob (T.resultCaptured (errored err))) oldJobs
secondRFork secondRReg secondRReturn secondRPub firstRReturn firstRPub : Pool.State
secondRFork = record (physical j₂₀ Pool.bodyRunning rRegistered) { parentFork = just j₂₀ }
secondRReg = record secondRFork { registered = j₂₀ ∷ j₁₀ ∷ j₁ ∷ j₀ ∷ []; parentFork = nothing }
secondRReturn = physical j₂₀ (Pool.bodyReturned newRPayload) secondRReg
secondRPub = record (physical j₂₀ (Pool.deregisterPending Pool.normalExit) secondRReturn) { completions = newRPayload ∷ [] }
firstRReturn = physical j₁₀ (Pool.bodyReturned rPayload) secondRPub
firstRPub = record (physical j₁₀ (Pool.deregisterPending Pool.normalExit) firstRReturn) { completions = newRPayload ∷ rPayload ∷ [] }
y0 y1 y2 y3 y4 y5 y6 y7 y8 y9 y10 y11 y12 : W.State
y0 = snapshot (sourceMux again messages) rRegistered oldJobs ((owner , j₁₀ ∷ []) ∷ [])
y1 = snapshot (sourceMux aMux1 messages) rRegistered oldJobs ((owner , j₁₀ ∷ []) ∷ [])
y2 = snapshot (sourceMux aMux2 messages) rRegistered oldJobs ((owner , j₁₀ ∷ []) ∷ [])
y3 = snapshot (sourceMux aMux3 messages) rRegistered oldJobs ((owner , j₁₀ ∷ []) ∷ [])
y4 = snapshot (sourceMux aMux4 messages) rRegistered oldJobs ((owner , j₁₀ ∷ []) ∷ [])
y5 = snapshot (sourceMux aMux5 messages) rRegistered oldJobs ((owner , j₁₀ ∷ []) ∷ [])
y6 = snapshot (sourceMux aMux6 messages) secondRFork newRJobs ((owner , j₁₀ ∷ []) ∷ [])
y7 = snapshot (sourceMux aMux6 messages) secondRReg newRJobs ((owner , j₁₀ ∷ []) ∷ [])
y8 = snapshot (sourceMux errorMux messages) secondRReg bothCaptured ((owner , j₁₀ ∷ j₂₀ ∷ []) ∷ [])
y9 = snapshot (sourceMux errorMux messages) secondRReturn bothCaptured ((owner , j₁₀ ∷ j₂₀ ∷ []) ∷ [])
y10 = snapshot (sourceMux newPublishedMux messages) secondRPub bothCaptured ((owner , j₁₀ ∷ []) ∷ [])
y11 = snapshot (sourceMux newPublishedMux messages) firstRReturn bothCaptured ((owner , j₁₀ ∷ []) ∷ [])
y12 = snapshot (sourceMux allPublishedMux messages) firstRPub bothCaptured ((owner , []) ∷ [])
occurrence1 : W.step (W.control owner W.selectCommand) y0 ≡ just y1
occurrence1 = refl
occurrence2 : W.step (W.control owner (W.demand 1)) y1 ≡ just y2
occurrence2 = refl
occurrence3 : W.step (W.control owner W.sampleTracer) y2 ≡ just y3
occurrence3 = refl
occurrence4 : W.step (W.control owner W.commitTracer) y3 ≡ just y4
occurrence4 = refl
occurrence5 : W.step (W.control owner W.finishStart) y4 ≡ just y5
occurrence5 = refl
occurrence6 : W.step (W.forkResponder owner j₂₀ r₃) y5 ≡ just y6
occurrence6 = refl
occurrence7 : W.step (W.registerProtocol j₂₀) y6 ≡ just y7
occurrence7 = refl
occurrence8 : W.step (W.protocolException j₂₀ err) y7 ≡ just y8
occurrence8 = refl
occurrence9 : W.step (W.returnProtocol j₂₀) y8 ≡ just y9
occurrence9 = refl
occurrence10 : W.step (W.publishProtocol j₂₀) y9 ≡ just y10
occurrence10 = refl
occurrence11 : W.step (W.returnProtocol j₁₀) y10 ≡ just y11
occurrence11 = refl
occurrence12 : W.step (W.publishProtocol j₁₀) y11 ≡ just y12
occurrence12 = refl
conditionalOccurrencePathActions : List W.Action
conditionalOccurrencePathActions = (W.control owner W.selectCommand) ∷ (W.control owner (W.demand 1)) ∷ (W.control owner W.sampleTracer) ∷ (W.control owner W.commitTracer) ∷ (W.control owner W.finishStart) ∷ (W.forkResponder owner j₂₀ r₃) ∷ (W.registerProtocol j₂₀) ∷ (W.protocolException j₂₀ err) ∷ (W.returnProtocol j₂₀) ∷ (W.publishProtocol j₂₀) ∷ (W.returnProtocol j₁₀) ∷ (W.publishProtocol j₁₀) ∷ []
conditionalOccurrencePath : W.Executes y0 conditionalOccurrencePathActions y12
conditionalOccurrencePath = W.next occurrence1 (W.next occurrence2 (W.next occurrence3 (W.next occurrence4 (W.next occurrence5 (W.next occurrence6 (W.next occurrence7 (W.next occurrence8 (W.next occurrence9 (W.next occurrence10 (W.next occurrence11 (W.next occurrence12 (W.done))))))))))))
conditional-source-and-pool-paths : Facts.Paths y0 y12
conditional-source-and-pool-paths = Facts.exec-projects conditionalOccurrencePath
older-body-running-at-newer-source-commit : lookup j₁₀ (Pool.handles (W.poolAt owner y8)) ≡ just Pool.bodyRunning
older-body-running-at-newer-source-commit = refl
exact-newer-occurrence-index : W.locate j₂₀ (W.pendingAt owner y9) ≡ just (1 , j₁₀ ∷ [])
exact-newer-occurrence-index = refl
newer-publication-keeps-older-source-occurrence : W.muxAt mid y10 ≡ just newPublishedMux
newer-publication-keeps-older-source-occurrence = refl
responder-newer-before-older-typed-queue : Pool.completions (W.poolAt owner y12) ≡ newRPayload ∷ rPayload ∷ []
responder-newer-before-older-typed-queue = refl
responder-newer-before-older-legacy-queue : Mux.completions allPublishedMux ≡ Mux.jobResult Mux.responderJob 1 (errored err) ∷ Mux.jobResult Mux.responderJob 1 clean ∷ []
responder-newer-before-older-legacy-queue = refl
responder-error-remains-busy : W.active owner Mux.responderJob 1 (W.jobs y12) ≡ true
responder-error-remains-busy = refl
old-pending-consumed-once : W.pendingAt owner y12 ≡ []
old-pending-consumed-once = refl
no-second-newer-publication : W.step (W.publishProtocol j₂₀) y10 ≡ nothing
no-second-newer-publication = refl
newer-publication-witness : Facts.Publication j₂₀ y9 y10
newer-publication-witness = Facts.publication-observation j₂₀ y9 occurrence10

-- Generic local-event certificates are instantiated on actual initialized
-- responder/initiator actions and on the conditional responder restart suffix.
actual-responder-fork-witness : Facts.Fork owner j₁₀ r₀ r5 r6
actual-responder-fork-witness = Facts.responder-fork-observation owner j₁₀ r₀ r5 responder6
observed-initiator-fork-witness : Facts.Fork owner j₁₁ r₁ x0 x1
observed-initiator-fork-witness = Facts.initiator-fork-observation owner j₁₁ r₁ 1 x0 cross1
actual-clean-commit-witness : Facts.CompletionCommit j₁₀ r7 r8
actual-clean-commit-witness = Facts.clean-observation j₁₀ r7 responder8
actual-initiator-error-witness : Facts.CompletionCommit j₁₂ x6 x7
actual-initiator-error-witness = Facts.exception-observation j₁₂ err x6 cross7
conditional-newer-source-occurrence : Facts.ResponderOccurrence j₂₀
  (newRJob (T.resultCaptured (errored err))) (errored err) y9 (sourceMux newPublishedMux messages) (j₁₀ ∷ [])
conditional-newer-source-occurrence = Facts.responder-occurrence-observation j₂₀
  (newRJob (T.resultCaptured (errored err))) (errored err) y9 refl refl

-- Isolate publication event matching from arbitrary malformed injected values.
-- Neither a source outcome mismatch nor a wrong physical generation can pass.
wrongSource wrongPhysical foreignMetadata : W.State
wrongSource = W.setSource (sourceMux (record errorMux
  { finishedJobs = (1 , clean) ∷ (1 , clean) ∷ [] }) messages) y9
wrongPhysical = snapshot (sourceMux errorMux messages)
  (physical j₂₀ (Pool.bodyReturned (T.protocolCompletion Mux.responderJob 1 r₀ (errored err))) secondRReg)
  bothCaptured ((owner , j₁₀ ∷ j₂₀ ∷ []) ∷ [])
foreignMetadata = record r9 { jobs = put j₁₀ (record (rJob (T.resultCaptured clean)) { owner = ident 999 }) (W.jobs r9) }
source-outcome-mismatch-refused : W.step (W.publishProtocol j₂₀) wrongSource ≡ nothing
source-outcome-mismatch-refused = refl
physical-generation-mismatch-refused : W.step (W.publishProtocol j₂₀) wrongPhysical ≡ nothing
physical-generation-mismatch-refused = refl
foreign-captured-owner-publication-refused : W.step (W.publishProtocol j₁₀) foreignMetadata ≡ nothing
foreign-captured-owner-publication-refused = refl

-- A local cross-frame history control: freshness scans every historical pool,
-- even when the selected pool has never contained that physical JobId.
foreignHistory : W.State
foreignHistory = record x0 { base = record (W.base x0) { frames =
  U.frames (W.base x0) ++ ((ident 999 , U.frame Prior.captured outbound Old.ps duplex
    (U.promisePublished (ident 99) (ident 99))
    (S.startupState (S.monitoring (ident 98) j₂₀)
      (record Pool.initial { handles = (j₂₀ , Pool.resultAvailable Pool.normalExit) ∷ [] }))) ∷ []) } }
foreign-history-id-reuse-refused : W.step (W.forkInitiator owner j₂₀ r₁ 1) foreignHistory ≡ nothing
foreign-history-id-reuse-refused = refl

-- Extend initialized prefixes to the early infrastructure and late selected-
-- command branches; these observations do not depend on an injected live pool.
startupForkActions : List W.Action
startupForkActions = W.run (U.startupStep owner S.allocateBuffer) ∷
  W.run (U.startupStep owner S.createBearer) ∷ W.run (U.startupStep owner S.enterRun) ∷
  W.run (U.startupStep owner S.traceStarting) ∷ W.run (U.startupStep owner S.allocateEgress) ∷
  W.run (U.startupStep owner S.openPool) ∷ W.run (U.startupStep owner (S.forkMuxer j₀)) ∷ []
startupForkPath : W.Executes c11 startupForkActions z7
startupForkPath = W.next startup1 (W.next startup2 (W.next startup3 (W.next startup4
  (W.next startup5 (W.next startup6 (W.next startup7 W.done))))))
abstract
  initialized-early-infra : W.Executes b0
    ((((birthPathActions ++ publicationPathActions) ++ callerPathActions) ++ startupForkActions) ++ earlyInfraPathActions) e7
  initialized-early-infra = append (append (append (append birthPath publicationPath) callerPath) startupForkPath) earlyInfraPath
initialized-early-infra-pool : Facts.PTrace Pool.initial (W.poolAt owner e7)
initialized-early-infra-pool = Facts.pool-from-initial actual-initializer initialized-early-infra owner
selectedActions : List W.Action
selectedActions = W.control owner W.selectCommand ∷ W.control owner (W.demand 1) ∷
  W.control owner W.sampleTracer ∷ W.control owner W.commitTracer ∷ []
selectedPath : W.Executes z12 selectedActions r4
selectedPath = W.next responder1 (W.next responder2 (W.next responder3 (W.next responder4 W.done)))
abstract
  initialized-selected-late-result : W.Executes b0 ((startActions ++ selectedActions) ++ selectedLatePathActions) l4
  initialized-selected-late-result = append (append initialized-start selectedPath) selectedLatePath
initialized-selected-late-pool : Facts.PTrace Pool.initial (W.poolAt owner l4)
initialized-selected-late-pool = Facts.pool-from-initial actual-initializer initialized-selected-late-result owner

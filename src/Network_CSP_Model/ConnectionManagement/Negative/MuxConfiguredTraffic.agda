{-# OPTIONS --guardedness #-}

-- Initialized configured-mux traffic: a scheduled mux is configured before
-- publication, its configured startup binds Direct/Scheduled lane muxers and
-- the demuxer, and a responder's payload is taken, sealed and written by the
-- actual Direct lane muxer before clean completion. No grants/M4 behaviour.
module ConnectionManagement.Negative.MuxConfiguredTraffic where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_; take)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; suc)
open import Data.Product using (_×_; _,_)
open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (job; worker; mux)
open import ConnectionManagement.Store using (Store; lookup)
open import ConnectionManagement.IGTypes using (clean)
import ConnectionManagement.State as Shared
import ConnectionManagement.MuxProtocolJobs as W
module U = W.U
module S = W.Startup
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxEgress as E
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.Negative.MuxProtocolJobs as Plain
import ConnectionManagement.Negative.MuxProtocolFixtures as Old
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.IGRegistration as IG

owner : WorkerId
owner = Plain.owner
plan : E.Layout
plan = E.scheduledLayout false
-- Duplex protocol 1: initiator demand on Scheduled, responder demand on Direct.
keys : List (Mux.ProtocolKey × E.Lane)
keys = ((1 , Mux.initiatorJob) , E.scheduledLane) ∷ ((1 , Mux.responderJob) , E.directLane) ∷ []
st : S.Action → W.Action
st a = W.run (U.startupStep owner a)
direct scheduled demux responder : JobId
direct = ident 30
scheduled = ident 31
demux = ident 32
responder = Plain.j₁₀

publication : List W.Action
publication = W.run (U.negotiate owner Old.ps duplex) ∷ W.run (U.allocateHandle owner (ident 0) Plain.mid) ∷
  W.run (U.configureMux owner plan 16 1000 keys) ∷ W.run (U.publishSuccess owner) ∷ []
startup : List W.Action
startup = st S.allocateBuffer ∷ st S.createBearer ∷ st S.enterRun ∷ st S.traceStarting ∷ st S.allocateEgress ∷
  st (S.configureStartup plan) ∷ st S.openPool ∷
  st (S.forkConfigured direct) ∷ st S.registerConfigured ∷ st (S.forkConfigured scheduled) ∷ st S.registerConfigured ∷
  st (S.forkConfigured demux) ∷ st S.registerConfigured ∷ st S.traceConfiguredMature ∷ st S.enterConfiguredMonitor ∷ []
fork : List W.Action
fork = W.control owner W.selectCommand ∷ W.control owner (W.demand 1) ∷ W.control owner W.sampleTracer ∷
  W.control owner W.commitTracer ∷ W.control owner W.finishStart ∷ W.forkResponder owner responder Plain.r₀ ∷
  W.enterProtocolBody responder ∷ W.appendProtocolPayload responder 5 ∷ []
traffic : List W.Action
traffic = W.egressMuxer owner (Mux.Egress.takeFirst E.directLane) ∷ W.protocolReturned responder ∷
  W.egressMuxer owner (Mux.Egress.selectDemand 0) ∷ W.egressMuxer owner (Mux.Egress.writeAccount 0) ∷
  W.commitClean responder ∷ []

-- Literal states: the plain fixture's actual states with ONLY the source mux
-- egress replaced by the configured profile, and configured startup frames
-- computed by small kernel executions. Each step below is one actual refl.
configuredEgress : Mux.Egress.State
configuredEgress with Mux.Egress.initial plan 16 1000 keys
... | just e = e
... | nothing = Mux.plainEgress []
cfgSource : O.Configuration → O.Configuration
cfgSource c with lookup Plain.mid (IG.muxes (IG.execution (M.inboundGovernor (O.core c))))
... | nothing = c
... | just m = record c { core = record (O.core c) { inboundGovernor =
  IG.setMux Plain.mid (record m { egress = configuredEgress }) (M.inboundGovernor (O.core c)) } }
cfg : W.State → W.State
cfg s = W.setSource (cfgSource (W.source s)) s

configure14 : W.step (W.run (U.configureMux owner plan 16 1000 keys)) Plain.b14 ≡ just (cfg Plain.b14)
configure14 = refl
publish15 : W.step (W.run (U.publishSuccess owner)) (cfg Plain.b14) ≡ just (cfg Plain.b15)
publish15 = refl
caller1 : W.step (W.run (U.run (B.outbound (O.acquire Plain.Fixture.caller A.readCounters)))) (cfg Plain.b15) ≡ just (cfg Plain.c1)
caller1 = refl
caller2 : W.step (W.run (U.run (B.outbound (O.acquire Plain.Fixture.caller A.readResult)))) (cfg Plain.c1) ≡ just (cfg Plain.c2)
caller2 = refl
caller3 : W.step (W.run (U.run (B.outbound (O.acquire Plain.Fixture.caller A.commitHandshake)))) (cfg Plain.c2) ≡ just (cfg Plain.c3)
caller3 = refl
caller4 : W.step (W.run (U.run (B.outbound (O.acquire Plain.Fixture.caller A.readCounters)))) (cfg Plain.c3) ≡ just (cfg Plain.c4)
caller4 = refl
caller5 : W.step (W.run (U.run (B.outbound (O.acquire Plain.Fixture.caller A.returnResult)))) (cfg Plain.c4) ≡ just (cfg Plain.c5)
caller5 = refl
caller6 : W.step (W.run (U.run (B.handler (H.run (M.igStep (IG.captureTime 0)))))) (cfg Plain.c5) ≡ just (cfg Plain.c6)
caller6 = refl
caller7 : W.step (W.run (U.run (B.handler (H.run (M.igStep IG.registerInactivity))))) (cfg Plain.c6) ≡ just (cfg Plain.c7)
caller7 = refl
caller8 : W.step (W.run (U.run (B.handler (H.run (M.igStep IG.selectBatch))))) (cfg Plain.c7) ≡ just (cfg Plain.c8)
caller8 = refl
caller9 : W.step (W.run (U.run (B.handler (H.run (M.igStep IG.readEvent))))) (cfg Plain.c8) ≡ just (cfg Plain.c9)
caller9 = refl
caller10 : W.step (W.run (U.run (B.handler (H.run (M.igStep IG.registerIdleTimer))))) (cfg Plain.c9) ≡ just (cfg Plain.c10)
caller10 = refl
caller11 : W.step (W.run (U.run (B.handler (H.run (M.igStep IG.runResponders))))) (cfg Plain.c10) ≡ just (cfg Plain.c11)
caller11 = refl

-- Configured startup frames: kernel executions from the published stage.
kexec : List S.Action → S.State → S.State
kexec [] s = s
kexec (a ∷ as) s with S.step a s
... | just t = kexec as t
... | nothing = s
startupKernel : List S.Action
startupKernel = S.allocateBuffer ∷ S.createBearer ∷ S.enterRun ∷ S.traceStarting ∷ S.allocateEgress ∷
  S.configureStartup plan ∷ S.openPool ∷
  S.forkConfigured direct ∷ S.registerConfigured ∷ S.forkConfigured scheduled ∷ S.registerConfigured ∷
  S.forkConfigured demux ∷ S.registerConfigured ∷ S.traceConfiguredMature ∷ S.enterConfiguredMonitor ∷ []
stage : ℕ → S.State
stage n = kexec (take n startupKernel) Plain.publishedStage
z : ℕ → W.State
z n = cfg (Plain.at (Old.U.source Old.c11) (stage n) [] [])
s1 : W.step (st S.allocateBuffer) (cfg Plain.c11) ≡ just (z 1)
s1 = refl
s2 : W.step (st S.createBearer) (z 1) ≡ just (z 2)
s2 = refl
s3 : W.step (st S.enterRun) (z 2) ≡ just (z 3)
s3 = refl
s4 : W.step (st S.traceStarting) (z 3) ≡ just (z 4)
s4 = refl
s5 : W.step (st S.allocateEgress) (z 4) ≡ just (z 5)
s5 = refl
s6 : W.step (st (S.configureStartup plan)) (z 5) ≡ just (z 6)
s6 = refl
s7 : W.step (st S.openPool) (z 6) ≡ just (z 7)
s7 = refl
s8 : W.step (st (S.forkConfigured direct)) (z 7) ≡ just (z 8)
s8 = refl
s9 : W.step (st S.registerConfigured) (z 8) ≡ just (z 9)
s9 = refl
s10 : W.step (st (S.forkConfigured scheduled)) (z 9) ≡ just (z 10)
s10 = refl
s11 : W.step (st S.registerConfigured) (z 10) ≡ just (z 11)
s11 = refl
s12 : W.step (st (S.forkConfigured demux)) (z 11) ≡ just (z 12)
s12 = refl
s13 : W.step (st S.registerConfigured) (z 12) ≡ just (z 13)
s13 = refl
s14 : W.step (st S.traceConfiguredMature) (z 13) ≡ just (z 14)
s14 = refl
s15 : W.step (st S.enterConfiguredMonitor) (z 14) ≡ just (z 15)
s15 = refl
monitored : W.State
monitored = z 15

publicationPath : W.Executes Plain.b12 publication (cfg Plain.b15)
publicationPath = W.next Plain.success13 (W.next Plain.success14 (W.next configure14 (W.next publish15 W.done)))
callerPath : W.Executes (cfg Plain.b15) Plain.callerPathActions (cfg Plain.c11)
callerPath = W.next caller1 (W.next caller2 (W.next caller3 (W.next caller4 (W.next caller5 (W.next caller6
  (W.next caller7 (W.next caller8 (W.next caller9 (W.next caller10 (W.next caller11 W.done))))))))))
startupPath : W.Executes (cfg Plain.c11) startup monitored
startupPath = W.next s1 (W.next s2 (W.next s3 (W.next s4 (W.next s5 (W.next s6 (W.next s7 (W.next s8 (W.next s9
  (W.next s10 (W.next s11 (W.next s12 (W.next s13 (W.next s14 (W.next s15 W.done))))))))))))))
append : ∀ {p as q bs r} → W.Executes p as q → W.Executes q bs r → W.Executes p (as ++ bs) r
append W.done tail = tail
append (W.next eq path) tail = W.next eq (append path tail)
segment : List W.Action
segment = fork ++ traffic

-- The traffic segment uses literal snapshots shaped like the plain fixture's
-- responder states: the same source muxes with the configured egress, the
-- configured monitoring frame and its pool. Egress updates are kernel steps.
cfgMonitor : S.State
cfgMonitor = stage 15
estep : Mux.Egress.Action → Mux.Egress.State → Mux.Egress.State
estep a e with Mux.Egress.step a e
... | just t = t
... | nothing = e
e1 e2 e3 e4 e5 : Mux.Egress.State
e1 = estep (Mux.Egress.createWanton (serial responder) (1 , Mux.responderJob)) configuredEgress
e2 = estep (Mux.Egress.appendPayload (serial responder) 5) e1
e3 = estep (Mux.Egress.takeFirst E.directLane) e2
e4 = estep (Mux.Egress.selectDemand 0) e3
e5 = estep (Mux.Egress.writeAccount 0) e4
csnap : Mux.Egress.State → Mux.Mux → List Shared.IGEvent → W.Pool.State → Store JobId Types.ProtocolJob → Store WorkerId (List JobId) → W.State
csnap e m queue p jobs pending = Plain.at (Plain.sourceMux (record m { egress = e }) queue) (record cfgMonitor { pool = p }) jobs pending
pool₀ forkedPool : W.Pool.State
pool₀ = S.pool cfgMonitor
forkedPool = record (Plain.physical responder W.Pool.bodyRunning pool₀) { parentFork = just responder }
job : Types.BodyPhase → Types.ProtocolJob
job = Plain.rJob
x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 : W.State
x1 = csnap configuredEgress Plain.m1 [] pool₀ [] []
x2 = csnap configuredEgress Plain.m2 [] pool₀ [] []
x3 = csnap configuredEgress Plain.m3 [] pool₀ [] []
x4 = csnap configuredEgress Plain.m4 Plain.messages pool₀ [] []
x5 = csnap configuredEgress Plain.m5 Plain.messages pool₀ [] []
x6 = csnap configuredEgress Plain.m6 Plain.messages forkedPool ((responder , job Types.executing) ∷ []) []
x7 = csnap e1 Plain.m6 Plain.messages forkedPool ((responder , job Types.executing) ∷ []) []
x8 = csnap e2 Plain.m6 Plain.messages forkedPool ((responder , job Types.executing) ∷ []) []
x9 = csnap e3 Plain.m6 Plain.messages forkedPool ((responder , job Types.executing) ∷ []) []
x10 = csnap e3 Plain.m6 Plain.messages forkedPool ((responder , job Types.waitingEgress) ∷ []) []
x11 = csnap e4 Plain.m6 Plain.messages forkedPool ((responder , job Types.waitingEgress) ∷ []) []
x12 = csnap e5 Plain.m6 Plain.messages forkedPool ((responder , job Types.waitingEgress) ∷ []) []
x13 = csnap e5 Plain.cleanMux Plain.messages forkedPool ((responder , job (Types.resultCaptured clean)) ∷ []) ((owner , responder ∷ []) ∷ [])
t1 : W.step (W.control owner W.selectCommand) monitored ≡ just x1
t1 = refl
t2 : W.step (W.control owner (W.demand 1)) x1 ≡ just x2
t2 = refl
t3 : W.step (W.control owner W.sampleTracer) x2 ≡ just x3
t3 = refl
t4 : W.step (W.control owner W.commitTracer) x3 ≡ just x4
t4 = refl
t5 : W.step (W.control owner W.finishStart) x4 ≡ just x5
t5 = refl
t6 : W.step (W.forkResponder owner responder Plain.r₀) x5 ≡ just x6
t6 = refl
t7 : W.step (W.enterProtocolBody responder) x6 ≡ just x7
t7 = refl
t8 : W.step (W.appendProtocolPayload responder 5) x7 ≡ just x8
t8 = refl
t9 : W.step (W.egressMuxer owner (Mux.Egress.takeFirst E.directLane)) x8 ≡ just x9
t9 = refl
t10 : W.step (W.protocolReturned responder) x9 ≡ just x10
t10 = refl
t11 : W.step (W.egressMuxer owner (Mux.Egress.selectDemand 0)) x10 ≡ just x11
t11 = refl
t12 : W.step (W.egressMuxer owner (Mux.Egress.writeAccount 0)) x11 ≡ just x12
t12 = refl
t13 : W.step (W.commitClean responder) x12 ≡ just x13
t13 = refl
segmentPath : W.Executes monitored segment x13
segmentPath = W.next t1 (W.next t2 (W.next t3 (W.next t4 (W.next t5 (W.next t6 (W.next t7 (W.next t8
  (W.next t9 (W.next t10 (W.next t11 (W.next t12 (W.next t13 W.done))))))))))))
abstract
  initialized-configured-traffic : W.Executes Plain.b0
    ((Plain.birthPathActions ++ publication) ++ (Plain.callerPathActions ++ (startup ++ segment))) x13
  initialized-configured-traffic = append (append Plain.birthPath publicationPath)
    (append callerPath (append startupPath segmentPath))

frame : W.State → Maybe U.Frame
frame s = lookup owner (U.frames (W.base s))
held sent : W.State → Maybe (Maybe Mux.Egress.Cell)
held s with W.muxAt Plain.mid s
... | nothing = nothing
... | just m = just (lookup (1 , Mux.responderJob) (Mux.Egress.cells (Mux.egress m)))
sent = held

-- The Direct lane muxer is resolved from the actual layout, batch lane and binding.
direct-worker : ∀ {f} → frame x8 ≡ just f →
  W.laneWorker f (Mux.Egress.takeFirst E.directLane) x8 ≡ just (Plain.mid , direct)
direct-worker refl = refl
scheduled-worker : ∀ {f} → frame x8 ≡ just f →
  W.laneWorker f (Mux.Egress.takeFirst E.scheduledLane) x8 ≡ just (Plain.mid , scheduled)
scheduled-worker refl = refl
-- The responder's demand is on Direct only: the Scheduled muxer has nothing to take.
scheduled-lane-empty : W.step (W.egressMuxer owner (Mux.Egress.takeFirst E.scheduledLane)) x8 ≡ nothing
scheduled-lane-empty = refl
-- While its batch is held the returned responder cannot complete cleanly.
held-blocks-clean : W.step (W.commitClean responder) x10 ≡ nothing
held-blocks-clean = refl
-- After the actual write the responder key cell is released with header-inclusive bytes.
released-and-credited : held x12 ≡ just (just (Mux.Egress.cell E.directLane (+ 0) 13))
released-and-credited = refl

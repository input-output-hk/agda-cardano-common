{-# OPTIONS --guardedness #-}

-- Optional mux byte counters (Counters.hs withByteCells): a configured mux run
-- registers its cells atomically just before pool entry, and retires them only
-- after the whole pool bracket and its continuation (scopeDone). The handler's
-- exit cannot observe the run's return while its row is live.
module ConnectionManagement.Negative.MuxConfiguredCounters where

open import Agda.Builtin.Reflection using (Term; TC; normalise; unify; bindTC)
open import Agda.Builtin.Unit using (⊤)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (job; worker; mux)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.MuxProtocolJobs as W
module U = W.U
module S = W.Startup
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.MuxResultMonitor as ResultMonitor
import ConnectionManagement.MuxHandlerExit as ExitModel
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Machine as M
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.MuxEgress as E
import ConnectionManagement.Negative.MuxResultMonitor as F
import ConnectionManagement.Negative.MuxGroupShutdown as GF
import ConnectionManagement.Negative.MuxProtocolJobs as Plain
import ConnectionManagement.Negative.MuxConfiguredTraffic as C
module G = Group F.bearerClosed
module MM = ResultMonitor F.bearerClosed
module X = ExitModel F.bearerClosed

-- One-step snapshot builder (see MuxConfiguredWholeClose); edges stay refl.
macro
  snapshot : Term → Term → TC ⊤
  snapshot t hole = bindTC (normalise t) (unify hole)
pafter : W.Action → W.State → W.State
pafter a s with W.step a s
... | just t = t
... | nothing = s
gafter : G.Action → G.State → G.State
gafter a s with G.step a s
... | just t = t
... | nothing = s

owner : WorkerId
owner = C.owner
st : S.Action → W.Action
st a = W.run (U.startupStep owner a)
rows : O.Configuration → List _
rows c = IG.counterRows (IG.execution (M.inboundGovernor (O.core c)))
retired : O.Configuration → List _
retired c = IG.retiredSent (IG.execution (M.inboundGovernor (O.core c)))
isJust : ∀ {A : Set} → Maybe A → Bool
isJust (just _) = true
isJust nothing = false

-- Protocol layer: register at cfgBeforePool, then finish the configured startup.
k0 k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 : W.State
k0 = C.z 6
k1 = snapshot (pafter (W.run (U.registerCounters owner)) k0)
k2 = snapshot (pafter (st S.openPool) k1)
k3 = snapshot (pafter (st (S.forkConfigured C.direct)) k2)
k4 = snapshot (pafter (st S.registerConfigured) k3)
k5 = snapshot (pafter (st (S.forkConfigured C.scheduled)) k4)
k6 = snapshot (pafter (st S.registerConfigured) k5)
k7 = snapshot (pafter (st (S.forkConfigured C.demux)) k6)
k8 = snapshot (pafter (st S.registerConfigured) k7)
k9 = snapshot (pafter (st S.traceConfiguredMature) k8)
k10 = snapshot (pafter (st S.enterConfiguredMonitor) k9)
p1 : W.step (W.run (U.registerCounters owner)) k0 ≡ just k1
p1 = refl
p2 : W.step (st S.openPool) k1 ≡ just k2
p2 = refl
p3 : W.step (st (S.forkConfigured C.direct)) k2 ≡ just k3
p3 = refl
p4 : W.step (st S.registerConfigured) k3 ≡ just k4
p4 = refl
p5 : W.step (st (S.forkConfigured C.scheduled)) k4 ≡ just k5
p5 = refl
p6 : W.step (st S.registerConfigured) k5 ≡ just k6
p6 = refl
p7 : W.step (st (S.forkConfigured C.demux)) k6 ≡ just k7
p7 = refl
p8 : W.step (st S.registerConfigured) k7 ≡ just k8
p8 = refl
p9 : W.step (st S.traceConfiguredMature) k8 ≡ just k9
p9 = refl
p10 : W.step (st S.enterConfiguredMonitor) k9 ≡ just k10
p10 = refl
registeredActions : List W.Action
registeredActions = (Plain.birthPathActions ++ C.publication) ++ (Plain.callerPathActions ++
  (st S.allocateBuffer ∷ st S.createBearer ∷ st S.enterRun ∷ st S.traceStarting ∷ st S.allocateEgress ∷
   st (S.configureStartup C.plan) ∷ W.run (U.registerCounters owner) ∷ st S.openPool ∷
   st (S.forkConfigured C.direct) ∷ st S.registerConfigured ∷ st (S.forkConfigured C.scheduled) ∷ st S.registerConfigured ∷
   st (S.forkConfigured C.demux) ∷ st S.registerConfigured ∷ st S.traceConfiguredMature ∷ st S.enterConfiguredMonitor ∷ []))
abstract
  initialized-registered : W.Executes Plain.b0 registeredActions k10
  initialized-registered = C.append (C.append Plain.birthPath C.publicationPath) (C.append C.callerPath
    (W.next C.s1 (W.next C.s2 (W.next C.s3 (W.next C.s4 (W.next C.s5 (W.next C.s6
    (W.next p1 (W.next p2 (W.next p3 (W.next p4 (W.next p5 (W.next p6 (W.next p7 (W.next p8 (W.next p9 (W.next p10 W.done)))))))))))))))))

-- Registration takes row 0 for the actual mux, exactly once and only before pool entry.
row-registered : IG.rowOf Plain.mid (rows (W.source k1)) ≡ just 0
row-registered = refl
second-registration-refused : W.step (W.run (U.registerCounters owner)) k1 ≡ nothing
second-registration-refused = refl
registration-after-pool-entry-refused : W.step (W.run (U.registerCounters owner)) (C.z 7) ≡ nothing
registration-after-pool-entry-refused = refl

-- Group layer: graceful shutdown and whole close, then retirement at scopeDone.
g0 : G.State
g0 = GF.wrap (F.wrap k10)
g1 : G.State
g1 = snapshot (gafter (G.run (MM.run (W.control owner W.selectCommand))) g0)
q1 : G.step (G.run (MM.run (W.control owner W.selectCommand))) g0 ≡ just g1
q1 = refl
g2 : G.State
g2 = snapshot (gafter (G.requestShutdown owner) g1)
q2 : G.step (G.requestShutdown owner) g1 ≡ just g2
q2 = refl
g3 : G.State
g3 = snapshot (gafter (G.selectShutdown owner) g2)
q3 : G.step (G.selectShutdown owner) g2 ≡ just g3
q3 = refl
g4 : G.State
g4 = snapshot (gafter (G.observeStoppingTrace owner) g3)
q4 : G.step (G.observeStoppingTrace owner) g3 ≡ just g4
q4 = refl
g5 : G.State
g5 = snapshot (gafter (G.writeStopping owner) g4)
q5 : G.step (G.writeStopping owner) g4 ≡ just g5
q5 = refl
g6 : G.State
g6 = snapshot (gafter (G.captureGroup owner []) g5)
q6 : G.step (G.captureGroup owner []) g5 ≡ just g6
q6 = refl
g7 : G.State
g7 = snapshot (gafter (G.finishGroup owner) g6)
q7 : G.step (G.finishGroup owner) g6 ≡ just g7
q7 = refl
g8 : G.State
g8 = snapshot (gafter (G.drainEmpty owner) g7)
q8 : G.step (G.drainEmpty owner) g7 ≡ just g8
q8 = refl
g9 : G.State
g9 = snapshot (gafter (G.writeStopped owner) g8)
q9 : G.step (G.writeStopped owner) g8 ≡ just g9
q9 = refl
g10 : G.State
g10 = snapshot (gafter (G.observeTraceStopped owner) g9)
q10 : G.step (G.observeTraceStopped owner) g9 ≡ just g10
q10 = refl
g11 : G.State
g11 = snapshot (gafter (G.sampleStoppedTracer owner) g10)
q11 : G.step (G.sampleStoppedTracer owner) g10 ≡ just g11
q11 = refl
g12 : G.State
g12 = snapshot (gafter (G.commitStoppedTracer owner) g11)
q12 : G.step (G.commitStoppedTracer owner) g11 ≡ just g12
q12 = refl
g13 : G.State
g13 = snapshot (gafter (G.finishStoppedTrace owner) g12)
q13 : G.step (G.finishStoppedTrace owner) g12 ≡ just g13
q13 = refl
g14 : G.State
g14 = snapshot (gafter (G.beginWholeClose owner (C.demux ∷ C.scheduled ∷ C.direct ∷ [])) g13)
q14 : G.step (G.beginWholeClose owner (C.demux ∷ C.scheduled ∷ C.direct ∷ [])) g13 ≡ just g14
q14 = refl
g15 : G.State
g15 = snapshot (gafter (G.requestWholeCancel owner) g14)
q15 : G.step (G.requestWholeCancel owner) g14 ≡ just g15
q15 = refl
g16 : G.State
g16 = snapshot (gafter (G.deliverWhole owner) g15)
q16 : G.step (G.deliverWhole owner) g15 ≡ just g16
q16 = refl
g17 : G.State
g17 = snapshot (gafter (G.finishChildUnwind C.demux) g16)
q17 : G.step (G.finishChildUnwind C.demux) g16 ≡ just g17
q17 = refl
g18 : G.State
g18 = snapshot (gafter (G.run (MM.run (W.deregisterInfra owner T.demuxer))) g17)
q18 : G.step (G.run (MM.run (W.deregisterInfra owner T.demuxer))) g17 ≡ just g18
q18 = refl
g19 : G.State
g19 = snapshot (gafter (G.run (MM.run (W.asyncInfraResult owner T.demuxer))) g18)
q19 : G.step (G.run (MM.run (W.asyncInfraResult owner T.demuxer))) g18 ≡ just g19
q19 = refl
g20 : G.State
g20 = snapshot (gafter (G.joinWhole owner) g19)
q20 : G.step (G.joinWhole owner) g19 ≡ just g20
q20 = refl
g21 : G.State
g21 = snapshot (gafter (G.requestWholeCancel owner) g20)
q21 : G.step (G.requestWholeCancel owner) g20 ≡ just g21
q21 = refl
g22 : G.State
g22 = snapshot (gafter (G.deliverWhole owner) g21)
q22 : G.step (G.deliverWhole owner) g21 ≡ just g22
q22 = refl
g23 : G.State
g23 = snapshot (gafter (G.finishChildUnwind C.scheduled) g22)
q23 : G.step (G.finishChildUnwind C.scheduled) g22 ≡ just g23
q23 = refl
g24 : G.State
g24 = snapshot (gafter (G.run (MM.run (W.deregisterInfra owner (T.laneMuxer E.scheduledLane)))) g23)
q24 : G.step (G.run (MM.run (W.deregisterInfra owner (T.laneMuxer E.scheduledLane)))) g23 ≡ just g24
q24 = refl
g25 : G.State
g25 = snapshot (gafter (G.run (MM.run (W.asyncInfraResult owner (T.laneMuxer E.scheduledLane)))) g24)
q25 : G.step (G.run (MM.run (W.asyncInfraResult owner (T.laneMuxer E.scheduledLane)))) g24 ≡ just g25
q25 = refl
g26 : G.State
g26 = snapshot (gafter (G.joinWhole owner) g25)
q26 : G.step (G.joinWhole owner) g25 ≡ just g26
q26 = refl
g27 : G.State
g27 = snapshot (gafter (G.requestWholeCancel owner) g26)
q27 : G.step (G.requestWholeCancel owner) g26 ≡ just g27
q27 = refl
g28 : G.State
g28 = snapshot (gafter (G.deliverWhole owner) g27)
q28 : G.step (G.deliverWhole owner) g27 ≡ just g28
q28 = refl
g29 : G.State
g29 = snapshot (gafter (G.finishChildUnwind C.direct) g28)
q29 : G.step (G.finishChildUnwind C.direct) g28 ≡ just g29
q29 = refl
g30 : G.State
g30 = snapshot (gafter (G.run (MM.run (W.deregisterInfra owner (T.laneMuxer E.directLane)))) g29)
q30 : G.step (G.run (MM.run (W.deregisterInfra owner (T.laneMuxer E.directLane)))) g29 ≡ just g30
q30 = refl
g31 : G.State
g31 = snapshot (gafter (G.run (MM.run (W.asyncInfraResult owner (T.laneMuxer E.directLane)))) g30)
q31 : G.step (G.run (MM.run (W.asyncInfraResult owner (T.laneMuxer E.directLane)))) g30 ≡ just g31
q31 = refl
g32 : G.State
g32 = snapshot (gafter (G.joinWhole owner) g31)
q32 : G.step (G.joinWhole owner) g31 ≡ just g32
q32 = refl
g33 : G.State
g33 = snapshot (gafter (G.finishWholeClose owner) g32)
q33 : G.step (G.finishWholeClose owner) g32 ≡ just g33
q33 = refl
g34 : G.State
g34 = snapshot (gafter (G.finishNormalScope owner) g33)
q34 : G.step (G.finishNormalScope owner) g33 ≡ just g34
q34 = refl
g35 : G.State
g35 = snapshot (gafter (G.retireCounters owner) g34)
q35 : G.step (G.retireCounters owner) g34 ≡ just g35
q35 = refl
closeActions : List G.Action
closeActions = (G.run (MM.run (W.control owner W.selectCommand))) ∷ (G.requestShutdown owner) ∷ (G.selectShutdown owner) ∷ (G.observeStoppingTrace owner) ∷ (G.writeStopping owner) ∷ (G.captureGroup owner []) ∷ (G.finishGroup owner) ∷ (G.drainEmpty owner) ∷ (G.writeStopped owner) ∷ (G.observeTraceStopped owner) ∷ (G.sampleStoppedTracer owner) ∷ (G.commitStoppedTracer owner) ∷ (G.finishStoppedTrace owner) ∷ (G.beginWholeClose owner (C.demux ∷ C.scheduled ∷ C.direct ∷ [])) ∷ (G.requestWholeCancel owner) ∷ (G.deliverWhole owner) ∷ (G.finishChildUnwind C.demux) ∷ (G.run (MM.run (W.deregisterInfra owner T.demuxer))) ∷ (G.run (MM.run (W.asyncInfraResult owner T.demuxer))) ∷ (G.joinWhole owner) ∷ (G.requestWholeCancel owner) ∷ (G.deliverWhole owner) ∷ (G.finishChildUnwind C.scheduled) ∷ (G.run (MM.run (W.deregisterInfra owner (T.laneMuxer E.scheduledLane)))) ∷ (G.run (MM.run (W.asyncInfraResult owner (T.laneMuxer E.scheduledLane)))) ∷ (G.joinWhole owner) ∷ (G.requestWholeCancel owner) ∷ (G.deliverWhole owner) ∷ (G.finishChildUnwind C.direct) ∷ (G.run (MM.run (W.deregisterInfra owner (T.laneMuxer E.directLane)))) ∷ (G.run (MM.run (W.asyncInfraResult owner (T.laneMuxer E.directLane)))) ∷ (G.joinWhole owner) ∷ (G.finishWholeClose owner) ∷ (G.finishNormalScope owner) ∷ (G.retireCounters owner) ∷ []
closePath : G.Executes g0 closeActions g35
closePath = G.next q1 (G.next q2 (G.next q3 (G.next q4 (G.next q5 (G.next q6 (G.next q7 (G.next q8 (G.next q9 (G.next q10 (G.next q11 (G.next q12 (G.next q13 (G.next q14 (G.next q15 (G.next q16 (G.next q17 (G.next q18 (G.next q19 (G.next q20 (G.next q21 (G.next q22 (G.next q23 (G.next q24 (G.next q25 (G.next q26 (G.next q27 (G.next q28 (G.next q29 (G.next q30 (G.next q31 (G.next q32 (G.next q33 (G.next q34 (G.next q35 (G.done)))))))))))))))))))))))))))))))))))
gappend : ∀ {p as q bs r} → G.Executes p as q → G.Executes q bs r → G.Executes p (as ++ bs) r
gappend G.done tail = tail
gappend (G.next eq path) tail = G.next eq (gappend path tail)
abstract
  initialized-counters-retired : G.Executes (GF.wrap (F.wrap Plain.b0))
    (map G.run (map MM.run registeredActions) ++ closeActions) g35
  initialized-counters-retired = gappend (GF.lift-path (F.lift-path initialized-registered) refl) closePath

-- Retirement waits for scopeDone, happens once, and moves the row's sent totals.
retire-before-scope-refused : G.step (G.retireCounters owner) g33 ≡ nothing
retire-before-scope-refused = refl
row-live-at-scope : IG.rowOf Plain.mid (rows (G.source g34)) ≡ just 0
row-live-at-scope = refl
row-retired : IG.rowOf Plain.mid (rows (G.source g35)) ≡ nothing
row-retired = refl
second-retire-refused : G.step (G.retireCounters owner) g35 ≡ nothing
second-retire-refused = refl
-- The handler exit cannot observe the mux run's return while the row is live.
exit-waits-for-retirement : X.step (X.beginExit owner) (X.handlerExitState g34 []) ≡ nothing
exit-waits-for-retirement = refl
exit-after-retirement : isJust (X.step (X.beginExit owner) (X.handlerExitState g35 [])) ≡ true
exit-after-retirement = refl
-- No traffic was sent in this run: both registered keys retire zero bytes.
retired-totals : retired (G.source g35) ≡ ((1 , Mux.initiatorJob) , 0) ∷ ((1 , Mux.responderJob) , 0) ∷ []
retired-totals = refl

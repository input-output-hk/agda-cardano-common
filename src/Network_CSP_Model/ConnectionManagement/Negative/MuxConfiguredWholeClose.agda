{-# OPTIONS --guardedness #-}

-- Initialized whole-pool close of a configured mux: after the configured
-- startup (Direct, Scheduled lane muxers and demuxer), graceful shutdown
-- captures the actual registry and cancels, unwinds, deregisters, publishes
-- and joins all three configured infrastructure jobs before closing.
module ConnectionManagement.Negative.MuxConfiguredWholeClose where

open import Agda.Builtin.Reflection using (Term; TC; normalise; unify; bindTC)
open import Agda.Builtin.Unit using (⊤)
open import Data.Bool using (true)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (job; worker; mux)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Negative.MuxProtocolJobs as Plain
import ConnectionManagement.MuxGroupShutdown as Group
import ConnectionManagement.MuxResultMonitor as ResultMonitor
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.MuxEgress as E
import ConnectionManagement.Negative.MuxResultMonitor as F
import ConnectionManagement.Negative.MuxGroupShutdown as GF
import ConnectionManagement.Negative.MuxConfiguredTraffic as C
module W = Group F.bearerClosed
module M = ResultMonitor F.bearerClosed

-- Snapshot builder: normalise one actual step from a literal state ONCE and
-- splice the result as the next literal state. Every edge below is still an
-- ordinary refl on W.step; the macro only avoids re-evaluating a long chain.
macro
  snapshot : Term → Term → TC ⊤
  snapshot t hole = bindTC (normalise t) (unify hole)
after : W.Action → W.State → W.State
after a s with W.step a s
... | just t = t
... | nothing = s

owner : WorkerId
owner = C.owner
g0 : W.State
g0 = GF.wrap (F.wrap C.monitored)
g1 : W.State
g1 = snapshot (after (W.run (M.run (P.control owner P.selectCommand))) g0)
e1 : W.step (W.run (M.run (P.control owner P.selectCommand))) g0 ≡ just g1
e1 = refl
g2 : W.State
g2 = snapshot (after (W.requestShutdown owner) g1)
e2 : W.step (W.requestShutdown owner) g1 ≡ just g2
e2 = refl
g3 : W.State
g3 = snapshot (after (W.selectShutdown owner) g2)
e3 : W.step (W.selectShutdown owner) g2 ≡ just g3
e3 = refl
g4 : W.State
g4 = snapshot (after (W.observeStoppingTrace owner) g3)
e4 : W.step (W.observeStoppingTrace owner) g3 ≡ just g4
e4 = refl
g5 : W.State
g5 = snapshot (after (W.writeStopping owner) g4)
e5 : W.step (W.writeStopping owner) g4 ≡ just g5
e5 = refl
g6 : W.State
g6 = snapshot (after (W.captureGroup owner []) g5)
e6 : W.step (W.captureGroup owner []) g5 ≡ just g6
e6 = refl
g7 : W.State
g7 = snapshot (after (W.finishGroup owner) g6)
e7 : W.step (W.finishGroup owner) g6 ≡ just g7
e7 = refl
g8 : W.State
g8 = snapshot (after (W.drainEmpty owner) g7)
e8 : W.step (W.drainEmpty owner) g7 ≡ just g8
e8 = refl
g9 : W.State
g9 = snapshot (after (W.writeStopped owner) g8)
e9 : W.step (W.writeStopped owner) g8 ≡ just g9
e9 = refl
g10 : W.State
g10 = snapshot (after (W.observeTraceStopped owner) g9)
e10 : W.step (W.observeTraceStopped owner) g9 ≡ just g10
e10 = refl
g11 : W.State
g11 = snapshot (after (W.sampleStoppedTracer owner) g10)
e11 : W.step (W.sampleStoppedTracer owner) g10 ≡ just g11
e11 = refl
g12 : W.State
g12 = snapshot (after (W.commitStoppedTracer owner) g11)
e12 : W.step (W.commitStoppedTracer owner) g11 ≡ just g12
e12 = refl
g13 : W.State
g13 = snapshot (after (W.finishStoppedTrace owner) g12)
e13 : W.step (W.finishStoppedTrace owner) g12 ≡ just g13
e13 = refl
g14 : W.State
g14 = snapshot (after (W.beginWholeClose owner (C.demux ∷ C.scheduled ∷ C.direct ∷ [])) g13)
e14 : W.step (W.beginWholeClose owner (C.demux ∷ C.scheduled ∷ C.direct ∷ [])) g13 ≡ just g14
e14 = refl
g15 : W.State
g15 = snapshot (after (W.requestWholeCancel owner) g14)
e15 : W.step (W.requestWholeCancel owner) g14 ≡ just g15
e15 = refl
g16 : W.State
g16 = snapshot (after (W.deliverWhole owner) g15)
e16 : W.step (W.deliverWhole owner) g15 ≡ just g16
e16 = refl
g17 : W.State
g17 = snapshot (after (W.finishChildUnwind C.demux) g16)
e17 : W.step (W.finishChildUnwind C.demux) g16 ≡ just g17
e17 = refl
g18 : W.State
g18 = snapshot (after (W.run (M.run (P.deregisterInfra owner T.demuxer))) g17)
e18 : W.step (W.run (M.run (P.deregisterInfra owner T.demuxer))) g17 ≡ just g18
e18 = refl
g19 : W.State
g19 = snapshot (after (W.run (M.run (P.asyncInfraResult owner T.demuxer))) g18)
e19 : W.step (W.run (M.run (P.asyncInfraResult owner T.demuxer))) g18 ≡ just g19
e19 = refl
g20 : W.State
g20 = snapshot (after (W.joinWhole owner) g19)
e20 : W.step (W.joinWhole owner) g19 ≡ just g20
e20 = refl
g21 : W.State
g21 = snapshot (after (W.requestWholeCancel owner) g20)
e21 : W.step (W.requestWholeCancel owner) g20 ≡ just g21
e21 = refl
g22 : W.State
g22 = snapshot (after (W.deliverWhole owner) g21)
e22 : W.step (W.deliverWhole owner) g21 ≡ just g22
e22 = refl
g23 : W.State
g23 = snapshot (after (W.finishChildUnwind C.scheduled) g22)
e23 : W.step (W.finishChildUnwind C.scheduled) g22 ≡ just g23
e23 = refl
g24 : W.State
g24 = snapshot (after (W.run (M.run (P.deregisterInfra owner (T.laneMuxer E.scheduledLane)))) g23)
e24 : W.step (W.run (M.run (P.deregisterInfra owner (T.laneMuxer E.scheduledLane)))) g23 ≡ just g24
e24 = refl
g25 : W.State
g25 = snapshot (after (W.run (M.run (P.asyncInfraResult owner (T.laneMuxer E.scheduledLane)))) g24)
e25 : W.step (W.run (M.run (P.asyncInfraResult owner (T.laneMuxer E.scheduledLane)))) g24 ≡ just g25
e25 = refl
g26 : W.State
g26 = snapshot (after (W.joinWhole owner) g25)
e26 : W.step (W.joinWhole owner) g25 ≡ just g26
e26 = refl
g27 : W.State
g27 = snapshot (after (W.requestWholeCancel owner) g26)
e27 : W.step (W.requestWholeCancel owner) g26 ≡ just g27
e27 = refl
g28 : W.State
g28 = snapshot (after (W.deliverWhole owner) g27)
e28 : W.step (W.deliverWhole owner) g27 ≡ just g28
e28 = refl
g29 : W.State
g29 = snapshot (after (W.finishChildUnwind C.direct) g28)
e29 : W.step (W.finishChildUnwind C.direct) g28 ≡ just g29
e29 = refl
g30 : W.State
g30 = snapshot (after (W.run (M.run (P.deregisterInfra owner (T.laneMuxer E.directLane)))) g29)
e30 : W.step (W.run (M.run (P.deregisterInfra owner (T.laneMuxer E.directLane)))) g29 ≡ just g30
e30 = refl
g31 : W.State
g31 = snapshot (after (W.run (M.run (P.asyncInfraResult owner (T.laneMuxer E.directLane)))) g30)
e31 : W.step (W.run (M.run (P.asyncInfraResult owner (T.laneMuxer E.directLane)))) g30 ≡ just g31
e31 = refl
g32 : W.State
g32 = snapshot (after (W.joinWhole owner) g31)
e32 : W.step (W.joinWhole owner) g31 ≡ just g32
e32 = refl
g33 : W.State
g33 = snapshot (after (W.finishWholeClose owner) g32)
e33 : W.step (W.finishWholeClose owner) g32 ≡ just g33
e33 = refl
g34 : W.State
g34 = snapshot (after (W.finishNormalScope owner) g33)
e34 : W.step (W.finishNormalScope owner) g33 ≡ just g34
e34 = refl
wholeCloseActions : List W.Action
wholeCloseActions = (W.run (M.run (P.control owner P.selectCommand))) ∷ (W.requestShutdown owner) ∷ (W.selectShutdown owner) ∷ (W.observeStoppingTrace owner) ∷ (W.writeStopping owner) ∷ (W.captureGroup owner []) ∷ (W.finishGroup owner) ∷ (W.drainEmpty owner) ∷ (W.writeStopped owner) ∷ (W.observeTraceStopped owner) ∷ (W.sampleStoppedTracer owner) ∷ (W.commitStoppedTracer owner) ∷ (W.finishStoppedTrace owner) ∷ (W.beginWholeClose owner (C.demux ∷ C.scheduled ∷ C.direct ∷ [])) ∷ (W.requestWholeCancel owner) ∷ (W.deliverWhole owner) ∷ (W.finishChildUnwind C.demux) ∷ (W.run (M.run (P.deregisterInfra owner T.demuxer))) ∷ (W.run (M.run (P.asyncInfraResult owner T.demuxer))) ∷ (W.joinWhole owner) ∷ (W.requestWholeCancel owner) ∷ (W.deliverWhole owner) ∷ (W.finishChildUnwind C.scheduled) ∷ (W.run (M.run (P.deregisterInfra owner (T.laneMuxer E.scheduledLane)))) ∷ (W.run (M.run (P.asyncInfraResult owner (T.laneMuxer E.scheduledLane)))) ∷ (W.joinWhole owner) ∷ (W.requestWholeCancel owner) ∷ (W.deliverWhole owner) ∷ (W.finishChildUnwind C.direct) ∷ (W.run (M.run (P.deregisterInfra owner (T.laneMuxer E.directLane)))) ∷ (W.run (M.run (P.asyncInfraResult owner (T.laneMuxer E.directLane)))) ∷ (W.joinWhole owner) ∷ (W.finishWholeClose owner) ∷ (W.finishNormalScope owner) ∷ []
wholeClosePath : W.Executes g0 wholeCloseActions g34
wholeClosePath = W.next e1 (W.next e2 (W.next e3 (W.next e4 (W.next e5 (W.next e6 (W.next e7 (W.next e8 (W.next e9 (W.next e10 (W.next e11 (W.next e12 (W.next e13 (W.next e14 (W.next e15 (W.next e16 (W.next e17 (W.next e18 (W.next e19 (W.next e20 (W.next e21 (W.next e22 (W.next e23 (W.next e24 (W.next e25 (W.next e26 (W.next e27 (W.next e28 (W.next e29 (W.next e30 (W.next e31 (W.next e32 (W.next e33 (W.next e34 (W.done))))))))))))))))))))))))))))))))))

append : ∀ {p as q bs r} → W.Executes p as q → W.Executes q bs r → W.Executes p (as ++ bs) r
append W.done tail = tail
append (W.next eq path) tail = W.next eq (append path tail)
abstract
  initialized-configured-whole-close : W.Executes (GF.wrap (F.wrap Plain.b0))
    (map W.run (map M.run C.toMonitoredActions) ++ wholeCloseActions) g34
  initialized-configured-whole-close =
    append (GF.lift-path (F.lift-path C.initialized-monitored) refl) wholeClosePath

-- The same actual pool is closed: all three configured infrastructure jobs
-- were cancelled, unwound, deregistered and their Async results published.
final-pool : W.Pool.State
final-pool = W.poolAt owner g34
closed : W.Pool.phase final-pool ≡ W.Pool.closedPool
closed = refl
direct-joined : lookup C.direct (W.Pool.handles final-pool) ≡ just (W.Pool.resultAvailable W.Pool.cancelledExit)
direct-joined = refl
scheduled-joined : lookup C.scheduled (W.Pool.handles final-pool) ≡ just (W.Pool.resultAvailable W.Pool.cancelledExit)
scheduled-joined = refl
demux-joined : lookup C.demux (W.Pool.handles final-pool) ≡ just (W.Pool.resultAvailable W.Pool.cancelledExit)
demux-joined = refl
no-registered-left : W.Pool.registered final-pool ≡ []
no-registered-left = refl

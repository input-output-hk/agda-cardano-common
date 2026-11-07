{-# OPTIONS --guardedness #-}

-- M1 egress readiness controls on the migrated fixtures. Actual initialized
-- traces show a held batch refusing protocol clean completion and successful
-- drain (timeout2 remains possible), and a real sealed write releasing it.
-- Additive: no legacy fixture statement is changed here.
module ConnectionManagement.Negative.MuxEgressReadiness where
open import Class.DecEq.Instances using (DecEq-ℕ)
open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Integer using (+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain hiding (job; worker; mux)
open import ConnectionManagement.IGTypes using (clean)
open import ConnectionManagement.Store using (put)
import ConnectionManagement.MuxProtocolJobs as P
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxEgress as E
import ConnectionManagement.Rules.MuxJobTypes as T
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Negative.MuxProtocolJobs as Old
import ConnectionManagement.Negative.MuxGroupShutdown as Previous
import ConnectionManagement.Negative.MuxResultMonitor as MonitorFixtures
module K = Mux.Egress
module G = Previous.W
module M = Previous.M

key : Mux.ProtocolKey
key = 1 , Mux.responderJob
entered offered held sealed written : K.State
entered = Mux.egress Old.enteredMux
offered = record entered
  { wantons = put (serial Old.j₁₀) (K.wanton key 1) (K.wantons entered)
  ; queues = put E.scheduledLane (serial Old.j₁₀ ∷ []) (K.queues entered) }
held = record offered
  { wantons = put (serial Old.j₁₀) (K.wanton key 0) (K.wantons offered)
  ; queues = put E.scheduledLane [] (K.queues offered)
  ; cells = put key (K.cell E.scheduledLane (+ 1) 0) (K.cells offered)
  ; batches = (0 , K.batch E.scheduledLane ((key , 9) ∷ []) nothing K.building 1) ∷ []
  ; runHeld = + 1; nextBatch = 1 }
sealed = record held
  { batches = (0 , K.batch E.scheduledLane ((key , 9) ∷ []) nothing K.ready 1) ∷ [] }
written = record sealed
  { cells = put key (K.cell E.scheduledLane (+ 0) 9) (K.cells sealed)
  ; batches = (0 , K.batch E.scheduledLane ((key , 9) ∷ []) nothing K.written 1) ∷ []
  ; runHeld = + 0 }

at : K.State → T.BodyPhase → P.State
at e phase = Old.snapshot (Old.sourceMux (record Old.m6 { egress = e }) Old.messages)
  Old.rFork ((Old.j₁₀ , Old.rJob phase) ∷ []) []
offerPayload : P.step (P.appendProtocolPayload Old.j₁₀ 1) Old.r6Entered ≡ just (at offered T.executing)
offerPayload = refl
actualFirstTake : P.step (P.egressMuxer Old.owner (K.takeFirst E.scheduledLane))
  (at offered T.executing) ≡ just (at held T.executing)
actualFirstTake = refl
actualBodyReturn : P.step (P.protocolReturned Old.j₁₀) (at held T.executing) ≡ just (at held T.waitingEgress)
actualBodyReturn = refl
heldBlocksActualClean : P.step (P.commitClean Old.j₁₀) (at held T.waitingEgress) ≡ nothing
heldBlocksActualClean = refl
noWriteBeforeRealSeal : P.step (P.egressMuxer Old.owner (K.writeAccount 0)) (at held T.waitingEgress) ≡ nothing
noWriteBeforeRealSeal = refl
actualEmptyObservation : P.step (P.egressMuxer Old.owner (K.selectDemand 0))
  (at held T.waitingEgress) ≡ just (at sealed T.waitingEgress)
actualEmptyObservation = refl
actualMaskedWriteAccount : P.step (P.egressMuxer Old.owner (K.writeAccount 0))
  (at sealed T.waitingEgress) ≡ just (at written T.waitingEgress)
actualMaskedWriteAccount = refl
noDuplicateWrite : P.step (P.egressMuxer Old.owner (K.writeAccount 0)) (at written T.waitingEgress) ≡ nothing
noDuplicateWrite = refl

afterClean : P.State
afterClean = Old.snapshot (Old.sourceMux (record Old.cleanMux { egress = written }) Old.messages)
  Old.rFork ((Old.j₁₀ , Old.rJob (T.resultCaptured clean)) ∷ []) ((Old.owner , Old.j₁₀ ∷ []) ∷ [])
actualCleanAfterWrite : P.step (P.commitClean Old.j₁₀) (at written T.waitingEgress) ≡ just afterClean
actualCleanAfterWrite = refl

-- Every state used by the positive controls is reached through genuine physical
-- and actual O.advance steps, including child entry and real owner muxer writes.
abstract
  initializedHeldWait : P.Executes Old.b0
    (((Old.startActions ++ Old.firstForkPathActions) ++
      (P.enterProtocolBody Old.j₁₀ ∷ P.appendProtocolPayload Old.j₁₀ 1 ∷
       P.egressMuxer Old.owner (K.takeFirst E.scheduledLane) ∷
       P.protocolReturned Old.j₁₀ ∷ []))) (at held T.waitingEgress)
  initializedHeldWait = Old.append (Old.append Old.initialized-start Old.firstForkPath)
    (P.next Old.responderEntry (P.next offerPayload (P.next actualFirstTake (P.next actualBodyReturn P.done))))
  initializedSuccessfulWrite : P.Executes Old.b0
    ((((Old.startActions ++ Old.firstForkPathActions) ++
      (P.enterProtocolBody Old.j₁₀ ∷ P.appendProtocolPayload Old.j₁₀ 1 ∷
       P.egressMuxer Old.owner (K.takeFirst E.scheduledLane) ∷
       P.protocolReturned Old.j₁₀ ∷ []))) ++
      (P.egressMuxer Old.owner (K.selectDemand 0) ∷ P.egressMuxer Old.owner (K.writeAccount 0) ∷ []))
    (at written T.waitingEgress)
  initializedSuccessfulWrite = Old.append initializedHeldWait
    (P.next actualEmptyObservation (P.next actualMaskedWriteAccount P.done))

wrongPhysicalOwnerRefused : P.step (P.egressMuxer (ident 999) (K.takeFirst E.scheduledLane))
  (at offered T.executing) ≡ nothing
wrongPhysicalOwnerRefused = refl
wrongPlainLaneRefused : P.step (P.egressMuxer Old.owner (K.takeFirst E.directLane))
  (at offered T.executing) ≡ nothing
wrongPlainLaneRefused = refl
protocolSendAliasRefused : P.step (P.egressMuxer Old.owner (K.appendPayload (serial Old.j₁₀) 1))
  (at offered T.executing) ≡ nothing
protocolSendAliasRefused = refl
protocolAllocationAliasRefused : P.step (P.egressMuxer Old.owner (K.createWanton 999 key))
  (at offered T.executing) ≡ nothing
protocolAllocationAliasRefused = refl

-- Drain readiness on the initialized normal-shutdown group trace.
-- A literal source-state lens; actual step equalities below, not this builder,
-- certify the reachable shared state and all unchanged physical actors.
withAccounting : K.State → G.State → G.State
withAccounting e s with P.muxAt Old.mid (G.protocolState s)
... | nothing = s
... | just m = G.setSource (record (G.source s)
  { core = record (O.core (G.source s)) { inboundGovernor = IG.setMux Old.mid
      (record m { egress = e }) (Machine.inboundGovernor (O.core (G.source s))) } }) s
drainEntered drainOffered : G.State
drainEntered = withAccounting entered Previous.normal0
drainOffered = withAccounting offered Previous.normal0
drainEntry : G.step (G.run (M.run (P.enterProtocolBody Old.j₁₀))) Previous.normal0 ≡ just drainEntered
drainEntry = refl
drainSend : G.step (G.run (M.run (P.appendProtocolPayload Old.j₁₀ 1))) drainEntered ≡ just drainOffered
drainSend = refl
n0 n1 n2 n3 n4 n5 n6 n7 n8 n9 n10 n11 n12 : G.State
n0 = withAccounting held Previous.normal0
n1 = withAccounting held Previous.normal1
n2 = withAccounting held Previous.normal2
n3 = withAccounting held Previous.normal3
n4 = withAccounting held Previous.normal4
n5 = withAccounting held Previous.normal5
n6 = withAccounting held Previous.normal6
n7 = withAccounting held Previous.normal7
n8 = withAccounting held Previous.normal8
n9 = withAccounting held Previous.normal9
n10 = withAccounting held Previous.normal10
n11 = withAccounting held Previous.normal11
n12 = withAccounting held Previous.normal12
drainTake : G.step (G.run (M.run (P.egressMuxer Old.owner (K.takeFirst E.scheduledLane)))) drainOffered ≡ just n0
drainTake = refl
edge1 : G.step (G.requestShutdown Old.owner) n0 ≡ just n1
edge1 = refl
edge2 : G.step (G.selectShutdown Old.owner) n1 ≡ just n2
edge2 = refl
edge3 : G.step (G.observeStoppingTrace Old.owner) n2 ≡ just n3
edge3 = refl
edge4 : G.step (G.writeStopping Old.owner) n3 ≡ just n4
edge4 = refl
edge5 : G.step (G.captureGroup Old.owner (Old.j₁₀ ∷ [])) n4 ≡ just n5
edge5 = refl
edge6 : G.step (G.requestGroupCancel Old.owner) n5 ≡ just n6
edge6 = refl
edge7 : G.step (G.deliverGroup Old.owner) n6 ≡ just n7
edge7 = refl
edge8 : G.step (G.finishChildUnwind Old.j₁₀) n7 ≡ just n8
edge8 = refl
edge9 : G.step (G.run (M.run (P.deregisterProtocol Old.j₁₀))) n8 ≡ just n9
edge9 = refl
edge10 : G.step (G.run (M.run (P.asyncProtocolResult Old.j₁₀))) n9 ≡ just n10
edge10 = refl
edge11 : G.step (G.joinGroup Old.owner) n10 ≡ just n11
edge11 = refl
edge12 : G.step (G.finishGroup Old.owner) n11 ≡ just n12
edge12 = refl
successfulDrainRefused : G.step (G.drainEmpty Old.owner) n12 ≡ nothing
successfulDrainRefused = refl
timeoutStillPossible : G.step (G.timeout2Elapsed Old.owner) n12 ≡ just (G.setPhase Old.owner G.drainReady n12)
timeoutStillPossible = refl
prefix : List G.Action
prefix = G.run (M.run (P.enterProtocolBody Old.j₁₀)) ∷
  G.run (M.run (P.appendProtocolPayload Old.j₁₀ 1)) ∷
  G.run (M.run (P.egressMuxer Old.owner (K.takeFirst E.scheduledLane))) ∷ []
shutdown : List G.Action
shutdown = (G.requestShutdown Old.owner) ∷ (G.selectShutdown Old.owner) ∷ (G.observeStoppingTrace Old.owner) ∷ (G.writeStopping Old.owner) ∷ (G.captureGroup Old.owner (Old.j₁₀ ∷ [])) ∷ (G.requestGroupCancel Old.owner) ∷ (G.deliverGroup Old.owner) ∷ (G.finishChildUnwind Old.j₁₀) ∷ (G.run (M.run (P.deregisterProtocol Old.j₁₀))) ∷ (G.run (M.run (P.asyncProtocolResult Old.j₁₀))) ∷ (G.joinGroup Old.owner) ∷ (G.finishGroup Old.owner) ∷ []
abstract
  initializedHeldDrain : G.Executes (Previous.wrap (MonitorFixtures.wrap Old.b0))
    ((map G.run (map M.run Old.startActions ++ MonitorFixtures.errorPrefixActions) ++ prefix) ++ shutdown) n12
  initializedHeldDrain = Previous.append (Previous.append Previous.initialized-running
    (G.next drainEntry (G.next drainSend (G.next drainTake G.done))))
    (G.next edge1 (G.next edge2 (G.next edge3 (G.next edge4 (G.next edge5 (G.next edge6 (G.next edge7 (G.next edge8 (G.next edge9 (G.next edge10 (G.next edge11 (G.next edge12 G.done))))))))))))

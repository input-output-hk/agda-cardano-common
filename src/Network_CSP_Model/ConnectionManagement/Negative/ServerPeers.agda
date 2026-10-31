{-# OPTIONS --guardedness #-}

-- Shared Server/PSA/governor acceptance: data fixtures and independently named
-- histories live together, with runtime aliases kept private in each module.
module ConnectionManagement.Negative.ServerPeers where

-- Data-only snapshots. All source writes are checked in Interleaving;
-- none is justified by a driver that substitutes an old state on failure.
module Fixtures where
  open import Data.Bool using (Bool; true; false)
  open import Data.List using (List; []; _∷_)
  open import Data.Maybe using (just; nothing)
  open import Data.Product using (_,_)
  open import ConnectionManagement.Domain hiding (worker; local; mux; entry; job)
  open import ConnectionManagement.Store using (Store; put)
  import ConnectionManagement.State as Shared
  import ConnectionManagement.Machine as I
  import ConnectionManagement.OutboundMachine as O
  import ConnectionManagement.Subsystem as Sub
  import ConnectionManagement.ServerPeers as Combined
  import ConnectionManagement.PeerContext as Context
  import ConnectionManagement.PeerSupervision as Supervision
  import ConnectionManagement.ServerAdmission as Server
  import ConnectionManagement.ServerIGExit as Exit
  import ConnectionManagement.Rules.OutboundGovernor as G
  import ConnectionManagement.Rules.OutboundAcquire as Acquire
  import ConnectionManagement.Rules.OutboundCases as Cases
  import ConnectionManagement.Rules.PeerJobs as J
  import ConnectionManagement.Rules.CallerCancellation as Cancel
  import ConnectionManagement.Rules.AsyncScope as Scope
  import ConnectionManagement.Scenarios.Admission as A
  import ConnectionManagement.Negative.MuxPublicationInboundFixtures as Classification
  import ConnectionManagement.Negative.ServerIGExitFixtures as X
  classify : ErrorId → Bool
  classify _ = false

  private
    module K = Combined Classification.bearerClosed classify
    module C = Context classify
    module PS = Supervision classify
    module GP = PS.GP
    module Pool = GP.Pool
    module S = Server Classification.bearerClosed
    module E = Exit Classification.bearerClosed

  -- The immutable exception classifier is independent of bearer loss.
  caller child : WorkerId
  caller = ident 10
  child = ident 11
  sock : SocketId
  sock = ident 10
  jobId : JobId
  jobId = ident 0
  err : ErrorId
  err = errorId 170
  settings : G.State
  settings = G.governorState (G.targets 1 1 1)
    ((remote A.key₁ , G.known 0 0 nothing false false) ∷ []) [] [] [] [] [] [] []
  work : G.Job
  work = G.job G.establish (remote A.key₁) nothing
  marked : G.State
  marked = G.mark G.establish (remote A.key₁ ∷ []) settings
  k0 : C.Context
  k0 = C.capture (PS.initial (E.source X.start) settings)
  sub : C.SubContext
  sub = C.subsystem k0
  k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 : C.Context
  k1 = record k0 { subsystem = record sub { pc = Sub.sampleInputs } }
  k2 = record k0 { subsystem = record sub { pc = Sub.prepareWait; privateState = G.advanceTime 0 settings } }
  k3 = record k0 { subsystem = record sub { pc = Sub.selecting; wakeupAt = G.nextWakeup 0 settings } }
  k4 = record k0 { subsystem = record sub { pc = Sub.apply (Sub.policy (G.decision marked (work ∷ []))) } }
  k5 = record k0 { subsystem = record sub { privateState = marked; pc = Sub.publishView (work ∷ []) } }
  k6 = record k5 { subsystem = record (C.subsystem k5) { pc = Sub.traceDecision (work ∷ []) } }
  k7 = record k5 { subsystem = record (C.subsystem k5) { pc = Sub.launch (work ∷ []) } }
  job : J.Frame
  job = J.frame work caller child sock (ident 0) J.begin
  jobs : J.Frame → Bool → Store JobId Sub.JobFrame
  jobs f deregistered = (jobId , Sub.jobFrame f false deregistered) ∷ []
  runningPool : Pool.State
  runningPool = Pool.poolState ((jobId , Pool.bodyRunning) ∷ []) (jobId ∷ []) nothing Pool.openPool [] [] [] []
  k8 = record k7
    { subsystem = record (C.subsystem k7) { pc = Sub.register jobId []; jobs = jobs job false; nextJob = 1; nextPeer = 1 }
    ; governorPool = Pool.poolState ((jobId , Pool.bodyRunning) ∷ []) [] (just jobId) Pool.openPool [] [] [] [] }
  k9 = record k8 { subsystem = record (C.subsystem k8) { pc = Sub.launch []; pool = jobId ∷ [] }; governorPool = runningPool }
  k10 = record k9 { subsystem = record (C.subsystem k9) { jobs = jobs (record job { pc = J.awaitAcquire }) false } }

  -- Both raw admission workers remain distinct from the governor caller/child.
  twoServer : E.State
  twoServer = X.wrap X.F.two
  source0 : O.Configuration
  source0 = E.source twoServer
  serverAt : O.Configuration → E.State
  serverAt c = K.setSource c twoServer
  at : O.Configuration → C.Context → K.State
  at c k = K.combined (serverAt c) k
  start one two : K.State
  start = K.combined X.start k0
  one = K.combined (X.wrap X.F.one) k0
  two = K.combined twoServer k0
  w0 : Shared.State
  w0 = S.shared (E.base twoServer)
  reservedMap : Shared.ConnMap
  reservedMap = Shared.insertLocal (remote A.key₁) unknownLocal (ident 0) []
  w1 w2 w3 : Shared.State
  w1 = record w0 { cm = Shared.cmStore (Shared.full reservedMap) ((ident 0 , Shared.reservedOutbound) ∷ []) 1 }
  w2 = record w1 { promises = ident 0 ∷ []; nextPromise = 1 }
  w3 = record w2 { sockets = put sock (Shared.admitting caller) (Shared.sockets w2) }
  req : Acquire.Request
  req = Acquire.acquireRequest (remote A.key₁) child sock outbound nothing
  active : Acquire.PC → Acquire.Frame
  active pc = Acquire.frame req pc
  sourceAt : Shared.State → Acquire.Runtime → O.Configuration
  sourceAt world acquiring = record source0
    { core = I.replaceWorld (O.core source0) world; acquiring = acquiring; randomGeneration = 1 }
  runtime : Acquire.PC → Acquire.Runtime
  runtime pc = (caller , active pc) ∷ []
  c10 c11 c12 c13 c14 detachedSource : O.Configuration
  c10 = record (sourceAt w0 (runtime Acquire.selecting)) { randomGeneration = 0 }
  c11 = sourceAt w1 (runtime (Acquire.count (Acquire.allocatePromise (ident 0))))
  c12 = sourceAt w1 (runtime (Acquire.allocatePromise (ident 0)))
  c13 = sourceAt w2 (runtime (Acquire.openSocket (ident 0) (ident 0)))
  c14 = sourceAt w3 (runtime (Acquire.configureSocket (ident 0) (ident 0)))
  detachedSource = sourceAt w3 []

  -- Exact detached capture; Server interference must retain entry zero.
  detached : Cancel.Frame
  detached = Cancel.cancellation caller err (Cancel.acquiring (active (Acquire.configureSocket (ident 0) (ident 0))))
    (Cancel.cleaning (active (Acquire.closeError (ident 0) (Cases.ioFailure err))))
  afterClose afterRemove afterCount : Cancel.Frame
  afterClose = record detached { pc = Cancel.cleaning (active (Acquire.removeError (ident 0) (Cases.ioFailure err))) }
  afterRemove = record detached { pc = Cancel.cleaning (active (Acquire.count (Acquire.complete (Cases.raised (Cases.ioFailure err))))) }
  afterCount = record detached { pc = Cancel.finished Cancel.cleanupComplete }

  q0 : Scope.State
  q0 = Scope.scopeState Scope.running Scope.running Scope.running Scope.running (Scope.openScope) false
  q1 : Scope.State
  q1 = Scope.scopeState Scope.running Scope.running Scope.running Scope.running (Scope.closing Scope.churn) false
  q2 : Scope.State
  q2 = Scope.scopeState Scope.cancelRequested Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  q3 : Scope.State
  q3 = Scope.scopeState Scope.cancelDelivered Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  q4 : Scope.State
  q4 = Scope.scopeState Scope.bodyExited Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  q5 : Scope.State
  q5 = Scope.scopeState Scope.resultAvailable Scope.running Scope.running Scope.running (Scope.closing Scope.churn) true
  q6 : Scope.State
  q6 = Scope.scopeState Scope.joined Scope.running Scope.running Scope.running (Scope.closing Scope.governor) false
  q7 : Scope.State
  q7 = Scope.scopeState Scope.joined Scope.cancelRequested Scope.running Scope.running (Scope.closing Scope.governor) true
  q8 : Scope.State
  q8 = Scope.scopeState Scope.joined Scope.cancelDelivered Scope.running Scope.running (Scope.closing Scope.governor) true
  q9 : Scope.State
  q9 = Scope.scopeState Scope.joined Scope.bodyExited Scope.running Scope.running (Scope.closing Scope.governor) true
  q10 : Scope.State
  q10 = Scope.scopeState Scope.joined Scope.resultAvailable Scope.running Scope.running (Scope.closing Scope.governor) true
  q11 : Scope.State
  q11 = Scope.scopeState Scope.joined Scope.joined Scope.running Scope.running (Scope.closing Scope.localRoot) false
  q12 : Scope.State
  q12 = Scope.scopeState Scope.joined Scope.joined Scope.cancelRequested Scope.running (Scope.closing Scope.localRoot) true
  q13 : Scope.State
  q13 = Scope.scopeState Scope.joined Scope.joined Scope.cancelDelivered Scope.running (Scope.closing Scope.localRoot) true
  q14 : Scope.State
  q14 = Scope.scopeState Scope.joined Scope.joined Scope.bodyExited Scope.running (Scope.closing Scope.localRoot) true
  q15 : Scope.State
  q15 = Scope.scopeState Scope.joined Scope.joined Scope.resultAvailable Scope.running (Scope.closing Scope.localRoot) true
  q16 : Scope.State
  q16 = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.running (Scope.closing Scope.ledger) false
  q17 : Scope.State
  q17 = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.cancelRequested (Scope.closing Scope.ledger) true
  q18 : Scope.State
  q18 = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.cancelDelivered (Scope.closing Scope.ledger) true
  q19 : Scope.State
  q19 = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.bodyExited (Scope.closing Scope.ledger) true
  q20 : Scope.State
  q20 = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.resultAvailable (Scope.closing Scope.ledger) true
  q21 : Scope.State
  q21 = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.readyToFinish) false
  q22 : Scope.State
  q22 = Scope.scopeState Scope.joined Scope.joined Scope.joined Scope.joined (Scope.finishedScope) false

  -- Scope observations have no CM copy and leave the current source untouched.
  atScope : Scope.State → C.Context → C.Context
  atScope q k = record k { scopes = q }
  kg0 kg1 kg2 kg3 kc1 kc2 kc3 ku kd kp kj kclosed : C.Context
  kg0 = atScope q8 k10
  closingPool : Pool.State
  closingPool = record runningPool { phase = Pool.closing; snapshot = jobId ∷ []; remaining = jobId ∷ [] }
  kg1 = record kg0 { governorPool = closingPool }
  kg2 = record kg0 { governorPool = record closingPool { phase = Pool.cancelPending jobId } }
  unwindingPool : Pool.State
  unwindingPool = record closingPool { phase = Pool.joinPending jobId; handles = (jobId , Pool.bodyUnwinding) ∷ [] }
  kg3 = record kg0 { governorPool = unwindingPool; unwinding = (jobId , detached) ∷ [] }
  kc1 = record kg3 { unwinding = (jobId , afterClose) ∷ [] }
  kc2 = record kg3 { unwinding = (jobId , afterRemove) ∷ [] }
  kc3 = record kg3 { unwinding = (jobId , afterCount) ∷ [] }
  ku = record kc3 { governorPool = record unwindingPool { handles = (jobId , Pool.deregisterPending Pool.cancelledExit) ∷ [] } }
  kd = record ku
    { governorPool = record unwindingPool { handles = (jobId , Pool.deregistered Pool.cancelledExit) ∷ []; registered = [] }
    ; subsystem = record (C.subsystem ku) { jobs = jobs (record job { pc = J.awaitAcquire }) true; pool = [] } }
  kp = record kd { governorPool = record (C.governorPool kd) { handles = (jobId , Pool.resultAvailable Pool.cancelledExit) ∷ [] } }
  kj = record kp { governorPool = record (C.governorPool kp) { phase = Pool.closing; remaining = []; joined = jobId ∷ [] } }
  kclosed = record kj { governorPool = record (C.governorPool kj) { phase = Pool.closedPool } }

  -- The raw worker captures the outbound reservation in its saved map. Its failed
  -- fork restores that map while retaining both already allocated entry records.
  lease : Shared.Lease
  lease = Shared.lease A.w₀ reservedMap
  held closedSocket counted allocated selected failed restored removed : Shared.State
  held = record w3 { cm = record (Shared.cm w3) { mapCell = Shared.taken A.w₀ }
    ; admissions = put A.w₀ (Shared.admissionWorker X.F.r₀ (Shared.count lease)) (Shared.admissions w3) }
  closedSocket = record held { sockets = put sock Shared.closed (Shared.sockets held) }
  counted = record closedSocket { admissions = put A.w₀ (Shared.admissionWorker X.F.r₀ (Shared.prepare lease)) (Shared.admissions closedSocket) }
  allocated = record counted { promises = ident 1 ∷ ident 0 ∷ []; nextPromise = 2
    ; admissions = put A.w₀ (Shared.admissionWorker X.F.r₀ (Shared.selectEntry lease (ident 1))) (Shared.admissions counted) }
  selected = record allocated
    { cm = record (Shared.cm allocated) { entries = put (ident 1) (Shared.unnegotiated inbound A.key₀ A.child₀) (Shared.entries (Shared.cm allocated)); nextEntry = 2 }
    ; admissions = put A.w₀ (Shared.admissionWorker X.F.r₀ (Shared.forkHandler lease (ident 1) (ident 1))) (Shared.admissions allocated) }
  failed = record selected { admissions = put A.w₀ (Shared.admissionWorker X.F.r₀ (Shared.reject lease Shared.forkFailed)) (Shared.admissions selected) }
  restored = record failed { cm = record (Shared.cm failed) { mapCell = Shared.full reservedMap }
    ; admissions = put A.w₀ (Shared.admissionWorker X.F.r₀ (Shared.closeSocket Shared.forkFailed)) (Shared.admissions failed) }
  removed = record restored { cm = record (Shared.cm restored) { mapCell = Shared.full []
    ; entries = put (ident 0) (Shared.terminated nothing) (Shared.entries (Shared.cm restored)) } }
  restoredSource finalSource : O.Configuration
  restoredSource = sourceAt restored []
  finalSource = sourceAt removed []
  kscopes kmonitor kdone : C.Context
  kscopes = atScope q22 kclosed
  kmonitor = record kscopes { monitorPool = record (C.monitorPool kscopes) { phase = PS.Pool.closing } }
  kdone = record kscopes { monitorPool = record (C.monitorPool kscopes) { phase = PS.Pool.closedPool } }
  returned : K.State
  returned = K.combined (record (serverAt finalSource) { base = record (E.base (serverAt finalSource)) { stage = S.actionBodyExited } }) kdone

-- Initialized shared-map interference, detached cleanup and lexical peer-close
-- order. This finite history is not a source-refinement or progress theorem.
module Interleaving where
  open import Data.Bool using (true; false)
  open import Data.List using (List; []; _∷_)
  import Data.List.Relation.Unary.All as All
  open import Data.List.Membership.Propositional using (_∈_)
  open import Data.List.Relation.Unary.Any using (here)
  open import Data.Maybe using (just; nothing)
  open import Data.Product using (_,_; proj₁; proj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import ConnectionManagement.Domain hiding (worker; local; mux; job)
  open import ConnectionManagement.Store using (lookup; put)
  import ConnectionManagement.ServerPeers as Combined
  import ConnectionManagement.ServerIGExit as Exit
  import ConnectionManagement.ServerAdmission as Server
  import ConnectionManagement.PeerContext as Context
  import ConnectionManagement.PeerSupervision as Supervision
  import ConnectionManagement.Properties.ServerPeers as Proof
  import ConnectionManagement.Properties.ServerPeersSupply as Supply
  import ConnectionManagement.Properties.JobPoolClose as Close
  import ConnectionManagement.Properties.AsyncScope as ScopeFacts
  import ConnectionManagement.OutboundMachine as O
  import ConnectionManagement.Machine as I
  import ConnectionManagement.State as Shared
  import ConnectionManagement.Subsystem as Sub
  import ConnectionManagement.Rules.OutboundAcquire as A
  import ConnectionManagement.Rules.CallerCancellation as Cancel
  import ConnectionManagement.Rules.PeerJobs as J
  import ConnectionManagement.Rules.Server as Admission
  import ConnectionManagement.Rules.AsyncScope as Scope
  module F = Fixtures
  import ConnectionManagement.Negative.ServerIGExitFixtures as X
  import ConnectionManagement.Negative.MuxPublicationInboundFixtures as Classification
  import ConnectionManagement.Scenarios.Admission as Actors
  private
    module K = Combined Classification.bearerClosed F.classify
    module E = Exit Classification.bearerClosed
    module S = Server Classification.bearerClosed
    module PS = Supervision F.classify
    module GP = PS.GP
    module C = Context F.classify
    module Facts = Proof Classification.bearerClosed F.classify
    module Inv = Supply Classification.bearerClosed F.classify
    module GClose = Close GP.Body

  ps : Sub.Action → K.Action
  ps a = K.peerStep (PS.run (GP.run a))
  gp : GP.Action → K.Action
  gp a = K.peerStep (PS.run a)
  sc : Scope.Action → K.Action
  sc a = K.peerStep (PS.scope a)
  cm : A.Action → K.Action
  cm a = K.coreStep (O.acquire F.caller a)
  admit : Admission.AdmissionAction → K.Action
  admit a = K.serverStep (E.run (S.run (S.runMachine (I.admissionStep Actors.w₀ a))))
  initializer : K.initial (O.initial (I.initial Shared.responderMode X.F.empty)) F.settings ≡ just F.start
  initializer = refl

  step1 : K.step (K.serverStep (E.run (S.acceptedFork Actors.w₀ X.F.r₀))) (F.start) ≡ just (F.one)
  step1 = refl
  step2 : K.step (K.serverStep (E.run (S.acceptedFork Actors.w₁ X.F.r₁))) (F.one) ≡ just (F.two)
  step2 = refl
  step3 : K.step (ps (Sub.publishPublicState)) (F.two) ≡ just (F.at F.source0 F.k1)
  step3 = refl
  step4 : K.step (ps (Sub.sampleTime 0)) (F.at F.source0 F.k1) ≡ just (F.at F.source0 F.k2)
  step4 = refl
  step5 : K.step (ps (Sub.registerWakeup)) (F.at F.source0 F.k2) ≡ just (F.at F.source0 F.k3)
  step5 = refl
  step6 : K.step (ps (Sub.selectPolicy (remote Actors.key₁ ∷ []))) (F.at F.source0 F.k3) ≡ just (F.at F.source0 F.k4)
  step6 = refl
  step7 : K.step (ps (Sub.applyAt 0)) (F.at F.source0 F.k4) ≡ just (F.at F.source0 F.k5)
  step7 = refl
  step8 : K.step (ps (Sub.publishCounters)) (F.at F.source0 F.k5) ≡ just (F.at F.source0 F.k6)
  step8 = refl
  step9 : K.step (ps (Sub.traceSelection)) (F.at F.source0 F.k6) ≡ just (F.at F.source0 F.k7)
  step9 = refl
  step10 : K.step (ps (Sub.forkJob F.caller F.child F.sock)) (F.at F.source0 F.k7) ≡ just (F.at F.source0 F.k8)
  step10 = refl
  step11 : K.step (ps (Sub.registerJob)) (F.at F.source0 F.k8) ≡ just (F.at F.source0 F.k9)
  step11 = refl
  step12 : K.step (ps (Sub.jobStep F.jobId J.enter)) (F.at F.source0 F.k9) ≡ just (F.at F.c10 F.k10)
  step12 = refl
  step13 : K.step (cm (A.select nothing)) (F.at F.c10 F.k10) ≡ just (F.at F.c11 F.k10)
  step13 = refl
  step14 : K.step (cm (A.readCounters)) (F.at F.c11 F.k10) ≡ just (F.at F.c12 F.k10)
  step14 = refl
  step15 : K.step (cm (A.newPromise)) (F.at F.c12 F.k10) ≡ just (F.at F.c13 F.k10)
  step15 = refl
  step16 : K.step (cm (A.openOK)) (F.at F.c13 F.k10) ≡ just (F.at F.c14 F.k10)
  step16 = refl
  step17 : K.step (sc (Scope.beginUnwind)) (F.at F.c14 F.k10) ≡ just (F.at F.c14 (F.atScope F.q1 F.k10))
  step17 = refl
  step18 : K.step (sc (Scope.requestCancel)) (F.at F.c14 (F.atScope F.q1 F.k10)) ≡ just (F.at F.c14 (F.atScope F.q2 F.k10))
  step18 = refl
  step19 : K.step (sc (Scope.deliverCancel)) (F.at F.c14 (F.atScope F.q2 F.k10)) ≡ just (F.at F.c14 (F.atScope F.q3 F.k10))
  step19 = refl
  step20 : K.step (sc (Scope.bodyExit Scope.churn)) (F.at F.c14 (F.atScope F.q3 F.k10)) ≡ just (F.at F.c14 (F.atScope F.q4 F.k10))
  step20 = refl
  step21 : K.step (sc (Scope.publishResult Scope.churn)) (F.at F.c14 (F.atScope F.q4 F.k10)) ≡ just (F.at F.c14 (F.atScope F.q5 F.k10))
  step21 = refl
  step22 : K.step (sc (Scope.join)) (F.at F.c14 (F.atScope F.q5 F.k10)) ≡ just (F.at F.c14 (F.atScope F.q6 F.k10))
  step22 = refl
  step23 : K.step (sc (Scope.requestCancel)) (F.at F.c14 (F.atScope F.q6 F.k10)) ≡ just (F.at F.c14 (F.atScope F.q7 F.k10))
  step23 = refl
  step24 : K.step (sc (Scope.deliverCancel)) (F.at F.c14 (F.atScope F.q7 F.k10)) ≡ just (F.at F.c14 (F.atScope F.q8 F.k10))
  step24 = refl
  step25 : K.step (gp (GP.beginClose (F.jobId ∷ []))) (F.at F.c14 (F.atScope F.q8 F.k10)) ≡ just (F.at F.c14 F.kg1)
  step25 = refl
  step26 : K.step (gp GP.requestCancel) (F.at F.c14 F.kg1) ≡ just (F.at F.c14 F.kg2)
  step26 = refl
  step27 : K.step (gp (GP.deliverCancellation F.err)) (F.at F.c14 F.kg2) ≡ just (F.at F.detachedSource F.kg3)
  step27 = refl
  step28 : K.step (admit Admission.take) (F.at F.detachedSource F.kg3) ≡ just (F.at (F.sourceAt F.held []) F.kg3)
  step28 = refl
  step29 : K.step (gp (GP.cleanup F.jobId Cancel.closeSocket)) (F.at (F.sourceAt F.held []) F.kg3) ≡ just (F.at (F.sourceAt F.closedSocket []) F.kc1)
  step29 = refl
  step30 : K.step (admit Admission.countLimit) (F.at (F.sourceAt F.closedSocket []) F.kc1) ≡ just (F.at (F.sourceAt F.counted []) F.kc1)
  step30 = refl
  step31 : K.step (admit Admission.allocatePromise) (F.at (F.sourceAt F.counted []) F.kc1) ≡ just (F.at (F.sourceAt F.allocated []) F.kc1)
  step31 = refl
  step32 : K.step (admit Admission.chooseEntry) (F.at (F.sourceAt F.allocated []) F.kc1) ≡ just (F.at (F.sourceAt F.selected []) F.kc1)
  step32 = refl
  step33 : K.step (admit Admission.failFork) (F.at (F.sourceAt F.selected []) F.kc1) ≡ just (F.at (F.sourceAt F.failed []) F.kc1)
  step33 = refl
  step34 : K.step (admit Admission.restore) (F.at (F.sourceAt F.failed []) F.kc1) ≡ just (F.at F.restoredSource F.kc1)
  step34 = refl
  step35 : K.step (gp (GP.cleanup F.jobId Cancel.removeReservation)) (F.at F.restoredSource F.kc1) ≡ just (F.at F.finalSource F.kc2)
  step35 = refl
  step36 : K.step (gp (GP.cleanup F.jobId Cancel.readCounters)) (F.at F.finalSource F.kc2) ≡ just (F.at F.finalSource F.kc3)
  step36 = refl
  step37 : K.step (gp (GP.bodyUnwound F.jobId)) (F.at F.finalSource F.kc3) ≡ just (F.at F.finalSource F.ku)
  step37 = refl
  step38 : K.step (gp (GP.deregisterCancelled F.jobId)) (F.at F.finalSource F.ku) ≡ just (F.at F.finalSource F.kd)
  step38 = refl
  step39 : K.step (gp (GP.publishAsyncResult F.jobId)) (F.at F.finalSource F.kd) ≡ just (F.at F.finalSource F.kp)
  step39 = refl
  step40 : K.step (gp GP.join) (F.at F.finalSource F.kp) ≡ just (F.at F.finalSource F.kj)
  step40 = refl
  step41 : K.step (gp GP.finishClose) (F.at F.finalSource F.kj) ≡ just (F.at F.finalSource F.kclosed)
  step41 = refl
  step42 : K.step (sc (Scope.bodyExit Scope.governor)) (F.at F.finalSource F.kclosed) ≡ just (F.at F.finalSource (F.atScope F.q9 F.kclosed))
  step42 = refl
  step43 : K.step (sc (Scope.publishResult Scope.governor)) (F.at F.finalSource (F.atScope F.q9 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q10 F.kclosed))
  step43 = refl
  step44 : K.step (sc (Scope.join)) (F.at F.finalSource (F.atScope F.q10 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q11 F.kclosed))
  step44 = refl
  step45 : K.step (sc (Scope.requestCancel)) (F.at F.finalSource (F.atScope F.q11 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q12 F.kclosed))
  step45 = refl
  step46 : K.step (sc (Scope.deliverCancel)) (F.at F.finalSource (F.atScope F.q12 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q13 F.kclosed))
  step46 = refl
  step47 : K.step (sc (Scope.bodyExit Scope.localRoot)) (F.at F.finalSource (F.atScope F.q13 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q14 F.kclosed))
  step47 = refl
  step48 : K.step (sc (Scope.publishResult Scope.localRoot)) (F.at F.finalSource (F.atScope F.q14 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q15 F.kclosed))
  step48 = refl
  step49 : K.step (sc (Scope.join)) (F.at F.finalSource (F.atScope F.q15 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q16 F.kclosed))
  step49 = refl
  step50 : K.step (sc (Scope.requestCancel)) (F.at F.finalSource (F.atScope F.q16 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q17 F.kclosed))
  step50 = refl
  step51 : K.step (sc (Scope.deliverCancel)) (F.at F.finalSource (F.atScope F.q17 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q18 F.kclosed))
  step51 = refl
  step52 : K.step (sc (Scope.bodyExit Scope.ledger)) (F.at F.finalSource (F.atScope F.q18 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q19 F.kclosed))
  step52 = refl
  step53 : K.step (sc (Scope.publishResult Scope.ledger)) (F.at F.finalSource (F.atScope F.q19 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q20 F.kclosed))
  step53 = refl
  step54 : K.step (sc (Scope.join)) (F.at F.finalSource (F.atScope F.q20 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q21 F.kclosed))
  step54 = refl
  step55 : K.step (sc (Scope.finishClose)) (F.at F.finalSource (F.atScope F.q21 F.kclosed)) ≡ just (F.at F.finalSource (F.atScope F.q22 F.kclosed))
  step55 = refl
  step56 : K.step (K.peerStep (PS.beginMonitorClose [])) (F.at F.finalSource (F.atScope F.q22 F.kclosed)) ≡ just (F.at F.finalSource F.kmonitor)
  step56 = refl
  step57 : K.step (K.peerStep PS.finishMonitorClose) (F.at F.finalSource F.kmonitor) ≡ just (F.at F.finalSource F.kdone)
  step57 = refl
  step58 : K.step (K.serverStep (E.run (S.scope S.returnAction))) (F.at F.finalSource F.kdone) ≡ just (F.returned)
  step58 = refl

  actions : List K.Action
  actions = (K.serverStep (E.run (S.acceptedFork Actors.w₀ X.F.r₀))) ∷ (K.serverStep (E.run (S.acceptedFork Actors.w₁ X.F.r₁))) ∷ (ps (Sub.publishPublicState)) ∷ (ps (Sub.sampleTime 0)) ∷ (ps (Sub.registerWakeup)) ∷ (ps (Sub.selectPolicy (remote Actors.key₁ ∷ []))) ∷ (ps (Sub.applyAt 0)) ∷ (ps (Sub.publishCounters)) ∷ (ps (Sub.traceSelection)) ∷ (ps (Sub.forkJob F.caller F.child F.sock)) ∷ (ps (Sub.registerJob)) ∷ (ps (Sub.jobStep F.jobId J.enter)) ∷ (cm (A.select nothing)) ∷ (cm (A.readCounters)) ∷ (cm (A.newPromise)) ∷ (cm (A.openOK)) ∷ (sc (Scope.beginUnwind)) ∷ (sc (Scope.requestCancel)) ∷ (sc (Scope.deliverCancel)) ∷ (sc (Scope.bodyExit Scope.churn)) ∷ (sc (Scope.publishResult Scope.churn)) ∷ (sc (Scope.join)) ∷ (sc (Scope.requestCancel)) ∷ (sc (Scope.deliverCancel)) ∷ (gp (GP.beginClose (F.jobId ∷ []))) ∷ (gp GP.requestCancel) ∷ (gp (GP.deliverCancellation F.err)) ∷ (admit Admission.take) ∷ (gp (GP.cleanup F.jobId Cancel.closeSocket)) ∷ (admit Admission.countLimit) ∷ (admit Admission.allocatePromise) ∷ (admit Admission.chooseEntry) ∷ (admit Admission.failFork) ∷ (admit Admission.restore) ∷ (gp (GP.cleanup F.jobId Cancel.removeReservation)) ∷ (gp (GP.cleanup F.jobId Cancel.readCounters)) ∷ (gp (GP.bodyUnwound F.jobId)) ∷ (gp (GP.deregisterCancelled F.jobId)) ∷ (gp (GP.publishAsyncResult F.jobId)) ∷ (gp GP.join) ∷ (gp GP.finishClose) ∷ (sc (Scope.bodyExit Scope.governor)) ∷ (sc (Scope.publishResult Scope.governor)) ∷ (sc (Scope.join)) ∷ (sc (Scope.requestCancel)) ∷ (sc (Scope.deliverCancel)) ∷ (sc (Scope.bodyExit Scope.localRoot)) ∷ (sc (Scope.publishResult Scope.localRoot)) ∷ (sc (Scope.join)) ∷ (sc (Scope.requestCancel)) ∷ (sc (Scope.deliverCancel)) ∷ (sc (Scope.bodyExit Scope.ledger)) ∷ (sc (Scope.publishResult Scope.ledger)) ∷ (sc (Scope.join)) ∷ (sc (Scope.finishClose)) ∷ (K.peerStep (PS.beginMonitorClose [])) ∷ (K.peerStep PS.finishMonitorClose) ∷ (K.serverStep (E.run (S.scope S.returnAction))) ∷ []
  captureActions : List K.Action
  captureActions = (K.serverStep (E.run (S.acceptedFork Actors.w₀ X.F.r₀))) ∷ (K.serverStep (E.run (S.acceptedFork Actors.w₁ X.F.r₁))) ∷ (ps (Sub.publishPublicState)) ∷ (ps (Sub.sampleTime 0)) ∷ (ps (Sub.registerWakeup)) ∷ (ps (Sub.selectPolicy (remote Actors.key₁ ∷ []))) ∷ (ps (Sub.applyAt 0)) ∷ (ps (Sub.publishCounters)) ∷ (ps (Sub.traceSelection)) ∷ (ps (Sub.forkJob F.caller F.child F.sock)) ∷ (ps (Sub.registerJob)) ∷ (ps (Sub.jobStep F.jobId J.enter)) ∷ (cm (A.select nothing)) ∷ (cm (A.readCounters)) ∷ (cm (A.newPromise)) ∷ (cm (A.openOK)) ∷ (sc (Scope.beginUnwind)) ∷ (sc (Scope.requestCancel)) ∷ (sc (Scope.deliverCancel)) ∷ (sc (Scope.bodyExit Scope.churn)) ∷ (sc (Scope.publishResult Scope.churn)) ∷ (sc (Scope.join)) ∷ (sc (Scope.requestCancel)) ∷ (sc (Scope.deliverCancel)) ∷ (gp (GP.beginClose (F.jobId ∷ []))) ∷ (gp GP.requestCancel) ∷ (gp (GP.deliverCancellation F.err)) ∷ (admit Admission.take) ∷ (gp (GP.cleanup F.jobId Cancel.closeSocket)) ∷ (admit Admission.countLimit) ∷ (admit Admission.allocatePromise) ∷ (admit Admission.chooseEntry) ∷ []
  abstract
    initialized : K.Executes F.start actions F.returned
    initialized = K.next step1 (K.next step2 (K.next step3 (K.next step4 (K.next step5 (K.next step6 (K.next step7 (K.next step8 (K.next step9 (K.next step10 (K.next step11 (K.next step12 (K.next step13 (K.next step14 (K.next step15 (K.next step16 (K.next step17 (K.next step18 (K.next step19 (K.next step20 (K.next step21 (K.next step22 (K.next step23 (K.next step24 (K.next step25 (K.next step26 (K.next step27 (K.next step28 (K.next step29 (K.next step30 (K.next step31 (K.next step32 (K.next step33 (K.next step34 (K.next step35 (K.next step36 (K.next step37 (K.next step38 (K.next step39 (K.next step40 (K.next step41 (K.next step42 (K.next step43 (K.next step44 (K.next step45 (K.next step46 (K.next step47 (K.next step48 (K.next step49 (K.next step50 (K.next step51 (K.next step52 (K.next step53 (K.next step54 (K.next step55 (K.next step56 (K.next step57 (K.next step58 (K.done))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    initialized-capture : K.Executes F.start captureActions (F.at (F.sourceAt F.selected []) F.kc1)
    initialized-capture = K.next step1 (K.next step2 (K.next step3 (K.next step4 (K.next step5 (K.next step6 (K.next step7 (K.next step8 (K.next step9 (K.next step10 (K.next step11 (K.next step12 (K.next step13 (K.next step14 (K.next step15 (K.next step16 (K.next step17 (K.next step18 (K.next step19 (K.next step20 (K.next step21 (K.next step22 (K.next step23 (K.next step24 (K.next step25 (K.next step26 (K.next step27 (K.next step28 (K.next step29 (K.next step30 (K.next step31 (K.next step32 (K.done))))))))))))))))))))))))))))))))
  supply : Inv.Valid F.returned
  supply = Inv.from-initial-valid initializer (All.[] , All.[]) initialized
  capture-during-server-write : Inv.Valid (F.at (F.sourceAt F.selected []) F.kc1)
  capture-during-server-write = Inv.from-initial-valid initializer (All.[] , All.[]) initialized-capture
  all-scopes-joined : ScopeFacts.AllJoined (C.scopes F.kdone)
  all-scopes-joined = proj₂ (proj₂ (Facts.from-initial initializer initialized refl refl refl))
  captured-job-terminal : GClose.Terminal (C.governorPool F.kdone) F.jobId
  captured-job-terminal = proj₁ (Facts.from-initial initializer initialized refl refl refl) F.jobId (here refl)
  nonempty-governor-snapshot : GP.Pool.snapshot (C.governorPool F.kdone) ≡ F.jobId ∷ []
  nonempty-governor-snapshot = refl
  no-ordinary-completion : GP.Pool.completions (C.governorPool F.kdone) ≡ []
  no-ordinary-completion = refl
  raw-workers-still-incomplete : S.allResults (S.workers (E.base (K.server F.returned))) ≡ false
  raw-workers-still-incomplete = refl
  saved-map-was-shared : Shared.savedMap F.lease ≡ F.reservedMap
  saved-map-was-shared = refl
  cleanup-wrote-captured-entry : lookup (ident 0) (Shared.entries (Shared.cm (I.world (O.core F.finalSource)))) ≡ just (Shared.terminated nothing)
  cleanup-wrote-captured-entry = refl
  raw-failed-fork-write-retained : lookup (ident 1) (Shared.entries (Shared.cm (I.world (O.core F.finalSource)))) ≡ just (Shared.unnegotiated inbound Actors.key₀ Actors.child₀)
  raw-failed-fork-write-retained = refl
  no-callback-before-peer-close : K.step (K.serverStep (E.run (S.scope S.returnAction))) F.two ≡ nothing
  no-callback-before-peer-close = refl
  no-callback-before-monitor-close : K.step (K.serverStep (E.run (S.scope S.returnAction))) (F.at F.finalSource F.kscopes) ≡ nothing
  no-callback-before-monitor-close = refl
  cleanup-really-retries : Cancel.step Cancel.removeReservation F.afterClose (F.sourceAt F.closedSocket []) ≡ nothing
  cleanup-really-retries = refl
  no-cleanup-map-shortcut : K.step (gp (GP.cleanup F.jobId Cancel.removeReservation)) (F.at (F.sourceAt F.closedSocket []) F.kc1) ≡ nothing
  no-cleanup-map-shortcut = refl
  no-retired-caller-resumption : K.step (cm A.configureOK) (F.at F.detachedSource F.kg3) ≡ nothing
  no-retired-caller-resumption = refl
  no-result-before-cleanup : K.step (gp (GP.publishAsyncResult F.jobId)) (F.at F.detachedSource F.kg3) ≡ nothing
  no-result-before-cleanup = refl
  no-peer-core-alias : K.step (ps (Sub.core (O.acquire F.caller A.configureOK))) (F.at F.c14 F.k10) ≡ nothing
  no-peer-core-alias = refl
  no-server-core-alias : K.step (K.serverStep (E.run (S.run (S.runOutbound (O.acquire F.caller A.configureOK))))) (F.at F.c14 F.k10) ≡ nothing
  no-server-core-alias = refl
  no-reserved-peer-caller-reuse : K.step (K.serverStep (E.run (S.acceptedFork F.caller X.F.r₀))) (F.at F.source0 F.k8) ≡ nothing
  no-reserved-peer-caller-reuse = refl
  no-reserved-peer-child-reuse : K.step (K.serverStep (E.run (S.acceptedFork (ident 20) (Shared.admission Actors.key₀ (ident 20) F.child 10)))) (F.at F.source0 F.k8) ≡ nothing
  no-reserved-peer-child-reuse = refl
  no-reserved-peer-socket-reuse : K.step (K.serverStep (E.run (S.acceptedFork (ident 20) (Shared.admission Actors.key₀ F.sock (ident 21) 10)))) (F.at F.source0 F.k8) ≡ nothing
  no-reserved-peer-socket-reuse = refl
  no-raw-worker-reuse-by-peer : K.step (ps (Sub.forkJob Actors.w₀ (ident 21) F.sock)) (F.at F.source0 F.k7) ≡ nothing
  no-raw-worker-reuse-by-peer = refl
  no-logical-protocol-result : K.step (ps (Sub.publishInitiatorResult (ident 0) 1)) F.two ≡ nothing
  no-logical-protocol-result = refl

  -- An unowned request also has an initialized birth through the common route.
  -- Its future child/socket must be reserved before either physical allocation.
  foreignRequest : A.Request
  foreignRequest = A.acquireRequest (remote Actors.key₁) (ident 21) (ident 20) outbound nothing
  foreignSource : O.Configuration
  foreignSource = record F.source0
    { acquiring = (ident 20 , A.frame foreignRequest A.selecting) ∷ [] }
  foreignContext : C.Context
  foreignContext = record F.k0 { regions = (ident 20 , Cancel.ordinary) ∷ [] }
  foreignState : K.State
  foreignState = F.at foreignSource foreignContext
  foreign-birth : K.step (K.coreStep (O.beginAcquire (ident 20) foreignRequest)) F.two ≡ just foreignState
  foreign-birth = refl
  foreignActions : List K.Action
  foreignActions = K.serverStep (E.run (S.acceptedFork Actors.w₀ X.F.r₀)) ∷
    K.serverStep (E.run (S.acceptedFork Actors.w₁ X.F.r₁)) ∷
    K.coreStep (O.beginAcquire (ident 20) foreignRequest) ∷ []
  abstract
    initialized-foreign : K.Executes F.start foreignActions foreignState
    initialized-foreign = K.next step1 (K.next step2 (K.next foreign-birth K.done))
  foreign-supply : Inv.Valid foreignState
  foreign-supply = Inv.from-initial-valid initializer (All.[] , All.[]) initialized-foreign
  no-unowned-child-reuse : K.step (K.serverStep (E.run (S.acceptedFork (ident 30)
    (Shared.admission Actors.key₀ (ident 30) (ident 21) 10)))) foreignState ≡ nothing
  no-unowned-child-reuse = refl
  no-unopened-socket-reuse : K.step (K.serverStep (E.run (S.acceptedFork (ident 30)
    (Shared.admission Actors.key₀ (ident 20) (ident 31) 10)))) foreignState ≡ nothing
  no-unopened-socket-reuse = refl
  no-new-caller-after-callback : K.step (K.coreStep (O.beginAcquire (ident 20) foreignRequest)) F.returned ≡ nothing
  no-new-caller-after-callback = refl

  -- The successful callback step supplies closure, with no separate closure input.
  beforeReturnActions : List K.Action
  beforeReturnActions = (K.serverStep (E.run (S.acceptedFork Actors.w₀ X.F.r₀))) ∷ (K.serverStep (E.run (S.acceptedFork Actors.w₁ X.F.r₁))) ∷ (ps (Sub.publishPublicState)) ∷ (ps (Sub.sampleTime 0)) ∷ (ps (Sub.registerWakeup)) ∷ (ps (Sub.selectPolicy (remote Actors.key₁ ∷ []))) ∷ (ps (Sub.applyAt 0)) ∷ (ps (Sub.publishCounters)) ∷ (ps (Sub.traceSelection)) ∷ (ps (Sub.forkJob F.caller F.child F.sock)) ∷ (ps (Sub.registerJob)) ∷ (ps (Sub.jobStep F.jobId J.enter)) ∷ (cm (A.select nothing)) ∷ (cm (A.readCounters)) ∷ (cm (A.newPromise)) ∷ (cm (A.openOK)) ∷ (sc (Scope.beginUnwind)) ∷ (sc (Scope.requestCancel)) ∷ (sc (Scope.deliverCancel)) ∷ (sc (Scope.bodyExit Scope.churn)) ∷ (sc (Scope.publishResult Scope.churn)) ∷ (sc (Scope.join)) ∷ (sc (Scope.requestCancel)) ∷ (sc (Scope.deliverCancel)) ∷ (gp (GP.beginClose (F.jobId ∷ []))) ∷ (gp GP.requestCancel) ∷ (gp (GP.deliverCancellation F.err)) ∷ (admit Admission.take) ∷ (gp (GP.cleanup F.jobId Cancel.closeSocket)) ∷ (admit Admission.countLimit) ∷ (admit Admission.allocatePromise) ∷ (admit Admission.chooseEntry) ∷ (admit Admission.failFork) ∷ (admit Admission.restore) ∷ (gp (GP.cleanup F.jobId Cancel.removeReservation)) ∷ (gp (GP.cleanup F.jobId Cancel.readCounters)) ∷ (gp (GP.bodyUnwound F.jobId)) ∷ (gp (GP.deregisterCancelled F.jobId)) ∷ (gp (GP.publishAsyncResult F.jobId)) ∷ (gp GP.join) ∷ (gp GP.finishClose) ∷ (sc (Scope.bodyExit Scope.governor)) ∷ (sc (Scope.publishResult Scope.governor)) ∷ (sc (Scope.join)) ∷ (sc (Scope.requestCancel)) ∷ (sc (Scope.deliverCancel)) ∷ (sc (Scope.bodyExit Scope.localRoot)) ∷ (sc (Scope.publishResult Scope.localRoot)) ∷ (sc (Scope.join)) ∷ (sc (Scope.requestCancel)) ∷ (sc (Scope.deliverCancel)) ∷ (sc (Scope.bodyExit Scope.ledger)) ∷ (sc (Scope.publishResult Scope.ledger)) ∷ (sc (Scope.join)) ∷ (sc (Scope.finishClose)) ∷ (K.peerStep (PS.beginMonitorClose [])) ∷ (K.peerStep PS.finishMonitorClose) ∷ []
  abstract
    initialized-before-return : K.Executes F.start beforeReturnActions (F.at F.finalSource F.kdone)
    initialized-before-return = K.next step1 (K.next step2 (K.next step3 (K.next step4 (K.next step5 (K.next step6 (K.next step7 (K.next step8 (K.next step9 (K.next step10 (K.next step11 (K.next step12 (K.next step13 (K.next step14 (K.next step15 (K.next step16 (K.next step17 (K.next step18 (K.next step19 (K.next step20 (K.next step21 (K.next step22 (K.next step23 (K.next step24 (K.next step25 (K.next step26 (K.next step27 (K.next step28 (K.next step29 (K.next step30 (K.next step31 (K.next step32 (K.next step33 (K.next step34 (K.next step35 (K.next step36 (K.next step37 (K.next step38 (K.next step39 (K.next step40 (K.next step41 (K.next step42 (K.next step43 (K.next step44 (K.next step45 (K.next step46 (K.next step47 (K.next step48 (K.next step49 (K.next step50 (K.next step51 (K.next step52 (K.next step53 (K.next step54 (K.next step55 (K.next step56 (K.next step57 (K.done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  callback-certificates : Facts.Certificates (F.at F.finalSource F.kdone)
  callback-certificates = Facts.callback-from-initial initializer initialized-before-return step58

-- A second initialized history keeps a real pending IG release and another raw
-- worker's lease across peer-scope closure, then runs the checked nonempty exit.
module IGExit where
  open import Data.Bool using (true; false)
  open import Data.List using (List; []; _∷_)
  import Data.List.Relation.Unary.All as All
  open import Data.Maybe using (just; nothing)
  open import Data.Product using (_,_)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import ConnectionManagement.Domain hiding (worker; local; mux)
  import ConnectionManagement.State as Shared
  import ConnectionManagement.Machine as Machine
  import ConnectionManagement.OutboundMachine as O
  import ConnectionManagement.Subsystem
  import ConnectionManagement.ServerAdmission as Server
  import ConnectionManagement.ServerIGExit as Exit
  import ConnectionManagement.ServerPeers as Combined
  import ConnectionManagement.PeerContext as Context
  import ConnectionManagement.PeerSupervision as Supervision
  import ConnectionManagement.Properties.ServerPeers as Proof
  import ConnectionManagement.Properties.ServerPeersSupply as Supply
  module Data = Fixtures
  import ConnectionManagement.Negative.ServerIGExitRelease as R
  open import ConnectionManagement.Negative.ServerIGExitRelease using (base; ig; release)
  import ConnectionManagement.Negative.ServerIGExitFixtures as X
  import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
  import ConnectionManagement.Scenarios.Admission as A
  import ConnectionManagement.Rules.Server as Admission
  import ConnectionManagement.Rules.Handshake as Handshake
  import ConnectionManagement.Rules.InboundRelease as Release
  import ConnectionManagement.Rules.IGRegistration as IG
  import ConnectionManagement.Rules.AsyncScope as Scope
  import ConnectionManagement.MuxPublicationUnwind as Publication
  import ConnectionManagement.HandlerSupervision as H
  open import ConnectionManagement.Negative.ServerAdmissionPrefixSupport using (admit; consume; handler; mux)
  private
    module K = Combined I.bearerClosed Data.classify
    module E = Exit I.bearerClosed
    module S = Server I.bearerClosed
    module PS = Supervision Data.classify
    module GP = PS.GP
    module C = Context Data.classify
    module Facts = Proof I.bearerClosed Data.classify
    module Inv = Supply I.bearerClosed Data.classify
    module F = X.F
    module N = Publication I.bearerClosed
    module U = N.U

  wrap : E.State → K.State
  wrap e = K.combined e Data.k0
  initializer : K.initial (O.initial (Machine.initial Shared.responderMode F.empty)) Data.settings ≡ just (wrap X.start)
  initializer = refl
  emptyClosing emptyClosed emptyScopes emptyMonitors emptyDone : C.Context
  emptyClosing = record Data.k0
    { scopes = Data.q8; governorPool = record (C.governorPool Data.k0) { phase = GP.Pool.closing } }
  emptyClosed = record emptyClosing { governorPool = record (C.governorPool emptyClosing) { phase = GP.Pool.closedPool } }
  emptyScopes = record emptyClosed { scopes = Data.q22 }
  emptyMonitors = record emptyScopes { monitorPool = record (C.monitorPool emptyScopes) { phase = PS.Pool.closing } }
  emptyDone = record emptyScopes { monitorPool = record (C.monitorPool emptyScopes) { phase = PS.Pool.closedPool } }

  step1 : K.step (K.serverStep (E.run (S.acceptedFork A.w₀ F.r₀))) (wrap (X.start)) ≡ just (wrap (base F.one))
  step1 = Facts.lift-server-step (E.run (S.acceptedFork A.w₀ F.r₀)) (X.start) Data.k0 refl R.birth1
  step2 : K.step (K.serverStep (E.run (S.acceptedFork A.w₁ F.r₁))) (wrap (base F.one)) ≡ just (wrap (base F.two))
  step2 = Facts.lift-server-step (E.run (S.acceptedFork A.w₁ F.r₁)) (base F.one) Data.k0 refl R.birth2
  step3 : K.step (K.serverStep (E.run (admit A.w₀ Admission.take))) (wrap (base F.two)) ≡ just (wrap (base F.p1))
  step3 = Facts.lift-server-step (E.run (admit A.w₀ Admission.take)) (base F.two) Data.k0 refl R.birth3
  step4 : K.step (K.serverStep (E.run (admit A.w₀ Admission.countLimit))) (wrap (base F.p1)) ≡ just (wrap (base F.p2))
  step4 = Facts.lift-server-step (E.run (admit A.w₀ Admission.countLimit)) (base F.p1) Data.k0 refl R.birth4
  step5 : K.step (K.serverStep (E.run (admit A.w₀ Admission.allocatePromise))) (wrap (base F.p2)) ≡ just (wrap (base F.p3))
  step5 = Facts.lift-server-step (E.run (admit A.w₀ Admission.allocatePromise)) (base F.p2) Data.k0 refl R.birth5
  step6 : K.step (K.serverStep (E.run (admit A.w₀ Admission.chooseEntry))) (wrap (base F.p3)) ≡ just (wrap (base F.p4))
  step6 = Facts.lift-server-step (E.run (admit A.w₀ Admission.chooseEntry)) (base F.p3) Data.k0 refl R.birth6
  step7 : K.step (K.serverStep (E.run (admit A.w₀ Admission.fork))) (wrap (base F.p4)) ≡ just (wrap (base F.p5))
  step7 = Facts.lift-server-step (E.run (admit A.w₀ Admission.fork)) (base F.p4) Data.k0 refl R.birth7
  step8 : K.step (K.serverStep (E.run (admit A.w₀ Admission.putMapBack))) (wrap (base F.p5)) ≡ just (wrap (base F.p6))
  step8 = Facts.lift-server-step (E.run (admit A.w₀ Admission.putMapBack)) (base F.p5) Data.k0 refl R.birth8
  step9 : K.step (K.serverStep (E.run (admit A.w₀ Admission.readCounters))) (wrap (base F.p6)) ≡ just (wrap (base F.p7))
  step9 = Facts.lift-server-step (E.run (admit A.w₀ Admission.readCounters)) (base F.p6) Data.k0 refl R.birth9
  step10 : K.step (K.serverStep (E.run (handler (H.enterHandshake A.child₀)))) (wrap (base F.p7)) ≡ just (wrap (base F.s1))
  step10 = Facts.lift-server-step (E.run (handler (H.enterHandshake A.child₀))) (base F.p7) Data.k0 refl R.handshake1
  step11 : K.step (K.serverStep (E.run (mux (U.negotiate A.child₀ I.ps duplex)))) (wrap (base F.s1)) ≡ just (wrap (base F.s2))
  step11 = Facts.lift-server-step (E.run (mux (U.negotiate A.child₀ I.ps duplex))) (base F.s1) Data.k0 refl R.handshake2
  step12 : K.step (K.serverStep (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0))))) (wrap (base F.s2)) ≡ just (wrap (base F.s3))
  step12 = Facts.lift-server-step (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0)))) (base F.s2) Data.k0 refl R.handshake3
  step13 : K.step (K.serverStep (E.run (mux (U.publishSuccess A.child₀)))) (wrap (base F.s3)) ≡ just (wrap (base F.s4))
  step13 = Facts.lift-server-step (E.run (mux (U.publishSuccess A.child₀))) (base F.s3) Data.k0 refl R.handshake4
  step14 : K.step (K.serverStep (E.run (consume Handshake.readResult))) (wrap (base F.s4)) ≡ just (wrap (base F.s5))
  step14 = Facts.lift-server-step (E.run (consume Handshake.readResult)) (base F.s4) Data.k0 refl R.handshake5
  step15 : K.step (K.serverStep (E.run (consume Handshake.commitResult))) (wrap (base F.s5)) ≡ just (wrap (base F.s6))
  step15 = Facts.lift-server-step (E.run (consume Handshake.commitResult)) (base F.s5) Data.k0 refl R.handshake6
  step16 : K.step (K.serverStep (E.run (consume Handshake.readResultCounters))) (wrap (base F.s6)) ≡ just (wrap (base F.s7))
  step16 = Facts.lift-server-step (E.run (consume Handshake.readResultCounters)) (base F.s6) Data.k0 refl R.handshake7
  step17 : K.step (K.serverStep (E.run (consume Handshake.enqueueInbound))) (wrap (base F.s7)) ≡ just (wrap (base F.s8))
  step17 = Facts.lift-server-step (E.run (consume Handshake.enqueueInbound)) (base F.s7) Data.k0 refl R.handshake8
  step18 : K.step (K.serverStep (E.run (consume Handshake.returnResult))) (wrap (base F.s8)) ≡ just (wrap (base F.s9))
  step18 = Facts.lift-server-step (E.run (consume Handshake.returnResult)) (base F.s8) Data.k0 refl R.handshake9
  step19 : K.step (K.serverStep (E.run (S.workerReturned A.w₀))) (wrap (base F.s9)) ≡ just (wrap (base F.s10))
  step19 = Facts.lift-server-step (E.run (S.workerReturned A.w₀)) (base F.s9) Data.k0 refl R.handshake10
  step20 : K.step (K.serverStep (E.run (S.workerResult A.w₀))) (wrap (base F.s10)) ≡ just (wrap (X.admitted))
  step20 = Facts.lift-server-step (E.run (S.workerResult A.w₀)) (base F.s10) Data.k0 refl R.handshake11
  step21 : K.step (K.serverStep (ig (IG.captureTime 10))) (wrap (X.admitted)) ≡ just (wrap (X.g1))
  step21 = Facts.lift-server-step (ig (IG.captureTime 10)) (X.admitted) Data.k0 refl R.register1
  step22 : K.step (K.serverStep (ig IG.registerInactivity)) (wrap (X.g1)) ≡ just (wrap (X.g2))
  step22 = Facts.lift-server-step (ig IG.registerInactivity) (X.g1) Data.k0 refl R.register2
  step23 : K.step (K.serverStep (ig IG.selectBatch)) (wrap (X.g2)) ≡ just (wrap (X.g3))
  step23 = Facts.lift-server-step (ig IG.selectBatch) (X.g2) Data.k0 refl R.register3
  step24 : K.step (K.serverStep (ig IG.readEvent)) (wrap (X.g3)) ≡ just (wrap (X.g4))
  step24 = Facts.lift-server-step (ig IG.readEvent) (X.g3) Data.k0 refl R.register4
  step25 : K.step (K.serverStep (ig IG.registerIdleTimer)) (wrap (X.g4)) ≡ just (wrap (X.g5))
  step25 = Facts.lift-server-step (ig IG.registerIdleTimer) (X.g4) Data.k0 refl R.register5
  step26 : K.step (K.serverStep (ig IG.runResponders)) (wrap (X.g5)) ≡ just (wrap (X.g6))
  step26 = Facts.lift-server-step (ig IG.runResponders) (X.g5) Data.k0 refl R.register6
  step27 : K.step (K.serverStep (ig IG.finishBatch)) (wrap (X.g6)) ≡ just (wrap (X.g7))
  step27 = Facts.lift-server-step (ig IG.finishBatch) (X.g6) Data.k0 refl R.register7
  step28 : K.step (K.serverStep (ig (IG.captureTime 11))) (wrap (X.g7)) ≡ just (wrap (X.r1))
  step28 = Facts.lift-server-step (ig (IG.captureTime 11)) (X.g7) Data.k0 refl R.call1
  step29 : K.step (K.serverStep (ig IG.registerInactivity)) (wrap (X.r1)) ≡ just (wrap (X.r2))
  step29 = Facts.lift-server-step (ig IG.registerInactivity) (X.r1) Data.k0 refl R.call2
  step30 : K.step (K.serverStep (ig (IG.expireTimer (ident 1)))) (wrap (X.r2)) ≡ just (wrap (X.r3))
  step30 = Facts.lift-server-step (ig (IG.expireTimer (ident 1))) (X.r2) Data.k0 refl R.call3
  step31 : K.step (K.serverStep (ig IG.selectBatch)) (wrap (X.r3)) ≡ just (wrap (X.r4))
  step31 = Facts.lift-server-step (ig IG.selectBatch) (X.r3) Data.k0 refl R.call4
  step32 : K.step (K.serverStep (ig IG.readEvent)) (wrap (X.r4)) ≡ just (wrap (X.r5))
  step32 = Facts.lift-server-step (ig IG.readEvent) (X.r4) Data.k0 refl R.call5
  step33 : K.step (K.serverStep (release Release.enter)) (wrap (X.r5)) ≡ just (wrap (X.r6))
  step33 = Facts.lift-server-step (release Release.enter) (X.r5) Data.k0 refl R.call6
  step34 : K.step (K.serverStep (release Release.transact)) (wrap (X.r6)) ≡ just (wrap (X.r7))
  step34 = Facts.lift-server-step (release Release.transact) (X.r6) Data.k0 refl R.call7
  step35 : K.step (K.serverStep (E.run (admit A.w₁ Admission.take))) (wrap (X.r7)) ≡ just (wrap (X.held))
  step35 = Facts.lift-server-step (E.run (admit A.w₁ Admission.take)) (X.r7) Data.k0 refl R.call8
  step36 : K.step (K.peerStep (PS.scope (Scope.beginUnwind))) (wrap (X.held)) ≡ just (K.combined X.held (Data.atScope Data.q1 Data.k0))
  step36 = refl
  step37 : K.step (K.peerStep (PS.scope (Scope.requestCancel))) (K.combined X.held (Data.atScope Data.q1 Data.k0)) ≡ just (K.combined X.held (Data.atScope Data.q2 Data.k0))
  step37 = refl
  step38 : K.step (K.peerStep (PS.scope (Scope.deliverCancel))) (K.combined X.held (Data.atScope Data.q2 Data.k0)) ≡ just (K.combined X.held (Data.atScope Data.q3 Data.k0))
  step38 = refl
  step39 : K.step (K.peerStep (PS.scope (Scope.bodyExit Scope.churn))) (K.combined X.held (Data.atScope Data.q3 Data.k0)) ≡ just (K.combined X.held (Data.atScope Data.q4 Data.k0))
  step39 = refl
  step40 : K.step (K.peerStep (PS.scope (Scope.publishResult Scope.churn))) (K.combined X.held (Data.atScope Data.q4 Data.k0)) ≡ just (K.combined X.held (Data.atScope Data.q5 Data.k0))
  step40 = refl
  step41 : K.step (K.peerStep (PS.scope (Scope.join))) (K.combined X.held (Data.atScope Data.q5 Data.k0)) ≡ just (K.combined X.held (Data.atScope Data.q6 Data.k0))
  step41 = refl
  step42 : K.step (K.peerStep (PS.scope (Scope.requestCancel))) (K.combined X.held (Data.atScope Data.q6 Data.k0)) ≡ just (K.combined X.held (Data.atScope Data.q7 Data.k0))
  step42 = refl
  step43 : K.step (K.peerStep (PS.scope (Scope.deliverCancel))) (K.combined X.held (Data.atScope Data.q7 Data.k0)) ≡ just (K.combined X.held (Data.atScope Data.q8 Data.k0))
  step43 = refl
  step44 : K.step (K.peerStep (PS.run (GP.beginClose []))) (K.combined X.held (Data.atScope Data.q8 Data.k0)) ≡ just (K.combined X.held emptyClosing)
  step44 = refl
  step45 : K.step (K.peerStep (PS.run GP.finishClose)) (K.combined X.held emptyClosing) ≡ just (K.combined X.held emptyClosed)
  step45 = refl
  step46 : K.step (K.peerStep (PS.scope (Scope.bodyExit Scope.governor))) (K.combined X.held emptyClosed) ≡ just (K.combined X.held (Data.atScope Data.q9 emptyClosed))
  step46 = refl
  step47 : K.step (K.peerStep (PS.scope (Scope.publishResult Scope.governor))) (K.combined X.held (Data.atScope Data.q9 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q10 emptyClosed))
  step47 = refl
  step48 : K.step (K.peerStep (PS.scope (Scope.join))) (K.combined X.held (Data.atScope Data.q10 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q11 emptyClosed))
  step48 = refl
  step49 : K.step (K.peerStep (PS.scope (Scope.requestCancel))) (K.combined X.held (Data.atScope Data.q11 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q12 emptyClosed))
  step49 = refl
  step50 : K.step (K.peerStep (PS.scope (Scope.deliverCancel))) (K.combined X.held (Data.atScope Data.q12 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q13 emptyClosed))
  step50 = refl
  step51 : K.step (K.peerStep (PS.scope (Scope.bodyExit Scope.localRoot))) (K.combined X.held (Data.atScope Data.q13 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q14 emptyClosed))
  step51 = refl
  step52 : K.step (K.peerStep (PS.scope (Scope.publishResult Scope.localRoot))) (K.combined X.held (Data.atScope Data.q14 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q15 emptyClosed))
  step52 = refl
  step53 : K.step (K.peerStep (PS.scope (Scope.join))) (K.combined X.held (Data.atScope Data.q15 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q16 emptyClosed))
  step53 = refl
  step54 : K.step (K.peerStep (PS.scope (Scope.requestCancel))) (K.combined X.held (Data.atScope Data.q16 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q17 emptyClosed))
  step54 = refl
  step55 : K.step (K.peerStep (PS.scope (Scope.deliverCancel))) (K.combined X.held (Data.atScope Data.q17 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q18 emptyClosed))
  step55 = refl
  step56 : K.step (K.peerStep (PS.scope (Scope.bodyExit Scope.ledger))) (K.combined X.held (Data.atScope Data.q18 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q19 emptyClosed))
  step56 = refl
  step57 : K.step (K.peerStep (PS.scope (Scope.publishResult Scope.ledger))) (K.combined X.held (Data.atScope Data.q19 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q20 emptyClosed))
  step57 = refl
  step58 : K.step (K.peerStep (PS.scope (Scope.join))) (K.combined X.held (Data.atScope Data.q20 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q21 emptyClosed))
  step58 = refl
  step59 : K.step (K.peerStep (PS.scope (Scope.finishClose))) (K.combined X.held (Data.atScope Data.q21 emptyClosed)) ≡ just (K.combined X.held (Data.atScope Data.q22 emptyClosed))
  step59 = refl
  step60 : K.step (K.peerStep (PS.beginMonitorClose [])) (K.combined X.held (Data.atScope Data.q22 emptyClosed)) ≡ just (K.combined X.held emptyMonitors)
  step60 = refl
  step61 : K.step (K.peerStep PS.finishMonitorClose) (K.combined X.held emptyMonitors) ≡ just (K.combined X.held emptyDone)
  step61 = refl
  step62 : K.step (K.serverStep (E.run (S.scope S.returnAction))) (K.combined (X.held) emptyDone) ≡ just (K.combined (X.atScope S.actionBodyExited true X.held) emptyDone)
  step62 = Facts.lift-server-step (E.run (S.scope S.returnAction)) (X.held) emptyDone refl R.scope1
  step63 : K.step (K.serverStep (E.run (S.scope S.publishActionResult))) (K.combined (X.atScope S.actionBodyExited true X.held) emptyDone) ≡ just (K.combined (X.atScope S.actionResultAvailable true X.held) emptyDone)
  step63 = Facts.lift-server-step (E.run (S.scope S.publishActionResult)) (X.atScope S.actionBodyExited true X.held) emptyDone refl R.scope2
  step64 : K.step (K.serverStep (E.run (S.scope S.selectActionWinner))) (K.combined (X.atScope S.actionResultAvailable true X.held) emptyDone) ≡ just (K.combined (X.atScope S.closingAccept true X.held) emptyDone)
  step64 = Facts.lift-server-step (E.run (S.scope S.selectActionWinner)) (X.atScope S.actionResultAvailable true X.held) emptyDone refl R.scope3
  step65 : K.step (K.serverStep (E.run (S.scope S.requestAcceptCancel))) (K.combined (X.atScope S.closingAccept true X.held) emptyDone) ≡ just (K.combined (X.atScope S.acceptCancelRequested true X.held) emptyDone)
  step65 = Facts.lift-server-step (E.run (S.scope S.requestAcceptCancel)) (X.atScope S.closingAccept true X.held) emptyDone refl R.scope4
  step66 : K.step (K.serverStep (E.run (S.scope S.deliverAcceptAtWait))) (K.combined (X.atScope S.acceptCancelRequested true X.held) emptyDone) ≡ just (K.combined (X.atScope S.acceptCancelDelivered true X.held) emptyDone)
  step66 = Facts.lift-server-step (E.run (S.scope S.deliverAcceptAtWait)) (X.atScope S.acceptCancelRequested true X.held) emptyDone refl R.scope5
  step67 : K.step (K.serverStep (E.run (S.scope S.closeListener))) (K.combined (X.atScope S.acceptCancelDelivered true X.held) emptyDone) ≡ just (K.combined (X.atScope S.acceptBodyExited false X.held) emptyDone)
  step67 = Facts.lift-server-step (E.run (S.scope S.closeListener)) (X.atScope S.acceptCancelDelivered true X.held) emptyDone refl R.scope6
  step68 : K.step (K.serverStep (E.run (S.scope S.publishAcceptResult))) (K.combined (X.atScope S.acceptBodyExited false X.held) emptyDone) ≡ just (K.combined (X.atScope S.acceptResultAvailable false X.held) emptyDone)
  step68 = Facts.lift-server-step (E.run (S.scope S.publishAcceptResult)) (X.atScope S.acceptBodyExited false X.held) emptyDone refl R.scope7
  step69 : K.step (K.serverStep (E.run (S.scope S.joinAccept))) (K.combined (X.atScope S.acceptResultAvailable false X.held) emptyDone) ≡ just (K.combined (X.atScope S.acceptJoined false X.held) emptyDone)
  step69 = Facts.lift-server-step (E.run (S.scope S.joinAccept)) (X.atScope S.acceptResultAvailable false X.held) emptyDone refl R.scope8
  step70 : K.step (K.serverStep (E.run (S.scope S.traceStopped))) (K.combined (X.atScope S.acceptJoined false X.held) emptyDone) ≡ just (K.combined (X.atScope S.serverStopped false X.held) emptyDone)
  step70 = Facts.lift-server-step (E.run (S.scope S.traceStopped)) (X.atScope S.acceptJoined false X.held) emptyDone refl R.scope9
  step71 : K.step (K.serverStep (E.run (S.scope S.cancelJoinReturnedAction))) (K.combined (X.atScope S.serverStopped false X.held) emptyDone) ≡ just (K.combined (X.atScope S.actionJoined false X.held) emptyDone)
  step71 = Facts.lift-server-step (E.run (S.scope S.cancelJoinReturnedAction)) (X.atScope S.serverStopped false X.held) emptyDone refl R.scope10
  step72 : K.step (K.serverStep (E.run (S.scope S.requestIGCancel))) (K.combined (X.atScope S.actionJoined false X.held) emptyDone) ≡ just (K.combined (X.atScope S.igCancelRequested false X.held) emptyDone)
  step72 = Facts.lift-server-step (E.run (S.scope S.requestIGCancel)) (X.atScope S.actionJoined false X.held) emptyDone refl R.scope11
  step73 : K.step (K.serverStep (E.receive E.releaseCounters X.err)) (K.combined (X.atScope S.igCancelRequested false X.held) emptyDone) ≡ just (K.combined (X.caughtRelease) emptyDone)
  step73 = Facts.lift-server-step (E.receive E.releaseCounters X.err) (X.atScope S.igCancelRequested false X.held) emptyDone refl R.exit1
  step74 : K.step (K.serverStep (E.run (S.scope S.deactivateIG))) (K.combined (X.caughtRelease) emptyDone) ≡ just (K.combined (X.inactive) emptyDone)
  step74 = Facts.lift-server-step (E.run (S.scope S.deactivateIG)) (X.caughtRelease) emptyDone refl R.exit2
  step75 : K.step (K.serverStep (E.run (S.scope S.flushIG))) (K.combined (X.inactive) emptyDone) ≡ just (K.combined (X.flushed) emptyDone)
  step75 = Facts.lift-server-step (E.run (S.scope S.flushIG)) (X.inactive) emptyDone refl R.exit3
  step76 : K.step (K.serverStep (E.captureSnapshot)) (K.combined (X.flushed) emptyDone) ≡ just (K.combined (X.snapshot) emptyDone)
  step76 = Facts.lift-server-step (E.captureSnapshot) (X.flushed) emptyDone refl R.exit4
  step77 : K.step (K.serverStep (E.invokeFinal)) (K.combined (X.snapshot) emptyDone) ≡ just (K.combined (X.invoked) emptyDone)
  step77 = Facts.lift-server-step (E.invokeFinal) (X.snapshot) emptyDone refl R.exit5
  step78 : K.step (K.serverStep (E.returnFinal)) (K.combined (X.invoked) emptyDone) ≡ just (K.combined (X.returned) emptyDone)
  step78 = Facts.lift-server-step (E.returnFinal) (X.invoked) emptyDone refl R.exit6
  step79 : K.step (K.serverStep (E.finishFinal)) (K.combined (X.returned) emptyDone) ≡ just (K.combined (X.bodyDone) emptyDone)
  step79 = Facts.lift-server-step (E.finishFinal) (X.returned) emptyDone refl R.exit7
  step80 : K.step (K.serverStep (E.run (S.scope S.publishIGResult))) (K.combined (X.bodyDone) emptyDone) ≡ just (K.combined (X.published) emptyDone)
  step80 = Facts.lift-server-step (E.run (S.scope S.publishIGResult)) (X.bodyDone) emptyDone refl R.exit8
  step81 : K.step (K.serverStep (E.run (S.scope S.joinIG))) (K.combined (X.published) emptyDone) ≡ just (K.combined (X.joined) emptyDone)
  step81 = Facts.lift-server-step (E.run (S.scope S.joinIG)) (X.published) emptyDone refl R.exit9

  actions : List K.Action
  actions = (K.serverStep (E.run (S.acceptedFork A.w₀ F.r₀))) ∷ (K.serverStep (E.run (S.acceptedFork A.w₁ F.r₁))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.take))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.countLimit))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.allocatePromise))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.chooseEntry))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.fork))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.putMapBack))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.readCounters))) ∷ (K.serverStep (E.run (handler (H.enterHandshake A.child₀)))) ∷ (K.serverStep (E.run (mux (U.negotiate A.child₀ I.ps duplex)))) ∷ (K.serverStep (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0))))) ∷ (K.serverStep (E.run (mux (U.publishSuccess A.child₀)))) ∷ (K.serverStep (E.run (consume Handshake.readResult))) ∷ (K.serverStep (E.run (consume Handshake.commitResult))) ∷ (K.serverStep (E.run (consume Handshake.readResultCounters))) ∷ (K.serverStep (E.run (consume Handshake.enqueueInbound))) ∷ (K.serverStep (E.run (consume Handshake.returnResult))) ∷ (K.serverStep (E.run (S.workerReturned A.w₀))) ∷ (K.serverStep (E.run (S.workerResult A.w₀))) ∷ (K.serverStep (ig (IG.captureTime 10))) ∷ (K.serverStep (ig IG.registerInactivity)) ∷ (K.serverStep (ig IG.selectBatch)) ∷ (K.serverStep (ig IG.readEvent)) ∷ (K.serverStep (ig IG.registerIdleTimer)) ∷ (K.serverStep (ig IG.runResponders)) ∷ (K.serverStep (ig IG.finishBatch)) ∷ (K.serverStep (ig (IG.captureTime 11))) ∷ (K.serverStep (ig IG.registerInactivity)) ∷ (K.serverStep (ig (IG.expireTimer (ident 1)))) ∷ (K.serverStep (ig IG.selectBatch)) ∷ (K.serverStep (ig IG.readEvent)) ∷ (K.serverStep (release Release.enter)) ∷ (K.serverStep (release Release.transact)) ∷ (K.serverStep (E.run (admit A.w₁ Admission.take))) ∷ (K.peerStep (PS.scope (Scope.beginUnwind))) ∷ (K.peerStep (PS.scope (Scope.requestCancel))) ∷ (K.peerStep (PS.scope (Scope.deliverCancel))) ∷ (K.peerStep (PS.scope (Scope.bodyExit Scope.churn))) ∷ (K.peerStep (PS.scope (Scope.publishResult Scope.churn))) ∷ (K.peerStep (PS.scope (Scope.join))) ∷ (K.peerStep (PS.scope (Scope.requestCancel))) ∷ (K.peerStep (PS.scope (Scope.deliverCancel))) ∷ (K.peerStep (PS.run (GP.beginClose []))) ∷ (K.peerStep (PS.run GP.finishClose)) ∷ (K.peerStep (PS.scope (Scope.bodyExit Scope.governor))) ∷ (K.peerStep (PS.scope (Scope.publishResult Scope.governor))) ∷ (K.peerStep (PS.scope (Scope.join))) ∷ (K.peerStep (PS.scope (Scope.requestCancel))) ∷ (K.peerStep (PS.scope (Scope.deliverCancel))) ∷ (K.peerStep (PS.scope (Scope.bodyExit Scope.localRoot))) ∷ (K.peerStep (PS.scope (Scope.publishResult Scope.localRoot))) ∷ (K.peerStep (PS.scope (Scope.join))) ∷ (K.peerStep (PS.scope (Scope.requestCancel))) ∷ (K.peerStep (PS.scope (Scope.deliverCancel))) ∷ (K.peerStep (PS.scope (Scope.bodyExit Scope.ledger))) ∷ (K.peerStep (PS.scope (Scope.publishResult Scope.ledger))) ∷ (K.peerStep (PS.scope (Scope.join))) ∷ (K.peerStep (PS.scope (Scope.finishClose))) ∷ (K.peerStep (PS.beginMonitorClose [])) ∷ (K.peerStep PS.finishMonitorClose) ∷ (K.serverStep (E.run (S.scope S.returnAction))) ∷ (K.serverStep (E.run (S.scope S.publishActionResult))) ∷ (K.serverStep (E.run (S.scope S.selectActionWinner))) ∷ (K.serverStep (E.run (S.scope S.requestAcceptCancel))) ∷ (K.serverStep (E.run (S.scope S.deliverAcceptAtWait))) ∷ (K.serverStep (E.run (S.scope S.closeListener))) ∷ (K.serverStep (E.run (S.scope S.publishAcceptResult))) ∷ (K.serverStep (E.run (S.scope S.joinAccept))) ∷ (K.serverStep (E.run (S.scope S.traceStopped))) ∷ (K.serverStep (E.run (S.scope S.cancelJoinReturnedAction))) ∷ (K.serverStep (E.run (S.scope S.requestIGCancel))) ∷ (K.serverStep (E.receive E.releaseCounters X.err)) ∷ (K.serverStep (E.run (S.scope S.deactivateIG))) ∷ (K.serverStep (E.run (S.scope S.flushIG))) ∷ (K.serverStep (E.captureSnapshot)) ∷ (K.serverStep (E.invokeFinal)) ∷ (K.serverStep (E.returnFinal)) ∷ (K.serverStep (E.finishFinal)) ∷ (K.serverStep (E.run (S.scope S.publishIGResult))) ∷ (K.serverStep (E.run (S.scope S.joinIG))) ∷ []
  beforeReceipt : List K.Action
  beforeReceipt = (K.serverStep (E.run (S.acceptedFork A.w₀ F.r₀))) ∷ (K.serverStep (E.run (S.acceptedFork A.w₁ F.r₁))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.take))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.countLimit))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.allocatePromise))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.chooseEntry))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.fork))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.putMapBack))) ∷ (K.serverStep (E.run (admit A.w₀ Admission.readCounters))) ∷ (K.serverStep (E.run (handler (H.enterHandshake A.child₀)))) ∷ (K.serverStep (E.run (mux (U.negotiate A.child₀ I.ps duplex)))) ∷ (K.serverStep (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0))))) ∷ (K.serverStep (E.run (mux (U.publishSuccess A.child₀)))) ∷ (K.serverStep (E.run (consume Handshake.readResult))) ∷ (K.serverStep (E.run (consume Handshake.commitResult))) ∷ (K.serverStep (E.run (consume Handshake.readResultCounters))) ∷ (K.serverStep (E.run (consume Handshake.enqueueInbound))) ∷ (K.serverStep (E.run (consume Handshake.returnResult))) ∷ (K.serverStep (E.run (S.workerReturned A.w₀))) ∷ (K.serverStep (E.run (S.workerResult A.w₀))) ∷ (K.serverStep (ig (IG.captureTime 10))) ∷ (K.serverStep (ig IG.registerInactivity)) ∷ (K.serverStep (ig IG.selectBatch)) ∷ (K.serverStep (ig IG.readEvent)) ∷ (K.serverStep (ig IG.registerIdleTimer)) ∷ (K.serverStep (ig IG.runResponders)) ∷ (K.serverStep (ig IG.finishBatch)) ∷ (K.serverStep (ig (IG.captureTime 11))) ∷ (K.serverStep (ig IG.registerInactivity)) ∷ (K.serverStep (ig (IG.expireTimer (ident 1)))) ∷ (K.serverStep (ig IG.selectBatch)) ∷ (K.serverStep (ig IG.readEvent)) ∷ (K.serverStep (release Release.enter)) ∷ (K.serverStep (release Release.transact)) ∷ (K.serverStep (E.run (admit A.w₁ Admission.take))) ∷ (K.peerStep (PS.scope (Scope.beginUnwind))) ∷ (K.peerStep (PS.scope (Scope.requestCancel))) ∷ (K.peerStep (PS.scope (Scope.deliverCancel))) ∷ (K.peerStep (PS.scope (Scope.bodyExit Scope.churn))) ∷ (K.peerStep (PS.scope (Scope.publishResult Scope.churn))) ∷ (K.peerStep (PS.scope (Scope.join))) ∷ (K.peerStep (PS.scope (Scope.requestCancel))) ∷ (K.peerStep (PS.scope (Scope.deliverCancel))) ∷ (K.peerStep (PS.run (GP.beginClose []))) ∷ (K.peerStep (PS.run GP.finishClose)) ∷ (K.peerStep (PS.scope (Scope.bodyExit Scope.governor))) ∷ (K.peerStep (PS.scope (Scope.publishResult Scope.governor))) ∷ (K.peerStep (PS.scope (Scope.join))) ∷ (K.peerStep (PS.scope (Scope.requestCancel))) ∷ (K.peerStep (PS.scope (Scope.deliverCancel))) ∷ (K.peerStep (PS.scope (Scope.bodyExit Scope.localRoot))) ∷ (K.peerStep (PS.scope (Scope.publishResult Scope.localRoot))) ∷ (K.peerStep (PS.scope (Scope.join))) ∷ (K.peerStep (PS.scope (Scope.requestCancel))) ∷ (K.peerStep (PS.scope (Scope.deliverCancel))) ∷ (K.peerStep (PS.scope (Scope.bodyExit Scope.ledger))) ∷ (K.peerStep (PS.scope (Scope.publishResult Scope.ledger))) ∷ (K.peerStep (PS.scope (Scope.join))) ∷ (K.peerStep (PS.scope (Scope.finishClose))) ∷ (K.peerStep (PS.beginMonitorClose [])) ∷ (K.peerStep PS.finishMonitorClose) ∷ []
  abstract
    initialized : K.Executes (wrap X.start) actions (K.combined X.joined emptyDone)
    initialized = K.next step1 (K.next step2 (K.next step3 (K.next step4 (K.next step5 (K.next step6 (K.next step7 (K.next step8 (K.next step9 (K.next step10 (K.next step11 (K.next step12 (K.next step13 (K.next step14 (K.next step15 (K.next step16 (K.next step17 (K.next step18 (K.next step19 (K.next step20 (K.next step21 (K.next step22 (K.next step23 (K.next step24 (K.next step25 (K.next step26 (K.next step27 (K.next step28 (K.next step29 (K.next step30 (K.next step31 (K.next step32 (K.next step33 (K.next step34 (K.next step35 (K.next step36 (K.next step37 (K.next step38 (K.next step39 (K.next step40 (K.next step41 (K.next step42 (K.next step43 (K.next step44 (K.next step45 (K.next step46 (K.next step47 (K.next step48 (K.next step49 (K.next step50 (K.next step51 (K.next step52 (K.next step53 (K.next step54 (K.next step55 (K.next step56 (K.next step57 (K.next step58 (K.next step59 (K.next step60 (K.next step61 (K.next step62 (K.next step63 (K.next step64 (K.next step65 (K.next step66 (K.next step67 (K.next step68 (K.next step69 (K.next step70 (K.next step71 (K.next step72 (K.next step73 (K.next step74 (K.next step75 (K.next step76 (K.next step77 (K.next step78 (K.next step79 (K.next step80 (K.next step81 (K.done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
    initialized-before-receipt : K.Executes (wrap X.start) beforeReceipt (K.combined X.held emptyDone)
    initialized-before-receipt = K.next step1 (K.next step2 (K.next step3 (K.next step4 (K.next step5 (K.next step6 (K.next step7 (K.next step8 (K.next step9 (K.next step10 (K.next step11 (K.next step12 (K.next step13 (K.next step14 (K.next step15 (K.next step16 (K.next step17 (K.next step18 (K.next step19 (K.next step20 (K.next step21 (K.next step22 (K.next step23 (K.next step24 (K.next step25 (K.next step26 (K.next step27 (K.next step28 (K.next step29 (K.next step30 (K.next step31 (K.next step32 (K.next step33 (K.next step34 (K.next step35 (K.next step36 (K.next step37 (K.next step38 (K.next step39 (K.next step40 (K.next step41 (K.next step42 (K.next step43 (K.next step44 (K.next step45 (K.next step46 (K.next step47 (K.next step48 (K.next step49 (K.next step50 (K.next step51 (K.next step52 (K.next step53 (K.next step54 (K.next step55 (K.next step56 (K.next step57 (K.next step58 (K.next step59 (K.next step60 (K.next step61 (K.done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  supply : Inv.Valid (K.combined X.joined emptyDone)
  supply = Inv.from-initial-valid initializer (All.[] , All.[]) initialized
  pending-call-survives-peer-close : Machine.inboundRelease (O.core (K.source (K.combined X.held emptyDone))) ≡ just X.writtenFrame
  pending-call-survives-peer-close = refl
  lease-survives-peer-close : Shared.mapCell (Shared.cm (Machine.world (O.core (K.source (K.combined X.held emptyDone))))) ≡ Shared.taken A.w₁
  lease-survives-peer-close = refl
  exact-shared-core-after-peer-close : K.source (K.combined X.held emptyDone) ≡ E.source X.held
  exact-shared-core-after-peer-close = refl
  peer-view-sees-final-ig-state : PS.cm (K.peers (K.combined X.joined emptyDone)) ≡ E.source X.joined
  peer-view-sees-final-ig-state = refl
  exact-call-archived : E.received (E.exit (K.server (K.combined X.joined emptyDone))) ≡ just X.receivedRelease
  exact-call-archived = refl
  no-whole-server-return : K.step (K.serverStep (E.run (S.scope S.finishServer))) (K.combined X.joined emptyDone) ≡ nothing
  no-whole-server-return = refl
  no-peer-owner-after-callback : K.step (K.peerStep (PS.run (GP.run ConnectionManagement.Subsystem.publishPublicState)))
    (K.combined (X.atScope S.actionBodyExited true X.held) emptyDone) ≡ nothing
  no-peer-owner-after-callback = refl


-- Physical initiator starts/results over the shared source. Fixtures and both
-- initialized and conditional controls stay together in this acceptance module.
module Protocols where
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat using (ℕ; _+_)
  import Data.Nat as Nat
  open import Data.List using (List; []; _∷_; _++_; map)
  import Data.List.Relation.Unary.All as All
  open import Data.Maybe using (Maybe; just; nothing)
  open import Data.Product using (_,_; proj₁; proj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl)
  open import Relation.Nullary using (yes; no)
  open import Class.DecEq using (_≟_)
  open import ConnectionManagement.Domain hiding (worker; local; mux; job)
  open import ConnectionManagement.Store using (Store; lookup; put)
  open import ConnectionManagement.IGTypes using (Protocol; clean; errored; hot; number)
  import ConnectionManagement.State as Shared
  import ConnectionManagement.Machine as Machine
  import ConnectionManagement.OutboundMachine as O
  import ConnectionManagement.Subsystem as Sub
  import ConnectionManagement.ServerAdmission as Server
  import ConnectionManagement.ServerIGExit as Exit
  import ConnectionManagement.ServerPeers as Combined
  import ConnectionManagement.PeerSupervision as Supervision
  import ConnectionManagement.PeerContext as Context
  import ConnectionManagement.MuxPublicationUnwind as Publication
  import ConnectionManagement.Properties.ServerPeers as Proof
  import ConnectionManagement.Properties.ServerPeersSupply as Supply
  import ConnectionManagement.Rules.OutboundAcquire as Acquire
  import ConnectionManagement.Rules.OutboundCases as Cases
  import ConnectionManagement.Rules.OutboundGovernor as G
  import ConnectionManagement.Rules.PeerJobs as J
  import ConnectionManagement.Rules.PeerActions as Peer
  import ConnectionManagement.Rules.IGRegistration as IG
  import ConnectionManagement.Rules.MuxRuntime as Mux
  import ConnectionManagement.Rules.MuxJobTypes as Types
  import ConnectionManagement.Rules.AsyncScope as Scope
  import ConnectionManagement.Rules.CallerCancellation as Cancel
  import ConnectionManagement.Rules.Server as Admission
  import ConnectionManagement.Rules.Handshake as Handshake
  import ConnectionManagement.HandlerSupervision as H
  import ConnectionManagement.Scenarios.Admission as A
  import ConnectionManagement.CSP.GovernorLifecycle as L
  import ConnectionManagement.Negative.GovernorPool as Prior
  import ConnectionManagement.Negative.PeerSupervisionScenarios as OldPeer
  import ConnectionManagement.Negative.ServerIGExitRelease as R
  open import ConnectionManagement.Negative.ServerIGExitRelease using (base; ig; release)
  import ConnectionManagement.Negative.ServerIGExitFixtures as X
  import ConnectionManagement.Negative.ServerIGExitProtocolFixtures as Y
  import ConnectionManagement.Negative.ServerIGExitProtocolPrefix as Prefix
  import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
  open import ConnectionManagement.Negative.ServerAdmissionPrefixSupport using (admit; consume; handler; mux)
  capability : HandleId → ℕ → Bool
  capability hid n with hid ≟ ident 0 | n Nat.≟ 1
  ... | yes _ | yes _ = true
  ... | _ | _ = false
  private
    module K = Combined I.bearerClosed Prior.classify
    module V = K.Protocols capability
    module E = Exit I.bearerClosed
    module S = Server I.bearerClosed
    module C = Context Prior.classify
    module PS = Supervision Prior.classify
    module GP = PS.GP
    module BFacts = Proof I.bearerClosed Prior.classify
    module Facts = BFacts.Protocols capability
    module Bounds = Supply I.bearerClosed Prior.classify
    module Inv = Bounds.Protocols capability
    module N = Publication I.bearerClosed
    module P = N.P
    module U = N.U
    module T = N.S
    module Pool = P.Pool
    module F = X.F

  -- Only CM-free peer metadata is reused. Every physical source transition
  -- below starts at the new wrapper initializer and is checked separately.
  -- Align governor samples with the preceding IG time 10. Only metadata is
  -- reused; absolute activation/promotion times are shifted consistently.
  shiftPeer : Peer.Peer → Peer.Peer
  shiftPeer p with Peer.promotedAt p
  ... | nothing = p
  ... | just time = record p { promotedAt = just (time + 10) }
  -- Activation completion also schedules an absolute failure-clear deadline.
  shiftDeadline : Maybe ℕ → Maybe ℕ
  shiftDeadline nothing = nothing
  shiftDeadline (just time) = just (time + 10)
  shiftG : G.State → G.State
  shiftG g = record g
    { establishedPeers = map (λ { (peer , info) → peer , record info { activateAt = G.activateAt info + 10 } }) (G.establishedPeers g)
    ; knownPeers = map (λ { (peer , info) → peer , record info { clearFailuresAt = shiftDeadline (G.clearFailuresAt info) } }) (G.knownPeers g) }
  shiftSelected : Sub.Selected → Sub.Selected
  shiftSelected (Sub.policy d) = Sub.policy (G.decision (shiftG (G.nextState d)) (G.launches d))
  shiftSelected (Sub.wakeup time) = Sub.wakeup (time + 10)
  shiftSelected (Sub.completion c) = Sub.completion c
  shiftSelected (Sub.monitor changes delays) = Sub.monitor changes delays
  shiftSelected (Sub.targets goal) = Sub.targets goal
  shiftPC : Sub.PC → Sub.PC
  shiftPC Sub.publishPublic = Sub.publishPublic
  shiftPC Sub.sampleInputs = Sub.sampleInputs
  shiftPC Sub.prepareWait = Sub.prepareWait
  shiftPC Sub.selecting = Sub.selecting
  shiftPC (Sub.cancelTimer chosen) = Sub.cancelTimer (shiftSelected chosen)
  shiftPC (Sub.apply chosen) = Sub.apply (shiftSelected chosen)
  shiftPC (Sub.publishView work) = Sub.publishView work
  shiftPC (Sub.traceDecision work) = Sub.traceDecision work
  shiftPC (Sub.launch work) = Sub.launch work
  shiftPC (Sub.register j work) = Sub.register j work
  shiftPC (Sub.completionAssertionFailed c) = Sub.completionAssertionFailed c
  shiftRaw : Sub.Configuration → Sub.Configuration
  shiftRaw raw = record raw
    { now = Sub.now raw + 10; privateState = shiftG (Sub.privateState raw); publicState = shiftG (Sub.publicState raw)
    ; pc = shiftPC (Sub.pc raw); world = record (Sub.world raw) { peers = map (λ { (ref , p) → ref , shiftPeer p }) (J.peers (Sub.world raw)) } }
  shiftContext : PS.State → C.Context
  shiftContext p = record (C.capture p) { subsystem = C.captureSub (shiftRaw (PS.machine p)) }
  k0 : C.Context
  k0 = C.capture OldPeer.p₀
  wrap : E.State → V.Runtime
  wrap e = V.runtime (K.combined e k0) V.empty
  initial : V.Runtime
  initial = wrap X.start
  initializer : V.initialize (O.initial (Machine.initial Shared.responderMode F.empty)) L.settings ≡ just initial
  initializer = refl
  model : Y.Model
  model = Y.s12
  k1 k2 k3 k4 k5 k6 k7 k8 k9 k10 kAcquired : C.Context
  k1 = C.capture OldPeer.p1
  k2 = shiftContext OldPeer.p2
  k3 = shiftContext OldPeer.p3
  k4 = shiftContext OldPeer.p4
  k5 = shiftContext OldPeer.p5
  k6 = shiftContext OldPeer.p6
  k7 = shiftContext OldPeer.p7
  k8 = shiftContext OldPeer.p8
  k9 = shiftContext OldPeer.p9
  k10 = shiftContext OldPeer.p10
  kAcquired = shiftContext OldPeer.p27
  req : Acquire.Request
  req = Acquire.acquireRequest L.peerAddr L.child (ident 10) outbound nothing
  result : Cases.Result
  result = Cases.connected A.key₀ duplex (ident 0)
  callFrame : Acquire.PC → Acquire.Runtime
  callFrame pc = (L.caller , Acquire.frame req pc) ∷ []
  reused : Y.Model
  reused = record model { world = record (Y.world model)
    { cm = record (Shared.cm (Y.world model))
      { entries = put (ident 0) (Shared.outboundDup A.key₀ A.child₀ (ident 0) ticking) (Shared.entries (Shared.cm (Y.world model))) } } }
  render : Y.Model → C.Context → Acquire.Runtime → Store WorkerId Cases.Result → ℕ → V.Front → V.Runtime
  render m k acqs results gen f = V.runtime (K.combined
    (K.setSource (record (Y.configuration m) { acquiring = acqs; acquired = results; randomGeneration = gen }) (Y.render m)) k) f
  beforeAcquire : C.Context → V.Runtime
  beforeAcquire k = render model k [] [] 0 V.empty
  at : Y.Model → C.Context → V.Front → V.Runtime
  at m k f = render m k [] ((L.caller , result) ∷ []) 1 f

  body0 : GP.Body
  body0 = GP.body (ident 0) Prior.work (G.establishedOK (ident 0))
  body1 : GP.Body
  body1 = GP.body (ident 1) (G.job G.activate L.peerAddr (just (ident 0))) G.succeeded
  g40 g41 g42 g0done g59 g60 : GP.Pool.State
  g40 = GP.pool (PS.governor OldPeer.m4)
  g41 = record g40 { handles = put (ident 0) (GP.Pool.deregisterPending GP.Pool.normalExit) (GP.Pool.handles g40); completions = body0 ∷ [] }
  g42 = record g41 { handles = put (ident 0) (GP.Pool.deregistered GP.Pool.normalExit) (GP.Pool.handles g41); registered = [] }
  g0done = record g42 { handles = put (ident 0) (GP.Pool.resultAvailable GP.Pool.normalExit) (GP.Pool.handles g42) }
  g59 = record g0done { handles = put (ident 1) GP.Pool.bodyRunning (GP.Pool.handles g0done); parentFork = just (ident 1) }
  g60 = record g59 { registered = ident 1 ∷ []; parentFork = nothing }
  ctx : Sub.Configuration → GP.Pool.State → C.Context
  ctx raw pool = record (C.capture OldPeer.m4) { subsystem = C.captureSub (shiftRaw raw); governorPool = pool }
  k34 : C.Context
  k34 = shiftContext OldPeer.p34
  k35 : C.Context
  k35 = shiftContext OldPeer.p35
  k36 : C.Context
  k36 = shiftContext OldPeer.p36
  k37 : C.Context
  k37 = shiftContext OldPeer.p37
  k38 : C.Context
  k38 = shiftContext OldPeer.p38
  k39 : C.Context
  k39 = shiftContext OldPeer.p39
  km1 : C.Context
  km1 = shiftContext OldPeer.m1
  km2 : C.Context
  km2 = shiftContext OldPeer.m2
  km3 : C.Context
  km3 = shiftContext OldPeer.m3
  km4 : C.Context
  km4 = shiftContext OldPeer.m4
  k41 : C.Context
  k41 = ctx L.c41 g41
  k42 : C.Context
  k42 = ctx L.c42 g42
  k43 : C.Context
  k43 = ctx L.c43 g0done
  k44 : C.Context
  k44 = ctx L.c44 g0done
  k45 : C.Context
  k45 = ctx L.c45 g0done
  k46 : C.Context
  k46 = ctx L.c46 g0done
  k47 : C.Context
  k47 = ctx L.c47 g0done
  k48 : C.Context
  k48 = ctx L.c48 g0done
  k49 : C.Context
  k49 = ctx L.c49 g0done
  k50 : C.Context
  k50 = ctx L.c50 g0done
  k51 : C.Context
  k51 = ctx L.c51 g0done
  k52 : C.Context
  k52 = ctx L.c52 g0done
  k53 : C.Context
  k53 = ctx L.c53 g0done
  k54 : C.Context
  k54 = ctx L.c54 g0done
  k55 : C.Context
  k55 = ctx L.c55 g0done
  k56 : C.Context
  k56 = ctx L.c56 g0done
  k57 : C.Context
  k57 = ctx L.c57 g0done
  k58 : C.Context
  k58 = ctx L.c58 g0done
  k59 : C.Context
  k59 = ctx L.c59 g59
  k60 : C.Context
  k60 = ctx L.c60 g60
  k61 : C.Context
  k61 = ctx L.c61 g60
  k62 : C.Context
  k62 = ctx L.c62 g60
  k63 : C.Context
  k63 = ctx L.c63 g60
  ps : Sub.Action → V.Event
  ps a = V.dispatch (K.peerStep (PS.run (GP.run a)))
  peerStep : PS.Action → V.Event
  peerStep a = V.dispatch (K.peerStep a)
  common : Acquire.Action → V.Event
  common a = V.dispatch (K.coreStep (O.acquire L.caller a))
  physicalStep : P.Action → V.Event
  physicalStep a = V.dispatch (V.physicalAction a)

  p1 : V.advance (V.dispatch (K.serverStep (E.run (S.acceptedFork A.w₀ F.r₀)))) (wrap (X.start)) ≡ just (wrap (base F.one))
  p1 = Facts.lift-dispatch (K.serverStep (E.run (S.acceptedFork A.w₀ F.r₀))) (K.combined (X.start) k0) V.empty refl
    (BFacts.lift-server-step (E.run (S.acceptedFork A.w₀ F.r₀)) (X.start) k0 refl R.birth1)
  p2 : V.advance (V.dispatch (K.serverStep (E.run (S.acceptedFork A.w₁ F.r₁)))) (wrap (base F.one)) ≡ just (wrap (base F.two))
  p2 = Facts.lift-dispatch (K.serverStep (E.run (S.acceptedFork A.w₁ F.r₁))) (K.combined (base F.one) k0) V.empty refl
    (BFacts.lift-server-step (E.run (S.acceptedFork A.w₁ F.r₁)) (base F.one) k0 refl R.birth2)
  p3 : V.advance (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.take)))) (wrap (base F.two)) ≡ just (wrap (base F.p1))
  p3 = Facts.lift-dispatch (K.serverStep (E.run (admit A.w₀ Admission.take))) (K.combined (base F.two) k0) V.empty refl
    (BFacts.lift-server-step (E.run (admit A.w₀ Admission.take)) (base F.two) k0 refl R.birth3)
  p4 : V.advance (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.countLimit)))) (wrap (base F.p1)) ≡ just (wrap (base F.p2))
  p4 = Facts.lift-dispatch (K.serverStep (E.run (admit A.w₀ Admission.countLimit))) (K.combined (base F.p1) k0) V.empty refl
    (BFacts.lift-server-step (E.run (admit A.w₀ Admission.countLimit)) (base F.p1) k0 refl R.birth4)
  p5 : V.advance (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.allocatePromise)))) (wrap (base F.p2)) ≡ just (wrap (base F.p3))
  p5 = Facts.lift-dispatch (K.serverStep (E.run (admit A.w₀ Admission.allocatePromise))) (K.combined (base F.p2) k0) V.empty refl
    (BFacts.lift-server-step (E.run (admit A.w₀ Admission.allocatePromise)) (base F.p2) k0 refl R.birth5)
  p6 : V.advance (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.chooseEntry)))) (wrap (base F.p3)) ≡ just (wrap (base F.p4))
  p6 = Facts.lift-dispatch (K.serverStep (E.run (admit A.w₀ Admission.chooseEntry))) (K.combined (base F.p3) k0) V.empty refl
    (BFacts.lift-server-step (E.run (admit A.w₀ Admission.chooseEntry)) (base F.p3) k0 refl R.birth6)
  p7 : V.advance (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.fork)))) (wrap (base F.p4)) ≡ just (wrap (base F.p5))
  p7 = Facts.lift-dispatch (K.serverStep (E.run (admit A.w₀ Admission.fork))) (K.combined (base F.p4) k0) V.empty refl
    (BFacts.lift-server-step (E.run (admit A.w₀ Admission.fork)) (base F.p4) k0 refl R.birth7)
  p8 : V.advance (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.putMapBack)))) (wrap (base F.p5)) ≡ just (wrap (base F.p6))
  p8 = Facts.lift-dispatch (K.serverStep (E.run (admit A.w₀ Admission.putMapBack))) (K.combined (base F.p5) k0) V.empty refl
    (BFacts.lift-server-step (E.run (admit A.w₀ Admission.putMapBack)) (base F.p5) k0 refl R.birth8)
  p9 : V.advance (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.readCounters)))) (wrap (base F.p6)) ≡ just (wrap (base F.p7))
  p9 = Facts.lift-dispatch (K.serverStep (E.run (admit A.w₀ Admission.readCounters))) (K.combined (base F.p6) k0) V.empty refl
    (BFacts.lift-server-step (E.run (admit A.w₀ Admission.readCounters)) (base F.p6) k0 refl R.birth9)
  p10 : V.advance (V.dispatch (K.serverStep (E.run (handler (H.enterHandshake A.child₀))))) (wrap (base F.p7)) ≡ just (wrap (base F.s1))
  p10 = Facts.lift-dispatch (K.serverStep (E.run (handler (H.enterHandshake A.child₀)))) (K.combined (base F.p7) k0) V.empty refl
    (BFacts.lift-server-step (E.run (handler (H.enterHandshake A.child₀))) (base F.p7) k0 refl R.handshake1)
  p11 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.negotiate A.child₀ I.ps duplex))))) (wrap (base F.s1)) ≡ just (wrap (base F.s2))
  p11 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.negotiate A.child₀ I.ps duplex)))) (K.combined (base F.s1) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.negotiate A.child₀ I.ps duplex))) (base F.s1) k0 refl R.handshake2)
  p12 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0)))))) (wrap (base F.s2)) ≡ just (wrap (base F.s3))
  p12 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0))))) (K.combined (base F.s2) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0)))) (base F.s2) k0 refl R.handshake3)
  p13 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.publishSuccess A.child₀))))) (wrap (base F.s3)) ≡ just (wrap (base F.s4))
  p13 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.publishSuccess A.child₀)))) (K.combined (base F.s3) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.publishSuccess A.child₀))) (base F.s3) k0 refl R.handshake4)
  p14 : V.advance (V.dispatch (K.serverStep (E.run (consume Handshake.readResult)))) (wrap (base F.s4)) ≡ just (wrap (base F.s5))
  p14 = Facts.lift-dispatch (K.serverStep (E.run (consume Handshake.readResult))) (K.combined (base F.s4) k0) V.empty refl
    (BFacts.lift-server-step (E.run (consume Handshake.readResult)) (base F.s4) k0 refl R.handshake5)
  p15 : V.advance (V.dispatch (K.serverStep (E.run (consume Handshake.commitResult)))) (wrap (base F.s5)) ≡ just (wrap (base F.s6))
  p15 = Facts.lift-dispatch (K.serverStep (E.run (consume Handshake.commitResult))) (K.combined (base F.s5) k0) V.empty refl
    (BFacts.lift-server-step (E.run (consume Handshake.commitResult)) (base F.s5) k0 refl R.handshake6)
  p16 : V.advance (V.dispatch (K.serverStep (E.run (consume Handshake.readResultCounters)))) (wrap (base F.s6)) ≡ just (wrap (base F.s7))
  p16 = Facts.lift-dispatch (K.serverStep (E.run (consume Handshake.readResultCounters))) (K.combined (base F.s6) k0) V.empty refl
    (BFacts.lift-server-step (E.run (consume Handshake.readResultCounters)) (base F.s6) k0 refl R.handshake7)
  p17 : V.advance (V.dispatch (K.serverStep (E.run (consume Handshake.enqueueInbound)))) (wrap (base F.s7)) ≡ just (wrap (base F.s8))
  p17 = Facts.lift-dispatch (K.serverStep (E.run (consume Handshake.enqueueInbound))) (K.combined (base F.s7) k0) V.empty refl
    (BFacts.lift-server-step (E.run (consume Handshake.enqueueInbound)) (base F.s7) k0 refl R.handshake8)
  p18 : V.advance (V.dispatch (K.serverStep (E.run (consume Handshake.returnResult)))) (wrap (base F.s8)) ≡ just (wrap (base F.s9))
  p18 = Facts.lift-dispatch (K.serverStep (E.run (consume Handshake.returnResult))) (K.combined (base F.s8) k0) V.empty refl
    (BFacts.lift-server-step (E.run (consume Handshake.returnResult)) (base F.s8) k0 refl R.handshake9)
  p19 : V.advance (V.dispatch (K.serverStep (E.run (S.workerReturned A.w₀)))) (wrap (base F.s9)) ≡ just (wrap (base F.s10))
  p19 = Facts.lift-dispatch (K.serverStep (E.run (S.workerReturned A.w₀))) (K.combined (base F.s9) k0) V.empty refl
    (BFacts.lift-server-step (E.run (S.workerReturned A.w₀)) (base F.s9) k0 refl R.handshake10)
  p20 : V.advance (V.dispatch (K.serverStep (E.run (S.workerResult A.w₀)))) (wrap (base F.s10)) ≡ just (wrap (X.admitted))
  p20 = Facts.lift-dispatch (K.serverStep (E.run (S.workerResult A.w₀))) (K.combined (base F.s10) k0) V.empty refl
    (BFacts.lift-server-step (E.run (S.workerResult A.w₀)) (base F.s10) k0 refl R.handshake11)
  p21 : V.advance (V.dispatch (K.serverStep (ig (IG.captureTime 10)))) (wrap (X.admitted)) ≡ just (wrap (X.g1))
  p21 = Facts.lift-dispatch (K.serverStep (ig (IG.captureTime 10))) (K.combined (X.admitted) k0) V.empty refl
    (BFacts.lift-server-step (ig (IG.captureTime 10)) (X.admitted) k0 refl R.register1)
  p22 : V.advance (V.dispatch (K.serverStep (ig IG.registerInactivity))) (wrap (X.g1)) ≡ just (wrap (X.g2))
  p22 = Facts.lift-dispatch (K.serverStep (ig IG.registerInactivity)) (K.combined (X.g1) k0) V.empty refl
    (BFacts.lift-server-step (ig IG.registerInactivity) (X.g1) k0 refl R.register2)
  p23 : V.advance (V.dispatch (K.serverStep (ig IG.selectBatch))) (wrap (X.g2)) ≡ just (wrap (X.g3))
  p23 = Facts.lift-dispatch (K.serverStep (ig IG.selectBatch)) (K.combined (X.g2) k0) V.empty refl
    (BFacts.lift-server-step (ig IG.selectBatch) (X.g2) k0 refl R.register3)
  p24 : V.advance (V.dispatch (K.serverStep (ig IG.readEvent))) (wrap (X.g3)) ≡ just (wrap (X.g4))
  p24 = Facts.lift-dispatch (K.serverStep (ig IG.readEvent)) (K.combined (X.g3) k0) V.empty refl
    (BFacts.lift-server-step (ig IG.readEvent) (X.g3) k0 refl R.register4)
  p25 : V.advance (V.dispatch (K.serverStep (ig IG.registerIdleTimer))) (wrap (X.g4)) ≡ just (wrap (X.g5))
  p25 = Facts.lift-dispatch (K.serverStep (ig IG.registerIdleTimer)) (K.combined (X.g4) k0) V.empty refl
    (BFacts.lift-server-step (ig IG.registerIdleTimer) (X.g4) k0 refl R.register5)
  p26 : V.advance (V.dispatch (K.serverStep (ig IG.runResponders))) (wrap (X.g5)) ≡ just (wrap (X.g6))
  p26 = Facts.lift-dispatch (K.serverStep (ig IG.runResponders)) (K.combined (X.g5) k0) V.empty refl
    (BFacts.lift-server-step (ig IG.runResponders) (X.g5) k0 refl R.register6)
  p27 : V.advance (V.dispatch (K.serverStep (ig IG.finishBatch))) (wrap (X.g6)) ≡ just (wrap (X.g7))
  p27 = Facts.lift-dispatch (K.serverStep (ig IG.finishBatch)) (K.combined (X.g6) k0) V.empty refl
    (BFacts.lift-server-step (ig IG.finishBatch) (X.g6) k0 refl R.register7)
  p28 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.allocateBuffer))))) (wrap (Y.render Y.root)) ≡ just (wrap (Y.render Y.s1))
  p28 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.allocateBuffer)))) (K.combined (Y.render Y.root) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ T.allocateBuffer))) (Y.render Y.root) k0 refl Prefix.startup1)
  p29 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.createBearer))))) (wrap (Y.render Y.s1)) ≡ just (wrap (Y.render Y.s2))
  p29 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.createBearer)))) (K.combined (Y.render Y.s1) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ T.createBearer))) (Y.render Y.s1) k0 refl Prefix.startup2)
  p30 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.enterRun))))) (wrap (Y.render Y.s2)) ≡ just (wrap (Y.render Y.s3))
  p30 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.enterRun)))) (K.combined (Y.render Y.s2) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ T.enterRun))) (Y.render Y.s2) k0 refl Prefix.startup3)
  p31 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.traceStarting))))) (wrap (Y.render Y.s3)) ≡ just (wrap (Y.render Y.s4))
  p31 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.traceStarting)))) (K.combined (Y.render Y.s3) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ T.traceStarting))) (Y.render Y.s3) k0 refl Prefix.startup4)
  p32 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.allocateEgress))))) (wrap (Y.render Y.s4)) ≡ just (wrap (Y.render Y.s5))
  p32 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.allocateEgress)))) (K.combined (Y.render Y.s4) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ T.allocateEgress))) (Y.render Y.s4) k0 refl Prefix.startup5)
  p33 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.openPool))))) (wrap (Y.render Y.s5)) ≡ just (wrap (Y.render Y.s6))
  p33 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.openPool)))) (K.combined (Y.render Y.s5) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ T.openPool))) (Y.render Y.s5) k0 refl Prefix.startup6)
  p34 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ (T.forkMuxer (ident 0))))))) (wrap (Y.render Y.s6)) ≡ just (wrap (Y.render Y.s7))
  p34 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ (T.forkMuxer (ident 0)))))) (K.combined (Y.render Y.s6) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ (T.forkMuxer (ident 0))))) (Y.render Y.s6) k0 refl Prefix.startup7)
  p35 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.registerMuxer))))) (wrap (Y.render Y.s7)) ≡ just (wrap (Y.render Y.s8))
  p35 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.registerMuxer)))) (K.combined (Y.render Y.s7) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ T.registerMuxer))) (Y.render Y.s7) k0 refl Prefix.startup8)
  p36 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ (T.forkDemuxer (ident 1))))))) (wrap (Y.render Y.s8)) ≡ just (wrap (Y.render Y.s9))
  p36 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ (T.forkDemuxer (ident 1)))))) (K.combined (Y.render Y.s8) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ (T.forkDemuxer (ident 1))))) (Y.render Y.s8) k0 refl Prefix.startup9)
  p37 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.registerDemuxer))))) (wrap (Y.render Y.s9)) ≡ just (wrap (Y.render Y.s10))
  p37 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.registerDemuxer)))) (K.combined (Y.render Y.s9) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ T.registerDemuxer))) (Y.render Y.s9) k0 refl Prefix.startup10)
  p38 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.traceMature))))) (wrap (Y.render Y.s10)) ≡ just (wrap (Y.render Y.s11))
  p38 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.traceMature)))) (K.combined (Y.render Y.s10) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ T.traceMature))) (Y.render Y.s10) k0 refl Prefix.startup11)
  p39 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.enterMonitor))))) (wrap (Y.render Y.s11)) ≡ just (wrap (Y.render Y.s12))
  p39 = Facts.lift-dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.enterMonitor)))) (K.combined (Y.render Y.s11) k0) V.empty refl
    (BFacts.lift-server-step (E.run (mux (U.startupStep A.child₀ T.enterMonitor))) (Y.render Y.s11) k0 refl Prefix.startup12)
  p40 : V.advance (ps L.a1) (wrap (Y.render Y.s12)) ≡ just (beforeAcquire k1)
  p40 = refl
  p41 : V.advance (ps (Sub.sampleTime 10)) (beforeAcquire k1) ≡ just (beforeAcquire k2)
  p41 = refl
  p42 : V.advance (ps L.a3) (beforeAcquire k2) ≡ just (beforeAcquire k3)
  p42 = refl
  p43 : V.advance (ps L.a4) (beforeAcquire k3) ≡ just (beforeAcquire k4)
  p43 = refl
  p44 : V.advance (ps (Sub.applyAt 10)) (beforeAcquire k4) ≡ just (beforeAcquire k5)
  p44 = refl
  p45 : V.advance (ps L.a6) (beforeAcquire k5) ≡ just (beforeAcquire k6)
  p45 = refl
  p46 : V.advance (ps L.a7) (beforeAcquire k6) ≡ just (beforeAcquire k7)
  p46 = refl
  p47 : V.advance (ps L.a8) (beforeAcquire k7) ≡ just (beforeAcquire k8)
  p47 = refl
  p48 : V.advance (ps L.a9) (beforeAcquire k8) ≡ just (beforeAcquire k9)
  p48 = refl
  p49 : V.advance (ps L.a10) (beforeAcquire k9) ≡ just (render model k10 (callFrame Acquire.selecting) [] 0 V.empty)
  p49 = refl
  p50 : V.advance (common (Acquire.select (just (ident 0)))) (render model k10 (callFrame Acquire.selecting) [] 0 V.empty) ≡ just (render reused k10 (callFrame (Acquire.count (Acquire.count (Acquire.complete result)))) [] 1 V.empty)
  p50 = refl
  p51 : V.advance (common (Acquire.readCounters)) (render reused k10 (callFrame (Acquire.count (Acquire.count (Acquire.complete result)))) [] 1 V.empty) ≡ just (render reused k10 (callFrame (Acquire.count (Acquire.complete result))) [] 1 V.empty)
  p51 = refl
  p52 : V.advance (common (Acquire.readCounters)) (render reused k10 (callFrame (Acquire.count (Acquire.complete result))) [] 1 V.empty) ≡ just (render reused k10 (callFrame (Acquire.complete result)) [] 1 V.empty)
  p52 = refl
  p53 : V.advance (common (Acquire.returnResult)) (render reused k10 (callFrame (Acquire.complete result)) [] 1 V.empty) ≡ just (at reused kAcquired V.empty)
  p53 = refl
  p54 : V.advance (ps L.a34) (at reused kAcquired V.empty) ≡ just (at reused k34 V.empty)
  p54 = refl
  p55 : V.advance (ps L.a35) (at reused k34 V.empty) ≡ just (at reused k35 V.empty)
  p55 = refl
  p56 : V.advance (ps L.a36) (at reused k35 V.empty) ≡ just (at reused k36 V.empty)
  p56 = refl
  p57 : V.advance (ps L.a37) (at reused k36 V.empty) ≡ just (at reused k37 V.empty)
  p57 = refl
  p58 : V.advance (ps L.a38) (at reused k37 V.empty) ≡ just (at reused k38 V.empty)
  p58 = refl
  p59 : V.advance (ps L.a39) (at reused k38 V.empty) ≡ just (at reused k39 V.empty)
  p59 = refl
  p60 : V.advance (peerStep (PS.forkMonitor (ident 0) (ident 50))) (at reused k39 V.empty) ≡ just (at reused km1 V.empty)
  p60 = refl
  p61 : V.advance (peerStep (PS.registerMonitor (ident 50))) (at reused km1 V.empty) ≡ just (at reused km2 V.empty)
  p61 = refl
  p62 : V.advance (peerStep (PS.returnEstablishment (ident 0))) (at reused km2 V.empty) ≡ just (at reused km3 V.empty)
  p62 = refl
  p63 : V.advance (peerStep (PS.finishEstablishment (ident 0))) (at reused km3 V.empty) ≡ just (at reused km4 V.empty)
  p63 = refl
  p64 : V.advance (ps L.a41) (at reused km4 V.empty) ≡ just (at reused k41 V.empty)
  p64 = refl
  p65 : V.advance (ps L.a42) (at reused k41 V.empty) ≡ just (at reused k42 V.empty)
  p65 = refl
  p66 : V.advance (peerStep (PS.run (GP.publishAsyncResult (ident 0)))) (at reused k42 V.empty) ≡ just (at reused (ctx L.c42 g0done) V.empty)
  p66 = refl
  p67 : V.advance (ps L.a43) (at reused (ctx L.c42 g0done) V.empty) ≡ just (at reused k43 V.empty)
  p67 = refl
  p68 : V.advance (ps L.a44) (at reused k43 V.empty) ≡ just (at reused k44 V.empty)
  p68 = refl
  p69 : V.advance (ps (Sub.sampleTime 11)) (at reused k44 V.empty) ≡ just (at reused k45 V.empty)
  p69 = refl
  p70 : V.advance (ps L.a46) (at reused k45 V.empty) ≡ just (at reused k46 V.empty)
  p70 = refl
  p71 : V.advance (ps L.a47) (at reused k46 V.empty) ≡ just (at reused k47 V.empty)
  p71 = refl
  p72 : V.advance (ps (Sub.applyAt 11)) (at reused k47 V.empty) ≡ just (at reused k48 V.empty)
  p72 = refl
  p73 : V.advance (ps L.a49) (at reused k48 V.empty) ≡ just (at reused k49 V.empty)
  p73 = refl
  p74 : V.advance (ps L.a50) (at reused k49 V.empty) ≡ just (at reused k50 V.empty)
  p74 = refl
  p75 : V.advance (ps L.a51) (at reused k50 V.empty) ≡ just (at reused k51 V.empty)
  p75 = refl
  p76 : V.advance (ps L.a52) (at reused k51 V.empty) ≡ just (at reused k52 V.empty)
  p76 = refl
  p77 : V.advance (ps (Sub.sampleTime 12)) (at reused k52 V.empty) ≡ just (at reused k53 V.empty)
  p77 = refl
  p78 : V.advance (ps L.a54) (at reused k53 V.empty) ≡ just (at reused k54 V.empty)
  p78 = refl
  p79 : V.advance (ps L.a55) (at reused k54 V.empty) ≡ just (at reused k55 V.empty)
  p79 = refl
  p80 : V.advance (ps (Sub.applyAt 12)) (at reused k55 V.empty) ≡ just (at reused k56 V.empty)
  p80 = refl
  p81 : V.advance (ps L.a57) (at reused k56 V.empty) ≡ just (at reused k57 V.empty)
  p81 = refl
  p82 : V.advance (ps L.a58) (at reused k57 V.empty) ≡ just (at reused k58 V.empty)
  p82 = refl
  p83 : V.advance (ps L.a59) (at reused k58 V.empty) ≡ just (at reused k59 V.empty)
  p83 = refl
  p84 : V.advance (ps L.a60) (at reused k59 V.empty) ≡ just (at reused k60 V.empty)
  p84 = refl
  p85 : V.advance (ps L.a61) (at reused k60 V.empty) ≡ just (at reused k61 V.empty)
  p85 = refl
  prefixActions : List V.Event
  prefixActions = (V.dispatch (K.serverStep (E.run (S.acceptedFork A.w₀ F.r₀)))) ∷ (V.dispatch (K.serverStep (E.run (S.acceptedFork A.w₁ F.r₁)))) ∷ (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.take)))) ∷ (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.countLimit)))) ∷ (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.allocatePromise)))) ∷ (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.chooseEntry)))) ∷ (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.fork)))) ∷ (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.putMapBack)))) ∷ (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.readCounters)))) ∷ (V.dispatch (K.serverStep (E.run (handler (H.enterHandshake A.child₀))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.negotiate A.child₀ I.ps duplex))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0)))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.publishSuccess A.child₀))))) ∷ (V.dispatch (K.serverStep (E.run (consume Handshake.readResult)))) ∷ (V.dispatch (K.serverStep (E.run (consume Handshake.commitResult)))) ∷ (V.dispatch (K.serverStep (E.run (consume Handshake.readResultCounters)))) ∷ (V.dispatch (K.serverStep (E.run (consume Handshake.enqueueInbound)))) ∷ (V.dispatch (K.serverStep (E.run (consume Handshake.returnResult)))) ∷ (V.dispatch (K.serverStep (E.run (S.workerReturned A.w₀)))) ∷ (V.dispatch (K.serverStep (E.run (S.workerResult A.w₀)))) ∷ (V.dispatch (K.serverStep (ig (IG.captureTime 10)))) ∷ (V.dispatch (K.serverStep (ig IG.registerInactivity))) ∷ (V.dispatch (K.serverStep (ig IG.selectBatch))) ∷ (V.dispatch (K.serverStep (ig IG.readEvent))) ∷ (V.dispatch (K.serverStep (ig IG.registerIdleTimer))) ∷ (V.dispatch (K.serverStep (ig IG.runResponders))) ∷ (V.dispatch (K.serverStep (ig IG.finishBatch))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.allocateBuffer))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.createBearer))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.enterRun))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.traceStarting))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.allocateEgress))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.openPool))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ (T.forkMuxer (ident 0))))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.registerMuxer))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ (T.forkDemuxer (ident 1))))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.registerDemuxer))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.traceMature))))) ∷ (V.dispatch (K.serverStep (E.run (mux (U.startupStep A.child₀ T.enterMonitor))))) ∷ (ps L.a1) ∷ (ps (Sub.sampleTime 10)) ∷ (ps L.a3) ∷ (ps L.a4) ∷ (ps (Sub.applyAt 10)) ∷ (ps L.a6) ∷ (ps L.a7) ∷ (ps L.a8) ∷ (ps L.a9) ∷ (ps L.a10) ∷ (common (Acquire.select (just (ident 0)))) ∷ (common (Acquire.readCounters)) ∷ (common (Acquire.readCounters)) ∷ (common (Acquire.returnResult)) ∷ (ps L.a34) ∷ (ps L.a35) ∷ (ps L.a36) ∷ (ps L.a37) ∷ (ps L.a38) ∷ (ps L.a39) ∷ (peerStep (PS.forkMonitor (ident 0) (ident 50))) ∷ (peerStep (PS.registerMonitor (ident 50))) ∷ (peerStep (PS.returnEstablishment (ident 0))) ∷ (peerStep (PS.finishEstablishment (ident 0))) ∷ (ps L.a41) ∷ (ps L.a42) ∷ (peerStep (PS.run (GP.publishAsyncResult (ident 0)))) ∷ (ps L.a43) ∷ (ps L.a44) ∷ (ps (Sub.sampleTime 11)) ∷ (ps L.a46) ∷ (ps L.a47) ∷ (ps (Sub.applyAt 11)) ∷ (ps L.a49) ∷ (ps L.a50) ∷ (ps L.a51) ∷ (ps L.a52) ∷ (ps (Sub.sampleTime 12)) ∷ (ps L.a54) ∷ (ps L.a55) ∷ (ps (Sub.applyAt 12)) ∷ (ps L.a57) ∷ (ps L.a58) ∷ (ps L.a59) ∷ (ps L.a60) ∷ (ps L.a61) ∷ []
  abstract
    initialized-to-start : V.Runs initial prefixActions (at reused k61 V.empty)
    initialized-to-start = V.more p1 (V.more p2 (V.more p3 (V.more p4 (V.more p5 (V.more p6 (V.more p7 (V.more p8 (V.more p9 (V.more p10 (V.more p11 (V.more p12 (V.more p13 (V.more p14 (V.more p15 (V.more p16 (V.more p17 (V.more p18 (V.more p19 (V.more p20 (V.more p21 (V.more p22 (V.more p23 (V.more p24 (V.more p25 (V.more p26 (V.more p27 (V.more p28 (V.more p29 (V.more p30 (V.more p31 (V.more p32 (V.more p33 (V.more p34 (V.more p35 (V.more p36 (V.more p37 (V.more p38 (V.more p39 (V.more p40 (V.more p41 (V.more p42 (V.more p43 (V.more p44 (V.more p45 (V.more p46 (V.more p47 (V.more p48 (V.more p49 (V.more p50 (V.more p51 (V.more p52 (V.more p53 (V.more p54 (V.more p55 (V.more p56 (V.more p57 (V.more p58 (V.more p59 (V.more p60 (V.more p61 (V.more p62 (V.more p63 (V.more p64 (V.more p65 (V.more p66 (V.more p67 (V.more p68 (V.more p69 (V.more p70 (V.more p71 (V.more p72 (V.more p73 (V.more p74 (V.more p75 (V.more p76 (V.more p77 (V.more p78 (V.more p79 (V.more p80 (V.more p81 (V.more p82 (V.more p83 (V.more p84 (V.more p85 (V.stop)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  start-supply : Inv.ProtocolValid (at reused k61 V.empty)
  start-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-to-start

  -- The successful runMiniProtocol call allocates its cell and queues a start;
  -- neither this cell nor the PSA running marker is a physical job birth.
  rid : RunId
  rid = ident 20
  jid : JobId
  jid = ident 20
  proto : Protocol
  proto = IG.protocol 1 hot IG.onDemand
  requested : V.Call
  requested = V.call (ident 0) (ident 0) A.child₀ (ident 0) proto nothing nothing
  queuedFront zeroFront selectedFront tracingFront readyFront bornFront cleanFront freeFront : V.Front
  queuedFront = V.frontend ((rid , requested) ∷ []) ((A.child₀ , V.command rid 1 ∷ []) ∷ []) []
  zeroFront = record queuedFront { commands = (A.child₀ , V.command rid 0 ∷ []) ∷ [] }
  selectedFront = V.frontend ((rid , requested) ∷ []) ((A.child₀ , []) ∷ []) ((A.child₀ , V.selectedC rid) ∷ [])
  tracingFront = V.setCursor A.child₀ (V.tracingC rid) selectedFront
  readyFront = V.setCursor A.child₀ (V.forkReadyC rid) selectedFront
  bornFront = record readyFront
    { calls = (rid , record requested { thread = just jid }) ∷ []
    ; cursors = (A.child₀ , V.registeringC rid jid) ∷ [] }
  cleanFront = record bornFront { calls = (rid , record requested { thread = just jid; value = just clean }) ∷ [] }
  freeFront = V.setCursor A.child₀ V.idleC cleanFront
  legacy : Y.Model
  legacy = record reused { governor = IG.setMux (ident 0) Y.m1 (Y.governor reused) }
  payload : Types.TypedResult
  payload = Types.protocolCompletion Mux.initiatorJob 1 rid clean
  bornPool registeredPool returnedPool publishedPool deregisteredPool availablePool consumedPool : Pool.State
  bornPool = record Y.engines { handles = put jid Pool.bodyRunning (Pool.handles Y.engines); parentFork = just jid }
  registeredPool = record bornPool { registered = jid ∷ Pool.registered Y.engines; parentFork = nothing }
  returnedPool = record registeredPool { handles = put jid (Pool.bodyReturned payload) (Pool.handles registeredPool) }
  publishedPool = record registeredPool { handles = put jid (Pool.deregisterPending Pool.normalExit) (Pool.handles registeredPool); completions = payload ∷ [] }
  deregisteredPool = record publishedPool { handles = put jid (Pool.deregistered Pool.normalExit) (Pool.handles publishedPool); registered = Pool.registered Y.engines }
  availablePool = record deregisteredPool { handles = put jid (Pool.resultAvailable Pool.normalExit) (Pool.handles deregisteredPool) }
  consumedPool = record availablePool { completions = [] }
  physicalJob : Types.BodyPhase → Types.ProtocolJob
  physicalJob phase = Types.protocolJob A.child₀ (ident 0) Mux.initiatorJob 1 rid phase
  withPhysical : Types.BodyPhase → Pool.State → Y.Model
  withPhysical phase pool = record legacy
    { startup = T.startupState (T.monitoring (ident 0) (ident 1)) pool
    ; jobs = (jid , physicalJob phase) ∷ [] }
  born waiting localClean registered : Y.Model
  born = withPhysical Types.executing bornPool
  waiting = withPhysical Types.waitingEgress bornPool
  localClean = withPhysical (Types.resultCaptured clean) bornPool
  registered = withPhysical (Types.resultCaptured clean) registeredPool
  withPeer : Peer.Peer → C.Context → C.Context
  withPeer p k = record k { subsystem = record (C.subsystem k) { peers = (ident 0 , p) ∷ [] } }
  cleanUnpublished cleanPublished cleanPromoted : Peer.Peer
  cleanUnpublished = record L.p14 { runs = Peer.protocolRun proto (Peer.returned clean) Peer.notStarted ∷ [] }
  cleanPublished = record L.p15 { runs = Peer.protocolRun proto (Peer.returned clean) Peer.running ∷ [] }
  cleanPromoted = record (shiftPeer L.promotedPeer) { runs = Peer.protocolRun proto (Peer.returned clean) Peer.running ∷ [] }
  kc63 kc64 kc65 kc66 kc67 kActivationDone : C.Context
  kc63 = withPeer cleanUnpublished k63
  kc64 = withPeer cleanPublished (ctx L.c64 g60)
  g65 g66 g67 gBothDone : GP.Pool.State
  g65 = record g60 { handles = put (ident 1) (GP.Pool.bodyReturned body1) (GP.Pool.handles g60) }
  g66 = record g65 { handles = put (ident 1) (GP.Pool.deregisterPending GP.Pool.normalExit) (GP.Pool.handles g65); completions = body0 ∷ body1 ∷ [] }
  g67 = record g66 { handles = put (ident 1) (GP.Pool.deregistered GP.Pool.normalExit) (GP.Pool.handles g66); registered = [] }
  gBothDone = record g67 { handles = put (ident 1) (GP.Pool.resultAvailable GP.Pool.normalExit) (GP.Pool.handles g67) }
  kc65 = withPeer cleanPromoted (ctx L.c65 g65)
  kc66 = withPeer cleanPromoted (ctx L.c66 g66)
  kc67 = withPeer cleanPromoted (ctx L.c67 g67)
  kActivationDone = withPeer cleanPromoted (ctx L.c67 gBothDone)
  popped handled traceBegun traceReturned deltaBegun monitorDone : Y.Model
  popped = record (withPhysical (Types.resultCaptured clean) consumedPool)
    { monitors = (A.child₀ , N.M.selected payload) ∷ []
    ; tickets = (A.child₀ , N.D.ticket payload N.D.captured) ∷ [] }
  handled = record popped { monitors = (A.child₀ , N.M.initiatorTracing clean) ∷ [] }
  traceBegun = record handled { tickets = (A.child₀ , N.D.ticket payload N.D.muxInvoked) ∷ [] }
  traceReturned = record handled { tickets = (A.child₀ , N.D.ticket payload N.D.muxReturned) ∷ [] }
  deltaBegun = record handled { tickets = (A.child₀ , N.D.ticket payload N.D.invoked) ∷ [] }
  monitorDone = record handled
    { monitors = (A.child₀ , N.M.waiting) ∷ []
    ; tickets = (A.child₀ , N.D.ticket payload N.D.returned) ∷ [] }
  monitorStep : N.M.Action → V.Event
  monitorStep a = V.dispatch (K.serverStep (Prefix.monitor a))
  deltaStep : N.D.Action → V.Event
  deltaStep a = V.dispatch (K.serverStep (Prefix.delta a))
  run1 : V.advance (V.startNext (ident 1) rid) (at reused k61 V.empty) ≡ just (at reused k62 queuedFront)
  run1 = refl
  run2 : V.advance (ps L.a63) (at reused k62 queuedFront) ≡ just (at reused k63 queuedFront)
  run2 = refl
  run3 : V.advance (physicalStep (P.control A.child₀ P.selectCommand)) (at reused k63 queuedFront) ≡ just (at legacy k63 zeroFront)
  run3 = refl
  run4 : V.advance (V.selectStart A.child₀) (at legacy k63 zeroFront) ≡ just (at legacy k63 selectedFront)
  run4 = refl
  run5 : V.advance (V.invokeStartTrace A.child₀) (at legacy k63 selectedFront) ≡ just (at legacy k63 tracingFront)
  run5 = refl
  run6 : V.advance (V.returnStartTrace A.child₀) (at legacy k63 tracingFront) ≡ just (at legacy k63 readyFront)
  run6 = refl
  run7 : V.advance (V.forkStart A.child₀ jid) (at legacy k63 readyFront) ≡ just (at born k63 bornFront)
  run7 = refl
  run8 : V.advance (physicalStep (P.protocolReturned jid)) (at born k63 bornFront) ≡ just (at waiting k63 bornFront)
  run8 = refl
  run9 : V.advance (V.commitClean jid) (at waiting k63 bornFront) ≡ just (at localClean kc63 cleanFront)
  run9 = refl
  run10 : V.advance (V.registerStart jid) (at localClean kc63 cleanFront) ≡ just (at registered kc63 freeFront)
  run10 = refl
  run11 : V.advance (ps L.a64) (at registered kc63 freeFront) ≡ just (at registered kc64 freeFront)
  run11 = refl
  run12 : V.advance (ps (Sub.jobStep (ident 1) (J.finishHotAt 12))) (at registered kc64 freeFront) ≡ just (at registered kc65 freeFront)
  run12 = refl
  run13 : V.advance (ps L.a66) (at registered kc65 freeFront) ≡ just (at registered kc66 freeFront)
  run13 = refl
  run14 : V.advance (ps L.a67) (at registered kc66 freeFront) ≡ just (at registered kc67 freeFront)
  run14 = refl
  run15 : V.advance (peerStep (PS.run (GP.publishAsyncResult (ident 1)))) (at registered kc67 freeFront) ≡ just (at registered kActivationDone freeFront)
  run15 = refl
  run16 : V.advance (physicalStep (P.returnProtocol jid)) (at registered kActivationDone freeFront) ≡ just (at (withPhysical (Types.resultCaptured clean) returnedPool) kActivationDone freeFront)
  run16 = refl
  run17 : V.advance (physicalStep (P.publishProtocol jid)) (at (withPhysical (Types.resultCaptured clean) returnedPool) kActivationDone freeFront) ≡ just (at (withPhysical (Types.resultCaptured clean) publishedPool) kActivationDone freeFront)
  run17 = refl
  run18 : V.advance (physicalStep (P.deregisterProtocol jid)) (at (withPhysical (Types.resultCaptured clean) publishedPool) kActivationDone freeFront) ≡ just (at (withPhysical (Types.resultCaptured clean) deregisteredPool) kActivationDone freeFront)
  run18 = refl
  run19 : V.advance (physicalStep (P.asyncProtocolResult jid)) (at (withPhysical (Types.resultCaptured clean) deregisteredPool) kActivationDone freeFront) ≡ just (at (withPhysical (Types.resultCaptured clean) availablePool) kActivationDone freeFront)
  run19 = refl
  run20 : V.advance (monitorStep (N.M.consume A.child₀)) (at (withPhysical (Types.resultCaptured clean) availablePool) kActivationDone freeFront) ≡ just (at popped kActivationDone freeFront)
  run20 = refl
  run21 : V.advance (monitorStep (N.M.handleSelected A.child₀)) (at popped kActivationDone freeFront) ≡ just (at handled kActivationDone freeFront)
  run21 = refl
  run22 : V.advance (deltaStep (N.D.beginInitiatorTrace A.child₀)) (at handled kActivationDone freeFront) ≡ just (at traceBegun kActivationDone freeFront)
  run22 = refl
  run23 : V.advance (deltaStep (N.D.observeInitiatorReturn A.child₀)) (at traceBegun kActivationDone freeFront) ≡ just (at traceReturned kActivationDone freeFront)
  run23 = refl
  run24 : V.advance (deltaStep (N.D.beginDeltaQ A.child₀)) (at traceReturned kActivationDone freeFront) ≡ just (at deltaBegun kActivationDone freeFront)
  run24 = refl
  run25 : V.advance (deltaStep (N.D.observeReturn A.child₀)) (at deltaBegun kActivationDone freeFront) ≡ just (at monitorDone kActivationDone freeFront)
  run25 = refl
  protocolActions : List V.Event
  protocolActions = (V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ (V.invokeStartTrace A.child₀) ∷ (V.returnStartTrace A.child₀) ∷ (V.forkStart A.child₀ jid) ∷ (physicalStep (P.protocolReturned jid)) ∷ (V.commitClean jid) ∷ (V.registerStart jid) ∷ (ps L.a64) ∷ (ps (Sub.jobStep (ident 1) (J.finishHotAt 12))) ∷ (ps L.a66) ∷ (ps L.a67) ∷ (peerStep (PS.run (GP.publishAsyncResult (ident 1)))) ∷ (physicalStep (P.returnProtocol jid)) ∷ (physicalStep (P.publishProtocol jid)) ∷ (physicalStep (P.deregisterProtocol jid)) ∷ (physicalStep (P.asyncProtocolResult jid)) ∷ (monitorStep (N.M.consume A.child₀)) ∷ (monitorStep (N.M.handleSelected A.child₀)) ∷ (deltaStep (N.D.beginInitiatorTrace A.child₀)) ∷ (deltaStep (N.D.observeInitiatorReturn A.child₀)) ∷ (deltaStep (N.D.beginDeltaQ A.child₀)) ∷ (deltaStep (N.D.observeReturn A.child₀)) ∷ []
  abstract
    protocol-path : V.Runs (at reused k61 V.empty) protocolActions (at monitorDone kActivationDone freeFront)
    protocol-path = V.more run1 (V.more run2 (V.more run3 (V.more run4 (V.more run5 (V.more run6 (V.more run7 (V.more run8 (V.more run9 (V.more run10 (V.more run11 (V.more run12 (V.more run13 (V.more run14 (V.more run15 (V.more run16 (V.more run17 (V.more run18 (V.more run19 (V.more run20 (V.more run21 (V.more run22 (V.more run23 (V.more run24 (V.more run25 (V.stop)))))))))))))))))))))))))
    selected-path : V.Runs (at reused k61 V.empty) ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ []) (at legacy k63 selectedFront)
    selected-path = V.more run1 (V.more run2 (V.more run3 (V.more run4 (V.stop))))
    before-select-path : V.Runs (at reused k61 V.empty) ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ []) (at legacy k63 zeroFront)
    before-select-path = V.more run1 (V.more run2 (V.more run3 (V.stop)))
    waiting-path : V.Runs (at reused k61 V.empty) ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ (V.invokeStartTrace A.child₀) ∷ (V.returnStartTrace A.child₀) ∷ (V.forkStart A.child₀ jid) ∷ (physicalStep (P.protocolReturned jid)) ∷ []) (at waiting k63 bornFront)
    waiting-path = V.more run1 (V.more run2 (V.more run3 (V.more run4 (V.more run5 (V.more run6 (V.more run7 (V.more run8 (V.stop))))))))
    clean-path : V.Runs (at reused k61 V.empty) ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ (V.invokeStartTrace A.child₀) ∷ (V.returnStartTrace A.child₀) ∷ (V.forkStart A.child₀ jid) ∷ (physicalStep (P.protocolReturned jid)) ∷ (V.commitClean jid) ∷ []) (at localClean kc63 cleanFront)
    clean-path = V.more run1 (V.more run2 (V.more run3 (V.more run4 (V.more run5 (V.more run6 (V.more run7 (V.more run8 (V.more run9 (V.stop)))))))))
  allProtocolActions : List V.Event
  allProtocolActions = prefixActions ++ protocolActions
  abstract
    initialized-protocol : V.Runs initial allProtocolActions (at monitorDone kActivationDone freeFront)
    initialized-protocol = Facts.append-protocols initialized-to-start protocol-path
  protocol-supply : Inv.ProtocolValid (at monitorDone kActivationDone freeFront)
  protocol-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-protocol
  actual-birth : Facts.Birth A.child₀ jid (at legacy k63 readyFront) (at born k63 bornFront)
  actual-birth = Facts.fork-observation A.child₀ jid (at legacy k63 readyFront) run7
  no-birth-at-caller-return : lookup jid (P.jobs (V.physical (V.base (at reused k62 queuedFront)))) ≡ nothing
  no-birth-at-caller-return = refl
  no-result-before-physical-commit : V.observe rid (at waiting k63 bornFront) ≡ nothing
  no-result-before-physical-commit = refl
  local-result-before-publication : V.observe rid (at localClean kc63 cleanFront) ≡ just (V.localResult clean)
  local-result-before-publication = refl
  unpublished-is-not-visible : Peer.first hot (Peer.runs cleanUnpublished) ≡ nothing
  unpublished-is-not-visible = refl
  published-observes-current-result : Peer.first hot (Peer.runs cleanPublished) ≡ just clean
  published-observes-current-result = refl
  local-result-is-not-an-async-result : lookup jid (Pool.handles bornPool) ≡ just Pool.bodyRunning
  local-result-is-not-an-async-result = refl
  clean-slot-is-restartable : V.slotIdle A.child₀ 1 cleanFront ≡ true
  clean-slot-is-restartable = refl
  no-legacy-pending-result : Peer.pendingResults cleanPublished ≡ []
  no-legacy-pending-result = refl
  no-initiator-ig-counter-events : Shared.inboundInfo (Machine.world (O.core (V.sourceOf (at monitorDone kActivationDone freeFront)))) ≡ []
  no-initiator-ig-counter-events = refl
  no-premature-selection : V.advance (V.selectStart A.child₀) (at reused k62 queuedFront) ≡ nothing
  no-premature-selection = refl
  no-demand-overtaking : V.advance (physicalStep (P.control A.child₀ (P.demand 1))) (at legacy k63 zeroFront) ≡ nothing
  no-demand-overtaking = refl
  no-unobserved-fork : V.advance (physicalStep (P.forkInitiator A.child₀ jid rid 1)) (at legacy k63 readyFront) ≡ nothing
  no-unobserved-fork = refl
  no-trace-return-before-invocation : V.advance (V.returnStartTrace A.child₀) (at legacy k63 selectedFront) ≡ nothing
  no-trace-return-before-invocation = refl
  no-coupled-commit-shortcut : V.advance (physicalStep (P.commitClean jid)) (at waiting k63 bornFront) ≡ nothing
  no-coupled-commit-shortcut = refl

  -- Close the actual nonempty PSA monitor registry. Governor jobs have real
  -- terminal results; their already removed registry entries are not recaptured.
  atScope : Scope.State → C.Context → C.Context
  atScope q k = record k { scopes = q }
  gClosing gClosed : GP.Pool.State
  gClosing = record gBothDone { phase = GP.Pool.closing }
  gClosed = record gBothDone { phase = GP.Pool.closedPool }
  kClosing kClosed kScopes : C.Context
  kClosing = record kActivationDone { scopes = Fixtures.q8; governorPool = gClosing }
  kClosed = record kActivationDone { scopes = Fixtures.q8; governorPool = gClosed }
  kScopes = atScope Fixtures.q22 kClosed
  monClosing monRequested monDelivered monUnwound monRemoved monPublished monJoined monClosed : PS.Pool.State
  monClosing = record (C.monitorPool kScopes) { phase = PS.Pool.closing; snapshot = ident 50 ∷ []; remaining = ident 50 ∷ [] }
  monRequested = record monClosing { phase = PS.Pool.cancelPending (ident 50) }
  monDelivered = record monClosing { phase = PS.Pool.joinPending (ident 50); handles = (ident 50 , PS.Pool.bodyUnwinding) ∷ [] }
  monUnwound = record monDelivered { handles = (ident 50 , PS.Pool.deregisterPending PS.Pool.cancelledExit) ∷ [] }
  monRemoved = record monDelivered { handles = (ident 50 , PS.Pool.deregistered PS.Pool.cancelledExit) ∷ []; registered = [] }
  monPublished = record monRemoved { handles = (ident 50 , PS.Pool.resultAvailable PS.Pool.cancelledExit) ∷ [] }
  monJoined = record monPublished { phase = PS.Pool.closing; remaining = []; joined = ident 50 ∷ [] }
  monClosed = record monJoined { phase = PS.Pool.closedPool }
  cancelMonitor : Cancel.Frame
  cancelMonitor = Cancel.cancellation (ident 50) (errorId 172) Cancel.noCaller (Cancel.finished Cancel.abandoned)
  monitorThread : PS.MonitorPC → PS.Thread
  monitorThread pc = PS.thread (ident 0) (ident 50) (ident 0) PS.returned pc (just cancelMonitor) nothing
  kmClosing kmRequested kmDelivered kmUnwound kmRemoved kmPublished kmJoined kDone : C.Context
  kmClosing = record kScopes { monitorPool = monClosing }
  kmRequested = record kScopes { monitorPool = monRequested }
  kmDelivered = record kScopes { monitorPool = monDelivered; monitors = (ident 50 , monitorThread PS.cancelling) ∷ [] }
  kmUnwound = withPeer (record cleanPromoted { monitorStarted = false })
    (record kScopes { monitorPool = monUnwound; monitors = (ident 50 , monitorThread PS.exited) ∷ [] })
  kmRemoved = record kmUnwound { monitorPool = monRemoved }
  kmPublished = record kmUnwound { monitorPool = monPublished }
  kmJoined = record kmUnwound { monitorPool = monJoined }
  kDone = record kmUnwound { monitorPool = monClosed }
  closed : V.Runtime
  closed = at monitorDone kDone freeFront
  callbackReturned : V.Runtime
  callbackReturned = record closed { base = record (V.base closed)
    { server = record (K.server (V.base closed)) { base = record (E.base (K.server (V.base closed))) { stage = S.actionBodyExited } } } }
  scoped : Scope.Action → V.Event
  scoped a = peerStep (PS.scope a)
  close1 : V.advance (scoped (Scope.beginUnwind)) (at monitorDone kActivationDone freeFront) ≡ just (at monitorDone (atScope Fixtures.q1 kActivationDone) freeFront)
  close1 = refl
  close2 : V.advance (scoped (Scope.requestCancel)) (at monitorDone (atScope Fixtures.q1 kActivationDone) freeFront) ≡ just (at monitorDone (atScope Fixtures.q2 kActivationDone) freeFront)
  close2 = refl
  close3 : V.advance (scoped (Scope.deliverCancel)) (at monitorDone (atScope Fixtures.q2 kActivationDone) freeFront) ≡ just (at monitorDone (atScope Fixtures.q3 kActivationDone) freeFront)
  close3 = refl
  close4 : V.advance (scoped (Scope.bodyExit Scope.churn)) (at monitorDone (atScope Fixtures.q3 kActivationDone) freeFront) ≡ just (at monitorDone (atScope Fixtures.q4 kActivationDone) freeFront)
  close4 = refl
  close5 : V.advance (scoped (Scope.publishResult Scope.churn)) (at monitorDone (atScope Fixtures.q4 kActivationDone) freeFront) ≡ just (at monitorDone (atScope Fixtures.q5 kActivationDone) freeFront)
  close5 = refl
  close6 : V.advance (scoped (Scope.join)) (at monitorDone (atScope Fixtures.q5 kActivationDone) freeFront) ≡ just (at monitorDone (atScope Fixtures.q6 kActivationDone) freeFront)
  close6 = refl
  close7 : V.advance (scoped (Scope.requestCancel)) (at monitorDone (atScope Fixtures.q6 kActivationDone) freeFront) ≡ just (at monitorDone (atScope Fixtures.q7 kActivationDone) freeFront)
  close7 = refl
  close8 : V.advance (scoped (Scope.deliverCancel)) (at monitorDone (atScope Fixtures.q7 kActivationDone) freeFront) ≡ just (at monitorDone (atScope Fixtures.q8 kActivationDone) freeFront)
  close8 = refl
  close9 : V.advance (peerStep (PS.run (GP.beginClose []))) (at monitorDone (atScope Fixtures.q8 kActivationDone) freeFront) ≡ just (at monitorDone kClosing freeFront)
  close9 = refl
  close10 : V.advance (peerStep (PS.run GP.finishClose)) (at monitorDone kClosing freeFront) ≡ just (at monitorDone kClosed freeFront)
  close10 = refl
  close11 : V.advance (scoped (Scope.bodyExit Scope.governor)) (at monitorDone kClosed freeFront) ≡ just (at monitorDone (atScope Fixtures.q9 kClosed) freeFront)
  close11 = refl
  close12 : V.advance (scoped (Scope.publishResult Scope.governor)) (at monitorDone (atScope Fixtures.q9 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q10 kClosed) freeFront)
  close12 = refl
  close13 : V.advance (scoped (Scope.join)) (at monitorDone (atScope Fixtures.q10 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q11 kClosed) freeFront)
  close13 = refl
  close14 : V.advance (scoped (Scope.requestCancel)) (at monitorDone (atScope Fixtures.q11 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q12 kClosed) freeFront)
  close14 = refl
  close15 : V.advance (scoped (Scope.deliverCancel)) (at monitorDone (atScope Fixtures.q12 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q13 kClosed) freeFront)
  close15 = refl
  close16 : V.advance (scoped (Scope.bodyExit Scope.localRoot)) (at monitorDone (atScope Fixtures.q13 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q14 kClosed) freeFront)
  close16 = refl
  close17 : V.advance (scoped (Scope.publishResult Scope.localRoot)) (at monitorDone (atScope Fixtures.q14 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q15 kClosed) freeFront)
  close17 = refl
  close18 : V.advance (scoped (Scope.join)) (at monitorDone (atScope Fixtures.q15 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q16 kClosed) freeFront)
  close18 = refl
  close19 : V.advance (scoped (Scope.requestCancel)) (at monitorDone (atScope Fixtures.q16 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q17 kClosed) freeFront)
  close19 = refl
  close20 : V.advance (scoped (Scope.deliverCancel)) (at monitorDone (atScope Fixtures.q17 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q18 kClosed) freeFront)
  close20 = refl
  close21 : V.advance (scoped (Scope.bodyExit Scope.ledger)) (at monitorDone (atScope Fixtures.q18 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q19 kClosed) freeFront)
  close21 = refl
  close22 : V.advance (scoped (Scope.publishResult Scope.ledger)) (at monitorDone (atScope Fixtures.q19 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q20 kClosed) freeFront)
  close22 = refl
  close23 : V.advance (scoped (Scope.join)) (at monitorDone (atScope Fixtures.q20 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q21 kClosed) freeFront)
  close23 = refl
  close24 : V.advance (scoped (Scope.finishClose)) (at monitorDone (atScope Fixtures.q21 kClosed) freeFront) ≡ just (at monitorDone (atScope Fixtures.q22 kClosed) freeFront)
  close24 = refl
  close25 : V.advance (peerStep (PS.beginMonitorClose (ident 50 ∷ []))) (at monitorDone (atScope Fixtures.q22 kClosed) freeFront) ≡ just (at monitorDone kmClosing freeFront)
  close25 = refl
  close26 : V.advance (peerStep (PS.requestMonitorCancel)) (at monitorDone kmClosing freeFront) ≡ just (at monitorDone kmRequested freeFront)
  close26 = refl
  close27 : V.advance (peerStep (PS.deliverMonitorCancellation (errorId 172))) (at monitorDone kmRequested freeFront) ≡ just (at monitorDone kmDelivered freeFront)
  close27 = refl
  close28 : V.advance (peerStep (PS.monitorBodyUnwound (ident 50))) (at monitorDone kmDelivered freeFront) ≡ just (at monitorDone kmUnwound freeFront)
  close28 = refl
  close29 : V.advance (peerStep (PS.deregisterMonitor (ident 50))) (at monitorDone kmUnwound freeFront) ≡ just (at monitorDone kmRemoved freeFront)
  close29 = refl
  close30 : V.advance (peerStep (PS.publishMonitorResult (ident 50))) (at monitorDone kmRemoved freeFront) ≡ just (at monitorDone kmPublished freeFront)
  close30 = refl
  close31 : V.advance (peerStep (PS.joinMonitor)) (at monitorDone kmPublished freeFront) ≡ just (at monitorDone kmJoined freeFront)
  close31 = refl
  close32 : V.advance (peerStep (PS.finishMonitorClose)) (at monitorDone kmJoined freeFront) ≡ just (at monitorDone kDone freeFront)
  close32 = refl
  close33 : V.advance (V.dispatch (K.serverStep (E.run (S.scope S.returnAction)))) (at monitorDone kDone freeFront) ≡ just (callbackReturned)
  close33 = refl
  closeActions : List V.Event
  closeActions = (scoped (Scope.beginUnwind)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.churn)) ∷ (scoped (Scope.publishResult Scope.churn)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (peerStep (PS.run (GP.beginClose []))) ∷ (peerStep (PS.run GP.finishClose)) ∷ (scoped (Scope.bodyExit Scope.governor)) ∷ (scoped (Scope.publishResult Scope.governor)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.localRoot)) ∷ (scoped (Scope.publishResult Scope.localRoot)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.ledger)) ∷ (scoped (Scope.publishResult Scope.ledger)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.finishClose)) ∷ (peerStep (PS.beginMonitorClose (ident 50 ∷ []))) ∷ (peerStep (PS.requestMonitorCancel)) ∷ (peerStep (PS.deliverMonitorCancellation (errorId 172))) ∷ (peerStep (PS.monitorBodyUnwound (ident 50))) ∷ (peerStep (PS.deregisterMonitor (ident 50))) ∷ (peerStep (PS.publishMonitorResult (ident 50))) ∷ (peerStep (PS.joinMonitor)) ∷ (peerStep (PS.finishMonitorClose)) ∷ (V.dispatch (K.serverStep (E.run (S.scope S.returnAction)))) ∷ []
  beforeCallbackActions : List V.Event
  beforeCallbackActions = (scoped (Scope.beginUnwind)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.churn)) ∷ (scoped (Scope.publishResult Scope.churn)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (peerStep (PS.run (GP.beginClose []))) ∷ (peerStep (PS.run GP.finishClose)) ∷ (scoped (Scope.bodyExit Scope.governor)) ∷ (scoped (Scope.publishResult Scope.governor)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.localRoot)) ∷ (scoped (Scope.publishResult Scope.localRoot)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.ledger)) ∷ (scoped (Scope.publishResult Scope.ledger)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.finishClose)) ∷ (peerStep (PS.beginMonitorClose (ident 50 ∷ []))) ∷ (peerStep (PS.requestMonitorCancel)) ∷ (peerStep (PS.deliverMonitorCancellation (errorId 172))) ∷ (peerStep (PS.monitorBodyUnwound (ident 50))) ∷ (peerStep (PS.deregisterMonitor (ident 50))) ∷ (peerStep (PS.publishMonitorResult (ident 50))) ∷ (peerStep (PS.joinMonitor)) ∷ (peerStep (PS.finishMonitorClose)) ∷ []
  abstract
    close-path : V.Runs (at monitorDone kActivationDone freeFront) closeActions callbackReturned
    close-path = V.more close1 (V.more close2 (V.more close3 (V.more close4 (V.more close5 (V.more close6 (V.more close7 (V.more close8 (V.more close9 (V.more close10 (V.more close11 (V.more close12 (V.more close13 (V.more close14 (V.more close15 (V.more close16 (V.more close17 (V.more close18 (V.more close19 (V.more close20 (V.more close21 (V.more close22 (V.more close23 (V.more close24 (V.more close25 (V.more close26 (V.more close27 (V.more close28 (V.more close29 (V.more close30 (V.more close31 (V.more close32 (V.more close33 (V.stop)))))))))))))))))))))))))))))))))
    before-callback-path : V.Runs (at monitorDone kActivationDone freeFront) beforeCallbackActions closed
    before-callback-path = V.more close1 (V.more close2 (V.more close3 (V.more close4 (V.more close5 (V.more close6 (V.more close7 (V.more close8 (V.more close9 (V.more close10 (V.more close11 (V.more close12 (V.more close13 (V.more close14 (V.more close15 (V.more close16 (V.more close17 (V.more close18 (V.more close19 (V.more close20 (V.more close21 (V.more close22 (V.more close23 (V.more close24 (V.more close25 (V.more close26 (V.more close27 (V.more close28 (V.more close29 (V.more close30 (V.more close31 (V.more close32 (V.stop))))))))))))))))))))))))))))))))
    initialized : V.Runs initial (allProtocolActions ++ closeActions) callbackReturned
    initialized = Facts.append-protocols initialized-protocol close-path
    initialized-before-callback : V.Runs initial (allProtocolActions ++ beforeCallbackActions) closed
    initialized-before-callback = Facts.append-protocols initialized-protocol before-callback-path
  final-supply : Inv.ProtocolValid callbackReturned
  final-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized
  callback-certificates : BFacts.Certificates (V.base closed)
  callback-certificates = Facts.callback-from-protocols initializer initialized-before-callback close33
  open import Data.List.Relation.Unary.Any using (here)
  import ConnectionManagement.Properties.JobPoolCloseKernel as BackgroundClose
  private
    module BClose = BackgroundClose (Maybe ErrorId) false
  nonempty-monitor-certificate : BClose.Terminal (C.monitorPool kDone) (ident 50)
  nonempty-monitor-certificate = proj₁ (proj₂ callback-certificates) (ident 50) (here refl)
  captured-monitor : PS.Pool.snapshot (C.monitorPool kDone) ≡ ident 50 ∷ []
  captured-monitor = refl
  cancellation-retains-duration : Peer.promotedAt (record cleanPromoted { monitorStarted = false }) ≡ just 12
  cancellation-retains-duration = refl
  physical-handler-pool-still-open : Pool.phase (P.poolAt A.child₀ (V.physical (V.base callbackReturned))) ≡ Pool.openPool
  physical-handler-pool-still-open = refl
  raw-admissions-still-incomplete : S.allResults (S.workers (E.base (K.server (V.base callbackReturned)))) ≡ false
  raw-admissions-still-incomplete = refl

  -- An already selected command may finish its trace/fork while a later stop
  -- command and infrastructure result arrive. New selections retain FIFO priority.
  err : ErrorId
  err = errorId 177
  infraPayload : Types.TypedResult
  infraPayload = Types.infraMuxer err
  infraReturnedPool infraQueuedPool : Pool.State
  infraReturnedPool = record Y.engines { handles = put (ident 0) (Pool.bodyReturned infraPayload) (Pool.handles Y.engines) }
  infraQueuedPool = record Y.engines
    { handles = put (ident 0) (Pool.deregisterPending Pool.normalExit) (Pool.handles Y.engines); completions = infraPayload ∷ [] }
  withPool : Pool.State → Y.Model → Y.Model
  withPool pool m = record m { startup = record (Y.startup m) { pool = pool } }
  stoppedCommand : Y.Model
  stoppedCommand = record legacy { governor = IG.setMux (ident 0) (record Y.m1 { commands = Mux.shutdown ∷ [] }) (Y.governor legacy) }
  lateReturned lateQueued lateBorn : Y.Model
  lateReturned = withPool infraReturnedPool stoppedCommand
  lateQueued = withPool infraQueuedPool stoppedCommand
  lateBorn = record (withPool (record infraQueuedPool
    { handles = put jid Pool.bodyRunning (Pool.handles infraQueuedPool); parentFork = just jid }) stoppedCommand)
    { jobs = (jid , physicalJob Types.executing) ∷ [] }
  shutdownStep : N.G.Action → V.Event
  shutdownStep a = V.dispatch (K.serverStep (E.run (S.run (N.run (N.C.run (N.D.run
    (N.R.run (N.D.X.run (N.W.run a)))))))))

  late1 : V.advance (shutdownStep (N.G.requestShutdown A.child₀)) (at legacy k63 selectedFront) ≡ just (at stoppedCommand k63 selectedFront)
  late1 = refl
  late2 : V.advance (physicalStep (P.infrastructureReturn A.child₀ Types.muxer err)) (at stoppedCommand k63 selectedFront) ≡ just (at lateReturned k63 selectedFront)
  late2 = refl
  late3 : V.advance (physicalStep (P.publishInfra A.child₀ Types.muxer)) (at lateReturned k63 selectedFront) ≡ just (at lateQueued k63 selectedFront)
  late3 = refl
  late4 : V.advance (V.invokeStartTrace A.child₀) (at lateQueued k63 selectedFront) ≡ just (at lateQueued k63 tracingFront)
  late4 = refl
  late5 : V.advance (V.returnStartTrace A.child₀) (at lateQueued k63 tracingFront) ≡ just (at lateQueued k63 readyFront)
  late5 = refl
  late6 : V.advance (V.forkStart A.child₀ jid) (at lateQueued k63 readyFront) ≡ just (at lateBorn k63 bornFront)
  late6 = refl
  lateActions : List V.Event
  lateActions = shutdownStep (N.G.requestShutdown A.child₀) ∷
    physicalStep (P.infrastructureReturn A.child₀ Types.muxer err) ∷ physicalStep (P.publishInfra A.child₀ Types.muxer) ∷
    V.invokeStartTrace A.child₀ ∷ V.returnStartTrace A.child₀ ∷ V.forkStart A.child₀ jid ∷ []
  abstract
    initialized-late-fork : V.Runs initial ((prefixActions ++ ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ [])) ++ lateActions) (at lateBorn k63 bornFront)
    initialized-late-fork = Facts.append-protocols (Facts.append-protocols initialized-to-start selected-path)
      (V.more late1 (V.more late2 (V.more late3 (V.more late4 (V.more late5 (V.more late6 V.stop))))))
  late-fork-supply : Inv.ProtocolValid (at lateBorn k63 bornFront)
  late-fork-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-late-fork
  late-typed-result-retained : Pool.completions (P.poolAt A.child₀ (V.physical (V.base (at lateBorn k63 bornFront)))) ≡ infraPayload ∷ []
  late-typed-result-retained = refl
  no-monitor-pop-during-selected-start : V.advance (monitorStep (N.M.consume A.child₀)) (at lateQueued k63 readyFront) ≡ nothing
  no-monitor-pop-during-selected-start = refl

  -- A queued caller cell also wakes through the source Shutdown fallback if the
  -- mux fails BEFORE its command is selected or any physical job is born.
  queuedInfraReturned queuedInfra poppedInfra failedBeforeFork : Y.Model
  queuedInfraReturned = withPool infraReturnedPool legacy
  queuedInfra = withPool infraQueuedPool legacy
  poppedInfra = record (withPool (record infraQueuedPool { completions = [] }) legacy)
    { monitors = (A.child₀ , N.M.selected infraPayload) ∷ []
    ; tickets = (A.child₀ , N.D.ticket infraPayload N.D.captured) ∷ [] }
  failedBeforeFork = record poppedInfra
    { governor = IG.setMux (ident 0) (record Y.m1 { status = Mux.failed err }) (Y.governor poppedInfra)
    ; monitors = (A.child₀ , N.M.deadReady (N.M.failed err)) ∷ [] }
  fallback1 : V.advance (physicalStep (P.infrastructureReturn A.child₀ Types.muxer err)) (at legacy k63 zeroFront) ≡ just (at queuedInfraReturned k63 zeroFront)
  fallback1 = refl
  fallback2 : V.advance (physicalStep (P.publishInfra A.child₀ Types.muxer)) (at queuedInfraReturned k63 zeroFront) ≡ just (at queuedInfra k63 zeroFront)
  fallback2 = refl
  fallback3 : V.advance (monitorStep (N.M.consume A.child₀)) (at queuedInfra k63 zeroFront) ≡ just (at poppedInfra k63 zeroFront)
  fallback3 = refl
  fallback4 : V.advance (monitorStep (N.M.handleSelected A.child₀)) (at poppedInfra k63 zeroFront) ≡ just (at failedBeforeFork k63 zeroFront)
  fallback4 = refl
  fallbackActions : List V.Event
  fallbackActions = physicalStep (P.infrastructureReturn A.child₀ Types.muxer err) ∷ physicalStep (P.publishInfra A.child₀ Types.muxer) ∷
    monitorStep (N.M.consume A.child₀) ∷ monitorStep (N.M.handleSelected A.child₀) ∷ []
  abstract
    initialized-shutdown-observation : V.Runs initial ((prefixActions ++ ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ [])) ++ fallbackActions) (at failedBeforeFork k63 zeroFront)
    initialized-shutdown-observation = Facts.append-protocols (Facts.append-protocols initialized-to-start before-select-path)
      (V.more fallback1 (V.more fallback2 (V.more fallback3 (V.more fallback4 V.stop))))
  shutdown-observation-supply : Inv.ProtocolValid (at failedBeforeFork k63 zeroFront)
  shutdown-observation-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-shutdown-observation
  typed-head-before-command : V.advance (V.selectStart A.child₀) (at queuedInfra k63 zeroFront) ≡ nothing
  typed-head-before-command = refl
  fallback-without-job-result : V.observe rid (at failedBeforeFork k63 zeroFront) ≡ just (V.shutdownResult (Mux.failed err))
  fallback-without-job-result = refl
  fallback-did-not-invent-body : lookup jid (P.jobs (V.physical (V.base (at failedBeforeFork k63 zeroFront)))) ≡ nothing
  fallback-did-not-invent-body = refl

  -- A synchronous job error fills its own cell but does not reset StatusIdle.
  -- This is a separate initialized outcome, not an ordinary clean restart.
  errorPeer : Peer.Peer
  errorPeer = record L.p14 { runs = Peer.protocolRun proto (Peer.returned (errored err)) Peer.notStarted ∷ [] }
  errorContext : C.Context
  errorContext = withPeer errorPeer k63
  errorModel : Y.Model
  errorModel = withPhysical (Types.resultCaptured (errored err)) bornPool
  errorFront : V.Front
  errorFront = record bornFront { calls = (rid , record requested { thread = just jid; value = just (errored err) }) ∷ [] }
  error-step : V.advance (V.commitError jid err) (at waiting k63 bornFront) ≡ just (at errorModel errorContext errorFront)
  error-step = refl
  abstract
    initialized-error : V.Runs initial ((prefixActions ++ ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ (V.invokeStartTrace A.child₀) ∷ (V.returnStartTrace A.child₀) ∷ (V.forkStart A.child₀ jid) ∷ (physicalStep (P.protocolReturned jid)) ∷ [])) ++ (V.commitError jid err ∷ [])) (at errorModel errorContext errorFront)
    initialized-error = Facts.append-protocols (Facts.append-protocols initialized-to-start waiting-path) (V.more error-step V.stop)
  error-supply : Inv.ProtocolValid (at errorModel errorContext errorFront)
  error-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-error
  exact-error-cell : V.observe rid (at errorModel errorContext errorFront) ≡ just (V.localResult (errored err))
  exact-error-cell = refl
  error-slot-not-idle : V.slotIdle A.child₀ 1 errorFront ≡ false
  error-slot-not-idle = refl
  busy-is-a-source-error-frontier : V.startProblem (V.request (ident 1) (ident 0) L.p13 A.child₀ proto) (at errorModel errorContext errorFront) ≡ just Mux.alreadyRunning
  busy-is-a-source-error-frontier = refl

  -- Conditional restart/control snapshots; no second initialized activation is
  -- claimed here. Old local cells remain readable and cannot update a new run.
  restartContext : C.Context
  restartContext = withPeer (record L.p14 { runs = Peer.protocolRun proto Peer.running (Peer.returned clean) ∷ [] })
    (record kc63 { subsystem = record (C.subsystem kc63) { jobs = put (ident 1)
      (Sub.jobFrame (J.frame (G.job G.activate L.peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.startBundle IG.hot (1 ∷ []))) false false)
      (C.SubContext.jobs (C.subsystem kc63)) } })
  restartedFront : V.Front
  restartedFront = record freeFront
    { calls = (ident 21 , requested) ∷ V.calls freeFront
    ; commands = (A.child₀ , V.command (ident 21) 0 ∷ []) ∷ [] }
  restart-preserves-old-cell : V.observe rid (at registered restartContext restartedFront) ≡ just (V.localResult clean)
  restart-preserves-old-cell = refl
  restart-cell-is-empty : V.observe (ident 21) (at registered restartContext restartedFront) ≡ nothing
  restart-cell-is-empty = refl
  stale-cell-cannot-overwrite-current : V.cacheResult rid requested (errored err) restartedFront (V.base (at registered restartContext restartedFront)) ≡ V.base (at registered restartContext restartedFront)
  stale-cell-cannot-overwrite-current = refl
  -- Exercise the real start operation from a conditional second-activation PC.
  -- Fresh cells must precede old cells: Store.put would append them and make
  -- latest select the old clean generation instead of the current running one.
  restartBefore restartAfter : C.Context
  restartBefore = withPeer cleanPublished restartContext
  restartAfter = record restartContext { subsystem = record (C.subsystem restartContext)
    { jobs = put (ident 1)
      (Sub.jobFrame (J.frame (G.job G.activate L.peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.startBundle IG.hot [])) false false)
      (C.SubContext.jobs (C.subsystem restartContext)) } }
  conditional-restart-step : V.advance (V.startNext (ident 1) (ident 21))
    (at registered restartBefore freeFront) ≡ just (at registered restartAfter restartedFront)
  conditional-restart-step = refl
  latest-is-new-generation : V.latest A.child₀ 1 (V.calls restartedFront) ≡ just (ident 21 , requested)
  latest-is-new-generation = refl
  new-generation-is-busy : V.slotIdle A.child₀ 1 restartedFront ≡ false
  new-generation-is-busy = refl
  wrong-direction-capability : capability (ident 1) 1 ≡ false
  wrong-direction-capability = refl

  -- Both directions of protocol 1 coexist in the actual physical pool. The
  -- responder's real tracer produces IG events; the initiator has no such count.
  overlapFront : V.Front
  overlapFront = V.setCursor A.child₀ V.idleC bornFront
  overlapRegistered overlapDemand overlapSampled overlapTraced overlapReady overlapBorn overlapBoth : Y.Model
  overlapRegistered = withPhysical Types.waitingEgress registeredPool
  overlapDemand = Y.sourceMux Y.m2 [] overlapRegistered
  overlapSampled = Y.sourceMux Y.m3 [] overlapRegistered
  overlapTraced = Y.sourceMux Y.m4 Y.messages overlapRegistered
  overlapReady = Y.sourceMux Y.m5 Y.messages overlapRegistered
  responderPool bothPool : Pool.State
  responderPool = record registeredPool
    { handles = put (ident 21) Pool.bodyRunning (Pool.handles registeredPool); parentFork = just (ident 21) }
  bothPool = record responderPool { registered = ident 21 ∷ Pool.registered registeredPool; parentFork = nothing }
  responder21 : Types.ProtocolJob
  responder21 = Types.protocolJob A.child₀ (ident 0) Mux.responderJob 1 (ident 21) Types.executing
  overlapBorn = record (withPool responderPool (Y.sourceMux Y.m6 Y.messages overlapRegistered))
    { jobs = (jid , physicalJob Types.waitingEgress) ∷ (ident 21 , responder21) ∷ [] }
  overlapBoth = withPool bothPool overlapBorn
  overlap1 : V.advance (V.registerStart jid) (at waiting k63 bornFront) ≡ just (at overlapRegistered k63 overlapFront)
  overlap1 = refl
  overlap2 : V.advance (physicalStep (P.control A.child₀ (P.demand 1))) (at overlapRegistered k63 overlapFront) ≡ just (at overlapDemand k63 overlapFront)
  overlap2 = refl
  overlap3 : V.advance (physicalStep (P.control A.child₀ P.sampleTracer)) (at overlapDemand k63 overlapFront) ≡ just (at overlapSampled k63 overlapFront)
  overlap3 = refl
  overlap4 : V.advance (physicalStep (P.control A.child₀ P.commitTracer)) (at overlapSampled k63 overlapFront) ≡ just (at overlapTraced k63 overlapFront)
  overlap4 = refl
  overlap5 : V.advance (physicalStep (P.control A.child₀ P.finishStart)) (at overlapTraced k63 overlapFront) ≡ just (at overlapReady k63 overlapFront)
  overlap5 = refl
  overlap6 : V.advance (physicalStep (P.forkResponder A.child₀ (ident 21) (ident 21))) (at overlapReady k63 overlapFront) ≡ just (at overlapBorn k63 overlapFront)
  overlap6 = refl
  overlap7 : V.advance (physicalStep (P.registerProtocol (ident 21))) (at overlapBorn k63 overlapFront) ≡ just (at overlapBoth k63 overlapFront)
  overlap7 = refl
  overlapActions : List V.Event
  overlapActions = V.registerStart jid ∷ physicalStep (P.control A.child₀ (P.demand 1)) ∷
    physicalStep (P.control A.child₀ P.sampleTracer) ∷ physicalStep (P.control A.child₀ P.commitTracer) ∷
    physicalStep (P.control A.child₀ P.finishStart) ∷ physicalStep (P.forkResponder A.child₀ (ident 21) (ident 21)) ∷
    physicalStep (P.registerProtocol (ident 21)) ∷ []
  abstract
    initialized-directions : V.Runs initial ((prefixActions ++
      (V.startNext (ident 1) rid ∷ ps L.a63 ∷ physicalStep (P.control A.child₀ P.selectCommand) ∷
       V.selectStart A.child₀ ∷ V.invokeStartTrace A.child₀ ∷ V.returnStartTrace A.child₀ ∷
       V.forkStart A.child₀ jid ∷ physicalStep (P.protocolReturned jid) ∷ [])) ++ overlapActions)
      (at overlapBoth k63 overlapFront)
    initialized-directions = Facts.append-protocols (Facts.append-protocols initialized-to-start waiting-path)
      (V.more overlap1 (V.more overlap2 (V.more overlap3 (V.more overlap4 (V.more overlap5 (V.more overlap6 (V.more overlap7 V.stop)))))))
  directions-supply : Inv.ProtocolValid (at overlapBoth k63 overlapFront)
  directions-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-directions
  actual-direction-pair : P.jobs (V.physical (V.base (at overlapBoth k63 overlapFront))) ≡
    (jid , physicalJob Types.waitingEgress) ∷ (ident 21 , responder21) ∷ []
  actual-direction-pair = refl
  responder-notifications : Shared.inboundInfo (Y.world overlapBoth) ≡ Y.messages
  responder-notifications = refl

  -- A filled completion cell wins over Shutdown even after an actual later
  -- infrastructure failure. No fallback value overwrites the local result.
  afterCleanInfraReturned afterCleanInfraQueued afterCleanInfraPopped afterCleanFailed : Y.Model
  afterCleanInfraReturned = withPool (record registeredPool
    { handles = put (ident 0) (Pool.bodyReturned infraPayload) (Pool.handles registeredPool) }) registered
  afterCleanInfraQueued = withPool (record registeredPool
    { handles = put (ident 0) (Pool.deregisterPending Pool.normalExit) (Pool.handles registeredPool)
    ; completions = infraPayload ∷ [] }) registered
  afterCleanInfraPopped = record (withPool (record registeredPool
    { handles = put (ident 0) (Pool.deregisterPending Pool.normalExit) (Pool.handles registeredPool) }) registered)
    { monitors = (A.child₀ , N.M.selected infraPayload) ∷ []
    ; tickets = (A.child₀ , N.D.ticket infraPayload N.D.captured) ∷ [] }
  afterCleanFailed = record afterCleanInfraPopped
    { governor = IG.setMux (ident 0) (record Y.m1 { status = Mux.failed err }) (Y.governor afterCleanInfraPopped)
    ; monitors = (A.child₀ , N.M.deadReady (N.M.failed err)) ∷ [] }
  priority1 : V.advance (physicalStep (P.infrastructureReturn A.child₀ Types.muxer err)) (at registered kc63 freeFront) ≡ just (at afterCleanInfraReturned kc63 freeFront)
  priority1 = refl
  priority2 : V.advance (physicalStep (P.publishInfra A.child₀ Types.muxer)) (at afterCleanInfraReturned kc63 freeFront) ≡ just (at afterCleanInfraQueued kc63 freeFront)
  priority2 = refl
  priority3 : V.advance (monitorStep (N.M.consume A.child₀)) (at afterCleanInfraQueued kc63 freeFront) ≡ just (at afterCleanInfraPopped kc63 freeFront)
  priority3 = refl
  priority4 : V.advance (monitorStep (N.M.handleSelected A.child₀)) (at afterCleanInfraPopped kc63 freeFront) ≡ just (at afterCleanFailed kc63 freeFront)
  priority4 = refl
  abstract
    initialized-local-priority : V.Runs initial ((prefixActions ++
      (V.startNext (ident 1) rid ∷ ps L.a63 ∷ physicalStep (P.control A.child₀ P.selectCommand) ∷
       V.selectStart A.child₀ ∷ V.invokeStartTrace A.child₀ ∷ V.returnStartTrace A.child₀ ∷
       V.forkStart A.child₀ jid ∷ physicalStep (P.protocolReturned jid) ∷ V.commitClean jid ∷ [])) ++
      (V.registerStart jid ∷ physicalStep (P.infrastructureReturn A.child₀ Types.muxer err) ∷
       physicalStep (P.publishInfra A.child₀ Types.muxer) ∷ monitorStep (N.M.consume A.child₀) ∷
       monitorStep (N.M.handleSelected A.child₀) ∷ [])) (at afterCleanFailed kc63 freeFront)
    initialized-local-priority = Facts.append-protocols (Facts.append-protocols initialized-to-start clean-path)
      (V.more run10 (V.more priority1 (V.more priority2 (V.more priority3 (V.more priority4 V.stop)))))
  local-result-wins : V.observe rid (at afterCleanFailed kc63 freeFront) ≡ just (V.localResult clean)
  local-result-wins = refl
  priority-supply : Inv.ProtocolValid (at afterCleanFailed kc63 freeFront)
  priority-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-local-priority

  -- Physical completion-action reads and their selected peer continuations.
  -- All fixtures stay in this file, under the existing protocol acceptance.
  module Waiters where
    import ConnectionManagement.Rules.ProductionPolicy as Policy
    livePublished : C.Context
    livePublished = ctx L.c64 g60
    cooledPublished : C.Context
    cooledPublished = withPeer (Peer.cool (shiftPeer L.p15)) livePublished
    published-after-failure : V.advance (ps L.a64) (at failedBeforeFork k63 zeroFront) ≡
      just (at failedBeforeFork livePublished zeroFront)
    published-after-failure = refl
    poll-shutdown : V.advance (V.pollResults (ident 0) (ident 50)) (at failedBeforeFork livePublished zeroFront) ≡
      just (at failedBeforeFork cooledPublished zeroFront)
    poll-shutdown = refl
    abstract
      initialized-monitor-shutdown : V.Runs initial
        (((prefixActions ++ (V.startNext (ident 1) rid ∷ ps L.a63 ∷ physicalStep (P.control A.child₀ P.selectCommand) ∷ [])) ++ fallbackActions) ++
        (ps L.a64 ∷ V.pollResults (ident 0) (ident 50) ∷ []))
        (at failedBeforeFork cooledPublished zeroFront)
      initialized-monitor-shutdown = Facts.append-protocols initialized-shutdown-observation
        (V.more published-after-failure (V.more poll-shutdown V.stop))
    monitor-shutdown-supply : Inv.ProtocolValid (at failedBeforeFork cooledPublished zeroFront)
    monitor-shutdown-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-monitor-shutdown
    unpublished-shutdown-retries : V.advance (V.pollResults (ident 0) (ident 50)) (at failedBeforeFork k63 zeroFront) ≡ nothing
    unpublished-shutdown-retries = refl
    ready-empty-cell-retries : V.advance (V.pollResults (ident 0) (ident 50)) (at legacy livePublished zeroFront) ≡ nothing
    ready-empty-cell-retries = refl
    shutdown-retains-empty-cell : lookup rid (V.calls (V.front (at failedBeforeFork cooledPublished zeroFront))) ≡ just requested
    shutdown-retains-empty-cell = refl
    no-body-at-monitor-shutdown : lookup jid (P.jobs (V.physical (V.base (at failedBeforeFork cooledPublished zeroFront)))) ≡ nothing
    no-body-at-monitor-shutdown = refl
    no-result-enqueued-by-read : Pool.completions (P.poolAt A.child₀ (V.physical (V.base (at failedBeforeFork cooledPublished zeroFront)))) ≡ []
    no-result-enqueued-by-read = refl
    no-cold-from-mux-failure : V.advance (V.pollResults (ident 0) (ident 50)) (at failedBeforeFork cooledPublished zeroFront) ≡ nothing
    no-cold-from-mux-failure = refl
    no-logical-poll-alias : V.advance (ps (Sub.pollPeer (ident 0) (ident 50))) (at failedBeforeFork livePublished zeroFront) ≡ nothing
    no-logical-poll-alias = refl
    wrong-physical-monitor : V.advance (V.pollResults (ident 0) (ident 51)) (at failedBeforeFork livePublished zeroFront) ≡ nothing
    wrong-physical-monitor = refl
    published-shutdown-kind : V.firstPeer (ident 0) (shiftPeer L.p15) (at failedBeforeFork livePublished zeroFront) ≡
      just (G.deactivate , V.shutdownResult (Mux.failed err))
    published-shutdown-kind = refl

    -- A local clean cell wins even after physical mux failure and sends the
    -- monitor through a real successful deactivation, not the Shutdown branch.
    cleanAfterPublication : C.Context
    cleanAfterPublication = kc64
    cleanFollowup : J.Frame
    cleanFollowup = J.frame (G.job G.deactivate L.peerAddr (just (ident 0))) (ident 50) (ident 50) (ident 0) (ident 0) J.begin
    followupContext : J.Frame → Peer.Peer → C.Context
    followupContext f p = record (withPeer p cleanAfterPublication)
      { subsystem = record (C.subsystem (withPeer p cleanAfterPublication))
        { monitors = (ident 0 , f) ∷ [] } }
    deactivatingClean : Peer.Peer
    deactivatingClean = record cleanPublished { hotControl = Peer.terminate; warmControl = Peer.continue }
    retiredClean : Peer.Peer
    retiredClean = record deactivatingClean
      { status = Peer.peerWarm; runs = Peer.protocolRun proto (Peer.notRunning clean) (Peer.notRunning clean) ∷ []; promotedAt = nothing }
    cleanWait cleanReturned : J.Frame
    cleanWait = record cleanFollowup { pc = J.awaitHot }
    cleanReturned = record cleanFollowup { pc = J.complete G.succeeded }
    clean1 : V.advance (ps L.a64) (at afterCleanFailed kc63 freeFront) ≡ just (at afterCleanFailed cleanAfterPublication freeFront)
    clean1 = refl
    clean2 : V.advance (V.pollResults (ident 0) (ident 50)) (at afterCleanFailed cleanAfterPublication freeFront) ≡
      just (at afterCleanFailed (followupContext cleanFollowup cleanPublished) freeFront)
    clean2 = refl
    clean3 : V.advance (ps (Sub.monitorStep (ident 0) J.enter)) (at afterCleanFailed (followupContext cleanFollowup cleanPublished) freeFront) ≡
      just (at afterCleanFailed (followupContext cleanWait deactivatingClean) freeFront)
    clean3 = refl
    clean4 : V.advance (V.waitMonitorResults (ident 0)) (at afterCleanFailed (followupContext cleanWait deactivatingClean) freeFront) ≡
      just (at afterCleanFailed (followupContext cleanReturned retiredClean) freeFront)
    clean4 = refl
    cleanReadActions : List V.Event
    cleanReadActions = ps L.a64 ∷ V.pollResults (ident 0) (ident 50) ∷ ps (Sub.monitorStep (ident 0) J.enter) ∷ V.waitMonitorResults (ident 0) ∷ []
    abstract
      initialized-local-continuation : V.Runs initial
        (((prefixActions ++ (V.startNext (ident 1) rid ∷ ps L.a63 ∷ physicalStep (P.control A.child₀ P.selectCommand) ∷
          V.selectStart A.child₀ ∷ V.invokeStartTrace A.child₀ ∷ V.returnStartTrace A.child₀ ∷
          V.forkStart A.child₀ jid ∷ physicalStep (P.protocolReturned jid) ∷ V.commitClean jid ∷ [])) ++
          (V.registerStart jid ∷ physicalStep (P.infrastructureReturn A.child₀ Types.muxer err) ∷
          physicalStep (P.publishInfra A.child₀ Types.muxer) ∷ monitorStep (N.M.consume A.child₀) ∷
          monitorStep (N.M.handleSelected A.child₀) ∷ [])) ++ cleanReadActions)
        (at afterCleanFailed (followupContext cleanReturned retiredClean) freeFront)
      initialized-local-continuation = Facts.append-protocols initialized-local-priority
        (V.more clean1 (V.more clean2 (V.more clean3 (V.more clean4 V.stop))))
    local-continuation-supply : Inv.ProtocolValid (at afterCleanFailed (followupContext cleanReturned retiredClean) freeFront)
    local-continuation-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-local-continuation
    raw-wait-alias-refused : V.advance (ps (Sub.monitorStep (ident 0) J.observeHot))
      (at afterCleanFailed (followupContext cleanWait deactivatingClean) freeFront) ≡ nothing
    raw-wait-alias-refused = refl
    peer-read-is-not-body-return : lookup jid (Pool.handles (P.poolAt A.child₀
      (V.physical (V.base (at afterCleanFailed (followupContext cleanReturned retiredClean) freeFront))))) ≡ just Pool.bodyRunning
    peer-read-is-not-body-return = refl

    -- Actual target/policy selection launches a deactivation job while the
    -- eager protocol command remains queued and has never acquired a body.
    active64 active65 active66 active67 activeDone : C.Context
    active64 = livePublished
    active65 = ctx L.c65 g65
    active66 = ctx L.c66 g66
    active67 = ctx L.c67 g67
    activeDone = ctx L.c67 gBothDone
    deactForkPool deactPool : GP.Pool.State
    deactForkPool = record gBothDone
      { handles = put (ident 2) GP.Pool.bodyRunning (GP.Pool.handles gBothDone); parentFork = just (ident 2) }
    deactPool = record deactForkPool { registered = ident 2 ∷ []; parentFork = nothing }
    d68 : C.Context
    d68 = ctx L.c68 gBothDone
    d69 : C.Context
    d69 = ctx L.c69 gBothDone
    d70 : C.Context
    d70 = ctx L.c70 gBothDone
    d71 : C.Context
    d71 = ctx L.c71 gBothDone
    d72 : C.Context
    d72 = ctx L.c72 gBothDone
    d73 : C.Context
    d73 = ctx L.c73 gBothDone
    d74 : C.Context
    d74 = ctx L.c74 gBothDone
    d75 : C.Context
    d75 = ctx L.c75 gBothDone
    d76 : C.Context
    d76 = ctx L.c76 gBothDone
    d77 : C.Context
    d77 = ctx L.c77 gBothDone
    d78 : C.Context
    d78 = ctx L.c78 gBothDone
    d79 : C.Context
    d79 = ctx L.c79 gBothDone
    d80 : C.Context
    d80 = ctx L.c80 gBothDone
    d81 : C.Context
    d81 = ctx L.c81 gBothDone
    d82 : C.Context
    d82 = ctx L.c82 gBothDone
    d83 : C.Context
    d83 = ctx L.c83 gBothDone
    d84 : C.Context
    d84 = ctx L.c84 gBothDone
    d85 : C.Context
    d85 = ctx L.c85 gBothDone
    d86 : C.Context
    d86 = ctx L.c86 gBothDone
    d87 : C.Context
    d87 = ctx L.c87 gBothDone
    d88 : C.Context
    d88 = ctx L.c88 gBothDone
    d89 : C.Context
    d89 = ctx L.c89 gBothDone
    d90 : C.Context
    d90 = ctx L.c90 gBothDone
    d91 : C.Context
    d91 = ctx L.c91 gBothDone
    d92 : C.Context
    d92 = ctx L.c92 gBothDone
    d93 : C.Context
    d93 = ctx L.c93 deactForkPool
    d94 : C.Context
    d94 = ctx L.c94 deactPool
    d95 : C.Context
    d95 = ctx L.c95 deactPool
    activate1 : V.advance (ps L.a64) (at legacy k63 zeroFront) ≡ just (at legacy active64 zeroFront)
    activate1 = refl
    activate2 : V.advance (ps (Sub.jobStep (ident 1) (J.finishHotAt 12))) (at legacy active64 zeroFront) ≡ just (at legacy active65 zeroFront)
    activate2 = refl
    activate3 : V.advance (ps L.a66) (at legacy active65 zeroFront) ≡ just (at legacy active66 zeroFront)
    activate3 = refl
    activate4 : V.advance (ps L.a67) (at legacy active66 zeroFront) ≡ just (at legacy active67 zeroFront)
    activate4 = refl
    activate5 : V.advance (peerStep (PS.run (GP.publishAsyncResult (ident 1)))) (at legacy active67 zeroFront) ≡ just (at legacy activeDone zeroFront)
    activate5 = refl
    deact68 : V.advance (ps L.a68) (at legacy activeDone zeroFront) ≡ just (at legacy d68 zeroFront)
    deact68 = refl
    deact69 : V.advance (ps L.a69) (at legacy d68 zeroFront) ≡ just (at legacy d69 zeroFront)
    deact69 = refl
    deact70 : V.advance (ps (Sub.sampleTime 13)) (at legacy d69 zeroFront) ≡ just (at legacy d70 zeroFront)
    deact70 = refl
    deact71 : V.advance (ps L.a71) (at legacy d70 zeroFront) ≡ just (at legacy d71 zeroFront)
    deact71 = refl
    deact72 : V.advance (ps L.a72) (at legacy d71 zeroFront) ≡ just (at legacy d72 zeroFront)
    deact72 = refl
    deact73 : V.advance (ps (Sub.applyAt 13)) (at legacy d72 zeroFront) ≡ just (at legacy d73 zeroFront)
    deact73 = refl
    deact74 : V.advance (ps L.a74) (at legacy d73 zeroFront) ≡ just (at legacy d74 zeroFront)
    deact74 = refl
    deact75 : V.advance (ps L.a75) (at legacy d74 zeroFront) ≡ just (at legacy d75 zeroFront)
    deact75 = refl
    deact76 : V.advance (ps L.a76) (at legacy d75 zeroFront) ≡ just (at legacy d76 zeroFront)
    deact76 = refl
    deact77 : V.advance (ps L.a77) (at legacy d76 zeroFront) ≡ just (at legacy d77 zeroFront)
    deact77 = refl
    deact78 : V.advance (ps L.a78) (at legacy d77 zeroFront) ≡ just (at legacy d78 zeroFront)
    deact78 = refl
    deact79 : V.advance (ps (Sub.sampleTime 14)) (at legacy d78 zeroFront) ≡ just (at legacy d79 zeroFront)
    deact79 = refl
    deact80 : V.advance (ps L.a80) (at legacy d79 zeroFront) ≡ just (at legacy d80 zeroFront)
    deact80 = refl
    deact81 : V.advance (ps L.a81) (at legacy d80 zeroFront) ≡ just (at legacy d81 zeroFront)
    deact81 = refl
    deact82 : V.advance (ps (Sub.applyAt 14)) (at legacy d81 zeroFront) ≡ just (at legacy d82 zeroFront)
    deact82 = refl
    deact83 : V.advance (ps L.a83) (at legacy d82 zeroFront) ≡ just (at legacy d83 zeroFront)
    deact83 = refl
    deact84 : V.advance (ps L.a84) (at legacy d83 zeroFront) ≡ just (at legacy d84 zeroFront)
    deact84 = refl
    deact85 : V.advance (ps L.a85) (at legacy d84 zeroFront) ≡ just (at legacy d85 zeroFront)
    deact85 = refl
    deact86 : V.advance (ps L.a86) (at legacy d85 zeroFront) ≡ just (at legacy d86 zeroFront)
    deact86 = refl
    deact87 : V.advance (ps (Sub.sampleTime 15)) (at legacy d86 zeroFront) ≡ just (at legacy d87 zeroFront)
    deact87 = refl
    deact88 : V.advance (ps L.a88) (at legacy d87 zeroFront) ≡ just (at legacy d88 zeroFront)
    deact88 = refl
    deact89 : V.advance (ps L.a89) (at legacy d88 zeroFront) ≡ just (at legacy d89 zeroFront)
    deact89 = refl
    deact90 : V.advance (ps (Sub.applyAt 15)) (at legacy d89 zeroFront) ≡ just (at legacy d90 zeroFront)
    deact90 = refl
    deact91 : V.advance (ps L.a91) (at legacy d90 zeroFront) ≡ just (at legacy d91 zeroFront)
    deact91 = refl
    deact92 : V.advance (ps L.a92) (at legacy d91 zeroFront) ≡ just (at legacy d92 zeroFront)
    deact92 = refl
    deact93 : V.advance (ps L.a93) (at legacy d92 zeroFront) ≡ just (at legacy d93 zeroFront)
    deact93 = refl
    deact94 : V.advance (ps L.a94) (at legacy d93 zeroFront) ≡ just (at legacy d94 zeroFront)
    deact94 = refl
    deact95 : V.advance (ps L.a95) (at legacy d94 zeroFront) ≡ just (at legacy d95 zeroFront)
    deact95 = refl
    deactivationActions : List V.Event
    deactivationActions = (ps L.a64) ∷ (ps (Sub.jobStep (ident 1) (J.finishHotAt 12))) ∷ (ps L.a66) ∷ (ps L.a67) ∷ (peerStep (PS.run (GP.publishAsyncResult (ident 1)))) ∷ (ps L.a68) ∷ (ps L.a69) ∷ (ps (Sub.sampleTime 13)) ∷ (ps L.a71) ∷ (ps L.a72) ∷ (ps (Sub.applyAt 13)) ∷ (ps L.a74) ∷ (ps L.a75) ∷ (ps L.a76) ∷ (ps L.a77) ∷ (ps L.a78) ∷ (ps (Sub.sampleTime 14)) ∷ (ps L.a80) ∷ (ps L.a81) ∷ (ps (Sub.applyAt 14)) ∷ (ps L.a83) ∷ (ps L.a84) ∷ (ps L.a85) ∷ (ps L.a86) ∷ (ps (Sub.sampleTime 15)) ∷ (ps L.a88) ∷ (ps L.a89) ∷ (ps (Sub.applyAt 15)) ∷ (ps L.a91) ∷ (ps L.a92) ∷ (ps L.a93) ∷ (ps L.a94) ∷ (ps L.a95) ∷ []
    abstract
      deactivation-prefix : V.Runs (at legacy k63 zeroFront) deactivationActions (at legacy d95 zeroFront)
      deactivation-prefix = V.more activate1 (V.more activate2 (V.more activate3 (V.more activate4 (V.more activate5 (V.more deact68 (V.more deact69 (V.more deact70 (V.more deact71 (V.more deact72 (V.more deact73 (V.more deact74 (V.more deact75 (V.more deact76 (V.more deact77 (V.more deact78 (V.more deact79 (V.more deact80 (V.more deact81 (V.more deact82 (V.more deact83 (V.more deact84 (V.more deact85 (V.more deact86 (V.more deact87 (V.more deact88 (V.more deact89 (V.more deact90 (V.more deact91 (V.more deact92 (V.more deact93 (V.more deact94 (V.more deact95 (V.stop)))))))))))))))))))))))))))))))))

    deactFailedPeer : Peer.Peer
    deactFailedPeer = Peer.cool (shiftPeer L.p19)
    deactFailedFrame : Sub.JobFrame
    deactFailedFrame = Sub.jobFrame
      (J.frame (G.job G.deactivate L.peerAddr (just (ident 0))) (ident 14) (ident 15) (ident 14) (ident 0) (J.awaitCold G.failed)) false false
    deactFailure : C.Context
    deactFailure = record (withPeer deactFailedPeer d95)
      { subsystem = record (C.subsystem (withPeer deactFailedPeer d95))
        { jobs = put (ident 2) deactFailedFrame (C.SubContext.jobs (C.subsystem d95)) } }
    fail1 : V.advance (physicalStep (P.infrastructureReturn A.child₀ Types.muxer err))
      (at legacy d95 zeroFront) ≡ just (at queuedInfraReturned d95 zeroFront)
    fail1 = refl
    fail2 : V.advance (physicalStep (P.publishInfra A.child₀ Types.muxer))
      (at queuedInfraReturned d95 zeroFront) ≡ just (at queuedInfra d95 zeroFront)
    fail2 = refl
    fail3 : V.advance (monitorStep (N.M.consume A.child₀))
      (at queuedInfra d95 zeroFront) ≡ just (at poppedInfra d95 zeroFront)
    fail3 = refl
    fail4 : V.advance (monitorStep (N.M.handleSelected A.child₀))
      (at poppedInfra d95 zeroFront) ≡ just (at failedBeforeFork d95 zeroFront)
    fail4 = refl
    wait-deactivation-shutdown : V.advance (V.waitJobResults (ident 2))
      (at failedBeforeFork d95 zeroFront) ≡ just (at failedBeforeFork deactFailure zeroFront)
    wait-deactivation-shutdown = refl
    abstract
      initialized-job-shutdown : V.Runs initial
        (((prefixActions ++ (V.startNext (ident 1) rid ∷ ps L.a63 ∷ physicalStep (P.control A.child₀ P.selectCommand) ∷ [])) ++ deactivationActions) ++
         (physicalStep (P.infrastructureReturn A.child₀ Types.muxer err) ∷ physicalStep (P.publishInfra A.child₀ Types.muxer) ∷
          monitorStep (N.M.consume A.child₀) ∷ monitorStep (N.M.handleSelected A.child₀) ∷ V.waitJobResults (ident 2) ∷ []))
        (at failedBeforeFork deactFailure zeroFront)
      initialized-job-shutdown = Facts.append-protocols
        (Facts.append-protocols (Facts.append-protocols initialized-to-start before-select-path) deactivation-prefix)
        (V.more fail1 (V.more fail2 (V.more fail3 (V.more fail4 (V.more wait-deactivation-shutdown V.stop)))))
    job-shutdown-supply : Inv.ProtocolValid (at failedBeforeFork deactFailure zeroFront)
    job-shutdown-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-job-shutdown
    no-job-before-wait : lookup jid (P.jobs (V.physical (V.base (at failedBeforeFork deactFailure zeroFront)))) ≡ nothing
    no-job-before-wait = refl
    wait-retains-real-job-body : lookup (ident 2) (GP.Pool.handles (C.governorPool deactFailure)) ≡ just GP.Pool.bodyRunning
    wait-retains-real-job-body = refl
    wait-is-not-governor-publication : C.SubContext.completions (C.subsystem deactFailure) ≡ []
    wait-is-not-governor-publication = refl
    failed-deactivation-has-no-release : O.releasing (V.sourceOf (at failedBeforeFork deactFailure zeroFront)) ≡ []
    failed-deactivation-has-no-release = refl
    raw-job-wait-alias-refused : V.advance (ps (Sub.jobStep (ident 2) J.observeHot)) (at failedBeforeFork d95 zeroFront) ≡ nothing
    raw-job-wait-alias-refused = refl
    cancelled-deactivation : C.Context
    cancelled-deactivation = record d95 { governorPool = record deactPool
      { handles = put (ident 2) GP.Pool.bodyUnwinding (GP.Pool.handles deactPool) } }
    cancelled-job-cannot-read : V.advance (V.waitJobResults (ident 2)) (at failedBeforeFork cancelled-deactivation zeroFront) ≡ nothing
    cancelled-job-cannot-read = refl

    -- Conditional multi-protocol read controls. These snapshots test the STM
    -- combinators, not initialized births of additional application protocols.
    proto2 : Protocol
    proto2 = IG.protocol 2 hot IG.onDemand
    second : V.Call
    second = V.call (ident 0) (ident 0) A.child₀ (ident 0) proto2 (just (errored err)) nothing
    mixedFront : V.Front
    mixedFront = record zeroFront { calls = (ident 21 , second) ∷ V.calls zeroFront }
    mixedPeer : Peer.Peer
    mixedPeer = record L.p15 { runs = Peer.protocolRun proto Peer.running Peer.running ∷
      Peer.protocolRun proto2 (Peer.returned (errored err)) Peer.running ∷ [] }
    mixedContext : C.Context
    mixedContext = withPeer mixedPeer livePublished
    first-skips-retrying-action : V.firstPublished hot (ident 0) mixedPeer (at legacy mixedContext mixedFront) ≡
      just (2 , V.localResult (errored err))
    first-skips-retrying-action = refl
    all-does-not-short-circuit-error : V.allPublished hot (ident 0) mixedPeer (at legacy mixedContext mixedFront) ≡ nothing
    all-does-not-short-circuit-error = refl
    failed-all-reads-every-cell : V.allPublished hot (ident 0) mixedPeer (at failedBeforeFork mixedContext mixedFront) ≡
      just ((1 , V.shutdownResult (Mux.failed err)) ∷ (2 , V.localResult (errored err)) ∷ [])
    failed-all-reads-every-cell = refl
    proto0 : Protocol
    proto0 = IG.protocol 0 hot IG.onDemand
    neverPeer retiredPeer : Peer.Peer
    neverPeer = record mixedPeer { runs = Peer.protocolRun proto0 Peer.notStarted Peer.notStarted ∷ Peer.runs mixedPeer }
    retiredPeer = record mixedPeer { runs = Peer.protocolRun proto0 (Peer.notRunning clean) (Peer.notRunning clean) ∷ Peer.runs mixedPeer }
    never-blocks-first-after-choice : V.firstPublished hot (ident 0) neverPeer (at failedBeforeFork mixedContext mixedFront) ≡ nothing
    never-blocks-first-after-choice = refl
    retired-blocks-first-after-choice : V.firstPublished hot (ident 0) retiredPeer (at failedBeforeFork mixedContext mixedFront) ≡ nothing
    retired-blocks-first-after-choice = refl
    retired-participates-in-all : V.allPublished hot (ident 0) retiredPeer (at failedBeforeFork mixedContext mixedFront) ≡
      just ((0 , V.localResult clean) ∷ (1 , V.shutdownResult (Mux.failed err)) ∷ (2 , V.localResult (errored err)) ∷ [])
    retired-participates-in-all = refl
    priorityPeer : Peer.Peer
    priorityPeer = record L.p15 { runs = Peer.protocolRun proto Peer.running Peer.running ∷
      Peer.protocolRun (IG.protocol 2 IG.established IG.onDemand) (Peer.returned clean) (Peer.returned clean) ∷ [] }
    established-before-hot : V.firstPeer (ident 0) priorityPeer (at failedBeforeFork livePublished zeroFront) ≡
      just (G.close , V.localResult clean)
    established-before-hot = refl

    -- Conditional close/followup PCs isolate the all-bundle error continuation.
    -- The initialized job above already covers the real hot-bundle error path.
    closeFrame : J.Frame
    closeFrame = J.frame (G.job G.close L.peerAddr (just (ident 0))) (ident 50) (ident 50) (ident 0) (ident 0) J.awaitAll
    closingPeer : Peer.Peer
    closingPeer = record (Peer.cool (shiftPeer L.p15))
      { hotControl = Peer.terminate; warmControl = Peer.terminate; establishedControl = Peer.terminate }
    closeContext : J.Frame → C.Context
    closeContext f = record (withPeer closingPeer livePublished)
      { subsystem = record (C.subsystem (withPeer closingPeer livePublished))
        { monitors = (ident 0 , f) ∷ [] } }
    close-all-shutdown : V.advance (V.waitMonitorResults (ident 0)) (at failedBeforeFork (closeContext closeFrame) zeroFront) ≡
      just (at failedBeforeFork (closeContext (record closeFrame { pc = J.awaitCold G.failed })) zeroFront)
    close-all-shutdown = refl
    close-all-does-not-release : O.releasing (V.sourceOf
      (at failedBeforeFork (closeContext (record closeFrame { pc = J.awaitCold G.failed })) zeroFront)) ≡ []
    close-all-does-not-release = refl
    pending-close-cannot-finish : V.advance (V.waitMonitorResults (ident 0)) (at legacy (closeContext closeFrame) zeroFront) ≡ nothing
    pending-close-cannot-finish = refl
    stoppedPolicy : C.Context
    stoppedPolicy = record livePublished { policyStage = Policy.stopped (Policy.jobDelivery (ident 1) (Cases.ioFailure err)) }
    no-read-after-profile-stop : V.advance (V.pollResults (ident 0) (ident 50)) (at failedBeforeFork stoppedPolicy zeroFront) ≡ nothing
    no-read-after-profile-stop = refl
    interruptedMonitor : C.Context
    interruptedMonitor = record livePublished { monitorPool = record (C.monitorPool livePublished)
      { handles = put (ident 50) PS.Pool.bodyUnwinding (PS.Pool.handles (C.monitorPool livePublished)) } }
    no-read-after-monitor-interruption : V.advance (V.pollResults (ident 0) (ident 50)) (at failedBeforeFork interruptedMonitor zeroFront) ≡ nothing
    no-read-after-monitor-interruption = refl

  -- Selected eager initiator tracing, with real pool unwind and CM receipt.
  -- The standard ignored IG leg is normal; sync failure is an observed custom
  -- tracer input. Async receipt is permitted by the restored monitor body.
  module StartTrace where
    import ConnectionManagement.Rules.CMShutdown as Close
    import ConnectionManagement.Properties.MuxStartupUnwind as UnwindProof
    private
      module Unwind = N.R
      module W = N.W
      module SelectionProof = UnwindProof I.bearerClosed
    traceError : ErrorId
    traceError = errorId 181
    tracePrefixActions : List V.Event
    tracePrefixActions = V.startNext (ident 1) rid ∷ ps L.a63 ∷ physicalStep (P.control A.child₀ P.selectCommand) ∷
      V.selectStart A.child₀ ∷ V.invokeStartTrace A.child₀ ∷ []
    abstract
      tracePrefix : V.Runs initial (prefixActions ++ tracePrefixActions) (at legacy k63 tracingFront)
      tracePrefix = Facts.append-protocols initialized-to-start
        (V.more run1 (V.more run2 (V.more run3 (V.more run4 (V.more run5 V.stop)))))
    selectedFault : Unwind.Exception → Unwind.PC → Unwind.Fault
    selectedFault outcome phase = Unwind.fault I.captured (ident 0) (T.monitoring (ident 0) (ident 1))
      Mux.returned Unwind.poolBody outcome phase
    failedFront : Unwind.Exception → V.Front
    failedFront outcome = V.setCursor A.child₀ (V.failedC rid outcome) tracingFront
    faultAt : Unwind.Exception → Unwind.PC → Y.Model → C.Context → V.Runtime
    faultAt outcome phase m k = V.runtime
      (V.setStartFaults ((A.child₀ , selectedFault outcome phase) ∷ []) (V.base (at m k (failedFront outcome)))) (failedFront outcome)
    unwindStep : Unwind.Action → V.Event
    unwindStep a = V.dispatch (K.serverStep (E.run (S.run (N.run (N.C.run (N.D.run a))))))
    capture : ∀ outcome → V.advance (V.observeStartTraceException A.child₀ outcome) (at legacy k63 tracingFront) ≡
      just (faultAt outcome Unwind.awaitingClose legacy k63)
    capture outcome = refl
    capture-evidence : ∀ outcome → SelectionProof.Selection A.child₀ outcome (λ _ _ → just Unwind.poolBody)
      (N.raw (V.publication (V.base (at legacy k63 tracingFront))))
      (Unwind.local ((A.child₀ , selectedFault outcome Unwind.awaitingClose) ∷ []))
    capture-evidence outcome = SelectionProof.selection-observation A.child₀ outcome (λ _ _ → just Unwind.poolBody)
      (N.raw (V.publication (V.base (at legacy k63 tracingFront)))) refl
    order : List JobId
    order = ident 1 ∷ ident 0 ∷ []
    q0 q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 q13 q14 : Pool.State
    q0 = Y.engines
    q1 = record q0 { phase = Pool.closing; snapshot = order; remaining = order }
    q2 = record q1 { phase = Pool.cancelPending (ident 1) }
    q3 = record q2 { phase = Pool.joinPending (ident 1); handles = put (ident 1) Pool.bodyUnwinding (Pool.handles q2) }
    q4 = record q3 { handles = put (ident 1) (Pool.deregisterPending Pool.cancelledExit) (Pool.handles q3) }
    q5 = record q4 { handles = put (ident 1) (Pool.deregistered Pool.cancelledExit) (Pool.handles q4); registered = ident 0 ∷ [] }
    q6 = record q5 { handles = put (ident 1) (Pool.resultAvailable Pool.cancelledExit) (Pool.handles q5) }
    q7 = record q6 { phase = Pool.closing; remaining = ident 0 ∷ []; joined = ident 1 ∷ [] }
    q8 = record q7 { phase = Pool.cancelPending (ident 0) }
    q9 = record q8 { phase = Pool.joinPending (ident 0); handles = put (ident 0) Pool.bodyUnwinding (Pool.handles q8) }
    q10 = record q9 { handles = put (ident 0) (Pool.deregisterPending Pool.cancelledExit) (Pool.handles q9) }
    q11 = record q10 { handles = put (ident 0) (Pool.deregistered Pool.cancelledExit) (Pool.handles q10); registered = [] }
    q12 = record q11 { handles = put (ident 0) (Pool.resultAvailable Pool.cancelledExit) (Pool.handles q11) }
    q13 = record q12 { phase = Pool.closing; remaining = []; joined = order }
    q14 = record q13 { phase = Pool.closedPool }

    module Cleanup (outcome : Unwind.Exception) where
      atPool : Unwind.PC → Pool.State → V.Runtime
      atPool phase p = faultAt outcome phase (withPool p legacy) k63
      captureActions : List V.Event
      captureActions = V.observeStartTraceException A.child₀ outcome ∷ []
      abstract
        initialized-capture : V.Runs initial ((prefixActions ++ tracePrefixActions) ++ captureActions)
          (atPool Unwind.awaitingClose q0)
        initialized-capture = Facts.append-protocols tracePrefix (V.more (capture outcome) V.stop)
      poolEdge1 : V.advance (unwindStep (Unwind.beginClose A.child₀ order)) (atPool Unwind.awaitingClose q0) ≡ just (atPool Unwind.closing q1)
      poolEdge1 = refl
      poolEdge2 : V.advance (unwindStep (Unwind.requestCancel A.child₀)) (atPool Unwind.closing q1) ≡ just (atPool Unwind.closing q2)
      poolEdge2 = refl
      poolEdge3 : V.advance (unwindStep (Unwind.deliverCancel A.child₀)) (atPool Unwind.closing q2) ≡ just (atPool Unwind.closing q3)
      poolEdge3 = refl
      poolEdge4 : V.advance (shutdownStep (N.G.finishChildUnwind (ident 1))) (atPool Unwind.closing q3) ≡ just (atPool Unwind.closing q4)
      poolEdge4 = refl
      poolEdge5 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.demuxer)) (atPool Unwind.closing q4) ≡ just (atPool Unwind.closing q5)
      poolEdge5 = refl
      poolEdge6 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer)) (atPool Unwind.closing q5) ≡ just (atPool Unwind.closing q6)
      poolEdge6 = refl
      poolEdge7 : V.advance (unwindStep (Unwind.join A.child₀)) (atPool Unwind.closing q6) ≡ just (atPool Unwind.closing q7)
      poolEdge7 = refl
      poolEdge8 : V.advance (unwindStep (Unwind.requestCancel A.child₀)) (atPool Unwind.closing q7) ≡ just (atPool Unwind.closing q8)
      poolEdge8 = refl
      poolEdge9 : V.advance (unwindStep (Unwind.deliverCancel A.child₀)) (atPool Unwind.closing q8) ≡ just (atPool Unwind.closing q9)
      poolEdge9 = refl
      poolEdge10 : V.advance (shutdownStep (N.G.finishChildUnwind (ident 0))) (atPool Unwind.closing q9) ≡ just (atPool Unwind.closing q10)
      poolEdge10 = refl
      poolEdge11 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.muxer)) (atPool Unwind.closing q10) ≡ just (atPool Unwind.closing q11)
      poolEdge11 = refl
      poolEdge12 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.muxer)) (atPool Unwind.closing q11) ≡ just (atPool Unwind.closing q12)
      poolEdge12 = refl
      poolEdge13 : V.advance (unwindStep (Unwind.join A.child₀)) (atPool Unwind.closing q12) ≡ just (atPool Unwind.closing q13)
      poolEdge13 = refl
      poolEdge14 : V.advance (unwindStep (Unwind.finishClose A.child₀)) (atPool Unwind.closing q13) ≡ just (atPool Unwind.poolClosed q14)
      poolEdge14 = refl
      poolActions : List V.Event
      poolActions = (unwindStep (Unwind.beginClose A.child₀ order)) ∷ (unwindStep (Unwind.requestCancel A.child₀)) ∷ (unwindStep (Unwind.deliverCancel A.child₀)) ∷ (shutdownStep (N.G.finishChildUnwind (ident 1))) ∷ (physicalStep (P.deregisterInfra A.child₀ Types.demuxer)) ∷ (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer)) ∷ (unwindStep (Unwind.join A.child₀)) ∷ (unwindStep (Unwind.requestCancel A.child₀)) ∷ (unwindStep (Unwind.deliverCancel A.child₀)) ∷ (shutdownStep (N.G.finishChildUnwind (ident 0))) ∷ (physicalStep (P.deregisterInfra A.child₀ Types.muxer)) ∷ (physicalStep (P.asyncInfraResult A.child₀ Types.muxer)) ∷ (unwindStep (Unwind.join A.child₀)) ∷ (unwindStep (Unwind.finishClose A.child₀)) ∷ []
      abstract
        closePath : V.Runs (atPool Unwind.awaitingClose q0) poolActions (atPool Unwind.poolClosed q14)
        closePath = V.more poolEdge1 (V.more poolEdge2 (V.more poolEdge3 (V.more poolEdge4 (V.more poolEdge5 (V.more poolEdge6 (V.more poolEdge7 (V.more poolEdge8 (V.more poolEdge9 (V.more poolEdge10 (V.more poolEdge11 (V.more poolEdge12 (V.more poolEdge13 (V.more poolEdge14 (V.stop))))))))))))))
        initialized-close : V.Runs initial (((prefixActions ++ tracePrefixActions) ++ captureActions) ++ poolActions) (atPool Unwind.poolClosed q14)
        initialized-close = Facts.append-protocols initialized-capture closePath
      close-supply : Inv.ProtocolValid (atPool Unwind.poolClosed q14)
      close-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-close
      actual-joined-snapshot : Pool.joined (P.poolAt A.child₀ (V.physical (V.base (atPool Unwind.poolClosed q14)))) ≡ order
      actual-joined-snapshot = refl
      no-initiator-created : lookup jid (P.jobs (V.physical (V.base (atPool Unwind.poolClosed q14)))) ≡ nothing
      no-initiator-created = refl
      no-local-result-created : lookup rid (V.calls (V.front (atPool Unwind.poolClosed q14))) ≡ just requested
      no-local-result-created = refl
      no-cancellation-result-enqueued : Pool.completions (P.poolAt A.child₀ (V.physical (V.base (atPool Unwind.poolClosed q14)))) ≡ []
      no-cancellation-result-enqueued = refl

    module Sync where
      module Path = Cleanup (Unwind.sync traceError)
      ready : V.Runtime
      ready = faultAt (Unwind.sync traceError) Unwind.readyBuffer (withPool q14 legacy) k63
      continue : V.advance (unwindStep (Unwind.continueSync A.child₀)) (Path.atPool Unwind.poolClosed q14) ≡ just ready
      continue = refl
      abstract
        initialized-outcome : V.Runs initial
          ((((prefixActions ++ tracePrefixActions) ++ Path.captureActions) ++ Path.poolActions) ++
            (unwindStep (Unwind.continueSync A.child₀) ∷ [])) ready
        initialized-outcome = Facts.append-protocols Path.initialized-close (V.more continue V.stop)
      supply : Inv.ProtocolValid ready
      supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-outcome
      still-ready : P.muxAt (ident 0) (V.physical (V.base ready)) ≡ just Y.m1
      still-ready = refl
      pending-completion-still-retries : V.observe rid ready ≡ nothing
      pending-completion-still-retries = refl
      published : V.Runtime
      published = faultAt (Unwind.sync traceError) Unwind.readyBuffer (withPool q14 legacy) Waiters.livePublished
      caller-can-publish : V.advance (ps L.a64) ready ≡ just published
      caller-can-publish = refl
      published-wait-still-retries : V.advance (V.pollResults (ident 0) (ident 50)) published ≡ nothing
      published-wait-still-retries = refl

    failedMux deadMux sampledMux completedMux : Mux.Mux
    failedMux = record Y.m1 { status = Mux.failed traceError }
    deadMux = record failedMux { callback = Mux.readActive Mux.muxStopped }
    sampledMux = record failedMux { callback = Mux.commitTrace true Mux.muxStopped }
    completedMux = record failedMux { traceCounters = nothing }
    failedModel deadModel sampledModel completedModel : Y.Model
    failedModel = Y.sourceMux failedMux [] (withPool q14 legacy)
    deadModel = Y.sourceMux deadMux [] (withPool q14 legacy)
    sampledModel = Y.sourceMux sampledMux [] (withPool q14 legacy)
    completedModel = Y.sourceMux completedMux (Shared.muxFinished A.key₀ ∷ []) (withPool q14 legacy)

    module Async where
      module Path = Cleanup (Unwind.async traceError)
      status dead sampled completed ready : V.Runtime
      status = faultAt (Unwind.async traceError) Unwind.asyncStatus failedModel k63
      dead = faultAt (Unwind.async traceError) Unwind.asyncDead deadModel k63
      sampled = faultAt (Unwind.async traceError) Unwind.asyncDead sampledModel k63
      completed = faultAt (Unwind.async traceError) Unwind.asyncDead completedModel k63
      ready = faultAt (Unwind.async traceError) Unwind.readyBuffer completedModel k63
      catch1 : V.advance (unwindStep (Unwind.writeAsyncFailure A.child₀)) (Path.atPool Unwind.poolClosed q14) ≡ just status
      catch1 = refl
      catch2 : V.advance (unwindStep (Unwind.beginDead A.child₀)) status ≡ just dead
      catch2 = refl
      catch3 : V.advance (unwindStep (Unwind.sampleDead A.child₀)) dead ≡ just sampled
      catch3 = refl
      catch4 : V.advance (unwindStep (Unwind.commitDead A.child₀)) sampled ≡ just completed
      catch4 = refl
      catch5 : V.advance (unwindStep (Unwind.finishDead A.child₀)) completed ≡ just ready
      catch5 = refl
      catchActions : List V.Event
      catchActions = unwindStep (Unwind.writeAsyncFailure A.child₀) ∷ unwindStep (Unwind.beginDead A.child₀) ∷
        unwindStep (Unwind.sampleDead A.child₀) ∷ unwindStep (Unwind.commitDead A.child₀) ∷ unwindStep (Unwind.finishDead A.child₀) ∷ []
      abstract
        catchPath : V.Runs (Path.atPool Unwind.poolClosed q14) catchActions ready
        catchPath = V.more catch1 (V.more catch2 (V.more catch3 (V.more catch4 (V.more catch5 V.stop))))
        initialized-outcome : V.Runs initial
          ((((prefixActions ++ tracePrefixActions) ++ Path.captureActions) ++ Path.poolActions) ++ catchActions) ready
        initialized-outcome = Facts.append-protocols Path.initialized-close catchPath
      supply : Inv.ProtocolValid ready
      supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-outcome
      early-failed-write-refused : V.advance (unwindStep (Unwind.writeAsyncFailure A.child₀))
        (Path.atPool Unwind.awaitingClose q0) ≡ nothing
      early-failed-write-refused = refl
      fallback-after-actual-close : V.observe rid ready ≡ just (V.shutdownResult (Mux.failed traceError))
      fallback-after-actual-close = refl
      published cooled : V.Runtime
      published = faultAt (Unwind.async traceError) Unwind.readyBuffer completedModel Waiters.livePublished
      cooled = faultAt (Unwind.async traceError) Unwind.readyBuffer completedModel Waiters.cooledPublished
      peer1 : V.advance (ps L.a64) ready ≡ just published
      peer1 = refl
      peer2 : V.advance (V.pollResults (ident 0) (ident 50)) published ≡ just cooled
      peer2 = refl
      abstract
        initialized-peer-cooling : V.Runs initial
          (((((prefixActions ++ tracePrefixActions) ++ Path.captureActions) ++ Path.poolActions) ++ catchActions) ++
           (ps L.a64 ∷ V.pollResults (ident 0) (ident 50) ∷ [])) cooled
        initialized-peer-cooling = Facts.append-protocols initialized-outcome (V.more peer1 (V.more peer2 V.stop))
      peer-supply : Inv.ProtocolValid cooled
      peer-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-peer-cooling

    no-fault-before-invocation : V.advance (V.observeStartTraceException A.child₀ (Unwind.sync traceError))
      (at legacy k63 selectedFront) ≡ nothing
    no-fault-before-invocation = refl
    no-fault-in-masked-registration-gap : V.advance (V.observeStartTraceException A.child₀ (Unwind.async traceError))
      (at born k63 bornFront) ≡ nothing
    no-fault-in-masked-registration-gap = refl
    raw-abort-cannot-erase-start-trace : V.advance (shutdownStep (N.G.abortOwner A.child₀ traceError))
      (at legacy k63 tracingFront) ≡ nothing
    raw-abort-cannot-erase-start-trace = refl
    no-return-after-exception : V.advance (V.returnStartTrace A.child₀) Async.ready ≡ nothing
    no-return-after-exception = refl
    no-late-fork-after-exception : V.advance (V.forkStart A.child₀ jid) Async.ready ≡ nothing
    no-late-fork-after-exception = refl
    no-second-exception-receipt : V.advance (V.observeStartTraceException A.child₀ (Unwind.async traceError)) Async.ready ≡ nothing
    no-second-exception-receipt = refl
    no-early-join : V.advance (unwindStep (Unwind.join A.child₀)) (Async.Path.atPool Unwind.closing q3) ≡ nothing
    no-early-join = refl
    no-early-scope-close : V.advance (unwindStep (Unwind.finishClose A.child₀)) (Async.Path.atPool Unwind.closing q7) ≡ nothing
    no-early-scope-close = refl

    module CM where
      withCoordinator : Close.State → V.Runtime → V.Runtime
      -- Conditional CM-close profile: reaching this lexical stage while the
      -- start remains pending is not claimed by the initialized-outcome histories above.
      withCoordinator coordinator s = record s { base = record b
        { server = record (K.server b) { base = record (E.base (K.server b)) { stage = S.closingCM } } } }
        where b = V.setStartShutdown coordinator (V.base s)
      conditionalStart : V.Runtime
      conditionalStart = withCoordinator Close.initialState (at legacy k63 tracingFront)
      coordinatorStep : Close.Action → V.Event
      coordinatorStep a = unwindStep (Unwind.run (N.D.X.run (W.shutdownStep a)))
      captured read send acknowledged cmWait : Close.State
      captured = Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []
      read = Close.shutdownState (Close.sendReady (ident 0) A.child₀) (ident 0 ∷ []) [] []
      send = Close.shutdownState (Close.awaitDelivery (ident 0) A.child₀) (ident 0 ∷ []) [] []
      acknowledged = Close.shutdownState Close.reading (ident 0 ∷ []) [] (A.child₀ ∷ [])
      cmWait = Close.shutdownState Close.awaitResults (ident 0 ∷ []) [] (A.child₀ ∷ [])
      c1 c2 c3 c4 c5 : V.Runtime
      c1 = withCoordinator captured (at legacy k63 tracingFront)
      c2 = withCoordinator read (at legacy k63 tracingFront)
      c3 = withCoordinator send (at legacy k63 tracingFront)
      c4 = withCoordinator acknowledged (faultAt (Unwind.async traceError) Unwind.awaitingClose legacy k63)
      c5 = withCoordinator cmWait (faultAt (Unwind.async traceError) Unwind.awaitingClose legacy k63)
      cm1 : V.advance (coordinatorStep Close.captureSnapshot) conditionalStart ≡ just c1
      cm1 = refl
      cm2 : V.advance (coordinatorStep Close.readEntry) c1 ≡ just c2
      cm2 = refl
      cm3 : V.advance (coordinatorStep Close.requestCancellation) c2 ≡ just c3
      cm3 = refl
      cm4 : V.advance (V.deliverStartTraceShutdown traceError) c3 ≡ just c4
      cm4 = refl
      cm5 : V.advance (coordinatorStep Close.finishTraversal) c4 ≡ just c5
      cm5 = refl
      receiptActions : List V.Event
      receiptActions = coordinatorStep Close.captureSnapshot ∷ coordinatorStep Close.readEntry ∷ coordinatorStep Close.requestCancellation ∷
        V.deliverStartTraceShutdown traceError ∷ coordinatorStep Close.finishTraversal ∷ []
      abstract
        receiptPath : V.Runs conditionalStart receiptActions c5
        receiptPath = V.more cm1 (V.more cm2 (V.more cm3 (V.more cm4 (V.more cm5 V.stop))))
      no-implicit-cm-ack : V.advance (V.observeStartTraceException A.child₀ (Unwind.async traceError)) c3 ≡
        just (withCoordinator send (faultAt (Unwind.async traceError) Unwind.awaitingClose legacy k63))
      no-implicit-cm-ack = refl
      raw-ack-refused : V.advance (coordinatorStep Close.acknowledgeDelivery) c3 ≡ nothing
      raw-ack-refused = refl
      duplicate-receipt-refused : V.advance (V.deliverStartTraceShutdown traceError) c4 ≡ nothing
      duplicate-receipt-refused = refl
      no-receipt-before-send : V.advance (V.deliverStartTraceShutdown traceError) c2 ≡ nothing
      no-receipt-before-send = refl
      no-cm-receipt-during-callback : V.advance (V.deliverStartTraceShutdown traceError)
        (record (at legacy k63 tracingFront) { base = V.setStartShutdown send (V.base (at legacy k63 tracingFront)) }) ≡ nothing
      no-cm-receipt-during-callback = refl
      receipt-does-not-join : Pool.phase (P.poolAt A.child₀ (V.physical (V.base c4))) ≡ Pool.openPool
      receipt-does-not-join = refl
      receipt-is-not-handler-result : W.resultReady A.child₀ (Unwind.base (N.raw (V.publication (V.base c4)))) ≡ false
      receipt-is-not-handler-result = refl
      cm-still-waits : V.advance (coordinatorStep Close.finishClose) c5 ≡ nothing
      cm-still-waits = refl
      atCM : Unwind.PC → Pool.State → V.Runtime
      atCM phase p = withCoordinator cmWait (faultAt (Unwind.async traceError) phase (withPool p legacy) k63)
      poolEdge1 : V.advance (unwindStep (Unwind.beginClose A.child₀ order)) (atCM Unwind.awaitingClose q0) ≡ just (atCM Unwind.closing q1)
      poolEdge1 = refl
      poolEdge2 : V.advance (unwindStep (Unwind.requestCancel A.child₀)) (atCM Unwind.closing q1) ≡ just (atCM Unwind.closing q2)
      poolEdge2 = refl
      poolEdge3 : V.advance (unwindStep (Unwind.deliverCancel A.child₀)) (atCM Unwind.closing q2) ≡ just (atCM Unwind.closing q3)
      poolEdge3 = refl
      poolEdge4 : V.advance (shutdownStep (N.G.finishChildUnwind (ident 1))) (atCM Unwind.closing q3) ≡ just (atCM Unwind.closing q4)
      poolEdge4 = refl
      poolEdge5 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.demuxer)) (atCM Unwind.closing q4) ≡ just (atCM Unwind.closing q5)
      poolEdge5 = refl
      poolEdge6 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer)) (atCM Unwind.closing q5) ≡ just (atCM Unwind.closing q6)
      poolEdge6 = refl
      poolEdge7 : V.advance (unwindStep (Unwind.join A.child₀)) (atCM Unwind.closing q6) ≡ just (atCM Unwind.closing q7)
      poolEdge7 = refl
      poolEdge8 : V.advance (unwindStep (Unwind.requestCancel A.child₀)) (atCM Unwind.closing q7) ≡ just (atCM Unwind.closing q8)
      poolEdge8 = refl
      poolEdge9 : V.advance (unwindStep (Unwind.deliverCancel A.child₀)) (atCM Unwind.closing q8) ≡ just (atCM Unwind.closing q9)
      poolEdge9 = refl
      poolEdge10 : V.advance (shutdownStep (N.G.finishChildUnwind (ident 0))) (atCM Unwind.closing q9) ≡ just (atCM Unwind.closing q10)
      poolEdge10 = refl
      poolEdge11 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.muxer)) (atCM Unwind.closing q10) ≡ just (atCM Unwind.closing q11)
      poolEdge11 = refl
      poolEdge12 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.muxer)) (atCM Unwind.closing q11) ≡ just (atCM Unwind.closing q12)
      poolEdge12 = refl
      poolEdge13 : V.advance (unwindStep (Unwind.join A.child₀)) (atCM Unwind.closing q12) ≡ just (atCM Unwind.closing q13)
      poolEdge13 = refl
      poolEdge14 : V.advance (unwindStep (Unwind.finishClose A.child₀)) (atCM Unwind.closing q13) ≡ just (atCM Unwind.poolClosed q14)
      poolEdge14 = refl
      abstract
        pool-close-path : V.Runs conditionalStart (receiptActions ++ Async.Path.poolActions) (atCM Unwind.poolClosed q14)
        pool-close-path = Facts.append-protocols receiptPath
          (V.more poolEdge1 (V.more poolEdge2 (V.more poolEdge3 (V.more poolEdge4 (V.more poolEdge5 (V.more poolEdge6 (V.more poolEdge7 (V.more poolEdge8 (V.more poolEdge9 (V.more poolEdge10 (V.more poolEdge11 (V.more poolEdge12 (V.more poolEdge13 (V.more poolEdge14 (V.stop)))))))))))))))
      post1 : V.advance (unwindStep (Unwind.writeAsyncFailure A.child₀)) (atCM Unwind.poolClosed q14) ≡ just (withCoordinator cmWait Async.status)
      post1 = refl
      post2 : V.advance (unwindStep (Unwind.beginDead A.child₀)) (withCoordinator cmWait Async.status) ≡ just (withCoordinator cmWait Async.dead)
      post2 = refl
      post3 : V.advance (unwindStep (Unwind.sampleDead A.child₀)) (withCoordinator cmWait Async.dead) ≡ just (withCoordinator cmWait Async.sampled)
      post3 = refl
      post4 : V.advance (unwindStep (Unwind.commitDead A.child₀)) (withCoordinator cmWait Async.sampled) ≡ just (withCoordinator cmWait Async.completed)
      post4 = refl
      post5 : V.advance (unwindStep (Unwind.finishDead A.child₀)) (withCoordinator cmWait Async.completed) ≡ just (withCoordinator cmWait Async.ready)
      post5 = refl
      abstract
        catch-path : V.Runs conditionalStart ((receiptActions ++ Async.Path.poolActions) ++ Async.catchActions) (withCoordinator cmWait Async.ready)
        catch-path = Facts.append-protocols pool-close-path
          (V.more post1 (V.more post2 (V.more post3 (V.more post4 (V.more post5 (V.stop))))))
      actual-pool-closed : Pool.phase (P.poolAt A.child₀ (V.physical (V.base (withCoordinator cmWait Async.ready)))) ≡ Pool.closedPool
      actual-pool-closed = refl
      still-no-handler-result : W.resultReady A.child₀ (Unwind.base (N.raw (V.publication (V.base (withCoordinator cmWait Async.ready))))) ≡ false
      still-no-handler-result = refl
      no-cm-result-from-pool-close : V.advance (coordinatorStep Close.finishClose) (withCoordinator cmWait Async.ready) ≡ nothing
      no-cm-result-from-pool-close = refl

    -- Every scope/coordinator snapshot below is the endpoint of an actual
    -- successful step from tracePrefix. No closingCM stage is assumed.
    module ScopedCM where
      scopeError igError : ErrorId
      scopeError = errorId 182
      igError = errorId 183
      govCancel : Cancel.Frame
      govCancel = Cancel.cancellation (ident 12) scopeError Cancel.noCaller (Cancel.finished Cancel.abandoned)
      gc0 gc1 gc2 gc3 gc4 gc5 gc6 gc7 : GP.Pool.State
      gc0 = record g60 { phase = GP.Pool.closing; snapshot = ident 1 ∷ []; remaining = ident 1 ∷ [] }
      gc1 = record gc0 { phase = GP.Pool.cancelPending (ident 1) }
      gc2 = record gc0 { phase = GP.Pool.joinPending (ident 1)
        ; handles = put (ident 1) GP.Pool.bodyUnwinding (GP.Pool.handles gc0) }
      gc3 = record gc2 { handles = put (ident 1) (GP.Pool.deregisterPending GP.Pool.cancelledExit) (GP.Pool.handles gc2) }
      gc4 = record gc3 { handles = put (ident 1) (GP.Pool.deregistered GP.Pool.cancelledExit) (GP.Pool.handles gc3); registered = [] }
      gc5 = record gc4 { handles = put (ident 1) (GP.Pool.resultAvailable GP.Pool.cancelledExit) (GP.Pool.handles gc4) }
      gc6 = record gc5 { phase = GP.Pool.closing; remaining = []; joined = ident 1 ∷ [] }
      gc7 = record gc6 { phase = GP.Pool.closedPool }
      govBase : Scope.State → GP.Pool.State → C.Context
      govBase q p = record k63 { scopes = q; governorPool = p }
      govInterrupted : Scope.State → GP.Pool.State → C.Context
      govInterrupted q p = record (govBase q p) { unwinding = (ident 1 , govCancel) ∷ [] }
      abandonedJob : Sub.JobFrame
      abandonedJob = Sub.jobFrame
        (J.frame (G.job G.activate L.peerAddr (just (ident 0))) (ident 12) (ident 13) (ident 12) (ident 0) (J.publishBundle hot)) false true
      govRemoved : Scope.State → GP.Pool.State → C.Context
      govRemoved q p = record (govInterrupted q p)
        { subsystem = record (C.subsystem k63)
          { jobs = put (ident 1) abandonedJob (C.SubContext.jobs (C.subsystem k63)); pool = [] } }
      govSettled : Scope.State → C.Context
      govSettled q = govRemoved q gc7
      innerDone : C.Context
      innerDone = govSettled Fixtures.q22
      mc0 mc1 mc2 mc3 mc4 mc5 mc6 mc7 : PS.Pool.State
      mc0 = record (C.monitorPool innerDone) { phase = PS.Pool.closing; snapshot = ident 50 ∷ []; remaining = ident 50 ∷ [] }
      mc1 = record mc0 { phase = PS.Pool.cancelPending (ident 50) }
      mc2 = record mc0 { phase = PS.Pool.joinPending (ident 50)
        ; handles = put (ident 50) PS.Pool.bodyUnwinding (PS.Pool.handles mc0) }
      mc3 = record mc2 { handles = put (ident 50) (PS.Pool.deregisterPending PS.Pool.cancelledExit) (PS.Pool.handles mc2) }
      mc4 = record mc3 { handles = put (ident 50) (PS.Pool.deregistered PS.Pool.cancelledExit) (PS.Pool.handles mc3); registered = [] }
      mc5 = record mc4 { handles = put (ident 50) (PS.Pool.resultAvailable PS.Pool.cancelledExit) (PS.Pool.handles mc4) }
      mc6 = record mc5 { phase = PS.Pool.closing; remaining = []; joined = ident 50 ∷ [] }
      mc7 = record mc6 { phase = PS.Pool.closedPool }
      monCancel : Cancel.Frame
      monCancel = Cancel.cancellation (ident 50) scopeError Cancel.noCaller (Cancel.finished Cancel.abandoned)
      stoppedThread : PS.MonitorPC → PS.Thread
      stoppedThread pc = PS.thread (ident 0) (ident 50) (ident 0) PS.returned pc (just monCancel) nothing
      monBase : PS.Pool.State → C.Context
      monBase p = record innerDone { monitorPool = p }
      monInterrupted : PS.Pool.State → C.Context
      monInterrupted p = record (monBase p) { monitors = (ident 50 , stoppedThread PS.cancelling) ∷ [] }
      monStopped : PS.Pool.State → C.Context
      monStopped p = withPeer (record L.p14 { monitorStarted = false })
        (record (monBase p) { monitors = (ident 50 , stoppedThread PS.exited) ∷ [] })
      peerDone : C.Context
      peerDone = monStopped mc7

      -- Data-only rendering keeps the one authoritative CM configuration and
      -- the actual selected cursor; each stage change requires a step proof.
      scene : S.Stage → Bool → E.Exit → Y.Model → C.Context → V.Front → V.Runtime
      scene stage listener ex m k f = record original { base = record b
        { server = record (K.server b) { base = record (E.base (K.server b))
          { stage = stage; listenerOpen = listener }; exit = ex } } }
        where
        original = at m k f
        b = V.base original
      pre : C.Context → V.Runtime
      pre k = scene S.serving true E.emptyExit legacy k tracingFront
      returnedCallback : V.Runtime
      returnedCallback = scene S.actionBodyExited true E.emptyExit legacy peerDone tracingFront
      peerEdge1 : V.advance (scoped (Scope.beginUnwind)) (pre k63) ≡ just (pre (atScope Fixtures.q1 k63))
      peerEdge1 = refl
      peerEdge2 : V.advance (scoped (Scope.requestCancel)) (pre (atScope Fixtures.q1 k63)) ≡ just (pre (atScope Fixtures.q2 k63))
      peerEdge2 = refl
      peerEdge3 : V.advance (scoped (Scope.deliverCancel)) (pre (atScope Fixtures.q2 k63)) ≡ just (pre (atScope Fixtures.q3 k63))
      peerEdge3 = refl
      peerEdge4 : V.advance (scoped (Scope.bodyExit Scope.churn)) (pre (atScope Fixtures.q3 k63)) ≡ just (pre (atScope Fixtures.q4 k63))
      peerEdge4 = refl
      peerEdge5 : V.advance (scoped (Scope.publishResult Scope.churn)) (pre (atScope Fixtures.q4 k63)) ≡ just (pre (atScope Fixtures.q5 k63))
      peerEdge5 = refl
      peerEdge6 : V.advance (scoped (Scope.join)) (pre (atScope Fixtures.q5 k63)) ≡ just (pre (atScope Fixtures.q6 k63))
      peerEdge6 = refl
      peerEdge7 : V.advance (scoped (Scope.requestCancel)) (pre (atScope Fixtures.q6 k63)) ≡ just (pre (atScope Fixtures.q7 k63))
      peerEdge7 = refl
      peerEdge8 : V.advance (scoped (Scope.deliverCancel)) (pre (atScope Fixtures.q7 k63)) ≡ just (pre (atScope Fixtures.q8 k63))
      peerEdge8 = refl
      peerEdge9 : V.advance (peerStep (PS.run (GP.beginClose (ident 1 ∷ [])))) (pre (atScope Fixtures.q8 k63)) ≡ just (pre (govBase Fixtures.q8 gc0))
      peerEdge9 = refl
      peerEdge10 : V.advance (peerStep (PS.run (GP.requestCancel))) (pre (govBase Fixtures.q8 gc0)) ≡ just (pre (govBase Fixtures.q8 gc1))
      peerEdge10 = refl
      peerEdge11 : V.advance (peerStep (PS.run (GP.deliverCancellation scopeError))) (pre (govBase Fixtures.q8 gc1)) ≡ just (pre (govInterrupted Fixtures.q8 gc2))
      peerEdge11 = refl
      peerEdge12 : V.advance (peerStep (PS.run (GP.bodyUnwound (ident 1)))) (pre (govInterrupted Fixtures.q8 gc2)) ≡ just (pre (govInterrupted Fixtures.q8 gc3))
      peerEdge12 = refl
      peerEdge13 : V.advance (peerStep (PS.run (GP.deregisterCancelled (ident 1)))) (pre (govInterrupted Fixtures.q8 gc3)) ≡ just (pre (govRemoved Fixtures.q8 gc4))
      peerEdge13 = refl
      peerEdge14 : V.advance (peerStep (PS.run (GP.publishAsyncResult (ident 1)))) (pre (govRemoved Fixtures.q8 gc4)) ≡ just (pre (govRemoved Fixtures.q8 gc5))
      peerEdge14 = refl
      peerEdge15 : V.advance (peerStep (PS.run (GP.join))) (pre (govRemoved Fixtures.q8 gc5)) ≡ just (pre (govRemoved Fixtures.q8 gc6))
      peerEdge15 = refl
      peerEdge16 : V.advance (peerStep (PS.run (GP.finishClose))) (pre (govRemoved Fixtures.q8 gc6)) ≡ just (pre (govSettled Fixtures.q8))
      peerEdge16 = refl
      peerEdge17 : V.advance (scoped (Scope.bodyExit Scope.governor)) (pre (govSettled Fixtures.q8)) ≡ just (pre (govSettled Fixtures.q9))
      peerEdge17 = refl
      peerEdge18 : V.advance (scoped (Scope.publishResult Scope.governor)) (pre (govSettled Fixtures.q9)) ≡ just (pre (govSettled Fixtures.q10))
      peerEdge18 = refl
      peerEdge19 : V.advance (scoped (Scope.join)) (pre (govSettled Fixtures.q10)) ≡ just (pre (govSettled Fixtures.q11))
      peerEdge19 = refl
      peerEdge20 : V.advance (scoped (Scope.requestCancel)) (pre (govSettled Fixtures.q11)) ≡ just (pre (govSettled Fixtures.q12))
      peerEdge20 = refl
      peerEdge21 : V.advance (scoped (Scope.deliverCancel)) (pre (govSettled Fixtures.q12)) ≡ just (pre (govSettled Fixtures.q13))
      peerEdge21 = refl
      peerEdge22 : V.advance (scoped (Scope.bodyExit Scope.localRoot)) (pre (govSettled Fixtures.q13)) ≡ just (pre (govSettled Fixtures.q14))
      peerEdge22 = refl
      peerEdge23 : V.advance (scoped (Scope.publishResult Scope.localRoot)) (pre (govSettled Fixtures.q14)) ≡ just (pre (govSettled Fixtures.q15))
      peerEdge23 = refl
      peerEdge24 : V.advance (scoped (Scope.join)) (pre (govSettled Fixtures.q15)) ≡ just (pre (govSettled Fixtures.q16))
      peerEdge24 = refl
      peerEdge25 : V.advance (scoped (Scope.requestCancel)) (pre (govSettled Fixtures.q16)) ≡ just (pre (govSettled Fixtures.q17))
      peerEdge25 = refl
      peerEdge26 : V.advance (scoped (Scope.deliverCancel)) (pre (govSettled Fixtures.q17)) ≡ just (pre (govSettled Fixtures.q18))
      peerEdge26 = refl
      peerEdge27 : V.advance (scoped (Scope.bodyExit Scope.ledger)) (pre (govSettled Fixtures.q18)) ≡ just (pre (govSettled Fixtures.q19))
      peerEdge27 = refl
      peerEdge28 : V.advance (scoped (Scope.publishResult Scope.ledger)) (pre (govSettled Fixtures.q19)) ≡ just (pre (govSettled Fixtures.q20))
      peerEdge28 = refl
      peerEdge29 : V.advance (scoped (Scope.join)) (pre (govSettled Fixtures.q20)) ≡ just (pre (govSettled Fixtures.q21))
      peerEdge29 = refl
      peerEdge30 : V.advance (scoped (Scope.finishClose)) (pre (govSettled Fixtures.q21)) ≡ just (pre (govSettled Fixtures.q22))
      peerEdge30 = refl
      peerEdge31 : V.advance (peerStep (PS.beginMonitorClose (ident 50 ∷ []))) (pre innerDone) ≡ just (pre (monBase mc0))
      peerEdge31 = refl
      peerEdge32 : V.advance (peerStep (PS.requestMonitorCancel)) (pre (monBase mc0)) ≡ just (pre (monBase mc1))
      peerEdge32 = refl
      peerEdge33 : V.advance (peerStep (PS.deliverMonitorCancellation scopeError)) (pre (monBase mc1)) ≡ just (pre (monInterrupted mc2))
      peerEdge33 = refl
      peerEdge34 : V.advance (peerStep (PS.monitorBodyUnwound (ident 50))) (pre (monInterrupted mc2)) ≡ just (pre (monStopped mc3))
      peerEdge34 = refl
      peerEdge35 : V.advance (peerStep (PS.deregisterMonitor (ident 50))) (pre (monStopped mc3)) ≡ just (pre (monStopped mc4))
      peerEdge35 = refl
      peerEdge36 : V.advance (peerStep (PS.publishMonitorResult (ident 50))) (pre (monStopped mc4)) ≡ just (pre (monStopped mc5))
      peerEdge36 = refl
      peerEdge37 : V.advance (peerStep (PS.joinMonitor)) (pre (monStopped mc5)) ≡ just (pre (monStopped mc6))
      peerEdge37 = refl
      peerEdge38 : V.advance (peerStep (PS.finishMonitorClose)) (pre (monStopped mc6)) ≡ just (pre peerDone)
      peerEdge38 = refl
      peerEdge39 : V.advance (V.dispatch (K.serverStep (E.run (S.scope S.returnAction)))) (pre peerDone) ≡ just (returnedCallback)
      peerEdge39 = refl
      peerScopeActions : List V.Event
      peerScopeActions = (scoped (Scope.beginUnwind)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.churn)) ∷ (scoped (Scope.publishResult Scope.churn)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (peerStep (PS.run (GP.beginClose (ident 1 ∷ [])))) ∷ (peerStep (PS.run (GP.requestCancel))) ∷ (peerStep (PS.run (GP.deliverCancellation scopeError))) ∷ (peerStep (PS.run (GP.bodyUnwound (ident 1)))) ∷ (peerStep (PS.run (GP.deregisterCancelled (ident 1)))) ∷ (peerStep (PS.run (GP.publishAsyncResult (ident 1)))) ∷ (peerStep (PS.run (GP.join))) ∷ (peerStep (PS.run (GP.finishClose))) ∷ (scoped (Scope.bodyExit Scope.governor)) ∷ (scoped (Scope.publishResult Scope.governor)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.localRoot)) ∷ (scoped (Scope.publishResult Scope.localRoot)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.ledger)) ∷ (scoped (Scope.publishResult Scope.ledger)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.finishClose)) ∷ (peerStep (PS.beginMonitorClose (ident 50 ∷ []))) ∷ (peerStep (PS.requestMonitorCancel)) ∷ (peerStep (PS.deliverMonitorCancellation scopeError)) ∷ (peerStep (PS.monitorBodyUnwound (ident 50))) ∷ (peerStep (PS.deregisterMonitor (ident 50))) ∷ (peerStep (PS.publishMonitorResult (ident 50))) ∷ (peerStep (PS.joinMonitor)) ∷ (peerStep (PS.finishMonitorClose)) ∷ (V.dispatch (K.serverStep (E.run (S.scope S.returnAction)))) ∷ []
      abstract
        peerScopePath : V.Runs (at legacy k63 tracingFront) peerScopeActions returnedCallback
        peerScopePath = V.more peerEdge1 (V.more peerEdge2 (V.more peerEdge3 (V.more peerEdge4 (V.more peerEdge5 (V.more peerEdge6 (V.more peerEdge7 (V.more peerEdge8 (V.more peerEdge9 (V.more peerEdge10 (V.more peerEdge11 (V.more peerEdge12 (V.more peerEdge13 (V.more peerEdge14 (V.more peerEdge15 (V.more peerEdge16 (V.more peerEdge17 (V.more peerEdge18 (V.more peerEdge19 (V.more peerEdge20 (V.more peerEdge21 (V.more peerEdge22 (V.more peerEdge23 (V.more peerEdge24 (V.more peerEdge25 (V.more peerEdge26 (V.more peerEdge27 (V.more peerEdge28 (V.more peerEdge29 (V.more peerEdge30 (V.more peerEdge31 (V.more peerEdge32 (V.more peerEdge33 (V.more peerEdge34 (V.more peerEdge35 (V.more peerEdge36 (V.more peerEdge37 (V.more peerEdge38 (V.more peerEdge39 (V.stop)))))))))))))))))))))))))))))))))))))))
        initialized-peer-exit : V.Runs initial ((prefixActions ++ tracePrefixActions) ++ peerScopeActions) returnedCallback
        initialized-peer-exit = Facts.append-protocols tracePrefix peerScopePath
      peer-exit-supply : Inv.ProtocolValid returnedCallback
      peer-exit-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-peer-exit

      -- Callback return derives actual nonempty pool/scope certificates. The
      -- abandoned publisher and handler tracer retain their real continuations.
      scopeBeforeReturnActions : List V.Event
      scopeBeforeReturnActions = (scoped (Scope.beginUnwind)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.churn)) ∷ (scoped (Scope.publishResult Scope.churn)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (peerStep (PS.run (GP.beginClose (ident 1 ∷ [])))) ∷ (peerStep (PS.run (GP.requestCancel))) ∷ (peerStep (PS.run (GP.deliverCancellation scopeError))) ∷ (peerStep (PS.run (GP.bodyUnwound (ident 1)))) ∷ (peerStep (PS.run (GP.deregisterCancelled (ident 1)))) ∷ (peerStep (PS.run (GP.publishAsyncResult (ident 1)))) ∷ (peerStep (PS.run (GP.join))) ∷ (peerStep (PS.run (GP.finishClose))) ∷ (scoped (Scope.bodyExit Scope.governor)) ∷ (scoped (Scope.publishResult Scope.governor)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.localRoot)) ∷ (scoped (Scope.publishResult Scope.localRoot)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.requestCancel)) ∷ (scoped (Scope.deliverCancel)) ∷ (scoped (Scope.bodyExit Scope.ledger)) ∷ (scoped (Scope.publishResult Scope.ledger)) ∷ (scoped (Scope.join)) ∷ (scoped (Scope.finishClose)) ∷ (peerStep (PS.beginMonitorClose (ident 50 ∷ []))) ∷ (peerStep (PS.requestMonitorCancel)) ∷ (peerStep (PS.deliverMonitorCancellation scopeError)) ∷ (peerStep (PS.monitorBodyUnwound (ident 50))) ∷ (peerStep (PS.deregisterMonitor (ident 50))) ∷ (peerStep (PS.publishMonitorResult (ident 50))) ∷ (peerStep (PS.joinMonitor)) ∷ (peerStep (PS.finishMonitorClose)) ∷ []
      abstract
        scopeBeforeReturnPath : V.Runs (at legacy k63 tracingFront) scopeBeforeReturnActions (pre peerDone)
        scopeBeforeReturnPath = V.more peerEdge1 (V.more peerEdge2 (V.more peerEdge3 (V.more peerEdge4 (V.more peerEdge5 (V.more peerEdge6 (V.more peerEdge7 (V.more peerEdge8 (V.more peerEdge9 (V.more peerEdge10 (V.more peerEdge11 (V.more peerEdge12 (V.more peerEdge13 (V.more peerEdge14 (V.more peerEdge15 (V.more peerEdge16 (V.more peerEdge17 (V.more peerEdge18 (V.more peerEdge19 (V.more peerEdge20 (V.more peerEdge21 (V.more peerEdge22 (V.more peerEdge23 (V.more peerEdge24 (V.more peerEdge25 (V.more peerEdge26 (V.more peerEdge27 (V.more peerEdge28 (V.more peerEdge29 (V.more peerEdge30 (V.more peerEdge31 (V.more peerEdge32 (V.more peerEdge33 (V.more peerEdge34 (V.more peerEdge35 (V.more peerEdge36 (V.more peerEdge37 (V.more peerEdge38 (V.stop))))))))))))))))))))))))))))))))))))))
        initialized-before-return : V.Runs initial ((prefixActions ++ tracePrefixActions) ++ scopeBeforeReturnActions) (pre peerDone)
        initialized-before-return = Facts.append-protocols tracePrefix scopeBeforeReturnPath
      scope-certificates : BFacts.Certificates (V.base (pre peerDone))
      scope-certificates = Facts.callback-from-protocols initializer initialized-before-return peerEdge39
      import ConnectionManagement.Properties.JobPoolClose as GovCloseProof
      private
        module GovClose = GovCloseProof GP.Body
      governor-terminal : GovClose.Terminal (C.governorPool peerDone) (ident 1)
      governor-terminal = proj₁ scope-certificates (ident 1) (here refl)
      monitor-terminal : BClose.Terminal (C.monitorPool peerDone) (ident 50)
      monitor-terminal = proj₁ (proj₂ scope-certificates) (ident 50) (here refl)

      serverEvent : S.ScopeAction → V.Event
      serverEvent a = V.dispatch (K.serverStep (E.run (S.scope a)))
      exitEvent : E.Action → V.Event
      exitEvent a = V.dispatch (K.serverStep a)
      igReceipt : E.Receipt
      igReceipt = E.receipt E.loopBoundary igError nothing
      caughtIG : E.Exit
      caughtIG = E.caughtExit igReceipt
      dormant flushingDone : Y.Model
      dormant = record legacy { governor = record (Y.governor legacy)
        { continuation = IG.exitFlush; execution = record (IG.execution (Y.governor legacy)) { active = false } } }
      flushingDone = record dormant { governor = record (Y.governor dormant) { continuation = IG.exited } }
      exitRows : List E.Row
      exitRows = (A.key₀ , E.idle) ∷ []
      snapshotIG invokedIG returnedIG finishedIG publishedIG : E.Exit
      snapshotIG = record caughtIG { phase = E.traversing; snapshot = exitRows; remaining = exitRows }
      invokedIG = record snapshotIG { phase = E.invoked }
      returnedIG = record snapshotIG { remaining = []; returned = exitRows }
      finishedIG = record returnedIG { phase = E.bodyDone }
      publishedIG = record finishedIG { result = just (S.async igError) }
      serverEdge1 : V.advance (serverEvent S.publishActionResult) (scene S.actionBodyExited true E.emptyExit legacy peerDone tracingFront) ≡ just (scene S.actionResultAvailable true E.emptyExit legacy peerDone tracingFront)
      serverEdge1 = refl
      serverEdge2 : V.advance (serverEvent S.selectActionWinner) (scene S.actionResultAvailable true E.emptyExit legacy peerDone tracingFront) ≡ just (scene S.closingAccept true E.emptyExit legacy peerDone tracingFront)
      serverEdge2 = refl
      serverEdge3 : V.advance (serverEvent S.requestAcceptCancel) (scene S.closingAccept true E.emptyExit legacy peerDone tracingFront) ≡ just (scene S.acceptCancelRequested true E.emptyExit legacy peerDone tracingFront)
      serverEdge3 = refl
      serverEdge4 : V.advance (serverEvent S.deliverAcceptAtWait) (scene S.acceptCancelRequested true E.emptyExit legacy peerDone tracingFront) ≡ just (scene S.acceptCancelDelivered true E.emptyExit legacy peerDone tracingFront)
      serverEdge4 = refl
      serverEdge5 : V.advance (serverEvent S.closeListener) (scene S.acceptCancelDelivered true E.emptyExit legacy peerDone tracingFront) ≡ just (scene S.acceptBodyExited false E.emptyExit legacy peerDone tracingFront)
      serverEdge5 = refl
      serverEdge6 : V.advance (serverEvent S.publishAcceptResult) (scene S.acceptBodyExited false E.emptyExit legacy peerDone tracingFront) ≡ just (scene S.acceptResultAvailable false E.emptyExit legacy peerDone tracingFront)
      serverEdge6 = refl
      serverEdge7 : V.advance (serverEvent S.joinAccept) (scene S.acceptResultAvailable false E.emptyExit legacy peerDone tracingFront) ≡ just (scene S.acceptJoined false E.emptyExit legacy peerDone tracingFront)
      serverEdge7 = refl
      serverEdge8 : V.advance (serverEvent S.traceStopped) (scene S.acceptJoined false E.emptyExit legacy peerDone tracingFront) ≡ just (scene S.serverStopped false E.emptyExit legacy peerDone tracingFront)
      serverEdge8 = refl
      serverEdge9 : V.advance (serverEvent S.cancelJoinReturnedAction) (scene S.serverStopped false E.emptyExit legacy peerDone tracingFront) ≡ just (scene S.actionJoined false E.emptyExit legacy peerDone tracingFront)
      serverEdge9 = refl
      serverEdge10 : V.advance (serverEvent S.requestIGCancel) (scene S.actionJoined false E.emptyExit legacy peerDone tracingFront) ≡ just (scene S.igCancelRequested false E.emptyExit legacy peerDone tracingFront)
      serverEdge10 = refl
      serverEdge11 : V.advance (exitEvent (E.receive E.loopBoundary igError)) (scene S.igCancelRequested false E.emptyExit legacy peerDone tracingFront) ≡ just (scene S.igCancelDelivered false caughtIG legacy peerDone tracingFront)
      serverEdge11 = refl
      serverEdge12 : V.advance (serverEvent S.deactivateIG) (scene S.igCancelDelivered false caughtIG legacy peerDone tracingFront) ≡ just (scene S.igInactive false caughtIG dormant peerDone tracingFront)
      serverEdge12 = refl
      serverEdge13 : V.advance (serverEvent S.flushIG) (scene S.igInactive false caughtIG dormant peerDone tracingFront) ≡ just (scene S.igFlushed false caughtIG flushingDone peerDone tracingFront)
      serverEdge13 = refl
      serverEdge14 : V.advance (exitEvent E.captureSnapshot) (scene S.igFlushed false caughtIG flushingDone peerDone tracingFront) ≡ just (scene S.igFlushed false snapshotIG flushingDone peerDone tracingFront)
      serverEdge14 = refl
      serverEdge15 : V.advance (exitEvent E.invokeFinal) (scene S.igFlushed false snapshotIG flushingDone peerDone tracingFront) ≡ just (scene S.igFlushed false invokedIG flushingDone peerDone tracingFront)
      serverEdge15 = refl
      serverEdge16 : V.advance (exitEvent E.returnFinal) (scene S.igFlushed false invokedIG flushingDone peerDone tracingFront) ≡ just (scene S.igFlushed false returnedIG flushingDone peerDone tracingFront)
      serverEdge16 = refl
      serverEdge17 : V.advance (exitEvent E.finishFinal) (scene S.igFlushed false returnedIG flushingDone peerDone tracingFront) ≡ just (scene S.igBodyExited false finishedIG flushingDone peerDone tracingFront)
      serverEdge17 = refl
      serverEdge18 : V.advance (serverEvent S.publishIGResult) (scene S.igBodyExited false finishedIG flushingDone peerDone tracingFront) ≡ just (scene S.igResultAvailable false publishedIG flushingDone peerDone tracingFront)
      serverEdge18 = refl
      serverEdge19 : V.advance (serverEvent S.joinIG) (scene S.igResultAvailable false publishedIG flushingDone peerDone tracingFront) ≡ just (scene S.igJoined false publishedIG flushingDone peerDone tracingFront)
      serverEdge19 = refl
      serverEdge20 : V.advance (serverEvent S.beginCM) (scene S.igJoined false publishedIG flushingDone peerDone tracingFront) ≡ just (scene S.closingCM false publishedIG flushingDone peerDone tracingFront)
      serverEdge20 = refl
      serverScopeActions : List V.Event
      serverScopeActions = (serverEvent S.publishActionResult) ∷ (serverEvent S.selectActionWinner) ∷ (serverEvent S.requestAcceptCancel) ∷ (serverEvent S.deliverAcceptAtWait) ∷ (serverEvent S.closeListener) ∷ (serverEvent S.publishAcceptResult) ∷ (serverEvent S.joinAccept) ∷ (serverEvent S.traceStopped) ∷ (serverEvent S.cancelJoinReturnedAction) ∷ (serverEvent S.requestIGCancel) ∷ (exitEvent (E.receive E.loopBoundary igError)) ∷ (serverEvent S.deactivateIG) ∷ (serverEvent S.flushIG) ∷ (exitEvent E.captureSnapshot) ∷ (exitEvent E.invokeFinal) ∷ (exitEvent E.returnFinal) ∷ (exitEvent E.finishFinal) ∷ (serverEvent S.publishIGResult) ∷ (serverEvent S.joinIG) ∷ (serverEvent S.beginCM) ∷ []
      atCMEntry : V.Runtime
      atCMEntry = scene S.closingCM false publishedIG flushingDone peerDone tracingFront
      abstract
        serverScopePath : V.Runs returnedCallback serverScopeActions atCMEntry
        serverScopePath = V.more serverEdge1 (V.more serverEdge2 (V.more serverEdge3 (V.more serverEdge4 (V.more serverEdge5 (V.more serverEdge6 (V.more serverEdge7 (V.more serverEdge8 (V.more serverEdge9 (V.more serverEdge10 (V.more serverEdge11 (V.more serverEdge12 (V.more serverEdge13 (V.more serverEdge14 (V.more serverEdge15 (V.more serverEdge16 (V.more serverEdge17 (V.more serverEdge18 (V.more serverEdge19 (V.more serverEdge20 (V.stop))))))))))))))))))))
        initialized-cm-entry : V.Runs initial (((prefixActions ++ tracePrefixActions) ++ peerScopeActions) ++ serverScopeActions) atCMEntry
        initialized-cm-entry = Facts.append-protocols initialized-peer-exit serverScopePath
      cm-entry-supply : Inv.ProtocolValid atCMEntry
      cm-entry-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-cm-entry

      -- CM shutdown is now reached through the actual initialized lexical
      -- scopes. This setter changes only coordinator metadata, never a stage.
      coordinated : Close.State → V.Runtime → V.Runtime
      coordinated coordinator s = record s { base = V.setStartShutdown coordinator (V.base s) }
      cmCaptured cmRead cmSend cmAcknowledged cmWait : Close.State
      cmCaptured = Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []
      cmRead = Close.shutdownState (Close.sendReady (ident 0) A.child₀) (ident 0 ∷ []) [] []
      cmSend = Close.shutdownState (Close.awaitDelivery (ident 0) A.child₀) (ident 0 ∷ []) [] []
      cmAcknowledged = Close.shutdownState Close.reading (ident 0 ∷ []) [] (A.child₀ ∷ [])
      cmWait = Close.shutdownState Close.awaitResults (ident 0 ∷ []) [] (A.child₀ ∷ [])
      coordinatorEvent : Close.Action → V.Event
      coordinatorEvent a = unwindStep (Unwind.run (N.D.X.run (W.shutdownStep a)))
      faultScene : Unwind.PC → Y.Model → V.Runtime
      faultScene phase m = V.runtime (V.setStartFaults ((A.child₀ , selectedFault (Unwind.async traceError) phase) ∷ [])
        (V.base (scene S.closingCM false publishedIG m peerDone (failedFront (Unwind.async traceError)))))
        (failedFront (Unwind.async traceError))
      cmState1 cmState2 cmState3 cmState4 cmState5 : V.Runtime
      cmState1 = coordinated cmCaptured atCMEntry
      cmState2 = coordinated cmRead atCMEntry
      cmState3 = coordinated cmSend atCMEntry
      cmState4 = coordinated cmAcknowledged (faultScene Unwind.awaitingClose flushingDone)
      cmState5 = coordinated cmWait (faultScene Unwind.awaitingClose flushingDone)
      cmEdge1 : V.advance (coordinatorEvent Close.captureSnapshot) atCMEntry ≡ just cmState1
      cmEdge1 = refl
      cmEdge2 : V.advance (coordinatorEvent Close.readEntry) cmState1 ≡ just cmState2
      cmEdge2 = refl
      cmEdge3 : V.advance (coordinatorEvent Close.requestCancellation) cmState2 ≡ just cmState3
      cmEdge3 = refl
      cmEdge4 : V.advance (V.deliverStartTraceShutdown traceError) cmState3 ≡ just cmState4
      cmEdge4 = refl
      cmEdge5 : V.advance (coordinatorEvent Close.finishTraversal) cmState4 ≡ just cmState5
      cmEdge5 = refl
      cmReceiptActions : List V.Event
      cmReceiptActions = coordinatorEvent Close.captureSnapshot ∷ coordinatorEvent Close.readEntry ∷ coordinatorEvent Close.requestCancellation ∷
        V.deliverStartTraceShutdown traceError ∷ coordinatorEvent Close.finishTraversal ∷ []
      entryActions : List V.Event
      entryActions = ((prefixActions ++ tracePrefixActions) ++ peerScopeActions) ++ serverScopeActions
      abstract
        cmReceiptPath : V.Runs atCMEntry cmReceiptActions cmState5
        cmReceiptPath = V.more cmEdge1 (V.more cmEdge2 (V.more cmEdge3 (V.more cmEdge4 (V.more cmEdge5 V.stop))))
        initialized-receipt-scoped : V.Runs initial (entryActions ++ cmReceiptActions) cmState5
        initialized-receipt-scoped = Facts.append-protocols initialized-cm-entry cmReceiptPath
      scoped-receipt-supply : Inv.ProtocolValid cmState5
      scoped-receipt-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-receipt-scoped
      physicalAt : Unwind.PC → Pool.State → V.Runtime
      physicalAt phase p = coordinated cmWait (faultScene phase (withPool p flushingDone))
      physicalEdge1 : V.advance (unwindStep (Unwind.beginClose A.child₀ order)) (physicalAt Unwind.awaitingClose q0) ≡ just (physicalAt Unwind.closing q1)
      physicalEdge1 = refl
      physicalEdge2 : V.advance (unwindStep (Unwind.requestCancel A.child₀)) (physicalAt Unwind.closing q1) ≡ just (physicalAt Unwind.closing q2)
      physicalEdge2 = refl
      physicalEdge3 : V.advance (unwindStep (Unwind.deliverCancel A.child₀)) (physicalAt Unwind.closing q2) ≡ just (physicalAt Unwind.closing q3)
      physicalEdge3 = refl
      physicalEdge4 : V.advance (shutdownStep (N.G.finishChildUnwind (ident 1))) (physicalAt Unwind.closing q3) ≡ just (physicalAt Unwind.closing q4)
      physicalEdge4 = refl
      physicalEdge5 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.demuxer)) (physicalAt Unwind.closing q4) ≡ just (physicalAt Unwind.closing q5)
      physicalEdge5 = refl
      physicalEdge6 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer)) (physicalAt Unwind.closing q5) ≡ just (physicalAt Unwind.closing q6)
      physicalEdge6 = refl
      physicalEdge7 : V.advance (unwindStep (Unwind.join A.child₀)) (physicalAt Unwind.closing q6) ≡ just (physicalAt Unwind.closing q7)
      physicalEdge7 = refl
      physicalEdge8 : V.advance (unwindStep (Unwind.requestCancel A.child₀)) (physicalAt Unwind.closing q7) ≡ just (physicalAt Unwind.closing q8)
      physicalEdge8 = refl
      physicalEdge9 : V.advance (unwindStep (Unwind.deliverCancel A.child₀)) (physicalAt Unwind.closing q8) ≡ just (physicalAt Unwind.closing q9)
      physicalEdge9 = refl
      physicalEdge10 : V.advance (shutdownStep (N.G.finishChildUnwind (ident 0))) (physicalAt Unwind.closing q9) ≡ just (physicalAt Unwind.closing q10)
      physicalEdge10 = refl
      physicalEdge11 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.muxer)) (physicalAt Unwind.closing q10) ≡ just (physicalAt Unwind.closing q11)
      physicalEdge11 = refl
      physicalEdge12 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.muxer)) (physicalAt Unwind.closing q11) ≡ just (physicalAt Unwind.closing q12)
      physicalEdge12 = refl
      physicalEdge13 : V.advance (unwindStep (Unwind.join A.child₀)) (physicalAt Unwind.closing q12) ≡ just (physicalAt Unwind.closing q13)
      physicalEdge13 = refl
      physicalEdge14 : V.advance (unwindStep (Unwind.finishClose A.child₀)) (physicalAt Unwind.closing q13) ≡ just (physicalAt Unwind.poolClosed q14)
      physicalEdge14 = refl

      physicalActions : List V.Event
      physicalActions = (unwindStep (Unwind.beginClose A.child₀ order)) ∷ (unwindStep (Unwind.requestCancel A.child₀)) ∷ (unwindStep (Unwind.deliverCancel A.child₀)) ∷ (shutdownStep (N.G.finishChildUnwind (ident 1))) ∷ (physicalStep (P.deregisterInfra A.child₀ Types.demuxer)) ∷ (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer)) ∷ (unwindStep (Unwind.join A.child₀)) ∷ (unwindStep (Unwind.requestCancel A.child₀)) ∷ (unwindStep (Unwind.deliverCancel A.child₀)) ∷ (shutdownStep (N.G.finishChildUnwind (ident 0))) ∷ (physicalStep (P.deregisterInfra A.child₀ Types.muxer)) ∷ (physicalStep (P.asyncInfraResult A.child₀ Types.muxer)) ∷ (unwindStep (Unwind.join A.child₀)) ∷ (unwindStep (Unwind.finishClose A.child₀)) ∷ []
      abstract
        physicalPath : V.Runs cmState5 physicalActions (physicalAt Unwind.poolClosed q14)
        physicalPath = V.more physicalEdge1 (V.more physicalEdge2 (V.more physicalEdge3 (V.more physicalEdge4 (V.more physicalEdge5 (V.more physicalEdge6 (V.more physicalEdge7 (V.more physicalEdge8 (V.more physicalEdge9 (V.more physicalEdge10 (V.more physicalEdge11 (V.more physicalEdge12 (V.more physicalEdge13 (V.more physicalEdge14 (V.stop))))))))))))))
        initialized-physical-close : V.Runs initial ((entryActions ++ cmReceiptActions) ++ physicalActions)
          (physicalAt Unwind.poolClosed q14)
        initialized-physical-close = Facts.append-protocols initialized-receipt-scoped physicalPath

      -- With IG inactive, Dead returns through the false-active branch. It
      -- neither publishes MuxFinished nor clears the old responder counters.
      inactiveFailed inactiveDead inactiveSampled : Y.Model
      inactiveFailed = Y.sourceMux failedMux [] (withPool q14 flushingDone)
      inactiveDead = Y.sourceMux deadMux [] (withPool q14 flushingDone)
      inactiveSampled = Y.sourceMux (record failedMux { callback = Mux.commitTrace false Mux.muxStopped }) []
        (withPool q14 flushingDone)
      scopedStatus scopedDead scopedSampled scopedCommitted scopedReady : V.Runtime
      scopedStatus = coordinated cmWait (faultScene Unwind.asyncStatus inactiveFailed)
      scopedDead = coordinated cmWait (faultScene Unwind.asyncDead inactiveDead)
      scopedSampled = coordinated cmWait (faultScene Unwind.asyncDead inactiveSampled)
      scopedCommitted = coordinated cmWait (faultScene Unwind.asyncDead inactiveFailed)
      scopedReady = coordinated cmWait (faultScene Unwind.readyBuffer inactiveFailed)
      catchEdge1 : V.advance (unwindStep (Unwind.writeAsyncFailure A.child₀)) (physicalAt Unwind.poolClosed q14) ≡ just scopedStatus
      catchEdge1 = refl
      catchEdge2 : V.advance (unwindStep (Unwind.beginDead A.child₀)) scopedStatus ≡ just scopedDead
      catchEdge2 = refl
      catchEdge3 : V.advance (unwindStep (Unwind.sampleDead A.child₀)) scopedDead ≡ just scopedSampled
      catchEdge3 = refl
      catchEdge4 : V.advance (unwindStep (Unwind.commitDead A.child₀)) scopedSampled ≡ just scopedCommitted
      catchEdge4 = refl
      catchEdge5 : V.advance (unwindStep (Unwind.finishDead A.child₀)) scopedCommitted ≡ just scopedReady
      catchEdge5 = refl
      scopedCatchActions : List V.Event
      scopedCatchActions = unwindStep (Unwind.writeAsyncFailure A.child₀) ∷ unwindStep (Unwind.beginDead A.child₀) ∷
        unwindStep (Unwind.sampleDead A.child₀) ∷ unwindStep (Unwind.commitDead A.child₀) ∷ unwindStep (Unwind.finishDead A.child₀) ∷ []
      abstract
        scopedCatchPath : V.Runs (physicalAt Unwind.poolClosed q14) scopedCatchActions scopedReady
        scopedCatchPath = V.more catchEdge1 (V.more catchEdge2 (V.more catchEdge3 (V.more catchEdge4 (V.more catchEdge5 V.stop))))
        initialized-scoped-catch : V.Runs initial (((entryActions ++ cmReceiptActions) ++ physicalActions) ++ scopedCatchActions) scopedReady
        initialized-scoped-catch = Facts.append-protocols initialized-physical-close scopedCatchPath
      scoped-final-supply : Inv.ProtocolValid scopedReady
      scoped-final-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-scoped-catch

      tracer-survives-peer-exit : V.cursor A.child₀ (V.front returnedCallback) ≡ V.tracingC rid
      tracer-survives-peer-exit = refl
      tracer-survives-ig-exit : V.cursor A.child₀ (V.front atCMEntry) ≡ V.tracingC rid
      tracer-survives-ig-exit = refl
      publication-never-completed : lookup (ident 1) (C.SubContext.jobs (C.subsystem peerDone)) ≡ just abandonedJob
      publication-never-completed = refl
      cancelled-publisher-cannot-resume : V.advance (ps L.a64) (pre peerDone) ≡ nothing
      cancelled-publisher-cannot-resume = refl
      early-callback-refused : V.advance (serverEvent S.returnAction) (pre innerDone) ≡ nothing
      early-callback-refused = refl
      premature-cm-refused : V.advance (coordinatorEvent Close.captureSnapshot) returnedCallback ≡ nothing
      premature-cm-refused = refl
      cm-entry-ig-inactive : IG.active (IG.execution (Machine.inboundGovernor (O.core (V.sourceOf atCMEntry)))) ≡ false
      cm-entry-ig-inactive = refl
      actual-nonempty-ig-snapshot : E.snapshot (E.exit (K.server (V.base atCMEntry))) ≡ exitRows
      actual-nonempty-ig-snapshot = refl
      receipt-is-not-pool-close : Pool.phase (P.poolAt A.child₀ (V.physical (V.base cmState4))) ≡ Pool.openPool
      receipt-is-not-pool-close = refl
      joined-physical-children : Pool.joined (P.poolAt A.child₀ (V.physical (V.base scopedReady))) ≡ order
      joined-physical-children = refl
      no-invented-initiator : lookup jid (P.jobs (V.physical (V.base scopedReady))) ≡ nothing
      no-invented-initiator = refl
      old-cell-still-empty : lookup rid (V.calls (V.front scopedReady)) ≡ just requested
      old-cell-still-empty = refl
      inactive-dead-has-no-ig-notification : Shared.inboundInfo (Machine.world (O.core (V.sourceOf scopedReady))) ≡ []
      inactive-dead-has-no-ig-notification = refl
      inactive-dead-retains-counters : P.muxAt (ident 0) (V.physical (V.base scopedReady)) ≡ just failedMux
      inactive-dead-retains-counters = refl
      completion-observes-real-shutdown : V.observe rid scopedReady ≡ just (V.shutdownResult (Mux.failed traceError))
      completion-observes-real-shutdown = refl
      no-psa-poll-after-exit : V.advance (V.pollResults (ident 0) (ident 50)) scopedReady ≡ nothing
      no-psa-poll-after-exit = refl
      pending-handler-result : W.resultReady A.child₀ (Unwind.base (N.raw (V.publication (V.base scopedReady)))) ≡ false
      pending-handler-result = refl
      coordinator-still-waits : V.advance (coordinatorEvent Close.finishClose) scopedReady ≡ nothing
      coordinator-still-waits = refl
      no-late-normal-return : V.advance (V.returnStartTrace A.child₀) scopedReady ≡ nothing
      no-late-normal-return = refl

      -- A real provider return resumes the captured handler, whose finalizer
      -- must finish before its Async result can release CM's collective wait.
      module Completion where
        import ConnectionManagement.Rules.Cleanup as Cleanup
        import ConnectionManagement.Properties.MuxHandlerExit as HandlerProof
        private
          module HandlerFacts = HandlerProof I.bearerClosed
        finalWorld0 finalWorld1 finalWorld2 finalWorld3 finalWorld4 finalWorld5 finalWorld6 : Shared.State
        finalWorld0 = Y.world inactiveFailed
        cleanupLease : Shared.Lease
        cleanupLease = Shared.lease A.child₀ F.binding
        finalWorld1 = record finalWorld0 { cleanups = put A.child₀ Shared.cleanupAcquire (Shared.cleanups finalWorld0) }
        finalWorld2 = record finalWorld1
          { cm = record (Shared.cm finalWorld1) { mapCell = Shared.taken A.child₀ }
          ; cleanups = put A.child₀ (Shared.cleanupSelect cleanupLease) (Shared.cleanups finalWorld1) }
        finalWorld3 = record finalWorld2
          { cm = record (Shared.cm finalWorld2)
            { entries = put (ident 0) (Shared.terminated nothing) (Shared.entries (Shared.cm finalWorld2)) }
          ; cleanups = put A.child₀ (Shared.cleanupClose cleanupLease [] Shared.countImmediately) (Shared.cleanups finalWorld2) }
        finalWorld4 = record finalWorld3
          { sockets = put (Shared.handlerSocket I.captured) Shared.closed (Shared.sockets finalWorld3)
          ; cleanups = put A.child₀ (Shared.cleanupPublish cleanupLease [] Shared.countImmediately) (Shared.cleanups finalWorld3) }
        finalWorld5 = record finalWorld4
          { cm = record (Shared.cm finalWorld4) { mapCell = Shared.full [] }
          ; cleanups = put A.child₀ (Shared.cleanupCount Shared.cleanupNormal) (Shared.cleanups finalWorld4) }
        finalWorld6 = record finalWorld5
          { cleanups = put A.child₀ (Shared.cleanupDone Shared.cleanupNormal) (Shared.cleanups finalWorld5) }

        -- Expected snapshots replace only the captured handler's exit row.
        -- Every source/phase change is justified by a separate step below.
        withHandlerExit : W.Phase → V.Runtime → V.Runtime
        withHandlerExit pc original = record original { base = record b
          { server = record (K.server b) { base = record (E.base (K.server b))
            { base = record n { base = record c { base = record d { base = record r
              { base = record x { exits = (A.child₀ , W.exitFrame I.captured pc nothing) ∷ [] } } } } } } } } }
          where
          b = V.base original
          n = V.publication b
          c = N.base n
          d = N.C.base c
          r = N.D.base d
          x = Unwind.base r
        handlerSnapshot : W.Phase → Shared.State → V.Runtime
        handlerSnapshot pc world = withHandlerExit pc (coordinated cmWait
          (faultScene Unwind.handedOff (record inactiveFailed { world = world })))
        handlerEvent : W.Action → V.Event
        handlerEvent a = unwindStep (Unwind.run (N.D.X.run a))
        h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 : V.Runtime
        h1 = handlerSnapshot (W.bufferScope (N.G.asyncExit traceError)) finalWorld0
        h2 = handlerSnapshot (W.bodyExited (W.asyncException traceError)) finalWorld0
        h3 = handlerSnapshot (W.finalizing (W.asyncException traceError)) finalWorld1
        h4 = handlerSnapshot (W.finalizing (W.asyncException traceError)) finalWorld2
        h5 = handlerSnapshot (W.finalizing (W.asyncException traceError)) finalWorld3
        h6 = handlerSnapshot (W.finalizing (W.asyncException traceError)) finalWorld4
        h7 = handlerSnapshot (W.finalizing (W.asyncException traceError)) finalWorld5
        h8 = handlerSnapshot (W.finalizing (W.asyncException traceError)) finalWorld6
        h9 = handlerSnapshot (W.cleanupComplete (W.asyncException traceError) Shared.cleanupNormal) finalWorld6
        h10 = handlerSnapshot (W.resultAvailable (W.asyncException traceError) Shared.cleanupNormal) finalWorld6
        cmFinished : V.Runtime
        cmFinished = coordinated (Close.shutdownState Close.closed (ident 0 ∷ []) [] (A.child₀ ∷ [])) h10
        serverFinished : V.Runtime
        serverFinished = record cmFinished { base = record (V.base cmFinished)
          { server = record (K.server (V.base cmFinished))
            { base = record (E.base (K.server (V.base cmFinished))) { stage = S.serverReturned } } } }
        finishEdge1 : V.advance (unwindStep (Unwind.handoff A.child₀)) scopedReady ≡ just h1
        finishEdge1 = refl
        finishEdge2 : V.advance (handlerEvent (W.observeBufferReturn A.child₀)) h1 ≡ just h2
        finishEdge2 = refl
        finishEdge3 : V.advance (handlerEvent (W.enterFinalizer A.child₀)) h2 ≡ just h3
        finishEdge3 = refl
        finishEdge4 : V.advance (handlerEvent (W.cleanup A.child₀ Cleanup.takeCleanupMap)) h3 ≡ just h4
        finishEdge4 = refl
        finishEdge5 : V.advance (handlerEvent (W.cleanup A.child₀ Cleanup.selectCleanupEntry)) h4 ≡ just h5
        finishEdge5 = refl
        finishEdge6 : V.advance (handlerEvent (W.cleanup A.child₀ Cleanup.closeHandlerSocket)) h5 ≡ just h6
        finishEdge6 = refl
        finishEdge7 : V.advance (handlerEvent (W.cleanup A.child₀ Cleanup.publishCleanupMap)) h6 ≡ just h7
        finishEdge7 = refl
        finishEdge8 : V.advance (handlerEvent (W.cleanup A.child₀ Cleanup.readCleanupCounters)) h7 ≡ just h8
        finishEdge8 = refl
        finishEdge9 : V.advance (handlerEvent (W.finishCleanup A.child₀)) h8 ≡ just h9
        finishEdge9 = refl
        finishEdge10 : V.advance (handlerEvent (W.publishAsyncResult A.child₀)) h9 ≡ just h10
        finishEdge10 = refl
        finishEdge11 : V.advance (coordinatorEvent Close.finishClose) h10 ≡ just cmFinished
        finishEdge11 = refl
        finishEdge12 : V.advance (serverEvent S.finishServer) cmFinished ≡ just serverFinished
        finishEdge12 = refl
        finishActions : List V.Event
        finishActions = (unwindStep (Unwind.handoff A.child₀)) ∷ (handlerEvent (W.observeBufferReturn A.child₀)) ∷ (handlerEvent (W.enterFinalizer A.child₀)) ∷ (handlerEvent (W.cleanup A.child₀ Cleanup.takeCleanupMap)) ∷ (handlerEvent (W.cleanup A.child₀ Cleanup.selectCleanupEntry)) ∷ (handlerEvent (W.cleanup A.child₀ Cleanup.closeHandlerSocket)) ∷ (handlerEvent (W.cleanup A.child₀ Cleanup.publishCleanupMap)) ∷ (handlerEvent (W.cleanup A.child₀ Cleanup.readCleanupCounters)) ∷ (handlerEvent (W.finishCleanup A.child₀)) ∷ (handlerEvent (W.publishAsyncResult A.child₀)) ∷ (coordinatorEvent Close.finishClose) ∷ (serverEvent S.finishServer) ∷ []
        allFinishedActions : List V.Event
        allFinishedActions = (((entryActions ++ cmReceiptActions) ++ physicalActions) ++ scopedCatchActions) ++ finishActions
        abstract
          finishPath : V.Runs scopedReady finishActions serverFinished
          finishPath = V.more finishEdge1 (V.more finishEdge2 (V.more finishEdge3 (V.more finishEdge4 (V.more finishEdge5 (V.more finishEdge6 (V.more finishEdge7 (V.more finishEdge8 (V.more finishEdge9 (V.more finishEdge10 (V.more finishEdge11 (V.more finishEdge12 (V.stop))))))))))))
          initialized-server-finish : V.Runs initial allFinishedActions serverFinished
          initialized-server-finish = Facts.append-protocols initialized-scoped-catch finishPath
        server-finish-supply : Inv.ProtocolValid serverFinished
        server-finish-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-server-finish

        -- This is the exact physical result table consumed by CM, rather than
        -- an inference from pool closure, cleanupDone or registry absence.
        physical-final-wait : HandlerFacts.PhysicalWait
          (Unwind.base (N.raw (V.publication (V.base h10))))
          (Unwind.base (N.raw (V.publication (V.base cmFinished))))
        physical-final-wait = HandlerFacts.physical-wait-observation
          (Unwind.base (N.raw (V.publication (V.base h10)))) refl

        no-result-at-body-exit : W.resultReady A.child₀ (Unwind.base (N.raw (V.publication (V.base h2)))) ≡ false
        no-result-at-body-exit = refl
        no-result-at-cleanup-end : W.resultReady A.child₀ (Unwind.base (N.raw (V.publication (V.base h9)))) ≡ false
        no-result-at-cleanup-end = refl
        no-cm-close-before-result : V.advance (coordinatorEvent Close.finishClose) h9 ≡ nothing
        no-cm-close-before-result = refl
        no-early-handler-result : V.advance (handlerEvent (W.publishAsyncResult A.child₀)) h8 ≡ nothing
        no-early-handler-result = refl
        no-time-wait-in-this-branch : V.advance (handlerEvent (W.cleanup A.child₀ Cleanup.timeWaitElapsed)) h7 ≡ nothing
        no-time-wait-in-this-branch = refl
        actual-handler-outcome : W.resultOf A.child₀ (Unwind.base (N.raw (V.publication (V.base h10)))) ≡
          just (W.asyncException traceError)
        actual-handler-outcome = refl
        actual-handler-result : W.resultReady A.child₀ (Unwind.base (N.raw (V.publication (V.base cmFinished)))) ≡ true
        actual-handler-result = refl
        actual-cm-closed : Close.phase (W.shutdown (Unwind.base (N.raw (V.publication (V.base serverFinished))))) ≡ Close.closed
        actual-cm-closed = refl
        actual-server-return : S.stage (E.base (K.server (V.base serverFinished))) ≡ S.serverReturned
        actual-server-return = refl
        captured-entry-retained : lookup (ident 0) (Shared.entries (Shared.cm (Machine.world (O.core (V.sourceOf serverFinished))))) ≡
          just (Shared.terminated nothing)
        captured-entry-retained = refl
        actual-map-purged : Shared.mapCell (Shared.cm (Machine.world (O.core (V.sourceOf serverFinished)))) ≡ Shared.full []
        actual-map-purged = refl
        captured-socket-closed : lookup (Shared.handlerSocket I.captured) (Shared.sockets (Machine.world (O.core (V.sourceOf serverFinished)))) ≡ just Shared.closed
        captured-socket-closed = refl
        empty-protocol-cell-retained : lookup rid (V.calls (V.front serverFinished)) ≡ just requested
        empty-protocol-cell-retained = refl
        no-initiator-at-server-return : lookup jid (P.jobs (V.physical (V.base serverFinished))) ≡ nothing
        no-initiator-at-server-return = refl
        no-late-tracer-return : V.advance (V.returnStartTrace A.child₀) serverFinished ≡ nothing
        no-late-tracer-return = refl
        no-peer-publication-after-return : V.advance (ps L.a64) serverFinished ≡ nothing
        no-peer-publication-after-return = refl

        raw-worker-unjoined : lookup A.w₁ (S.workers (E.base (K.server (V.base serverFinished)))) ≡
          just (S.rawWorker F.r₁ S.calling 0)
        raw-worker-unjoined = refl
        raw-workers-not-all-finished : S.allResults (S.workers (E.base (K.server (V.base serverFinished)))) ≡ false
        raw-workers-not-all-finished = refl
        open import Data.Empty using (⊥)
        false-not-true : false ≡ true → ⊥
        false-not-true ()
        no-universal-raw-worker-completion :
          (∀ {t} (as : List V.Event) → V.Runs initial as t →
            S.stage (E.base (K.server (V.base t))) ≡ S.serverReturned →
            S.allResults (S.workers (E.base (K.server (V.base t)))) ≡ true) → ⊥
        no-universal-raw-worker-completion claim =
          false-not-true (claim allFinishedActions initialized-server-finish actual-server-return)

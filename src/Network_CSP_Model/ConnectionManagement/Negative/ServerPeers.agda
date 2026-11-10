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
    ((remote A.key₁ , G.known 0 0 nothing false false) ∷ []) [] [] [] [] [] [] [] []
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


  -- SI4 increment 2: asynchronous cancellation of the thread running
  -- Server.with. At step 55 the peer scopes have finished but the PSA monitor
  -- pool is still open. The Server is interrupted there: the accept loop closes
  -- and the Server stops while the peer side is still live; only after the
  -- monitor pool closes is the action thread joined.
  open import Data.List using (take; _++_)
  open import Data.Bool using (Bool)
  live : C.Context
  live = F.atScope F.q22 F.kclosed
  staged : S.Stage → Bool → C.Context → K.State
  staged st lo k = K.combined (record (F.serverAt F.finalSource)
    { base = record (E.base (F.serverAt F.finalSource)) { stage = st; listenerOpen = lo } }) k
  interrupt1 : K.step (K.serverStep (E.run (S.scope S.interruptServer))) (F.at F.finalSource live) ≡ just (staged S.closingAccept true live)
  interrupt1 = refl
  interrupt2 : K.step (K.serverStep (E.run (S.scope S.requestAcceptCancel))) (staged S.closingAccept true live) ≡ just (staged S.acceptCancelRequested true live)
  interrupt2 = refl
  interrupt3 : K.step (K.serverStep (E.run (S.scope S.deliverAcceptAtWait))) (staged S.acceptCancelRequested true live) ≡ just (staged S.acceptCancelDelivered true live)
  interrupt3 = refl
  interrupt4 : K.step (K.serverStep (E.run (S.scope S.closeListener))) (staged S.acceptCancelDelivered true live) ≡ just (staged S.acceptBodyExited false live)
  interrupt4 = refl
  interrupt5 : K.step (K.serverStep (E.run (S.scope S.publishAcceptResult))) (staged S.acceptBodyExited false live) ≡ just (staged S.acceptResultAvailable false live)
  interrupt5 = refl
  interrupt6 : K.step (K.serverStep (E.run (S.scope S.joinAccept))) (staged S.acceptResultAvailable false live) ≡ just (staged S.acceptJoined false live)
  interrupt6 = refl
  interrupt7 : K.step (K.serverStep (E.run (S.scope S.traceStopped))) (staged S.acceptJoined false live) ≡ just (staged S.serverStopped false live)
  interrupt7 = refl
  interrupt8 : K.step (K.peerStep (PS.beginMonitorClose [])) (staged S.serverStopped false live) ≡ just (staged S.serverStopped false F.kmonitor)
  interrupt8 = refl
  interrupt9 : K.step (K.peerStep PS.finishMonitorClose) (staged S.serverStopped false F.kmonitor) ≡ just (staged S.serverStopped false F.kdone)
  interrupt9 = refl
  interrupt10 : K.step (K.serverStep (E.run (S.scope S.cancelJoinReturnedAction))) (staged S.serverStopped false F.kdone) ≡ just (staged S.actionJoined false F.kdone)
  interrupt10 = refl
  interruptActions : List K.Action
  interruptActions =
    (K.serverStep (E.run (S.scope S.interruptServer))) ∷ (K.serverStep (E.run (S.scope S.requestAcceptCancel))) ∷ (K.serverStep (E.run (S.scope S.deliverAcceptAtWait))) ∷ (K.serverStep (E.run (S.scope S.closeListener))) ∷ (K.serverStep (E.run (S.scope S.publishAcceptResult))) ∷ (K.serverStep (E.run (S.scope S.joinAccept))) ∷ (K.serverStep (E.run (S.scope S.traceStopped))) ∷ (K.peerStep (PS.beginMonitorClose [])) ∷ (K.peerStep PS.finishMonitorClose) ∷ (K.serverStep (E.run (S.scope S.cancelJoinReturnedAction))) ∷ []
  abstract
    initialized-interrupt : K.Executes F.start (take 55 actions ++ interruptActions) (staged S.actionJoined false F.kdone)
    initialized-interrupt = (K.next step1 (K.next step2 (K.next step3 (K.next step4 (K.next step5 (K.next step6 (K.next step7 (K.next step8 (K.next step9 (K.next step10 (K.next step11 (K.next step12 (K.next step13 (K.next step14 (K.next step15 (K.next step16 (K.next step17 (K.next step18 (K.next step19 (K.next step20 (K.next step21 (K.next step22 (K.next step23 (K.next step24 (K.next step25 (K.next step26 (K.next step27 (K.next step28 (K.next step29 (K.next step30 (K.next step31 (K.next step32 (K.next step33 (K.next step34 (K.next step35 (K.next step36 (K.next step37 (K.next step38 (K.next step39 (K.next step40 (K.next step41 (K.next step42 (K.next step43 (K.next step44 (K.next step45 (K.next step46 (K.next step47 (K.next step48 (K.next step49 (K.next step50 (K.next step51 (K.next step52 (K.next step53 (K.next step54 (K.next step55 (K.next interrupt1 (K.next interrupt2 (K.next interrupt3 (K.next interrupt4 (K.next interrupt5 (K.next interrupt6 (K.next interrupt7 (K.next interrupt8 (K.next interrupt9 (K.next interrupt10 K.done)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  interrupt-supply : Inv.Valid (staged S.actionJoined false F.kdone)
  interrupt-supply = Inv.from-initial-valid initializer (All.[] , All.[]) initialized-interrupt
  -- Controls: the action is joined only after the peer side closes, it cannot
  -- return once the Server has been interrupted, the interruption happens once,
  -- and the peer side stays open exactly until it closes.
  no-join-before-peer-close : K.step (K.serverStep (E.run (S.scope S.cancelJoinReturnedAction))) (staged S.serverStopped false live) ≡ nothing
  no-join-before-peer-close = refl
  no-return-after-interrupt : K.step (K.serverStep (E.run (S.scope S.returnAction))) (staged S.closingAccept true live) ≡ nothing
  no-return-after-interrupt = refl
  no-second-interrupt : K.step (K.serverStep (E.run (S.scope S.interruptServer))) (staged S.closingAccept true live) ≡ nothing
  no-second-interrupt = refl
  peer-live-after-stop : K.peerOpen (staged S.serverStopped false live) ≡ true
  peer-live-after-stop = refl
  peer-shut-after-close : K.peerOpen (staged S.serverStopped false F.kdone) ≡ false
  peer-shut-after-close = refl

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
    ; knownPeers = map (λ { (peer , info) → peer , record info { clearFailuresAt = shiftDeadline (G.clearFailuresAt info) } }) (G.knownPeers g)
    ; activeSince = map (λ { (peer , time) → peer , time + 10 }) (G.activeSince g) }
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
  -- After its actual child entry the initiator owns one empty source wanton;
  -- later snapshots retain it. The pre-entry born state has none.
  enteredLegacy : Y.Model
  enteredLegacy = record legacy { governor = IG.setMux (ident 0) (Y.withWanton jid Mux.initiatorJob Y.m1) (Y.governor reused) }
  withPhysicalOn : Y.Model → Types.BodyPhase → Pool.State → Y.Model
  withPhysicalOn base phase pool = record base
    { startup = T.startupState (T.monitoring (ident 0) (ident 1)) pool
    ; jobs = (jid , physicalJob phase) ∷ [] }
  withPhysical : Types.BodyPhase → Pool.State → Y.Model
  withPhysical = withPhysicalOn enteredLegacy
  born entered waiting localClean registered : Y.Model
  born = withPhysicalOn legacy Types.executing bornPool
  entered = withPhysical Types.executing bornPool
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
  run7a : V.advance (physicalStep (P.enterProtocolBody jid)) (at born k63 bornFront) ≡ just (at entered k63 bornFront)
  run7a = refl
  run8 : V.advance (physicalStep (P.protocolReturned jid)) (at entered k63 bornFront) ≡ just (at waiting k63 bornFront)
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
  protocolActions = (V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ (V.invokeStartTrace A.child₀) ∷ (V.returnStartTrace A.child₀) ∷ (V.forkStart A.child₀ jid) ∷ (physicalStep (P.enterProtocolBody jid)) ∷ (physicalStep (P.protocolReturned jid)) ∷ (V.commitClean jid) ∷ (V.registerStart jid) ∷ (ps L.a64) ∷ (ps (Sub.jobStep (ident 1) (J.finishHotAt 12))) ∷ (ps L.a66) ∷ (ps L.a67) ∷ (peerStep (PS.run (GP.publishAsyncResult (ident 1)))) ∷ (physicalStep (P.returnProtocol jid)) ∷ (physicalStep (P.publishProtocol jid)) ∷ (physicalStep (P.deregisterProtocol jid)) ∷ (physicalStep (P.asyncProtocolResult jid)) ∷ (monitorStep (N.M.consume A.child₀)) ∷ (monitorStep (N.M.handleSelected A.child₀)) ∷ (deltaStep (N.D.beginInitiatorTrace A.child₀)) ∷ (deltaStep (N.D.observeInitiatorReturn A.child₀)) ∷ (deltaStep (N.D.beginDeltaQ A.child₀)) ∷ (deltaStep (N.D.observeReturn A.child₀)) ∷ []
  abstract
    protocol-path : V.Runs (at reused k61 V.empty) protocolActions (at monitorDone kActivationDone freeFront)
    protocol-path = V.more run1 (V.more run2 (V.more run3 (V.more run4 (V.more run5 (V.more run6 (V.more run7 (V.more run7a (V.more run8 (V.more run9 (V.more run10 (V.more run11 (V.more run12 (V.more run13 (V.more run14 (V.more run15 (V.more run16 (V.more run17 (V.more run18 (V.more run19 (V.more run20 (V.more run21 (V.more run22 (V.more run23 (V.more run24 (V.more run25 (V.stop))))))))))))))))))))))))))
    selected-path : V.Runs (at reused k61 V.empty) ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ []) (at legacy k63 selectedFront)
    selected-path = V.more run1 (V.more run2 (V.more run3 (V.more run4 (V.stop))))
    before-select-path : V.Runs (at reused k61 V.empty) ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ []) (at legacy k63 zeroFront)
    before-select-path = V.more run1 (V.more run2 (V.more run3 (V.stop)))
    waiting-path : V.Runs (at reused k61 V.empty) ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ (V.invokeStartTrace A.child₀) ∷ (V.returnStartTrace A.child₀) ∷ (V.forkStart A.child₀ jid) ∷ (physicalStep (P.enterProtocolBody jid)) ∷ (physicalStep (P.protocolReturned jid)) ∷ []) (at waiting k63 bornFront)
    waiting-path = V.more run1 (V.more run2 (V.more run3 (V.more run4 (V.more run5 (V.more run6 (V.more run7 (V.more run7a (V.more run8 (V.stop)))))))))
    clean-path : V.Runs (at reused k61 V.empty) ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ (V.invokeStartTrace A.child₀) ∷ (V.returnStartTrace A.child₀) ∷ (V.forkStart A.child₀ jid) ∷ (physicalStep (P.enterProtocolBody jid)) ∷ (physicalStep (P.protocolReturned jid)) ∷ (V.commitClean jid) ∷ []) (at localClean kc63 cleanFront)
    clean-path = V.more run1 (V.more run2 (V.more run3 (V.more run4 (V.more run5 (V.more run6 (V.more run7 (V.more run7a (V.more run8 (V.more run9 (V.stop))))))))))
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
  -- Child entry adds the job's empty initiator wanton to the actual mux snapshot.
  enterIn : JobId → Y.Model → Y.Model
  enterIn j m = record m { governor = IG.setMux (ident 0)
    (Y.withWanton j Mux.initiatorJob (Data.Maybe.fromMaybe Y.m1 (lookup (ident 0) (IG.Engine.muxes (IG.execution (Y.governor m))))))
    (Y.governor m) }
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
    initialized-error : V.Runs initial ((prefixActions ++ ((V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ (V.invokeStartTrace A.child₀) ∷ (V.returnStartTrace A.child₀) ∷ (V.forkStart A.child₀ jid) ∷ (physicalStep (P.enterProtocolBody jid)) ∷ (physicalStep (P.protocolReturned jid)) ∷ [])) ++ (V.commitError jid err ∷ [])) (at errorModel errorContext errorFront)
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
  overlapDemand = Y.sourceMux (Y.withWanton jid Mux.initiatorJob Y.m2) [] overlapRegistered
  overlapSampled = Y.sourceMux (Y.withWanton jid Mux.initiatorJob Y.m3) [] overlapRegistered
  overlapTraced = Y.sourceMux (Y.withWanton jid Mux.initiatorJob Y.m4) Y.messages overlapRegistered
  overlapReady = Y.sourceMux (Y.withWanton jid Mux.initiatorJob Y.m5) Y.messages overlapRegistered
  responderPool bothPool : Pool.State
  responderPool = record registeredPool
    { handles = put (ident 21) Pool.bodyRunning (Pool.handles registeredPool); parentFork = just (ident 21) }
  bothPool = record responderPool { registered = ident 21 ∷ Pool.registered registeredPool; parentFork = nothing }
  responder21 : Types.ProtocolJob
  responder21 = Types.protocolJob A.child₀ (ident 0) Mux.responderJob 1 (ident 21) Types.executing
  overlapBorn = record (withPool responderPool (Y.sourceMux (Y.withWanton jid Mux.initiatorJob Y.m6) Y.messages overlapRegistered))
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
       V.forkStart A.child₀ jid ∷ physicalStep (P.enterProtocolBody jid) ∷ physicalStep (P.protocolReturned jid) ∷ [])) ++ overlapActions)
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
    { governor = IG.setMux (ident 0) (record (Y.withWanton jid Mux.initiatorJob Y.m1) { status = Mux.failed err }) (Y.governor afterCleanInfraPopped)
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
       V.forkStart A.child₀ jid ∷ physicalStep (P.enterProtocolBody jid) ∷ physicalStep (P.protocolReturned jid) ∷ V.commitClean jid ∷ [])) ++
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
          V.forkStart A.child₀ jid ∷ physicalStep (P.enterProtocolBody jid) ∷ physicalStep (P.protocolReturned jid) ∷ V.commitClean jid ∷ [])) ++
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

  -- Target-driven hot retirement and a second physical initiator generation.
  -- All expected snapshots are checked by actual wrapper transitions below.
  module Reactivation where
    terminatingPeer retiredPeer secondActivatedPeer secondStartedPeer secondPublishedPeer secondPromotedPeer secondErroredPeer : Peer.Peer
    terminatingPeer = record cleanPromoted { hotControl = Peer.terminate; warmControl = Peer.continue }
    retiredPeer = record terminatingPeer
      { status = Peer.peerWarm; runs = Peer.protocolRun proto (Peer.notRunning clean) (Peer.notRunning clean) ∷ []; promotedAt = nothing }
    secondActivatedPeer = record retiredPeer { status = Peer.peerHot; hotControl = Peer.continue; warmControl = Peer.quiesce }
    secondStartedPeer = record secondActivatedPeer
      { runs = Peer.protocolRun proto Peer.running (Peer.notRunning clean) ∷ [] }
    secondPublishedPeer = record secondStartedPeer { runs = Peer.protocolRun proto Peer.running Peer.running ∷ [] }
    secondPromotedPeer = record secondPublishedPeer { promotedAt = just 18 }
    secondErroredPeer = record secondPromotedPeer { runs = Peer.protocolRun proto (Peer.returned (errored err)) Peer.running ∷ [] }
    deactivationWork secondWork : G.Job
    deactivationWork = G.job G.deactivate L.peerAddr (just (ident 0))
    secondWork = G.job G.activate L.peerAddr (just (ident 0))
    deactivationFrame activationFrame : J.PC → Bool → Bool → Sub.JobFrame
    deactivationFrame pc queued removed = Sub.jobFrame
      (J.frame deactivationWork (ident 14) (ident 15) (ident 14) (ident 0) pc) queued removed
    activationFrame pc queued removed = Sub.jobFrame
      (J.frame secondWork (ident 16) (ident 17) (ident 16) (ident 0) pc) queued removed
    deactivationBody activationBody : GP.Body
    deactivationBody = GP.body (ident 2) deactivationWork G.succeeded
    activationBody = GP.body (ident 3) secondWork G.succeeded
    deactivationCompletion activationCompletion : G.Completion
    deactivationCompletion = G.completion deactivationWork G.succeeded 0
    activationCompletion = G.completion secondWork G.succeeded 0

    -- Body return, queue publication, deregistration and Async publication are
    -- separate observations in both real governor jobs.
    deactivationReturnedPool deactivationQueuedPool deactivationRemovedPool deactivationDonePool : GP.Pool.State
    deactivationReturnedPool = record Waiters.deactPool
      { handles = put (ident 2) (GP.Pool.bodyReturned deactivationBody) (GP.Pool.handles Waiters.deactPool) }
    deactivationQueuedPool = record deactivationReturnedPool
      { handles = put (ident 2) (GP.Pool.deregisterPending GP.Pool.normalExit) (GP.Pool.handles deactivationReturnedPool)
      ; completions = GP.Pool.completions deactivationReturnedPool ++ (deactivationBody ∷ []) }
    deactivationRemovedPool = record deactivationQueuedPool
      { handles = put (ident 2) (GP.Pool.deregistered GP.Pool.normalExit) (GP.Pool.handles deactivationQueuedPool); registered = [] }
    deactivationDonePool = record deactivationRemovedPool
      { handles = put (ident 2) (GP.Pool.resultAvailable GP.Pool.normalExit) (GP.Pool.handles deactivationRemovedPool) }
    warmGovernor warmTargetGovernor secondPromotingGovernor : G.State
    warmGovernor = G.complete 5 60 16 deactivationCompletion (shiftG L.g18)
    warmTargetGovernor = record warmGovernor { target = G.targets 1 1 1 }
    secondPromotingGovernor = G.mark G.activate (L.peerAddr ∷ []) warmTargetGovernor
    activationForkPool activationRegisteredPool activationReturnedPool activationQueuedPool activationRemovedPool activationDonePool : GP.Pool.State
    activationForkPool = record deactivationDonePool
      { handles = put (ident 3) GP.Pool.bodyRunning (GP.Pool.handles deactivationDonePool); parentFork = just (ident 3) }
    activationRegisteredPool = record activationForkPool { registered = ident 3 ∷ []; parentFork = nothing }
    activationReturnedPool = record activationRegisteredPool
      { handles = put (ident 3) (GP.Pool.bodyReturned activationBody) (GP.Pool.handles activationRegisteredPool) }
    activationQueuedPool = record activationReturnedPool
      { handles = put (ident 3) (GP.Pool.deregisterPending GP.Pool.normalExit) (GP.Pool.handles activationReturnedPool)
      ; completions = GP.Pool.completions activationReturnedPool ++ (activationBody ∷ []) }
    activationRemovedPool = record activationQueuedPool
      { handles = put (ident 3) (GP.Pool.deregistered GP.Pool.normalExit) (GP.Pool.handles activationQueuedPool); registered = [] }
    activationDonePool = record activationRemovedPool
      { handles = put (ident 3) (GP.Pool.resultAvailable GP.Pool.normalExit) (GP.Pool.handles activationRemovedPool) }

    secondQueuedFront secondSelectedFront secondTracingFront secondReadyFront secondBornFront secondFreeFront secondErrorFront : V.Front
    secondQueuedFront = record freeFront
      { calls = (ident 21 , requested) ∷ V.calls freeFront
      ; commands = (A.child₀ , V.command (ident 21) 0 ∷ []) ∷ [] }
    secondSelectedFront = V.setCursor A.child₀ (V.selectedC (ident 21))
      (record secondQueuedFront { commands = (A.child₀ , []) ∷ [] })
    secondTracingFront = V.setCursor A.child₀ (V.tracingC (ident 21)) secondSelectedFront
    secondReadyFront = V.setCursor A.child₀ (V.forkReadyC (ident 21)) secondSelectedFront
    secondBornFront = record secondReadyFront
      { calls = put (ident 21) (record requested { thread = just (ident 21) }) (V.calls secondReadyFront)
      ; cursors = (A.child₀ , V.registeringC (ident 21) (ident 21)) ∷ [] }
    secondFreeFront = V.setCursor A.child₀ V.idleC secondBornFront
    secondErrorFront = record secondFreeFront
      { calls = put (ident 21) (record requested { thread = just (ident 21); value = just (errored err) }) (V.calls secondFreeFront) }
    secondJob : Types.BodyPhase → Types.ProtocolJob
    secondJob phase = Types.protocolJob A.child₀ (ident 0) Mux.initiatorJob 1 (ident 21) phase
    secondPayload : Types.TypedResult
    secondPayload = Types.protocolCompletion Mux.initiatorJob 1 (ident 21) (errored err)
    secondPhysicalForkPool secondPhysicalRegisteredPool oldReturnedPool oldQueuedPool oldRemovedPool oldAvailablePool oldConsumedPool : Pool.State
    secondPhysicalForkPool = record registeredPool
      { handles = put (ident 21) Pool.bodyRunning (Pool.handles registeredPool); parentFork = just (ident 21) }
    secondPhysicalRegisteredPool = record secondPhysicalForkPool
      { registered = ident 21 ∷ Pool.registered registeredPool; parentFork = nothing }
    oldReturnedPool = record secondPhysicalRegisteredPool
      { handles = put jid (Pool.bodyReturned payload) (Pool.handles secondPhysicalRegisteredPool) }
    oldQueuedPool = record oldReturnedPool
      { handles = put jid (Pool.deregisterPending Pool.normalExit) (Pool.handles oldReturnedPool); completions = payload ∷ [] }
    oldRemovedPool = record oldQueuedPool
      { handles = put jid (Pool.deregistered Pool.normalExit) (Pool.handles oldQueuedPool)
      ; registered = ident 21 ∷ Pool.registered Y.engines }
    oldAvailablePool = record oldRemovedPool
      { handles = put jid (Pool.resultAvailable Pool.normalExit) (Pool.handles oldRemovedPool) }
    oldConsumedPool = record oldAvailablePool { completions = [] }
    secondBorn secondRegistered oldBodyReturned oldBodyQueued oldBodyRemoved oldBodyAvailable oldCompletionPopped oldCompletionHandled oldTraceInvoked oldTraceReturned oldDeltaInvoked oldCompletionFinished : Y.Model
    secondBorn = record (withPool secondPhysicalForkPool registered)
      { jobs = put (ident 21) (secondJob Types.executing) (Y.jobs registered) }
    secondRegistered = withPool secondPhysicalRegisteredPool secondBorn
    oldBodyReturned = withPool oldReturnedPool secondRegistered
    oldBodyQueued = withPool oldQueuedPool secondRegistered
    oldBodyRemoved = withPool oldRemovedPool secondRegistered
    oldBodyAvailable = withPool oldAvailablePool secondRegistered
    oldCompletionPopped = record (withPool oldConsumedPool secondRegistered)
      { monitors = (A.child₀ , N.M.selected payload) ∷ []
      ; tickets = (A.child₀ , N.D.ticket payload N.D.captured) ∷ [] }
    oldCompletionHandled = record oldCompletionPopped { monitors = (A.child₀ , N.M.initiatorTracing clean) ∷ [] }
    oldTraceInvoked = record oldCompletionHandled { tickets = (A.child₀ , N.D.ticket payload N.D.muxInvoked) ∷ [] }
    oldTraceReturned = record oldCompletionHandled { tickets = (A.child₀ , N.D.ticket payload N.D.muxReturned) ∷ [] }
    oldDeltaInvoked = record oldCompletionHandled { tickets = (A.child₀ , N.D.ticket payload N.D.invoked) ∷ [] }
    oldCompletionFinished = record oldCompletionHandled
      { monitors = (A.child₀ , N.M.waiting) ∷ []; tickets = (A.child₀ , N.D.ticket payload N.D.returned) ∷ [] }
    secondErrorCaptured secondBodyReturned secondBodyQueued secondBodyRemoved secondBodyAvailable : Y.Model
    secondErrorCaptured = record oldCompletionFinished
      { jobs = put (ident 21) (secondJob (Types.resultCaptured (errored err))) (Y.jobs oldCompletionFinished) }
    secondReturnedPool secondQueuedPool secondRemovedPool secondAvailablePool : Pool.State
    secondReturnedPool = record oldConsumedPool
      { handles = put (ident 21) (Pool.bodyReturned secondPayload) (Pool.handles oldConsumedPool) }
    secondQueuedPool = record secondReturnedPool
      { handles = put (ident 21) (Pool.deregisterPending Pool.normalExit) (Pool.handles secondReturnedPool); completions = secondPayload ∷ [] }
    secondRemovedPool = record secondQueuedPool
      { handles = put (ident 21) (Pool.deregistered Pool.normalExit) (Pool.handles secondQueuedPool)
      ; registered = Pool.registered Y.engines }
    secondAvailablePool = record secondRemovedPool
      { handles = put (ident 21) (Pool.resultAvailable Pool.normalExit) (Pool.handles secondRemovedPool) }
    secondBodyReturned = withPool secondReturnedPool secondErrorCaptured
    secondBodyQueued = withPool secondQueuedPool secondErrorCaptured
    secondBodyRemoved = withPool secondRemovedPool secondErrorCaptured
    secondBodyAvailable = withPool secondAvailablePool secondErrorCaptured

    down68 : C.Context
    down68 = withPeer cleanPromoted Waiters.d68
    down69 : C.Context
    down69 = withPeer cleanPromoted Waiters.d69
    down70 : C.Context
    down70 = withPeer cleanPromoted Waiters.d70
    down71 : C.Context
    down71 = withPeer cleanPromoted Waiters.d71
    down72 : C.Context
    down72 = withPeer cleanPromoted Waiters.d72
    down73 : C.Context
    down73 = withPeer cleanPromoted Waiters.d73
    down74 : C.Context
    down74 = withPeer cleanPromoted Waiters.d74
    down75 : C.Context
    down75 = withPeer cleanPromoted Waiters.d75
    down76 : C.Context
    down76 = withPeer cleanPromoted Waiters.d76
    down77 : C.Context
    down77 = withPeer cleanPromoted Waiters.d77
    down78 : C.Context
    down78 = withPeer cleanPromoted Waiters.d78
    down79 : C.Context
    down79 = withPeer cleanPromoted Waiters.d79
    down80 : C.Context
    down80 = withPeer cleanPromoted Waiters.d80
    down81 : C.Context
    down81 = withPeer cleanPromoted Waiters.d81
    down82 : C.Context
    down82 = withPeer cleanPromoted Waiters.d82
    down83 : C.Context
    down83 = withPeer cleanPromoted Waiters.d83
    down84 : C.Context
    down84 = withPeer cleanPromoted Waiters.d84
    down85 : C.Context
    down85 = withPeer cleanPromoted Waiters.d85
    down86 : C.Context
    down86 = withPeer cleanPromoted Waiters.d86
    down87 : C.Context
    down87 = withPeer cleanPromoted Waiters.d87
    down88 : C.Context
    down88 = withPeer cleanPromoted Waiters.d88
    down89 : C.Context
    down89 = withPeer cleanPromoted Waiters.d89
    down90 : C.Context
    down90 = withPeer cleanPromoted Waiters.d90
    down91 : C.Context
    down91 = withPeer cleanPromoted Waiters.d91
    down92 : C.Context
    down92 = withPeer cleanPromoted Waiters.d92
    down93 : C.Context
    down93 = withPeer cleanPromoted Waiters.d93
    down94 : C.Context
    down94 = withPeer cleanPromoted Waiters.d94
    down95 : C.Context
    down95 = withPeer terminatingPeer Waiters.d95
    warm1 : C.Context
    warm1 = record record down95 { subsystem = record (C.subsystem down95) { peers = (ident 0 , retiredPeer) ∷ []; jobs = put (ident 2) (deactivationFrame (J.complete G.succeeded) false false) (C.SubContext.jobs (C.subsystem down95)) } } { governorPool = deactivationReturnedPool }
    warm2 : C.Context
    warm2 = record record warm1 { subsystem = record (C.subsystem warm1) { jobs = put (ident 2) (deactivationFrame (J.complete G.succeeded) true false) (C.SubContext.jobs (C.subsystem warm1)); completions = deactivationCompletion ∷ [] } } { governorPool = deactivationQueuedPool }
    warm3 : C.Context
    warm3 = record record warm2 { subsystem = record (C.subsystem warm2) { jobs = put (ident 2) (deactivationFrame (J.complete G.succeeded) true true) (C.SubContext.jobs (C.subsystem warm2)); pool = [] } } { governorPool = deactivationRemovedPool }
    warm4 : C.Context
    warm4 = record warm3 { governorPool = deactivationDonePool }
    warm5 : C.Context
    warm5 = record warm4 { subsystem = record (C.subsystem warm4) { pc = Sub.publishPublic } }
    warm6 : C.Context
    warm6 = record warm5 { subsystem = record (C.subsystem warm5) { publicState = C.SubContext.privateState (C.subsystem warm5); pc = Sub.sampleInputs } }
    warm7 : C.Context
    warm7 = record warm6 { subsystem = record (C.subsystem warm6) { now = 16; pc = Sub.prepareWait } }
    warm8 : C.Context
    warm8 = record warm7 { subsystem = record (C.subsystem warm7) { pc = Sub.selecting } }
    warm9 : C.Context
    warm9 = record warm8 { subsystem = record (C.subsystem warm8) { pc = Sub.apply (Sub.completion deactivationCompletion); completions = [] } }
    warm10 : C.Context
    warm10 = record warm9 { subsystem = record (C.subsystem warm9) { privateState = warmGovernor; pc = Sub.publishView [] } }
    warm11 : C.Context
    warm11 = record warm10 { subsystem = record (C.subsystem warm10) { pc = Sub.traceDecision [] } }
    warm12 : C.Context
    warm12 = record warm11 { subsystem = record (C.subsystem warm11) { pc = Sub.launch [] } }
    warm13 : C.Context
    warm13 = record warm12 { subsystem = record (C.subsystem warm12) { pc = Sub.publishPublic } }
    warm14 : C.Context
    warm14 = record warm13 { subsystem = record (C.subsystem warm13) { targetInput = G.targets 1 1 1 } }
    warm15 : C.Context
    warm15 = record warm14 { subsystem = record (C.subsystem warm14) { publicState = warmGovernor; pc = Sub.sampleInputs } }
    warm16 : C.Context
    warm16 = record warm15 { subsystem = record (C.subsystem warm15) { now = 17; pc = Sub.prepareWait } }
    warm17 : C.Context
    warm17 = record warm16 { subsystem = record (C.subsystem warm16) { pc = Sub.selecting } }
    warm18 : C.Context
    warm18 = record warm17 { subsystem = record (C.subsystem warm17) { pc = Sub.apply (Sub.targets (G.targets 1 1 1)) } }
    warm19 : C.Context
    warm19 = record warm18 { subsystem = record (C.subsystem warm18) { privateState = warmTargetGovernor; pc = Sub.publishView [] } }
    warm20 : C.Context
    warm20 = record warm19 { subsystem = record (C.subsystem warm19) { pc = Sub.traceDecision [] } }
    warm21 : C.Context
    warm21 = record warm20 { subsystem = record (C.subsystem warm20) { pc = Sub.launch [] } }
    warm22 : C.Context
    warm22 = record warm21 { subsystem = record (C.subsystem warm21) { pc = Sub.publishPublic } }
    warm23 : C.Context
    warm23 = record warm22 { subsystem = record (C.subsystem warm22) { publicState = warmTargetGovernor; pc = Sub.sampleInputs } }
    warm24 : C.Context
    warm24 = record warm23 { subsystem = record (C.subsystem warm23) { now = 18; pc = Sub.prepareWait } }
    warm25 : C.Context
    warm25 = record warm24 { subsystem = record (C.subsystem warm24) { pc = Sub.selecting } }
    warm26 : C.Context
    warm26 = record warm25 { subsystem = record (C.subsystem warm25) { pc = Sub.apply (Sub.policy (G.decision secondPromotingGovernor (secondWork ∷ []))) } }
    warm27 : C.Context
    warm27 = record warm26 { subsystem = record (C.subsystem warm26) { privateState = secondPromotingGovernor; pc = Sub.publishView (secondWork ∷ []) } }
    warm28 : C.Context
    warm28 = record warm27 { subsystem = record (C.subsystem warm27) { pc = Sub.traceDecision (secondWork ∷ []) } }
    warm29 : C.Context
    warm29 = record warm28 { subsystem = record (C.subsystem warm28) { pc = Sub.launch (secondWork ∷ []) } }
    warm30 : C.Context
    warm30 = record record warm29 { subsystem = record (C.subsystem warm29) { jobs = put (ident 3) (activationFrame (J.begin) false false) (C.SubContext.jobs (C.subsystem warm29)); nextJob = 4; pc = Sub.register (ident 3) [] } } { governorPool = activationForkPool }
    warm31 : C.Context
    warm31 = record record warm30 { subsystem = record (C.subsystem warm30) { pool = ident 3 ∷ []; pc = Sub.launch [] } } { governorPool = activationRegisteredPool }
    warm32 : C.Context
    warm32 = record warm31 { subsystem = record (C.subsystem warm31) { peers = (ident 0 , secondActivatedPeer) ∷ []; jobs = put (ident 3) (activationFrame (J.startBundle hot (1 ∷ [])) false false) (C.SubContext.jobs (C.subsystem warm31)) } }
    secondStartedContext : C.Context
    secondStartedContext = record warm32 { subsystem = record (C.subsystem warm32) { peers = (ident 0 , secondStartedPeer) ∷ []; jobs = put (ident 3) (activationFrame (J.startBundle hot []) false false) (C.SubContext.jobs (C.subsystem warm32)) } }
    secondTraversalContext : C.Context
    secondTraversalContext = record secondStartedContext { subsystem = record (C.subsystem secondStartedContext) { jobs = put (ident 3) (activationFrame (J.publishBundle hot) false false) (C.SubContext.jobs (C.subsystem secondStartedContext)) } }
    secondPublishedContext : C.Context
    secondPublishedContext = record secondTraversalContext { subsystem = record (C.subsystem secondTraversalContext) { peers = (ident 0 , secondPublishedPeer) ∷ []; jobs = put (ident 3) (activationFrame (J.finishActivation) false false) (C.SubContext.jobs (C.subsystem secondTraversalContext)) } }
    secondReturnedContext : C.Context
    secondReturnedContext = record record secondPublishedContext { subsystem = record (C.subsystem secondPublishedContext) { peers = (ident 0 , secondPromotedPeer) ∷ []; jobs = put (ident 3) (activationFrame (J.complete G.succeeded) false false) (C.SubContext.jobs (C.subsystem secondPublishedContext)) } } { governorPool = activationReturnedPool }
    secondQueuedContext : C.Context
    secondQueuedContext = record record secondReturnedContext { subsystem = record (C.subsystem secondReturnedContext) { jobs = put (ident 3) (activationFrame (J.complete G.succeeded) true false) (C.SubContext.jobs (C.subsystem secondReturnedContext)); completions = activationCompletion ∷ [] } } { governorPool = activationQueuedPool }
    secondRemovedContext : C.Context
    secondRemovedContext = record record secondQueuedContext { subsystem = record (C.subsystem secondQueuedContext) { jobs = put (ident 3) (activationFrame (J.complete G.succeeded) true true) (C.SubContext.jobs (C.subsystem secondQueuedContext)); pool = [] } } { governorPool = activationRemovedPool }
    secondDoneContext : C.Context
    secondDoneContext = record secondRemovedContext { governorPool = activationDonePool }
    secondErrorContext : C.Context
    secondErrorContext = withPeer secondErroredPeer secondDoneContext
    secondCooledContext : C.Context
    secondCooledContext = withPeer (Peer.cool secondErroredPeer) secondErrorContext

    firstCompletedActions : List V.Event
    firstCompletedActions = (V.startNext (ident 1) rid) ∷ (ps L.a63) ∷ (physicalStep (P.control A.child₀ P.selectCommand)) ∷ (V.selectStart A.child₀) ∷ (V.invokeStartTrace A.child₀) ∷ (V.returnStartTrace A.child₀) ∷ (V.forkStart A.child₀ jid) ∷ (physicalStep (P.enterProtocolBody jid)) ∷ (physicalStep (P.protocolReturned jid)) ∷ (V.commitClean jid) ∷ (V.registerStart jid) ∷ (ps L.a64) ∷ (ps (Sub.jobStep (ident 1) (J.finishHotAt 12))) ∷ (ps L.a66) ∷ (ps L.a67) ∷ (peerStep (PS.run (GP.publishAsyncResult (ident 1)))) ∷ []
    abstract
      first-completed-path : V.Runs (at reused k61 V.empty) firstCompletedActions (at registered kActivationDone freeFront)
      first-completed-path = V.more run1 (V.more run2 (V.more run3 (V.more run4 (V.more run5 (V.more run6 (V.more run7 (V.more run7a (V.more run8 (V.more run9 (V.more run10 (V.more run11 (V.more run12 (V.more run13 (V.more run14 (V.more run15 (V.stop))))))))))))))))
      initialized-first-completed : V.Runs initial (prefixActions ++ firstCompletedActions) (at registered kActivationDone freeFront)
      initialized-first-completed = Facts.append-protocols initialized-to-start first-completed-path

    reactEdge1 : V.advance (ps L.a68) (at registered kActivationDone freeFront) ≡ just (at registered down68 freeFront)
    reactEdge1 = refl

    reactEdge2 : V.advance (ps L.a69) (at registered down68 freeFront) ≡ just (at registered down69 freeFront)
    reactEdge2 = refl

    reactEdge3 : V.advance (ps (Sub.sampleTime 13)) (at registered down69 freeFront) ≡ just (at registered down70 freeFront)
    reactEdge3 = refl

    reactEdge4 : V.advance (ps L.a71) (at registered down70 freeFront) ≡ just (at registered down71 freeFront)
    reactEdge4 = refl

    reactEdge5 : V.advance (ps L.a72) (at registered down71 freeFront) ≡ just (at registered down72 freeFront)
    reactEdge5 = refl

    reactEdge6 : V.advance (ps (Sub.applyAt 13)) (at registered down72 freeFront) ≡ just (at registered down73 freeFront)
    reactEdge6 = refl

    reactEdge7 : V.advance (ps L.a74) (at registered down73 freeFront) ≡ just (at registered down74 freeFront)
    reactEdge7 = refl

    reactEdge8 : V.advance (ps L.a75) (at registered down74 freeFront) ≡ just (at registered down75 freeFront)
    reactEdge8 = refl

    reactEdge9 : V.advance (ps L.a76) (at registered down75 freeFront) ≡ just (at registered down76 freeFront)
    reactEdge9 = refl

    reactEdge10 : V.advance (ps L.a77) (at registered down76 freeFront) ≡ just (at registered down77 freeFront)
    reactEdge10 = refl

    reactEdge11 : V.advance (ps L.a78) (at registered down77 freeFront) ≡ just (at registered down78 freeFront)
    reactEdge11 = refl

    reactEdge12 : V.advance (ps (Sub.sampleTime 14)) (at registered down78 freeFront) ≡ just (at registered down79 freeFront)
    reactEdge12 = refl

    reactEdge13 : V.advance (ps L.a80) (at registered down79 freeFront) ≡ just (at registered down80 freeFront)
    reactEdge13 = refl

    reactEdge14 : V.advance (ps L.a81) (at registered down80 freeFront) ≡ just (at registered down81 freeFront)
    reactEdge14 = refl

    reactEdge15 : V.advance (ps (Sub.applyAt 14)) (at registered down81 freeFront) ≡ just (at registered down82 freeFront)
    reactEdge15 = refl

    reactEdge16 : V.advance (ps L.a83) (at registered down82 freeFront) ≡ just (at registered down83 freeFront)
    reactEdge16 = refl

    reactEdge17 : V.advance (ps L.a84) (at registered down83 freeFront) ≡ just (at registered down84 freeFront)
    reactEdge17 = refl

    reactEdge18 : V.advance (ps L.a85) (at registered down84 freeFront) ≡ just (at registered down85 freeFront)
    reactEdge18 = refl

    reactEdge19 : V.advance (ps L.a86) (at registered down85 freeFront) ≡ just (at registered down86 freeFront)
    reactEdge19 = refl

    reactEdge20 : V.advance (ps (Sub.sampleTime 15)) (at registered down86 freeFront) ≡ just (at registered down87 freeFront)
    reactEdge20 = refl

    reactEdge21 : V.advance (ps L.a88) (at registered down87 freeFront) ≡ just (at registered down88 freeFront)
    reactEdge21 = refl

    reactEdge22 : V.advance (ps L.a89) (at registered down88 freeFront) ≡ just (at registered down89 freeFront)
    reactEdge22 = refl

    reactEdge23 : V.advance (ps (Sub.applyAt 15)) (at registered down89 freeFront) ≡ just (at registered down90 freeFront)
    reactEdge23 = refl

    reactEdge24 : V.advance (ps L.a91) (at registered down90 freeFront) ≡ just (at registered down91 freeFront)
    reactEdge24 = refl

    reactEdge25 : V.advance (ps L.a92) (at registered down91 freeFront) ≡ just (at registered down92 freeFront)
    reactEdge25 = refl

    reactEdge26 : V.advance (ps L.a93) (at registered down92 freeFront) ≡ just (at registered down93 freeFront)
    reactEdge26 = refl

    reactEdge27 : V.advance (ps L.a94) (at registered down93 freeFront) ≡ just (at registered down94 freeFront)
    reactEdge27 = refl

    reactEdge28 : V.advance (ps L.a95) (at registered down94 freeFront) ≡ just (at registered down95 freeFront)
    reactEdge28 = refl

    reactEdge29 : V.advance (V.waitJobResults (ident 2)) (at registered down95 freeFront) ≡ just (at registered warm1 freeFront)
    reactEdge29 = refl

    reactEdge30 : V.advance (ps (Sub.enqueueCompletion (ident 2) 0)) (at registered warm1 freeFront) ≡ just (at registered warm2 freeFront)
    reactEdge30 = refl

    reactEdge31 : V.advance (ps (Sub.deregisterJob (ident 2))) (at registered warm2 freeFront) ≡ just (at registered warm3 freeFront)
    reactEdge31 = refl

    reactEdge32 : V.advance (peerStep (PS.run (GP.publishAsyncResult (ident 2)))) (at registered warm3 freeFront) ≡ just (at registered warm4 freeFront)
    reactEdge32 = refl

    reactEdge33 : V.advance (ps Sub.finishLaunch) (at registered warm4 freeFront) ≡ just (at registered warm5 freeFront)
    reactEdge33 = refl

    reactEdge34 : V.advance (ps Sub.publishPublicState) (at registered warm5 freeFront) ≡ just (at registered warm6 freeFront)
    reactEdge34 = refl

    reactEdge35 : V.advance (ps (Sub.sampleTime 16)) (at registered warm6 freeFront) ≡ just (at registered warm7 freeFront)
    reactEdge35 = refl

    reactEdge36 : V.advance (ps Sub.registerWakeup) (at registered warm7 freeFront) ≡ just (at registered warm8 freeFront)
    reactEdge36 = refl

    reactEdge37 : V.advance (ps Sub.selectCompletion) (at registered warm8 freeFront) ≡ just (at registered warm9 freeFront)
    reactEdge37 = refl

    reactEdge38 : V.advance (ps (Sub.applyAt 16)) (at registered warm9 freeFront) ≡ just (at registered warm10 freeFront)
    reactEdge38 = refl

    reactEdge39 : V.advance (ps Sub.publishCounters) (at registered warm10 freeFront) ≡ just (at registered warm11 freeFront)
    reactEdge39 = refl

    reactEdge40 : V.advance (ps Sub.traceSelection) (at registered warm11 freeFront) ≡ just (at registered warm12 freeFront)
    reactEdge40 = refl

    reactEdge41 : V.advance (ps Sub.finishLaunch) (at registered warm12 freeFront) ≡ just (at registered warm13 freeFront)
    reactEdge41 = refl

    reactEdge42 : V.advance (ps (Sub.setTargets (G.targets 1 1 1))) (at registered warm13 freeFront) ≡ just (at registered warm14 freeFront)
    reactEdge42 = refl

    reactEdge43 : V.advance (ps Sub.publishPublicState) (at registered warm14 freeFront) ≡ just (at registered warm15 freeFront)
    reactEdge43 = refl

    reactEdge44 : V.advance (ps (Sub.sampleTime 17)) (at registered warm15 freeFront) ≡ just (at registered warm16 freeFront)
    reactEdge44 = refl

    reactEdge45 : V.advance (ps Sub.registerWakeup) (at registered warm16 freeFront) ≡ just (at registered warm17 freeFront)
    reactEdge45 = refl

    reactEdge46 : V.advance (ps Sub.selectTargets) (at registered warm17 freeFront) ≡ just (at registered warm18 freeFront)
    reactEdge46 = refl

    reactEdge47 : V.advance (ps (Sub.applyAt 17)) (at registered warm18 freeFront) ≡ just (at registered warm19 freeFront)
    reactEdge47 = refl

    reactEdge48 : V.advance (ps Sub.publishCounters) (at registered warm19 freeFront) ≡ just (at registered warm20 freeFront)
    reactEdge48 = refl

    reactEdge49 : V.advance (ps Sub.traceSelection) (at registered warm20 freeFront) ≡ just (at registered warm21 freeFront)
    reactEdge49 = refl

    reactEdge50 : V.advance (ps Sub.finishLaunch) (at registered warm21 freeFront) ≡ just (at registered warm22 freeFront)
    reactEdge50 = refl

    reactEdge51 : V.advance (ps Sub.publishPublicState) (at registered warm22 freeFront) ≡ just (at registered warm23 freeFront)
    reactEdge51 = refl

    reactEdge52 : V.advance (ps (Sub.sampleTime 18)) (at registered warm23 freeFront) ≡ just (at registered warm24 freeFront)
    reactEdge52 = refl

    reactEdge53 : V.advance (ps Sub.registerWakeup) (at registered warm24 freeFront) ≡ just (at registered warm25 freeFront)
    reactEdge53 = refl

    reactEdge54 : V.advance (ps (Sub.selectPolicy (L.peerAddr ∷ []))) (at registered warm25 freeFront) ≡ just (at registered warm26 freeFront)
    reactEdge54 = refl

    reactEdge55 : V.advance (ps (Sub.applyAt 18)) (at registered warm26 freeFront) ≡ just (at registered warm27 freeFront)
    reactEdge55 = refl

    reactEdge56 : V.advance (ps Sub.publishCounters) (at registered warm27 freeFront) ≡ just (at registered warm28 freeFront)
    reactEdge56 = refl

    reactEdge57 : V.advance (ps Sub.traceSelection) (at registered warm28 freeFront) ≡ just (at registered warm29 freeFront)
    reactEdge57 = refl

    reactEdge58 : V.advance (ps (Sub.forkJob (ident 16) (ident 17) (ident 16))) (at registered warm29 freeFront) ≡ just (at registered warm30 freeFront)
    reactEdge58 = refl

    reactEdge59 : V.advance (ps Sub.registerJob) (at registered warm30 freeFront) ≡ just (at registered warm31 freeFront)
    reactEdge59 = refl

    reactEdge60 : V.advance (ps (Sub.jobStep (ident 3) J.enter)) (at registered warm31 freeFront) ≡ just (at registered warm32 freeFront)
    reactEdge60 = refl

    reactEdge61 : V.advance (V.startNext (ident 3) (ident 21)) (at registered warm32 freeFront) ≡ just (at registered secondStartedContext secondQueuedFront)
    reactEdge61 = refl

    reactEdge62 : V.advance (ps (Sub.jobStep (ident 3) J.runNext)) (at registered secondStartedContext secondQueuedFront) ≡ just (at registered secondTraversalContext secondQueuedFront)
    reactEdge62 = refl

    reactEdge63 : V.advance (V.selectStart A.child₀) (at registered secondTraversalContext secondQueuedFront) ≡ just (at registered secondTraversalContext secondSelectedFront)
    reactEdge63 = refl

    reactEdge64 : V.advance (V.invokeStartTrace A.child₀) (at registered secondTraversalContext secondSelectedFront) ≡ just (at registered secondTraversalContext secondTracingFront)
    reactEdge64 = refl

    reactEdge65 : V.advance (V.returnStartTrace A.child₀) (at registered secondTraversalContext secondTracingFront) ≡ just (at registered secondTraversalContext secondReadyFront)
    reactEdge65 = refl

    reactEdge66 : V.advance (V.forkStart A.child₀ (ident 21)) (at registered secondTraversalContext secondReadyFront) ≡ just (at secondBorn secondTraversalContext secondBornFront)
    reactEdge66 = refl

    reactEdge67 : V.advance (V.registerStart (ident 21)) (at secondBorn secondTraversalContext secondBornFront) ≡ just (at secondRegistered secondTraversalContext secondFreeFront)
    reactEdge67 = refl

    reactEdge68 : V.advance (ps (Sub.jobStep (ident 3) J.publishStarted)) (at secondRegistered secondTraversalContext secondFreeFront) ≡ just (at secondRegistered secondPublishedContext secondFreeFront)
    reactEdge68 = refl

    reactEdge69 : V.advance (ps (Sub.jobStep (ident 3) (J.finishHotAt 18))) (at secondRegistered secondPublishedContext secondFreeFront) ≡ just (at secondRegistered secondReturnedContext secondFreeFront)
    reactEdge69 = refl

    reactEdge70 : V.advance (ps (Sub.enqueueCompletion (ident 3) 0)) (at secondRegistered secondReturnedContext secondFreeFront) ≡ just (at secondRegistered secondQueuedContext secondFreeFront)
    reactEdge70 = refl

    reactEdge71 : V.advance (ps (Sub.deregisterJob (ident 3))) (at secondRegistered secondQueuedContext secondFreeFront) ≡ just (at secondRegistered secondRemovedContext secondFreeFront)
    reactEdge71 = refl

    reactEdge72 : V.advance (peerStep (PS.run (GP.publishAsyncResult (ident 3)))) (at secondRegistered secondRemovedContext secondFreeFront) ≡ just (at secondRegistered secondDoneContext secondFreeFront)
    reactEdge72 = refl

    reactEdge73 : V.advance (physicalStep (P.returnProtocol jid)) (at secondRegistered secondDoneContext secondFreeFront) ≡ just (at oldBodyReturned secondDoneContext secondFreeFront)
    reactEdge73 = refl

    reactEdge74 : V.advance (physicalStep (P.publishProtocol jid)) (at oldBodyReturned secondDoneContext secondFreeFront) ≡ just (at oldBodyQueued secondDoneContext secondFreeFront)
    reactEdge74 = refl

    reactEdge75 : V.advance (physicalStep (P.deregisterProtocol jid)) (at oldBodyQueued secondDoneContext secondFreeFront) ≡ just (at oldBodyRemoved secondDoneContext secondFreeFront)
    reactEdge75 = refl

    reactEdge76 : V.advance (physicalStep (P.asyncProtocolResult jid)) (at oldBodyRemoved secondDoneContext secondFreeFront) ≡ just (at oldBodyAvailable secondDoneContext secondFreeFront)
    reactEdge76 = refl

    reactEdge77 : V.advance (monitorStep (N.M.consume A.child₀)) (at oldBodyAvailable secondDoneContext secondFreeFront) ≡ just (at oldCompletionPopped secondDoneContext secondFreeFront)
    reactEdge77 = refl

    reactEdge78 : V.advance (monitorStep (N.M.handleSelected A.child₀)) (at oldCompletionPopped secondDoneContext secondFreeFront) ≡ just (at oldCompletionHandled secondDoneContext secondFreeFront)
    reactEdge78 = refl

    reactEdge79 : V.advance (deltaStep (N.D.beginInitiatorTrace A.child₀)) (at oldCompletionHandled secondDoneContext secondFreeFront) ≡ just (at oldTraceInvoked secondDoneContext secondFreeFront)
    reactEdge79 = refl

    reactEdge80 : V.advance (deltaStep (N.D.observeInitiatorReturn A.child₀)) (at oldTraceInvoked secondDoneContext secondFreeFront) ≡ just (at oldTraceReturned secondDoneContext secondFreeFront)
    reactEdge80 = refl

    reactEdge81 : V.advance (deltaStep (N.D.beginDeltaQ A.child₀)) (at oldTraceReturned secondDoneContext secondFreeFront) ≡ just (at oldDeltaInvoked secondDoneContext secondFreeFront)
    reactEdge81 = refl

    reactEdge82 : V.advance (deltaStep (N.D.observeReturn A.child₀)) (at oldDeltaInvoked secondDoneContext secondFreeFront) ≡ just (at oldCompletionFinished secondDoneContext secondFreeFront)
    reactEdge82 = refl

    reactEdge83 : V.advance (V.commitError (ident 21) err) (at oldCompletionFinished secondDoneContext secondFreeFront) ≡ just (at secondErrorCaptured secondErrorContext secondErrorFront)
    reactEdge83 = refl

    reactEdge84 : V.advance (physicalStep (P.returnProtocol (ident 21))) (at secondErrorCaptured secondErrorContext secondErrorFront) ≡ just (at secondBodyReturned secondErrorContext secondErrorFront)
    reactEdge84 = refl

    reactEdge85 : V.advance (physicalStep (P.publishProtocol (ident 21))) (at secondBodyReturned secondErrorContext secondErrorFront) ≡ just (at secondBodyQueued secondErrorContext secondErrorFront)
    reactEdge85 = refl

    reactEdge86 : V.advance (physicalStep (P.deregisterProtocol (ident 21))) (at secondBodyQueued secondErrorContext secondErrorFront) ≡ just (at secondBodyRemoved secondErrorContext secondErrorFront)
    reactEdge86 = refl

    reactEdge87 : V.advance (physicalStep (P.asyncProtocolResult (ident 21))) (at secondBodyRemoved secondErrorContext secondErrorFront) ≡ just (at secondBodyAvailable secondErrorContext secondErrorFront)
    reactEdge87 = refl

    reactEdge88 : V.advance (V.pollResults (ident 0) (ident 50)) (at secondBodyAvailable secondErrorContext secondErrorFront) ≡ just (at secondBodyAvailable secondCooledContext secondErrorFront)
    reactEdge88 = refl

    reactivationActions : List V.Event
    reactivationActions = (ps L.a68) ∷ (ps L.a69) ∷ (ps (Sub.sampleTime 13)) ∷ (ps L.a71) ∷ (ps L.a72) ∷ (ps (Sub.applyAt 13)) ∷ (ps L.a74) ∷ (ps L.a75) ∷ (ps L.a76) ∷ (ps L.a77) ∷ (ps L.a78) ∷ (ps (Sub.sampleTime 14)) ∷ (ps L.a80) ∷ (ps L.a81) ∷ (ps (Sub.applyAt 14)) ∷ (ps L.a83) ∷ (ps L.a84) ∷ (ps L.a85) ∷ (ps L.a86) ∷ (ps (Sub.sampleTime 15)) ∷ (ps L.a88) ∷ (ps L.a89) ∷ (ps (Sub.applyAt 15)) ∷ (ps L.a91) ∷ (ps L.a92) ∷ (ps L.a93) ∷ (ps L.a94) ∷ (ps L.a95) ∷ (V.waitJobResults (ident 2)) ∷ (ps (Sub.enqueueCompletion (ident 2) 0)) ∷ (ps (Sub.deregisterJob (ident 2))) ∷ (peerStep (PS.run (GP.publishAsyncResult (ident 2)))) ∷ (ps Sub.finishLaunch) ∷ (ps Sub.publishPublicState) ∷ (ps (Sub.sampleTime 16)) ∷ (ps Sub.registerWakeup) ∷ (ps Sub.selectCompletion) ∷ (ps (Sub.applyAt 16)) ∷ (ps Sub.publishCounters) ∷ (ps Sub.traceSelection) ∷ (ps Sub.finishLaunch) ∷ (ps (Sub.setTargets (G.targets 1 1 1))) ∷ (ps Sub.publishPublicState) ∷ (ps (Sub.sampleTime 17)) ∷ (ps Sub.registerWakeup) ∷ (ps Sub.selectTargets) ∷ (ps (Sub.applyAt 17)) ∷ (ps Sub.publishCounters) ∷ (ps Sub.traceSelection) ∷ (ps Sub.finishLaunch) ∷ (ps Sub.publishPublicState) ∷ (ps (Sub.sampleTime 18)) ∷ (ps Sub.registerWakeup) ∷ (ps (Sub.selectPolicy (L.peerAddr ∷ []))) ∷ (ps (Sub.applyAt 18)) ∷ (ps Sub.publishCounters) ∷ (ps Sub.traceSelection) ∷ (ps (Sub.forkJob (ident 16) (ident 17) (ident 16))) ∷ (ps Sub.registerJob) ∷ (ps (Sub.jobStep (ident 3) J.enter)) ∷ (V.startNext (ident 3) (ident 21)) ∷ (ps (Sub.jobStep (ident 3) J.runNext)) ∷ (V.selectStart A.child₀) ∷ (V.invokeStartTrace A.child₀) ∷ (V.returnStartTrace A.child₀) ∷ (V.forkStart A.child₀ (ident 21)) ∷ (V.registerStart (ident 21)) ∷ (ps (Sub.jobStep (ident 3) J.publishStarted)) ∷ (ps (Sub.jobStep (ident 3) (J.finishHotAt 18))) ∷ (ps (Sub.enqueueCompletion (ident 3) 0)) ∷ (ps (Sub.deregisterJob (ident 3))) ∷ (peerStep (PS.run (GP.publishAsyncResult (ident 3)))) ∷ (physicalStep (P.returnProtocol jid)) ∷ (physicalStep (P.publishProtocol jid)) ∷ (physicalStep (P.deregisterProtocol jid)) ∷ (physicalStep (P.asyncProtocolResult jid)) ∷ (monitorStep (N.M.consume A.child₀)) ∷ (monitorStep (N.M.handleSelected A.child₀)) ∷ (deltaStep (N.D.beginInitiatorTrace A.child₀)) ∷ (deltaStep (N.D.observeInitiatorReturn A.child₀)) ∷ (deltaStep (N.D.beginDeltaQ A.child₀)) ∷ (deltaStep (N.D.observeReturn A.child₀)) ∷ (V.commitError (ident 21) err) ∷ (physicalStep (P.returnProtocol (ident 21))) ∷ (physicalStep (P.publishProtocol (ident 21))) ∷ (physicalStep (P.deregisterProtocol (ident 21))) ∷ (physicalStep (P.asyncProtocolResult (ident 21))) ∷ (V.pollResults (ident 0) (ident 50)) ∷ []
    initializedReactivationActions : List V.Event
    initializedReactivationActions = (prefixActions ++ firstCompletedActions) ++ reactivationActions
    abstract
      reactivation-path : V.Runs (at registered kActivationDone freeFront) reactivationActions (at secondBodyAvailable secondCooledContext secondErrorFront)
      reactivation-path = V.more reactEdge1 (V.more reactEdge2 (V.more reactEdge3 (V.more reactEdge4 (V.more reactEdge5 (V.more reactEdge6 (V.more reactEdge7 (V.more reactEdge8 (V.more reactEdge9 (V.more reactEdge10 (V.more reactEdge11 (V.more reactEdge12 (V.more reactEdge13 (V.more reactEdge14 (V.more reactEdge15 (V.more reactEdge16 (V.more reactEdge17 (V.more reactEdge18 (V.more reactEdge19 (V.more reactEdge20 (V.more reactEdge21 (V.more reactEdge22 (V.more reactEdge23 (V.more reactEdge24 (V.more reactEdge25 (V.more reactEdge26 (V.more reactEdge27 (V.more reactEdge28 (V.more reactEdge29 (V.more reactEdge30 (V.more reactEdge31 (V.more reactEdge32 (V.more reactEdge33 (V.more reactEdge34 (V.more reactEdge35 (V.more reactEdge36 (V.more reactEdge37 (V.more reactEdge38 (V.more reactEdge39 (V.more reactEdge40 (V.more reactEdge41 (V.more reactEdge42 (V.more reactEdge43 (V.more reactEdge44 (V.more reactEdge45 (V.more reactEdge46 (V.more reactEdge47 (V.more reactEdge48 (V.more reactEdge49 (V.more reactEdge50 (V.more reactEdge51 (V.more reactEdge52 (V.more reactEdge53 (V.more reactEdge54 (V.more reactEdge55 (V.more reactEdge56 (V.more reactEdge57 (V.more reactEdge58 (V.more reactEdge59 (V.more reactEdge60 (V.more reactEdge61 (V.more reactEdge62 (V.more reactEdge63 (V.more reactEdge64 (V.more reactEdge65 (V.more reactEdge66 (V.more reactEdge67 (V.more reactEdge68 (V.more reactEdge69 (V.more reactEdge70 (V.more reactEdge71 (V.more reactEdge72 (V.more reactEdge73 (V.more reactEdge74 (V.more reactEdge75 (V.more reactEdge76 (V.more reactEdge77 (V.more reactEdge78 (V.more reactEdge79 (V.more reactEdge80 (V.more reactEdge81 (V.more reactEdge82 (V.more reactEdge83 (V.more reactEdge84 (V.more reactEdge85 (V.more reactEdge86 (V.more reactEdge87 (V.more reactEdge88 (V.stop))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
      initialized-reactivation : V.Runs initial initializedReactivationActions (at secondBodyAvailable secondCooledContext secondErrorFront)
      initialized-reactivation = Facts.append-protocols initialized-first-completed reactivation-path
    reactivation-supply : Inv.ProtocolValid (at secondBodyAvailable secondCooledContext secondErrorFront)
    reactivation-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-reactivation

    -- These controls use states on the initialized path above, including the
    -- old physical completion delivered while the second cell is still empty.
    secondQueuedRuntime secondPublishedRuntime oldDeliveredRuntime secondResultRuntime secondCooledRuntime : V.Runtime
    secondQueuedRuntime = at registered secondStartedContext secondQueuedFront
    secondPublishedRuntime = at secondRegistered secondPublishedContext secondFreeFront
    oldDeliveredRuntime = at oldCompletionFinished secondDoneContext secondFreeFront
    secondResultRuntime = at secondBodyAvailable secondErrorContext secondErrorFront
    secondCooledRuntime = at secondBodyAvailable secondCooledContext secondErrorFront
    current-cell-is-fresh : V.latest A.child₀ 1 (V.calls (V.front secondQueuedRuntime)) ≡ just (ident 21 , requested)
    current-cell-is-fresh = refl
    old-result-at-second-call : V.observe rid secondQueuedRuntime ≡ just (V.localResult clean)
    old-result-at-second-call = refl
    new-cell-starts-empty : V.observe (ident 21) secondQueuedRuntime ≡ nothing
    new-cell-starts-empty = refl
    new-slot-is-busy : V.slotIdle A.child₀ 1 (V.front secondQueuedRuntime) ≡ false
    new-slot-is-busy = refl
    no-reused-result-cell : V.advance (V.startNext (ident 3) rid) (at registered warm32 freeFront) ≡ nothing
    no-reused-result-cell = refl
    no-reused-physical-job : V.advance (V.forkStart A.child₀ jid)
      (at registered secondTraversalContext secondReadyFront) ≡ nothing
    no-reused-physical-job = refl
    no-physical-birth-at-call-return : lookup (ident 21) (P.jobs (V.physical (V.base secondQueuedRuntime))) ≡ nothing
    no-physical-birth-at-call-return = refl
    retirement-blocks-unpublished-result : V.firstPublished hot (ident 0) secondStartedPeer secondQueuedRuntime ≡ nothing
    retirement-blocks-unpublished-result = refl
    no-poll-before-new-publication : V.advance (V.pollResults (ident 0) (ident 50)) secondQueuedRuntime ≡ nothing
    no-poll-before-new-publication = refl
    new-published-result-retries : V.firstPublished hot (ident 0) secondPublishedPeer secondPublishedRuntime ≡ nothing
    new-published-result-retries = refl
    no-old-clean-poll-after-new-publication : V.advance (V.pollResults (ident 0) (ident 50)) secondPublishedRuntime ≡ nothing
    no-old-clean-poll-after-new-publication = refl
    stale-cache-cannot-update-second-run :
      V.cacheResult rid requested (errored err) (V.front secondPublishedRuntime) (V.base secondPublishedRuntime) ≡ V.base secondPublishedRuntime
    stale-cache-cannot-update-second-run = refl
    no-second-write-to-old-cell : V.advance (V.commitError jid err) secondPublishedRuntime ≡ nothing
    no-second-write-to-old-cell = refl
    late-old-completion-keeps-new-cell-empty : V.observe (ident 21) oldDeliveredRuntime ≡ nothing
    late-old-completion-keeps-new-cell-empty = refl
    late-old-completion-keeps-current-published-action :
      V.firstPublished hot (ident 0) secondPromotedPeer oldDeliveredRuntime ≡ nothing
    late-old-completion-keeps-current-published-action = refl
    old-async-is-really-published : lookup jid (Pool.handles (P.poolAt A.child₀ (V.physical (V.base oldDeliveredRuntime)))) ≡
      just (Pool.resultAvailable Pool.normalExit)
    old-async-is-really-published = refl
    new-body-survives-old-completion : lookup (ident 21) (Pool.handles (P.poolAt A.child₀ (V.physical (V.base oldDeliveredRuntime)))) ≡ just Pool.bodyRunning
    new-body-survives-old-completion = refl
    distinct-physical-generations : P.jobs (V.physical (V.base oldDeliveredRuntime)) ≡
      (jid , physicalJob (Types.resultCaptured clean)) ∷ (ident 21 , secondJob Types.executing) ∷ []
    distinct-physical-generations = refl
    old-result-after-new-error : V.observe rid secondResultRuntime ≡ just (V.localResult clean)
    old-result-after-new-error = refl
    current-result-is-new-error : V.observe (ident 21) secondResultRuntime ≡ just (V.localResult (errored err))
    current-result-is-new-error = refl
    published-action-reads-new-result :
      V.firstPublished hot (ident 0) secondErroredPeer secondResultRuntime ≡ just (1 , V.localResult (errored err))
    published-action-reads-new-result = refl
    new-async-is-really-published : lookup (ident 21) (Pool.handles (P.poolAt A.child₀ (V.physical (V.base secondResultRuntime)))) ≡
      just (Pool.resultAvailable Pool.normalExit)
    new-async-is-really-published = refl
    actual-new-typed-completion : Pool.completions (P.poolAt A.child₀ (V.physical (V.base secondResultRuntime))) ≡ secondPayload ∷ []
    actual-new-typed-completion = refl
    peer-cools-on-new-result : lookup (ident 0) (C.SubContext.peers (C.subsystem (K.context (V.base secondCooledRuntime)))) ≡
      just (Peer.cool secondErroredPeer)
    peer-cools-on-new-result = refl
    server-still-serving : S.stage (E.base (K.server (V.base secondCooledRuntime))) ≡ S.serving
    server-still-serving = refl
    initiator-completions-do-not-notify-ig : Shared.inboundInfo (Machine.world (O.core (V.sourceOf secondCooledRuntime))) ≡ []
    initiator-completions-do-not-notify-ig = refl

    -- A live restarted initiator and an older clean body share the actual mux
    -- pool. Scope exit reaches CM's normal monitor-delivery boundary.
    module Shutdown where
      import ConnectionManagement.Rules.CMShutdown as Close
      import ConnectionManagement.Rules.Cleanup as Cleanup
      import ConnectionManagement.Properties.MuxHandlerExit as HandlerProof
      import ConnectionManagement.Properties.ServerPeersMonitorJoins as CacheLifecycle
      private
        module Lifecycle52 = CacheLifecycle.Frontend I.bearerClosed Prior.classify capability
          using (FramedRuns; frameDone; frameNext; server-framed; handler-action)
        module SC = StartTrace.ScopedCM
        module Group = N.G
        module W = N.W
        module HandlerFacts = HandlerProof I.bearerClosed
      shutdownError : ErrorId
      shutdownError = errorId 191
      liveActivationActions : List V.Event
      liveActivationActions = (ps L.a68) ∷ (ps L.a69) ∷ (ps (Sub.sampleTime 13)) ∷ (ps L.a71) ∷ (ps L.a72) ∷ (ps (Sub.applyAt 13)) ∷ (ps L.a74) ∷ (ps L.a75) ∷ (ps L.a76) ∷ (ps L.a77) ∷ (ps L.a78) ∷ (ps (Sub.sampleTime 14)) ∷ (ps L.a80) ∷ (ps L.a81) ∷ (ps (Sub.applyAt 14)) ∷ (ps L.a83) ∷ (ps L.a84) ∷ (ps L.a85) ∷ (ps L.a86) ∷ (ps (Sub.sampleTime 15)) ∷ (ps L.a88) ∷ (ps L.a89) ∷ (ps (Sub.applyAt 15)) ∷ (ps L.a91) ∷ (ps L.a92) ∷ (ps L.a93) ∷ (ps L.a94) ∷ (ps L.a95) ∷ (V.waitJobResults (ident 2)) ∷ (ps (Sub.enqueueCompletion (ident 2) 0)) ∷ (ps (Sub.deregisterJob (ident 2))) ∷ (peerStep (PS.run (GP.publishAsyncResult (ident 2)))) ∷ (ps Sub.finishLaunch) ∷ (ps Sub.publishPublicState) ∷ (ps (Sub.sampleTime 16)) ∷ (ps Sub.registerWakeup) ∷ (ps Sub.selectCompletion) ∷ (ps (Sub.applyAt 16)) ∷ (ps Sub.publishCounters) ∷ (ps Sub.traceSelection) ∷ (ps Sub.finishLaunch) ∷ (ps (Sub.setTargets (G.targets 1 1 1))) ∷ (ps Sub.publishPublicState) ∷ (ps (Sub.sampleTime 17)) ∷ (ps Sub.registerWakeup) ∷ (ps Sub.selectTargets) ∷ (ps (Sub.applyAt 17)) ∷ (ps Sub.publishCounters) ∷ (ps Sub.traceSelection) ∷ (ps Sub.finishLaunch) ∷ (ps Sub.publishPublicState) ∷ (ps (Sub.sampleTime 18)) ∷ (ps Sub.registerWakeup) ∷ (ps (Sub.selectPolicy (L.peerAddr ∷ []))) ∷ (ps (Sub.applyAt 18)) ∷ (ps Sub.publishCounters) ∷ (ps Sub.traceSelection) ∷ (ps (Sub.forkJob (ident 16) (ident 17) (ident 16))) ∷ (ps Sub.registerJob) ∷ (ps (Sub.jobStep (ident 3) J.enter)) ∷ (V.startNext (ident 3) (ident 21)) ∷ (ps (Sub.jobStep (ident 3) J.runNext)) ∷ (V.selectStart A.child₀) ∷ (V.invokeStartTrace A.child₀) ∷ (V.returnStartTrace A.child₀) ∷ (V.forkStart A.child₀ (ident 21)) ∷ (V.registerStart (ident 21)) ∷ (ps (Sub.jobStep (ident 3) J.publishStarted)) ∷ (ps (Sub.jobStep (ident 3) (J.finishHotAt 18))) ∷ (ps (Sub.enqueueCompletion (ident 3) 0)) ∷ (ps (Sub.deregisterJob (ident 3))) ∷ (peerStep (PS.run (GP.publishAsyncResult (ident 3)))) ∷ []
      livePrefixActions : List V.Event
      livePrefixActions = (prefixActions ++ firstCompletedActions) ++ liveActivationActions
      liveRestart : V.Runtime
      liveRestart = at secondRegistered secondDoneContext secondFreeFront
      -- Explicit states keep these long witnesses cheap to elaborate when
      -- declaration caching is disabled; the checked edges are unchanged.
      abstract
        live-activation-path : V.Runs (at registered kActivationDone freeFront) liveActivationActions liveRestart
        live-activation-path = V.more {s = (at registered kActivationDone freeFront)} {t = (at registered down68 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a68)} reactEdge1 (V.more {s = (at registered down68 freeFront)} {t = (at registered down69 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a69)} reactEdge2 (V.more {s = (at registered down69 freeFront)} {t = (at registered down70 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.sampleTime 13))} reactEdge3 (V.more {s = (at registered down70 freeFront)} {t = (at registered down71 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a71)} reactEdge4 (V.more {s = (at registered down71 freeFront)} {t = (at registered down72 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a72)} reactEdge5 (V.more {s = (at registered down72 freeFront)} {t = (at registered down73 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.applyAt 13))} reactEdge6 (V.more {s = (at registered down73 freeFront)} {t = (at registered down74 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a74)} reactEdge7 (V.more {s = (at registered down74 freeFront)} {t = (at registered down75 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a75)} reactEdge8 (V.more {s = (at registered down75 freeFront)} {t = (at registered down76 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a76)} reactEdge9 (V.more {s = (at registered down76 freeFront)} {t = (at registered down77 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a77)} reactEdge10 (V.more {s = (at registered down77 freeFront)} {t = (at registered down78 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a78)} reactEdge11 (V.more {s = (at registered down78 freeFront)} {t = (at registered down79 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.sampleTime 14))} reactEdge12 (V.more {s = (at registered down79 freeFront)} {t = (at registered down80 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a80)} reactEdge13 (V.more {s = (at registered down80 freeFront)} {t = (at registered down81 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a81)} reactEdge14 (V.more {s = (at registered down81 freeFront)} {t = (at registered down82 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.applyAt 14))} reactEdge15 (V.more {s = (at registered down82 freeFront)} {t = (at registered down83 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a83)} reactEdge16 (V.more {s = (at registered down83 freeFront)} {t = (at registered down84 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a84)} reactEdge17 (V.more {s = (at registered down84 freeFront)} {t = (at registered down85 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a85)} reactEdge18 (V.more {s = (at registered down85 freeFront)} {t = (at registered down86 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a86)} reactEdge19 (V.more {s = (at registered down86 freeFront)} {t = (at registered down87 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.sampleTime 15))} reactEdge20 (V.more {s = (at registered down87 freeFront)} {t = (at registered down88 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a88)} reactEdge21 (V.more {s = (at registered down88 freeFront)} {t = (at registered down89 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a89)} reactEdge22 (V.more {s = (at registered down89 freeFront)} {t = (at registered down90 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.applyAt 15))} reactEdge23 (V.more {s = (at registered down90 freeFront)} {t = (at registered down91 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a91)} reactEdge24 (V.more {s = (at registered down91 freeFront)} {t = (at registered down92 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a92)} reactEdge25 (V.more {s = (at registered down92 freeFront)} {t = (at registered down93 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a93)} reactEdge26 (V.more {s = (at registered down93 freeFront)} {t = (at registered down94 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a94)} reactEdge27 (V.more {s = (at registered down94 freeFront)} {t = (at registered down95 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps L.a95)} reactEdge28 (V.more {s = (at registered down95 freeFront)} {t = (at registered warm1 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (V.waitJobResults (ident 2))} reactEdge29 (V.more {s = (at registered warm1 freeFront)} {t = (at registered warm2 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.enqueueCompletion (ident 2) 0))} reactEdge30 (V.more {s = (at registered warm2 freeFront)} {t = (at registered warm3 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.deregisterJob (ident 2)))} reactEdge31 (V.more {s = (at registered warm3 freeFront)} {t = (at registered warm4 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (peerStep (PS.run (GP.publishAsyncResult (ident 2))))} reactEdge32 (V.more {s = (at registered warm4 freeFront)} {t = (at registered warm5 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.finishLaunch)} reactEdge33 (V.more {s = (at registered warm5 freeFront)} {t = (at registered warm6 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.publishPublicState)} reactEdge34 (V.more {s = (at registered warm6 freeFront)} {t = (at registered warm7 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.sampleTime 16))} reactEdge35 (V.more {s = (at registered warm7 freeFront)} {t = (at registered warm8 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.registerWakeup)} reactEdge36 (V.more {s = (at registered warm8 freeFront)} {t = (at registered warm9 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.selectCompletion)} reactEdge37 (V.more {s = (at registered warm9 freeFront)} {t = (at registered warm10 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.applyAt 16))} reactEdge38 (V.more {s = (at registered warm10 freeFront)} {t = (at registered warm11 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.publishCounters)} reactEdge39 (V.more {s = (at registered warm11 freeFront)} {t = (at registered warm12 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.traceSelection)} reactEdge40 (V.more {s = (at registered warm12 freeFront)} {t = (at registered warm13 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.finishLaunch)} reactEdge41 (V.more {s = (at registered warm13 freeFront)} {t = (at registered warm14 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.setTargets (G.targets 1 1 1)))} reactEdge42 (V.more {s = (at registered warm14 freeFront)} {t = (at registered warm15 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.publishPublicState)} reactEdge43 (V.more {s = (at registered warm15 freeFront)} {t = (at registered warm16 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.sampleTime 17))} reactEdge44 (V.more {s = (at registered warm16 freeFront)} {t = (at registered warm17 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.registerWakeup)} reactEdge45 (V.more {s = (at registered warm17 freeFront)} {t = (at registered warm18 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.selectTargets)} reactEdge46 (V.more {s = (at registered warm18 freeFront)} {t = (at registered warm19 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.applyAt 17))} reactEdge47 (V.more {s = (at registered warm19 freeFront)} {t = (at registered warm20 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.publishCounters)} reactEdge48 (V.more {s = (at registered warm20 freeFront)} {t = (at registered warm21 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.traceSelection)} reactEdge49 (V.more {s = (at registered warm21 freeFront)} {t = (at registered warm22 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.finishLaunch)} reactEdge50 (V.more {s = (at registered warm22 freeFront)} {t = (at registered warm23 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.publishPublicState)} reactEdge51 (V.more {s = (at registered warm23 freeFront)} {t = (at registered warm24 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.sampleTime 18))} reactEdge52 (V.more {s = (at registered warm24 freeFront)} {t = (at registered warm25 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.registerWakeup)} reactEdge53 (V.more {s = (at registered warm25 freeFront)} {t = (at registered warm26 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.selectPolicy (L.peerAddr ∷ [])))} reactEdge54 (V.more {s = (at registered warm26 freeFront)} {t = (at registered warm27 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.applyAt 18))} reactEdge55 (V.more {s = (at registered warm27 freeFront)} {t = (at registered warm28 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.publishCounters)} reactEdge56 (V.more {s = (at registered warm28 freeFront)} {t = (at registered warm29 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.traceSelection)} reactEdge57 (V.more {s = (at registered warm29 freeFront)} {t = (at registered warm30 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.forkJob (ident 16) (ident 17) (ident 16)))} reactEdge58 (V.more {s = (at registered warm30 freeFront)} {t = (at registered warm31 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps Sub.registerJob)} reactEdge59 (V.more {s = (at registered warm31 freeFront)} {t = (at registered warm32 freeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.jobStep (ident 3) J.enter))} reactEdge60 (V.more {s = (at registered warm32 freeFront)} {t = (at registered secondStartedContext secondQueuedFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (V.startNext (ident 3) (ident 21))} reactEdge61 (V.more {s = (at registered secondStartedContext secondQueuedFront)} {t = (at registered secondTraversalContext secondQueuedFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.jobStep (ident 3) J.runNext))} reactEdge62 (V.more {s = (at registered secondTraversalContext secondQueuedFront)} {t = (at registered secondTraversalContext secondSelectedFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (V.selectStart A.child₀)} reactEdge63 (V.more {s = (at registered secondTraversalContext secondSelectedFront)} {t = (at registered secondTraversalContext secondTracingFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (V.invokeStartTrace A.child₀)} reactEdge64 (V.more {s = (at registered secondTraversalContext secondTracingFront)} {t = (at registered secondTraversalContext secondReadyFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (V.returnStartTrace A.child₀)} reactEdge65 (V.more {s = (at registered secondTraversalContext secondReadyFront)} {t = (at secondBorn secondTraversalContext secondBornFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (V.forkStart A.child₀ (ident 21))} reactEdge66 (V.more {s = (at secondBorn secondTraversalContext secondBornFront)} {t = (at secondRegistered secondTraversalContext secondFreeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (V.registerStart (ident 21))} reactEdge67 (V.more {s = (at secondRegistered secondTraversalContext secondFreeFront)} {t = (at secondRegistered secondPublishedContext secondFreeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.jobStep (ident 3) J.publishStarted))} reactEdge68 (V.more {s = (at secondRegistered secondPublishedContext secondFreeFront)} {t = (at secondRegistered secondReturnedContext secondFreeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.jobStep (ident 3) (J.finishHotAt 18)))} reactEdge69 (V.more {s = (at secondRegistered secondReturnedContext secondFreeFront)} {t = (at secondRegistered secondQueuedContext secondFreeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.enqueueCompletion (ident 3) 0))} reactEdge70 (V.more {s = (at secondRegistered secondQueuedContext secondFreeFront)} {t = (at secondRegistered secondRemovedContext secondFreeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (ps (Sub.deregisterJob (ident 3)))} reactEdge71 (V.more {s = (at secondRegistered secondRemovedContext secondFreeFront)} {t = (at secondRegistered secondDoneContext secondFreeFront)} {u = (at secondRegistered secondDoneContext secondFreeFront)} {a = (peerStep (PS.run (GP.publishAsyncResult (ident 3))))} reactEdge72 (V.stop {s = (at secondRegistered secondDoneContext secondFreeFront)}))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
        initialized-live-restart : V.Runs initial livePrefixActions liveRestart
        initialized-live-restart = Facts.append-protocols initialized-first-completed live-activation-path

      -- Only peer metadata differs from the previous scope-close profile.
      -- Historical completed governor jobs and the pending completion survive.
      peerGovClosing peerGovClosed peerScopes : C.Context
      peerGovClosing = record secondDoneContext
        { scopes = Fixtures.q8; governorPool = record activationDonePool { phase = GP.Pool.closing } }
      peerGovClosed = record peerGovClosing
        { governorPool = record activationDonePool { phase = GP.Pool.closedPool } }
      peerScopes = atScope Fixtures.q22 peerGovClosed
      peerMonClosing peerMonRequested peerMonDelivered peerMonUnwound peerMonRemoved peerMonPublished peerMonJoined peerFinished : C.Context
      peerMonClosing = record peerScopes { monitorPool = monClosing }
      peerMonRequested = record peerScopes { monitorPool = monRequested }
      peerMonDelivered = record peerScopes
        { monitorPool = monDelivered; monitors = (ident 50 , monitorThread PS.cancelling) ∷ [] }
      peerMonUnwound = withPeer (record secondPromotedPeer { monitorStarted = false })
        (record peerScopes { monitorPool = monUnwound; monitors = (ident 50 , monitorThread PS.exited) ∷ [] })
      peerMonRemoved = record peerMonUnwound { monitorPool = monRemoved }
      peerMonPublished = record peerMonUnwound { monitorPool = monPublished }
      peerMonJoined = record peerMonUnwound { monitorPool = monJoined }
      peerFinished = record peerMonUnwound { monitorPool = monClosed }
      stageScene : S.Stage → Bool → E.Exit → Y.Model → C.Context → V.Front → V.Runtime
      stageScene = SC.scene
      innerClosed callbackExited : V.Runtime
      innerClosed = at secondRegistered peerFinished secondFreeFront
      callbackExited = stageScene S.actionBodyExited true E.emptyExit secondRegistered peerFinished secondFreeFront

      peerCloseEdge1 : V.advance (scoped (Scope.beginUnwind)) (at secondRegistered secondDoneContext secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q1 secondDoneContext) secondFreeFront)
      peerCloseEdge1 = refl

      peerCloseEdge2 : V.advance (scoped (Scope.requestCancel)) (at secondRegistered (atScope Fixtures.q1 secondDoneContext) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q2 secondDoneContext) secondFreeFront)
      peerCloseEdge2 = refl

      peerCloseEdge3 : V.advance (scoped (Scope.deliverCancel)) (at secondRegistered (atScope Fixtures.q2 secondDoneContext) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q3 secondDoneContext) secondFreeFront)
      peerCloseEdge3 = refl

      peerCloseEdge4 : V.advance (scoped (Scope.bodyExit Scope.churn)) (at secondRegistered (atScope Fixtures.q3 secondDoneContext) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q4 secondDoneContext) secondFreeFront)
      peerCloseEdge4 = refl

      peerCloseEdge5 : V.advance (scoped (Scope.publishResult Scope.churn)) (at secondRegistered (atScope Fixtures.q4 secondDoneContext) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q5 secondDoneContext) secondFreeFront)
      peerCloseEdge5 = refl

      peerCloseEdge6 : V.advance (scoped (Scope.join)) (at secondRegistered (atScope Fixtures.q5 secondDoneContext) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q6 secondDoneContext) secondFreeFront)
      peerCloseEdge6 = refl

      peerCloseEdge7 : V.advance (scoped (Scope.requestCancel)) (at secondRegistered (atScope Fixtures.q6 secondDoneContext) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q7 secondDoneContext) secondFreeFront)
      peerCloseEdge7 = refl

      peerCloseEdge8 : V.advance (scoped (Scope.deliverCancel)) (at secondRegistered (atScope Fixtures.q7 secondDoneContext) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q8 secondDoneContext) secondFreeFront)
      peerCloseEdge8 = refl

      peerCloseEdge9 : V.advance (peerStep (PS.run (GP.beginClose []))) (at secondRegistered (atScope Fixtures.q8 secondDoneContext) secondFreeFront) ≡ just (at secondRegistered peerGovClosing secondFreeFront)
      peerCloseEdge9 = refl

      peerCloseEdge10 : V.advance (peerStep (PS.run GP.finishClose)) (at secondRegistered peerGovClosing secondFreeFront) ≡ just (at secondRegistered peerGovClosed secondFreeFront)
      peerCloseEdge10 = refl

      peerCloseEdge11 : V.advance (scoped (Scope.bodyExit Scope.governor)) (at secondRegistered peerGovClosed secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q9 peerGovClosed) secondFreeFront)
      peerCloseEdge11 = refl

      peerCloseEdge12 : V.advance (scoped (Scope.publishResult Scope.governor)) (at secondRegistered (atScope Fixtures.q9 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q10 peerGovClosed) secondFreeFront)
      peerCloseEdge12 = refl

      peerCloseEdge13 : V.advance (scoped (Scope.join)) (at secondRegistered (atScope Fixtures.q10 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q11 peerGovClosed) secondFreeFront)
      peerCloseEdge13 = refl

      peerCloseEdge14 : V.advance (scoped (Scope.requestCancel)) (at secondRegistered (atScope Fixtures.q11 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q12 peerGovClosed) secondFreeFront)
      peerCloseEdge14 = refl

      peerCloseEdge15 : V.advance (scoped (Scope.deliverCancel)) (at secondRegistered (atScope Fixtures.q12 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q13 peerGovClosed) secondFreeFront)
      peerCloseEdge15 = refl

      peerCloseEdge16 : V.advance (scoped (Scope.bodyExit Scope.localRoot)) (at secondRegistered (atScope Fixtures.q13 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q14 peerGovClosed) secondFreeFront)
      peerCloseEdge16 = refl

      peerCloseEdge17 : V.advance (scoped (Scope.publishResult Scope.localRoot)) (at secondRegistered (atScope Fixtures.q14 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q15 peerGovClosed) secondFreeFront)
      peerCloseEdge17 = refl

      peerCloseEdge18 : V.advance (scoped (Scope.join)) (at secondRegistered (atScope Fixtures.q15 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q16 peerGovClosed) secondFreeFront)
      peerCloseEdge18 = refl

      peerCloseEdge19 : V.advance (scoped (Scope.requestCancel)) (at secondRegistered (atScope Fixtures.q16 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q17 peerGovClosed) secondFreeFront)
      peerCloseEdge19 = refl

      peerCloseEdge20 : V.advance (scoped (Scope.deliverCancel)) (at secondRegistered (atScope Fixtures.q17 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q18 peerGovClosed) secondFreeFront)
      peerCloseEdge20 = refl

      peerCloseEdge21 : V.advance (scoped (Scope.bodyExit Scope.ledger)) (at secondRegistered (atScope Fixtures.q18 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q19 peerGovClosed) secondFreeFront)
      peerCloseEdge21 = refl

      peerCloseEdge22 : V.advance (scoped (Scope.publishResult Scope.ledger)) (at secondRegistered (atScope Fixtures.q19 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q20 peerGovClosed) secondFreeFront)
      peerCloseEdge22 = refl

      peerCloseEdge23 : V.advance (scoped (Scope.join)) (at secondRegistered (atScope Fixtures.q20 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q21 peerGovClosed) secondFreeFront)
      peerCloseEdge23 = refl

      peerCloseEdge24 : V.advance (scoped (Scope.finishClose)) (at secondRegistered (atScope Fixtures.q21 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered (atScope Fixtures.q22 peerGovClosed) secondFreeFront)
      peerCloseEdge24 = refl

      peerCloseEdge25 : V.advance (peerStep (PS.beginMonitorClose (ident 50 ∷ []))) (at secondRegistered (atScope Fixtures.q22 peerGovClosed) secondFreeFront) ≡ just (at secondRegistered peerMonClosing secondFreeFront)
      peerCloseEdge25 = refl

      peerCloseEdge26 : V.advance (peerStep (PS.requestMonitorCancel)) (at secondRegistered peerMonClosing secondFreeFront) ≡ just (at secondRegistered peerMonRequested secondFreeFront)
      peerCloseEdge26 = refl

      peerCloseEdge27 : V.advance (peerStep (PS.deliverMonitorCancellation (errorId 172))) (at secondRegistered peerMonRequested secondFreeFront) ≡ just (at secondRegistered peerMonDelivered secondFreeFront)
      peerCloseEdge27 = refl

      peerCloseEdge28 : V.advance (peerStep (PS.monitorBodyUnwound (ident 50))) (at secondRegistered peerMonDelivered secondFreeFront) ≡ just (at secondRegistered peerMonUnwound secondFreeFront)
      peerCloseEdge28 = refl

      peerCloseEdge29 : V.advance (peerStep (PS.deregisterMonitor (ident 50))) (at secondRegistered peerMonUnwound secondFreeFront) ≡ just (at secondRegistered peerMonRemoved secondFreeFront)
      peerCloseEdge29 = refl

      peerCloseEdge30 : V.advance (peerStep (PS.publishMonitorResult (ident 50))) (at secondRegistered peerMonRemoved secondFreeFront) ≡ just (at secondRegistered peerMonPublished secondFreeFront)
      peerCloseEdge30 = refl

      peerCloseEdge31 : V.advance (peerStep (PS.joinMonitor)) (at secondRegistered peerMonPublished secondFreeFront) ≡ just (at secondRegistered peerMonJoined secondFreeFront)
      peerCloseEdge31 = refl

      peerCloseEdge32 : V.advance (peerStep (PS.finishMonitorClose)) (at secondRegistered peerMonJoined secondFreeFront) ≡ just (at secondRegistered peerFinished secondFreeFront)
      peerCloseEdge32 = refl

      peerCloseEdge33 : V.advance (V.dispatch (K.serverStep (E.run (S.scope S.returnAction)))) (at secondRegistered peerFinished secondFreeFront) ≡ just (callbackExited)
      peerCloseEdge33 = refl

      peerCloseActions : List V.Event
      peerCloseActions = ((scoped (Scope.beginUnwind))) ∷ ((scoped (Scope.requestCancel))) ∷ ((scoped (Scope.deliverCancel))) ∷ ((scoped (Scope.bodyExit Scope.churn))) ∷ ((scoped (Scope.publishResult Scope.churn))) ∷ ((scoped (Scope.join))) ∷ ((scoped (Scope.requestCancel))) ∷ ((scoped (Scope.deliverCancel))) ∷ ((peerStep (PS.run (GP.beginClose [])))) ∷ ((peerStep (PS.run GP.finishClose))) ∷ ((scoped (Scope.bodyExit Scope.governor))) ∷ ((scoped (Scope.publishResult Scope.governor))) ∷ ((scoped (Scope.join))) ∷ ((scoped (Scope.requestCancel))) ∷ ((scoped (Scope.deliverCancel))) ∷ ((scoped (Scope.bodyExit Scope.localRoot))) ∷ ((scoped (Scope.publishResult Scope.localRoot))) ∷ ((scoped (Scope.join))) ∷ ((scoped (Scope.requestCancel))) ∷ ((scoped (Scope.deliverCancel))) ∷ ((scoped (Scope.bodyExit Scope.ledger))) ∷ ((scoped (Scope.publishResult Scope.ledger))) ∷ ((scoped (Scope.join))) ∷ ((scoped (Scope.finishClose))) ∷ ((peerStep (PS.beginMonitorClose (ident 50 ∷ [])))) ∷ ((peerStep (PS.requestMonitorCancel))) ∷ ((peerStep (PS.deliverMonitorCancellation (errorId 172)))) ∷ ((peerStep (PS.monitorBodyUnwound (ident 50)))) ∷ ((peerStep (PS.deregisterMonitor (ident 50)))) ∷ ((peerStep (PS.publishMonitorResult (ident 50)))) ∷ ((peerStep (PS.joinMonitor))) ∷ ((peerStep (PS.finishMonitorClose))) ∷ ((V.dispatch (K.serverStep (E.run (S.scope S.returnAction))))) ∷ []
      abstract
        peer-close-path : V.Runs liveRestart peerCloseActions callbackExited
        peer-close-path = V.more {s = (at secondRegistered secondDoneContext secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q1 secondDoneContext) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.beginUnwind))} peerCloseEdge1 (V.more {s = (at secondRegistered (atScope Fixtures.q1 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q2 secondDoneContext) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.requestCancel))} peerCloseEdge2 (V.more {s = (at secondRegistered (atScope Fixtures.q2 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q3 secondDoneContext) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge3 (V.more {s = (at secondRegistered (atScope Fixtures.q3 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q4 secondDoneContext) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.bodyExit Scope.churn))} peerCloseEdge4 (V.more {s = (at secondRegistered (atScope Fixtures.q4 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q5 secondDoneContext) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.publishResult Scope.churn))} peerCloseEdge5 (V.more {s = (at secondRegistered (atScope Fixtures.q5 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q6 secondDoneContext) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.join))} peerCloseEdge6 (V.more {s = (at secondRegistered (atScope Fixtures.q6 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q7 secondDoneContext) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.requestCancel))} peerCloseEdge7 (V.more {s = (at secondRegistered (atScope Fixtures.q7 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q8 secondDoneContext) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge8 (V.more {s = (at secondRegistered (atScope Fixtures.q8 secondDoneContext) secondFreeFront)} {t = (at secondRegistered peerGovClosing secondFreeFront)} {u = (callbackExited)} {a = (peerStep (PS.run (GP.beginClose [])))} peerCloseEdge9 (V.more {s = (at secondRegistered peerGovClosing secondFreeFront)} {t = (at secondRegistered peerGovClosed secondFreeFront)} {u = (callbackExited)} {a = (peerStep (PS.run GP.finishClose))} peerCloseEdge10 (V.more {s = (at secondRegistered peerGovClosed secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q9 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.bodyExit Scope.governor))} peerCloseEdge11 (V.more {s = (at secondRegistered (atScope Fixtures.q9 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q10 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.publishResult Scope.governor))} peerCloseEdge12 (V.more {s = (at secondRegistered (atScope Fixtures.q10 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q11 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.join))} peerCloseEdge13 (V.more {s = (at secondRegistered (atScope Fixtures.q11 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q12 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.requestCancel))} peerCloseEdge14 (V.more {s = (at secondRegistered (atScope Fixtures.q12 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q13 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge15 (V.more {s = (at secondRegistered (atScope Fixtures.q13 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q14 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.bodyExit Scope.localRoot))} peerCloseEdge16 (V.more {s = (at secondRegistered (atScope Fixtures.q14 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q15 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.publishResult Scope.localRoot))} peerCloseEdge17 (V.more {s = (at secondRegistered (atScope Fixtures.q15 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q16 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.join))} peerCloseEdge18 (V.more {s = (at secondRegistered (atScope Fixtures.q16 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q17 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.requestCancel))} peerCloseEdge19 (V.more {s = (at secondRegistered (atScope Fixtures.q17 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q18 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge20 (V.more {s = (at secondRegistered (atScope Fixtures.q18 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q19 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.bodyExit Scope.ledger))} peerCloseEdge21 (V.more {s = (at secondRegistered (atScope Fixtures.q19 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q20 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.publishResult Scope.ledger))} peerCloseEdge22 (V.more {s = (at secondRegistered (atScope Fixtures.q20 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q21 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.join))} peerCloseEdge23 (V.more {s = (at secondRegistered (atScope Fixtures.q21 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q22 peerGovClosed) secondFreeFront)} {u = (callbackExited)} {a = (scoped (Scope.finishClose))} peerCloseEdge24 (V.more {s = (at secondRegistered (atScope Fixtures.q22 peerGovClosed) secondFreeFront)} {t = (at secondRegistered peerMonClosing secondFreeFront)} {u = (callbackExited)} {a = (peerStep (PS.beginMonitorClose (ident 50 ∷ [])))} peerCloseEdge25 (V.more {s = (at secondRegistered peerMonClosing secondFreeFront)} {t = (at secondRegistered peerMonRequested secondFreeFront)} {u = (callbackExited)} {a = (peerStep (PS.requestMonitorCancel))} peerCloseEdge26 (V.more {s = (at secondRegistered peerMonRequested secondFreeFront)} {t = (at secondRegistered peerMonDelivered secondFreeFront)} {u = (callbackExited)} {a = (peerStep (PS.deliverMonitorCancellation (errorId 172)))} peerCloseEdge27 (V.more {s = (at secondRegistered peerMonDelivered secondFreeFront)} {t = (at secondRegistered peerMonUnwound secondFreeFront)} {u = (callbackExited)} {a = (peerStep (PS.monitorBodyUnwound (ident 50)))} peerCloseEdge28 (V.more {s = (at secondRegistered peerMonUnwound secondFreeFront)} {t = (at secondRegistered peerMonRemoved secondFreeFront)} {u = (callbackExited)} {a = (peerStep (PS.deregisterMonitor (ident 50)))} peerCloseEdge29 (V.more {s = (at secondRegistered peerMonRemoved secondFreeFront)} {t = (at secondRegistered peerMonPublished secondFreeFront)} {u = (callbackExited)} {a = (peerStep (PS.publishMonitorResult (ident 50)))} peerCloseEdge30 (V.more {s = (at secondRegistered peerMonPublished secondFreeFront)} {t = (at secondRegistered peerMonJoined secondFreeFront)} {u = (callbackExited)} {a = (peerStep (PS.joinMonitor))} peerCloseEdge31 (V.more {s = (at secondRegistered peerMonJoined secondFreeFront)} {t = (at secondRegistered peerFinished secondFreeFront)} {u = (callbackExited)} {a = (peerStep (PS.finishMonitorClose))} peerCloseEdge32 (V.more {s = (at secondRegistered peerFinished secondFreeFront)} {t = (callbackExited)} {u = (callbackExited)} {a = (V.dispatch (K.serverStep (E.run (S.scope S.returnAction))))} peerCloseEdge33 (V.stop {s = (callbackExited)})))))))))))))))))))))))))))))))))
        initialized-peer-close : V.Runs initial (livePrefixActions ++ peerCloseActions) callbackExited
        initialized-peer-close = Facts.append-protocols initialized-live-restart peer-close-path
      open import Data.List using (take)
      peerBeforeCallbackActions : List V.Event
      peerBeforeCallbackActions = take 32 peerCloseActions
      abstract
        restarted-before-callback : V.Runs initial (livePrefixActions ++ peerBeforeCallbackActions) innerClosed
        restarted-before-callback = Facts.append-protocols initialized-live-restart (V.more {s = (at secondRegistered secondDoneContext secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q1 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.beginUnwind))} peerCloseEdge1 (V.more {s = (at secondRegistered (atScope Fixtures.q1 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q2 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.requestCancel))} peerCloseEdge2 (V.more {s = (at secondRegistered (atScope Fixtures.q2 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q3 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge3 (V.more {s = (at secondRegistered (atScope Fixtures.q3 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q4 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.bodyExit Scope.churn))} peerCloseEdge4 (V.more {s = (at secondRegistered (atScope Fixtures.q4 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q5 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.publishResult Scope.churn))} peerCloseEdge5 (V.more {s = (at secondRegistered (atScope Fixtures.q5 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q6 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.join))} peerCloseEdge6 (V.more {s = (at secondRegistered (atScope Fixtures.q6 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q7 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.requestCancel))} peerCloseEdge7 (V.more {s = (at secondRegistered (atScope Fixtures.q7 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q8 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge8 (V.more {s = (at secondRegistered (atScope Fixtures.q8 secondDoneContext) secondFreeFront)} {t = (at secondRegistered peerGovClosing secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (peerStep (PS.run (GP.beginClose [])))} peerCloseEdge9 (V.more {s = (at secondRegistered peerGovClosing secondFreeFront)} {t = (at secondRegistered peerGovClosed secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (peerStep (PS.run GP.finishClose))} peerCloseEdge10 (V.more {s = (at secondRegistered peerGovClosed secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q9 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.bodyExit Scope.governor))} peerCloseEdge11 (V.more {s = (at secondRegistered (atScope Fixtures.q9 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q10 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.publishResult Scope.governor))} peerCloseEdge12 (V.more {s = (at secondRegistered (atScope Fixtures.q10 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q11 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.join))} peerCloseEdge13 (V.more {s = (at secondRegistered (atScope Fixtures.q11 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q12 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.requestCancel))} peerCloseEdge14 (V.more {s = (at secondRegistered (atScope Fixtures.q12 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q13 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge15 (V.more {s = (at secondRegistered (atScope Fixtures.q13 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q14 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.bodyExit Scope.localRoot))} peerCloseEdge16 (V.more {s = (at secondRegistered (atScope Fixtures.q14 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q15 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.publishResult Scope.localRoot))} peerCloseEdge17 (V.more {s = (at secondRegistered (atScope Fixtures.q15 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q16 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.join))} peerCloseEdge18 (V.more {s = (at secondRegistered (atScope Fixtures.q16 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q17 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.requestCancel))} peerCloseEdge19 (V.more {s = (at secondRegistered (atScope Fixtures.q17 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q18 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge20 (V.more {s = (at secondRegistered (atScope Fixtures.q18 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q19 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.bodyExit Scope.ledger))} peerCloseEdge21 (V.more {s = (at secondRegistered (atScope Fixtures.q19 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q20 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.publishResult Scope.ledger))} peerCloseEdge22 (V.more {s = (at secondRegistered (atScope Fixtures.q20 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q21 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.join))} peerCloseEdge23 (V.more {s = (at secondRegistered (atScope Fixtures.q21 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q22 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (scoped (Scope.finishClose))} peerCloseEdge24 (V.more {s = (at secondRegistered (atScope Fixtures.q22 peerGovClosed) secondFreeFront)} {t = (at secondRegistered peerMonClosing secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (peerStep (PS.beginMonitorClose (ident 50 ∷ [])))} peerCloseEdge25 (V.more {s = (at secondRegistered peerMonClosing secondFreeFront)} {t = (at secondRegistered peerMonRequested secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (peerStep (PS.requestMonitorCancel))} peerCloseEdge26 (V.more {s = (at secondRegistered peerMonRequested secondFreeFront)} {t = (at secondRegistered peerMonDelivered secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (peerStep (PS.deliverMonitorCancellation (errorId 172)))} peerCloseEdge27 (V.more {s = (at secondRegistered peerMonDelivered secondFreeFront)} {t = (at secondRegistered peerMonUnwound secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (peerStep (PS.monitorBodyUnwound (ident 50)))} peerCloseEdge28 (V.more {s = (at secondRegistered peerMonUnwound secondFreeFront)} {t = (at secondRegistered peerMonRemoved secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (peerStep (PS.deregisterMonitor (ident 50)))} peerCloseEdge29 (V.more {s = (at secondRegistered peerMonRemoved secondFreeFront)} {t = (at secondRegistered peerMonPublished secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (peerStep (PS.publishMonitorResult (ident 50)))} peerCloseEdge30 (V.more {s = (at secondRegistered peerMonPublished secondFreeFront)} {t = (at secondRegistered peerMonJoined secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (peerStep (PS.joinMonitor))} peerCloseEdge31 (V.more {s = (at secondRegistered peerMonJoined secondFreeFront)} {t = (at secondRegistered peerFinished secondFreeFront)} {u = (at secondRegistered peerFinished secondFreeFront)} {a = (peerStep (PS.finishMonitorClose))} peerCloseEdge32 (V.stop {s = (at secondRegistered peerFinished secondFreeFront)})))))))))))))))))))))))))))))))))
      callback-certificates-restarted : BFacts.Certificates (V.base innerClosed)
      callback-certificates-restarted = Facts.callback-from-protocols initializer restarted-before-callback peerCloseEdge33

      -- An actual initialized prefix ending immediately before the monitor join.
      open import Data.List using (take)
      abstract
        before-monitor-join : V.Runs liveRestart (take 30 peerCloseActions) (at secondRegistered peerMonPublished secondFreeFront)
        before-monitor-join = V.more {s = (at secondRegistered secondDoneContext secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q1 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.beginUnwind))} peerCloseEdge1 (V.more {s = (at secondRegistered (atScope Fixtures.q1 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q2 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.requestCancel))} peerCloseEdge2 (V.more {s = (at secondRegistered (atScope Fixtures.q2 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q3 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge3 (V.more {s = (at secondRegistered (atScope Fixtures.q3 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q4 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.bodyExit Scope.churn))} peerCloseEdge4 (V.more {s = (at secondRegistered (atScope Fixtures.q4 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q5 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.publishResult Scope.churn))} peerCloseEdge5 (V.more {s = (at secondRegistered (atScope Fixtures.q5 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q6 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.join))} peerCloseEdge6 (V.more {s = (at secondRegistered (atScope Fixtures.q6 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q7 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.requestCancel))} peerCloseEdge7 (V.more {s = (at secondRegistered (atScope Fixtures.q7 secondDoneContext) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q8 secondDoneContext) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge8 (V.more {s = (at secondRegistered (atScope Fixtures.q8 secondDoneContext) secondFreeFront)} {t = (at secondRegistered peerGovClosing secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (peerStep (PS.run (GP.beginClose [])))} peerCloseEdge9 (V.more {s = (at secondRegistered peerGovClosing secondFreeFront)} {t = (at secondRegistered peerGovClosed secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (peerStep (PS.run GP.finishClose))} peerCloseEdge10 (V.more {s = (at secondRegistered peerGovClosed secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q9 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.bodyExit Scope.governor))} peerCloseEdge11 (V.more {s = (at secondRegistered (atScope Fixtures.q9 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q10 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.publishResult Scope.governor))} peerCloseEdge12 (V.more {s = (at secondRegistered (atScope Fixtures.q10 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q11 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.join))} peerCloseEdge13 (V.more {s = (at secondRegistered (atScope Fixtures.q11 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q12 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.requestCancel))} peerCloseEdge14 (V.more {s = (at secondRegistered (atScope Fixtures.q12 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q13 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge15 (V.more {s = (at secondRegistered (atScope Fixtures.q13 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q14 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.bodyExit Scope.localRoot))} peerCloseEdge16 (V.more {s = (at secondRegistered (atScope Fixtures.q14 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q15 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.publishResult Scope.localRoot))} peerCloseEdge17 (V.more {s = (at secondRegistered (atScope Fixtures.q15 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q16 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.join))} peerCloseEdge18 (V.more {s = (at secondRegistered (atScope Fixtures.q16 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q17 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.requestCancel))} peerCloseEdge19 (V.more {s = (at secondRegistered (atScope Fixtures.q17 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q18 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.deliverCancel))} peerCloseEdge20 (V.more {s = (at secondRegistered (atScope Fixtures.q18 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q19 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.bodyExit Scope.ledger))} peerCloseEdge21 (V.more {s = (at secondRegistered (atScope Fixtures.q19 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q20 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.publishResult Scope.ledger))} peerCloseEdge22 (V.more {s = (at secondRegistered (atScope Fixtures.q20 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q21 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.join))} peerCloseEdge23 (V.more {s = (at secondRegistered (atScope Fixtures.q21 peerGovClosed) secondFreeFront)} {t = (at secondRegistered (atScope Fixtures.q22 peerGovClosed) secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (scoped (Scope.finishClose))} peerCloseEdge24 (V.more {s = (at secondRegistered (atScope Fixtures.q22 peerGovClosed) secondFreeFront)} {t = (at secondRegistered peerMonClosing secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (peerStep (PS.beginMonitorClose (ident 50 ∷ [])))} peerCloseEdge25 (V.more {s = (at secondRegistered peerMonClosing secondFreeFront)} {t = (at secondRegistered peerMonRequested secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (peerStep (PS.requestMonitorCancel))} peerCloseEdge26 (V.more {s = (at secondRegistered peerMonRequested secondFreeFront)} {t = (at secondRegistered peerMonDelivered secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (peerStep (PS.deliverMonitorCancellation (errorId 172)))} peerCloseEdge27 (V.more {s = (at secondRegistered peerMonDelivered secondFreeFront)} {t = (at secondRegistered peerMonUnwound secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (peerStep (PS.monitorBodyUnwound (ident 50)))} peerCloseEdge28 (V.more {s = (at secondRegistered peerMonUnwound secondFreeFront)} {t = (at secondRegistered peerMonRemoved secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (peerStep (PS.deregisterMonitor (ident 50)))} peerCloseEdge29 (V.more {s = (at secondRegistered peerMonRemoved secondFreeFront)} {t = (at secondRegistered peerMonPublished secondFreeFront)} {u = (at secondRegistered peerMonPublished secondFreeFront)} {a = (peerStep (PS.publishMonitorResult (ident 50)))} peerCloseEdge30 (V.stop {s = (at secondRegistered peerMonPublished secondFreeFront)}))))))))))))))))))))))))))))))
        initialized-before-monitor-join : V.Runs initial (livePrefixActions ++ take 30 peerCloseActions) (at secondRegistered peerMonPublished secondFreeFront)
        initialized-before-monitor-join = Facts.append-protocols
          {s = initial} {t = liveRestart} {u = (at secondRegistered peerMonPublished secondFreeFront)} initialized-live-restart before-monitor-join

      -- IG exits independently of the two initiator generations. Its actual
      -- nonempty snapshot and inactive flag are retained through CM cleanup.
      inactiveModel exitedModel : Y.Model
      -- Keep the actual governor (including mux egress); change only the IG
      -- continuation/activity fields written by deactivation and flush.
      inactiveModel = record secondRegistered { governor = record (Y.governor secondRegistered)
        { continuation = IG.exitFlush; execution = record (IG.execution (Y.governor secondRegistered)) { active = false } } }
      exitedModel = record inactiveModel { governor = record (Y.governor inactiveModel) { continuation = IG.exited } }

      serverCloseEdge1 : V.advance (SC.serverEvent S.publishActionResult) (stageScene S.actionBodyExited true E.emptyExit secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.actionResultAvailable true E.emptyExit secondRegistered peerFinished secondFreeFront)
      serverCloseEdge1 = refl

      serverCloseEdge2 : V.advance (SC.serverEvent S.selectActionWinner) (stageScene S.actionResultAvailable true E.emptyExit secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.closingAccept true E.emptyExit secondRegistered peerFinished secondFreeFront)
      serverCloseEdge2 = refl

      serverCloseEdge3 : V.advance (SC.serverEvent S.requestAcceptCancel) (stageScene S.closingAccept true E.emptyExit secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.acceptCancelRequested true E.emptyExit secondRegistered peerFinished secondFreeFront)
      serverCloseEdge3 = refl

      serverCloseEdge4 : V.advance (SC.serverEvent S.deliverAcceptAtWait) (stageScene S.acceptCancelRequested true E.emptyExit secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.acceptCancelDelivered true E.emptyExit secondRegistered peerFinished secondFreeFront)
      serverCloseEdge4 = refl

      serverCloseEdge5 : V.advance (SC.serverEvent S.closeListener) (stageScene S.acceptCancelDelivered true E.emptyExit secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.acceptBodyExited false E.emptyExit secondRegistered peerFinished secondFreeFront)
      serverCloseEdge5 = refl

      serverCloseEdge6 : V.advance (SC.serverEvent S.publishAcceptResult) (stageScene S.acceptBodyExited false E.emptyExit secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.acceptResultAvailable false E.emptyExit secondRegistered peerFinished secondFreeFront)
      serverCloseEdge6 = refl

      serverCloseEdge7 : V.advance (SC.serverEvent S.joinAccept) (stageScene S.acceptResultAvailable false E.emptyExit secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.acceptJoined false E.emptyExit secondRegistered peerFinished secondFreeFront)
      serverCloseEdge7 = refl

      serverCloseEdge8 : V.advance (SC.serverEvent S.traceStopped) (stageScene S.acceptJoined false E.emptyExit secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.serverStopped false E.emptyExit secondRegistered peerFinished secondFreeFront)
      serverCloseEdge8 = refl

      serverCloseEdge9 : V.advance (SC.serverEvent S.cancelJoinReturnedAction) (stageScene S.serverStopped false E.emptyExit secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.actionJoined false E.emptyExit secondRegistered peerFinished secondFreeFront)
      serverCloseEdge9 = refl

      serverCloseEdge10 : V.advance (SC.serverEvent S.requestIGCancel) (stageScene S.actionJoined false E.emptyExit secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.igCancelRequested false E.emptyExit secondRegistered peerFinished secondFreeFront)
      serverCloseEdge10 = refl

      serverCloseEdge11 : V.advance (SC.exitEvent (E.receive E.loopBoundary SC.igError)) (stageScene S.igCancelRequested false E.emptyExit secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.igCancelDelivered false SC.caughtIG secondRegistered peerFinished secondFreeFront)
      serverCloseEdge11 = refl

      serverCloseEdge12 : V.advance (SC.serverEvent S.deactivateIG) (stageScene S.igCancelDelivered false SC.caughtIG secondRegistered peerFinished secondFreeFront) ≡ just (stageScene S.igInactive false SC.caughtIG inactiveModel peerFinished secondFreeFront)
      serverCloseEdge12 = refl

      serverCloseEdge13 : V.advance (SC.serverEvent S.flushIG) (stageScene S.igInactive false SC.caughtIG inactiveModel peerFinished secondFreeFront) ≡ just (stageScene S.igFlushed false SC.caughtIG exitedModel peerFinished secondFreeFront)
      serverCloseEdge13 = refl

      serverCloseEdge14 : V.advance (SC.exitEvent E.captureSnapshot) (stageScene S.igFlushed false SC.caughtIG exitedModel peerFinished secondFreeFront) ≡ just (stageScene S.igFlushed false SC.snapshotIG exitedModel peerFinished secondFreeFront)
      serverCloseEdge14 = refl

      serverCloseEdge15 : V.advance (SC.exitEvent E.invokeFinal) (stageScene S.igFlushed false SC.snapshotIG exitedModel peerFinished secondFreeFront) ≡ just (stageScene S.igFlushed false SC.invokedIG exitedModel peerFinished secondFreeFront)
      serverCloseEdge15 = refl

      serverCloseEdge16 : V.advance (SC.exitEvent E.returnFinal) (stageScene S.igFlushed false SC.invokedIG exitedModel peerFinished secondFreeFront) ≡ just (stageScene S.igFlushed false SC.returnedIG exitedModel peerFinished secondFreeFront)
      serverCloseEdge16 = refl

      serverCloseEdge17 : V.advance (SC.exitEvent E.finishFinal) (stageScene S.igFlushed false SC.returnedIG exitedModel peerFinished secondFreeFront) ≡ just (stageScene S.igBodyExited false SC.finishedIG exitedModel peerFinished secondFreeFront)
      serverCloseEdge17 = refl

      serverCloseEdge18 : V.advance (SC.serverEvent S.publishIGResult) (stageScene S.igBodyExited false SC.finishedIG exitedModel peerFinished secondFreeFront) ≡ just (stageScene S.igResultAvailable false SC.publishedIG exitedModel peerFinished secondFreeFront)
      serverCloseEdge18 = refl

      serverCloseEdge19 : V.advance (SC.serverEvent S.joinIG) (stageScene S.igResultAvailable false SC.publishedIG exitedModel peerFinished secondFreeFront) ≡ just (stageScene S.igJoined false SC.publishedIG exitedModel peerFinished secondFreeFront)
      serverCloseEdge19 = refl

      serverCloseEdge20 : V.advance (SC.serverEvent S.beginCM) (stageScene S.igJoined false SC.publishedIG exitedModel peerFinished secondFreeFront) ≡ just (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)
      serverCloseEdge20 = refl

      cmEntry : V.Runtime
      cmEntry = stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront
      serverCloseActions : List V.Event
      serverCloseActions = ((SC.serverEvent S.publishActionResult)) ∷ ((SC.serverEvent S.selectActionWinner)) ∷ ((SC.serverEvent S.requestAcceptCancel)) ∷ ((SC.serverEvent S.deliverAcceptAtWait)) ∷ ((SC.serverEvent S.closeListener)) ∷ ((SC.serverEvent S.publishAcceptResult)) ∷ ((SC.serverEvent S.joinAccept)) ∷ ((SC.serverEvent S.traceStopped)) ∷ ((SC.serverEvent S.cancelJoinReturnedAction)) ∷ ((SC.serverEvent S.requestIGCancel)) ∷ ((SC.exitEvent (E.receive E.loopBoundary SC.igError))) ∷ ((SC.serverEvent S.deactivateIG)) ∷ ((SC.serverEvent S.flushIG)) ∷ ((SC.exitEvent E.captureSnapshot)) ∷ ((SC.exitEvent E.invokeFinal)) ∷ ((SC.exitEvent E.returnFinal)) ∷ ((SC.exitEvent E.finishFinal)) ∷ ((SC.serverEvent S.publishIGResult)) ∷ ((SC.serverEvent S.joinIG)) ∷ ((SC.serverEvent S.beginCM)) ∷ []
      abstract
        server-close-path : V.Runs callbackExited serverCloseActions cmEntry
        server-close-path = V.more {s = (stageScene S.actionBodyExited true E.emptyExit secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.actionResultAvailable true E.emptyExit secondRegistered peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.publishActionResult)} serverCloseEdge1 (V.more {s = (stageScene S.actionResultAvailable true E.emptyExit secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.closingAccept true E.emptyExit secondRegistered peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.selectActionWinner)} serverCloseEdge2 (V.more {s = (stageScene S.closingAccept true E.emptyExit secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.acceptCancelRequested true E.emptyExit secondRegistered peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.requestAcceptCancel)} serverCloseEdge3 (V.more {s = (stageScene S.acceptCancelRequested true E.emptyExit secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.acceptCancelDelivered true E.emptyExit secondRegistered peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.deliverAcceptAtWait)} serverCloseEdge4 (V.more {s = (stageScene S.acceptCancelDelivered true E.emptyExit secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.acceptBodyExited false E.emptyExit secondRegistered peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.closeListener)} serverCloseEdge5 (V.more {s = (stageScene S.acceptBodyExited false E.emptyExit secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.acceptResultAvailable false E.emptyExit secondRegistered peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.publishAcceptResult)} serverCloseEdge6 (V.more {s = (stageScene S.acceptResultAvailable false E.emptyExit secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.acceptJoined false E.emptyExit secondRegistered peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.joinAccept)} serverCloseEdge7 (V.more {s = (stageScene S.acceptJoined false E.emptyExit secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.serverStopped false E.emptyExit secondRegistered peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.traceStopped)} serverCloseEdge8 (V.more {s = (stageScene S.serverStopped false E.emptyExit secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.actionJoined false E.emptyExit secondRegistered peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.cancelJoinReturnedAction)} serverCloseEdge9 (V.more {s = (stageScene S.actionJoined false E.emptyExit secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.igCancelRequested false E.emptyExit secondRegistered peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.requestIGCancel)} serverCloseEdge10 (V.more {s = (stageScene S.igCancelRequested false E.emptyExit secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.igCancelDelivered false SC.caughtIG secondRegistered peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.exitEvent (E.receive E.loopBoundary SC.igError))} serverCloseEdge11 (V.more {s = (stageScene S.igCancelDelivered false SC.caughtIG secondRegistered peerFinished secondFreeFront)} {t = (stageScene S.igInactive false SC.caughtIG inactiveModel peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.deactivateIG)} serverCloseEdge12 (V.more {s = (stageScene S.igInactive false SC.caughtIG inactiveModel peerFinished secondFreeFront)} {t = (stageScene S.igFlushed false SC.caughtIG exitedModel peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.flushIG)} serverCloseEdge13 (V.more {s = (stageScene S.igFlushed false SC.caughtIG exitedModel peerFinished secondFreeFront)} {t = (stageScene S.igFlushed false SC.snapshotIG exitedModel peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.exitEvent E.captureSnapshot)} serverCloseEdge14 (V.more {s = (stageScene S.igFlushed false SC.snapshotIG exitedModel peerFinished secondFreeFront)} {t = (stageScene S.igFlushed false SC.invokedIG exitedModel peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.exitEvent E.invokeFinal)} serverCloseEdge15 (V.more {s = (stageScene S.igFlushed false SC.invokedIG exitedModel peerFinished secondFreeFront)} {t = (stageScene S.igFlushed false SC.returnedIG exitedModel peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.exitEvent E.returnFinal)} serverCloseEdge16 (V.more {s = (stageScene S.igFlushed false SC.returnedIG exitedModel peerFinished secondFreeFront)} {t = (stageScene S.igBodyExited false SC.finishedIG exitedModel peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.exitEvent E.finishFinal)} serverCloseEdge17 (V.more {s = (stageScene S.igBodyExited false SC.finishedIG exitedModel peerFinished secondFreeFront)} {t = (stageScene S.igResultAvailable false SC.publishedIG exitedModel peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.publishIGResult)} serverCloseEdge18 (V.more {s = (stageScene S.igResultAvailable false SC.publishedIG exitedModel peerFinished secondFreeFront)} {t = (stageScene S.igJoined false SC.publishedIG exitedModel peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.joinIG)} serverCloseEdge19 (V.more {s = (stageScene S.igJoined false SC.publishedIG exitedModel peerFinished secondFreeFront)} {t = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {u = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)} {a = (SC.serverEvent S.beginCM)} serverCloseEdge20 (V.stop {s = (stageScene S.closingCM false SC.publishedIG exitedModel peerFinished secondFreeFront)}))))))))))))))))))))
        initialized-restarted-cm-entry : V.Runs initial ((livePrefixActions ++ peerCloseActions) ++ serverCloseActions) cmEntry
        initialized-restarted-cm-entry = Facts.append-protocols initialized-peer-close server-close-path
      restarted-cm-entry-supply : Inv.ProtocolValid cmEntry
      restarted-cm-entry-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-restarted-cm-entry

      -- This renderer changes group/coordinator metadata only; each change is
      -- justified by its actual CM receipt or group transition below.
      withGroupPhase : Group.Phase → V.Runtime → V.Runtime
      withGroupPhase pc original = record original { base = record b
        { server = record (K.server b) { base = record (E.base (K.server b))
          { base = record n { base = record c { base = record d { base = record r
            { base = record w { base = Group.setPhase A.child₀ pc (W.base w) } } } } } } } } }
        where
        b = V.base original
        n = V.publication b
        c = N.base n
        d = N.C.base c
        r = N.D.base d
        w = N.R.base r
      handlerAction : W.Action → V.Event
      handlerAction a = StartTrace.unwindStep (N.R.run (N.D.X.run a))
      groupAt : Group.Phase → Y.Model → V.Runtime
      groupAt pc m = withGroupPhase pc (SC.coordinated SC.cmWait
        (stageScene S.closingCM false SC.publishedIG m peerFinished secondFreeFront))
      receipt1 receipt2 receipt3 receipt4 receipt5 : V.Runtime
      receipt1 = SC.coordinated SC.cmCaptured cmEntry
      receipt2 = SC.coordinated SC.cmRead cmEntry
      receipt3 = SC.coordinated SC.cmSend cmEntry
      receipt4 = withGroupPhase (Group.ownerAborting shutdownError) (SC.coordinated SC.cmAcknowledged cmEntry)
      receipt5 = groupAt (Group.ownerAborting shutdownError) exitedModel

      receiptEdge1 : V.advance (SC.coordinatorEvent Close.captureSnapshot) cmEntry ≡ just receipt1
      receiptEdge1 = refl

      receiptEdge2 : V.advance (SC.coordinatorEvent Close.readEntry) receipt1 ≡ just receipt2
      receiptEdge2 = refl

      receiptEdge3 : V.advance (SC.coordinatorEvent Close.requestCancellation) receipt2 ≡ just receipt3
      receiptEdge3 = refl

      receiptEdge4 : V.advance (handlerAction (W.deliverShutdownMux shutdownError)) receipt3 ≡ just receipt4
      receiptEdge4 = refl

      receiptEdge5 : V.advance (SC.coordinatorEvent Close.finishTraversal) receipt4 ≡ just receipt5
      receiptEdge5 = refl

      receiptActions : List V.Event
      receiptActions = (SC.coordinatorEvent Close.captureSnapshot) ∷ (SC.coordinatorEvent Close.readEntry) ∷ (SC.coordinatorEvent Close.requestCancellation) ∷ (handlerAction (W.deliverShutdownMux shutdownError)) ∷ (SC.coordinatorEvent Close.finishTraversal) ∷ []
      entryAndReceiptActions : List V.Event
      entryAndReceiptActions = ((livePrefixActions ++ peerCloseActions) ++ serverCloseActions) ++ receiptActions
      abstract
        receipt-path : V.Runs cmEntry receiptActions receipt5
        receipt-path = V.more {s = cmEntry} {t = receipt1} {u = receipt5} {a = (SC.coordinatorEvent Close.captureSnapshot)} receiptEdge1 (V.more {s = receipt1} {t = receipt2} {u = receipt5} {a = (SC.coordinatorEvent Close.readEntry)} receiptEdge2 (V.more {s = receipt2} {t = receipt3} {u = receipt5} {a = (SC.coordinatorEvent Close.requestCancellation)} receiptEdge3 (V.more {s = receipt3} {t = receipt4} {u = receipt5} {a = (handlerAction (W.deliverShutdownMux shutdownError))} receiptEdge4 (V.more {s = receipt4} {t = receipt5} {u = receipt5} {a = (SC.coordinatorEvent Close.finishTraversal)} receiptEdge5 (V.stop {s = receipt5})))))
        initialized-normal-monitor-receipt : V.Runs initial entryAndReceiptActions receipt5
        initialized-normal-monitor-receipt = Facts.append-protocols initialized-restarted-cm-entry receipt-path

      -- Both protocol generations and both infrastructure handles are still
      -- registered. Cancellation never fabricates a typed protocol completion.
      capturedPhysicalOrder : List JobId
      capturedPhysicalOrder = ident 21 ∷ jid ∷ ident 1 ∷ ident 0 ∷ []
      physical0 : Pool.State
      physical0 = secondPhysicalRegisteredPool
      physical1 : Pool.State
      physical1 = record physical0 { phase = Pool.closing; snapshot = capturedPhysicalOrder; remaining = capturedPhysicalOrder }
      physical2 : Pool.State
      physical2 = record physical1 { phase = Pool.cancelPending (ident 21) }
      physical3 : Pool.State
      physical3 = record physical2 { phase = Pool.joinPending (ident 21); handles = put (ident 21) Pool.bodyUnwinding (Pool.handles physical2) }
      physical4 : Pool.State
      physical4 = record physical3 { handles = put (ident 21) (Pool.deregisterPending Pool.cancelledExit) (Pool.handles physical3) }
      physical5 : Pool.State
      physical5 = record physical4 { handles = put (ident 21) (Pool.deregistered Pool.cancelledExit) (Pool.handles physical4); registered = ident 20 ∷ ident 1 ∷ ident 0 ∷ [] }
      physical6 : Pool.State
      physical6 = record physical5 { handles = put (ident 21) (Pool.resultAvailable Pool.cancelledExit) (Pool.handles physical5) }
      physical7 : Pool.State
      physical7 = record physical6 { phase = Pool.closing; remaining = ident 20 ∷ ident 1 ∷ ident 0 ∷ []; joined = ident 21 ∷ [] }
      physical8 : Pool.State
      physical8 = record physical7 { phase = Pool.cancelPending (ident 20) }
      physical9 : Pool.State
      physical9 = record physical8 { phase = Pool.joinPending (ident 20); handles = put (ident 20) Pool.bodyUnwinding (Pool.handles physical8) }
      physical10 : Pool.State
      physical10 = record physical9 { handles = put (ident 20) (Pool.deregisterPending Pool.cancelledExit) (Pool.handles physical9) }
      physical11 : Pool.State
      physical11 = record physical10 { handles = put (ident 20) (Pool.deregistered Pool.cancelledExit) (Pool.handles physical10); registered = ident 1 ∷ ident 0 ∷ [] }
      physical12 : Pool.State
      physical12 = record physical11 { handles = put (ident 20) (Pool.resultAvailable Pool.cancelledExit) (Pool.handles physical11) }
      physical13 : Pool.State
      physical13 = record physical12 { phase = Pool.closing; remaining = ident 1 ∷ ident 0 ∷ []; joined = ident 21 ∷ ident 20 ∷ [] }
      physical14 : Pool.State
      physical14 = record physical13 { phase = Pool.cancelPending (ident 1) }
      physical15 : Pool.State
      physical15 = record physical14 { phase = Pool.joinPending (ident 1); handles = put (ident 1) Pool.bodyUnwinding (Pool.handles physical14) }
      physical16 : Pool.State
      physical16 = record physical15 { handles = put (ident 1) (Pool.deregisterPending Pool.cancelledExit) (Pool.handles physical15) }
      physical17 : Pool.State
      physical17 = record physical16 { handles = put (ident 1) (Pool.deregistered Pool.cancelledExit) (Pool.handles physical16); registered = ident 0 ∷ [] }
      physical18 : Pool.State
      physical18 = record physical17 { handles = put (ident 1) (Pool.resultAvailable Pool.cancelledExit) (Pool.handles physical17) }
      physical19 : Pool.State
      physical19 = record physical18 { phase = Pool.closing; remaining = ident 0 ∷ []; joined = ident 21 ∷ ident 20 ∷ ident 1 ∷ [] }
      physical20 : Pool.State
      physical20 = record physical19 { phase = Pool.cancelPending (ident 0) }
      physical21 : Pool.State
      physical21 = record physical20 { phase = Pool.joinPending (ident 0); handles = put (ident 0) Pool.bodyUnwinding (Pool.handles physical20) }
      physical22 : Pool.State
      physical22 = record physical21 { handles = put (ident 0) (Pool.deregisterPending Pool.cancelledExit) (Pool.handles physical21) }
      physical23 : Pool.State
      physical23 = record physical22 { handles = put (ident 0) (Pool.deregistered Pool.cancelledExit) (Pool.handles physical22); registered = [] }
      physical24 : Pool.State
      physical24 = record physical23 { handles = put (ident 0) (Pool.resultAvailable Pool.cancelledExit) (Pool.handles physical23) }
      physical25 : Pool.State
      physical25 = record physical24 { phase = Pool.closing; remaining = []; joined = ident 21 ∷ ident 20 ∷ ident 1 ∷ ident 0 ∷ [] }
      physical26 : Pool.State
      physical26 = record physical25 { phase = Pool.closedPool }

      poolCloseEdge1 : V.advance (shutdownStep (Group.beginWholeClose A.child₀ capturedPhysicalOrder)) (receipt5) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical1 exitedModel))
      poolCloseEdge1 = refl

      poolCloseEdge2 : V.advance (shutdownStep (Group.requestWholeCancel A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical1 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel))
      poolCloseEdge2 = refl

      poolCloseEdge3 : V.advance (shutdownStep (Group.deliverWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel))
      poolCloseEdge3 = refl

      poolCloseEdge4 : V.advance (shutdownStep (Group.finishChildUnwind (ident 21))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical4 exitedModel))
      poolCloseEdge4 = refl

      poolCloseEdge5 : V.advance (physicalStep (P.deregisterProtocol (ident 21))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical4 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical5 exitedModel))
      poolCloseEdge5 = refl

      poolCloseEdge6 : V.advance (physicalStep (P.asyncProtocolResult (ident 21))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical5 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical6 exitedModel))
      poolCloseEdge6 = refl

      poolCloseEdge7 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical6 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical7 exitedModel))
      poolCloseEdge7 = refl

      poolCloseEdge8 : V.advance (shutdownStep (Group.requestWholeCancel A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical7 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical8 exitedModel))
      poolCloseEdge8 = refl

      poolCloseEdge9 : V.advance (shutdownStep (Group.deliverWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical8 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel))
      poolCloseEdge9 = refl

      poolCloseEdge10 : V.advance (shutdownStep (Group.finishChildUnwind (ident 20))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical10 exitedModel))
      poolCloseEdge10 = refl

      poolCloseEdge11 : V.advance (physicalStep (P.deregisterProtocol (ident 20))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical10 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical11 exitedModel))
      poolCloseEdge11 = refl

      poolCloseEdge12 : V.advance (physicalStep (P.asyncProtocolResult (ident 20))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical11 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical12 exitedModel))
      poolCloseEdge12 = refl

      poolCloseEdge13 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical12 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical13 exitedModel))
      poolCloseEdge13 = refl

      poolCloseEdge14 : V.advance (shutdownStep (Group.requestWholeCancel A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical13 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical14 exitedModel))
      poolCloseEdge14 = refl

      poolCloseEdge15 : V.advance (shutdownStep (Group.deliverWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical14 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical15 exitedModel))
      poolCloseEdge15 = refl

      poolCloseEdge16 : V.advance (shutdownStep (Group.finishChildUnwind (ident 1))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical15 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical16 exitedModel))
      poolCloseEdge16 = refl

      poolCloseEdge17 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.demuxer)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical16 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical17 exitedModel))
      poolCloseEdge17 = refl

      poolCloseEdge18 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical17 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical18 exitedModel))
      poolCloseEdge18 = refl

      poolCloseEdge19 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical18 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical19 exitedModel))
      poolCloseEdge19 = refl

      poolCloseEdge20 : V.advance (shutdownStep (Group.requestWholeCancel A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical19 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical20 exitedModel))
      poolCloseEdge20 = refl

      poolCloseEdge21 : V.advance (shutdownStep (Group.deliverWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical20 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical21 exitedModel))
      poolCloseEdge21 = refl

      poolCloseEdge22 : V.advance (shutdownStep (Group.finishChildUnwind (ident 0))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical21 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical22 exitedModel))
      poolCloseEdge22 = refl

      poolCloseEdge23 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.muxer)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical22 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical23 exitedModel))
      poolCloseEdge23 = refl

      poolCloseEdge24 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.muxer)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical23 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical24 exitedModel))
      poolCloseEdge24 = refl

      poolCloseEdge25 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical24 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel))
      poolCloseEdge25 = refl

      poolCloseEdge26 : V.advance (shutdownStep (Group.finishWholeClose A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel)) ≡ just (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))
      poolCloseEdge26 = refl

      wholePoolActions : List V.Event
      wholePoolActions = (shutdownStep (Group.beginWholeClose A.child₀ capturedPhysicalOrder)) ∷ (shutdownStep (Group.requestWholeCancel A.child₀)) ∷ (shutdownStep (Group.deliverWhole A.child₀)) ∷ (shutdownStep (Group.finishChildUnwind (ident 21))) ∷ (physicalStep (P.deregisterProtocol (ident 21))) ∷ (physicalStep (P.asyncProtocolResult (ident 21))) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.requestWholeCancel A.child₀)) ∷ (shutdownStep (Group.deliverWhole A.child₀)) ∷ (shutdownStep (Group.finishChildUnwind (ident 20))) ∷ (physicalStep (P.deregisterProtocol (ident 20))) ∷ (physicalStep (P.asyncProtocolResult (ident 20))) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.requestWholeCancel A.child₀)) ∷ (shutdownStep (Group.deliverWhole A.child₀)) ∷ (shutdownStep (Group.finishChildUnwind (ident 1))) ∷ (physicalStep (P.deregisterInfra A.child₀ Types.demuxer)) ∷ (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer)) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.requestWholeCancel A.child₀)) ∷ (shutdownStep (Group.deliverWhole A.child₀)) ∷ (shutdownStep (Group.finishChildUnwind (ident 0))) ∷ (physicalStep (P.deregisterInfra A.child₀ Types.muxer)) ∷ (physicalStep (P.asyncInfraResult A.child₀ Types.muxer)) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.finishWholeClose A.child₀)) ∷ []
      wholePoolClosed : V.Runtime
      wholePoolClosed = groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel)
      physicalCloseActions : List V.Event
      physicalCloseActions = entryAndReceiptActions ++ wholePoolActions
      abstract
        whole-pool-path : V.Runs receipt5 wholePoolActions wholePoolClosed
        whole-pool-path = V.more {s = (receipt5)} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical1 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.beginWholeClose A.child₀ capturedPhysicalOrder))} poolCloseEdge1 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical1 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.requestWholeCancel A.child₀))} poolCloseEdge2 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.deliverWhole A.child₀))} poolCloseEdge3 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical4 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.finishChildUnwind (ident 21)))} poolCloseEdge4 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical4 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical5 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (physicalStep (P.deregisterProtocol (ident 21)))} poolCloseEdge5 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical5 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical6 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (physicalStep (P.asyncProtocolResult (ident 21)))} poolCloseEdge6 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical6 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical7 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.joinWhole A.child₀))} poolCloseEdge7 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical7 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical8 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.requestWholeCancel A.child₀))} poolCloseEdge8 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical8 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.deliverWhole A.child₀))} poolCloseEdge9 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical10 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.finishChildUnwind (ident 20)))} poolCloseEdge10 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical10 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical11 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (physicalStep (P.deregisterProtocol (ident 20)))} poolCloseEdge11 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical11 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical12 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (physicalStep (P.asyncProtocolResult (ident 20)))} poolCloseEdge12 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical12 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical13 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.joinWhole A.child₀))} poolCloseEdge13 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical13 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical14 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.requestWholeCancel A.child₀))} poolCloseEdge14 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical14 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical15 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.deliverWhole A.child₀))} poolCloseEdge15 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical15 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical16 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.finishChildUnwind (ident 1)))} poolCloseEdge16 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical16 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical17 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (physicalStep (P.deregisterInfra A.child₀ Types.demuxer))} poolCloseEdge17 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical17 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical18 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer))} poolCloseEdge18 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical18 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical19 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.joinWhole A.child₀))} poolCloseEdge19 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical19 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical20 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.requestWholeCancel A.child₀))} poolCloseEdge20 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical20 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical21 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.deliverWhole A.child₀))} poolCloseEdge21 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical21 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical22 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.finishChildUnwind (ident 0)))} poolCloseEdge22 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical22 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical23 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (physicalStep (P.deregisterInfra A.child₀ Types.muxer))} poolCloseEdge23 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical23 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical24 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (physicalStep (P.asyncInfraResult A.child₀ Types.muxer))} poolCloseEdge24 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical24 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.joinWhole A.child₀))} poolCloseEdge25 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel))} {t = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {u = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))} {a = (shutdownStep (Group.finishWholeClose A.child₀))} poolCloseEdge26 (V.stop {s = (groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))}))))))))))))))))))))))))))
        initialized-restarted-pool-close : V.Runs initial physicalCloseActions wholePoolClosed
        initialized-restarted-pool-close = Facts.append-protocols initialized-normal-monitor-receipt whole-pool-path

      -- Failed/Dead is after every captured Async result and join. IG has
      -- already exited, so the tracer takes its real false-active branch.
      failedAfterClose deadAfterClose sampledAfterClose : Y.Model
      failedAfterClose = Y.sourceMux (record (Y.withWanton jid Mux.initiatorJob Y.m1) { status = Mux.failed shutdownError }) [] (withPool physical26 exitedModel)
      deadAfterClose = Y.sourceMux (record (Y.withWanton jid Mux.initiatorJob Y.m1) { status = Mux.failed shutdownError; callback = Mux.readActive Mux.muxStopped }) [] (withPool physical26 exitedModel)
      sampledAfterClose = Y.sourceMux (record (Y.withWanton jid Mux.initiatorJob Y.m1) { status = Mux.failed shutdownError; callback = Mux.commitTrace false Mux.muxStopped }) [] (withPool physical26 exitedModel)
      failedStatus deadInvoked deadSampled deadCommitted readyForBuffer : V.Runtime
      failedStatus = groupAt (Group.asyncFailureWritten shutdownError) failedAfterClose
      deadInvoked = groupAt (Group.asyncDeadTracing shutdownError) deadAfterClose
      deadSampled = groupAt (Group.asyncDeadTracing shutdownError) sampledAfterClose
      deadCommitted = groupAt (Group.asyncDeadTracing shutdownError) failedAfterClose
      readyForBuffer = groupAt (Group.scopeDone (Group.asyncExit shutdownError)) failedAfterClose

      asyncCatchEdge1 : V.advance (shutdownStep (Group.writeAsyncFailure A.child₀)) wholePoolClosed ≡ just failedStatus
      asyncCatchEdge1 = refl

      asyncCatchEdge2 : V.advance (shutdownStep (Group.beginAsyncDead A.child₀)) failedStatus ≡ just deadInvoked
      asyncCatchEdge2 = refl

      asyncCatchEdge3 : V.advance (shutdownStep (Group.sampleAsyncTracer A.child₀)) deadInvoked ≡ just deadSampled
      asyncCatchEdge3 = refl

      asyncCatchEdge4 : V.advance (shutdownStep (Group.commitAsyncTracer A.child₀)) deadSampled ≡ just deadCommitted
      asyncCatchEdge4 = refl

      asyncCatchEdge5 : V.advance (shutdownStep (Group.finishAsyncDead A.child₀)) deadCommitted ≡ just readyForBuffer
      asyncCatchEdge5 = refl

      normalCatchActions : List V.Event
      normalCatchActions = (shutdownStep (Group.writeAsyncFailure A.child₀)) ∷ (shutdownStep (Group.beginAsyncDead A.child₀)) ∷ (shutdownStep (Group.sampleAsyncTracer A.child₀)) ∷ (shutdownStep (Group.commitAsyncTracer A.child₀)) ∷ (shutdownStep (Group.finishAsyncDead A.child₀)) ∷ []
      catchCompleteActions : List V.Event
      catchCompleteActions = physicalCloseActions ++ normalCatchActions
      abstract
        normal-catch-path : V.Runs wholePoolClosed normalCatchActions readyForBuffer
        normal-catch-path = V.more {s = wholePoolClosed} {t = failedStatus} {u = readyForBuffer} {a = (shutdownStep (Group.writeAsyncFailure A.child₀))} asyncCatchEdge1 (V.more {s = failedStatus} {t = deadInvoked} {u = readyForBuffer} {a = (shutdownStep (Group.beginAsyncDead A.child₀))} asyncCatchEdge2 (V.more {s = deadInvoked} {t = deadSampled} {u = readyForBuffer} {a = (shutdownStep (Group.sampleAsyncTracer A.child₀))} asyncCatchEdge3 (V.more {s = deadSampled} {t = deadCommitted} {u = readyForBuffer} {a = (shutdownStep (Group.commitAsyncTracer A.child₀))} asyncCatchEdge4 (V.more {s = deadCommitted} {t = readyForBuffer} {u = readyForBuffer} {a = (shutdownStep (Group.finishAsyncDead A.child₀))} asyncCatchEdge5 (V.stop {s = readyForBuffer})))))
        initialized-restarted-catch : V.Runs initial catchCompleteActions readyForBuffer
        initialized-restarted-catch = Facts.append-protocols initialized-restarted-pool-close normal-catch-path


      -- The captured handler's finally is after buffer-provider unwind. Its
      -- cleanup completion is still distinct from physical Async publication.
      cleanupWorld0 cleanupWorld1 cleanupWorld2 cleanupWorld3 cleanupWorld4 cleanupWorld5 cleanupWorld6 : Shared.State
      cleanupWorld0 = Y.world failedAfterClose
      capturedCleanupLease : Shared.Lease
      capturedCleanupLease = Shared.lease A.child₀ F.binding
      cleanupWorld1 = record cleanupWorld0 { cleanups = put A.child₀ Shared.cleanupAcquire (Shared.cleanups cleanupWorld0) }
      cleanupWorld2 = record cleanupWorld1
        { cm = record (Shared.cm cleanupWorld1) { mapCell = Shared.taken A.child₀ }
        ; cleanups = put A.child₀ (Shared.cleanupSelect capturedCleanupLease) (Shared.cleanups cleanupWorld1) }
      cleanupWorld3 = record cleanupWorld2
        { cm = record (Shared.cm cleanupWorld2)
          { entries = put (ident 0) (Shared.terminated nothing) (Shared.entries (Shared.cm cleanupWorld2)) }
        ; cleanups = put A.child₀ (Shared.cleanupClose capturedCleanupLease [] Shared.countImmediately) (Shared.cleanups cleanupWorld2) }
      cleanupWorld4 = record cleanupWorld3
        { sockets = put (Shared.handlerSocket I.captured) Shared.closed (Shared.sockets cleanupWorld3)
        ; cleanups = put A.child₀ (Shared.cleanupPublish capturedCleanupLease [] Shared.countImmediately) (Shared.cleanups cleanupWorld3) }
      cleanupWorld5 = record cleanupWorld4
        { cm = record (Shared.cm cleanupWorld4) { mapCell = Shared.full [] }
        ; cleanups = put A.child₀ (Shared.cleanupCount Shared.cleanupNormal) (Shared.cleanups cleanupWorld4) }
      cleanupWorld6 = record cleanupWorld5
        { cleanups = put A.child₀ (Shared.cleanupDone Shared.cleanupNormal) (Shared.cleanups cleanupWorld5) }
      handlerAt : W.Phase → Shared.State → V.Runtime
      handlerAt pc world = SC.Completion.withHandlerExit pc
        (groupAt (Group.scopeDone (Group.asyncExit shutdownError)) (record failedAfterClose { world = world }))
      handler1 handler2 handler3 handler4 handler5 handler6 handler7 handler8 handler9 handler10 : V.Runtime
      handler1 = handlerAt (W.bufferScope (Group.asyncExit shutdownError)) cleanupWorld0
      handler2 = handlerAt (W.bodyExited (W.asyncException shutdownError)) cleanupWorld0
      handler3 = handlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld1
      handler4 = handlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld2
      handler5 = handlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld3
      handler6 = handlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld4
      handler7 = handlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld5
      handler8 = handlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld6
      handler9 = handlerAt (W.cleanupComplete (W.asyncException shutdownError) Shared.cleanupNormal) cleanupWorld6
      handler10 = handlerAt (W.resultAvailable (W.asyncException shutdownError) Shared.cleanupNormal) cleanupWorld6
      finalCM returnedServer : V.Runtime
      finalCM = SC.coordinated (Close.shutdownState Close.closed (ident 0 ∷ []) [] (A.child₀ ∷ [])) handler10
      returnedServer = record finalCM { base = record (V.base finalCM)
        { server = record (K.server (V.base finalCM))
          { base = record (E.base (K.server (V.base finalCM))) { stage = S.serverReturned } } } }

      handlerFinishEdge1 : V.advance (handlerAction (W.beginExit A.child₀)) readyForBuffer ≡ just handler1
      handlerFinishEdge1 = refl

      handlerFinishEdge2 : V.advance (handlerAction (W.observeBufferReturn A.child₀)) handler1 ≡ just handler2
      handlerFinishEdge2 = refl

      handlerFinishEdge3 : V.advance (handlerAction (W.enterFinalizer A.child₀)) handler2 ≡ just handler3
      handlerFinishEdge3 = refl

      handlerFinishEdge4 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap)) handler3 ≡ just handler4
      handlerFinishEdge4 = refl

      handlerFinishEdge5 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry)) handler4 ≡ just handler5
      handlerFinishEdge5 = refl

      handlerFinishEdge6 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket)) handler5 ≡ just handler6
      handlerFinishEdge6 = refl

      handlerFinishEdge7 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap)) handler6 ≡ just handler7
      handlerFinishEdge7 = refl

      handlerFinishEdge8 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters)) handler7 ≡ just handler8
      handlerFinishEdge8 = refl

      handlerFinishEdge9 : V.advance (handlerAction (W.finishCleanup A.child₀)) handler8 ≡ just handler9
      handlerFinishEdge9 = refl

      handlerFinishEdge10 : V.advance (handlerAction (W.publishAsyncResult A.child₀)) handler9 ≡ just handler10
      handlerFinishEdge10 = refl

      handlerFinishEdge11 : V.advance (SC.coordinatorEvent Close.finishClose) handler10 ≡ just finalCM
      handlerFinishEdge11 = refl

      handlerFinishEdge12 : V.advance (SC.serverEvent S.finishServer) finalCM ≡ just returnedServer
      handlerFinishEdge12 = refl

      handlerFinishActions : List V.Event
      handlerFinishActions = (handlerAction (W.beginExit A.child₀)) ∷ (handlerAction (W.observeBufferReturn A.child₀)) ∷ (handlerAction (W.enterFinalizer A.child₀)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters)) ∷ (handlerAction (W.finishCleanup A.child₀)) ∷ (handlerAction (W.publishAsyncResult A.child₀)) ∷ (SC.coordinatorEvent Close.finishClose) ∷ (SC.serverEvent S.finishServer) ∷ []
      restartedShutdownActions : List V.Event
      restartedShutdownActions = catchCompleteActions ++ handlerFinishActions
      abstract
        handler-finish-path : V.Runs readyForBuffer handlerFinishActions returnedServer
        handler-finish-path = V.more {s = readyForBuffer} {t = handler1} {u = returnedServer} {a = (handlerAction (W.beginExit A.child₀))} handlerFinishEdge1 (V.more {s = handler1} {t = handler2} {u = returnedServer} {a = (handlerAction (W.observeBufferReturn A.child₀))} handlerFinishEdge2 (V.more {s = handler2} {t = handler3} {u = returnedServer} {a = (handlerAction (W.enterFinalizer A.child₀))} handlerFinishEdge3 (V.more {s = handler3} {t = handler4} {u = returnedServer} {a = (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap))} handlerFinishEdge4 (V.more {s = handler4} {t = handler5} {u = returnedServer} {a = (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry))} handlerFinishEdge5 (V.more {s = handler5} {t = handler6} {u = returnedServer} {a = (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket))} handlerFinishEdge6 (V.more {s = handler6} {t = handler7} {u = returnedServer} {a = (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap))} handlerFinishEdge7 (V.more {s = handler7} {t = handler8} {u = returnedServer} {a = (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters))} handlerFinishEdge8 (V.more {s = handler8} {t = handler9} {u = returnedServer} {a = (handlerAction (W.finishCleanup A.child₀))} handlerFinishEdge9 (V.more {s = handler9} {t = handler10} {u = returnedServer} {a = (handlerAction (W.publishAsyncResult A.child₀))} handlerFinishEdge10 (V.more {s = handler10} {t = finalCM} {u = returnedServer} {a = (SC.coordinatorEvent Close.finishClose)} handlerFinishEdge11 (V.more {s = finalCM} {t = returnedServer} {u = returnedServer} {a = (SC.serverEvent S.finishServer)} handlerFinishEdge12 (V.stop {s = returnedServer}))))))))))))
        initialized-restarted-server-return : V.Runs initial restartedShutdownActions returnedServer
        initialized-restarted-server-return = Facts.append-protocols initialized-restarted-catch handler-finish-path
      restarted-shutdown-supply : Inv.ProtocolValid returnedServer
      restarted-shutdown-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-restarted-server-return

      -- Retain the actual physical result table at CM's successful wait.
      handlerStateOf : V.Runtime → W.State
      handlerStateOf s = N.R.base (N.raw (V.publication (V.base s)))
      abstract
        handler-before-wait : V.Runs readyForBuffer (take 10 handlerFinishActions) handler10
        handler-before-wait = V.more {s = readyForBuffer} {t = handler1} {u = handler10} {a = (handlerAction (W.beginExit A.child₀))} handlerFinishEdge1 (V.more {s = handler1} {t = handler2} {u = handler10} {a = (handlerAction (W.observeBufferReturn A.child₀))} handlerFinishEdge2 (V.more {s = handler2} {t = handler3} {u = handler10} {a = (handlerAction (W.enterFinalizer A.child₀))} handlerFinishEdge3 (V.more {s = handler3} {t = handler4} {u = handler10} {a = (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap))} handlerFinishEdge4 (V.more {s = handler4} {t = handler5} {u = handler10} {a = (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry))} handlerFinishEdge5 (V.more {s = handler5} {t = handler6} {u = handler10} {a = (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket))} handlerFinishEdge6 (V.more {s = handler6} {t = handler7} {u = handler10} {a = (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap))} handlerFinishEdge7 (V.more {s = handler7} {t = handler8} {u = handler10} {a = (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters))} handlerFinishEdge8 (V.more {s = handler8} {t = handler9} {u = handler10} {a = (handlerAction (W.finishCleanup A.child₀))} handlerFinishEdge9 (V.more {s = handler9} {t = handler10} {u = handler10} {a = (handlerAction (W.publishAsyncResult A.child₀))} handlerFinishEdge10 (V.stop {s = handler10}))))))))))
      captured-handler-wait : HandlerFacts.PhysicalWait (handlerStateOf handler10) (handlerStateOf finalCM)
      captured-handler-wait = HandlerFacts.physical-wait-observation (handlerStateOf handler10) refl


      -- Results certify the actual nonempty physical snapshot. Registry
      -- absence or a local completion cell is not used as an Async result.
      import ConnectionManagement.Properties.JobPoolCloseKernel as PoolProof
      private
        module PhysicalFacts = PoolProof Types.TypedResult true
      closedPhysicalPool : Pool.State
      closedPhysicalPool = P.poolAt A.child₀ (V.physical (V.base wholePoolClosed))
      four-actual-results : All.All (PhysicalFacts.Terminal closedPhysicalPool) (Pool.snapshot closedPhysicalPool)
      four-actual-results = (Pool.cancelledExit , refl) All.∷ (Pool.cancelledExit , refl) All.∷
        (Pool.cancelledExit , refl) All.∷ (Pool.cancelledExit , refl) All.∷ All.[]
      actual-four-handle-snapshot : Pool.snapshot closedPhysicalPool ≡ capturedPhysicalOrder
      actual-four-handle-snapshot = refl
      actual-four-handle-joins : Pool.joined closedPhysicalPool ≡ capturedPhysicalOrder
      actual-four-handle-joins = refl
      body-live-at-cm-entry : lookup (ident 21) (Pool.handles (P.poolAt A.child₀ (V.physical (V.base cmEntry)))) ≡ just Pool.bodyRunning
      body-live-at-cm-entry = refl
      old-body-unpublished-at-cm-entry : lookup jid (Pool.handles (P.poolAt A.child₀ (V.physical (V.base cmEntry)))) ≡ just Pool.bodyRunning
      old-body-unpublished-at-cm-entry = refl
      no-start-tracer-fault-at-receipt : lookup A.child₀ (N.R.faults (N.raw (V.publication (V.base receipt5)))) ≡ nothing
      no-start-tracer-fault-at-receipt = refl
      receipt-is-not-physical-close : Pool.phase (P.poolAt A.child₀ (V.physical (V.base receipt5))) ≡ Pool.openPool
      receipt-is-not-physical-close = refl
      no-raw-cm-acknowledgement : V.advance (SC.coordinatorEvent Close.acknowledgeDelivery) receipt3 ≡ nothing
      no-raw-cm-acknowledgement = refl
      no-cm-before-callback-exit : V.advance (SC.coordinatorEvent Close.captureSnapshot) liveRestart ≡ nothing
      no-cm-before-callback-exit = refl
      no-failed-before-physical-close : V.advance (shutdownStep (Group.writeAsyncFailure A.child₀))
        (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel)) ≡ nothing
      no-failed-before-physical-close = refl
      no-early-physical-join : V.advance (shutdownStep (Group.joinWhole A.child₀))
        (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel)) ≡ nothing
      no-early-physical-join = refl
      cancelled-new-body-cannot-commit : V.advance (V.commitError (ident 21) err)
        (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel)) ≡ nothing
      cancelled-new-body-cannot-commit = refl
      cancelled-old-body-cannot-return : V.advance (physicalStep (P.returnProtocol jid))
        (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel)) ≡ nothing
      cancelled-old-body-cannot-return = refl
      cancelled-old-body-cannot-publish : V.advance (physicalStep (P.publishProtocol jid)) wholePoolClosed ≡ nothing
      cancelled-old-body-cannot-publish = refl
      no-typed-completion-from-cancellation : Pool.completions closedPhysicalPool ≡ []
      no-typed-completion-from-cancellation = refl
      old-clean-cell-survives : V.observe rid returnedServer ≡ just (V.localResult clean)
      old-clean-cell-survives = refl
      current-cell-remains-empty : lookup (ident 21) (V.calls (V.front returnedServer)) ≡
        just (record requested { thread = just (ident 21) })
      current-cell-remains-empty = refl
      current-cell-observes-shutdown : V.observe (ident 21) returnedServer ≡ just (V.shutdownResult (Mux.failed shutdownError))
      current-cell-observes-shutdown = refl
      shutdown-wakes-current-before-handler-result : V.observe (ident 21) readyForBuffer ≡ just (V.shutdownResult (Mux.failed shutdownError))
      shutdown-wakes-current-before-handler-result = refl
      still-no-handler-result-after-catch : W.resultReady A.child₀ (handlerStateOf readyForBuffer) ≡ false
      still-no-handler-result-after-catch = refl
      still-no-handler-result-after-cleanup : W.resultReady A.child₀ (handlerStateOf handler9) ≡ false
      still-no-handler-result-after-cleanup = refl
      cm-waits-for-actual-handler-result : V.advance (SC.coordinatorEvent Close.finishClose) handler9 ≡ nothing
      cm-waits-for-actual-handler-result = refl
      no-early-handler-result-publication : V.advance (handlerAction (W.publishAsyncResult A.child₀)) handler8 ≡ nothing
      no-early-handler-result-publication = refl
      actual-handler-async-outcome : W.resultOf A.child₀ (handlerStateOf returnedServer) ≡ just (W.asyncException shutdownError)
      actual-handler-async-outcome = refl
      actual-returned-server : S.stage (E.base (K.server (V.base returnedServer))) ≡ S.serverReturned
      actual-returned-server = refl
      actual-closed-cm : Close.phase (W.shutdown (handlerStateOf returnedServer)) ≡ Close.closed
      actual-closed-cm = refl
      captured-cm-handler-retained : Close.collected (W.shutdown (handlerStateOf returnedServer)) ≡ A.child₀ ∷ []
      captured-cm-handler-retained = refl
      captured-map-is-purged : Shared.mapCell (Shared.cm (Machine.world (O.core (V.sourceOf returnedServer)))) ≡ Shared.full []
      captured-map-is-purged = refl
      captured-entry-is-terminated : lookup (ident 0) (Shared.entries (Shared.cm (Machine.world (O.core (V.sourceOf returnedServer))))) ≡ just (Shared.terminated nothing)
      captured-entry-is-terminated = refl
      captured-socket-is-closed : lookup (Shared.handlerSocket I.captured) (Shared.sockets (Machine.world (O.core (V.sourceOf returnedServer)))) ≡ just Shared.closed
      captured-socket-is-closed = refl
      no-time-wait-on-outbound-dup : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.timeWaitElapsed)) handler7 ≡ nothing
      no-time-wait-on-outbound-dup = refl
      actual-ig-is-inactive : IG.active (IG.execution (Machine.inboundGovernor (O.core (V.sourceOf returnedServer)))) ≡ false
      actual-ig-is-inactive = refl
      actual-nonempty-ig-exit : E.snapshot (E.exit (K.server (V.base returnedServer))) ≡ SC.exitRows
      actual-nonempty-ig-exit = refl
      inactive-dead-adds-no-notification : Shared.inboundInfo (Machine.world (O.core (V.sourceOf returnedServer))) ≡ []
      inactive-dead-adds-no-notification = refl
      inactive-dead-retains-mux-counters : P.muxAt (ident 0) (V.physical (V.base returnedServer)) ≡ just (record (Y.withWanton jid Mux.initiatorJob Y.m1) { status = Mux.failed shutdownError })
      inactive-dead-retains-mux-counters = refl
      published-activation-completion-retained : C.SubContext.completions (C.subsystem (K.context (V.base returnedServer))) ≡ activationCompletion ∷ []
      published-activation-completion-retained = refl
      no-monitor-read-after-scope-exit : V.advance (V.pollResults (ident 0) (ident 50)) returnedServer ≡ nothing
      no-monitor-read-after-scope-exit = refl
      unjoined-raw-admission : lookup A.w₁ (S.workers (E.base (K.server (V.base returnedServer)))) ≡ just (S.rawWorker F.r₁ S.calling 0)
      unjoined-raw-admission = refl
      not-all-raw-admissions-finished : S.allResults (S.workers (E.base (K.server (V.base returnedServer)))) ≡ false
      not-all-raw-admissions-finished = refl
      open import Data.Empty using (⊥)
      -- This actual initialized Server return does not weaken the SI5 target.
      restarted-counterexample-to-all-worker-completion :
        (∀ {t} (as : List V.Event) → V.Runs initial as t →
          S.stage (E.base (K.server (V.base t))) ≡ S.serverReturned →
          S.allResults (S.workers (E.base (K.server (V.base t)))) ≡ true) → ⊥
      restarted-counterexample-to-all-worker-completion claim =
        SC.Completion.false-not-true (claim restartedShutdownActions initialized-restarted-server-return actual-returned-server)

      -- A captured clean body can publish normally while pool close waits for
      -- another generation. Its immutable snapshot membership survives removal.
      module PublicationRace where
        racePool0 : Pool.State
        racePool0 = physical1
        racePool1 : Pool.State
        racePool1 = record racePool0 { handles = put jid (Pool.bodyReturned payload) (Pool.handles racePool0) }
        racePool2 : Pool.State
        racePool2 = record racePool1 { handles = put jid (Pool.deregisterPending Pool.normalExit) (Pool.handles racePool1); completions = payload ∷ [] }
        racePool3 : Pool.State
        racePool3 = record racePool2 { handles = put jid (Pool.deregistered Pool.normalExit) (Pool.handles racePool2); registered = ident 21 ∷ ident 1 ∷ ident 0 ∷ [] }
        racePool4 : Pool.State
        racePool4 = record racePool3 { handles = put jid (Pool.resultAvailable Pool.normalExit) (Pool.handles racePool3) }
        racePool5 : Pool.State
        racePool5 = record racePool4 { phase = Pool.cancelPending (ident 21) }
        racePool6 : Pool.State
        racePool6 = record racePool5 { phase = Pool.joinPending (ident 21); handles = put (ident 21) Pool.bodyUnwinding (Pool.handles racePool5) }
        racePool7 : Pool.State
        racePool7 = record racePool6 { handles = put (ident 21) (Pool.deregisterPending Pool.cancelledExit) (Pool.handles racePool6) }
        racePool8 : Pool.State
        racePool8 = record racePool7 { handles = put (ident 21) (Pool.deregistered Pool.cancelledExit) (Pool.handles racePool7); registered = ident 1 ∷ ident 0 ∷ [] }
        racePool9 : Pool.State
        racePool9 = record racePool8 { handles = put (ident 21) (Pool.resultAvailable Pool.cancelledExit) (Pool.handles racePool8) }
        racePool10 : Pool.State
        racePool10 = record racePool9 { phase = Pool.closing; remaining = ident 20 ∷ ident 1 ∷ ident 0 ∷ []; joined = ident 21 ∷ [] }
        racePool11 : Pool.State
        racePool11 = record racePool10 { phase = Pool.joinPending (ident 20) }
        racePool12 : Pool.State
        racePool12 = record racePool11 { phase = Pool.closing; remaining = ident 1 ∷ ident 0 ∷ []; joined = ident 21 ∷ ident 20 ∷ [] }
        racePool13 : Pool.State
        racePool13 = record racePool12 { phase = Pool.cancelPending (ident 1) }
        racePool14 : Pool.State
        racePool14 = record racePool13 { phase = Pool.joinPending (ident 1); handles = put (ident 1) Pool.bodyUnwinding (Pool.handles racePool13) }
        racePool15 : Pool.State
        racePool15 = record racePool14 { handles = put (ident 1) (Pool.deregisterPending Pool.cancelledExit) (Pool.handles racePool14) }
        racePool16 : Pool.State
        racePool16 = record racePool15 { handles = put (ident 1) (Pool.deregistered Pool.cancelledExit) (Pool.handles racePool15); registered = ident 0 ∷ [] }
        racePool17 : Pool.State
        racePool17 = record racePool16 { handles = put (ident 1) (Pool.resultAvailable Pool.cancelledExit) (Pool.handles racePool16) }
        racePool18 : Pool.State
        racePool18 = record racePool17 { phase = Pool.closing; remaining = ident 0 ∷ []; joined = ident 21 ∷ ident 20 ∷ ident 1 ∷ [] }
        racePool19 : Pool.State
        racePool19 = record racePool18 { phase = Pool.cancelPending (ident 0) }
        racePool20 : Pool.State
        racePool20 = record racePool19 { phase = Pool.joinPending (ident 0); handles = put (ident 0) Pool.bodyUnwinding (Pool.handles racePool19) }
        racePool21 : Pool.State
        racePool21 = record racePool20 { handles = put (ident 0) (Pool.deregisterPending Pool.cancelledExit) (Pool.handles racePool20) }
        racePool22 : Pool.State
        racePool22 = record racePool21 { handles = put (ident 0) (Pool.deregistered Pool.cancelledExit) (Pool.handles racePool21); registered = [] }
        racePool23 : Pool.State
        racePool23 = record racePool22 { handles = put (ident 0) (Pool.resultAvailable Pool.cancelledExit) (Pool.handles racePool22) }
        racePool24 : Pool.State
        racePool24 = record racePool23 { phase = Pool.closing; remaining = []; joined = ident 21 ∷ ident 20 ∷ ident 1 ∷ ident 0 ∷ [] }
        racePool25 : Pool.State
        racePool25 = record racePool24 { phase = Pool.closedPool }
        raceClosed : V.Runtime
        raceClosed = groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool racePool25 exitedModel)

        raceEdge1 : V.advance (physicalStep (P.returnProtocol jid)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool0 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool1 exitedModel))
        raceEdge1 = refl

        raceEdge2 : V.advance (physicalStep (P.publishProtocol jid)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool1 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool2 exitedModel))
        raceEdge2 = refl

        raceEdge3 : V.advance (physicalStep (P.deregisterProtocol jid)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool2 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool3 exitedModel))
        raceEdge3 = refl

        raceEdge4 : V.advance (physicalStep (P.asyncProtocolResult jid)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool3 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool4 exitedModel))
        raceEdge4 = refl

        raceEdge5 : V.advance (shutdownStep (Group.requestWholeCancel A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool4 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool5 exitedModel))
        raceEdge5 = refl

        raceEdge6 : V.advance (shutdownStep (Group.deliverWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool5 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool6 exitedModel))
        raceEdge6 = refl

        raceEdge7 : V.advance (shutdownStep (Group.finishChildUnwind (ident 21))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool6 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool7 exitedModel))
        raceEdge7 = refl

        raceEdge8 : V.advance (physicalStep (P.deregisterProtocol (ident 21))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool7 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool8 exitedModel))
        raceEdge8 = refl

        raceEdge9 : V.advance (physicalStep (P.asyncProtocolResult (ident 21))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool8 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool9 exitedModel))
        raceEdge9 = refl

        raceEdge10 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool9 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool10 exitedModel))
        raceEdge10 = refl

        raceEdge11 : V.advance (shutdownStep (Group.requestWholeCancel A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool10 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool11 exitedModel))
        raceEdge11 = refl

        raceEdge12 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool11 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool12 exitedModel))
        raceEdge12 = refl

        raceEdge13 : V.advance (shutdownStep (Group.requestWholeCancel A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool12 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool13 exitedModel))
        raceEdge13 = refl

        raceEdge14 : V.advance (shutdownStep (Group.deliverWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool13 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool14 exitedModel))
        raceEdge14 = refl

        raceEdge15 : V.advance (shutdownStep (Group.finishChildUnwind (ident 1))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool14 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool15 exitedModel))
        raceEdge15 = refl

        raceEdge16 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.demuxer)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool15 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool16 exitedModel))
        raceEdge16 = refl

        raceEdge17 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool16 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool17 exitedModel))
        raceEdge17 = refl

        raceEdge18 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool17 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool18 exitedModel))
        raceEdge18 = refl

        raceEdge19 : V.advance (shutdownStep (Group.requestWholeCancel A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool18 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool19 exitedModel))
        raceEdge19 = refl

        raceEdge20 : V.advance (shutdownStep (Group.deliverWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool19 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool20 exitedModel))
        raceEdge20 = refl

        raceEdge21 : V.advance (shutdownStep (Group.finishChildUnwind (ident 0))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool20 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool21 exitedModel))
        raceEdge21 = refl

        raceEdge22 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.muxer)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool21 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool22 exitedModel))
        raceEdge22 = refl

        raceEdge23 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.muxer)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool22 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool23 exitedModel))
        raceEdge23 = refl

        raceEdge24 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool23 exitedModel)) ≡ just (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool24 exitedModel))
        raceEdge24 = refl

        raceEdge25 : V.advance (shutdownStep (Group.finishWholeClose A.child₀)) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool24 exitedModel)) ≡ just (raceClosed)
        raceEdge25 = refl

        raceActions : List V.Event
        raceActions = (physicalStep (P.returnProtocol jid)) ∷ (physicalStep (P.publishProtocol jid)) ∷ (physicalStep (P.deregisterProtocol jid)) ∷ (physicalStep (P.asyncProtocolResult jid)) ∷ (shutdownStep (Group.requestWholeCancel A.child₀)) ∷ (shutdownStep (Group.deliverWhole A.child₀)) ∷ (shutdownStep (Group.finishChildUnwind (ident 21))) ∷ (physicalStep (P.deregisterProtocol (ident 21))) ∷ (physicalStep (P.asyncProtocolResult (ident 21))) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.requestWholeCancel A.child₀)) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.requestWholeCancel A.child₀)) ∷ (shutdownStep (Group.deliverWhole A.child₀)) ∷ (shutdownStep (Group.finishChildUnwind (ident 1))) ∷ (physicalStep (P.deregisterInfra A.child₀ Types.demuxer)) ∷ (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer)) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.requestWholeCancel A.child₀)) ∷ (shutdownStep (Group.deliverWhole A.child₀)) ∷ (shutdownStep (Group.finishChildUnwind (ident 0))) ∷ (physicalStep (P.deregisterInfra A.child₀ Types.muxer)) ∷ (physicalStep (P.asyncInfraResult A.child₀ Types.muxer)) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.finishWholeClose A.child₀)) ∷ []
        raceCapturedActions : List V.Event
        raceCapturedActions = entryAndReceiptActions ++ (shutdownStep (Group.beginWholeClose A.child₀ capturedPhysicalOrder) ∷ [])
        raceClosedActions : List V.Event
        raceClosedActions = raceCapturedActions ++ raceActions
        abstract
          initialized-race-capture : V.Runs initial raceCapturedActions (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool0 exitedModel))
          initialized-race-capture = Facts.append-protocols initialized-normal-monitor-receipt (V.more {s = (receipt5)} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical1 exitedModel))} {u = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical1 exitedModel))} {a = (shutdownStep (Group.beginWholeClose A.child₀ capturedPhysicalOrder))} poolCloseEdge1 (V.stop {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical1 exitedModel))}))
          race-pool-path : V.Runs (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool0 exitedModel)) raceActions raceClosed
          race-pool-path = V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool0 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool1 exitedModel))} {u = (raceClosed)} {a = (physicalStep (P.returnProtocol jid))} raceEdge1 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool1 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool2 exitedModel))} {u = (raceClosed)} {a = (physicalStep (P.publishProtocol jid))} raceEdge2 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool2 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool3 exitedModel))} {u = (raceClosed)} {a = (physicalStep (P.deregisterProtocol jid))} raceEdge3 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool3 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool4 exitedModel))} {u = (raceClosed)} {a = (physicalStep (P.asyncProtocolResult jid))} raceEdge4 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool4 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool5 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.requestWholeCancel A.child₀))} raceEdge5 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool5 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool6 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.deliverWhole A.child₀))} raceEdge6 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool6 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool7 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.finishChildUnwind (ident 21)))} raceEdge7 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool7 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool8 exitedModel))} {u = (raceClosed)} {a = (physicalStep (P.deregisterProtocol (ident 21)))} raceEdge8 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool8 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool9 exitedModel))} {u = (raceClosed)} {a = (physicalStep (P.asyncProtocolResult (ident 21)))} raceEdge9 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool9 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool10 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.joinWhole A.child₀))} raceEdge10 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool10 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool11 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.requestWholeCancel A.child₀))} raceEdge11 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool11 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool12 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.joinWhole A.child₀))} raceEdge12 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool12 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool13 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.requestWholeCancel A.child₀))} raceEdge13 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool13 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool14 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.deliverWhole A.child₀))} raceEdge14 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool14 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool15 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.finishChildUnwind (ident 1)))} raceEdge15 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool15 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool16 exitedModel))} {u = (raceClosed)} {a = (physicalStep (P.deregisterInfra A.child₀ Types.demuxer))} raceEdge16 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool16 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool17 exitedModel))} {u = (raceClosed)} {a = (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer))} raceEdge17 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool17 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool18 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.joinWhole A.child₀))} raceEdge18 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool18 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool19 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.requestWholeCancel A.child₀))} raceEdge19 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool19 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool20 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.deliverWhole A.child₀))} raceEdge20 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool20 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool21 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.finishChildUnwind (ident 0)))} raceEdge21 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool21 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool22 exitedModel))} {u = (raceClosed)} {a = (physicalStep (P.deregisterInfra A.child₀ Types.muxer))} raceEdge22 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool22 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool23 exitedModel))} {u = (raceClosed)} {a = (physicalStep (P.asyncInfraResult A.child₀ Types.muxer))} raceEdge23 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool23 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool24 exitedModel))} {u = (raceClosed)} {a = (shutdownStep (Group.joinWhole A.child₀))} raceEdge24 (V.more {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool24 exitedModel))} {t = (raceClosed)} {u = (raceClosed)} {a = (shutdownStep (Group.finishWholeClose A.child₀))} raceEdge25 (V.stop {s = (raceClosed)})))))))))))))))))))))))))
          initialized-race-pool-close : V.Runs initial raceClosedActions raceClosed
          initialized-race-pool-close = Facts.append-protocols initialized-race-capture race-pool-path

        -- Catch and finally retain the old typed FIFO, including after Failed.
        raceFailed raceDead raceSampled : Y.Model
        raceFailed = Y.sourceMux (record (Y.withWanton jid Mux.initiatorJob Y.m1) { status = Mux.failed shutdownError }) [] (withPool racePool25 exitedModel)
        raceDead = Y.sourceMux (record (Y.withWanton jid Mux.initiatorJob Y.m1) { status = Mux.failed shutdownError; callback = Mux.readActive Mux.muxStopped }) [] (withPool racePool25 exitedModel)
        raceSampled = Y.sourceMux (record (Y.withWanton jid Mux.initiatorJob Y.m1) { status = Mux.failed shutdownError; callback = Mux.commitTrace false Mux.muxStopped }) [] (withPool racePool25 exitedModel)
        raceStatus raceInvoked raceSampledRuntime raceCommitted raceReady : V.Runtime
        raceStatus = groupAt (Group.asyncFailureWritten shutdownError) raceFailed
        raceInvoked = groupAt (Group.asyncDeadTracing shutdownError) raceDead
        raceSampledRuntime = groupAt (Group.asyncDeadTracing shutdownError) raceSampled
        raceCommitted = groupAt (Group.asyncDeadTracing shutdownError) raceFailed
        raceReady = groupAt (Group.scopeDone (Group.asyncExit shutdownError)) raceFailed
        raceCatch1 : V.advance (shutdownStep (Group.writeAsyncFailure A.child₀)) raceClosed ≡ just raceStatus
        raceCatch1 = refl
        raceCatch2 : V.advance (shutdownStep (Group.beginAsyncDead A.child₀)) raceStatus ≡ just raceInvoked
        raceCatch2 = refl
        raceCatch3 : V.advance (shutdownStep (Group.sampleAsyncTracer A.child₀)) raceInvoked ≡ just raceSampledRuntime
        raceCatch3 = refl
        raceCatch4 : V.advance (shutdownStep (Group.commitAsyncTracer A.child₀)) raceSampledRuntime ≡ just raceCommitted
        raceCatch4 = refl
        raceCatch5 : V.advance (shutdownStep (Group.finishAsyncDead A.child₀)) raceCommitted ≡ just raceReady
        raceCatch5 = refl
        raceCatchActions : List V.Event
        raceCatchActions = raceClosedActions ++ normalCatchActions
        abstract
          initialized-race-catch : V.Runs initial raceCatchActions raceReady
          initialized-race-catch = Facts.append-protocols initialized-race-pool-close (V.more {s = raceClosed} {t = raceStatus} {u = raceReady} {a = (shutdownStep (Group.writeAsyncFailure A.child₀))} raceCatch1 (V.more {s = raceStatus} {t = raceInvoked} {u = raceReady} {a = (shutdownStep (Group.beginAsyncDead A.child₀))} raceCatch2 (V.more {s = raceInvoked} {t = raceSampledRuntime} {u = raceReady} {a = (shutdownStep (Group.sampleAsyncTracer A.child₀))} raceCatch3 (V.more {s = raceSampledRuntime} {t = raceCommitted} {u = raceReady} {a = (shutdownStep (Group.commitAsyncTracer A.child₀))} raceCatch4 (V.more {s = raceCommitted} {t = raceReady} {u = raceReady} {a = (shutdownStep (Group.finishAsyncDead A.child₀))} raceCatch5 (V.stop {s = raceReady}))))))
        raceHandlerAt : W.Phase → Shared.State → V.Runtime
        raceHandlerAt pc world = SC.Completion.withHandlerExit pc
          (groupAt (Group.scopeDone (Group.asyncExit shutdownError)) (record raceFailed { world = world }))
        raceHandler1 raceHandler2 raceHandler3 raceHandler4 raceHandler5 raceHandler6 raceHandler7 raceHandler8 raceHandler9 raceHandler10 : V.Runtime
        raceHandler1 = raceHandlerAt (W.bufferScope (Group.asyncExit shutdownError)) cleanupWorld0
        raceHandler2 = raceHandlerAt (W.bodyExited (W.asyncException shutdownError)) cleanupWorld0
        raceHandler3 = raceHandlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld1
        raceHandler4 = raceHandlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld2
        raceHandler5 = raceHandlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld3
        raceHandler6 = raceHandlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld4
        raceHandler7 = raceHandlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld5
        raceHandler8 = raceHandlerAt (W.finalizing (W.asyncException shutdownError)) cleanupWorld6
        raceHandler9 = raceHandlerAt (W.cleanupComplete (W.asyncException shutdownError) Shared.cleanupNormal) cleanupWorld6
        raceHandler10 = raceHandlerAt (W.resultAvailable (W.asyncException shutdownError) Shared.cleanupNormal) cleanupWorld6
        raceFinalCM raceServer : V.Runtime
        raceFinalCM = SC.coordinated (Close.shutdownState Close.closed (ident 0 ∷ []) [] (A.child₀ ∷ [])) raceHandler10
        raceServer = record raceFinalCM { base = record (V.base raceFinalCM)
          { server = record (K.server (V.base raceFinalCM))
            { base = record (E.base (K.server (V.base raceFinalCM))) { stage = S.serverReturned } } } }

        raceFinishEdge1 : V.advance (handlerAction (W.beginExit A.child₀)) raceReady ≡ just raceHandler1
        raceFinishEdge1 = refl

        raceFinishEdge2 : V.advance (handlerAction (W.observeBufferReturn A.child₀)) raceHandler1 ≡ just raceHandler2
        raceFinishEdge2 = refl

        raceFinishEdge3 : V.advance (handlerAction (W.enterFinalizer A.child₀)) raceHandler2 ≡ just raceHandler3
        raceFinishEdge3 = refl

        raceFinishEdge4 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap)) raceHandler3 ≡ just raceHandler4
        raceFinishEdge4 = refl

        raceFinishEdge5 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry)) raceHandler4 ≡ just raceHandler5
        raceFinishEdge5 = refl

        raceFinishEdge6 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket)) raceHandler5 ≡ just raceHandler6
        raceFinishEdge6 = refl

        raceFinishEdge7 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap)) raceHandler6 ≡ just raceHandler7
        raceFinishEdge7 = refl

        raceFinishEdge8 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters)) raceHandler7 ≡ just raceHandler8
        raceFinishEdge8 = refl

        raceFinishEdge9 : V.advance (handlerAction (W.finishCleanup A.child₀)) raceHandler8 ≡ just raceHandler9
        raceFinishEdge9 = refl

        raceFinishEdge10 : V.advance (handlerAction (W.publishAsyncResult A.child₀)) raceHandler9 ≡ just raceHandler10
        raceFinishEdge10 = refl

        raceFinishEdge11 : V.advance (SC.coordinatorEvent Close.finishClose) raceHandler10 ≡ just raceFinalCM
        raceFinishEdge11 = refl

        raceFinishEdge12 : V.advance (SC.serverEvent S.finishServer) raceFinalCM ≡ just raceServer
        raceFinishEdge12 = refl

        raceFinishActions : List V.Event
        raceFinishActions = (handlerAction (W.beginExit A.child₀)) ∷ (handlerAction (W.observeBufferReturn A.child₀)) ∷ (handlerAction (W.enterFinalizer A.child₀)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters)) ∷ (handlerAction (W.finishCleanup A.child₀)) ∷ (handlerAction (W.publishAsyncResult A.child₀)) ∷ (SC.coordinatorEvent Close.finishClose) ∷ (SC.serverEvent S.finishServer) ∷ []
        raceShutdownActions : List V.Event
        raceShutdownActions = raceCatchActions ++ raceFinishActions
        abstract
          race-finish-path : V.Runs raceReady raceFinishActions raceServer
          race-finish-path = V.more {s = raceReady} {t = raceHandler1} {u = raceServer} {a = (handlerAction (W.beginExit A.child₀))} raceFinishEdge1 (V.more {s = raceHandler1} {t = raceHandler2} {u = raceServer} {a = (handlerAction (W.observeBufferReturn A.child₀))} raceFinishEdge2 (V.more {s = raceHandler2} {t = raceHandler3} {u = raceServer} {a = (handlerAction (W.enterFinalizer A.child₀))} raceFinishEdge3 (V.more {s = raceHandler3} {t = raceHandler4} {u = raceServer} {a = (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap))} raceFinishEdge4 (V.more {s = raceHandler4} {t = raceHandler5} {u = raceServer} {a = (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry))} raceFinishEdge5 (V.more {s = raceHandler5} {t = raceHandler6} {u = raceServer} {a = (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket))} raceFinishEdge6 (V.more {s = raceHandler6} {t = raceHandler7} {u = raceServer} {a = (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap))} raceFinishEdge7 (V.more {s = raceHandler7} {t = raceHandler8} {u = raceServer} {a = (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters))} raceFinishEdge8 (V.more {s = raceHandler8} {t = raceHandler9} {u = raceServer} {a = (handlerAction (W.finishCleanup A.child₀))} raceFinishEdge9 (V.more {s = raceHandler9} {t = raceHandler10} {u = raceServer} {a = (handlerAction (W.publishAsyncResult A.child₀))} raceFinishEdge10 (V.more {s = raceHandler10} {t = raceFinalCM} {u = raceServer} {a = (SC.coordinatorEvent Close.finishClose)} raceFinishEdge11 (V.more {s = raceFinalCM} {t = raceServer} {u = raceServer} {a = (SC.serverEvent S.finishServer)} raceFinishEdge12 (V.stop {s = raceServer}))))))))))))
          initialized-publication-race-return : V.Runs initial raceShutdownActions raceServer
          initialized-publication-race-return = Facts.append-protocols initialized-race-catch race-finish-path
        race-shutdown-supply : Inv.ProtocolValid raceServer
        race-shutdown-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-publication-race-return

        -- Retain the actual physical result table at CM's successful wait.
        raceHandlerStateOf : V.Runtime → W.State
        raceHandlerStateOf s = N.R.base (N.raw (V.publication (V.base s)))
        race-handler-wait : HandlerFacts.PhysicalWait (raceHandlerStateOf raceHandler10) (raceHandlerStateOf raceFinalCM)
        race-handler-wait = HandlerFacts.physical-wait-observation (raceHandlerStateOf raceHandler10) refl

        -- These observations refer to the actual initialized race states.
        raceSnapshotRetained : Pool.snapshot racePool25 ≡ capturedPhysicalOrder
        raceSnapshotRetained = refl
        raceJoinsRetained : Pool.joined racePool25 ≡ capturedPhysicalOrder
        raceJoinsRetained = refl
        raceMixedResults : All.All (PhysicalFacts.Terminal racePool25) (Pool.snapshot racePool25)
        raceMixedResults = (Pool.cancelledExit , refl) All.∷ (Pool.normalExit , refl) All.∷
          (Pool.cancelledExit , refl) All.∷ (Pool.cancelledExit , refl) All.∷ All.[]
        old-normal-result-before-cancel-request : lookup jid (Pool.handles racePool4) ≡ just (Pool.resultAvailable Pool.normalExit)
        old-normal-result-before-cancel-request = refl
        removed-old-handle-still-captured : Pool.remaining racePool4 ≡ capturedPhysicalOrder
        removed-old-handle-still-captured = refl
        old-request-skips-delivery : Pool.phase racePool11 ≡ Pool.joinPending jid
        old-request-skips-delivery = refl
        no-delivery-to-finished-old-child : V.advance (shutdownStep (Group.deliverWhole A.child₀))
          (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool11 exitedModel)) ≡ nothing
        no-delivery-to-finished-old-child = refl
        no-new-result-from-old-publication : V.observe (ident 21)
          (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool4 exitedModel)) ≡ nothing
        no-new-result-from-old-publication = refl
        new-body-still-live-after-old-publication : lookup (ident 21) (Pool.handles racePool4) ≡ just Pool.bodyRunning
        new-body-still-live-after-old-publication = refl
        no-pop-during-pool-close : V.advance (monitorStep (N.M.consume A.child₀))
          (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool4 exitedModel)) ≡ nothing
        no-pop-during-pool-close = refl
        exact-old-fifo-after-close : Pool.completions racePool25 ≡ payload ∷ []
        exact-old-fifo-after-close = refl
        exact-old-fifo-after-server-return : Pool.completions (P.poolAt A.child₀ (V.physical (V.base raceServer))) ≡ payload ∷ []
        exact-old-fifo-after-server-return = refl
        no-late-pop-after-return : V.advance (monitorStep (N.M.consume A.child₀)) raceServer ≡ nothing
        no-late-pop-after-return = refl
        old-cell-remains-clean-in-race : V.observe rid raceServer ≡ just (V.localResult clean)
        old-cell-remains-clean-in-race = refl
        current-cell-remains-empty-in-race : lookup (ident 21) (V.calls (V.front raceServer)) ≡ just (record requested { thread = just (ident 21) })
        current-cell-remains-empty-in-race = refl
        current-cell-observes-real-race-shutdown : V.observe (ident 21) raceServer ≡ just (V.shutdownResult (Mux.failed shutdownError))
        current-cell-observes-real-race-shutdown = refl
        race-cm-waits-for-handler-result : V.advance (SC.coordinatorEvent Close.finishClose) raceHandler9 ≡ nothing
        race-cm-waits-for-handler-result = refl
        race-handler-async-outcome : W.resultOf A.child₀ (raceHandlerStateOf raceServer) ≡ just (W.asyncException shutdownError)
        race-handler-async-outcome = refl
        actual-race-server-return : S.stage (E.base (K.server (V.base raceServer))) ≡ S.serverReturned
        actual-race-server-return = refl
        actual-race-cm-closed : Close.phase (W.shutdown (raceHandlerStateOf raceServer)) ≡ Close.closed
        actual-race-cm-closed = refl
        race-map-purged : Shared.mapCell (Shared.cm (Machine.world (O.core (V.sourceOf raceServer)))) ≡ Shared.full []
        race-map-purged = refl
        race-socket-closed : lookup (Shared.handlerSocket I.captured) (Shared.sockets (Machine.world (O.core (V.sourceOf raceServer)))) ≡ just Shared.closed
        race-socket-closed = refl
        race-raw-worker-unjoined : lookup A.w₁ (S.workers (E.base (K.server (V.base raceServer)))) ≡ just (S.rawWorker F.r₁ S.calling 0)
        race-raw-worker-unjoined = refl
        race-refutes-all-worker-completion :
          (∀ {t} (as : List V.Event) → V.Runs initial as t →
            S.stage (E.base (K.server (V.base t))) ≡ S.serverReturned →
            S.allResults (S.workers (E.base (K.server (V.base t)))) ≡ true) → ⊥
        race-refutes-all-worker-completion claim =
          SC.Completion.false-not-true (claim raceShutdownActions initialized-publication-race-return actual-race-server-return)

        raceStart52 : V.Runtime
        raceStart52 = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool0 exitedModel))
        abstract
          race-start-frame : Lifecycle52.FramedRuns (receipt5) (shutdownStep (Group.beginWholeClose A.child₀ capturedPhysicalOrder) ∷ []) raceStart52
          race-start-frame = Lifecycle52.frameNext {s = (receipt5)} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical1 exitedModel))} {u = raceStart52} {event = (shutdownStep (Group.beginWholeClose A.child₀ capturedPhysicalOrder))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.beginWholeClose A.child₀ capturedPhysicalOrder))) (receipt5) poolCloseEdge1) poolCloseEdge1 (Lifecycle52.frameDone {s = raceStart52})
        abstract
          race-pool-frame : Lifecycle52.FramedRuns (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool0 exitedModel)) (raceActions) (raceClosed)
          race-pool-frame = Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool0 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool1 exitedModel))} {u = (raceClosed)} {event = (physicalStep (P.returnProtocol jid))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.returnProtocol jid)))))))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool0 exitedModel)) raceEdge1) raceEdge1 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool1 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool2 exitedModel))} {u = (raceClosed)} {event = (physicalStep (P.publishProtocol jid))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.publishProtocol jid)))))))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool1 exitedModel)) raceEdge2) raceEdge2 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool2 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool3 exitedModel))} {u = (raceClosed)} {event = (physicalStep (P.deregisterProtocol jid))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.deregisterProtocol jid)))))))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool2 exitedModel)) raceEdge3) raceEdge3 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool3 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool4 exitedModel))} {u = (raceClosed)} {event = (physicalStep (P.asyncProtocolResult jid))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.asyncProtocolResult jid)))))))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool3 exitedModel)) raceEdge4) raceEdge4 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool4 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool5 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.requestWholeCancel A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.requestWholeCancel A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool4 exitedModel)) raceEdge5) raceEdge5 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool5 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool6 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.deliverWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.deliverWhole A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool5 exitedModel)) raceEdge6) raceEdge6 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool6 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool7 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.finishChildUnwind (ident 21)))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.finishChildUnwind (ident 21)))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool6 exitedModel)) raceEdge7) raceEdge7 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool7 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool8 exitedModel))} {u = (raceClosed)} {event = (physicalStep (P.deregisterProtocol (ident 21)))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.deregisterProtocol (ident 21))))))))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool7 exitedModel)) raceEdge8) raceEdge8 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool8 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool9 exitedModel))} {u = (raceClosed)} {event = (physicalStep (P.asyncProtocolResult (ident 21)))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.asyncProtocolResult (ident 21))))))))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool8 exitedModel)) raceEdge9) raceEdge9 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool9 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool10 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.joinWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.joinWhole A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool9 exitedModel)) raceEdge10) raceEdge10 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool10 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool11 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.requestWholeCancel A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.requestWholeCancel A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool10 exitedModel)) raceEdge11) raceEdge11 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool11 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool12 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.joinWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.joinWhole A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool11 exitedModel)) raceEdge12) raceEdge12 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool12 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool13 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.requestWholeCancel A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.requestWholeCancel A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool12 exitedModel)) raceEdge13) raceEdge13 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool13 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool14 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.deliverWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.deliverWhole A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool13 exitedModel)) raceEdge14) raceEdge14 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool14 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool15 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.finishChildUnwind (ident 1)))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.finishChildUnwind (ident 1)))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool14 exitedModel)) raceEdge15) raceEdge15 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool15 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool16 exitedModel))} {u = (raceClosed)} {event = (physicalStep (P.deregisterInfra A.child₀ Types.demuxer))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.deregisterInfra A.child₀ Types.demuxer)))))))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool15 exitedModel)) raceEdge16) raceEdge16 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool16 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool17 exitedModel))} {u = (raceClosed)} {event = (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.asyncInfraResult A.child₀ Types.demuxer)))))))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool16 exitedModel)) raceEdge17) raceEdge17 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool17 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool18 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.joinWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.joinWhole A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool17 exitedModel)) raceEdge18) raceEdge18 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool18 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool19 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.requestWholeCancel A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.requestWholeCancel A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool18 exitedModel)) raceEdge19) raceEdge19 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool19 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool20 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.deliverWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.deliverWhole A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool19 exitedModel)) raceEdge20) raceEdge20 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool20 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool21 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.finishChildUnwind (ident 0)))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.finishChildUnwind (ident 0)))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool20 exitedModel)) raceEdge21) raceEdge21 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool21 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool22 exitedModel))} {u = (raceClosed)} {event = (physicalStep (P.deregisterInfra A.child₀ Types.muxer))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.deregisterInfra A.child₀ Types.muxer)))))))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool21 exitedModel)) raceEdge22) raceEdge22 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool22 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool23 exitedModel))} {u = (raceClosed)} {event = (physicalStep (P.asyncInfraResult A.child₀ Types.muxer))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.asyncInfraResult A.child₀ Types.muxer)))))))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool22 exitedModel)) raceEdge23) raceEdge23 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool23 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool24 exitedModel))} {u = (raceClosed)} {event = (shutdownStep (Group.joinWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.joinWhole A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool23 exitedModel)) raceEdge24) raceEdge24 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool24 exitedModel))} {t = (raceClosed)} {u = (raceClosed)} {event = (shutdownStep (Group.finishWholeClose A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.finishWholeClose A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool racePool24 exitedModel)) raceEdge25) raceEdge25 (Lifecycle52.frameDone {s = (raceClosed)})))))))))))))))))))))))))
        abstract
          race-catch-frame : Lifecycle52.FramedRuns raceClosed (normalCatchActions) raceReady
          race-catch-frame = Lifecycle52.frameNext {s = raceClosed} {t = raceStatus} {u = raceReady} {event = (shutdownStep (Group.writeAsyncFailure A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.writeAsyncFailure A.child₀))) raceClosed raceCatch1) raceCatch1 (Lifecycle52.frameNext {s = raceStatus} {t = raceInvoked} {u = raceReady} {event = (shutdownStep (Group.beginAsyncDead A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.beginAsyncDead A.child₀))) raceStatus raceCatch2) raceCatch2 (Lifecycle52.frameNext {s = raceInvoked} {t = raceSampledRuntime} {u = raceReady} {event = (shutdownStep (Group.sampleAsyncTracer A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.sampleAsyncTracer A.child₀))) raceInvoked raceCatch3) raceCatch3 (Lifecycle52.frameNext {s = raceSampledRuntime} {t = raceCommitted} {u = raceReady} {event = (shutdownStep (Group.commitAsyncTracer A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.commitAsyncTracer A.child₀))) raceSampledRuntime raceCatch4) raceCatch4 (Lifecycle52.frameNext {s = raceCommitted} {t = raceReady} {u = raceReady} {event = (shutdownStep (Group.finishAsyncDead A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.finishAsyncDead A.child₀))) raceCommitted raceCatch5) raceCatch5 (Lifecycle52.frameDone {s = raceReady})))))
        abstract
          race-finalizer-frame : Lifecycle52.FramedRuns raceReady (take 10 raceFinishActions) raceHandler10
          race-finalizer-frame = Lifecycle52.frameNext {s = raceReady} {t = raceHandler1} {u = raceHandler10} {event = (handlerAction (W.beginExit A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.beginExit A.child₀)) raceReady raceFinishEdge1) raceFinishEdge1 (Lifecycle52.frameNext {s = raceHandler1} {t = raceHandler2} {u = raceHandler10} {event = (handlerAction (W.observeBufferReturn A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.observeBufferReturn A.child₀)) raceHandler1 raceFinishEdge2) raceFinishEdge2 (Lifecycle52.frameNext {s = raceHandler2} {t = raceHandler3} {u = raceHandler10} {event = (handlerAction (W.enterFinalizer A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.enterFinalizer A.child₀)) raceHandler2 raceFinishEdge3) raceFinishEdge3 (Lifecycle52.frameNext {s = raceHandler3} {t = raceHandler4} {u = raceHandler10} {event = (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.cleanup A.child₀ Cleanup.takeCleanupMap)) raceHandler3 raceFinishEdge4) raceFinishEdge4 (Lifecycle52.frameNext {s = raceHandler4} {t = raceHandler5} {u = raceHandler10} {event = (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.cleanup A.child₀ Cleanup.selectCleanupEntry)) raceHandler4 raceFinishEdge5) raceFinishEdge5 (Lifecycle52.frameNext {s = raceHandler5} {t = raceHandler6} {u = raceHandler10} {event = (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.cleanup A.child₀ Cleanup.closeHandlerSocket)) raceHandler5 raceFinishEdge6) raceFinishEdge6 (Lifecycle52.frameNext {s = raceHandler6} {t = raceHandler7} {u = raceHandler10} {event = (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.cleanup A.child₀ Cleanup.publishCleanupMap)) raceHandler6 raceFinishEdge7) raceFinishEdge7 (Lifecycle52.frameNext {s = raceHandler7} {t = raceHandler8} {u = raceHandler10} {event = (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.cleanup A.child₀ Cleanup.readCleanupCounters)) raceHandler7 raceFinishEdge8) raceFinishEdge8 (Lifecycle52.frameNext {s = raceHandler8} {t = raceHandler9} {u = raceHandler10} {event = (handlerAction (W.finishCleanup A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.finishCleanup A.child₀)) raceHandler8 raceFinishEdge9) raceFinishEdge9 (Lifecycle52.frameNext {s = raceHandler9} {t = raceHandler10} {u = raceHandler10} {event = (handlerAction (W.publishAsyncResult A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.publishAsyncResult A.child₀)) raceHandler9 raceFinishEdge10) raceFinishEdge10 (Lifecycle52.frameDone {s = raceHandler10}))))))))))

      -- A current clean completion can win after cancellation was requested,
      -- while its physical body still has not received that exception.
      module CurrentClean where
        pendingChild : V.Runtime
        pendingChild = groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel)
        -- The current child's actual entry allocates its own empty wanton.
        exitedModel21 : Y.Model
        exitedModel21 = enterIn (ident 21) exitedModel
        pendingEntered : V.Runtime
        pendingEntered = groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel21)
        currentBodyReturned : V.Runtime
        currentBodyReturned = V.runtime (V.setPhysical
          (record (V.physical (V.base pendingEntered))
            { jobs = put (ident 21) (secondJob Types.waitingEgress) (P.jobs (V.physical (V.base pendingEntered))) })
          (V.base pendingEntered)) (V.front pendingEntered)

        -- Expected snapshots change only the current job, its result cell and
        -- the matching peer cache. Successful actual steps justify them below.
        -- Every snapshot after the current child's actual entry retains its
        -- empty wanton in the one source mux; put makes this idempotent.
        withEntry : P.State → P.State
        withEntry p with P.muxAt (ident 0) p
        ... | nothing = p
        ... | just m = P.setSource (record (P.source p) { core = record (O.core (P.source p))
          { inboundGovernor = IG.setMux (ident 0) (Y.withWanton (ident 21) Mux.initiatorJob m)
              (Machine.inboundGovernor (O.core (P.source p))) } }) p
        withCurrentClean : V.Runtime → V.Runtime
        withCurrentClean original = V.runtime
          (V.cacheResult (ident 21) requested clean (V.front original)
            (V.setPhysical (record (withEntry p) { jobs = put (ident 21) (secondJob (Types.resultCaptured clean)) (P.jobs p) }) (V.base original)))
          (record (V.front original)
            { calls = put (ident 21) (record requested { thread = just (ident 21); value = just clean }) (V.calls (V.front original)) })
          where
          p = V.physical (V.base original)
        currentCommitted : V.Runtime
        currentCommitted = withCurrentClean pendingEntered
        cleanRequestActions : List V.Event
        cleanRequestActions = entryAndReceiptActions ++
          (shutdownStep (Group.beginWholeClose A.child₀ capturedPhysicalOrder) ∷
           shutdownStep (Group.requestWholeCancel A.child₀) ∷ [])
        abstract
          initialized-current-cancel-request : V.Runs initial cleanRequestActions pendingChild
          initialized-current-cancel-request = Facts.append-protocols initialized-normal-monitor-receipt
            (V.more poolCloseEdge1 (V.more poolCloseEdge2 V.stop))
        currentEntryEdge : V.advance (physicalStep (P.enterProtocolBody (ident 21))) pendingChild ≡ just pendingEntered
        currentEntryEdge = refl
        currentReturnEdge : V.advance (physicalStep (P.protocolReturned (ident 21))) pendingEntered ≡ just currentBodyReturned
        currentReturnEdge = refl
        currentCommitEdge : V.advance (V.commitClean (ident 21)) currentBodyReturned ≡ just currentCommitted
        currentCommitEdge = refl
        cleanCommitActions : List V.Event
        cleanCommitActions = cleanRequestActions ++ (physicalStep (P.enterProtocolBody (ident 21)) ∷ physicalStep (P.protocolReturned (ident 21)) ∷ V.commitClean (ident 21) ∷ [])
        abstract
          initialized-current-clean-commit : V.Runs initial cleanCommitActions currentCommitted
          initialized-current-clean-commit = Facts.append-protocols initialized-current-cancel-request
            (V.more currentEntryEdge (V.more currentReturnEdge (V.more currentCommitEdge V.stop)))

        cleanEdge1 : V.advance (shutdownStep (Group.deliverWhole A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel))))
        cleanEdge1 = refl

        cleanEdge2 : V.advance (shutdownStep (Group.finishChildUnwind (ident 21))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical4 exitedModel))))
        cleanEdge2 = refl

        cleanEdge3 : V.advance (physicalStep (P.deregisterProtocol (ident 21))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical4 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical5 exitedModel))))
        cleanEdge3 = refl

        cleanEdge4 : V.advance (physicalStep (P.asyncProtocolResult (ident 21))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical5 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical6 exitedModel))))
        cleanEdge4 = refl

        cleanEdge5 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical6 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical7 exitedModel))))
        cleanEdge5 = refl

        cleanEdge6 : V.advance (shutdownStep (Group.requestWholeCancel A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical7 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical8 exitedModel))))
        cleanEdge6 = refl

        cleanEdge7 : V.advance (shutdownStep (Group.deliverWhole A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical8 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel))))
        cleanEdge7 = refl

        cleanEdge8 : V.advance (shutdownStep (Group.finishChildUnwind (ident 20))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical10 exitedModel))))
        cleanEdge8 = refl

        cleanEdge9 : V.advance (physicalStep (P.deregisterProtocol (ident 20))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical10 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical11 exitedModel))))
        cleanEdge9 = refl

        cleanEdge10 : V.advance (physicalStep (P.asyncProtocolResult (ident 20))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical11 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical12 exitedModel))))
        cleanEdge10 = refl

        cleanEdge11 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical12 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical13 exitedModel))))
        cleanEdge11 = refl

        cleanEdge12 : V.advance (shutdownStep (Group.requestWholeCancel A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical13 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical14 exitedModel))))
        cleanEdge12 = refl

        cleanEdge13 : V.advance (shutdownStep (Group.deliverWhole A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical14 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical15 exitedModel))))
        cleanEdge13 = refl

        cleanEdge14 : V.advance (shutdownStep (Group.finishChildUnwind (ident 1))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical15 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical16 exitedModel))))
        cleanEdge14 = refl

        cleanEdge15 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.demuxer)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical16 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical17 exitedModel))))
        cleanEdge15 = refl

        cleanEdge16 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical17 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical18 exitedModel))))
        cleanEdge16 = refl

        cleanEdge17 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical18 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical19 exitedModel))))
        cleanEdge17 = refl

        cleanEdge18 : V.advance (shutdownStep (Group.requestWholeCancel A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical19 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical20 exitedModel))))
        cleanEdge18 = refl

        cleanEdge19 : V.advance (shutdownStep (Group.deliverWhole A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical20 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical21 exitedModel))))
        cleanEdge19 = refl

        cleanEdge20 : V.advance (shutdownStep (Group.finishChildUnwind (ident 0))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical21 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical22 exitedModel))))
        cleanEdge20 = refl

        cleanEdge21 : V.advance (physicalStep (P.deregisterInfra A.child₀ Types.muxer)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical22 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical23 exitedModel))))
        cleanEdge21 = refl

        cleanEdge22 : V.advance (physicalStep (P.asyncInfraResult A.child₀ Types.muxer)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical23 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical24 exitedModel))))
        cleanEdge22 = refl

        cleanEdge23 : V.advance (shutdownStep (Group.joinWhole A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical24 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel))))
        cleanEdge23 = refl

        cleanEdge24 : V.advance (shutdownStep (Group.finishWholeClose A.child₀)) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel)))) ≡ just (withCurrentClean ((groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))))
        cleanEdge24 = refl

        cleanEdge25 : V.advance (shutdownStep (Group.writeAsyncFailure A.child₀)) (withCurrentClean (wholePoolClosed)) ≡ just (withCurrentClean (failedStatus))
        cleanEdge25 = refl

        cleanEdge26 : V.advance (shutdownStep (Group.beginAsyncDead A.child₀)) (withCurrentClean (failedStatus)) ≡ just (withCurrentClean (deadInvoked))
        cleanEdge26 = refl

        cleanEdge27 : V.advance (shutdownStep (Group.sampleAsyncTracer A.child₀)) (withCurrentClean (deadInvoked)) ≡ just (withCurrentClean (deadSampled))
        cleanEdge27 = refl

        cleanEdge28 : V.advance (shutdownStep (Group.commitAsyncTracer A.child₀)) (withCurrentClean (deadSampled)) ≡ just (withCurrentClean (deadCommitted))
        cleanEdge28 = refl

        cleanEdge29 : V.advance (shutdownStep (Group.finishAsyncDead A.child₀)) (withCurrentClean (deadCommitted)) ≡ just (withCurrentClean (readyForBuffer))
        cleanEdge29 = refl

        cleanEdge30 : V.advance (handlerAction (W.beginExit A.child₀)) (withCurrentClean (readyForBuffer)) ≡ just (withCurrentClean (handler1))
        cleanEdge30 = refl

        cleanEdge31 : V.advance (handlerAction (W.observeBufferReturn A.child₀)) (withCurrentClean (handler1)) ≡ just (withCurrentClean (handler2))
        cleanEdge31 = refl

        cleanEdge32 : V.advance (handlerAction (W.enterFinalizer A.child₀)) (withCurrentClean (handler2)) ≡ just (withCurrentClean (handler3))
        cleanEdge32 = refl

        cleanEdge33 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap)) (withCurrentClean (handler3)) ≡ just (withCurrentClean (handler4))
        cleanEdge33 = refl

        cleanEdge34 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry)) (withCurrentClean (handler4)) ≡ just (withCurrentClean (handler5))
        cleanEdge34 = refl

        cleanEdge35 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket)) (withCurrentClean (handler5)) ≡ just (withCurrentClean (handler6))
        cleanEdge35 = refl

        cleanEdge36 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap)) (withCurrentClean (handler6)) ≡ just (withCurrentClean (handler7))
        cleanEdge36 = refl

        cleanEdge37 : V.advance (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters)) (withCurrentClean (handler7)) ≡ just (withCurrentClean (handler8))
        cleanEdge37 = refl

        cleanEdge38 : V.advance (handlerAction (W.finishCleanup A.child₀)) (withCurrentClean (handler8)) ≡ just (withCurrentClean (handler9))
        cleanEdge38 = refl

        cleanEdge39 : V.advance (handlerAction (W.publishAsyncResult A.child₀)) (withCurrentClean (handler9)) ≡ just (withCurrentClean (handler10))
        cleanEdge39 = refl

        cleanEdge40 : V.advance (SC.coordinatorEvent Close.finishClose) (withCurrentClean (handler10)) ≡ just (withCurrentClean (finalCM))
        cleanEdge40 = refl

        cleanEdge41 : V.advance (SC.serverEvent S.finishServer) (withCurrentClean (finalCM)) ≡ just (withCurrentClean (returnedServer))
        cleanEdge41 = refl

        cleanContinuationActions : List V.Event
        cleanContinuationActions = (shutdownStep (Group.deliverWhole A.child₀)) ∷ (shutdownStep (Group.finishChildUnwind (ident 21))) ∷ (physicalStep (P.deregisterProtocol (ident 21))) ∷ (physicalStep (P.asyncProtocolResult (ident 21))) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.requestWholeCancel A.child₀)) ∷ (shutdownStep (Group.deliverWhole A.child₀)) ∷ (shutdownStep (Group.finishChildUnwind (ident 20))) ∷ (physicalStep (P.deregisterProtocol (ident 20))) ∷ (physicalStep (P.asyncProtocolResult (ident 20))) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.requestWholeCancel A.child₀)) ∷ (shutdownStep (Group.deliverWhole A.child₀)) ∷ (shutdownStep (Group.finishChildUnwind (ident 1))) ∷ (physicalStep (P.deregisterInfra A.child₀ Types.demuxer)) ∷ (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer)) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.requestWholeCancel A.child₀)) ∷ (shutdownStep (Group.deliverWhole A.child₀)) ∷ (shutdownStep (Group.finishChildUnwind (ident 0))) ∷ (physicalStep (P.deregisterInfra A.child₀ Types.muxer)) ∷ (physicalStep (P.asyncInfraResult A.child₀ Types.muxer)) ∷ (shutdownStep (Group.joinWhole A.child₀)) ∷ (shutdownStep (Group.finishWholeClose A.child₀)) ∷ (shutdownStep (Group.writeAsyncFailure A.child₀)) ∷ (shutdownStep (Group.beginAsyncDead A.child₀)) ∷ (shutdownStep (Group.sampleAsyncTracer A.child₀)) ∷ (shutdownStep (Group.commitAsyncTracer A.child₀)) ∷ (shutdownStep (Group.finishAsyncDead A.child₀)) ∷ (handlerAction (W.beginExit A.child₀)) ∷ (handlerAction (W.observeBufferReturn A.child₀)) ∷ (handlerAction (W.enterFinalizer A.child₀)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap)) ∷ (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters)) ∷ (handlerAction (W.finishCleanup A.child₀)) ∷ (handlerAction (W.publishAsyncResult A.child₀)) ∷ (SC.coordinatorEvent Close.finishClose) ∷ (SC.serverEvent S.finishServer) ∷ []
        cleanShutdownActions : List V.Event
        cleanShutdownActions = cleanCommitActions ++ cleanContinuationActions
        cleanServer : V.Runtime
        cleanServer = withCurrentClean returnedServer
        abstract
          clean-continuation-path : V.Runs currentCommitted cleanContinuationActions cleanServer
          clean-continuation-path = V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.deliverWhole A.child₀))} cleanEdge1 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical4 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.finishChildUnwind (ident 21)))} cleanEdge2 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical4 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical5 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (physicalStep (P.deregisterProtocol (ident 21)))} cleanEdge3 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical5 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical6 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (physicalStep (P.asyncProtocolResult (ident 21)))} cleanEdge4 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical6 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical7 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.joinWhole A.child₀))} cleanEdge5 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical7 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical8 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.requestWholeCancel A.child₀))} cleanEdge6 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical8 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.deliverWhole A.child₀))} cleanEdge7 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical10 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.finishChildUnwind (ident 20)))} cleanEdge8 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical10 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical11 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (physicalStep (P.deregisterProtocol (ident 20)))} cleanEdge9 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical11 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical12 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (physicalStep (P.asyncProtocolResult (ident 20)))} cleanEdge10 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical12 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical13 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.joinWhole A.child₀))} cleanEdge11 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical13 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical14 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.requestWholeCancel A.child₀))} cleanEdge12 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical14 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical15 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.deliverWhole A.child₀))} cleanEdge13 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical15 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical16 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.finishChildUnwind (ident 1)))} cleanEdge14 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical16 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical17 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (physicalStep (P.deregisterInfra A.child₀ Types.demuxer))} cleanEdge15 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical17 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical18 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer))} cleanEdge16 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical18 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical19 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.joinWhole A.child₀))} cleanEdge17 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical19 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical20 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.requestWholeCancel A.child₀))} cleanEdge18 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical20 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical21 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.deliverWhole A.child₀))} cleanEdge19 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical21 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical22 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.finishChildUnwind (ident 0)))} cleanEdge20 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical22 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical23 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (physicalStep (P.deregisterInfra A.child₀ Types.muxer))} cleanEdge21 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical23 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical24 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (physicalStep (P.asyncInfraResult A.child₀ Types.muxer))} cleanEdge22 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical24 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.joinWhole A.child₀))} cleanEdge23 (V.more {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.finishWholeClose A.child₀))} cleanEdge24 (V.more {s = (withCurrentClean (wholePoolClosed))} {t = (withCurrentClean (failedStatus))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.writeAsyncFailure A.child₀))} cleanEdge25 (V.more {s = (withCurrentClean (failedStatus))} {t = (withCurrentClean (deadInvoked))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.beginAsyncDead A.child₀))} cleanEdge26 (V.more {s = (withCurrentClean (deadInvoked))} {t = (withCurrentClean (deadSampled))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.sampleAsyncTracer A.child₀))} cleanEdge27 (V.more {s = (withCurrentClean (deadSampled))} {t = (withCurrentClean (deadCommitted))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.commitAsyncTracer A.child₀))} cleanEdge28 (V.more {s = (withCurrentClean (deadCommitted))} {t = (withCurrentClean (readyForBuffer))} {u = (withCurrentClean (returnedServer))} {a = (shutdownStep (Group.finishAsyncDead A.child₀))} cleanEdge29 (V.more {s = (withCurrentClean (readyForBuffer))} {t = (withCurrentClean (handler1))} {u = (withCurrentClean (returnedServer))} {a = (handlerAction (W.beginExit A.child₀))} cleanEdge30 (V.more {s = (withCurrentClean (handler1))} {t = (withCurrentClean (handler2))} {u = (withCurrentClean (returnedServer))} {a = (handlerAction (W.observeBufferReturn A.child₀))} cleanEdge31 (V.more {s = (withCurrentClean (handler2))} {t = (withCurrentClean (handler3))} {u = (withCurrentClean (returnedServer))} {a = (handlerAction (W.enterFinalizer A.child₀))} cleanEdge32 (V.more {s = (withCurrentClean (handler3))} {t = (withCurrentClean (handler4))} {u = (withCurrentClean (returnedServer))} {a = (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap))} cleanEdge33 (V.more {s = (withCurrentClean (handler4))} {t = (withCurrentClean (handler5))} {u = (withCurrentClean (returnedServer))} {a = (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry))} cleanEdge34 (V.more {s = (withCurrentClean (handler5))} {t = (withCurrentClean (handler6))} {u = (withCurrentClean (returnedServer))} {a = (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket))} cleanEdge35 (V.more {s = (withCurrentClean (handler6))} {t = (withCurrentClean (handler7))} {u = (withCurrentClean (returnedServer))} {a = (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap))} cleanEdge36 (V.more {s = (withCurrentClean (handler7))} {t = (withCurrentClean (handler8))} {u = (withCurrentClean (returnedServer))} {a = (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters))} cleanEdge37 (V.more {s = (withCurrentClean (handler8))} {t = (withCurrentClean (handler9))} {u = (withCurrentClean (returnedServer))} {a = (handlerAction (W.finishCleanup A.child₀))} cleanEdge38 (V.more {s = (withCurrentClean (handler9))} {t = (withCurrentClean (handler10))} {u = (withCurrentClean (returnedServer))} {a = (handlerAction (W.publishAsyncResult A.child₀))} cleanEdge39 (V.more {s = (withCurrentClean (handler10))} {t = (withCurrentClean (finalCM))} {u = (withCurrentClean (returnedServer))} {a = (SC.coordinatorEvent Close.finishClose)} cleanEdge40 (V.more {s = (withCurrentClean (finalCM))} {t = (withCurrentClean (returnedServer))} {u = (withCurrentClean (returnedServer))} {a = (SC.serverEvent S.finishServer)} cleanEdge41 (V.stop {s = (withCurrentClean (returnedServer))})))))))))))))))))))))))))))))))))))))))))
          initialized-current-clean-return : V.Runs initial cleanShutdownActions cleanServer
          initialized-current-clean-return = Facts.append-protocols initialized-current-clean-commit clean-continuation-path
        clean-return-supply : Inv.ProtocolValid cleanServer
        clean-return-supply = Inv.from-initial-protocols initializer (All.[] , All.[]) initialized-current-clean-return

        -- A local clean cell is neither a typed FIFO publication nor an Async
        -- result. CM must still wait for the actual captured handler result.
        clean-handler-wait : HandlerFacts.PhysicalWait
          (handlerStateOf (withCurrentClean handler10)) (handlerStateOf (withCurrentClean finalCM))
        clean-handler-wait = HandlerFacts.physical-wait-observation (handlerStateOf (withCurrentClean handler10)) refl
        clean-four-results : All.All (PhysicalFacts.Terminal
          (P.poolAt A.child₀ (V.physical (V.base cleanServer)))) capturedPhysicalOrder
        clean-four-results = (Pool.cancelledExit , refl) All.∷ (Pool.cancelledExit , refl) All.∷
          (Pool.cancelledExit , refl) All.∷ (Pool.cancelledExit , refl) All.∷ All.[]
        no-result-before-clean-commit : V.observe (ident 21) currentBodyReturned ≡ nothing
        no-result-before-clean-commit = refl
        current-clean-before-delivery : V.observe (ident 21) currentCommitted ≡ just (V.localResult clean)
        current-clean-before-delivery = refl
        pending-delivery-after-clean-commit : Pool.phase (P.poolAt A.child₀ (V.physical (V.base currentCommitted))) ≡ Pool.cancelPending (ident 21)
        pending-delivery-after-clean-commit = refl
        physical-body-not-yet-finished : lookup (ident 21) (Pool.handles (P.poolAt A.child₀ (V.physical (V.base currentCommitted)))) ≡ just Pool.bodyRunning
        physical-body-not-yet-finished = refl
        clean-cell-before-async-result : V.advance (physicalStep (P.asyncProtocolResult (ident 21))) currentCommitted ≡ nothing
        clean-cell-before-async-result = refl
        no-invented-physical-publication : V.advance (physicalStep (P.publishProtocol (ident 21))) currentCommitted ≡ nothing
        no-invented-physical-publication = refl
        no-second-current-cell-write : V.advance (V.commitError (ident 21) err) currentCommitted ≡ nothing
        no-second-current-cell-write = refl
        current-clean-survives-failed : V.observe (ident 21) (withCurrentClean failedStatus) ≡ just (V.localResult clean)
        current-clean-survives-failed = refl
        current-clean-survives-return : V.observe (ident 21) cleanServer ≡ just (V.localResult clean)
        current-clean-survives-return = refl
        original-clean-survives-current-race : V.observe rid cleanServer ≡ just (V.localResult clean)
        original-clean-survives-current-race = refl
        actual-failed-mux-with-clean-cell : P.muxAt (ident 0) (V.physical (V.base cleanServer)) ≡ just (record (Y.withWanton (ident 21) Mux.initiatorJob (Y.withWanton jid Mux.initiatorJob Y.m1)) { status = Mux.failed shutdownError })
        actual-failed-mux-with-clean-cell = refl
        no-current-typed-result-invented : Pool.completions (P.poolAt A.child₀ (V.physical (V.base cleanServer))) ≡ []
        no-current-typed-result-invented = refl
        physical-current-result-is-cancelled : lookup (ident 21) (Pool.handles (P.poolAt A.child₀ (V.physical (V.base cleanServer)))) ≡ just (Pool.resultAvailable Pool.cancelledExit)
        physical-current-result-is-cancelled = refl
        clean-cell-does-not-complete-handler : W.resultReady A.child₀ (handlerStateOf (withCurrentClean readyForBuffer)) ≡ false
        clean-cell-does-not-complete-handler = refl
        clean-cell-does-not-close-cm : V.advance (SC.coordinatorEvent Close.finishClose) (withCurrentClean handler9) ≡ nothing
        clean-cell-does-not-close-cm = refl
        actual-clean-race-handler-outcome : W.resultOf A.child₀ (handlerStateOf cleanServer) ≡ just (W.asyncException shutdownError)
        actual-clean-race-handler-outcome = refl
        actual-clean-race-server-return : S.stage (E.base (K.server (V.base cleanServer))) ≡ S.serverReturned
        actual-clean-race-server-return = refl
        clean-race-refutes-all-worker-completion :
          (∀ {t} (as : List V.Event) → V.Runs initial as t →
            S.stage (E.base (K.server (V.base t))) ≡ S.serverReturned →
            S.allResults (S.workers (E.base (K.server (V.base t)))) ≡ true) → ⊥
        clean-race-refutes-all-worker-completion claim =
          SC.Completion.false-not-true (claim cleanShutdownActions initialized-current-clean-return actual-clean-race-server-return)

  -- Generic preservation is instantiated on initialized clean/error histories.
  -- The duplicate-key control is explicitly malformed and unreachable.
        abstract
          clean-request-frame : Lifecycle52.FramedRuns (receipt5) (shutdownStep (Group.beginWholeClose A.child₀ capturedPhysicalOrder) ∷ shutdownStep (Group.requestWholeCancel A.child₀) ∷ []) pendingChild
          clean-request-frame = Lifecycle52.frameNext {s = (receipt5)} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical1 exitedModel))} {u = pendingChild} {event = (shutdownStep (Group.beginWholeClose A.child₀ capturedPhysicalOrder))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.beginWholeClose A.child₀ capturedPhysicalOrder))) (receipt5) poolCloseEdge1) poolCloseEdge1 (Lifecycle52.frameNext {s = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical1 exitedModel))} {t = (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel))} {u = pendingChild} {event = (shutdownStep (Group.requestWholeCancel A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.requestWholeCancel A.child₀))) (groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical1 exitedModel)) poolCloseEdge2) poolCloseEdge2 (Lifecycle52.frameDone {s = pendingChild}))
        abstract
          clean-commit-frame : Lifecycle52.FramedRuns pendingChild (physicalStep (P.enterProtocolBody (ident 21)) ∷ physicalStep (P.protocolReturned (ident 21)) ∷ V.commitClean (ident 21) ∷ []) currentCommitted
          clean-commit-frame = Lifecycle52.frameNext {s = pendingChild} {t = pendingEntered} {u = currentCommitted} {event = (physicalStep (P.enterProtocolBody (ident 21)))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.enterProtocolBody (ident 21))))))))) pendingChild currentEntryEdge) currentEntryEdge (Lifecycle52.frameNext {s = pendingEntered} {t = currentBodyReturned} {u = currentCommitted} {event = (physicalStep (P.protocolReturned (ident 21)))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.protocolReturned (ident 21))))))))) pendingEntered currentReturnEdge) currentReturnEdge (Lifecycle52.frameNext {s = currentBodyReturned} {t = currentCommitted} {u = currentCommitted} {event = (V.commitClean (ident 21))} refl currentCommitEdge (Lifecycle52.frameDone {s = currentCommitted})))
        abstract
          clean-finalizer-frame : Lifecycle52.FramedRuns (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel)))) (take 39 cleanContinuationActions) (withCurrentClean (handler10))
          clean-finalizer-frame = Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.deliverWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.deliverWhole A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical2 exitedModel)))) cleanEdge1) cleanEdge1 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical4 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.finishChildUnwind (ident 21)))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.finishChildUnwind (ident 21)))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical3 exitedModel)))) cleanEdge2) cleanEdge2 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical4 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical5 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (physicalStep (P.deregisterProtocol (ident 21)))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.deregisterProtocol (ident 21))))))))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical4 exitedModel)))) cleanEdge3) cleanEdge3 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical5 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical6 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (physicalStep (P.asyncProtocolResult (ident 21)))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.asyncProtocolResult (ident 21))))))))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical5 exitedModel)))) cleanEdge4) cleanEdge4 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical6 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical7 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.joinWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.joinWhole A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical6 exitedModel)))) cleanEdge5) cleanEdge5 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical7 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical8 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.requestWholeCancel A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.requestWholeCancel A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical7 exitedModel)))) cleanEdge6) cleanEdge6 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical8 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.deliverWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.deliverWhole A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical8 exitedModel)))) cleanEdge7) cleanEdge7 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical10 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.finishChildUnwind (ident 20)))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.finishChildUnwind (ident 20)))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical9 exitedModel)))) cleanEdge8) cleanEdge8 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical10 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical11 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (physicalStep (P.deregisterProtocol (ident 20)))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.deregisterProtocol (ident 20))))))))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical10 exitedModel)))) cleanEdge9) cleanEdge9 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical11 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical12 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (physicalStep (P.asyncProtocolResult (ident 20)))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.asyncProtocolResult (ident 20))))))))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical11 exitedModel)))) cleanEdge10) cleanEdge10 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical12 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical13 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.joinWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.joinWhole A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical12 exitedModel)))) cleanEdge11) cleanEdge11 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical13 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical14 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.requestWholeCancel A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.requestWholeCancel A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical13 exitedModel)))) cleanEdge12) cleanEdge12 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical14 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical15 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.deliverWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.deliverWhole A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical14 exitedModel)))) cleanEdge13) cleanEdge13 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical15 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical16 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.finishChildUnwind (ident 1)))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.finishChildUnwind (ident 1)))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical15 exitedModel)))) cleanEdge14) cleanEdge14 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical16 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical17 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (physicalStep (P.deregisterInfra A.child₀ Types.demuxer))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.deregisterInfra A.child₀ Types.demuxer)))))))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical16 exitedModel)))) cleanEdge15) cleanEdge15 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical17 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical18 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (physicalStep (P.asyncInfraResult A.child₀ Types.demuxer))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.asyncInfraResult A.child₀ Types.demuxer)))))))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical17 exitedModel)))) cleanEdge16) cleanEdge16 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical18 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical19 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.joinWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.joinWhole A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical18 exitedModel)))) cleanEdge17) cleanEdge17 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical19 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical20 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.requestWholeCancel A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.requestWholeCancel A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical19 exitedModel)))) cleanEdge18) cleanEdge18 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical20 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical21 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.deliverWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.deliverWhole A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical20 exitedModel)))) cleanEdge19) cleanEdge19 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical21 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical22 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.finishChildUnwind (ident 0)))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.finishChildUnwind (ident 0)))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical21 exitedModel)))) cleanEdge20) cleanEdge20 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical22 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical23 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (physicalStep (P.deregisterInfra A.child₀ Types.muxer))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.deregisterInfra A.child₀ Types.muxer)))))))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical22 exitedModel)))) cleanEdge21) cleanEdge21 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical23 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical24 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (physicalStep (P.asyncInfraResult A.child₀ Types.muxer))} (Lifecycle52.server-framed (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run (P.asyncInfraResult A.child₀ Types.muxer)))))))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical23 exitedModel)))) cleanEdge22) cleanEdge22 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical24 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.joinWhole A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.joinWhole A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical24 exitedModel)))) cleanEdge23) cleanEdge23 (Lifecycle52.frameNext {s = (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel))))} {t = (withCurrentClean ((groupAt (Group.wholeClosed (Group.asyncExit shutdownError)) (withPool physical26 exitedModel))))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.finishWholeClose A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.finishWholeClose A.child₀))) (withCurrentClean ((groupAt (Group.wholeClosing (Group.asyncExit shutdownError)) (withPool physical25 exitedModel)))) cleanEdge24) cleanEdge24 (Lifecycle52.frameNext {s = (withCurrentClean (wholePoolClosed))} {t = (withCurrentClean (failedStatus))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.writeAsyncFailure A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.writeAsyncFailure A.child₀))) (withCurrentClean (wholePoolClosed)) cleanEdge25) cleanEdge25 (Lifecycle52.frameNext {s = (withCurrentClean (failedStatus))} {t = (withCurrentClean (deadInvoked))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.beginAsyncDead A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.beginAsyncDead A.child₀))) (withCurrentClean (failedStatus)) cleanEdge26) cleanEdge26 (Lifecycle52.frameNext {s = (withCurrentClean (deadInvoked))} {t = (withCurrentClean (deadSampled))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.sampleAsyncTracer A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.sampleAsyncTracer A.child₀))) (withCurrentClean (deadInvoked)) cleanEdge27) cleanEdge27 (Lifecycle52.frameNext {s = (withCurrentClean (deadSampled))} {t = (withCurrentClean (deadCommitted))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.commitAsyncTracer A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.commitAsyncTracer A.child₀))) (withCurrentClean (deadSampled)) cleanEdge28) cleanEdge28 (Lifecycle52.frameNext {s = (withCurrentClean (deadCommitted))} {t = (withCurrentClean (readyForBuffer))} {u = (withCurrentClean (handler10))} {event = (shutdownStep (Group.finishAsyncDead A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.run (Group.finishAsyncDead A.child₀))) (withCurrentClean (deadCommitted)) cleanEdge29) cleanEdge29 (Lifecycle52.frameNext {s = (withCurrentClean (readyForBuffer))} {t = (withCurrentClean (handler1))} {u = (withCurrentClean (handler10))} {event = (handlerAction (W.beginExit A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.beginExit A.child₀)) (withCurrentClean (readyForBuffer)) cleanEdge30) cleanEdge30 (Lifecycle52.frameNext {s = (withCurrentClean (handler1))} {t = (withCurrentClean (handler2))} {u = (withCurrentClean (handler10))} {event = (handlerAction (W.observeBufferReturn A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.observeBufferReturn A.child₀)) (withCurrentClean (handler1)) cleanEdge31) cleanEdge31 (Lifecycle52.frameNext {s = (withCurrentClean (handler2))} {t = (withCurrentClean (handler3))} {u = (withCurrentClean (handler10))} {event = (handlerAction (W.enterFinalizer A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.enterFinalizer A.child₀)) (withCurrentClean (handler2)) cleanEdge32) cleanEdge32 (Lifecycle52.frameNext {s = (withCurrentClean (handler3))} {t = (withCurrentClean (handler4))} {u = (withCurrentClean (handler10))} {event = (handlerAction (W.cleanup A.child₀ Cleanup.takeCleanupMap))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.cleanup A.child₀ Cleanup.takeCleanupMap)) (withCurrentClean (handler3)) cleanEdge33) cleanEdge33 (Lifecycle52.frameNext {s = (withCurrentClean (handler4))} {t = (withCurrentClean (handler5))} {u = (withCurrentClean (handler10))} {event = (handlerAction (W.cleanup A.child₀ Cleanup.selectCleanupEntry))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.cleanup A.child₀ Cleanup.selectCleanupEntry)) (withCurrentClean (handler4)) cleanEdge34) cleanEdge34 (Lifecycle52.frameNext {s = (withCurrentClean (handler5))} {t = (withCurrentClean (handler6))} {u = (withCurrentClean (handler10))} {event = (handlerAction (W.cleanup A.child₀ Cleanup.closeHandlerSocket))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.cleanup A.child₀ Cleanup.closeHandlerSocket)) (withCurrentClean (handler5)) cleanEdge35) cleanEdge35 (Lifecycle52.frameNext {s = (withCurrentClean (handler6))} {t = (withCurrentClean (handler7))} {u = (withCurrentClean (handler10))} {event = (handlerAction (W.cleanup A.child₀ Cleanup.publishCleanupMap))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.cleanup A.child₀ Cleanup.publishCleanupMap)) (withCurrentClean (handler6)) cleanEdge36) cleanEdge36 (Lifecycle52.frameNext {s = (withCurrentClean (handler7))} {t = (withCurrentClean (handler8))} {u = (withCurrentClean (handler10))} {event = (handlerAction (W.cleanup A.child₀ Cleanup.readCleanupCounters))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.cleanup A.child₀ Cleanup.readCleanupCounters)) (withCurrentClean (handler7)) cleanEdge37) cleanEdge37 (Lifecycle52.frameNext {s = (withCurrentClean (handler8))} {t = (withCurrentClean (handler9))} {u = (withCurrentClean (handler10))} {event = (handlerAction (W.finishCleanup A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.finishCleanup A.child₀)) (withCurrentClean (handler8)) cleanEdge38) cleanEdge38 (Lifecycle52.frameNext {s = (withCurrentClean (handler9))} {t = (withCurrentClean (handler10))} {u = (withCurrentClean (handler10))} {event = (handlerAction (W.publishAsyncResult A.child₀))} (Lifecycle52.server-framed (Lifecycle52.handler-action (W.publishAsyncResult A.child₀)) (withCurrentClean (handler9)) cleanEdge39) cleanEdge39 (Lifecycle52.frameDone {s = (withCurrentClean (handler10))})))))))))))))))))))))))))))))))))))))))

  module CellPreservationChecks where
    open import Data.Empty using (⊥)
    import Data.List.Relation.Unary.AllPairs as Pairs
    import ConnectionManagement.Properties.Stores as Stores
    private
      module Cells = Facts.CommittedCells
      module CC = Reactivation.Shutdown.CurrentClean
    currentCleanCall : V.Call
    currentCleanCall = record requested { thread = just (ident 21); value = just clean }
    generic-current-record-retained : lookup (ident 21) (V.calls (V.front CC.cleanServer)) ≡ just currentCleanCall
    generic-current-record-retained = Cells.from-initial-keeps initializer CC.initialized-current-clean-commit
      CC.clean-continuation-path (ident 21) currentCleanCall clean refl refl
    generic-current-observation-retained : V.observe (ident 21) CC.cleanServer ≡ just (V.localResult clean)
    generic-current-observation-retained = Cells.from-initial-observe initializer CC.initialized-current-clean-commit
      CC.clean-continuation-path (ident 21) currentCleanCall clean refl refl

    errorCapturedCall : V.Call
    errorCapturedCall = record requested { thread = just jid; value = just (errored err) }
    errorTypedResult : Types.TypedResult
    errorTypedResult = Types.protocolCompletion Mux.initiatorJob 1 rid (errored err)
    errorReturnedModel : Y.Model
    errorReturnedModel = withPool (record bornPool
      { handles = put jid (Pool.bodyReturned errorTypedResult) (Pool.handles bornPool) }) errorModel
    errorReturnEdge : V.advance (physicalStep (P.returnProtocol jid)) (at errorModel errorContext errorFront) ≡
      just (at errorReturnedModel errorContext errorFront)
    errorReturnEdge = refl
    generic-error-record-retained : lookup rid (V.calls (V.front (at errorReturnedModel errorContext errorFront))) ≡ just errorCapturedCall
    generic-error-record-retained = Cells.from-initial-keeps initializer initialized-error
      (V.more {a = physicalStep (P.returnProtocol jid)} errorReturnEdge V.stop) rid errorCapturedCall (errored err) refl refl
    generic-error-observation-retained : V.observe rid (at errorReturnedModel errorContext errorFront) ≡ just (V.localResult (errored err))
    generic-error-observation-retained = Cells.from-initial-observe initializer initialized-error
      (V.more {a = physicalStep (P.returnProtocol jid)} errorReturnEdge V.stop) rid errorCapturedCall (errored err) refl refl

    -- byThread can reach a later duplicate behind a committed first binding.
    -- This cannot arise from initialize and the fresh-generation start guard.
    duplicateCleanCall duplicateEmptyCall : V.Call
    duplicateCleanCall = record requested { value = just clean }
    duplicateEmptyCall = record requested { thread = just jid }
    duplicateFront duplicateAfterFront : V.Front
    duplicateFront = record bornFront { calls = (rid , duplicateCleanCall) ∷ (rid , duplicateEmptyCall) ∷ [] }
    duplicateAfterFront = record duplicateFront { calls = (rid , errorCapturedCall) ∷ (rid , duplicateEmptyCall) ∷ [] }
    duplicateBefore duplicateAfter : V.Runtime
    duplicateBefore = at waiting k63 duplicateFront
    duplicateAfter = at errorModel errorContext duplicateAfterFront
    malformed-duplicate-step : V.advance (V.commitError jid err) duplicateBefore ≡ just duplicateAfter
    malformed-duplicate-step = refl
    duplicate-table-not-unique : Stores.UniqueKeys (V.calls duplicateFront) → ⊥
    duplicate-table-not-unique ((apart All.∷ rest) Pairs.∷ unique) = apart refl
    changed-duplicate-result : lookup rid (V.calls duplicateAfterFront) ≡ just duplicateCleanCall → ⊥
    changed-duplicate-result ()
    no-arbitrary-table-preservation :
      (∀ a s {t} → V.advance a s ≡ just t → Cells.Keeps (V.calls (V.front s)) (V.calls (V.front t))) → ⊥
    no-arbitrary-table-preservation claim = changed-duplicate-result
      (claim (V.commitError jid err) duplicateBefore malformed-duplicate-step rid duplicateCleanCall clean refl refl)

  -- Capture certificates are derived from the actual initialized histories.
  -- Historical presence does not imply that the child is still executing.
  module ThreadCaptureChecks where
    open import Data.Empty using (⊥)
    private
      module Capture = BFacts.CaptureIdentity.Frontend capability
      module CC = Reactivation.Shutdown.CurrentClean
    initialized-clean-captures : Capture.Valid CC.cleanServer
    initialized-clean-captures = Capture.initialized-soundness initializer CC.initialized-current-clean-return
    initialized-error-captures : Capture.Valid (at errorModel errorContext errorFront)
    initialized-error-captures = Capture.initialized-soundness initializer initialized-error
    initialized-restart-captures : Capture.Valid
      (at Reactivation.secondBodyAvailable Reactivation.secondCooledContext Reactivation.secondErrorFront)
    initialized-restart-captures = Capture.initialized-soundness initializer Reactivation.initialized-reactivation

    -- A fabricated reference with no physical row cannot satisfy the invariant.
    no-unbacked-reference : Capture.Sound ((rid , record requested { thread = just jid }) ∷ []) [] → ⊥
    no-unbacked-reference claim with claim rid (record requested { thread = just jid }) jid refl refl
    ... | job , () , matches

  -- Local cells must agree with the current historical physical result row.
  module LocalResultChecks where
    open import Data.Empty using (⊥)
    import ConnectionManagement.Properties.ServerPeersResults as ResultsProof
    private
      module Results = ResultsProof I.bearerClosed Prior.classify
      module Agreement = Results.Frontend capability
      module CC = Reactivation.Shutdown.CurrentClean
    clean-shutdown-agreement : Agreement.Valid CC.cleanServer
    clean-shutdown-agreement = Agreement.initialized-soundness initializer CC.initialized-current-clean-return
    error-agreement : Agreement.Valid (at errorModel errorContext errorFront)
    error-agreement = Agreement.initialized-soundness initializer initialized-error
    restart-agreement : Agreement.Valid
      (at Reactivation.secondBodyAvailable Reactivation.secondCooledContext Reactivation.secondErrorFront)
    restart-agreement = Agreement.initialized-soundness initializer Reactivation.initialized-reactivation
    current-clean-physical-result : Agreement.Backed CellPreservationChecks.currentCleanCall clean
      (P.jobs (V.physical (V.base CC.cleanServer)))
    current-clean-physical-result = clean-shutdown-agreement (ident 21) CellPreservationChecks.currentCleanCall clean refl refl

    -- A fabricated committed cell with no physical job is rejected.
    no-unbacked-commit : Agreement.Sound ((rid , record requested { thread = just jid; value = just clean }) ∷ []) [] → ⊥
    no-unbacked-commit claim with claim rid (record requested { thread = just jid; value = just clean }) clean refl refl
    ... | j , threaded , job , () , phase

    -- Presence of the right handle alone cannot justify a different result.
    open import Data.Maybe.Properties using (just-injective)
    cleanPhysical : Types.ProtocolJob
    cleanPhysical = Types.protocolJob (V.owner requested) (V.mux requested) Mux.initiatorJob 1 rid (Types.resultCaptured clean)
    errorCell : V.Call
    errorCell = record requested { thread = just jid; value = just (errored err) }
    no-clean-row-for-error-cell : Agreement.Sound ((rid , errorCell) ∷ []) ((jid , cleanPhysical) ∷ []) → ⊥
    no-clean-row-for-error-cell claim with claim rid errorCell (errored err) refl refl
    ... | j , threaded , job , seen , phase with just-injective threaded
    ...   | refl with just-injective seen
    ...     | refl with phase
    ...       | ()

  -- Generic reader certificates instantiated on actual poll/wait events.
  module ObservationChecks where
    open import Data.Empty using (⊥)
    import ConnectionManagement.Properties.ServerPeersResults as ResultsProof
    private
      module Readers = ResultsProof.Observations I.bearerClosed Prior.classify capability
      module CC = Reactivation.Shutdown.CurrentClean
    initialized-shutdown-poll : Readers.PollRead (ident 0) (ident 50)
      (at failedBeforeFork Waiters.livePublished zeroFront)
    initialized-shutdown-poll = Readers.initialized-poll (ident 0) (ident 50) initializer
      (Facts.append-protocols initialized-shutdown-observation
        (V.more {a = ps L.a64} Waiters.published-after-failure V.stop)) Waiters.poll-shutdown
    initialized-clean-wait : Readers.MonitorRead (ident 0)
      (at afterCleanFailed (Waiters.followupContext Waiters.cleanWait Waiters.deactivatingClean) freeFront)
    initialized-clean-wait = Readers.initialized-monitor-wait (ident 0) initializer
      (Facts.append-protocols initialized-local-priority
        (V.more {a = ps L.a64} Waiters.clean1
          (V.more {a = V.pollResults (ident 0) (ident 50)} Waiters.clean2
            (V.more {a = ps (Sub.monitorStep (ident 0) J.enter)} Waiters.clean3 V.stop)))) Waiters.clean4
    initialized-shutdown-job : Readers.JobRead (ident 2) (at failedBeforeFork Waiters.d95 zeroFront)
    initialized-shutdown-job = Readers.initialized-job-wait (ident 2) initializer
      (Facts.append-protocols
        (Facts.append-protocols (Facts.append-protocols initialized-to-start before-select-path) Waiters.deactivation-prefix)
        (V.more {a = physicalStep (P.infrastructureReturn A.child₀ Types.muxer err)} Waiters.fail1
          (V.more {a = physicalStep (P.publishInfra A.child₀ Types.muxer)} Waiters.fail2
            (V.more {a = monitorStep (N.M.consume A.child₀)} Waiters.fail3
              (V.more {a = monitorStep (N.M.handleSelected A.child₀)} Waiters.fail4 V.stop))))) Waiters.wait-deactivation-shutdown

    clean-shutdown-readable : Readers.Readable CC.cleanServer
    clean-shutdown-readable = Readers.initialized-readable initializer CC.initialized-current-clean-return
    current-clean-observation : Readers.Outcome CC.cleanServer (ident 21) CellPreservationChecks.currentCleanCall (V.localResult clean)
    current-clean-observation = Readers.observe-proof (ident 21) CellPreservationChecks.currentCleanCall CC.cleanServer
      (V.localResult clean) clean-shutdown-readable refl refl
    error-observation : Readers.Outcome (at errorModel errorContext errorFront) rid
      CellPreservationChecks.errorCapturedCall (V.localResult (errored err))
    error-observation = Readers.observe-proof rid CellPreservationChecks.errorCapturedCall (at errorModel errorContext errorFront)
      (V.localResult (errored err)) (Readers.initialized-readable initializer initialized-error) refl refl
    restart-readable : Readers.Readable Reactivation.secondCooledRuntime
    restart-readable = Readers.initialized-readable initializer Reactivation.initialized-reactivation
    restart-first : Readers.Pick hot (ident 0) Reactivation.secondPromotedPeer Reactivation.secondCooledRuntime 1 (V.localResult (errored err))
    restart-first = Readers.first-proof hot (ident 0) Reactivation.secondPromotedPeer Reactivation.secondCooledRuntime 1
      (V.localResult (errored err)) restart-readable refl
    current-error-call : V.Call
    current-error-call = record requested { thread = just (ident 21); value = just (errored err) }
    restarted-observation : Readers.Outcome Reactivation.secondCooledRuntime (ident 21) current-error-call (V.localResult (errored err))
    restarted-observation = Readers.observe-proof (ident 21) current-error-call Reactivation.secondCooledRuntime
      (V.localResult (errored err)) restart-readable refl refl
    actual-shutdown-observation : Readers.Outcome (at failedBeforeFork k63 zeroFront) rid requested (V.shutdownResult (Mux.failed err))
    actual-shutdown-observation = Readers.observe-proof rid requested (at failedBeforeFork k63 zeroFront)
      (V.shutdownResult (Mux.failed err)) (Readers.initialized-readable initializer initialized-shutdown-observation) refl refl
    ready-is-not-shutdown : Readers.NonReady Mux.ready → ⊥
    ready-is-not-shutdown ()

    -- Arbitrary supplied peers can carry constants without any local call.
    -- Certify them as constants rather than inventing physical generation rows.
    cached-run retired-run : Peer.ProtocolRun
    cached-run = Peer.protocolRun proto (Peer.returned clean) (Peer.returned clean)
    retired-run = Peer.protocolRun proto (Peer.notRunning clean) (Peer.notRunning clean)
    cached-peer retired-peer : Peer.Peer
    cached-peer = record L.p15 { runs = cached-run ∷ [] }
    retired-peer = record L.p15 { runs = retired-run ∷ [] }
    constant-first : Readers.Pick hot (ident 0) cached-peer initial 1 (V.localResult clean)
    constant-first = Readers.first-proof hot (ident 0) cached-peer initial 1 (V.localResult clean)
      (Readers.initialized-readable initializer V.stop) refl
    retired-all : All.All (λ { (n , observation) → Readers.Pick hot (ident 0) retired-peer initial n observation })
      ((1 , V.localResult clean) ∷ [])
    retired-all = Readers.all-proof hot (ident 0) retired-peer initial ((1 , V.localResult clean) ∷ [])
      (Readers.initialized-readable initializer V.stop) refl
    constants-have-no-live-generation : ∀ rid r → Readers.Selection (ident 0) cached-peer cached-run initial rid r → ⊥
    constants-have-no-live-generation rid r claim with Readers.Selection.published claim
    ... | ()
    retired-first-blocks : V.firstPublished hot (ident 0) retired-peer initial ≡ nothing
    retired-first-blocks = refl
    wrong-peer-cannot-select-live : V.publishedCell (ident 99) (shiftPeer L.p15)
      (Peer.protocolRun proto Peer.running Peer.running) (at failedBeforeFork Waiters.livePublished zeroFront) ≡ V.blocked
    wrong-peer-cannot-select-live = refl


  -- Initialized cache constants keep historical backing across a new start.
  module CacheChecks where
    open import Data.Empty using (⊥)
    open import Data.List using (take)
    open import Data.List.Relation.Unary.Any using (here)
    open import Data.Maybe.Properties using (just-injective)
    import ConnectionManagement.Properties.ServerPeersCache as CacheProof
    import ConnectionManagement.Properties.ServerPeersResults as ResultsProof
    private
      module Root = CacheProof I.bearerClosed Prior.classify
      module Cache = Root.Frontend capability
      module Readers = ResultsProof.Observations I.bearerClosed Prior.classify capability
      module CC = Reactivation.Shutdown.CurrentClean
    secondStartActions : List V.Event
    secondStartActions = (prefixActions ++ Reactivation.firstCompletedActions) ++ take 61 Reactivation.reactivationActions
    abstract
      initialized-second-start : V.Runs initial secondStartActions Reactivation.secondQueuedRuntime
      initialized-second-start = Facts.append-protocols Reactivation.initialized-first-completed
        (V.more Reactivation.reactEdge1 (V.more Reactivation.reactEdge2 (V.more Reactivation.reactEdge3 (V.more Reactivation.reactEdge4 (V.more Reactivation.reactEdge5 (V.more Reactivation.reactEdge6 (V.more Reactivation.reactEdge7 (V.more Reactivation.reactEdge8 (V.more Reactivation.reactEdge9 (V.more Reactivation.reactEdge10 (V.more Reactivation.reactEdge11 (V.more Reactivation.reactEdge12 (V.more Reactivation.reactEdge13 (V.more Reactivation.reactEdge14 (V.more Reactivation.reactEdge15 (V.more Reactivation.reactEdge16 (V.more Reactivation.reactEdge17 (V.more Reactivation.reactEdge18 (V.more Reactivation.reactEdge19 (V.more Reactivation.reactEdge20 (V.more Reactivation.reactEdge21 (V.more Reactivation.reactEdge22 (V.more Reactivation.reactEdge23 (V.more Reactivation.reactEdge24 (V.more Reactivation.reactEdge25 (V.more Reactivation.reactEdge26 (V.more Reactivation.reactEdge27 (V.more Reactivation.reactEdge28 (V.more Reactivation.reactEdge29 (V.more Reactivation.reactEdge30 (V.more Reactivation.reactEdge31 (V.more Reactivation.reactEdge32 (V.more Reactivation.reactEdge33 (V.more Reactivation.reactEdge34 (V.more Reactivation.reactEdge35 (V.more Reactivation.reactEdge36 (V.more Reactivation.reactEdge37 (V.more Reactivation.reactEdge38 (V.more Reactivation.reactEdge39 (V.more Reactivation.reactEdge40 (V.more Reactivation.reactEdge41 (V.more Reactivation.reactEdge42 (V.more Reactivation.reactEdge43 (V.more Reactivation.reactEdge44 (V.more Reactivation.reactEdge45 (V.more Reactivation.reactEdge46 (V.more Reactivation.reactEdge47 (V.more Reactivation.reactEdge48 (V.more Reactivation.reactEdge49 (V.more Reactivation.reactEdge50 (V.more Reactivation.reactEdge51 (V.more Reactivation.reactEdge52 (V.more Reactivation.reactEdge53 (V.more Reactivation.reactEdge54 (V.more Reactivation.reactEdge55 (V.more Reactivation.reactEdge56 (V.more Reactivation.reactEdge57 (V.more Reactivation.reactEdge58 (V.more Reactivation.reactEdge59 (V.more Reactivation.reactEdge60 (V.more Reactivation.reactEdge61 (V.stop))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

    retiredRun : Peer.ProtocolRun
    retiredRun = Peer.protocolRun proto Peer.running (Peer.notRunning clean)
    old-constant-backed : Cache.Historical Reactivation.secondQueuedRuntime (ident 0) (ident 0) (ident 0) 1 clean
    old-constant-backed = Cache.initialized-published initializer initialized-second-start (ident 0)
      Reactivation.secondStartedPeer retiredRun clean refl (here refl) Root.retired
    constant-cannot-be-current : (history : Cache.Historical Reactivation.secondQueuedRuntime (ident 0) (ident 0) (ident 0) 1 clean) →
      proj₁ history ≡ ident 21 → ⊥
    constant-cannot-be-current (rid , r , found , filled , rest) refl with just-injective found
    ... | refl with filled
    ...   | ()
    current-cell-still-empty : V.observe (ident 21) Reactivation.secondQueuedRuntime ≡ nothing
    current-cell-still-empty = refl
    retired-results : All.All (λ { (n , result) → Readers.Pick hot (ident 0) Reactivation.secondStartedPeer Reactivation.secondQueuedRuntime n result })
      ((1 , V.localResult clean) ∷ [])
    retired-results = Readers.all-proof hot (ident 0) Reactivation.secondStartedPeer Reactivation.secondQueuedRuntime
      ((1 , V.localResult clean) ∷ []) (Readers.initialized-readable initializer initialized-second-start) refl
    retired-read-backed : Cache.Historical Reactivation.secondQueuedRuntime (ident 0) (ident 0) (ident 0) 1 clean
    retired-read-backed = Cache.initialized-pick-local initializer initialized-second-start hot (ident 0)
      Reactivation.secondStartedPeer 1 clean refl (All.head retired-results)
    retired-first-still-blocks : V.firstPublished hot (ident 0) Reactivation.secondStartedPeer Reactivation.secondQueuedRuntime ≡ nothing
    retired-first-still-blocks = refl
    clean-shutdown-cache : Cache.Valid CC.cleanServer
    clean-shutdown-cache = Cache.initialized-cache initializer CC.initialized-current-clean-return
    cacheErrorPeer : Peer.Peer
    cacheErrorPeer = Peer.cool Reactivation.secondErroredPeer
    cacheErrorRun : Peer.ProtocolRun
    cacheErrorRun = Peer.protocolRun proto (Peer.returned (errored err)) Peer.running
    error-actual-backed : Cache.Historical Reactivation.secondCooledRuntime (ident 0) (ident 0) (ident 0) 1 (errored err)
    error-actual-backed = Cache.initialized-actual initializer Reactivation.initialized-reactivation
      (ident 0) cacheErrorPeer cacheErrorRun (errored err) refl (here refl) Root.returned
    live-result : Readers.Pick hot (ident 0) cacheErrorPeer Reactivation.secondCooledRuntime 1 (V.localResult (errored err))
    live-result = Readers.first-proof hot (ident 0) cacheErrorPeer Reactivation.secondCooledRuntime 1 (V.localResult (errored err))
      (Readers.initialized-readable initializer Reactivation.initialized-reactivation) refl
    live-read-backed : Cache.Historical Reactivation.secondCooledRuntime (ident 0) (ident 0) (ident 0) 1 (errored err)
    live-read-backed = Cache.initialized-pick-local initializer Reactivation.initialized-reactivation
      hot (ident 0) cacheErrorPeer 1 (errored err) refl live-result

    -- A constant supplied out of thin air cannot satisfy the initialized cache
    -- invariant, even though the generic pure reader accepts its stored value.
    forgedContext : C.Context
    forgedContext = record (K.context (V.base initial))
      { subsystem = record (C.subsystem (K.context (V.base initial)))
        { peers = (ident 0 , ObservationChecks.cached-peer) ∷ [] } }
    forged : V.Runtime
    forged = record initial { base = record (V.base initial) { context = forgedContext } }
    no-forged-cache : Cache.Valid forged → ⊥
    no-forged-cache (((actual , published) All.∷ All.[]) All.∷ All.[]) with published
    ... | rid , r , () , rest
    no-initialized-forged-cache : ∀ as → V.Runs initial as forged → ⊥
    no-initialized-forged-cache as path = no-forged-cache (Cache.initialized-cache initializer path)

  -- Full physical certificates for actual initialized result-read events.
  module PhysicalReadChecks where
    open import Data.Empty using (⊥)
    import ConnectionManagement.Properties.ServerPeersCache as CacheProof
    import ConnectionManagement.Properties.ServerPeersResults as ResultsProof
    private
      module Cache = CacheProof.Frontend I.bearerClosed Prior.classify capability
      module Readers = ResultsProof.Observations I.bearerClosed Prior.classify capability
    abstract
      published-shutdown-prefix : V.Runs initial
        (((prefixActions ++ (V.startNext (ident 1) rid ∷ ps L.a63 ∷ physicalStep (P.control A.child₀ P.selectCommand) ∷ [])) ++ fallbackActions) ++
          (ps L.a64 ∷ [])) (at failedBeforeFork Waiters.livePublished zeroFront)
      published-shutdown-prefix = Facts.append-protocols initialized-shutdown-observation
        (V.more {a = ps L.a64} Waiters.published-after-failure V.stop)
    shutdown-poll : Cache.PhysicalPoll (ident 0) (ident 50) (at failedBeforeFork Waiters.livePublished zeroFront)
    shutdown-poll = Cache.initialized-physical-poll (ident 0) (ident 50) initializer published-shutdown-prefix Waiters.poll-shutdown
    clean-monitor-wait : Cache.PhysicalMonitorWait (ident 0)
      (at afterCleanFailed (Waiters.followupContext Waiters.cleanWait Waiters.deactivatingClean) freeFront)
    clean-monitor-wait = Cache.initialized-physical-monitor-wait (ident 0) initializer
      (Facts.append-protocols initialized-local-priority
        (V.more {a = ps L.a64} Waiters.clean1
          (V.more {a = V.pollResults (ident 0) (ident 50)} Waiters.clean2
            (V.more {a = ps (Sub.monitorStep (ident 0) J.enter)} Waiters.clean3 V.stop)))) Waiters.clean4
    failed-job-wait : Cache.PhysicalJobWait (ident 2) (at failedBeforeFork Waiters.d95 zeroFront)
    failed-job-wait = Cache.initialized-physical-job-wait (ident 2) initializer
      (Facts.append-protocols
        (Facts.append-protocols (Facts.append-protocols initialized-to-start before-select-path) Waiters.deactivation-prefix)
        (V.more {a = physicalStep (P.infrastructureReturn A.child₀ Types.muxer err)} Waiters.fail1
          (V.more {a = physicalStep (P.publishInfra A.child₀ Types.muxer)} Waiters.fail2
            (V.more {a = monitorStep (N.M.consume A.child₀)} Waiters.fail3
              (V.more {a = monitorStep (N.M.handleSelected A.child₀)} Waiters.fail4 V.stop))))) Waiters.wait-deactivation-shutdown
    retired-read-physical : Cache.PhysicalObservation Reactivation.secondQueuedRuntime (ident 0)
      Reactivation.secondStartedPeer 1 (V.localResult clean)
    retired-read-physical = Cache.certify-pick initializer CacheChecks.initialized-second-start hot (ident 0)
      Reactivation.secondStartedPeer 1 (V.localResult clean) refl (All.head CacheChecks.retired-results)
    live-read-physical : Cache.PhysicalObservation Reactivation.secondCooledRuntime (ident 0)
      CacheChecks.cacheErrorPeer 1 (V.localResult (errored err))
    live-read-physical = Cache.certify-pick initializer Reactivation.initialized-reactivation hot (ident 0)
      CacheChecks.cacheErrorPeer 1 (V.localResult (errored err)) refl CacheChecks.live-result
    shutdown-read-physical : Cache.PhysicalObservation (at failedBeforeFork Waiters.livePublished zeroFront) (ident 0)
      (shiftPeer L.p15) 1 (V.shutdownResult (Mux.failed err))
    shutdown-read-physical = Cache.certify-pick initializer published-shutdown-prefix hot (ident 0) (shiftPeer L.p15) 1
      (V.shutdownResult (Mux.failed err)) refl (Readers.first-proof hot (ident 0) (shiftPeer L.p15)
        (at failedBeforeFork Waiters.livePublished zeroFront) 1 (V.shutdownResult (Mux.failed err))
        (Readers.initialized-readable initializer published-shutdown-prefix) refl)
    shutdown-before-any-protocol-body : lookup jid (P.jobs (V.physical (V.base (at failedBeforeFork Waiters.livePublished zeroFront)))) ≡ nothing
    shutdown-before-any-protocol-body = refl
    ready-cannot-be-certified : ∀ s ref peer n → Cache.PhysicalObservation s ref peer n (V.shutdownResult Mux.ready) → ⊥
    ready-cannot-be-certified s ref peer n (Cache.shutdown-fallback protocolView genId callRow .Mux.ready inRuns sameNumber selectionProof muxEvidence)
      with Readers.Fallback.nonReady muxEvidence
    ... | ()
    old-certified-generation : Cache.PhysicalObservation Reactivation.secondQueuedRuntime (ident 0)
      Reactivation.secondStartedPeer 1 (V.localResult clean) → RunId
    old-certified-generation (Cache.local-capture .clean history) = proj₁ history
    old-certificate-not-current : ∀ proof → old-certified-generation proof ≡ ident 21 → ⊥
    old-certificate-not-current (Cache.local-capture .clean history) = CacheChecks.constant-cannot-be-current history

  -- Read-to-continuation agreement, including physical no-write failure effects.
  module ContinuationChecks where
    open import Data.Empty using (⊥)
    open import Data.Sum using (inj₂)
    open import Function using (case_of_)
    import ConnectionManagement.Properties.ServerPeersContinuations as Continuations
    import ConnectionManagement.Properties.ServerPeersCache as Captures
    import ConnectionManagement.Properties.ServerPeersResults as ReaderProof
    private
      module Agreement = Continuations.Frontend I.bearerClosed Prior.classify capability
      module Read = ReaderProof.Observations I.bearerClosed Prior.classify capability
      module Root = Continuations I.bearerClosed Prior.classify
      module Physical = Captures.Frontend I.bearerClosed Prior.classify capability
    shutdownBefore shutdownAfter cleanWaitBefore cleanWaitAfter jobWaitBefore jobWaitAfter : V.Runtime
    shutdownBefore = at failedBeforeFork Waiters.livePublished zeroFront
    shutdownAfter = at failedBeforeFork Waiters.cooledPublished zeroFront
    cleanWaitBefore = at afterCleanFailed (Waiters.followupContext Waiters.cleanWait Waiters.deactivatingClean) freeFront
    cleanWaitAfter = at afterCleanFailed (Waiters.followupContext Waiters.cleanReturned Waiters.retiredClean) freeFront
    jobWaitBefore = at failedBeforeFork Waiters.d95 zeroFront
    jobWaitAfter = at failedBeforeFork Waiters.deactFailure zeroFront
    shutdown-agreement : Agreement.PollAgreement (ident 0) (ident 50) shutdownBefore shutdownAfter
    shutdown-agreement = Agreement.initialized-poll-agreement (ident 0) (ident 50) initializer
      PhysicalReadChecks.published-shutdown-prefix Waiters.poll-shutdown
    clean-monitor-agreement : Agreement.MonitorAgreement (ident 0) cleanWaitBefore cleanWaitAfter
    clean-monitor-agreement = Agreement.initialized-monitor-agreement (ident 0) initializer
      (Facts.append-protocols initialized-local-priority
        (V.more {a = ps L.a64} Waiters.clean1
          (V.more {a = V.pollResults (ident 0) (ident 50)} Waiters.clean2
            (V.more {a = ps (Sub.monitorStep (ident 0) J.enter)} Waiters.clean3 V.stop)))) Waiters.clean4
    failed-job-agreement : Agreement.JobAgreement (ident 2) jobWaitBefore jobWaitAfter
    failed-job-agreement = Agreement.initialized-job-agreement (ident 2) initializer
      (Facts.append-protocols
        (Facts.append-protocols (Facts.append-protocols initialized-to-start before-select-path) Waiters.deactivation-prefix)
        (V.more {a = physicalStep (P.infrastructureReturn A.child₀ Types.muxer err)} Waiters.fail1
          (V.more {a = physicalStep (P.publishInfra A.child₀ Types.muxer)} Waiters.fail2
            (V.more {a = monitorStep (N.M.consume A.child₀)} Waiters.fail3
              (V.more {a = monitorStep (N.M.handleSelected A.child₀)} Waiters.fail4 V.stop))))) Waiters.wait-deactivation-shutdown
    clean-wait-observations : V.allClean
      (Read.MonitorRead.results (Agreement.monitor-reader clean-monitor-agreement)) ≡ true
    clean-wait-observations = Agreement.monitor-success-clean (ident 0) cleanWaitBefore cleanWaitAfter clean-monitor-agreement Waiters.cleanReturned refl refl
    clean-wait-peer : lookup (ident 0) (C.SubContext.peers (C.subsystem (K.context (V.base cleanWaitAfter)))) ≡ just Waiters.retiredClean
    clean-wait-peer = Agreement.monitor-success-peer (ident 0) cleanWaitBefore cleanWaitAfter clean-monitor-agreement Waiters.cleanReturned refl refl
    clean-wait-captures : All.All (λ { (n , observation) → Physical.Historical cleanWaitBefore (ident 0) (ident 0) (ident 0) n clean })
      ((1 , V.localResult clean) ∷ [])
    clean-wait-captures = Agreement.monitor-success-captures (ident 0) cleanWaitBefore cleanWaitAfter clean-monitor-agreement Waiters.cleanReturned refl refl
    failed-job-effects : Agreement.FailureEffects jobWaitBefore jobWaitAfter
    failed-job-effects = proj₂ (proj₂ (Agreement.job-nonclean (ident 2) jobWaitBefore jobWaitAfter failed-job-agreement refl))
    failed-job-pool-unchanged : C.governorPool (K.context (V.base jobWaitAfter)) ≡ C.governorPool (K.context (V.base jobWaitBefore))
    failed-job-pool-unchanged = Agreement.FailureEffects.governorPool failed-job-effects
    failed-job-physical-unchanged : V.physical (V.base jobWaitAfter) ≡ V.physical (V.base jobWaitBefore)
    failed-job-physical-unchanged = Agreement.FailureEffects.physical failed-job-effects
    failed-job-continuation : lookup (ident 2) (C.SubContext.jobs (C.subsystem (K.context (V.base jobWaitAfter)))) ≡ just Waiters.deactFailedFrame
    failed-job-continuation = proj₁ (Agreement.job-nonclean (ident 2) jobWaitBefore jobWaitAfter failed-job-agreement refl)
    shutdown-effects : Agreement.FailureEffects shutdownBefore shutdownAfter
    shutdown-effects = proj₂ (proj₂ (proj₂ (Agreement.poll-nonclean (ident 0) (ident 50) shutdownBefore shutdownAfter shutdown-agreement
      (shiftPeer L.p15) G.deactivate (V.shutdownResult (Mux.failed err)) refl (inj₂ refl) refl refl refl)))
    shutdown-does-not-touch-physical : V.physical (V.base shutdownAfter) ≡ V.physical (V.base shutdownBefore)
    shutdown-does-not-touch-physical = Agreement.FailureEffects.physical shutdown-effects
    failed-wait-cannot-succeed : Root.finished (J.pc (Sub.execution Waiters.deactFailedFrame)) ≡ true → ⊥
    failed-wait-cannot-succeed succeeded = case
      Agreement.job-success-clean (ident 2) jobWaitBefore jobWaitAfter failed-job-agreement Waiters.deactFailedFrame refl succeeded of λ ()

    -- This existing close/followup snapshot is a conditional transition, not a
    -- newly asserted initialized close history or a CM-release theorem.
    conditional-close-before conditional-close-after : V.Runtime
    conditional-close-before = at failedBeforeFork (Waiters.closeContext Waiters.closeFrame) zeroFront
    conditional-close-after = at failedBeforeFork
      (Waiters.closeContext (record Waiters.closeFrame { pc = J.awaitCold G.failed })) zeroFront
    conditional-close-failure : Agreement.MonitorOutcome (ident 0) Waiters.closeFrame Waiters.closingPeer
      ((1 , V.shutdownResult (Mux.failed err)) ∷ []) conditional-close-before conditional-close-after
    conditional-close-failure = Agreement.monitor-outcome (ident 0) Waiters.closeFrame Waiters.closingPeer conditional-close-before
      ((1 , V.shutdownResult (Mux.failed err)) ∷ []) refl refl refl refl Waiters.close-all-shutdown
    conditional-close-effects : Agreement.FailureEffects conditional-close-before conditional-close-after
    conditional-close-effects with conditional-close-failure
    ... | Agreement.monitor-failed bad afterMonitor afterPeer effects = effects
    ... | Agreement.monitor-forwarded () forwarded

    shutdown-cools-active-peer : lookup (ident 0) (C.SubContext.peers (C.subsystem (K.context (V.base shutdownAfter)))) ≡ just (Peer.cool (shiftPeer L.p15))
    shutdown-cools-active-peer = proj₁ (Agreement.poll-nonclean (ident 0) (ident 50) shutdownBefore shutdownAfter shutdown-agreement
      (shiftPeer L.p15) G.deactivate (V.shutdownResult (Mux.failed err)) refl (inj₂ refl) refl refl refl)
    failed-job-demotes : lookup (ident 0) (C.SubContext.peers (C.subsystem (K.context (V.base jobWaitAfter)))) ≡ just Waiters.deactFailedPeer
    failed-job-demotes = proj₁ (proj₂ (Agreement.job-nonclean (ident 2) jobWaitBefore jobWaitAfter failed-job-agreement refl))
    failed-job-server-unchanged : K.server (V.base jobWaitAfter) ≡ K.server (V.base jobWaitBefore)
    failed-job-server-unchanged = Agreement.FailureEffects.server failed-job-effects
    failed-job-monitor-threads-unchanged : C.monitors (K.context (V.base jobWaitAfter)) ≡ C.monitors (K.context (V.base jobWaitBefore))
    failed-job-monitor-threads-unchanged = Agreement.FailureEffects.monitorThreads failed-job-effects

  -- Actual initialized governor body return followed by its separate publication.
  module CompletionChecks where
    open import Data.List using (take)
    open import Data.Product using (Σ)
    open import Relation.Binary.PropositionalEquality using (cong)
    import ConnectionManagement.Properties.ServerPeersContinuations as Continuations
    private
      module Agreement = Continuations.Frontend I.bearerClosed Prior.classify capability
      module Root = Continuations I.bearerClosed Prior.classify
    jobBefore jobReturned jobPublished jobRemoved jobAvailable : V.Runtime
    jobBefore = at registered Reactivation.down95 freeFront
    jobReturned = at registered Reactivation.warm1 freeFront
    jobPublished = at registered Reactivation.warm2 freeFront
    jobRemoved = at registered Reactivation.warm3 freeFront
    jobAvailable = at registered Reactivation.warm4 freeFront
    returnedFrame : Sub.JobFrame
    returnedFrame = Reactivation.deactivationFrame (J.complete G.succeeded) false false
    completedPrefix : List V.Event
    completedPrefix = (prefixActions ++ Reactivation.firstCompletedActions) ++ take 28 Reactivation.reactivationActions
    abstract
      initialized-job-before : V.Runs initial completedPrefix jobBefore
      initialized-job-before = Facts.append-protocols Reactivation.initialized-first-completed
        (V.more Reactivation.reactEdge1 (V.more Reactivation.reactEdge2 (V.more Reactivation.reactEdge3 (V.more Reactivation.reactEdge4 (V.more Reactivation.reactEdge5 (V.more Reactivation.reactEdge6 (V.more Reactivation.reactEdge7 (V.more Reactivation.reactEdge8 (V.more Reactivation.reactEdge9 (V.more Reactivation.reactEdge10 (V.more Reactivation.reactEdge11 (V.more Reactivation.reactEdge12 (V.more Reactivation.reactEdge13 (V.more Reactivation.reactEdge14 (V.more Reactivation.reactEdge15 (V.more Reactivation.reactEdge16 (V.more Reactivation.reactEdge17 (V.more Reactivation.reactEdge18 (V.more Reactivation.reactEdge19 (V.more Reactivation.reactEdge20 (V.more Reactivation.reactEdge21 (V.more Reactivation.reactEdge22 (V.more Reactivation.reactEdge23 (V.more Reactivation.reactEdge24 (V.more Reactivation.reactEdge25 (V.more Reactivation.reactEdge26 (V.more Reactivation.reactEdge27 (V.more Reactivation.reactEdge28 (V.stop)))))))))))))))))))))))))))))
      initialized-job-returned : V.Runs initial (completedPrefix ++ (V.waitJobResults (ident 2) ∷ [])) jobReturned
      initialized-job-returned = Facts.append-protocols initialized-job-before (V.more Reactivation.reactEdge29 V.stop)
    completionActions : List V.Event
    completionActions = V.waitJobResults (ident 2) ∷ ps (Sub.enqueueCompletion (ident 2) 0) ∷
      ps (Sub.deregisterJob (ident 2)) ∷ peerStep (PS.run (GP.publishAsyncResult (ident 2))) ∷ []
    abstract
      initialized-completion-lifecycle : V.Runs initial (completedPrefix ++ completionActions) jobAvailable
      initialized-completion-lifecycle = Facts.append-protocols initialized-job-before
        (V.more Reactivation.reactEdge29 (V.more Reactivation.reactEdge30
          (V.more Reactivation.reactEdge31 (V.more Reactivation.reactEdge32 V.stop))))
    agreement : Agreement.JobAgreement (ident 2) jobBefore jobReturned
    agreement = Agreement.initialized-job-agreement (ident 2) initializer initialized-job-before Reactivation.reactEdge29
    exact-body-return : C.governorPool (K.context (V.base jobReturned)) ≡ record (C.governorPool (K.context (V.base jobBefore)))
      { handles = put (ident 2) (GP.Pool.bodyReturned Reactivation.deactivationBody)
        (GP.Pool.handles (C.governorPool (K.context (V.base jobBefore)))) }
    exact-body-return = Agreement.job-success-return (ident 2) jobBefore jobReturned agreement returnedFrame refl refl
    body-return-keeps-queue : GP.Pool.completions (C.governorPool (K.context (V.base jobReturned))) ≡
      GP.Pool.completions (C.governorPool (K.context (V.base jobBefore)))
    body-return-keeps-queue = cong GP.Pool.completions exact-body-return
    body-return-keeps-registry : GP.Pool.registered (C.governorPool (K.context (V.base jobReturned))) ≡
      GP.Pool.registered (C.governorPool (K.context (V.base jobBefore)))
    body-return-keeps-registry = cong GP.Pool.registered exact-body-return
    unqueued-return : Sub.queued returnedFrame ≡ false
    unqueued-return = Agreement.job-wait-unqueued (ident 2) jobBefore jobReturned agreement returnedFrame refl
    publication : Agreement.CompletionPublication (ident 2) 0 returnedFrame G.succeeded jobReturned jobPublished
    publication = Agreement.publish-completion (ident 2) 0 jobReturned jobPublished returnedFrame G.succeeded refl unqueued-return refl Reactivation.reactEdge30
    source-completion : C.SubContext.completions (C.subsystem (K.context (V.base jobPublished))) ≡ Reactivation.deactivationCompletion ∷ []
    source-completion = Agreement.CompletionPublication.sourceQueue publication
    published-pool : C.governorPool (K.context (V.base jobPublished)) ≡ Reactivation.deactivationQueuedPool
    published-pool = Agreement.CompletionPublication.pool publication
    exact-published-body : Agreement.CompletionPublication.captured publication ≡ Reactivation.deactivationBody
    exact-published-body = Agreement.job-published-body (ident 2) 0 jobBefore jobReturned jobPublished agreement returnedFrame refl refl publication
    publication-awaits-deregistration : lookup (ident 2) (GP.Pool.handles (C.governorPool (K.context (V.base jobPublished)))) ≡
      just (GP.Pool.deregisterPending GP.Pool.normalExit)
    publication-awaits-deregistration = Agreement.publication-handle (ident 2) 0 returnedFrame G.succeeded jobReturned jobPublished publication
    still-not-protocol-body-return : lookup jid (Pool.handles (P.poolAt A.child₀ (V.physical (V.base jobReturned)))) ≡ just Pool.bodyRunning
    still-not-protocol-body-return = refl

    -- Each forbidden shortcut is checked at its actual shared frontend event.
    no-publication-before-return : V.advance (ps (Sub.enqueueCompletion (ident 2) 0)) jobBefore ≡ nothing
    no-publication-before-return = refl
    no-publication-from-failed-wait : V.advance (ps (Sub.enqueueCompletion (ident 2) 0)) ContinuationChecks.jobWaitAfter ≡ nothing
    no-publication-from-failed-wait = refl
    no-async-at-body-return : V.advance (peerStep (PS.run (GP.publishAsyncResult (ident 2)))) jobReturned ≡ nothing
    no-async-at-body-return = refl
    no-deregistration-before-publication : V.advance (ps (Sub.deregisterJob (ident 2))) jobReturned ≡ nothing
    no-deregistration-before-publication = refl
    no-async-at-publication : V.advance (peerStep (PS.run (GP.publishAsyncResult (ident 2)))) jobPublished ≡ nothing
    no-async-at-publication = refl
    no-double-publication : V.advance (ps (Sub.enqueueCompletion (ident 2) 0)) jobPublished ≡ nothing
    no-double-publication = refl
    actual-deregistration : V.advance (ps (Sub.deregisterJob (ident 2))) jobPublished ≡ just jobRemoved
    actual-deregistration = Reactivation.reactEdge31
    actual-async-publication : V.advance (peerStep (PS.run (GP.publishAsyncResult (ident 2)))) jobRemoved ≡ just jobAvailable
    actual-async-publication = Reactivation.reactEdge32

    monitor-effects : Agreement.MonitorWaitEffects ContinuationChecks.cleanWaitBefore ContinuationChecks.cleanWaitAfter
    monitor-effects = Agreement.monitor-wait-preserves (ident 0) _ _ ContinuationChecks.clean-monitor-agreement
    monitor-pool-unchanged : C.monitorPool (K.context (V.base ContinuationChecks.cleanWaitAfter)) ≡
      C.monitorPool (K.context (V.base ContinuationChecks.cleanWaitBefore))
    monitor-pool-unchanged = Agreement.MonitorWaitEffects.pool monitor-effects
    monitor-threads-unchanged : C.monitors (K.context (V.base ContinuationChecks.cleanWaitAfter)) ≡
      C.monitors (K.context (V.base ContinuationChecks.cleanWaitBefore))
    monitor-threads-unchanged = Agreement.MonitorWaitEffects.threads monitor-effects
    no-monitor-return-from-followup : V.advance (peerStep (PS.finishMonitor (ident 50))) ContinuationChecks.cleanWaitAfter ≡ nothing
    no-monitor-return-from-followup = refl
    no-monitor-async-from-followup : V.advance (peerStep (PS.publishMonitorResult (ident 50))) ContinuationChecks.cleanWaitAfter ≡ nothing
    no-monitor-async-from-followup = refl

    -- The initialized successful followup can be cleared while its physical
    -- monitor keeps running; this is a real separate shared bookkeeping step.
    followupClearedContext : C.Context
    followupClearedContext = record (Waiters.followupContext Waiters.cleanReturned Waiters.retiredClean)
      { subsystem = record (C.subsystem (Waiters.followupContext Waiters.cleanReturned Waiters.retiredClean)) { monitors = [] } }
    followupCleared : V.Runtime
    followupCleared = at afterCleanFailed followupClearedContext freeFront
    actual-followup-clear : V.advance (ps (Sub.monitorFinished (ident 0))) ContinuationChecks.cleanWaitAfter ≡ just followupCleared
    actual-followup-clear = refl
    initialized-followup-clear : Σ (List V.Event) (λ actions → V.Runs initial actions followupCleared)
    initialized-followup-clear = _ , Facts.append-protocols Waiters.initialized-local-continuation
      (V.more {a = ps (Sub.monitorFinished (ident 0))} actual-followup-clear V.stop)
    no-monitor-body-return-after-clear : V.advance (peerStep (PS.finishMonitor (ident 50))) followupCleared ≡ nothing
    no-monitor-body-return-after-clear = refl
    no-monitor-async-after-clear : V.advance (peerStep (PS.publishMonitorResult (ident 50))) followupCleared ≡ nothing
    no-monitor-async-after-clear = refl

  -- Initialized governor completion consumption/application and public-state lag.
  module GovernorCompletionChecks where
    open import Data.List using (take)
    open import Relation.Binary.PropositionalEquality using (cong)
    import ConnectionManagement.Properties.ServerPeersContinuations as Continuations
    private
      module Root = Continuations I.bearerClosed Prior.classify
      module GovCompletion = Root.Frontend capability
    machineOf : V.Runtime → Sub.Configuration
    machineOf s = Root.machine (V.base s)
    selectingRuntime selectedRuntime appliedRuntime publicBefore publicAfter : V.Runtime
    selectingRuntime = at registered Reactivation.warm8 freeFront
    selectedRuntime = at registered Reactivation.warm9 freeFront
    appliedRuntime = at registered Reactivation.warm10 freeFront
    publicBefore = at registered Reactivation.warm14 freeFront
    publicAfter = at registered Reactivation.warm15 freeFront
    governorActions : List V.Event
    governorActions = ps Sub.finishLaunch ∷ ps Sub.publishPublicState ∷ ps (Sub.sampleTime 16) ∷ ps Sub.registerWakeup ∷
      ps Sub.selectCompletion ∷ ps (Sub.applyAt 16) ∷ ps Sub.publishCounters ∷ ps Sub.traceSelection ∷ ps Sub.finishLaunch ∷
      ps (Sub.setTargets (G.targets 1 1 1)) ∷ ps Sub.publishPublicState ∷ []
    completedActions : List V.Event
    completedActions = CompletionChecks.completedPrefix ++ CompletionChecks.completionActions
    abstract
      initialized-selecting : V.Runs initial (completedActions ++ take 4 governorActions) selectingRuntime
      initialized-selecting = Facts.append-protocols CompletionChecks.initialized-completion-lifecycle
        (V.more Reactivation.reactEdge33 (V.more Reactivation.reactEdge34 (V.more Reactivation.reactEdge35 (V.more Reactivation.reactEdge36 V.stop))))
      initialized-public-after : V.Runs initial (completedActions ++ governorActions) publicAfter
      initialized-public-after = Facts.append-protocols CompletionChecks.initialized-completion-lifecycle
        (V.more Reactivation.reactEdge33 (V.more Reactivation.reactEdge34 (V.more Reactivation.reactEdge35 (V.more Reactivation.reactEdge36
          (V.more Reactivation.reactEdge37 (V.more Reactivation.reactEdge38 (V.more Reactivation.reactEdge39 (V.more Reactivation.reactEdge40
            (V.more Reactivation.reactEdge41 (V.more Reactivation.reactEdge42 (V.more Reactivation.reactEdge43 V.stop)))))))))))
    selection : Root.CompletionSelection (machineOf selectingRuntime) (machineOf selectedRuntime)
    selection = proj₁ (GovCompletion.selected-completion selectingRuntime selectedRuntime Reactivation.reactEdge37)
    selection-effects : GovCompletion.OwnerEffects Sub.selectCompletion selectingRuntime selectedRuntime
    selection-effects = proj₂ (GovCompletion.selected-completion selectingRuntime selectedRuntime Reactivation.reactEdge37)
    exact-selected-head : Root.CompletionSelection.result selection ≡ Reactivation.deactivationCompletion
    exact-selected-head = refl
    source-queue-consumed : Sub.completions (machineOf selectedRuntime) ≡ []
    source-queue-consumed = refl
    selection-retains-private : Sub.privateState (machineOf selectedRuntime) ≡ Sub.privateState (machineOf selectingRuntime)
    selection-retains-private = cong Sub.privateState (Root.CompletionSelection.state selection)
    selection-retains-public : Sub.publicState (machineOf selectedRuntime) ≡ Sub.publicState (machineOf selectingRuntime)
    selection-retains-public = cong Sub.publicState (Root.CompletionSelection.state selection)
    selection-retains-body-ledger : C.governorPool (K.context (V.base selectedRuntime)) ≡ C.governorPool (K.context (V.base selectingRuntime))
    selection-retains-body-ledger = GovCompletion.OwnerEffects.ledger selection-effects
    application : Root.CompletionApplication 16 Reactivation.deactivationCompletion (machineOf selectedRuntime) (machineOf appliedRuntime)
    application = proj₁ (GovCompletion.applied-completion 16 Reactivation.deactivationCompletion selectedRuntime appliedRuntime refl Reactivation.reactEdge38)
    exact-current-application : Sub.privateState (machineOf appliedRuntime) ≡ G.complete
      (Sub.maxRetries (machineOf selectedRuntime)) (Sub.clearFailDelay (machineOf selectedRuntime)) 16
      Reactivation.deactivationCompletion (Sub.privateState (machineOf selectedRuntime))
    exact-current-application = Root.application-current 16 Reactivation.deactivationCompletion _ _ application refl
    application-retains-public : Sub.publicState (machineOf appliedRuntime) ≡ Sub.publicState (machineOf selectedRuntime)
    application-retains-public = Root.application-public 16 Reactivation.deactivationCompletion _ _ application
    public-publication : Root.PublicStatePublication (machineOf publicBefore) (machineOf publicAfter)
    public-publication = proj₁ (GovCompletion.public-governor-state publicBefore publicAfter Reactivation.reactEdge43)
    public-now-updated : Sub.publicState (machineOf publicAfter) ≡ Sub.privateState (machineOf publicBefore)
    public-now-updated = cong Sub.publicState (Root.PublicStatePublication.state public-publication)
    private-active-cleared : G.activePeers (Sub.privateState (machineOf appliedRuntime)) ≡ []
    private-active-cleared = refl
    public-active-still-present : G.activePeers (Sub.publicState (machineOf appliedRuntime)) ≡ L.peerAddr ∷ []
    public-active-still-present = refl
    source-target-priority : Sub.advance Sub.selectTargets (machineOf selectingRuntime) ≡ nothing
    source-target-priority = proj₁ (Root.completion-priority (machineOf selectingRuntime) (machineOf selectedRuntime) selection)
    targets-cannot-overtake-completion : V.advance (ps Sub.selectTargets) selectingRuntime ≡ nothing
    targets-cannot-overtake-completion = refl
    policy-cannot-overtake-completion : V.advance (ps (Sub.selectPolicy (L.peerAddr ∷ []))) selectingRuntime ≡ nothing
    policy-cannot-overtake-completion = refl
    wakeup-cannot-overtake-completion : V.advance (ps Sub.selectWakeup) selectingRuntime ≡ nothing
    wakeup-cannot-overtake-completion = refl
    no-backwards-application-time : V.advance (ps (Sub.applyAt 15)) selectedRuntime ≡ nothing
    no-backwards-application-time = refl
    no-public-write-before-loop : V.advance (ps Sub.publishPublicState) appliedRuntime ≡ nothing
    no-public-write-before-loop = refl

    -- Conditional scheduling controls reuse the existing captured completion;
    -- they do not assert new initialized assertion-failure or timer histories.
    monitorPriorityContext : C.Context
    monitorPriorityContext = record Reactivation.warm8 { subsystem = record (C.subsystem Reactivation.warm8)
      { privateState = record (C.SubContext.privateState (C.subsystem Reactivation.warm8)) { demotingHot = [] } } }
    ready-monitor-blocks-completion : V.advance (ps Sub.selectCompletion) (at registered monitorPriorityContext freeFront) ≡ nothing
    ready-monitor-blocks-completion = refl
    timerContext timerSelectedContext : C.Context
    timerContext = record Reactivation.warm8 { subsystem = record (C.subsystem Reactivation.warm8) { wakeupAt = just 20 } }
    timerSelectedContext = record Reactivation.warm9 { subsystem = record (C.subsystem Reactivation.warm9)
      { wakeupAt = just 20; pc = Sub.cancelTimer (Sub.completion Reactivation.deactivationCompletion) } }
    timerBefore timerSelected : V.Runtime
    timerBefore = at registered timerContext freeFront
    timerSelected = at registered timerSelectedContext freeFront
    timer-select : V.advance (ps Sub.selectCompletion) timerBefore ≡ just timerSelected
    timer-select = refl
    timer-must-cancel-first : V.advance (ps (Sub.applyAt 16)) timerSelected ≡ nothing
    timer-must-cancel-first = refl
    timer-cancel : V.advance (ps Sub.cancelWakeup) timerSelected ≡ just selectedRuntime
    timer-cancel = refl
    certified-timer-cancel : machineOf selectedRuntime ≡ record (machineOf timerSelected)
      { pc = Sub.apply (Sub.completion Reactivation.deactivationCompletion); wakeupAt = nothing; wakeupReady = false }
    certified-timer-cancel = proj₁ (GovCompletion.cancelled-completion-timer Reactivation.deactivationCompletion timerSelected selectedRuntime refl timer-cancel)
    assertionContext assertionFailedContext : C.Context
    assertionContext = record Reactivation.warm9 { subsystem = record (C.subsystem Reactivation.warm9)
      { privateState = record (C.SubContext.privateState (C.subsystem Reactivation.warm9)) { establishedPeers = [] } } }
    assertionFailedContext = record assertionContext { subsystem = record (C.subsystem assertionContext)
      { pc = Sub.completionAssertionFailed Reactivation.deactivationCompletion } }
    assertionBefore assertionAfter : V.Runtime
    assertionBefore = at registered assertionContext freeFront
    assertionAfter = at registered assertionFailedContext freeFront
    assertion-step : V.advance (ps (Sub.applyAt 16)) assertionBefore ≡ just assertionAfter
    assertion-step = refl
    rejected-application : Root.CompletionApplication 16 Reactivation.deactivationCompletion (machineOf assertionBefore) (machineOf assertionAfter)
    rejected-application = proj₁ (GovCompletion.applied-completion 16 Reactivation.deactivationCompletion assertionBefore assertionAfter refl assertion-step)
    assertion-retains-private : Sub.privateState (machineOf assertionAfter) ≡ Sub.privateState (machineOf assertionBefore)
    assertion-retains-private = proj₂ (Root.application-rejection 16 Reactivation.deactivationCompletion _ _ rejected-application refl)
    assertion-failure-pc : Sub.pc (machineOf assertionAfter) ≡ Sub.completionAssertionFailed Reactivation.deactivationCompletion
    assertion-failure-pc = proj₁ (Root.application-rejection 16 Reactivation.deactivationCompletion _ _ rejected-application refl)
    assertion-cannot-publish-counters : V.advance (ps Sub.publishCounters) assertionAfter ≡ nothing
    assertion-cannot-publish-counters = refl
    assertion-cannot-publish-public : V.advance (ps Sub.publishPublicState) assertionAfter ≡ nothing
    assertion-cannot-publish-public = refl

  -- Provenance is derived from initialized executions, including the actual
  -- queue publication and the separate earlier primitive pool body return.
  module CompletionProvenanceChecks where
    open import Data.Empty using (⊥)
    open import Data.List using (drop)
    open import Data.List.Relation.Unary.Any using (here)
    open import Relation.Binary.PropositionalEquality using (sym; trans; subst)
    open import Function using (case_of_)
    import ConnectionManagement.Properties.ServerPeersCompletions as CompletionOrigin
    import ConnectionManagement.Properties.GovernorCompletions as QueueEvidence
    import ConnectionManagement.Properties.JobPoolReturnHistory as ReturnHistory
    private
      module QueueProvenance = CompletionOrigin.Frontend I.bearerClosed Prior.classify capability
      module Evidence = QueueEvidence Prior.classify
      module Returns = ReturnHistory GP.Body
      module GC = GovernorCompletionChecks
    publishedActions : List V.Event
    publishedActions = CompletionChecks.completedPrefix ++
      (V.waitJobResults (ident 2) ∷ ps (Sub.enqueueCompletion (ident 2) 0) ∷ [])
    abstract
      initialized-pending : V.Runs initial publishedActions CompletionChecks.jobPublished
      initialized-pending = Facts.append-protocols CompletionChecks.initialized-job-before
        (V.more Reactivation.reactEdge29 (V.more Reactivation.reactEdge30 V.stop))
    pending-history : QueueProvenance.Origin initial CompletionChecks.jobPublished Reactivation.deactivationCompletion
    pending-history = QueueProvenance.initialized-pending initializer initialized-pending (here refl)
    pending-return : Returns.Returned GP.Pool.initial
      (Evidence.Publication.job (QueueProvenance.Origin.published pending-history))
      (Evidence.Publication.payload (QueueProvenance.Origin.published pending-history))
      (Evidence.View.pool (QueueProvenance.runtime-view (QueueProvenance.Origin.before pending-history)))
    pending-return = QueueProvenance.origin-returned initializer pending-history
    pending-work-matches : GP.work (Evidence.Publication.payload (QueueProvenance.Origin.published pending-history)) ≡ Reactivation.deactivationWork
    pending-work-matches = proj₁ (proj₂ (QueueProvenance.origin-agreement pending-history))
    pending-outcome-matches : GP.outcome (Evidence.Publication.payload (QueueProvenance.Origin.published pending-history)) ≡ G.succeeded
    pending-outcome-matches = proj₂ (proj₂ (QueueProvenance.origin-agreement pending-history))
    pending-identity-matches : GP.identity (Evidence.Publication.payload (QueueProvenance.Origin.published pending-history)) ≡
      Evidence.Publication.job (QueueProvenance.Origin.published pending-history)
    pending-identity-matches = proj₁ (QueueProvenance.origin-agreement pending-history)
    consumed-history : QueueProvenance.Origin initial GC.selectingRuntime Reactivation.deactivationCompletion
    consumed-history = subst (QueueProvenance.Origin initial GC.selectingRuntime) GC.exact-selected-head
      (QueueProvenance.initialized-consumed initializer GC.initialized-selecting Reactivation.reactEdge37)
    consumed-return : Returns.Returned GP.Pool.initial
      (Evidence.Publication.job (QueueProvenance.Origin.published consumed-history))
      (Evidence.Publication.payload (QueueProvenance.Origin.published consumed-history))
      (Evidence.View.pool (QueueProvenance.runtime-view GC.selectingRuntime))
    consumed-return = QueueProvenance.origin-returned-current initializer consumed-history
    remainingActions : List V.Event
    remainingActions = drop 4 GC.governorActions
    remaining-path : V.Runs GC.selectingRuntime remainingActions GC.publicAfter
    remaining-path = V.more Reactivation.reactEdge37 (V.more Reactivation.reactEdge38 (V.more Reactivation.reactEdge39
      (V.more Reactivation.reactEdge40 (V.more Reactivation.reactEdge41 (V.more Reactivation.reactEdge42 (V.more Reactivation.reactEdge43 V.stop))))))
    retained-history : QueueProvenance.Origin initial GC.publicAfter Reactivation.deactivationCompletion
    retained-history = QueueProvenance.extend-through remaining-path consumed-history
    retained-handle : Returns.Present (Evidence.Publication.job (QueueProvenance.Origin.published retained-history))
      (Evidence.View.pool (QueueProvenance.runtime-view GC.publicAfter))
    retained-handle = Returns.returned-present (QueueProvenance.origin-returned-current initializer retained-history)
    no-wrong-outcome : GP.outcome (Evidence.Publication.payload (QueueProvenance.Origin.published pending-history)) ≡ G.failed → ⊥
    no-wrong-outcome wrong = case trans (sym pending-outcome-matches) wrong of λ ()

    -- An arbitrary queue can be consumed without a body guard at selection.
    -- Erasing the historical pool makes this snapshot unreachable from init.
    forgedContext forgedSelectedContext : C.Context
    forgedContext = record Reactivation.warm8 { governorPool = GP.Pool.initial }
    forgedSelectedContext = record Reactivation.warm9 { governorPool = GP.Pool.initial }
    forgedRuntime forgedSelected : V.Runtime
    forgedRuntime = at registered forgedContext freeFront
    forgedSelected = at registered forgedSelectedContext freeFront
    arbitrary-queue-readable : V.advance (ps Sub.selectCompletion) forgedRuntime ≡ just forgedSelected
    arbitrary-queue-readable = refl
    initialized-forged-queue-impossible : ∀ {actions} → V.Runs initial actions forgedRuntime → ⊥
    initialized-forged-queue-impossible path with Returns.returned-present
      (QueueProvenance.origin-returned-current initializer
        (QueueProvenance.initialized-pending initializer path (here refl)))
    ... | phase , ()

  -- A consumed success has the same historical deactivation body as its
  -- publication, and its success is derived from initialized frame control.
  module DeactivationOriginChecks where
    open import Data.Empty using (⊥)
    open import Data.List using (take)
    open import Relation.Binary.PropositionalEquality using (sym; trans; subst)
    import ConnectionManagement.Properties.ServerPeersContinuations as Continuations
    import ConnectionManagement.Properties.ServerPeersDeactivation as SuccessOrigins
    import ConnectionManagement.Properties.ServerPeersCompletions as CompletionOrigin
    import ConnectionManagement.Properties.GovernorCompletions as QueueEvidence
    private
      module Success = SuccessOrigins.Frontend I.bearerClosed Prior.classify capability
      module QueueProvenance = CompletionOrigin.Frontend I.bearerClosed Prior.classify capability
      module Evidence = QueueEvidence Prior.classify
      module CP = CompletionProvenanceChecks
      module GC = GovernorCompletionChecks
    consumed-success : Success.History initial GC.selectingRuntime
      (Evidence.Publication.job (QueueProvenance.Origin.published CP.consumed-history)) Reactivation.deactivationWork
    consumed-success = Success.origin-success initializer CP.consumed-history refl refl
    retained-success : Success.History initial GC.publicAfter
      (Evidence.Publication.job (QueueProvenance.Origin.published CP.consumed-history)) Reactivation.deactivationWork
    retained-success = Success.extend-through CP.remaining-path consumed-success
    returned-success : Success.History initial CompletionChecks.jobReturned (ident 2) Reactivation.deactivationWork
    returned-success = proj₂ (Success.initialized-valid initializer CompletionChecks.initialized-job-returned
      (ident 2) CompletionChecks.returnedFrame refl refl) refl

    private
      module Agreement = Continuations.Frontend I.bearerClosed Prior.classify capability
    cleanPlan : V.Plan
    cleanPlan = V.inherit (K.peerStep (PS.run (GP.run (Sub.jobStep (ident 2) J.observeHot)))) freeFront
    actual-clean-selector : V.choose (V.waitJobResults (ident 2)) CompletionChecks.jobBefore ≡ just cleanPlan
    actual-clean-selector = refl
    clean-cause : Success.Cause (ident 2) Reactivation.deactivationWork CompletionChecks.jobBefore CompletionChecks.jobReturned
      (V.waitJobResults (ident 2)) cleanPlan
    clean-cause = Success.cleanWait (Reactivation.deactivationFrame J.awaitHot false false) CompletionChecks.returnedFrame
      refl refl refl CompletionChecks.agreement
      (Agreement.job-success-captures (ident 2) CompletionChecks.jobBefore CompletionChecks.jobReturned
        CompletionChecks.agreement CompletionChecks.returnedFrame refl refl) refl refl refl

    -- A monitor can finish deactivation between job registration and J.enter.
    -- That initialized race takes the source's legitimate PeerWarm shortcut.
    module WarmRace where
      beforeEntry : V.Runtime
      beforeEntry = at registered Reactivation.down94 freeFront
      prefix : List V.Event
      prefix = (prefixActions ++ Reactivation.firstCompletedActions) ++ take 27 Reactivation.reactivationActions
      abstract
        initialized-before : V.Runs initial prefix beforeEntry
        initialized-before = Facts.append-protocols Reactivation.initialized-first-completed
          (V.more Reactivation.reactEdge1 (V.more Reactivation.reactEdge2 (V.more Reactivation.reactEdge3 (V.more Reactivation.reactEdge4 (V.more Reactivation.reactEdge5 (V.more Reactivation.reactEdge6 (V.more Reactivation.reactEdge7 (V.more Reactivation.reactEdge8 (V.more Reactivation.reactEdge9 (V.more Reactivation.reactEdge10 (V.more Reactivation.reactEdge11 (V.more Reactivation.reactEdge12 (V.more Reactivation.reactEdge13 (V.more Reactivation.reactEdge14 (V.more Reactivation.reactEdge15 (V.more Reactivation.reactEdge16 (V.more Reactivation.reactEdge17 (V.more Reactivation.reactEdge18 (V.more Reactivation.reactEdge19 (V.more Reactivation.reactEdge20 (V.more Reactivation.reactEdge21 (V.more Reactivation.reactEdge22 (V.more Reactivation.reactEdge23 (V.more Reactivation.reactEdge24 (V.more Reactivation.reactEdge25 (V.more Reactivation.reactEdge26 (V.more Reactivation.reactEdge27 (V.stop))))))))))))))))))))))))))))
      followup : J.Frame
      followup = J.frame Reactivation.deactivationWork (ident 50) (ident 50) (ident 0) (ident 0) J.begin
      contextAt : J.Frame → Peer.Peer → C.Context
      contextAt f peer = record (withPeer peer Reactivation.down94)
        { subsystem = record (C.subsystem (withPeer peer Reactivation.down94))
          { monitors = put (ident 0) f (C.SubContext.monitors (C.subsystem Reactivation.down94)) } }
      warmPolled warmWaiting warmWarmed : C.Context
      warmPolled = contextAt followup cleanPromoted
      warmWaiting = contextAt (record followup { pc = J.awaitHot }) Reactivation.terminatingPeer
      warmWarmed = contextAt (record followup { pc = J.complete G.succeeded }) Reactivation.retiredPeer
      warmReturned warmPublished : C.Context
      warmReturned = record warmWarmed { subsystem = record (C.subsystem warmWarmed)
        { jobs = put (ident 2) CompletionChecks.returnedFrame (C.SubContext.jobs (C.subsystem warmWarmed)) }
        ; governorPool = Reactivation.deactivationReturnedPool }
      warmPublished = record warmReturned { subsystem = record (C.subsystem warmReturned)
        { jobs = put (ident 2) (Reactivation.deactivationFrame (J.complete G.succeeded) true false) (C.SubContext.jobs (C.subsystem warmReturned))
        ; completions = Reactivation.deactivationCompletion ∷ [] }
        ; governorPool = Reactivation.deactivationQueuedPool }
      poll : V.advance (V.pollResults (ident 0) (ident 50)) beforeEntry ≡ just (at registered warmPolled freeFront)
      poll = refl
      enterMonitor : V.advance (ps (Sub.monitorStep (ident 0) J.enter)) (at registered warmPolled freeFront) ≡ just (at registered warmWaiting freeFront)
      enterMonitor = refl
      finishMonitor : V.advance (V.waitMonitorResults (ident 0)) (at registered warmWaiting freeFront) ≡ just (at registered warmWarmed freeFront)
      finishMonitor = refl
      enterWarm : V.advance (ps (Sub.jobStep (ident 2) J.enter)) (at registered warmWarmed freeFront) ≡ just (at registered warmReturned freeFront)
      enterWarm = refl
      earlyPlan : V.Plan
      earlyPlan = V.inherit (K.peerStep (PS.run (GP.run (Sub.jobStep (ident 2) J.enter)))) freeFront
      earlyWorld : J.World
      earlyWorld = Sub.world (PS.machine (K.peers (V.base (at registered warmWarmed freeFront))))
      actual-early-selector : V.choose (ps (Sub.jobStep (ident 2) J.enter)) (at registered warmWarmed freeFront) ≡ just earlyPlan
      actual-early-selector = refl
      early-cause : Success.Cause (ident 2) Reactivation.deactivationWork (at registered warmWarmed freeFront) (at registered warmReturned freeFront)
        (ps (Sub.jobStep (ident 2) J.enter)) earlyPlan
      early-cause = Success.alreadyWarm (Reactivation.deactivationFrame J.begin false false)
        (Sub.execution CompletionChecks.returnedFrame) earlyWorld earlyWorld Reactivation.retiredPeer
        refl refl refl refl refl refl refl refl refl refl
      publish : V.advance (ps (Sub.enqueueCompletion (ident 2) 0)) (at registered warmReturned freeFront) ≡ just (at registered warmPublished freeFront)
      publish = refl
      actions : List V.Event
      actions = V.pollResults (ident 0) (ident 50) ∷ ps (Sub.monitorStep (ident 0) J.enter) ∷
        V.waitMonitorResults (ident 0) ∷ ps (Sub.jobStep (ident 2) J.enter) ∷ ps (Sub.enqueueCompletion (ident 2) 0) ∷ []
      abstract
        initialized-publication : V.Runs initial (prefix ++ actions) (at registered warmPublished freeFront)
        initialized-publication = Facts.append-protocols initialized-before
          (V.more poll (V.more enterMonitor (V.more finishMonitor (V.more enterWarm (V.more publish V.stop)))))
      open import Data.List.Relation.Unary.Any using (here)
      publication-history = QueueProvenance.initialized-pending initializer initialized-publication (here refl)
      success : Success.History initial (at registered warmPublished freeFront)
        (Evidence.Publication.job (QueueProvenance.Origin.published publication-history)) Reactivation.deactivationWork
      success = Success.origin-success initializer publication-history refl refl
      -- The target governor job did not wait; the monitor did. Separate IDs
      -- and the before-entry PC exclude attributing its read to this body.
      actual-warm-peer : Peer.status Reactivation.retiredPeer ≡ Peer.peerWarm
      actual-warm-peer = refl
      job-still-at-begin : J.pc (Sub.execution (Reactivation.deactivationFrame J.begin false false)) ≡ J.begin
      job-still-at-begin = refl
      no-target-wait : V.advance (V.waitJobResults (ident 2)) (at registered warmWarmed freeFront) ≡ nothing
      no-target-wait = refl

    -- An arbitrary deactivation row at an activation PC can manufacture a
    -- success-shaped body. Initialization excludes precisely that control mix.
    module ForgedControl where
      import ConnectionManagement.Properties.PeerJobControl as Control
      forgedFrame : Sub.JobFrame
      forgedFrame = Reactivation.deactivationFrame J.finishActivation false false
      forged : V.Runtime
      forged = at registered (record Reactivation.down94
        { subsystem = record (C.subsystem Reactivation.down94)
          { jobs = put (ident 2) forgedFrame (C.SubContext.jobs (C.subsystem Reactivation.down94)) } }) freeFront
      fabricatedReturn : V.Runtime
      fabricatedReturn = at registered (record Reactivation.down94
        { subsystem = record (C.subsystem Reactivation.down94)
          { jobs = put (ident 2) CompletionChecks.returnedFrame (C.SubContext.jobs (C.subsystem Reactivation.down94))
          ; peers = (ident 0 , record cleanPromoted { promotedAt = just 19 }) ∷ [] }
        ; governorPool = Reactivation.deactivationReturnedPool }) freeFront
      arbitrary-control-return : V.advance (ps (Sub.jobStep (ident 2) (J.finishHotAt 19))) forged ≡ just fabricatedReturn
      arbitrary-control-return = refl
      no-control : Control.DeactivatePC J.finishActivation → ⊥
      no-control ()
      unreachable : ∀ {actions} → V.Runs initial actions forged → ⊥
      unreachable path = no-control (proj₁ (Success.initialized-valid initializer path (ident 2) forgedFrame refl refl))


  -- Initialized close routes retain physical reads, the real shared CM release,
  -- Cold observation and completion provenance without conflating Async phases.
  module CloseOriginChecks where
    open import Data.Empty using (⊥)
    open import Data.List.Membership.Propositional using (_∈_)
    open import Data.List using (take; drop)
    open import Data.List.Relation.Unary.Any using (here)
    open import Relation.Binary.PropositionalEquality using (subst; sym; trans; cong)
    open import Data.Maybe.Properties using (just-injective)
    open import Data.Product using (Σ; _×_)
    open import Function using (case_of_)
    import ConnectionManagement.Rules.OutboundRelease as OutRelease
    import ConnectionManagement.Properties.ServerPeersDeactivation as DeactivationWitness
    import ConnectionManagement.Properties.ServerPeersClose as CloseOrigins
    import ConnectionManagement.Properties.ServerPeersCompletions as CompletionOrigin
    import ConnectionManagement.Properties.ServerPeersContinuations as Continuations
    import ConnectionManagement.Properties.GovernorCompletions as QueueEvidence
    private
      module Success = CloseOrigins.Frontend I.bearerClosed Prior.classify capability
      module QueueProvenance = CompletionOrigin.Frontend I.bearerClosed Prior.classify capability
      module Agreement = Continuations.Frontend I.bearerClosed Prior.classify capability
      module Root = Continuations I.bearerClosed Prior.classify
      module Evidence = QueueEvidence Prior.classify
      module GC = GovernorCompletionChecks
      module PhysicalReads = DeactivationWitness.Frontend I.bearerClosed Prior.classify capability

    import ConnectionManagement.Properties.ServerPeersMonitorReturns as MonitorReturns
    import ConnectionManagement.Properties.ServerPeersMonitorBacking as MonitorBacking
    import ConnectionManagement.Properties.ServerPeersMonitorStages as MonitorStages
    private
      module Monitor = MonitorReturns I.bearerClosed Prior.classify
      module Monitors = Monitor.Frontend capability
      module Backing = MonitorBacking.Frontend I.bearerClosed Prior.classify capability
      module Stages = MonitorStages.Frontend I.bearerClosed Prior.classify capability

    import ConnectionManagement.Store as Stores
    -- Transparent fixture data and events; no runtime rule is changed.
    initialCM : O.Configuration
    initialCM = O.initial (Machine.initial Shared.responderMode F.empty)
    sub : V.Runtime → C.SubContext
    sub state = C.subsystem (K.context (V.base state))
    withSub : (C.SubContext → C.SubContext) → V.Runtime → V.Runtime
    withSub update state = record state { base = record (V.base state)
      { context = record (K.context (V.base state)) { subsystem = update (sub state) } } }
    withGP : (GP.Pool.State → GP.Pool.State) → V.Runtime → V.Runtime
    withGP update state = record state { base = record (V.base state)
      { context = record (K.context (V.base state)) { governorPool = update (C.governorPool (K.context (V.base state))) } } }
    withCM : O.Configuration → V.Runtime → V.Runtime
    withCM source state = record state { base = record (V.base state) { server = K.setSource source (K.server (V.base state)) } }
    background : PS.MonitorPC → Maybe Cancel.Frame → PS.Thread
    background pc interrupted = PS.thread (ident 0) (ident 50) (ident 0) PS.returned pc interrupted nothing
    withBackground : PS.MonitorPC → Maybe Cancel.Frame → V.Runtime → V.Runtime
    withBackground pc interrupted state = record state { base = record (V.base state)
      { context = record (K.context (V.base state))
        { monitors = put (ident 50) (background pc interrupted) (C.monitors (K.context (V.base state))) } } }
    oldDup : Shared.ConnectionState
    oldDup = Shared.outboundDup A.key₀ A.child₀ (ident 0) ticking
    beginCM : WorkerId → V.Runtime → V.Runtime
    beginCM actor state = withCM (record (V.sourceOf state)
      { releasing = put actor (OutRelease.frame A.key₀ OutRelease.transaction false) (O.releasing (V.sourceOf state))
      ; released = Stores.delete actor (O.released (V.sourceOf state)) }) state
    transactCM : WorkerId → V.Runtime → V.Runtime
    transactCM actor state = withCM (record source
      { core = record (O.core source) { world = record world
          { cm = record (Shared.cm world) { entries = put (ident 0) (Shared.inboundIdle A.key₀ A.child₀ (ident 0) duplex) (Shared.entries (Shared.cm world)) } } }
      ; releasing = put actor (OutRelease.frame A.key₀ (OutRelease.count (OutRelease.complete (OutRelease.success (just oldDup)))) false) (O.releasing source) }) state
      where
      source = V.sourceOf state
      world = Machine.world (O.core source)
    countCM : WorkerId → V.Runtime → V.Runtime
    countCM actor state = withCM (record (V.sourceOf state)
      { releasing = put actor (OutRelease.frame A.key₀ (OutRelease.complete (OutRelease.success (just oldDup))) false) (O.releasing (V.sourceOf state)) }) state
    returnCM : WorkerId → V.Runtime → V.Runtime
    returnCM actor state = withCM (record (V.sourceOf state)
      { releasing = Stores.delete actor (O.releasing (V.sourceOf state))
      ; released = put actor (OutRelease.success (just oldDup)) (O.released (V.sourceOf state)) }) state
    stopMux : V.Runtime → V.Runtime
    stopMux state = withCM (record source { core = record (O.core source)
      { inboundGovernor = IG.setMux (ident 0) (record (Y.withWanton jid Mux.initiatorJob Y.m1) { commands = Mux.commands Y.m1 ++ (Mux.shutdown ∷ []) })
        (Machine.inboundGovernor (O.core source)) } }) state
      where source = V.sourceOf state
    closeWork : G.Job
    closeWork = G.job G.close L.peerAddr (just (ident 0))
    closeCompletion : G.Completion
    closeCompletion = G.completion closeWork G.succeeded 0
    closeFrame : J.PC → Bool → Sub.JobFrame
    closeFrame pc queued = Sub.jobFrame (J.frame closeWork (ident 18) (ident 19) (ident 18) (ident 0) pc) queued false
    closeBody : G.Outcome → GP.Body
    closeBody outcome = GP.body (ident 3) closeWork outcome
    closePeer : Peer.Peer
    closePeer = record (Peer.cool Reactivation.retiredPeer)
      { hotControl = Peer.terminate; warmControl = Peer.terminate; establishedControl = Peer.terminate }
    frameAt : J.PC → V.Runtime → V.Runtime
    frameAt pc = withSub (λ c → record c { jobs = put (ident 3) (closeFrame pc false) (C.SubContext.jobs c) })
    returnBody : G.Outcome → V.Runtime → V.Runtime
    returnBody outcome state = withGP (λ pool → record pool
      { handles = put (ident 3) (GP.Pool.bodyReturned (closeBody outcome)) (GP.Pool.handles pool) })
      (frameAt (J.complete outcome) state)
    publishBody : V.Runtime → V.Runtime
    publishBody state = withGP (λ pool → record pool
      { handles = put (ident 3) (GP.Pool.deregisterPending GP.Pool.normalExit) (GP.Pool.handles pool)
      ; completions = GP.Pool.completions pool ++ (closeBody G.succeeded ∷ []) })
      (withSub (λ c → record c { jobs = put (ident 3) (closeFrame (J.complete G.succeeded) true) (C.SubContext.jobs c)
        ; completions = C.SubContext.completions c ++ (closeCompletion ∷ []) }) state)
    observeColdPeer : V.Runtime → V.Runtime
    observeColdPeer state = withBackground PS.normalFinishing nothing
      (withSub (λ c → record c { peers = (ident 0 , record closePeer { status = Peer.peerCold }) ∷ [] }) state)
    withMonitorPool : (PS.Pool.State → PS.Pool.State) → V.Runtime → V.Runtime
    withMonitorPool update state = record state { base = record (V.base state)
      { context = record (K.context (V.base state)) { monitorPool = update (C.monitorPool (K.context (V.base state))) } } }
    finishPhysical : Maybe Cancel.Frame → V.Runtime → V.Runtime
    finishPhysical interrupted state = withMonitorPool (λ pool → record pool
      { handles = put (ident 50) (PS.Pool.deregisterPending PS.Pool.normalExit) (PS.Pool.handles pool) })
      (withBackground PS.exited interrupted (withSub (λ c → record c
        { peers = (ident 0 , record closePeer { status = Peer.peerCold; monitorStarted = false; promotedAt = nothing }) ∷ [] }) state))
    removePhysical : V.Runtime → V.Runtime
    removePhysical = withMonitorPool (λ pool → record pool
      { handles = put (ident 50) (PS.Pool.deregistered PS.Pool.normalExit) (PS.Pool.handles pool)
      ; registered = PS.Pool.remove (ident 50) (PS.Pool.registered pool) })
    publishPhysical : V.Runtime → V.Runtime
    publishPhysical = withMonitorPool (λ pool → record pool
      { handles = put (ident 50) (PS.Pool.resultAvailable PS.Pool.normalExit) (PS.Pool.handles pool) })
    removeMonitor publishMonitor : V.Event
    removeMonitor = peerStep (PS.deregisterMonitor (ident 50))
    publishMonitor = peerStep (PS.publishMonitorResult (ident 50))
    normalMonitorActions errorMonitorActions : List V.Event
    normalMonitorActions = Monitors.event Monitor.normal (ident 50) ∷ removeMonitor ∷ publishMonitor ∷ []
    errorMonitorActions = Monitors.event Monitor.exceptional (ident 50) ∷ removeMonitor ∷ publishMonitor ∷ []
    all-before-release : J.pc (Sub.execution (closeFrame J.awaitAll false)) ≡ J.awaitAll
    all-before-release = refl
    closeEvent1 : V.Event
    closeEvent1 = ps (Sub.setTargets (G.targets 1 0 0))
    closeEvent2 : V.Event
    closeEvent2 = ps (Sub.sampleTime 17)
    closeEvent3 : V.Event
    closeEvent3 = ps Sub.registerWakeup
    closeEvent4 : V.Event
    closeEvent4 = ps Sub.selectTargets
    closeEvent5 : V.Event
    closeEvent5 = ps (Sub.applyAt 17)
    closeEvent6 : V.Event
    closeEvent6 = ps Sub.publishCounters
    closeEvent7 : V.Event
    closeEvent7 = ps Sub.traceSelection
    closeEvent8 : V.Event
    closeEvent8 = ps Sub.finishLaunch
    closeEvent9 : V.Event
    closeEvent9 = ps Sub.publishPublicState
    closeEvent10 : V.Event
    closeEvent10 = ps (Sub.sampleTime 18)
    closeEvent11 : V.Event
    closeEvent11 = ps Sub.registerWakeup
    closeEvent12 : V.Event
    closeEvent12 = ps (Sub.selectPolicy (L.peerAddr ∷ []))
    closeEvent13 : V.Event
    closeEvent13 = ps (Sub.applyAt 18)
    closeEvent14 : V.Event
    closeEvent14 = ps Sub.publishCounters
    closeEvent15 : V.Event
    closeEvent15 = ps Sub.traceSelection
    closeEvent16 : V.Event
    closeEvent16 = ps (Sub.forkJob (ident 18) (ident 19) (ident 18))
    closeEvent17 : V.Event
    closeEvent17 = ps Sub.registerJob
    closeEvent18 : V.Event
    closeEvent18 = ps (Sub.jobStep (ident 3) J.enter)
    closeEvent19 : V.Event
    closeEvent19 = V.waitJobResults (ident 3)
    closeEvent20 : V.Event
    closeEvent20 = ps (Sub.jobStep (ident 3) J.requestRelease)
    closeEvent21 : V.Event
    closeEvent21 = V.dispatch (K.coreStep (O.release (ident 18) OutRelease.transactionStep))
    closeEvent22 : V.Event
    closeEvent22 = V.dispatch (K.coreStep (O.release (ident 18) OutRelease.readCounters))
    closeEvent23 : V.Event
    closeEvent23 = V.dispatch (K.coreStep (O.release (ident 18) OutRelease.returnResult))
    closeEvent24 : V.Event
    closeEvent24 = ps (Sub.jobStep (ident 3) J.collectRelease)
    closeEvent25 : V.Event
    closeEvent25 = V.pollResults (ident 0) (ident 50)
    closeEvent26 : V.Event
    closeEvent26 = ps (Sub.jobStep (ident 3) J.observeCold)
    closeEvent27 : V.Event
    closeEvent27 = ps (Sub.enqueueCompletion (ident 3) 0)
    closeEvent28 : V.Event
    closeEvent28 = ps Sub.finishLaunch
    closeEvent29 : V.Event
    closeEvent29 = ps Sub.publishPublicState
    closeEvent30 : V.Event
    closeEvent30 = ps (Sub.sampleTime 19)
    closeEvent31 : V.Event
    closeEvent31 = ps Sub.registerWakeup
    closeEvent32 : V.Event
    closeEvent32 = ps Sub.selectCompletion
    closeEvent33 : V.Event
    closeEvent33 = ps (Sub.applyAt 19)
    closeEvent34 : V.Event
    closeEvent34 = ps Sub.publishCounters
    closeEvent35 : V.Event
    closeEvent35 = ps Sub.traceSelection
    closeEvent36 : V.Event
    closeEvent36 = ps Sub.finishLaunch
    closeEvent37 : V.Event
    closeEvent37 = ps Sub.publishPublicState
    timeoutEvent1 : V.Event
    timeoutEvent1 = ps (Sub.jobStep (ident 3) J.operationTimeout)
    timeoutEvent2 : V.Event
    timeoutEvent2 = V.dispatch (K.coreStep (O.beginRelease (ident 80) A.key₀))
    timeoutEvent3 : V.Event
    timeoutEvent3 = V.dispatch (K.coreStep (O.release (ident 80) OutRelease.transactionStep))
    timeoutEvent4 : V.Event
    timeoutEvent4 = V.dispatch (K.coreStep (O.release (ident 80) OutRelease.readCounters))
    timeoutEvent5 : V.Event
    timeoutEvent5 = V.dispatch (K.coreStep (O.release (ident 80) OutRelease.returnResult))
    timeoutEvent6 : V.Event
    timeoutEvent6 = V.pollResults (ident 0) (ident 50)
    timeoutEvent7 : V.Event
    timeoutEvent7 = ps (Sub.jobStep (ident 3) J.observeCold)
    timeoutEvent8 : V.Event
    timeoutEvent8 = ps (Sub.enqueueCompletion (ident 3) 0)
    coldEntryEvent1 : V.Event
    coldEntryEvent1 = peerStep (PS.monitorException (ident 50) err)
    coldEntryEvent2 : V.Event
    coldEntryEvent2 = V.dispatch (K.coreStep (O.beginRelease (ident 80) A.key₀))
    coldEntryEvent3 : V.Event
    coldEntryEvent3 = V.dispatch (K.coreStep (O.release (ident 80) OutRelease.transactionStep))
    coldEntryEvent4 : V.Event
    coldEntryEvent4 = V.dispatch (K.coreStep (O.release (ident 80) OutRelease.readCounters))
    coldEntryEvent5 : V.Event
    coldEntryEvent5 = V.dispatch (K.coreStep (O.release (ident 80) OutRelease.returnResult))
    coldEntryEvent6 : V.Event
    coldEntryEvent6 = peerStep (PS.commitMonitorError (ident 50))
    coldEntryEvent7 : V.Event
    coldEntryEvent7 = ps (Sub.jobStep (ident 3) J.enter)
    coldEntryEvent8 : V.Event
    coldEntryEvent8 = ps (Sub.jobStep (ident 3) J.observeCold)
    coldEntryEvent9 : V.Event
    coldEntryEvent9 = ps (Sub.enqueueCompletion (ident 3) 0)
    closeRouteActions : List V.Event
    closeRouteActions = closeEvent1 ∷ closeEvent2 ∷ closeEvent3 ∷ closeEvent4 ∷ closeEvent5 ∷ closeEvent6 ∷ closeEvent7 ∷ closeEvent8 ∷ closeEvent9 ∷ closeEvent10 ∷ closeEvent11 ∷ closeEvent12 ∷ closeEvent13 ∷ closeEvent14 ∷ closeEvent15 ∷ closeEvent16 ∷ closeEvent17 ∷ closeEvent18 ∷ closeEvent19 ∷ closeEvent20 ∷ closeEvent21 ∷ closeEvent22 ∷ closeEvent23 ∷ closeEvent24 ∷ closeEvent25 ∷ closeEvent26 ∷ closeEvent27 ∷ closeEvent28 ∷ closeEvent29 ∷ closeEvent30 ∷ closeEvent31 ∷ closeEvent32 ∷ closeEvent33 ∷ closeEvent34 ∷ closeEvent35 ∷ closeEvent36 ∷ closeEvent37 ∷ []
    successPrefix17 : List V.Event
    successPrefix17 = (GC.completedActions ++ GC.governorActions) ++ (closeEvent1 ∷ closeEvent2 ∷ closeEvent3 ∷ closeEvent4 ∷ closeEvent5 ∷ closeEvent6 ∷ closeEvent7 ∷ closeEvent8 ∷ closeEvent9 ∷ closeEvent10 ∷ closeEvent11 ∷ closeEvent12 ∷ closeEvent13 ∷ closeEvent14 ∷ closeEvent15 ∷ closeEvent16 ∷ closeEvent17 ∷ [])
    successPrefix18 : List V.Event
    successPrefix18 = successPrefix17 ++ (closeEvent18 ∷ [])
    successPrefix19 : List V.Event
    successPrefix19 = successPrefix18 ++ (closeEvent19 ∷ [])
    successPrefix20 : List V.Event
    successPrefix20 = successPrefix19 ++ (closeEvent20 ∷ [])
    successPrefix24 : List V.Event
    successPrefix24 = successPrefix20 ++ (closeEvent21 ∷ closeEvent22 ∷ closeEvent23 ∷ closeEvent24 ∷ [])
    successPrefix26 : List V.Event
    successPrefix26 = successPrefix24 ++ (closeEvent25 ∷ closeEvent26 ∷ [])
    successPrefix27 : List V.Event
    successPrefix27 = successPrefix26 ++ (closeEvent27 ∷ [])
    successPrefix31 : List V.Event
    successPrefix31 = successPrefix27 ++ (closeEvent28 ∷ closeEvent29 ∷ closeEvent30 ∷ closeEvent31 ∷ [])
    successPrefix37 : List V.Event
    successPrefix37 = successPrefix31 ++ (closeEvent32 ∷ closeEvent33 ∷ closeEvent34 ∷ closeEvent35 ∷ closeEvent36 ∷ closeEvent37 ∷ [])
    timeoutActions : List V.Event
    timeoutActions = timeoutEvent1 ∷ timeoutEvent2 ∷ timeoutEvent3 ∷ timeoutEvent4 ∷ timeoutEvent5 ∷ timeoutEvent6 ∷ timeoutEvent7 ∷ timeoutEvent8 ∷ []
    coldEntryActions : List V.Event
    coldEntryActions = coldEntryEvent1 ∷ coldEntryEvent2 ∷ coldEntryEvent3 ∷ coldEntryEvent4 ∷ coldEntryEvent5 ∷ coldEntryEvent6 ∷ coldEntryEvent7 ∷ coldEntryEvent8 ∷ coldEntryEvent9 ∷ []
    normalPrefix1 normalPrefix2 normalPrefix3 errorPrefix1 errorPrefix2 errorPrefix3 : List V.Event
    normalPrefix1 = successPrefix37 ++ (Monitors.event Monitor.normal (ident 50) ∷ [])
    normalPrefix2 = normalPrefix1 ++ (removeMonitor ∷ [])
    normalPrefix3 = normalPrefix2 ++ (publishMonitor ∷ [])
    errorPrefix1 = (successPrefix17 ++ coldEntryActions) ++ (Monitors.event Monitor.exceptional (ident 50) ∷ [])
    errorPrefix2 = errorPrefix1 ++ (removeMonitor ∷ [])
    errorPrefix3 = errorPrefix2 ++ (publishMonitor ∷ [])
    -- An unchanged event schedule has a unique endpoint; use this to reject
    -- executable forged handle snapshots at the already initialized prefix.
    same-run : ∀ {start actions t u} → V.Runs start actions t → V.Runs start actions u → t ≡ u
    same-run V.stop V.stop = refl
    same-run (V.more left rest) (V.more right rest′) with just-injective (trans (sym left) right)
    ... | refl = same-run rest rest′

    gapBeforeRemoval gapBeforePublication gapAfterPublication : V.Event
    gapBeforeRemoval = ps (Sub.setTargets (G.targets 0 0 0))
    gapBeforePublication = ps (Sub.setTargets (G.targets 1 0 0))
    gapAfterPublication = ps (Sub.setTargets (G.targets 1 1 0))
    gappedActions : List V.Event
    gappedActions = gapBeforeRemoval ∷ removeMonitor ∷ gapBeforePublication ∷ publishMonitor ∷ gapAfterPublication ∷ []

    -- These siblings preserve the checked snapshot/edge interface while
    -- preventing generic proof elaboration from unfolding runtime representations.
    module Snapshots where
      abstract
        success0 : V.Runtime
        success0 = GC.publicAfter
        success1 : V.Runtime
        success1 = withSub (λ c → record c { targetInput = G.targets 1 0 0 }) success0
        closeEdge1 : V.advance closeEvent1 success0 ≡ just success1
        closeEdge1 = refl
        success2 : V.Runtime
        success2 = withSub (λ c → record c { now = 17; privateState = G.advanceTime 17 (C.SubContext.privateState c); pc = Sub.prepareWait }) success1
        closeEdge2 : V.advance closeEvent2 success1 ≡ just success2
        closeEdge2 = refl
        success3 : V.Runtime
        success3 = withSub (λ c → record c { pc = Sub.selecting; wakeupAt = nothing; wakeupReady = false }) success2
        closeEdge3 : V.advance closeEvent3 success2 ≡ just success3
        closeEdge3 = refl
        success4 : V.Runtime
        success4 = withSub (λ c → record c { pc = Sub.apply (Sub.targets (G.targets 1 0 0)) }) success3
        closeEdge4 : V.advance closeEvent4 success3 ≡ just success4
        closeEdge4 = refl
        success5 : V.Runtime
        success5 = withSub (λ c → record c { now = 17; privateState = record (C.SubContext.privateState c) { target = G.targets 1 0 0 }; pc = Sub.publishView [] }) success4
        closeEdge5 : V.advance closeEvent5 success4 ≡ just success5
        closeEdge5 = refl
        success6 : V.Runtime
        success6 = withSub (λ c → record c { pc = Sub.traceDecision [] }) success5
        closeEdge6 : V.advance closeEvent6 success5 ≡ just success6
        closeEdge6 = refl
        success7 : V.Runtime
        success7 = withSub (λ c → record c { pc = Sub.launch [] }) success6
        closeEdge7 : V.advance closeEvent7 success6 ≡ just success7
        closeEdge7 = refl
        success8 : V.Runtime
        success8 = withSub (λ c → record c { pc = Sub.publishPublic }) success7
        closeEdge8 : V.advance closeEvent8 success7 ≡ just success8
        closeEdge8 = refl
        success9 : V.Runtime
        success9 = withSub (λ c → record c { publicState = C.SubContext.privateState c; pc = Sub.sampleInputs }) success8
        closeEdge9 : V.advance closeEvent9 success8 ≡ just success9
        closeEdge9 = refl
        success10 : V.Runtime
        success10 = withSub (λ c → record c { now = 18; privateState = G.advanceTime 18 (C.SubContext.privateState c); pc = Sub.prepareWait }) success9
        closeEdge10 : V.advance closeEvent10 success9 ≡ just success10
        closeEdge10 = refl
        success11 : V.Runtime
        success11 = withSub (λ c → record c { pc = Sub.selecting; wakeupAt = nothing; wakeupReady = false }) success10
        closeEdge11 : V.advance closeEvent11 success10 ≡ just success11
        closeEdge11 = refl
        success12 : V.Runtime
        success12 = withSub (λ c → record c { pc = Sub.apply (Sub.policy (G.decision (G.mark G.close (L.peerAddr ∷ []) (C.SubContext.privateState c)) (closeWork ∷ []))) }) success11
        closeEdge12 : V.advance closeEvent12 success11 ≡ just success12
        closeEdge12 = refl
        success13 : V.Runtime
        success13 = withSub (λ c → record c { now = 18; privateState = G.mark G.close (L.peerAddr ∷ []) (C.SubContext.privateState c); pc = Sub.publishView (closeWork ∷ []) }) success12
        closeEdge13 : V.advance closeEvent13 success12 ≡ just success13
        closeEdge13 = refl
        success14 : V.Runtime
        success14 = withSub (λ c → record c { pc = Sub.traceDecision (closeWork ∷ []) }) success13
        closeEdge14 : V.advance closeEvent14 success13 ≡ just success14
        closeEdge14 = refl
        success15 : V.Runtime
        success15 = withSub (λ c → record c { pc = Sub.launch (closeWork ∷ []) }) success14
        closeEdge15 : V.advance closeEvent15 success14 ≡ just success15
        closeEdge15 = refl
        success16 : V.Runtime
        success16 = withGP (λ pool → record pool { handles = put (ident 3) GP.Pool.bodyRunning (GP.Pool.handles pool); parentFork = just (ident 3) }) (withSub (λ c → record c { jobs = put (ident 3) (closeFrame J.begin false) (C.SubContext.jobs c); nextJob = 4; pc = Sub.register (ident 3) [] }) success15)
        closeEdge16 : V.advance closeEvent16 success15 ≡ just success16
        closeEdge16 = refl
        success17 : V.Runtime
        success17 = withGP (λ pool → record pool { registered = ident 3 ∷ GP.Pool.registered pool; parentFork = nothing }) (withSub (λ c → record c { pool = ident 3 ∷ C.SubContext.pool c; pc = Sub.launch [] }) success16)
        closeEdge17 : V.advance closeEvent17 success16 ≡ just success17
        closeEdge17 = refl
        success18 : V.Runtime
        success18 = frameAt J.awaitAll (withSub (λ c → record c { peers = (ident 0 , closePeer) ∷ [] }) success17)
        closeEdge18 : V.advance closeEvent18 success17 ≡ just success18
        closeEdge18 = refl
        success19 : V.Runtime
        success19 = frameAt J.callRelease success18
        closeEdge19 : V.advance closeEvent19 success18 ≡ just success19
        closeEdge19 = refl
        success20 : V.Runtime
        success20 = beginCM (ident 18) (frameAt J.awaitRelease success19)
        closeEdge20 : V.advance closeEvent20 success19 ≡ just success20
        closeEdge20 = refl
        success21 : V.Runtime
        success21 = transactCM (ident 18) success20
        closeEdge21 : V.advance closeEvent21 success20 ≡ just success21
        closeEdge21 = refl
        success22 : V.Runtime
        success22 = countCM (ident 18) success21
        closeEdge22 : V.advance closeEvent22 success21 ≡ just success22
        closeEdge22 = refl
        success23 : V.Runtime
        success23 = returnCM (ident 18) success22
        closeEdge23 : V.advance closeEvent23 success22 ≡ just success23
        closeEdge23 = refl
        success24 : V.Runtime
        success24 = frameAt (J.awaitCold G.succeeded) success23
        closeEdge24 : V.advance closeEvent24 success23 ≡ just success24
        closeEdge24 = refl
        success25 : V.Runtime
        success25 = observeColdPeer success24
        closeEdge25 : V.advance closeEvent25 success24 ≡ just success25
        closeEdge25 = refl
        success26 : V.Runtime
        success26 = returnBody G.succeeded success25
        closeEdge26 : V.advance closeEvent26 success25 ≡ just success26
        closeEdge26 = refl
        success27 : V.Runtime
        success27 = publishBody success26
        closeEdge27 : V.advance closeEvent27 success26 ≡ just success27
        closeEdge27 = refl
        success28 : V.Runtime
        success28 = withSub (λ c → record c { pc = Sub.publishPublic }) success27
        closeEdge28 : V.advance closeEvent28 success27 ≡ just success28
        closeEdge28 = refl
        success29 : V.Runtime
        success29 = withSub (λ c → record c { publicState = C.SubContext.privateState c; pc = Sub.sampleInputs }) success28
        closeEdge29 : V.advance closeEvent29 success28 ≡ just success29
        closeEdge29 = refl
        success30 : V.Runtime
        success30 = withSub (λ c → record c { now = 19; privateState = G.advanceTime 19 (C.SubContext.privateState c); pc = Sub.prepareWait }) success29
        closeEdge30 : V.advance closeEvent30 success29 ≡ just success30
        closeEdge30 = refl
        success31 : V.Runtime
        success31 = withSub (λ c → record c { pc = Sub.selecting; wakeupAt = nothing; wakeupReady = false }) success30
        closeEdge31 : V.advance closeEvent31 success30 ≡ just success31
        closeEdge31 = refl
        success32 : V.Runtime
        success32 = withSub (λ c → record c { pc = Sub.apply (Sub.completion closeCompletion); completions = [] }) success31
        closeEdge32 : V.advance closeEvent32 success31 ≡ just success32
        closeEdge32 = refl
        success33 : V.Runtime
        success33 = withSub (λ c → record c { now = 19; privateState = G.complete (C.SubContext.maxRetries c) (C.SubContext.clearFailDelay c) 19 closeCompletion (C.SubContext.privateState c); pc = Sub.publishView [] }) success32
        closeEdge33 : V.advance closeEvent33 success32 ≡ just success33
        closeEdge33 = refl
        success34 : V.Runtime
        success34 = withSub (λ c → record c { pc = Sub.traceDecision [] }) success33
        closeEdge34 : V.advance closeEvent34 success33 ≡ just success34
        closeEdge34 = refl
        success35 : V.Runtime
        success35 = withSub (λ c → record c { pc = Sub.launch [] }) success34
        closeEdge35 : V.advance closeEvent35 success34 ≡ just success35
        closeEdge35 = refl
        success36 : V.Runtime
        success36 = withSub (λ c → record c { pc = Sub.publishPublic }) success35
        closeEdge36 : V.advance closeEvent36 success35 ≡ just success36
        closeEdge36 = refl
        success37 : V.Runtime
        success37 = withSub (λ c → record c { publicState = C.SubContext.privateState c; pc = Sub.sampleInputs }) success36
        closeEdge37 : V.advance closeEvent37 success36 ≡ just success37
        closeEdge37 = refl
        actual-await-all : lookup (ident 3) (Success.rows success18) ≡ just (closeFrame J.awaitAll false)
        actual-await-all = refl
        actual-call-release : lookup (ident 3) (Success.rows success19) ≡ just (closeFrame J.callRelease false)
        actual-call-release = refl
        actual-release-wait : lookup (ident 3) (Success.rows success20) ≡ just (closeFrame J.awaitRelease false)
        actual-release-wait = refl
        actual-successful-cold-wait : lookup (ident 3) (Success.rows success24) ≡ just (closeFrame (J.awaitCold G.succeeded) false)
        actual-successful-cold-wait = refl
        exact-selected-head : Root.CompletionSelection.result (proj₁ (Agreement.selected-completion success31 success32 closeEdge32)) ≡ closeCompletion
        exact-selected-head = refl
        protocol-body-still-running : lookup jid (Pool.handles (P.poolAt A.child₀ (V.physical (V.base success26)))) ≡ just Pool.bodyRunning
        protocol-body-still-running = refl
        no-premature-async : V.advance (peerStep (PS.run (GP.publishAsyncResult (ident 3)))) success26 ≡ nothing
        no-premature-async = refl
        selected-before-async : lookup (ident 3) (GP.Pool.handles (C.governorPool (K.context (V.base success32)))) ≡
          just (GP.Pool.deregisterPending GP.Pool.normalExit)
        selected-before-async = refl

        no-publication-at-clean-wait : V.advance (ps (Sub.enqueueCompletion (ident 3) 0)) success19 ≡ nothing
        no-publication-at-clean-wait = refl
        no-publication-before-Cold : V.advance (ps (Sub.enqueueCompletion (ident 3) 0)) success24 ≡ nothing
        no-publication-before-Cold = refl

        timeout0 : V.Runtime
        timeout0 = success18
        timeout1 : V.Runtime
        timeout1 = frameAt (J.awaitCold G.succeeded) (stopMux timeout0)
        timeoutEdge1 : V.advance timeoutEvent1 timeout0 ≡ just timeout1
        timeoutEdge1 = refl
        timeout2 : V.Runtime
        timeout2 = beginCM (ident 80) timeout1
        timeoutEdge2 : V.advance timeoutEvent2 timeout1 ≡ just timeout2
        timeoutEdge2 = refl
        timeout3 : V.Runtime
        timeout3 = transactCM (ident 80) timeout2
        timeoutEdge3 : V.advance timeoutEvent3 timeout2 ≡ just timeout3
        timeoutEdge3 = refl
        timeout4 : V.Runtime
        timeout4 = countCM (ident 80) timeout3
        timeoutEdge4 : V.advance timeoutEvent4 timeout3 ≡ just timeout4
        timeoutEdge4 = refl
        timeout5 : V.Runtime
        timeout5 = returnCM (ident 80) timeout4
        timeoutEdge5 : V.advance timeoutEvent5 timeout4 ≡ just timeout5
        timeoutEdge5 = refl
        timeout6 : V.Runtime
        timeout6 = observeColdPeer timeout5
        timeoutEdge6 : V.advance timeoutEvent6 timeout5 ≡ just timeout6
        timeoutEdge6 = refl
        timeout7 : V.Runtime
        timeout7 = returnBody G.succeeded timeout6
        timeoutEdge7 : V.advance timeoutEvent7 timeout6 ≡ just timeout7
        timeoutEdge7 = refl
        timeout8 : V.Runtime
        timeout8 = publishBody timeout7
        timeoutEdge8 : V.advance timeoutEvent8 timeout7 ≡ just timeout8
        timeoutEdge8 = refl
        coldEntry0 : V.Runtime
        coldEntry0 = success17
        coldEntry1 : V.Runtime
        coldEntry1 = withBackground (PS.errorWait err) (just (Cancel.cancellation (ident 50) err Cancel.noCaller (Cancel.finished Cancel.abandoned))) coldEntry0
        coldEntryEdge1 : V.advance coldEntryEvent1 coldEntry0 ≡ just coldEntry1
        coldEntryEdge1 = refl
        coldEntry2 : V.Runtime
        coldEntry2 = beginCM (ident 80) coldEntry1
        coldEntryEdge2 : V.advance coldEntryEvent2 coldEntry1 ≡ just coldEntry2
        coldEntryEdge2 = refl
        coldEntry3 : V.Runtime
        coldEntry3 = transactCM (ident 80) coldEntry2
        coldEntryEdge3 : V.advance coldEntryEvent3 coldEntry2 ≡ just coldEntry3
        coldEntryEdge3 = refl
        coldEntry4 : V.Runtime
        coldEntry4 = countCM (ident 80) coldEntry3
        coldEntryEdge4 : V.advance coldEntryEvent4 coldEntry3 ≡ just coldEntry4
        coldEntryEdge4 = refl
        coldEntry5 : V.Runtime
        coldEntry5 = returnCM (ident 80) coldEntry4
        coldEntryEdge5 : V.advance coldEntryEvent5 coldEntry4 ≡ just coldEntry5
        coldEntryEdge5 = refl
        coldEntry6 : V.Runtime
        coldEntry6 = withBackground (PS.errorFinishing err) (just (Cancel.cancellation (ident 50) err Cancel.noCaller (Cancel.finished Cancel.abandoned))) (withSub (λ c → record c { peers = (ident 0 , record Reactivation.retiredPeer { status = Peer.peerCold }) ∷ [] }) coldEntry5)
        coldEntryEdge6 : V.advance coldEntryEvent6 coldEntry5 ≡ just coldEntry6
        coldEntryEdge6 = refl
        coldEntry7 : V.Runtime
        coldEntry7 = frameAt (J.awaitCold G.succeeded) (withSub (λ c → record c { peers = (ident 0 , record closePeer { status = Peer.peerCold }) ∷ [] }) coldEntry6)
        coldEntryEdge7 : V.advance coldEntryEvent7 coldEntry6 ≡ just coldEntry7
        coldEntryEdge7 = refl
        coldEntry8 : V.Runtime
        coldEntry8 = returnBody G.succeeded coldEntry7
        coldEntryEdge8 : V.advance coldEntryEvent8 coldEntry7 ≡ just coldEntry8
        coldEntryEdge8 = refl
        coldEntry9 : V.Runtime
        coldEntry9 = publishBody coldEntry8
        coldEntryEdge9 : V.advance coldEntryEvent9 coldEntry8 ≡ just coldEntry9
        coldEntryEdge9 = refl
        timeout-waits-for-Cold : lookup (ident 3) (Success.rows timeout1) ≡ just (closeFrame (J.awaitCold G.succeeded) false)
        timeout-waits-for-Cold = refl
        timeout-did-not-request-release : lookup (ident 18) (O.releasing (V.sourceOf timeout1)) ≡ nothing
        timeout-did-not-request-release = refl
        Cold-entry-waits-for-Cold : lookup (ident 3) (Success.rows coldEntry7) ≡ just (closeFrame (J.awaitCold G.succeeded) false)
        Cold-entry-waits-for-Cold = refl
        Cold-entry-did-not-request-release : lookup (ident 18) (O.releasing (V.sourceOf coldEntry7)) ≡ nothing
        Cold-entry-did-not-request-release = refl
        demotionExpired : V.Runtime
        demotionExpired = returnBody G.demotionTimedOut success24
        demotion-timeout-outcome : lookup (ident 3) (Success.rows demotionExpired) ≡ just (closeFrame (J.complete G.demotionTimedOut) false)
        demotion-timeout-outcome = refl
        demotion-timeout-not-success : G.demotionTimedOut ≡ G.succeeded → ⊥
        demotion-timeout-not-success ()

        applied-close-removes-established : G.establishedPeers (C.SubContext.privateState (C.subsystem (K.context (V.base success37)))) ≡ []
        applied-close-removes-established = refl
        published-close-removes-established : G.establishedPeers (C.SubContext.publicState (C.subsystem (K.context (V.base success37)))) ≡ []
        published-close-removes-established = refl
        initialized-success0 : V.Runs initial (GC.completedActions ++ GC.governorActions) success0
        initialized-success0 = GC.initialized-public-after
        actual-complete : lookup (ident 3) (Success.rows success26) ≡ just (closeFrame (J.complete G.succeeded) false)
        actual-complete = refl
        pending27 : closeCompletion ∈ Evidence.View.pending (QueueProvenance.runtime-view success27)
        pending27 = here refl
        pendingTimeout : closeCompletion ∈ Evidence.View.pending (QueueProvenance.runtime-view timeout8)
        pendingTimeout = here refl
        pendingEntry : closeCompletion ∈ Evidence.View.pending (QueueProvenance.runtime-view coldEntry9)
        pendingEntry = here refl
        demotion-timeout-step : V.advance (ps (Sub.jobStep (ident 3) J.demotionTimeout)) success24 ≡ just demotionExpired
        demotion-timeout-step = refl

        timeout-start : timeout0 ≡ success18
        timeout-start = refl
        cold-entry-start : coldEntry0 ≡ success17
        cold-entry-start = refl

        -- Physical exit remains pending after the close result is consumed and
        -- the governor's public established set has already been cleared.
        normalReturned normalRemoved normalPublished : V.Runtime
        normalReturned = finishPhysical nothing success37
        normalRemoved = removePhysical normalReturned
        normalPublished = publishPhysical normalRemoved
        normalReturnEdge : V.advance (Monitors.event Monitor.normal (ident 50)) success37 ≡ just normalReturned
        normalReturnEdge = refl
        normalRemoveEdge : V.advance removeMonitor normalReturned ≡ just normalRemoved
        normalRemoveEdge = refl
        normalPublishEdge : V.advance publishMonitor normalRemoved ≡ just normalPublished
        normalPublishEdge = refl
        errorReturned errorRemoved errorPublished : V.Runtime
        errorReturned = finishPhysical (just (Cancel.cancellation (ident 50) err Cancel.noCaller (Cancel.finished Cancel.abandoned))) coldEntry9
        errorRemoved = removePhysical errorReturned
        errorPublished = publishPhysical errorRemoved
        errorReturnEdge : V.advance (Monitors.event Monitor.exceptional (ident 50)) coldEntry9 ≡ just errorReturned
        errorReturnEdge = refl
        errorRemoveEdge : V.advance removeMonitor errorReturned ≡ just errorRemoved
        errorRemoveEdge = refl
        errorPublishEdge : V.advance publishMonitor errorRemoved ≡ just errorPublished
        errorPublishEdge = refl
        normal-still-running-after-public-close : lookup (ident 50) (PS.Pool.handles (C.monitorPool (K.context (V.base success37)))) ≡ just PS.Pool.bodyRunning
        normal-still-running-after-public-close = refl
        error-still-running-after-governor-return : lookup (ident 50) (PS.Pool.handles (C.monitorPool (K.context (V.base coldEntry9)))) ≡ just PS.Pool.bodyRunning
        error-still-running-after-governor-return = refl
        no-normal-early-removal : V.advance (removeMonitor) success37 ≡ nothing
        no-normal-early-removal = refl
        no-normal-early-Async : V.advance (publishMonitor) success37 ≡ nothing
        no-normal-early-Async = refl
        no-error-early-removal : V.advance (removeMonitor) coldEntry9 ≡ nothing
        no-error-early-removal = refl
        no-error-early-Async : V.advance (publishMonitor) coldEntry9 ≡ nothing
        no-error-early-Async = refl
        normal-return-is-not-error : V.advance (Monitors.event Monitor.exceptional (ident 50)) success37 ≡ nothing
        normal-return-is-not-error = refl
        error-return-is-not-normal : V.advance (Monitors.event Monitor.normal (ident 50)) coldEntry9 ≡ nothing
        error-return-is-not-normal = refl
        normal-return-is-not-unwind : V.advance (Monitors.event Monitor.cancelled (ident 50)) success37 ≡ nothing
        normal-return-is-not-unwind = refl
        error-return-is-not-unwind : V.advance (Monitors.event Monitor.cancelled (ident 50)) coldEntry9 ≡ nothing
        error-return-is-not-unwind = refl
        no-Async-before-removal : V.advance (publishMonitor) normalReturned ≡ nothing
        no-Async-before-removal = refl
        no-double-normal-return : V.advance (Monitors.event Monitor.normal (ident 50)) normalReturned ≡ nothing
        no-double-normal-return = refl
        normal-returned-phase : lookup (ident 50) (PS.Pool.handles (C.monitorPool (K.context (V.base normalReturned)))) ≡ just (PS.Pool.deregisterPending PS.Pool.normalExit)
        normal-returned-phase = refl
        normal-removed-phase : lookup (ident 50) (PS.Pool.handles (C.monitorPool (K.context (V.base normalRemoved)))) ≡ just (PS.Pool.deregistered PS.Pool.normalExit)
        normal-removed-phase = refl
        normal-published-phase : lookup (ident 50) (PS.Pool.handles (C.monitorPool (K.context (V.base normalPublished)))) ≡ just (PS.Pool.resultAvailable PS.Pool.normalExit)
        normal-published-phase = refl
        normal-returned-registry : PS.Pool.registered (C.monitorPool (K.context (V.base normalReturned))) ≡ (ident 50 ∷ [])
        normal-returned-registry = refl
        normal-removed-registry : PS.Pool.registered (C.monitorPool (K.context (V.base normalRemoved))) ≡ ([])
        normal-removed-registry = refl
        error-returned-phase : lookup (ident 50) (PS.Pool.handles (C.monitorPool (K.context (V.base errorReturned)))) ≡ just (PS.Pool.deregisterPending PS.Pool.normalExit)
        error-returned-phase = refl
        error-removed-phase : lookup (ident 50) (PS.Pool.handles (C.monitorPool (K.context (V.base errorRemoved)))) ≡ just (PS.Pool.deregistered PS.Pool.normalExit)
        error-removed-phase = refl
        error-published-phase : lookup (ident 50) (PS.Pool.handles (C.monitorPool (K.context (V.base errorPublished)))) ≡ just (PS.Pool.resultAvailable PS.Pool.normalExit)
        error-published-phase = refl
        error-returned-registry : PS.Pool.registered (C.monitorPool (K.context (V.base errorReturned))) ≡ (ident 50 ∷ [])
        error-returned-registry = refl
        error-removed-registry : PS.Pool.registered (C.monitorPool (K.context (V.base errorRemoved))) ≡ ([])
        error-removed-registry = refl
        handled-error-body-operation : PS.Pool.step (PS.Pool.bodyReturnedWith (ident 50) (just err))
          (C.monitorPool (K.context (V.base coldEntry9))) ≡ just (C.monitorPool (K.context (V.base errorReturned)))
        handled-error-body-operation = refl
        normal-thread-at-return : lookup (ident 50) (PS.monitors (Monitors.peers success37)) ≡ just (background PS.normalFinishing nothing)
        normal-thread-at-return = refl
        error-thread-at-return : lookup (ident 50) (PS.monitors (Monitors.peers coldEntry9)) ≡ just (background (PS.errorFinishing err) (just (Cancel.cancellation (ident 50) err Cancel.noCaller (Cancel.finished Cancel.abandoned))))
        error-thread-at-return = refl

        -- This arbitrary snapshot can publish a terminal Async result while
        -- retaining the running thread PC. It is not the initialized prefix.
        forgedMonitorRemoved forgedMonitorPublished : V.Runtime
        forgedMonitorRemoved = withMonitorPool (λ pool → record pool
          { handles = put (ident 50) (PS.Pool.deregistered PS.Pool.normalExit) (PS.Pool.handles pool) }) success37
        forgedMonitorPublished = publishPhysical forgedMonitorRemoved
        forgedMonitorPublishEdge : V.advance publishMonitor forgedMonitorRemoved ≡ just forgedMonitorPublished
        forgedMonitorPublishEdge = refl
        forged-monitor-removed-phase : lookup (ident 50) (PS.Pool.handles (Backing.pool forgedMonitorRemoved)) ≡ just (PS.Pool.deregistered PS.Pool.normalExit)
        forged-monitor-removed-phase = refl
        forged-monitor-still-finishing : lookup (ident 50) (PS.monitors (Backing.peers forgedMonitorPublished)) ≡ just (background PS.normalFinishing nothing)
        forged-monitor-still-finishing = refl

        -- Real target-input writes interleave between the lifecycle stages
        -- and after publication, while the monitor pool keeps its history.
        gap1 gap2 gap3 gap4 gap5 : V.Runtime
        gap1 = withSub (λ c → record c { targetInput = G.targets 0 0 0 }) normalReturned
        gap2 = removePhysical gap1
        gap3 = withSub (λ c → record c { targetInput = G.targets 1 0 0 }) gap2
        gap4 = publishPhysical gap3
        gap5 = withSub (λ c → record c { targetInput = G.targets 1 1 0 }) gap4
        gapEdge1 : V.advance gapBeforeRemoval normalReturned ≡ just gap1
        gapEdge1 = refl
        gapEdge2 : V.advance removeMonitor gap1 ≡ just gap2
        gapEdge2 = refl
        gapEdge3 : V.advance gapBeforePublication gap2 ≡ just gap3
        gapEdge3 = refl
        gapEdge4 : V.advance publishMonitor gap3 ≡ just gap4
        gapEdge4 = refl
        gapEdge5 : V.advance gapAfterPublication gap4 ≡ just gap5
        gapEdge5 = refl
        gap5-phase : lookup (ident 50) (PS.Pool.handles (Stages.pool gap5)) ≡ just (PS.Pool.resultAvailable PS.Pool.normalExit)
        gap5-phase = refl
        gap1-target : C.SubContext.targetInput (sub gap1) ≡ G.targets 0 0 0
        gap1-target = refl
        gap3-target : C.SubContext.targetInput (sub gap3) ≡ G.targets 1 0 0
        gap3-target = refl
        gap5-target : C.SubContext.targetInput (sub gap5) ≡ G.targets 1 1 0
        gap5-target = refl

    open Snapshots public

    module Proofs where
      abstract
        initialized-success17 : V.Runs initial successPrefix17 success17
        initialized-success17 = Facts.append-protocols {s = initial} {as = (GC.completedActions ++ GC.governorActions)} {t = success0} {bs = (closeEvent1 ∷ closeEvent2 ∷ closeEvent3 ∷ closeEvent4 ∷ closeEvent5 ∷ closeEvent6 ∷ closeEvent7 ∷ closeEvent8 ∷ closeEvent9 ∷ closeEvent10 ∷ closeEvent11 ∷ closeEvent12 ∷ closeEvent13 ∷ closeEvent14 ∷ closeEvent15 ∷ closeEvent16 ∷ closeEvent17 ∷ [])} {u = success17}
          initialized-success0 (V.more {s = success0} {t = success1} {u = success17} {a = closeEvent1} closeEdge1 (V.more {s = success1} {t = success2} {u = success17} {a = closeEvent2} closeEdge2 (V.more {s = success2} {t = success3} {u = success17} {a = closeEvent3} closeEdge3 (V.more {s = success3} {t = success4} {u = success17} {a = closeEvent4} closeEdge4 (V.more {s = success4} {t = success5} {u = success17} {a = closeEvent5} closeEdge5 (V.more {s = success5} {t = success6} {u = success17} {a = closeEvent6} closeEdge6 (V.more {s = success6} {t = success7} {u = success17} {a = closeEvent7} closeEdge7 (V.more {s = success7} {t = success8} {u = success17} {a = closeEvent8} closeEdge8 (V.more {s = success8} {t = success9} {u = success17} {a = closeEvent9} closeEdge9 (V.more {s = success9} {t = success10} {u = success17} {a = closeEvent10} closeEdge10 (V.more {s = success10} {t = success11} {u = success17} {a = closeEvent11} closeEdge11 (V.more {s = success11} {t = success12} {u = success17} {a = closeEvent12} closeEdge12 (V.more {s = success12} {t = success13} {u = success17} {a = closeEvent13} closeEdge13 (V.more {s = success13} {t = success14} {u = success17} {a = closeEvent14} closeEdge14 (V.more {s = success14} {t = success15} {u = success17} {a = closeEvent15} closeEdge15 (V.more {s = success15} {t = success16} {u = success17} {a = closeEvent16} closeEdge16 (V.more {s = success16} {t = success17} {u = success17} {a = closeEvent17} closeEdge17 (V.stop {s = success17}))))))))))))))))))
        initialized-success18 : V.Runs initial successPrefix18 success18
        initialized-success18 = Facts.append-protocols {s = initial} {as = successPrefix17} {t = success17} {bs = (closeEvent18 ∷ [])} {u = success18}
          initialized-success17 (V.more {s = success17} {t = success18} {u = success18} {a = closeEvent18} closeEdge18 (V.stop {s = success18}))
        initialized-success19 : V.Runs initial successPrefix19 success19
        initialized-success19 = Facts.append-protocols {s = initial} {as = successPrefix18} {t = success18} {bs = (closeEvent19 ∷ [])} {u = success19}
          initialized-success18 (V.more {s = success18} {t = success19} {u = success19} {a = closeEvent19} closeEdge19 (V.stop {s = success19}))
        initialized-success20 : V.Runs initial successPrefix20 success20
        initialized-success20 = Facts.append-protocols {s = initial} {as = successPrefix19} {t = success19} {bs = (closeEvent20 ∷ [])} {u = success20}
          initialized-success19 (V.more {s = success19} {t = success20} {u = success20} {a = closeEvent20} closeEdge20 (V.stop {s = success20}))
        initialized-success24 : V.Runs initial successPrefix24 success24
        initialized-success24 = Facts.append-protocols {s = initial} {as = successPrefix20} {t = success20} {bs = (closeEvent21 ∷ closeEvent22 ∷ closeEvent23 ∷ closeEvent24 ∷ [])} {u = success24}
          initialized-success20 (V.more {s = success20} {t = success21} {u = success24} {a = closeEvent21} closeEdge21 (V.more {s = success21} {t = success22} {u = success24} {a = closeEvent22} closeEdge22 (V.more {s = success22} {t = success23} {u = success24} {a = closeEvent23} closeEdge23 (V.more {s = success23} {t = success24} {u = success24} {a = closeEvent24} closeEdge24 (V.stop {s = success24})))))
        initialized-success26 : V.Runs initial successPrefix26 success26
        initialized-success26 = Facts.append-protocols {s = initial} {as = successPrefix24} {t = success24} {bs = (closeEvent25 ∷ closeEvent26 ∷ [])} {u = success26}
          initialized-success24 (V.more {s = success24} {t = success25} {u = success26} {a = closeEvent25} closeEdge25 (V.more {s = success25} {t = success26} {u = success26} {a = closeEvent26} closeEdge26 (V.stop {s = success26})))
        initialized-success27 : V.Runs initial successPrefix27 success27
        initialized-success27 = Facts.append-protocols {s = initial} {as = successPrefix26} {t = success26} {bs = (closeEvent27 ∷ [])} {u = success27}
          initialized-success26 (V.more {s = success26} {t = success27} {u = success27} {a = closeEvent27} closeEdge27 (V.stop {s = success27}))
        initialized-success31 : V.Runs initial successPrefix31 success31
        initialized-success31 = Facts.append-protocols {s = initial} {as = successPrefix27} {t = success27} {bs = (closeEvent28 ∷ closeEvent29 ∷ closeEvent30 ∷ closeEvent31 ∷ [])} {u = success31}
          initialized-success27 (V.more {s = success27} {t = success28} {u = success31} {a = closeEvent28} closeEdge28 (V.more {s = success28} {t = success29} {u = success31} {a = closeEvent29} closeEdge29 (V.more {s = success29} {t = success30} {u = success31} {a = closeEvent30} closeEdge30 (V.more {s = success30} {t = success31} {u = success31} {a = closeEvent31} closeEdge31 (V.stop {s = success31})))))
        initialized-success37 : V.Runs initial successPrefix37 success37
        initialized-success37 = Facts.append-protocols {s = initial} {as = successPrefix31} {t = success31} {bs = (closeEvent32 ∷ closeEvent33 ∷ closeEvent34 ∷ closeEvent35 ∷ closeEvent36 ∷ closeEvent37 ∷ [])} {u = success37}
          initialized-success31 (V.more {s = success31} {t = success32} {u = success37} {a = closeEvent32} closeEdge32 (V.more {s = success32} {t = success33} {u = success37} {a = closeEvent33} closeEdge33 (V.more {s = success33} {t = success34} {u = success37} {a = closeEvent34} closeEdge34 (V.more {s = success34} {t = success35} {u = success37} {a = closeEvent35} closeEdge35 (V.more {s = success35} {t = success36} {u = success37} {a = closeEvent36} closeEdge36 (V.more {s = success36} {t = success37} {u = success37} {a = closeEvent37} closeEdge37 (V.stop {s = success37})))))))
        clean-agreement : Agreement.JobAgreement (ident 3) success18 success19
        clean-agreement = Agreement.initialized-job-agreement {c = initialCM} {g = L.settings} {start = initial} {as = successPrefix18} {s = success18} {t = success19} (ident 3) initializer initialized-success18 closeEdge19
        clean-captures : PhysicalReads.CleanReads clean-agreement
        clean-captures = Agreement.job-success-captures (ident 3) success18 success19 clean-agreement (closeFrame J.callRelease false) actual-call-release refl
        close-result : Success.History initial success26 (ident 3) closeWork
        close-result = Success.get-success {start = initial} {current = success26} {j = ident 3} {work = closeWork} {pc = J.complete G.succeeded} (Success.initialized-valid {c = initialCM} {g = L.settings} {start = initial} {actions = successPrefix26} {current = success26} initializer initialized-success26 (ident 3)
          (closeFrame (J.complete G.succeeded) false) actual-complete refl) refl
        pending-publication : QueueProvenance.Origin initial success27 closeCompletion
        pending-publication = QueueProvenance.initialized-pending {c = initialCM} {g = L.settings} {start = initial} {actions = successPrefix27} {s = success27} {result = closeCompletion} initializer initialized-success27 pending27
        published-result : Success.History initial success27
          (Evidence.Publication.job (QueueProvenance.Origin.published pending-publication)) closeWork
        published-result = Success.origin-success {c = initialCM} {g = L.settings} {start = initial} {current = success27} {result = closeCompletion} initializer pending-publication refl refl
        consumed-publication : QueueProvenance.Origin initial success31 closeCompletion
        consumed-publication = subst (QueueProvenance.Origin initial success31) exact-selected-head
          (QueueProvenance.initialized-consumed {c = initialCM} {g = L.settings} {start = initial} {actions = successPrefix31} {s = success31} {t = success32} initializer initialized-success31 closeEdge32)
        consumed-result : Success.History initial success31
          (Evidence.Publication.job (QueueProvenance.Origin.published consumed-publication)) closeWork
        consumed-result = Success.origin-success {c = initialCM} {g = L.settings} {start = initial} {current = success31} {result = closeCompletion} initializer consumed-publication refl refl
        selected-through-public : V.Runs success31 (drop 31 closeRouteActions) success37
        selected-through-public = V.more {s = success31} {t = success32} {u = success37} {a = closeEvent32} closeEdge32 (V.more {s = success32} {t = success33} {u = success37} {a = closeEvent33} closeEdge33 (V.more {s = success33} {t = success34} {u = success37} {a = closeEvent34} closeEdge34 (V.more {s = success34} {t = success35} {u = success37} {a = closeEvent35} closeEdge35 (V.more {s = success35} {t = success36} {u = success37} {a = closeEvent36} closeEdge36 (V.more {s = success36} {t = success37} {u = success37} {a = closeEvent37} closeEdge37 (V.stop {s = success37}))))))
        retained-result : Success.History initial success37
          (Evidence.Publication.job (QueueProvenance.Origin.published consumed-publication)) closeWork
        retained-result = Success.extend-through {start = initial} {s = success31} {t = success37} {j = Evidence.Publication.job (QueueProvenance.Origin.published consumed-publication)} {work = closeWork} {actions = drop 31 closeRouteActions} selected-through-public consumed-result
        initialized-timeout : V.Runs initial (successPrefix18 ++ timeoutActions) timeout8
        initialized-timeout = Facts.append-protocols {s = initial} {as = successPrefix18} {t = timeout0} {bs = timeoutActions} {u = timeout8}
          (subst (V.Runs initial successPrefix18) (sym timeout-start) initialized-success18) (V.more {s = timeout0} {t = timeout1} {u = timeout8} {a = timeoutEvent1} timeoutEdge1 (V.more {s = timeout1} {t = timeout2} {u = timeout8} {a = timeoutEvent2} timeoutEdge2 (V.more {s = timeout2} {t = timeout3} {u = timeout8} {a = timeoutEvent3} timeoutEdge3 (V.more {s = timeout3} {t = timeout4} {u = timeout8} {a = timeoutEvent4} timeoutEdge4 (V.more {s = timeout4} {t = timeout5} {u = timeout8} {a = timeoutEvent5} timeoutEdge5 (V.more {s = timeout5} {t = timeout6} {u = timeout8} {a = timeoutEvent6} timeoutEdge6 (V.more {s = timeout6} {t = timeout7} {u = timeout8} {a = timeoutEvent7} timeoutEdge7 (V.more {s = timeout7} {t = timeout8} {u = timeout8} {a = timeoutEvent8} timeoutEdge8 (V.stop {s = timeout8})))))))))
        timeout-publication : QueueProvenance.Origin initial timeout8 closeCompletion
        timeout-publication = QueueProvenance.initialized-pending {c = initialCM} {g = L.settings} {start = initial} {actions = (successPrefix18 ++ timeoutActions)} {s = timeout8} {result = closeCompletion} initializer initialized-timeout pendingTimeout
        timeout-success : Success.History initial timeout8
          (Evidence.Publication.job (QueueProvenance.Origin.published timeout-publication)) closeWork
        timeout-success = Success.origin-success {c = initialCM} {g = L.settings} {start = initial} {current = timeout8} {result = closeCompletion} initializer timeout-publication refl refl

        initialized-coldEntry : V.Runs initial (successPrefix17 ++ coldEntryActions) coldEntry9
        initialized-coldEntry = Facts.append-protocols {s = initial} {as = successPrefix17} {t = coldEntry0} {bs = coldEntryActions} {u = coldEntry9}
          (subst (V.Runs initial successPrefix17) (sym cold-entry-start) initialized-success17) (V.more {s = coldEntry0} {t = coldEntry1} {u = coldEntry9} {a = coldEntryEvent1} coldEntryEdge1 (V.more {s = coldEntry1} {t = coldEntry2} {u = coldEntry9} {a = coldEntryEvent2} coldEntryEdge2 (V.more {s = coldEntry2} {t = coldEntry3} {u = coldEntry9} {a = coldEntryEvent3} coldEntryEdge3 (V.more {s = coldEntry3} {t = coldEntry4} {u = coldEntry9} {a = coldEntryEvent4} coldEntryEdge4 (V.more {s = coldEntry4} {t = coldEntry5} {u = coldEntry9} {a = coldEntryEvent5} coldEntryEdge5 (V.more {s = coldEntry5} {t = coldEntry6} {u = coldEntry9} {a = coldEntryEvent6} coldEntryEdge6 (V.more {s = coldEntry6} {t = coldEntry7} {u = coldEntry9} {a = coldEntryEvent7} coldEntryEdge7 (V.more {s = coldEntry7} {t = coldEntry8} {u = coldEntry9} {a = coldEntryEvent8} coldEntryEdge8 (V.more {s = coldEntry8} {t = coldEntry9} {u = coldEntry9} {a = coldEntryEvent9} coldEntryEdge9 (V.stop {s = coldEntry9}))))))))))
        coldEntry-publication : QueueProvenance.Origin initial coldEntry9 closeCompletion
        coldEntry-publication = QueueProvenance.initialized-pending {c = initialCM} {g = L.settings} {start = initial} {actions = (successPrefix17 ++ coldEntryActions)} {s = coldEntry9} {result = closeCompletion} initializer initialized-coldEntry pendingEntry
        coldEntry-success : Success.History initial coldEntry9
          (Evidence.Publication.job (QueueProvenance.Origin.published coldEntry-publication)) closeWork
        coldEntry-success = Success.origin-success {c = initialCM} {g = L.settings} {start = initial} {current = coldEntry9} {result = closeCompletion} initializer coldEntry-publication refl refl
        normal-exit-origin : Monitors.Origin initial normalReturned (ident 50) Monitor.normal
        normal-exit-origin = Monitors.initialized-exit {c = initialCM} {g = L.settings} {start = initial} {before = success37} {after = normalReturned} {prefix = successPrefix37}
          Monitor.normal (ident 50) initializer initialized-success37 normalReturnEdge
        error-exit-origin : Monitors.Origin initial errorReturned (ident 50) Monitor.exceptional
        error-exit-origin = Monitors.initialized-exit {c = initialCM} {g = L.settings} {start = initial} {before = coldEntry9} {after = errorReturned} {prefix = successPrefix17 ++ coldEntryActions}
          Monitor.exceptional (ident 50) initializer initialized-coldEntry errorReturnEdge
        normal-removed-origin : Monitors.Removed initial normalRemoved (ident 50) Monitor.normal
        normal-removed-origin = Monitors.remove-origin {start = initial} {s = normalReturned} {t = normalRemoved} {tid = ident 50} {kind = Monitor.normal} normal-exit-origin normalRemoveEdge
        normal-published-origin : Monitors.Published initial normalPublished (ident 50) Monitor.normal
        normal-published-origin = Monitors.publish-origin {start = initial} {s = normalRemoved} {t = normalPublished} {tid = ident 50} {kind = Monitor.normal} normal-removed-origin normalPublishEdge
        normal-retained-origin : Monitors.Origin initial normalPublished (ident 50) Monitor.normal
        normal-retained-origin = Monitors.extend {start = initial} {s = normalReturned} {t = normalPublished} {tid = ident 50} {kind = Monitor.normal} {actions = removeMonitor ∷ publishMonitor ∷ []}
          (V.more {s = normalReturned} {t = normalRemoved} {u = normalPublished} {a = removeMonitor} normalRemoveEdge
            (V.more {s = normalRemoved} {t = normalPublished} {u = normalPublished} {a = publishMonitor} normalPublishEdge (V.stop {s = normalPublished}))) normal-exit-origin
        error-removed-origin : Monitors.Removed initial errorRemoved (ident 50) Monitor.exceptional
        error-removed-origin = Monitors.remove-origin {start = initial} {s = errorReturned} {t = errorRemoved} {tid = ident 50} {kind = Monitor.exceptional} error-exit-origin errorRemoveEdge
        error-published-origin : Monitors.Published initial errorPublished (ident 50) Monitor.exceptional
        error-published-origin = Monitors.publish-origin {start = initial} {s = errorRemoved} {t = errorPublished} {tid = ident 50} {kind = Monitor.exceptional} error-removed-origin errorPublishEdge
        error-retained-origin : Monitors.Origin initial errorPublished (ident 50) Monitor.exceptional
        error-retained-origin = Monitors.extend {start = initial} {s = errorReturned} {t = errorPublished} {tid = ident 50} {kind = Monitor.exceptional} {actions = removeMonitor ∷ publishMonitor ∷ []}
          (V.more {s = errorReturned} {t = errorRemoved} {u = errorPublished} {a = removeMonitor} errorRemoveEdge
            (V.more {s = errorRemoved} {t = errorPublished} {u = errorPublished} {a = publishMonitor} errorPublishEdge (V.stop {s = errorPublished}))) error-exit-origin

        -- Query each terminal handle directly. These applications supply only
        -- initialization, enabled execution and the current phase lookup.
        initialized-normal-physical1 : V.Runs initial normalPrefix1 normalReturned
        initialized-normal-physical1 = Facts.append-protocols {s = initial} {as = successPrefix37} {t = success37} {bs = (Monitors.event Monitor.normal (ident 50) ∷ [])} {u = normalReturned}
          initialized-success37 (V.more {s = success37} {t = normalReturned} {u = normalReturned} {a = Monitors.event Monitor.normal (ident 50)} normalReturnEdge (V.stop {s = normalReturned}))
        normal-pending-backing : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Backing.History initial normalReturned (ident 50) cause)
        normal-pending-backing = Backing.initialized-pending {c = initialCM} {g = L.settings} {start = initial} {actions = normalPrefix1} {current = normalReturned} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-normal-physical1 normal-returned-phase
        initialized-normal-physical2 : V.Runs initial normalPrefix2 normalRemoved
        initialized-normal-physical2 = Facts.append-protocols {s = initial} {as = normalPrefix1} {t = normalReturned} {bs = (removeMonitor ∷ [])} {u = normalRemoved}
          initialized-normal-physical1 (V.more {s = normalReturned} {t = normalRemoved} {u = normalRemoved} {a = removeMonitor} normalRemoveEdge (V.stop {s = normalRemoved}))
        normal-removed-backing : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Backing.History initial normalRemoved (ident 50) cause)
        normal-removed-backing = Backing.initialized-removed {c = initialCM} {g = L.settings} {start = initial} {actions = normalPrefix2} {current = normalRemoved} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-normal-physical2 normal-removed-phase
        initialized-normal-physical3 : V.Runs initial normalPrefix3 normalPublished
        initialized-normal-physical3 = Facts.append-protocols {s = initial} {as = normalPrefix2} {t = normalRemoved} {bs = (publishMonitor ∷ [])} {u = normalPublished}
          initialized-normal-physical2 (V.more {s = normalRemoved} {t = normalPublished} {u = normalPublished} {a = publishMonitor} normalPublishEdge (V.stop {s = normalPublished}))
        normal-published-backing : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Backing.History initial normalPublished (ident 50) cause)
        normal-published-backing = Backing.initialized-published {c = initialCM} {g = L.settings} {start = initial} {actions = normalPrefix3} {current = normalPublished} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-normal-physical3 normal-published-phase
        initialized-error-physical1 : V.Runs initial errorPrefix1 errorReturned
        initialized-error-physical1 = Facts.append-protocols {s = initial} {as = successPrefix17 ++ coldEntryActions} {t = coldEntry9} {bs = (Monitors.event Monitor.exceptional (ident 50) ∷ [])} {u = errorReturned}
          initialized-coldEntry (V.more {s = coldEntry9} {t = errorReturned} {u = errorReturned} {a = Monitors.event Monitor.exceptional (ident 50)} errorReturnEdge (V.stop {s = errorReturned}))
        error-pending-backing : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Backing.History initial errorReturned (ident 50) cause)
        error-pending-backing = Backing.initialized-pending {c = initialCM} {g = L.settings} {start = initial} {actions = errorPrefix1} {current = errorReturned} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-error-physical1 error-returned-phase
        initialized-error-physical2 : V.Runs initial errorPrefix2 errorRemoved
        initialized-error-physical2 = Facts.append-protocols {s = initial} {as = errorPrefix1} {t = errorReturned} {bs = (removeMonitor ∷ [])} {u = errorRemoved}
          initialized-error-physical1 (V.more {s = errorReturned} {t = errorRemoved} {u = errorRemoved} {a = removeMonitor} errorRemoveEdge (V.stop {s = errorRemoved}))
        error-removed-backing : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Backing.History initial errorRemoved (ident 50) cause)
        error-removed-backing = Backing.initialized-removed {c = initialCM} {g = L.settings} {start = initial} {actions = errorPrefix2} {current = errorRemoved} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-error-physical2 error-removed-phase
        initialized-error-physical3 : V.Runs initial errorPrefix3 errorPublished
        initialized-error-physical3 = Facts.append-protocols {s = initial} {as = errorPrefix2} {t = errorRemoved} {bs = (publishMonitor ∷ [])} {u = errorPublished}
          initialized-error-physical2 (V.more {s = errorRemoved} {t = errorPublished} {u = errorPublished} {a = publishMonitor} errorPublishEdge (V.stop {s = errorPublished}))
        error-published-backing : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Backing.History initial errorPublished (ident 50) cause)
        error-published-backing = Backing.initialized-published {c = initialCM} {g = L.settings} {start = initial} {actions = errorPrefix3} {current = errorPublished} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-error-physical3 error-published-phase
        forged-monitor-not-at-prefix : V.Runs initial successPrefix37 forgedMonitorRemoved → ⊥
        forged-monitor-not-at-prefix path = case just-injective
          (trans (sym normal-still-running-after-public-close)
            (trans (cong (λ runtime → lookup (ident 50) (PS.Pool.handles (Backing.pool runtime))) (same-run initialized-success37 path)) forged-monitor-removed-phase)) of λ ()

        -- Stage queries derive their causal predecessors; none of these
        -- applications receives a pre-constructed return/removal history.
        normal-pending-stages : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Backing.History initial normalReturned (ident 50) cause)
        normal-pending-stages = Stages.initialized-pending {c = initialCM} {g = L.settings} {start = initial} {actions = normalPrefix1} {current = normalReturned} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-normal-physical1 normal-returned-phase
        normal-removed-stages : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Stages.Removal initial normalRemoved (ident 50) cause)
        normal-removed-stages = Stages.initialized-removed {c = initialCM} {g = L.settings} {start = initial} {actions = normalPrefix2} {current = normalRemoved} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-normal-physical2 normal-removed-phase
        normal-published-stages : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Stages.Publication initial normalPublished (ident 50) cause)
        normal-published-stages = Stages.initialized-published {c = initialCM} {g = L.settings} {start = initial} {actions = normalPrefix3} {current = normalPublished} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-normal-physical3 normal-published-phase
        error-pending-stages : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Backing.History initial errorReturned (ident 50) cause)
        error-pending-stages = Stages.initialized-pending {c = initialCM} {g = L.settings} {start = initial} {actions = errorPrefix1} {current = errorReturned} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-error-physical1 error-returned-phase
        error-removed-stages : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Stages.Removal initial errorRemoved (ident 50) cause)
        error-removed-stages = Stages.initialized-removed {c = initialCM} {g = L.settings} {start = initial} {actions = errorPrefix2} {current = errorRemoved} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-error-physical2 error-removed-phase
        error-published-stages : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Stages.Publication initial errorPublished (ident 50) cause)
        error-published-stages = Stages.initialized-published {c = initialCM} {g = L.settings} {start = initial} {actions = errorPrefix3} {current = errorPublished} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-error-physical3 error-published-phase
        initialized-gapped-publication : V.Runs initial (normalPrefix1 ++ gappedActions) gap5
        initialized-gapped-publication = Facts.append-protocols {s = initial} {as = normalPrefix1} {t = normalReturned} {bs = gappedActions} {u = gap5}
          initialized-normal-physical1 (V.more {s = normalReturned} {t = gap1} {u = gap5} {a = gapBeforeRemoval} gapEdge1 (V.more {s = gap1} {t = gap2} {u = gap5} {a = removeMonitor} gapEdge2 (V.more {s = gap2} {t = gap3} {u = gap5} {a = gapBeforePublication} gapEdge3 (V.more {s = gap3} {t = gap4} {u = gap5} {a = publishMonitor} gapEdge4 (V.more {s = gap4} {t = gap5} {u = gap5} {a = gapAfterPublication} gapEdge5 (V.stop {s = gap5}))))))
        gapped-publication-stages : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.normalExit × Stages.Publication initial gap5 (ident 50) cause)
        gapped-publication-stages = Stages.initialized-published {c = initialCM} {g = L.settings} {start = initial} {actions = normalPrefix1 ++ gappedActions} {current = gap5} {tid = ident 50} {ex = PS.Pool.normalExit}
          initializer initialized-gapped-publication gap5-phase

    open Proofs public

  module MonitorCancellationChecks where
    open import Data.List using (take; drop)
    open import Data.List.Properties using (++-assoc)
    open import Relation.Binary.PropositionalEquality using (subst; sym)
    import ConnectionManagement.Properties.ServerPeersMonitorReturns as MonitorReturns
    private
      module Monitor = MonitorReturns I.bearerClosed Prior.classify
      module Monitors = Monitor.Frontend capability
      module D = Reactivation.Shutdown
    cancelPrefix cancelSuffix : List V.Event
    cancelPrefix = D.livePrefixActions ++ take 27 D.peerCloseActions
    cancelSuffix = drop 30 D.peerCloseActions
    -- Reuse the earlier initialized cancellation trace, including the separate
    -- registry/result steps and the later callback exit. No new runtime driver.
    trace-shape : (D.livePrefixActions ++ D.peerCloseActions) ≡
      (cancelPrefix ++ (Monitors.event Monitor.cancelled (ident 50) ∷
        peerStep (PS.deregisterMonitor (ident 50)) ∷ peerStep (PS.publishMonitorResult (ident 50)) ∷ cancelSuffix))
    trace-shape = sym (++-assoc D.livePrefixActions (take 27 D.peerCloseActions)
      (Monitors.event Monitor.cancelled (ident 50) ∷ peerStep (PS.deregisterMonitor (ident 50)) ∷
        peerStep (PS.publishMonitorResult (ident 50)) ∷ cancelSuffix))
    abstract
      initialized-cancelled-publication : Monitors.Published initial D.callbackExited (ident 50) Monitor.cancelled
      initialized-cancelled-publication = Monitors.initialized-lifecycle
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial} {current = D.callbackExited}
        Monitor.cancelled (ident 50) cancelPrefix cancelSuffix initializer
        (subst (λ actions → V.Runs initial actions D.callbackExited) trace-shape D.initialized-peer-close)
    cancelled-is-not-normal-return : V.advance (Monitors.event Monitor.normal (ident 50))
      (at Reactivation.secondRegistered D.peerMonDelivered Reactivation.secondFreeFront) ≡ nothing
    cancelled-is-not-normal-return = refl
    cancelled-is-not-error-return : V.advance (Monitors.event Monitor.exceptional (ident 50))
      (at Reactivation.secondRegistered D.peerMonDelivered Reactivation.secondFreeFront) ≡ nothing
    cancelled-is-not-error-return = refl
    no-Async-at-unwind : V.advance (peerStep (PS.publishMonitorResult (ident 50)))
      (at Reactivation.secondRegistered D.peerMonUnwound Reactivation.secondFreeFront) ≡ nothing
    no-Async-at-unwind = refl

  module MonitorTerminalCancellationChecks where
    open import Data.Product using (Σ; _×_)
    import ConnectionManagement.Properties.ServerPeersMonitorReturns as MonitorReturns
    import ConnectionManagement.Properties.ServerPeersMonitorBacking as MonitorBacking
    import ConnectionManagement.Properties.ServerPeersMonitorStages as MonitorStages
    private
      module Monitor = MonitorReturns I.bearerClosed Prior.classify
      module Backing = MonitorBacking.Frontend I.bearerClosed Prior.classify capability
      module Stages = MonitorStages.Frontend I.bearerClosed Prior.classify capability
      module D = Reactivation.Shutdown
    cancelled-terminal-phase : lookup (ident 50) (PS.Pool.handles (Backing.pool D.callbackExited)) ≡ just (PS.Pool.resultAvailable PS.Pool.cancelledExit)
    cancelled-terminal-phase = refl
    abstract
      initialized-cancelled-backing : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.cancelledExit × Backing.History initial D.callbackExited (ident 50) cause)
      initialized-cancelled-backing = Backing.initialized-published
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial}
        {actions = D.livePrefixActions ++ D.peerCloseActions} {current = D.callbackExited} {tid = ident 50} {ex = PS.Pool.cancelledExit}
        initializer D.initialized-peer-close cancelled-terminal-phase
      initialized-cancelled-history : Backing.History initial D.callbackExited (ident 50) Monitor.cancelled
      initialized-cancelled-history = Backing.cancelled-history initialized-cancelled-backing
      initialized-cancelled-stages : Σ Monitor.Kind (λ cause → Monitor.exit cause ≡ PS.Pool.cancelledExit × Stages.Publication initial D.callbackExited (ident 50) cause)
      initialized-cancelled-stages = Stages.initialized-published
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial}
        {actions = D.livePrefixActions ++ D.peerCloseActions} {current = D.callbackExited} {tid = ident 50} {ex = PS.Pool.cancelledExit}
        initializer D.initialized-peer-close cancelled-terminal-phase
      initialized-cancelled-publication-history : Stages.Publication initial D.callbackExited (ident 50) Monitor.cancelled
      initialized-cancelled-publication-history = Stages.cancelled-publication initialized-cancelled-stages


  module MonitorJoinChecks where
    open import Data.List using (take)
    open import Data.List.Membership.Propositional using (_∈_)
    open import Relation.Binary.PropositionalEquality using (subst)
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
    import ConnectionManagement.Properties.ServerPeersMonitorStages as MonitorStages
    import ConnectionManagement.Properties.ServerPeersMonitorReturns as MonitorReturns
    private
      module D = Reactivation.Shutdown
      module Jn = MonitorJoins I.bearerClosed Prior.classify
      module Joins = Jn.Frontend capability
      module Stages = MonitorStages.Frontend I.bearerClosed Prior.classify capability
      module Monitor = MonitorReturns I.bearerClosed Prior.classify
    before after : V.Runtime
    before = at Reactivation.secondRegistered D.peerMonPublished Reactivation.secondFreeFront
    after = at Reactivation.secondRegistered D.peerMonJoined Reactivation.secondFreeFront
    abstract
      initialized-join : Joins.Joined initial before after
      initialized-join = Joins.initialized-join
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial}
        {actions = D.livePrefixActions ++ take 30 D.peerCloseActions} {before = before} {after = after}
        initializer D.initialized-before-monitor-join D.peerCloseEdge31
      exact-captured-ID : Jn.Cursor.Join.current (Joins.Joined.shape initialized-join) ≡ ident 50
      exact-captured-ID = Joins.observed-id initialized-join refl
      captured-membership : ident 50 ∈ PS.Pool.snapshot (Joins.pool before)
      captured-membership = subst (_∈ PS.Pool.snapshot (Joins.pool before)) exact-captured-ID (Joins.Joined.captured initialized-join)
      cancelled-publication : Stages.Publication initial before (ident 50) Monitor.cancelled
      cancelled-publication = Stages.cancelled-publication
        (Joins.observed-publication initialized-join (ident 50) PS.Pool.cancelledExit exact-captured-ID refl)
    snapshot-retained : PS.Pool.snapshot (Joins.pool after) ≡ (ident 50 ∷ [])
    snapshot-retained = refl
    joined-in-order : PS.Pool.joined (Joins.pool after) ≡ (ident 50 ∷ [])
    joined-in-order = refl
    remaining-consumed : PS.Pool.remaining (Joins.pool after) ≡ []
    remaining-consumed = refl
    no-join-before-removal : V.advance Joins.event
      (at Reactivation.secondRegistered D.peerMonUnwound Reactivation.secondFreeFront) ≡ nothing
    no-join-before-removal = refl
    no-join-before-publication : V.advance Joins.event
      (at Reactivation.secondRegistered D.peerMonRemoved Reactivation.secondFreeFront) ≡ nothing
    no-join-before-publication = refl

  -- Primitive races exercise both ordinary/error returns without claiming a
  -- second full frontend shutdown witness. Both payloads precede cancellation.
  module MonitorJoinRace (result : Maybe ErrorId) where
    open import Data.List.Membership.Propositional using (_∈_)
    import Data.List.Relation.Unary.Any
    import ConnectionManagement.Properties.JobPoolJoinOrder as JoinOrder
    private
      module Q = PS.Pool
      module Order = JoinOrder (Maybe ErrorId) false
    c0 c1 c2 c3 c4 c5 c6 c7 c8 : Q.State
    c0 = Q.initial
    c1 = record c0 { handles = put (ident 50) Q.bodyRunning [] }
    c2 = record c1 { registered = ident 50 ∷ [] }
    c3 = record c2 { phase = Q.closing; snapshot = ident 50 ∷ []; remaining = ident 50 ∷ [] }
    c4 = record c3 { phase = Q.cancelPending (ident 50) }
    c5 = record c4 { handles = put (ident 50) (Q.deregisterPending Q.normalExit) (Q.handles c4) }
    c6 = record c5 { handles = put (ident 50) (Q.deregistered Q.normalExit) (Q.handles c5); registered = [] }
    c7 = record c6 { handles = put (ident 50) (Q.resultAvailable Q.normalExit) (Q.handles c6) }
    c8 = record c7 { phase = Q.closing; remaining = []; joined = ident 50 ∷ [] }
    e1 : Q.step (Q.forkConcurrent (ident 50)) c0 ≡ just c1
    e1 = refl
    e2 : Q.step (Q.registerConcurrent (ident 50)) c1 ≡ just c2
    e2 = refl
    e3 : Q.step (Q.beginClose (ident 50 ∷ [])) c2 ≡ just c3
    e3 = refl
    e4 : Q.step Q.requestCancel c3 ≡ just c4
    e4 = refl
    e5 : Q.step (Q.bodyReturnedWith (ident 50) result) c4 ≡ just c5
    e5 = refl
    e6 : Q.step (Q.deregister (ident 50)) c5 ≡ just c6
    e6 = refl
    e7 : Q.step (Q.publishAsyncResult (ident 50)) c6 ≡ just c7
    e7 = refl
    e8 : Q.step Q.join c7 ≡ just c8
    e8 = refl
    actions : List Q.Action
    actions = Q.forkConcurrent (ident 50) ∷ Q.registerConcurrent (ident 50) ∷
      Q.beginClose (ident 50 ∷ []) ∷ Q.requestCancel ∷ Q.bodyReturnedWith (ident 50) result ∷
      Q.deregister (ident 50) ∷ Q.publishAsyncResult (ident 50) ∷ []
    path : Q.Executes Q.initial actions c7
    path = Q.next {s = c0} {s₁ = c1} {a = Q.forkConcurrent (ident 50)} e1
      (Q.next {s = c1} {s₁ = c2} {a = Q.registerConcurrent (ident 50)} e2
      (Q.next {s = c2} {s₁ = c3} {a = Q.beginClose (ident 50 ∷ [])} e3
      (Q.next {s = c3} {s₁ = c4} {a = Q.requestCancel} e4
      (Q.next {s = c4} {s₁ = c5} {a = Q.bodyReturnedWith (ident 50) result} e5
      (Q.next {s = c5} {s₁ = c6} {a = Q.deregister (ident 50)} e6
      (Q.next {s = c6} {s₁ = c7} {a = Q.publishAsyncResult (ident 50)} e7 Q.done))))))
    partition : Order.Partition c7
    partition = Order.from-initial path
    join-shape : Order.Join c7 c8
    join-shape = Order.inspect-join c7 e8
    captured : Order.Join.current join-shape ∈ Q.snapshot c7
    captured = Order.captured partition join-shape
    no-join-running : Q.step Q.join c4 ≡ nothing
    no-join-running = refl
    no-join-pending : Q.step Q.join c5 ≡ nothing
    no-join-pending = refl
    no-join-removed : Q.step Q.join c6 ≡ nothing
    no-join-removed = refl
    return-prevents-cancel-delivery : Q.step Q.deliverCancel c5 ≡ nothing
    return-prevents-cancel-delivery = refl
    wrong-head-rejected : Q.step Q.join (record c7 { remaining = ident 51 ∷ [] }) ≡ nothing
    wrong-head-rejected = refl
    -- A result already present when cancellation is requested uses joinPending.
    ready : Q.State
    ready = record c7 { phase = Q.closing }
    readyWaiting : Q.State
    readyWaiting = record c7 { phase = Q.joinPending (ident 50) }
    ready-request : Q.step Q.requestCancel ready ≡ just readyWaiting
    ready-request = refl
    ready-join : Q.step Q.join readyWaiting ≡ just c8
    ready-join = refl
    ready-shape : Order.Join readyWaiting c8
    ready-shape = Order.inspect-join readyWaiting ready-join
    -- The already-available case also has an enabled execution from initial.
    returnedEarly removedEarly : Q.State
    returnedEarly = record c3 { handles = put (ident 50) (Q.deregisterPending Q.normalExit) (Q.handles c3) }
    removedEarly = record returnedEarly { handles = put (ident 50) (Q.deregistered Q.normalExit) (Q.handles returnedEarly); registered = [] }
    returned-before-request : Q.step (Q.bodyReturnedWith (ident 50) result) c3 ≡ just returnedEarly
    returned-before-request = refl
    removed-before-request : Q.step (Q.deregister (ident 50)) returnedEarly ≡ just removedEarly
    removed-before-request = refl
    published-before-request : Q.step (Q.publishAsyncResult (ident 50)) removedEarly ≡ just ready
    published-before-request = refl
    readyActions : List Q.Action
    readyActions = Q.forkConcurrent (ident 50) ∷ Q.registerConcurrent (ident 50) ∷
      Q.beginClose (ident 50 ∷ []) ∷ Q.bodyReturnedWith (ident 50) result ∷
      Q.deregister (ident 50) ∷ Q.publishAsyncResult (ident 50) ∷ Q.requestCancel ∷ []
    ready-path : Q.Executes Q.initial readyActions readyWaiting
    ready-path = Q.next {s = c0} {s₁ = c1} {a = Q.forkConcurrent (ident 50)} e1
      (Q.next {s = c1} {s₁ = c2} {a = Q.registerConcurrent (ident 50)} e2
      (Q.next {s = c2} {s₁ = c3} {a = Q.beginClose (ident 50 ∷ [])} e3
      (Q.next {s = c3} {s₁ = returnedEarly} {a = Q.bodyReturnedWith (ident 50) result} returned-before-request
      (Q.next {s = returnedEarly} {s₁ = removedEarly} {a = Q.deregister (ident 50)} removed-before-request
      (Q.next {s = removedEarly} {s₁ = ready} {a = Q.publishAsyncResult (ident 50)} published-before-request
      (Q.next {s = ready} {s₁ = readyWaiting} {a = Q.requestCancel} ready-request Q.done))))))
    ready-partition : Order.Partition readyWaiting
    ready-partition = Order.from-initial ready-path
    ready-captured : Order.Join.current ready-shape ∈ Q.snapshot readyWaiting
    ready-captured = Order.captured ready-partition ready-shape

    -- Closing the race keeps the initialized snapshot/order and terminal result.
    import ConnectionManagement.Properties.JobPoolCloseKernel as CloseKernel
    private module Closed = CloseKernel (Maybe ErrorId) false
    finishedPool : Q.State
    finishedPool = record c8 { phase = Q.closedPool }
    finish-pool : Q.step Q.finishClose c8 ≡ just finishedPool
    finish-pool = refl
    finish-path : ∀ {start as} → Q.Executes start as c7 →
      Q.Executes start (as ++ (Q.join ∷ Q.finishClose ∷ [])) finishedPool
    finish-path Q.done = Q.next {a = Q.join} e8 (Q.next {a = Q.finishClose} finish-pool Q.done)
    finish-path (Q.next advanced rest) = Q.next advanced (finish-path rest)
    closed-path : Q.Executes Q.initial (actions ++ (Q.join ∷ Q.finishClose ∷ [])) finishedPool
    closed-path = finish-path path
    closed-order : Q.snapshot finishedPool ≡ Q.joined finishedPool
    closed-order = Order.from-initial closed-path
    closed-result : Closed.Terminal finishedPool (ident 50)
    closed-result = Closed.from-initial closed-path refl (ident 50) (Data.List.Relation.Unary.Any.here refl)
    cannot-finish-before-join : Q.step Q.finishClose c7 ≡ nothing
    cannot-finish-before-join = refl

  module MonitorJoinNormalRace = MonitorJoinRace nothing
  module MonitorJoinErrorRace = MonitorJoinRace (just (errorId 170))


  module MonitorClosedSnapshotChecks where
    open import Data.List.Relation.Unary.Any using (here; there)
    open import Data.List.Membership.Propositional using (_∈_)
    open import Data.Empty using (⊥)
    import Data.List.Relation.Unary.All as All
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
    import ConnectionManagement.Properties.ServerPeersMonitorReturns as MonitorReturns
    import ConnectionManagement.Properties.ServerPeersMonitorBacking as MonitorBacking
    import ConnectionManagement.Properties.ServerPeersMonitorStages as MonitorStages
    private
      module D = Reactivation.Shutdown
      module Joins = MonitorJoins.Frontend I.bearerClosed Prior.classify capability
      module Monitor = MonitorReturns I.bearerClosed Prior.classify
      module Backing = MonitorBacking.Frontend I.bearerClosed Prior.classify capability
      module Stages = MonitorStages.Frontend I.bearerClosed Prior.classify capability
    abstract
      before-callback : Joins.ClosedSnapshot initial D.innerClosed
      before-callback = Joins.initialized-closed
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial}
        {actions = D.livePrefixActions ++ D.peerBeforeCallbackActions} {current = D.innerClosed}
        initializer D.restarted-before-callback refl
      after-callback : Joins.ClosedSnapshot initial D.callbackExited
      after-callback = Joins.initialized-closed
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial}
        {actions = D.livePrefixActions ++ D.peerCloseActions} {current = D.callbackExited}
        initializer D.initialized-peer-close refl
      exact-joined-order : PS.Pool.snapshot (Joins.pool D.innerClosed) ≡ PS.Pool.joined (Joins.pool D.innerClosed)
      exact-joined-order = Joins.ClosedSnapshot.order before-callback
      ordered-histories : All.All (Joins.SnapshotLifecycle initial D.innerClosed) (ident 50 ∷ [])
      ordered-histories = Joins.ClosedSnapshot.histories before-callback
      captured-history : Joins.SnapshotLifecycle initial D.innerClosed (ident 50)
      captured-history = Joins.captured-lifecycle before-callback (here refl)
      joined-history : Joins.SnapshotLifecycle initial D.callbackExited (ident 50)
      joined-history = Joins.joined-lifecycle after-callback (here refl)
      cancelled-publication : Stages.Publication initial D.innerClosed (ident 50) Monitor.cancelled
      cancelled-publication = Joins.cancelled-lifecycle captured-history refl
      cancelled-after-callback : Stages.Publication initial D.callbackExited (ident 50) Monitor.cancelled
      cancelled-after-callback = Joins.cancelled-lifecycle joined-history refl
      original-exit-retained : Backing.History initial D.callbackExited (ident 50) Monitor.cancelled
      original-exit-retained = Stages.publication-exit cancelled-after-callback
    no-uncaptured-handle : ident 51 ∈ PS.Pool.snapshot (Joins.pool D.innerClosed) → ⊥
    no-uncaptured-handle (here ())
    no-uncaptured-handle (there ())
    no-finish-with-published-unjoined-head : V.advance (peerStep PS.finishMonitorClose)
      MonitorJoinChecks.before ≡ nothing
    no-finish-with-published-unjoined-head = refl
    callback-still-running-at-pool-close : S.stage (E.base (K.server (V.base D.innerClosed))) ≡ S.serving
    callback-still-running-at-pool-close = refl

  module MonitorClosedEmptyAndForgedChecks where
    import Data.List.Membership.Propositional
    open import Data.Empty using (⊥)
    open import Data.Product using (Σ)
    import ConnectionManagement.Properties.JobPoolJoinOrder as JoinOrder
    import ConnectionManagement.Properties.JobPoolCloseKernel as CloseKernel
    private
      module Q = PS.Pool
      module Order = JoinOrder (Maybe ErrorId) false
      module Closed = CloseKernel (Maybe ErrorId) false
    emptyClosing emptyClosed : Q.State
    emptyClosing = record Q.initial { phase = Q.closing }
    emptyClosed = record emptyClosing { phase = Q.closedPool }
    empty-path : Q.Executes Q.initial (Q.beginClose [] ∷ Q.finishClose ∷ []) emptyClosed
    empty-path = Q.next {a = Q.beginClose []} refl (Q.next {a = Q.finishClose} refl Q.done)
    empty-order : Q.snapshot emptyClosed ≡ Q.joined emptyClosed
    empty-order = Order.from-initial empty-path
    empty-results : ∀ tid → tid Data.List.Membership.Propositional.∈ Q.snapshot emptyClosed → Closed.Terminal emptyClosed tid
    empty-results = Closed.from-initial empty-path refl
    -- A forged closed bit alone supplies neither order nor a terminal handle.
    forged : Q.State
    forged = record Q.initial { phase = Q.closedPool; snapshot = ident 50 ∷ [] }
    forged-closed : Q.phase forged ≡ Q.closedPool
    forged-closed = refl
    forged-order-fails : Q.snapshot forged ≡ Q.joined forged → ⊥
    forged-order-fails ()
    forged-result-missing : Closed.Terminal forged (ident 50) → ⊥
    forged-result-missing (ex , ())

  module CallbackLifecycleChecks where
    open import Relation.Binary.PropositionalEquality using (cong)
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
    import ConnectionManagement.Properties.ServerPeersMonitorReturns as MonitorReturns
    import ConnectionManagement.Properties.ServerPeersMonitorStages as MonitorStages
    private
      module D = Reactivation.Shutdown
      module Joins = MonitorJoins.Frontend I.bearerClosed Prior.classify capability
      module Monitor = MonitorReturns I.bearerClosed Prior.classify
      module Stages = MonitorStages.Frontend I.bearerClosed Prior.classify capability
    abstract
      first-exit : Joins.CallbackExit initial closed callbackReturned
      first-exit = Joins.initialized-callback
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial}
        {actions = allProtocolActions ++ beforeCallbackActions} {before = closed} {after = callbackReturned}
        initializer initialized-before-callback close33
      restarted-exit : Joins.CallbackExit initial D.innerClosed D.callbackExited
      restarted-exit = Joins.initialized-callback
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial}
        {actions = D.livePrefixActions ++ D.peerBeforeCallbackActions} {before = D.innerClosed} {after = D.callbackExited}
        initializer D.restarted-before-callback D.peerCloseEdge33
      first-components : BFacts.Certificates (V.base closed)
      first-components = Joins.CallbackExit.components first-exit
      first-components-after : BFacts.Certificates (V.base callbackReturned)
      first-components-after = Joins.callback-components-after first-exit
      restarted-components-after : BFacts.Certificates (V.base D.callbackExited)
      restarted-components-after = Joins.callback-components-after restarted-exit
      first-monitor-after : Joins.SnapshotLifecycle initial callbackReturned (ident 50)
      first-monitor-after = Joins.joined-lifecycle (Joins.callback-monitors-after first-exit) (here refl)
      restarted-monitor-before : Joins.SnapshotLifecycle initial D.innerClosed (ident 50)
      restarted-monitor-before = Joins.captured-lifecycle (Joins.CallbackExit.monitors restarted-exit) (here refl)
      restarted-monitor-after : Joins.SnapshotLifecycle initial D.callbackExited (ident 50)
      restarted-monitor-after = Joins.joined-lifecycle (Joins.callback-monitors-after restarted-exit) (here refl)
      first-cancelled-history : Stages.Publication initial callbackReturned (ident 50) Monitor.cancelled
      first-cancelled-history = Joins.cancelled-lifecycle first-monitor-after refl
      restarted-cancelled-history : Stages.Publication initial D.callbackExited (ident 50) Monitor.cancelled
      restarted-cancelled-history = Joins.cancelled-lifecycle restarted-monitor-after refl
      actual-shared-step : K.step Joins.callback-action (V.base D.innerClosed) ≡ just (V.base D.callbackExited)
      actual-shared-step = Joins.CallbackExit.sharedStep restarted-exit
      retained-snapshot : PS.Pool.snapshot (Joins.pool D.callbackExited) ≡ PS.Pool.snapshot (Joins.pool D.innerClosed)
      retained-snapshot = cong PS.Pool.snapshot (Joins.callback-pool-same restarted-exit)
      retained-joined-order : PS.Pool.joined (Joins.pool D.callbackExited) ≡ PS.Pool.joined (Joins.pool D.innerClosed)
      retained-joined-order = cong PS.Pool.joined (Joins.callback-pool-same restarted-exit)
      -- The extension keeps this same cause while extending its actual suffix.
      retained-cause : ∀ tid (w : Joins.SnapshotLifecycle initial D.innerClosed tid) →
        Joins.SnapshotLifecycle.kind (Joins.extend-lifecycle
          (V.more {a = Joins.callback-event} D.peerCloseEdge33 V.stop) (Joins.callback-pool-same restarted-exit) w) ≡
        Joins.SnapshotLifecycle.kind w
      retained-cause tid w = refl
    no-return-before-peer-close : V.advance Joins.callback-event D.liveRestart ≡ nothing
    no-return-before-peer-close = refl
    no-return-before-monitor-join : V.advance Joins.callback-event MonitorJoinChecks.before ≡ nothing
    no-return-before-monitor-join = refl
    no-return-before-monitor-finish : V.advance Joins.callback-event MonitorJoinChecks.after ≡ nothing
    no-return-before-monitor-finish = refl
    no-repeated-return : V.advance Joins.callback-event D.callbackExited ≡ nothing
    no-repeated-return = refl
    callback-is-not-server-return : S.stage (E.base (K.server (V.base D.callbackExited))) ≡ S.actionBodyExited
    callback-is-not-server-return = refl
    first-handler-remains-open : Pool.phase (P.poolAt A.child₀ (V.physical (V.base callbackReturned))) ≡ Pool.openPool
    first-handler-remains-open = physical-handler-pool-still-open
    first-admissions-incomplete : S.allResults (S.workers (E.base (K.server (V.base callbackReturned)))) ≡ false
    first-admissions-incomplete = raw-admissions-still-incomplete


  module ServerCMEntryLifecycleChecks where
    open import Relation.Binary.PropositionalEquality using (cong)
    import Data.List.Relation.Unary.All as All
    import ConnectionManagement.Rules.CMShutdown as Close
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
    import ConnectionManagement.Properties.ServerPeersMonitorReturns as MonitorReturns
    import ConnectionManagement.Properties.ServerPeersMonitorStages as MonitorStages
    import ConnectionManagement.Properties.ServerPeersMonitorBacking as MonitorBacking
    private
      module D = Reactivation.Shutdown
      module SC = StartTrace.ScopedCM
      module Joins = MonitorJoins.Frontend I.bearerClosed Prior.classify capability
      module Monitor = MonitorReturns I.bearerClosed Prior.classify
      module Stages = MonitorStages.Frontend I.bearerClosed Prior.classify capability
      module Backing = MonitorBacking.Frontend I.bearerClosed Prior.classify capability
    cleanupActions : List E.Action
    cleanupActions = (E.run (S.scope S.publishActionResult)) ∷ (E.run (S.scope S.selectActionWinner)) ∷ (E.run (S.scope S.requestAcceptCancel)) ∷ (E.run (S.scope S.deliverAcceptAtWait)) ∷ (E.run (S.scope S.closeListener)) ∷ (E.run (S.scope S.publishAcceptResult)) ∷ (E.run (S.scope S.joinAccept)) ∷ (E.run (S.scope S.traceStopped)) ∷ (E.run (S.scope S.cancelJoinReturnedAction)) ∷ (E.run (S.scope S.requestIGCancel)) ∷ (E.receive E.loopBoundary SC.igError) ∷ (E.run (S.scope S.deactivateIG)) ∷ (E.run (S.scope S.flushIG)) ∷ E.captureSnapshot ∷ E.invokeFinal ∷ E.returnFinal ∷ E.finishFinal ∷ (E.run (S.scope S.publishIGResult)) ∷ (E.run (S.scope S.joinIG)) ∷ []
    abstract
      actual-server-suffix : Joins.ServerRuns D.callbackExited (cleanupActions ++ (E.run (S.scope S.beginCM) ∷ [])) D.cmEntry
      actual-server-suffix = Joins.server-runs-from
        {s = D.callbackExited} {actions = cleanupActions ++ (E.run (S.scope S.beginCM) ∷ [])} {t = D.cmEntry}
        D.server-close-path
      entry-certificate : Joins.CMEntry initial D.cmEntry
      entry-certificate = Joins.initialized-cm-entry-run
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial}
        {prefix = D.livePrefixActions ++ D.peerBeforeCallbackActions} {callbackBefore = D.innerClosed}
        {callbackAfter = D.callbackExited} {actions = cleanupActions} {current = D.cmEntry}
        initializer D.restarted-before-callback D.peerCloseEdge33 actual-server-suffix
      actual-CM-stage : S.stage (E.base (K.server (V.base D.cmEntry))) ≡ S.closingCM
      actual-CM-stage = Joins.CMEntry.atCM entry-certificate
      retained-context : K.context (V.base D.cmEntry) ≡ K.context (V.base D.callbackExited)
      retained-context = Joins.server-context actual-server-suffix
      recorded-context : K.context (V.base D.cmEntry) ≡ K.context (V.base (Joins.CMEntry.callbackAfter entry-certificate))
      recorded-context = Joins.cm-context-same entry-certificate
      all-components : BFacts.Certificates (V.base D.cmEntry)
      all-components = Joins.cm-components entry-certificate
      closed-monitors : Joins.ClosedSnapshot initial D.cmEntry
      closed-monitors = Joins.cm-monitors entry-certificate
      ordered-histories : All.All (Joins.SnapshotLifecycle initial D.cmEntry) (ident 50 ∷ [])
      ordered-histories = Joins.ClosedSnapshot.histories closed-monitors
      captured-history : Joins.SnapshotLifecycle initial D.cmEntry (ident 50)
      captured-history = Joins.joined-lifecycle closed-monitors (here refl)
      cancelled-publication : Stages.Publication initial D.cmEntry (ident 50) Monitor.cancelled
      cancelled-publication = Joins.cancelled-lifecycle captured-history refl
      original-exit : Backing.History initial D.cmEntry (ident 50) Monitor.cancelled
      original-exit = Stages.publication-exit cancelled-publication
      retained-cause : ∀ tid (w : Joins.SnapshotLifecycle initial D.callbackExited tid) →
        Joins.SnapshotLifecycle.kind (Joins.extend-lifecycle (Joins.server-runs actual-server-suffix)
          (cong C.monitorPool retained-context) w) ≡ Joins.SnapshotLifecycle.kind w
      retained-cause tid w = refl
    no-CM-entry-before-callback : V.advance Joins.cm-event D.innerClosed ≡ nothing
    no-CM-entry-before-callback = refl
    no-CM-entry-immediately-after-callback : V.advance Joins.cm-event D.callbackExited ≡ nothing
    no-CM-entry-immediately-after-callback = refl
    no-CM-entry-before-IG-join : V.advance Joins.cm-event
      (D.stageScene S.igResultAvailable false SC.publishedIG D.exitedModel D.peerFinished Reactivation.secondFreeFront) ≡ nothing
    no-CM-entry-before-IG-join = refl
    no-repeated-CM-entry : V.advance Joins.cm-event D.cmEntry ≡ nothing
    no-repeated-CM-entry = refl
    no-Server-finish-at-CM-entry : V.advance (SC.serverEvent S.finishServer) D.cmEntry ≡ nothing
    no-Server-finish-at-CM-entry = refl
    CM-has-not-captured-snapshot : Close.phase (N.W.shutdown (D.handlerStateOf D.cmEntry)) ≡ Close.initial
    CM-has-not-captured-snapshot = refl
    current-handler-body-still-running : lookup (ident 21) (Pool.handles (P.poolAt A.child₀ (V.physical (V.base D.cmEntry)))) ≡ just Pool.bodyRunning
    current-handler-body-still-running = D.body-live-at-cm-entry
    old-body-still-unpublished : lookup jid (Pool.handles (P.poolAt A.child₀ (V.physical (V.base D.cmEntry)))) ≡ just Pool.bodyRunning
    old-body-still-unpublished = D.old-body-unpublished-at-cm-entry


  module CMResultLifecycleChecks where
    open import Data.List using (take)
    open import Relation.Binary.PropositionalEquality using (sym; trans)
    import ConnectionManagement.Rules.CMShutdown as Close
    import ConnectionManagement.Rules.Cleanup as Cleanup
    import ConnectionManagement.Properties.MuxHandlerExit as HandlerFacts
    import ConnectionManagement.Properties.CMShutdown as CloseFacts
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
    import ConnectionManagement.Properties.ServerPeersMonitorReturns as MonitorReturns
    import ConnectionManagement.Properties.ServerPeersMonitorStages as MonitorStages
    private
      module D = Reactivation.Shutdown
      module SC = StartTrace.ScopedCM
      module W = N.W
      module Group = N.G
      module PhysicalProofs = HandlerFacts I.bearerClosed using (Publication; PhysicalWait)
      module Joins = MonitorJoins.Frontend I.bearerClosed Prior.classify capability
      module Monitor = MonitorReturns I.bearerClosed Prior.classify
      module Stages = MonitorStages.Frontend I.bearerClosed Prior.classify capability
    protocol-action : P.Action → E.Action
    protocol-action a = Joins.handler-action (W.run (Group.run (N.M.run a)))
    receiptActions poolActions catchActions finalizerActions : List E.Action
    receiptActions = (Joins.handler-action (W.shutdownStep Close.captureSnapshot)) ∷ (Joins.handler-action (W.shutdownStep Close.readEntry)) ∷ (Joins.handler-action (W.shutdownStep Close.requestCancellation)) ∷ (Joins.handler-action (W.deliverShutdownMux D.shutdownError)) ∷ (Joins.handler-action (W.shutdownStep Close.finishTraversal)) ∷ []
    poolActions = (Joins.handler-action (W.run (Group.beginWholeClose A.child₀ D.capturedPhysicalOrder))) ∷ (Joins.handler-action (W.run (Group.requestWholeCancel A.child₀))) ∷ (Joins.handler-action (W.run (Group.deliverWhole A.child₀))) ∷ (Joins.handler-action (W.run (Group.finishChildUnwind (ident 21)))) ∷ (protocol-action (P.deregisterProtocol (ident 21))) ∷ (protocol-action (P.asyncProtocolResult (ident 21))) ∷ (Joins.handler-action (W.run (Group.joinWhole A.child₀))) ∷ (Joins.handler-action (W.run (Group.requestWholeCancel A.child₀))) ∷ (Joins.handler-action (W.run (Group.deliverWhole A.child₀))) ∷ (Joins.handler-action (W.run (Group.finishChildUnwind (ident 20)))) ∷ (protocol-action (P.deregisterProtocol (ident 20))) ∷ (protocol-action (P.asyncProtocolResult (ident 20))) ∷ (Joins.handler-action (W.run (Group.joinWhole A.child₀))) ∷ (Joins.handler-action (W.run (Group.requestWholeCancel A.child₀))) ∷ (Joins.handler-action (W.run (Group.deliverWhole A.child₀))) ∷ (Joins.handler-action (W.run (Group.finishChildUnwind (ident 1)))) ∷ (protocol-action (P.deregisterInfra A.child₀ Types.demuxer)) ∷ (protocol-action (P.asyncInfraResult A.child₀ Types.demuxer)) ∷ (Joins.handler-action (W.run (Group.joinWhole A.child₀))) ∷ (Joins.handler-action (W.run (Group.requestWholeCancel A.child₀))) ∷ (Joins.handler-action (W.run (Group.deliverWhole A.child₀))) ∷ (Joins.handler-action (W.run (Group.finishChildUnwind (ident 0)))) ∷ (protocol-action (P.deregisterInfra A.child₀ Types.muxer)) ∷ (protocol-action (P.asyncInfraResult A.child₀ Types.muxer)) ∷ (Joins.handler-action (W.run (Group.joinWhole A.child₀))) ∷ (Joins.handler-action (W.run (Group.finishWholeClose A.child₀))) ∷ []
    catchActions = (Joins.handler-action (W.run (Group.writeAsyncFailure A.child₀))) ∷ (Joins.handler-action (W.run (Group.beginAsyncDead A.child₀))) ∷ (Joins.handler-action (W.run (Group.sampleAsyncTracer A.child₀))) ∷ (Joins.handler-action (W.run (Group.commitAsyncTracer A.child₀))) ∷ (Joins.handler-action (W.run (Group.finishAsyncDead A.child₀))) ∷ []
    finalizerActions = (Joins.handler-action (W.beginExit A.child₀)) ∷ (Joins.handler-action (W.observeBufferReturn A.child₀)) ∷ (Joins.handler-action (W.enterFinalizer A.child₀)) ∷ (Joins.handler-action (W.cleanup A.child₀ Cleanup.takeCleanupMap)) ∷ (Joins.handler-action (W.cleanup A.child₀ Cleanup.selectCleanupEntry)) ∷ (Joins.handler-action (W.cleanup A.child₀ Cleanup.closeHandlerSocket)) ∷ (Joins.handler-action (W.cleanup A.child₀ Cleanup.publishCleanupMap)) ∷ (Joins.handler-action (W.cleanup A.child₀ Cleanup.readCleanupCounters)) ∷ (Joins.handler-action (W.finishCleanup A.child₀)) ∷ (Joins.handler-action (W.publishAsyncResult A.child₀)) ∷ []
    waitPrefix : List E.Action
    waitPrefix = ((receiptActions ++ poolActions) ++ catchActions) ++ finalizerActions
    abstract
      actual-receipt-path : Joins.ServerRuns D.cmEntry receiptActions D.receipt5
      actual-receipt-path = Joins.server-runs-from {s = D.cmEntry} {actions = receiptActions} {t = D.receipt5} D.receipt-path
      actual-pool-path : Joins.ServerRuns D.receipt5 poolActions D.wholePoolClosed
      actual-pool-path = Joins.server-runs-from {s = D.receipt5} {actions = poolActions} {t = D.wholePoolClosed} D.whole-pool-path
      actual-catch-path : Joins.ServerRuns D.wholePoolClosed catchActions D.readyForBuffer
      actual-catch-path = Joins.server-runs-from {s = D.wholePoolClosed} {actions = catchActions} {t = D.readyForBuffer} D.normal-catch-path
      actual-finalizer-path : Joins.ServerRuns D.readyForBuffer finalizerActions D.handler10
      actual-finalizer-path = Joins.server-runs-from {s = D.readyForBuffer} {actions = finalizerActions} {t = D.handler10} D.handler-before-wait
      actual-wait-prefix : Joins.ServerRuns D.cmEntry waitPrefix D.handler10
      actual-wait-prefix = Joins.server-append (Joins.server-append
        (Joins.server-append actual-receipt-path actual-pool-path) actual-catch-path) actual-finalizer-path
      wait-certificate : Joins.CMResultWait initial D.handler10 D.finalCM
      wait-certificate = Joins.initialized-cm-result-wait
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial}
        {prefix = D.livePrefixActions ++ D.peerBeforeCallbackActions} {callbackBefore = D.innerClosed} {callbackAfter = D.callbackExited}
        {entryActions = ServerCMEntryLifecycleChecks.cleanupActions} {entry = D.cmEntry} {before = D.handler10} {actions = waitPrefix} {after = D.finalCM}
        initializer D.restarted-before-callback D.peerCloseEdge33 ServerCMEntryLifecycleChecks.actual-server-suffix actual-wait-prefix D.handlerFinishEdge11
      actual-physical-wait : PhysicalProofs.PhysicalWait (Joins.physical D.handler10) (Joins.physical D.finalCM)
      actual-physical-wait = Joins.CMResultWait.observed wait-certificate
      exact-result-oracle : CloseFacts.available (PhysicalProofs.PhysicalWait.primitive-wait actual-physical-wait) ≡
        (λ worker → W.resultReady worker (Joins.physical D.handler10))
      exact-result-oracle = PhysicalProofs.PhysicalWait.physical-oracle actual-physical-wait
      delivery-receipt : Joins.MuxReceipt D.shutdownError (Joins.physical D.receipt3) (Joins.physical D.receipt4)
      delivery-receipt = Joins.physical-receipt D.shutdownError D.receipt3 D.receiptEdge4
      result-publication : PhysicalProofs.Publication A.child₀ (Joins.physical D.handler9) (Joins.physical D.handler10)
      result-publication = Joins.physical-publication A.child₀ D.handler9 D.handlerFinishEdge10
      receipt-components : BFacts.Certificates (V.base D.receipt5)
      receipt-components = Joins.follow-components ServerCMEntryLifecycleChecks.entry-certificate actual-receipt-path
      final-components : BFacts.Certificates (V.base D.finalCM)
      final-components = Joins.wait-components-after wait-certificate
      final-monitors : Joins.ClosedSnapshot initial D.finalCM
      final-monitors = Joins.wait-monitors-after wait-certificate
      final-monitor-history : Joins.SnapshotLifecycle initial D.finalCM (ident 50)
      final-monitor-history = Joins.joined-lifecycle final-monitors (here refl)
      original-monitor-cause : Stages.Publication initial D.finalCM (ident 50) Monitor.cancelled
      original-monitor-cause = Joins.cancelled-lifecycle final-monitor-history refl
      actual-server-return-path : Joins.ServerRuns D.finalCM (E.run (S.scope S.finishServer) ∷ []) D.returnedServer
      actual-server-return-path = Joins.serverNext {a = E.run (S.scope S.finishServer)} D.handlerFinishEdge12 Joins.serverDone
      return-monitors : Joins.ClosedSnapshot initial D.returnedServer
      return-monitors = Joins.follow-monitors (Joins.CMResultWait.entry wait-certificate)
        (Joins.server-append (Joins.wait-cleanup wait-certificate) actual-server-return-path)
      return-components : BFacts.Certificates (V.base D.returnedServer)
      return-components = Joins.follow-components (Joins.CMResultWait.entry wait-certificate)
        (Joins.server-append (Joins.wait-cleanup wait-certificate) actual-server-return-path)
      return-monitor-cause : Stages.Publication initial D.returnedServer (ident 50) Monitor.cancelled
      return-monitor-cause = Joins.cancelled-lifecycle (Joins.joined-lifecycle return-monitors (here refl)) refl
    same-worker : ∀ {e e′ w w′} → Close.awaitDelivery e w ≡ Close.awaitDelivery e′ w′ → w ≡ w′
    same-worker refl = refl
    abstract
      captured-receipt-worker : Joins.MuxReceipt.worker delivery-receipt ≡ A.child₀
      captured-receipt-worker = same-worker (trans (sym (Joins.MuxReceipt.awaiting delivery-receipt)) refl)
    no-wait-at-receipt : V.advance (SC.coordinatorEvent Close.finishClose) D.receipt5 ≡ nothing
    no-wait-at-receipt = refl
    no-wait-at-pool-close : V.advance (SC.coordinatorEvent Close.finishClose) D.wholePoolClosed ≡ nothing
    no-wait-at-pool-close = refl
    no-wait-after-catch : V.advance (SC.coordinatorEvent Close.finishClose) D.readyForBuffer ≡ nothing
    no-wait-after-catch = refl
    no-wait-before-publication : V.advance (SC.coordinatorEvent Close.finishClose) D.handler9 ≡ nothing
    no-wait-before-publication = D.cm-waits-for-actual-handler-result
    receipt-not-result : W.resultReady A.child₀ (Joins.physical D.receipt4) ≡ false
    receipt-not-result = refl
    cleanup-not-result : W.resultReady A.child₀ (Joins.physical D.handler9) ≡ false
    cleanup-not-result = D.still-no-handler-result-after-cleanup
    actual-handler-result : W.resultOf A.child₀ (Joins.physical D.handler10) ≡ just (W.asyncException D.shutdownError)
    actual-handler-result = refl
    actual-CM-closed : Close.phase (W.shutdown (Joins.physical D.finalCM)) ≡ Close.closed
    actual-CM-closed = refl
    collected-handle : Close.collected (W.shutdown (Joins.physical D.finalCM)) ≡ A.child₀ ∷ []
    collected-handle = refl
    actual-server-return : S.stage (E.base (K.server (V.base D.returnedServer))) ≡ S.serverReturned
    actual-server-return = D.actual-returned-server
    returned-admissions-incomplete : S.allResults (S.workers (E.base (K.server (V.base D.returnedServer)))) ≡ false
    returned-admissions-incomplete = refl


  module RaceLifecycleChecks where
    open import Data.List using (take)
    open import Data.Empty using (⊥)
    open import Relation.Binary.PropositionalEquality using (cong)
    import ConnectionManagement.Rules.CMShutdown as Close
    import ConnectionManagement.Properties.MuxHandlerExit as HandlerFacts
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
    import ConnectionManagement.Properties.ServerPeersMonitorStages as MonitorStages
    import ConnectionManagement.Properties.ServerPeersMonitorReturns as MonitorReturns
    private
      module D = Reactivation.Shutdown
      module PR = D.PublicationRace
      module CC = D.CurrentClean
      module SC = StartTrace.ScopedCM
      module Joins = MonitorJoins.Frontend I.bearerClosed Prior.classify capability
      module PhysicalProofs = HandlerFacts I.bearerClosed using (PhysicalWait)
      module Stages = MonitorStages.Frontend I.bearerClosed Prior.classify capability
      module Monitor = MonitorReturns I.bearerClosed Prior.classify
    racePrefix cleanPrefix : List V.Event
    racePrefix = (((D.receiptActions ++ (shutdownStep (N.G.beginWholeClose A.child₀ D.capturedPhysicalOrder) ∷ [])) ++ PR.raceActions) ++ D.normalCatchActions) ++ take 10 PR.raceFinishActions
    cleanPrefix = ((D.receiptActions ++ (shutdownStep (N.G.beginWholeClose A.child₀ D.capturedPhysicalOrder) ∷ shutdownStep (N.G.requestWholeCancel A.child₀) ∷ [])) ++
      (physicalStep (P.enterProtocolBody (ident 21)) ∷ physicalStep (P.protocolReturned (ident 21)) ∷ V.commitClean (ident 21) ∷ [])) ++ take 39 CC.cleanContinuationActions
    abstract
      receipt-frame : Joins.FramedRuns D.cmEntry D.receiptActions D.receipt5
      receipt-frame = Joins.framed-server CMResultLifecycleChecks.actual-receipt-path
      race-prefix : Joins.FramedRuns D.cmEntry racePrefix PR.raceHandler10
      race-prefix = Joins.framed-append (Joins.framed-append (Joins.framed-append
        (Joins.framed-append receipt-frame PR.race-start-frame) PR.race-pool-frame) PR.race-catch-frame) PR.race-finalizer-frame
      clean-prefix : Joins.FramedRuns D.cmEntry cleanPrefix (CC.withCurrentClean D.handler10)
      clean-prefix = Joins.framed-append (Joins.framed-append
        (Joins.framed-append receipt-frame CC.clean-request-frame) CC.clean-commit-frame) CC.clean-finalizer-frame
      publication-race-wait : Joins.FramedCMResultWait initial PR.raceHandler10 PR.raceFinalCM
      publication-race-wait = Joins.initialized-framed-result-wait
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial}
        {prefix = D.livePrefixActions ++ D.peerBeforeCallbackActions} {callbackBefore = D.innerClosed} {callbackAfter = D.callbackExited}
        {entryActions = ServerCMEntryLifecycleChecks.cleanupActions} {entry = D.cmEntry} {before = PR.raceHandler10} {events = racePrefix} {after = PR.raceFinalCM}
        initializer D.restarted-before-callback D.peerCloseEdge33 ServerCMEntryLifecycleChecks.actual-server-suffix race-prefix PR.raceFinishEdge11
      clean-race-wait : Joins.FramedCMResultWait initial (CC.withCurrentClean D.handler10) (CC.withCurrentClean D.finalCM)
      clean-race-wait = Joins.initialized-framed-result-wait
        {c = CloseOriginChecks.initialCM} {g = L.settings} {start = initial}
        {prefix = D.livePrefixActions ++ D.peerBeforeCallbackActions} {callbackBefore = D.innerClosed} {callbackAfter = D.callbackExited}
        {entryActions = ServerCMEntryLifecycleChecks.cleanupActions} {entry = D.cmEntry}
        {before = CC.withCurrentClean D.handler10} {events = cleanPrefix} {after = CC.withCurrentClean D.finalCM}
        initializer D.restarted-before-callback D.peerCloseEdge33 ServerCMEntryLifecycleChecks.actual-server-suffix clean-prefix CC.cleanEdge40
      publication-physical-wait : PhysicalProofs.PhysicalWait (Joins.physical PR.raceHandler10) (Joins.physical PR.raceFinalCM)
      publication-physical-wait = Joins.FramedCMResultWait.observed publication-race-wait
      clean-physical-wait : PhysicalProofs.PhysicalWait (Joins.physical (CC.withCurrentClean D.handler10)) (Joins.physical (CC.withCurrentClean D.finalCM))
      clean-physical-wait = Joins.FramedCMResultWait.observed clean-race-wait
      publication-components : BFacts.Certificates (V.base PR.raceFinalCM)
      publication-components = Joins.framed-wait-components publication-race-wait
      clean-components : BFacts.Certificates (V.base (CC.withCurrentClean D.finalCM))
      clean-components = Joins.framed-wait-components clean-race-wait
      publication-monitor : Stages.Publication initial PR.raceFinalCM (ident 50) Monitor.cancelled
      publication-monitor = Joins.cancelled-lifecycle (Joins.joined-lifecycle (Joins.framed-wait-monitors publication-race-wait) (here refl)) refl
      clean-monitor : Stages.Publication initial (CC.withCurrentClean D.finalCM) (ident 50) Monitor.cancelled
      clean-monitor = Joins.cancelled-lifecycle (Joins.joined-lifecycle (Joins.framed-wait-monitors clean-race-wait) (here refl)) refl
      publication-return-frame : Joins.FramedRuns PR.raceFinalCM (SC.serverEvent S.finishServer ∷ []) PR.raceServer
      publication-return-frame = Joins.frameNext {event = SC.serverEvent S.finishServer}
        (Joins.server-framed (E.run (S.scope S.finishServer)) PR.raceFinalCM PR.raceFinishEdge12) PR.raceFinishEdge12 Joins.frameDone
      clean-return-frame : Joins.FramedRuns (CC.withCurrentClean D.finalCM) (SC.serverEvent S.finishServer ∷ []) CC.cleanServer
      clean-return-frame = Joins.frameNext {event = SC.serverEvent S.finishServer}
        (Joins.server-framed (E.run (S.scope S.finishServer)) (CC.withCurrentClean D.finalCM) CC.cleanEdge41) CC.cleanEdge41 Joins.frameDone
      publication-return-components : BFacts.Certificates (V.base PR.raceServer)
      publication-return-components = Joins.framed-components (Joins.FramedCMResultWait.entry publication-race-wait)
        (Joins.framed-append (Joins.framed-wait-cleanup publication-race-wait) publication-return-frame)
      clean-return-components : BFacts.Certificates (V.base CC.cleanServer)
      clean-return-components = Joins.framed-components (Joins.FramedCMResultWait.entry clean-race-wait)
        (Joins.framed-append (Joins.framed-wait-cleanup clean-race-wait) clean-return-frame)
      clean-commit-preserves-scopes : Joins.frame-view CC.currentCommitted ≡ Joins.frame-view CC.currentBodyReturned
      clean-commit-preserves-scopes = Joins.advance-frame (V.commitClean (ident 21)) CC.currentBodyReturned refl CC.currentCommitEdge
    peer-cache-changes : lookup (ident 0) (C.SubContext.peers (C.subsystem (K.context (V.base CC.currentBodyReturned)))) ≡
      lookup (ident 0) (C.SubContext.peers (C.subsystem (K.context (V.base CC.currentCommitted)))) → ⊥
    peer-cache-changes ()
    whole-context-changes : K.context (V.base CC.currentBodyReturned) ≡ K.context (V.base CC.currentCommitted) → ⊥
    whole-context-changes eq = peer-cache-changes (cong (λ k → lookup (ident 0) (C.SubContext.peers (C.subsystem k))) eq)
    clean-local-result-retained : V.observe (ident 21) CC.cleanServer ≡ just (V.localResult clean)
    clean-local-result-retained = CC.current-clean-survives-return
    local-clean-is-not-handler-result : N.W.resultReady A.child₀ (Joins.physical (CC.withCurrentClean D.readyForBuffer)) ≡ false
    local-clean-is-not-handler-result = CC.clean-cell-does-not-complete-handler
    local-clean-is-not-CM-completion : V.advance (SC.coordinatorEvent Close.finishClose) (CC.withCurrentClean D.handler9) ≡ nothing
    local-clean-is-not-CM-completion = CC.clean-cell-does-not-close-cm
    physical-current-result-cancelled : lookup (ident 21) (Pool.handles (P.poolAt A.child₀ (V.physical (V.base CC.cleanServer)))) ≡ just (Pool.resultAvailable Pool.cancelledExit)
    physical-current-result-cancelled = CC.physical-current-result-is-cancelled
    admissions-still-incomplete : S.allResults (S.workers (E.base (K.server (V.base CC.cleanServer)))) ≡ false
    admissions-still-incomplete = refl


  -- Original handler references come from an actual initialized promise/select/
  -- fork prefix and survive all peer/cache/cleanup steps to physical boundaries.
  module HandlerResourceOriginChecks where
    open import Data.List using (take; drop)
    open import Data.List.Relation.Unary.Any using (here)
    open import Data.List.Membership.Propositional using (_∈_)
    open import Relation.Binary.PropositionalEquality using (sym; trans)
    open import Data.Empty using (⊥)
    import ConnectionManagement.Properties.ServerPeersHandlerResources as HandlerResources
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
    import ConnectionManagement.Properties.HandlerResourceFacts as ResourceFacts
    import ConnectionManagement.Rules.CMShutdown as Close
    import ConnectionManagement.Rules.Cleanup as Cleanup
    private
      module Resources = HandlerResources.Frontend I.bearerClosed Prior.classify capability
      module Joins = MonitorJoins.Frontend I.bearerClosed Prior.classify capability
      module D = Reactivation.Shutdown
      module PR = D.PublicationRace
      module CC = D.CurrentClean
      module W = N.W
    beforeAllocation : V.Runs initial (take 4 prefixActions) (wrap (base F.p2))
    beforeAllocation = V.more p1 (V.more p2 (V.more p3 (V.more p4 V.stop)))
    forkPrefix : V.Runs initial (take 7 prefixActions) (wrap (base F.p5))
    forkPrefix = V.more p1 (V.more p2 (V.more p3 (V.more p4 (V.more p5 (V.more p6 (V.more p7 V.stop))))))
    born-origin : Resources.Origin initial (wrap (base F.p5)) A.child₀
    born-origin = Resources.initialized-inbound-origin-from-frontend A.w₀ F.r₀ (Shared.lease A.w₀ [])
      initializer beforeAllocation refl p5 p6 p7 V.stop
    original-descriptor : Resources.Origin.captured born-origin ≡ I.captured
    original-descriptor = refl
    original-promise : Resources.Origin.promise born-origin ≡ Shared.handlerPromise I.captured
    original-promise = refl
    original-promise-allocated : Shared.handlerPromise I.captured ∈ Shared.promises (Resources.shared (wrap (base F.p3)))
    original-promise-allocated = Resources.Origin.promise-allocated born-origin
    -- These primitive source equations are outputs of the real frontend steps.
    derived-allocation : Machine.advance (Machine.admissionStep A.w₀ Admission.allocatePromise)
      (Resources.core (wrap (base F.p2))) ≡ just (Resources.core (wrap (base F.p3)))
    derived-allocation = Resources.allocation-lower A.w₀ (wrap (base F.p2)) p5
    derived-selection : Machine.advance (Machine.admissionStep A.w₀ Admission.chooseEntry)
      (Resources.core (wrap (base F.p3))) ≡ just (Resources.core (wrap (base F.p4)))
    derived-selection = Resources.selection-lower A.w₀ (wrap (base F.p3)) p6
    derived-fork : Machine.advance (Machine.admissionStep A.w₀ Admission.fork)
      (Resources.core (wrap (base F.p4))) ≡ just (Resources.core (wrap (base F.p5)))
    derived-fork = Resources.fork-lower A.w₀ (wrap (base F.p4)) p7
    no-allocation-before-admission : V.advance (Resources.event A.w₀ Admission.allocatePromise) initial ≡ nothing
    no-allocation-before-admission = refl
    no-selection-before-promise : V.advance (Resources.event A.w₀ Admission.chooseEntry) (wrap (base F.p2)) ≡ nothing
    no-selection-before-promise = refl
    no-fork-before-selection : V.advance (Resources.event A.w₀ Admission.fork) (wrap (base F.p3)) ≡ nothing
    no-fork-before-selection = refl
    entryPrefix : List V.Event
    entryPrefix = (D.livePrefixActions ++ D.peerCloseActions) ++
      map Joins.server-event (ServerCMEntryLifecycleChecks.cleanupActions ++ (E.run (S.scope S.beginCM) ∷ []))
    abstract
      initialized-entry : V.Runs initial entryPrefix D.cmEntry
      initialized-entry = Facts.append-protocols D.initialized-peer-close
        (Joins.server-runs ServerCMEntryLifecycleChecks.actual-server-suffix)
      entry-origin : Resources.Origin initial D.cmEntry A.child₀
      entry-origin = Resources.extend
        (Resources.discard-prefix {suffix = drop 7 entryPrefix} forkPrefix initialized-entry) born-origin
      ready-origin : Resources.Origin initial D.readyForBuffer A.child₀
      ready-origin = Resources.extend (Joins.server-runs (Joins.server-append
        (Joins.server-append CMResultLifecycleChecks.actual-receipt-path CMResultLifecycleChecks.actual-pool-path)
        CMResultLifecycleChecks.actual-catch-path)) entry-origin
      before-publication-path : V.Runs D.readyForBuffer (take 9 D.handlerFinishActions) D.handler9
      before-publication-path = V.more {s = D.readyForBuffer} {t = D.handler1} {u = D.handler9} {a = Joins.handler-event (W.beginExit A.child₀)} D.handlerFinishEdge1 (V.more {s = D.handler1} {t = D.handler2} {u = D.handler9} {a = Joins.handler-event (W.observeBufferReturn A.child₀)} D.handlerFinishEdge2 (V.more {s = D.handler2} {t = D.handler3} {u = D.handler9} {a = Joins.handler-event (W.enterFinalizer A.child₀)} D.handlerFinishEdge3 (V.more {s = D.handler3} {t = D.handler4} {u = D.handler9} {a = Joins.handler-event (W.cleanup A.child₀ Cleanup.takeCleanupMap)} D.handlerFinishEdge4 (V.more {s = D.handler4} {t = D.handler5} {u = D.handler9} {a = Joins.handler-event (W.cleanup A.child₀ Cleanup.selectCleanupEntry)} D.handlerFinishEdge5 (V.more {s = D.handler5} {t = D.handler6} {u = D.handler9} {a = Joins.handler-event (W.cleanup A.child₀ Cleanup.closeHandlerSocket)} D.handlerFinishEdge6 (V.more {s = D.handler6} {t = D.handler7} {u = D.handler9} {a = Joins.handler-event (W.cleanup A.child₀ Cleanup.publishCleanupMap)} D.handlerFinishEdge7 (V.more {s = D.handler7} {t = D.handler8} {u = D.handler9} {a = Joins.handler-event (W.cleanup A.child₀ Cleanup.readCleanupCounters)} D.handlerFinishEdge8 (V.more {s = D.handler8} {t = D.handler9} {u = D.handler9} {a = Joins.handler-event (W.finishCleanup A.child₀)} D.handlerFinishEdge9 (V.stop)))))))))
      before-publication-origin : Resources.Origin initial D.handler9 A.child₀
      before-publication-origin = Resources.extend before-publication-path ready-origin
      publication-origin : Resources.AtPublication initial D.handler9 D.handler10 A.child₀
      publication-origin = Resources.publication-origin before-publication-origin D.handlerFinishEdge10
      wait-origin : Resources.AtWait initial D.handler10 D.finalCM A.child₀
      wait-origin = Resources.wait-origin (Resources.AtPublication.following publication-origin) D.handlerFinishEdge11 (here refl)
      return-origin : Resources.Origin initial D.returnedServer A.child₀
      return-origin = Resources.extend (Joins.server-runs CMResultLifecycleChecks.actual-server-return-path) (Resources.AtWait.following wait-origin)
      publication-race-origin : Resources.AtWait initial PR.raceHandler10 PR.raceFinalCM A.child₀
      publication-race-origin = Resources.wait-origin
        (Resources.extend (Joins.framed-runs RaceLifecycleChecks.race-prefix) entry-origin) PR.raceFinishEdge11 (here refl)
      clean-race-origin : Resources.AtWait initial (CC.withCurrentClean D.handler10) (CC.withCurrentClean D.finalCM) A.child₀
      clean-race-origin = Resources.wait-origin
        (Resources.extend (Joins.framed-runs RaceLifecycleChecks.clean-prefix) entry-origin) CC.cleanEdge40 (here refl)
      retained-at-publication : ResourceFacts.Facts A.child₀ I.captured (Resources.shared D.handler10)
      retained-at-publication = Resources.Origin.retained (Resources.AtPublication.following publication-origin)
      retained-at-wait : ResourceFacts.Facts A.child₀ I.captured (Resources.shared D.finalCM)
      retained-at-wait = Resources.Origin.retained (Resources.AtWait.following wait-origin)
      retained-at-server-return : ResourceFacts.Facts A.child₀ I.captured (Resources.shared D.returnedServer)
      retained-at-server-return = Resources.Origin.retained return-origin
      retained-at-publication-race-wait : ResourceFacts.Facts A.child₀ I.captured (Resources.shared PR.raceFinalCM)
      retained-at-publication-race-wait = Resources.Origin.retained (Resources.AtWait.following publication-race-origin)
      retained-at-clean-race-wait : ResourceFacts.Facts A.child₀ I.captured (Resources.shared (CC.withCurrentClean D.finalCM))
      retained-at-clean-race-wait = Resources.Origin.retained (Resources.AtWait.following clean-race-origin)
    -- Socket storage persists after closure; this certificate asserts no live owner.
    socket-already-closed : lookup (Shared.handlerSocket I.captured) (Shared.sockets (Resources.shared D.handler9)) ≡ just Shared.closed
    socket-already-closed = refl
    wrong-worker-has-no-resources : ResourceFacts.Facts (ident 999) I.captured (Resources.shared D.handler10) → ⊥
    wrong-worker-has-no-resources (() , _)
    forged-descriptor : lookup A.child₀ (Shared.handlers (Resources.shared D.handler10)) ≡
      just (Shared.handlerStart (ident 999) (Shared.handlerSocket I.captured) (Shared.handlerPromise I.captured) (Shared.handlerKey I.captured)) → ⊥
    forged-descriptor ()
    premature-wait-still-refused : V.advance (StartTrace.ScopedCM.coordinatorEvent Close.finishClose) D.handler9 ≡ nothing
    premature-wait-still-refused = CMResultLifecycleChecks.no-wait-before-publication
    resource-raw-admissions-incomplete : S.allResults (S.workers (E.base (K.server (V.base D.returnedServer)))) ≡ false
    resource-raw-admissions-incomplete = CMResultLifecycleChecks.returned-admissions-incomplete


  -- A separate initialized outbound route, retaining the bounded pre-handshake
  -- coordinator. Expected states omit the old fixture's unused inbound actors;
  -- every edge below is checked through the unchanged common frontend.
  module OutboundHandlerResourceOriginChecks where
    open import Data.List.Membership.Propositional using (_∈_)
    open import Data.List.Relation.Unary.Any using (here)
    import ConnectionManagement.Properties.ServerPeersHandlerResources as HandlerResources
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
    import ConnectionManagement.Properties.HandlerResourceFacts as ResourceFacts
    import ConnectionManagement.Negative.OutboundHandlerSupervision as OB
    import ConnectionManagement.CSP.OutboundAdmission as OA
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.Rules.CMShutdown as Close
    import ConnectionManagement.Rules.Cleanup as Cleanup
    private
      module W = N.W
      module Resources = HandlerResources.Frontend I.bearerClosed Prior.classify capability
      module Joins = MonitorJoins.Frontend I.bearerClosed Prior.classify capability
    keep-socket : Store SocketId Shared.SocketOwner → Store SocketId Shared.SocketOwner
    keep-socket sockets with lookup OA.sock sockets
    ... | nothing = []
    ... | just owner = (OA.sock , owner) ∷ []
    outbound-state : B.State → B.State
    outbound-state b = record b { source = record c { core = Machine.replaceWorld (O.core c)
      (record world { admissions = []; sockets = keep-socket (Shared.sockets world) }) } }
      where
      c = B.source b
      world = Machine.world (O.core c)
    origins : B.State → Store WorkerId Provenance
    origins b with B.threads b
    ... | [] = []
    ... | _ ∷ _ = (OA.child , outbound) ∷ []
    render-outbound : B.State → Store WorkerId Cancel.Context → V.Runtime
    render-outbound b regions = V.runtime (record (V.setPhysical p (V.base initial))
      { context = record k0 { regions = regions } }) V.empty
      where
      old = V.physical (V.base initial)
      p = record old { base = record (P.base old) { base = outbound-state b; origins = origins b } }
    ordinary forked : Store WorkerId Cancel.Context
    ordinary = (OA.caller , Cancel.ordinary) ∷ []
    forked = (OA.caller , Cancel.forkedBeforeHandoff) ∷ []
    start : V.Runtime
    start = render-outbound OB.p₀ []
    outbound-initialized : V.initialize (O.initial (Machine.initial Shared.responderMode F.empty)) L.settings ≡ just start
    outbound-initialized = refl
    outbound1 : V.Runtime
    outbound1 = render-outbound OB.p1 ordinary
    outbound2 : V.Runtime
    outbound2 = render-outbound OB.p2 ordinary
    outbound3 : V.Runtime
    outbound3 = render-outbound OB.p3 ordinary
    outbound4 : V.Runtime
    outbound4 = render-outbound OB.p4 ordinary
    outbound5 : V.Runtime
    outbound5 = render-outbound OB.p5 ordinary
    outbound6 : V.Runtime
    outbound6 = render-outbound OB.p6 ordinary
    outbound7 : V.Runtime
    outbound7 = render-outbound OB.p7 ordinary
    outbound8 : V.Runtime
    outbound8 = render-outbound OB.p8 ordinary
    outbound9 : V.Runtime
    outbound9 = render-outbound OB.p9 ordinary
    outbound10 : V.Runtime
    outbound10 = render-outbound OB.p10 forked
    outbound11 : V.Runtime
    outbound11 = render-outbound OB.p11 forked
    outbound12 : V.Runtime
    outbound12 = render-outbound OB.p12 ordinary
    handed : V.Runtime
    handed = render-outbound OB.p11 ordinary
    -- Close the empty peer pools and all four lexical scopes before the
    -- actual Server callback return. No CM-bearing snapshot is substituted.
    outbound-context : Scope.State → GP.Pool.ClosePC → PS.Pool.ClosePC → C.Context
    outbound-context scopes governorPhase monitorPhase = record k0
      { regions = ordinary; scopes = scopes
      ; governorPool = record (C.governorPool k0) { phase = governorPhase }
      ; monitorPool = record (C.monitorPool k0) { phase = monitorPhase } }
    outbound-peer-at : Scope.State → GP.Pool.ClosePC → PS.Pool.ClosePC → V.Runtime
    outbound-peer-at scopes governorPhase monitorPhase = record outbound12
      { base = record (V.base outbound12) { context = outbound-context scopes governorPhase monitorPhase } }
    outbound-peer-event : PS.Action → V.Event
    outbound-peer-event action = V.dispatch (K.peerStep action)
    outbound-peer1 : V.Runtime
    outbound-peer1 = outbound-peer-at Fixtures.q1 GP.Pool.openPool PS.Pool.openPool
    outbound-peer-edge1 : V.advance (outbound-peer-event (PS.scope Scope.beginUnwind)) outbound12 ≡ just outbound-peer1
    outbound-peer-edge1 = refl
    outbound-peer2 : V.Runtime
    outbound-peer2 = outbound-peer-at Fixtures.q2 GP.Pool.openPool PS.Pool.openPool
    outbound-peer-edge2 : V.advance (outbound-peer-event (PS.scope Scope.requestCancel)) outbound-peer1 ≡ just outbound-peer2
    outbound-peer-edge2 = refl
    outbound-peer3 : V.Runtime
    outbound-peer3 = outbound-peer-at Fixtures.q3 GP.Pool.openPool PS.Pool.openPool
    outbound-peer-edge3 : V.advance (outbound-peer-event (PS.scope Scope.deliverCancel)) outbound-peer2 ≡ just outbound-peer3
    outbound-peer-edge3 = refl
    outbound-peer4 : V.Runtime
    outbound-peer4 = outbound-peer-at Fixtures.q4 GP.Pool.openPool PS.Pool.openPool
    outbound-peer-edge4 : V.advance (outbound-peer-event (PS.scope (Scope.bodyExit Scope.churn))) outbound-peer3 ≡ just outbound-peer4
    outbound-peer-edge4 = refl
    outbound-peer5 : V.Runtime
    outbound-peer5 = outbound-peer-at Fixtures.q5 GP.Pool.openPool PS.Pool.openPool
    outbound-peer-edge5 : V.advance (outbound-peer-event (PS.scope (Scope.publishResult Scope.churn))) outbound-peer4 ≡ just outbound-peer5
    outbound-peer-edge5 = refl
    outbound-peer6 : V.Runtime
    outbound-peer6 = outbound-peer-at Fixtures.q6 GP.Pool.openPool PS.Pool.openPool
    outbound-peer-edge6 : V.advance (outbound-peer-event (PS.scope Scope.join)) outbound-peer5 ≡ just outbound-peer6
    outbound-peer-edge6 = refl
    outbound-peer7 : V.Runtime
    outbound-peer7 = outbound-peer-at Fixtures.q7 GP.Pool.openPool PS.Pool.openPool
    outbound-peer-edge7 : V.advance (outbound-peer-event (PS.scope Scope.requestCancel)) outbound-peer6 ≡ just outbound-peer7
    outbound-peer-edge7 = refl
    outbound-peer8 : V.Runtime
    outbound-peer8 = outbound-peer-at Fixtures.q8 GP.Pool.openPool PS.Pool.openPool
    outbound-peer-edge8 : V.advance (outbound-peer-event (PS.scope Scope.deliverCancel)) outbound-peer7 ≡ just outbound-peer8
    outbound-peer-edge8 = refl
    outbound-peer9 : V.Runtime
    outbound-peer9 = outbound-peer-at Fixtures.q8 GP.Pool.closing PS.Pool.openPool
    outbound-peer-edge9 : V.advance (outbound-peer-event (PS.run (GP.beginClose []))) outbound-peer8 ≡ just outbound-peer9
    outbound-peer-edge9 = refl
    outbound-peer10 : V.Runtime
    outbound-peer10 = outbound-peer-at Fixtures.q8 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge10 : V.advance (outbound-peer-event (PS.run GP.finishClose)) outbound-peer9 ≡ just outbound-peer10
    outbound-peer-edge10 = refl
    outbound-peer11 : V.Runtime
    outbound-peer11 = outbound-peer-at Fixtures.q9 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge11 : V.advance (outbound-peer-event (PS.scope (Scope.bodyExit Scope.governor))) outbound-peer10 ≡ just outbound-peer11
    outbound-peer-edge11 = refl
    outbound-peer12 : V.Runtime
    outbound-peer12 = outbound-peer-at Fixtures.q10 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge12 : V.advance (outbound-peer-event (PS.scope (Scope.publishResult Scope.governor))) outbound-peer11 ≡ just outbound-peer12
    outbound-peer-edge12 = refl
    outbound-peer13 : V.Runtime
    outbound-peer13 = outbound-peer-at Fixtures.q11 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge13 : V.advance (outbound-peer-event (PS.scope Scope.join)) outbound-peer12 ≡ just outbound-peer13
    outbound-peer-edge13 = refl
    outbound-peer14 : V.Runtime
    outbound-peer14 = outbound-peer-at Fixtures.q12 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge14 : V.advance (outbound-peer-event (PS.scope Scope.requestCancel)) outbound-peer13 ≡ just outbound-peer14
    outbound-peer-edge14 = refl
    outbound-peer15 : V.Runtime
    outbound-peer15 = outbound-peer-at Fixtures.q13 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge15 : V.advance (outbound-peer-event (PS.scope Scope.deliverCancel)) outbound-peer14 ≡ just outbound-peer15
    outbound-peer-edge15 = refl
    outbound-peer16 : V.Runtime
    outbound-peer16 = outbound-peer-at Fixtures.q14 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge16 : V.advance (outbound-peer-event (PS.scope (Scope.bodyExit Scope.localRoot))) outbound-peer15 ≡ just outbound-peer16
    outbound-peer-edge16 = refl
    outbound-peer17 : V.Runtime
    outbound-peer17 = outbound-peer-at Fixtures.q15 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge17 : V.advance (outbound-peer-event (PS.scope (Scope.publishResult Scope.localRoot))) outbound-peer16 ≡ just outbound-peer17
    outbound-peer-edge17 = refl
    outbound-peer18 : V.Runtime
    outbound-peer18 = outbound-peer-at Fixtures.q16 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge18 : V.advance (outbound-peer-event (PS.scope Scope.join)) outbound-peer17 ≡ just outbound-peer18
    outbound-peer-edge18 = refl
    outbound-peer19 : V.Runtime
    outbound-peer19 = outbound-peer-at Fixtures.q17 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge19 : V.advance (outbound-peer-event (PS.scope Scope.requestCancel)) outbound-peer18 ≡ just outbound-peer19
    outbound-peer-edge19 = refl
    outbound-peer20 : V.Runtime
    outbound-peer20 = outbound-peer-at Fixtures.q18 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge20 : V.advance (outbound-peer-event (PS.scope Scope.deliverCancel)) outbound-peer19 ≡ just outbound-peer20
    outbound-peer-edge20 = refl
    outbound-peer21 : V.Runtime
    outbound-peer21 = outbound-peer-at Fixtures.q19 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge21 : V.advance (outbound-peer-event (PS.scope (Scope.bodyExit Scope.ledger))) outbound-peer20 ≡ just outbound-peer21
    outbound-peer-edge21 = refl
    outbound-peer22 : V.Runtime
    outbound-peer22 = outbound-peer-at Fixtures.q20 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge22 : V.advance (outbound-peer-event (PS.scope (Scope.publishResult Scope.ledger))) outbound-peer21 ≡ just outbound-peer22
    outbound-peer-edge22 = refl
    outbound-peer23 : V.Runtime
    outbound-peer23 = outbound-peer-at Fixtures.q21 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge23 : V.advance (outbound-peer-event (PS.scope Scope.join)) outbound-peer22 ≡ just outbound-peer23
    outbound-peer-edge23 = refl
    outbound-peer24 : V.Runtime
    outbound-peer24 = outbound-peer-at Fixtures.q22 GP.Pool.closedPool PS.Pool.openPool
    outbound-peer-edge24 : V.advance (outbound-peer-event (PS.scope Scope.finishClose)) outbound-peer23 ≡ just outbound-peer24
    outbound-peer-edge24 = refl
    outbound-peer25 : V.Runtime
    outbound-peer25 = outbound-peer-at Fixtures.q22 GP.Pool.closedPool PS.Pool.closing
    outbound-peer-edge25 : V.advance (outbound-peer-event (PS.beginMonitorClose [])) outbound-peer24 ≡ just outbound-peer25
    outbound-peer-edge25 = refl
    outbound-peer26 : V.Runtime
    outbound-peer26 = outbound-peer-at Fixtures.q22 GP.Pool.closedPool PS.Pool.closedPool
    outbound-peer-edge26 : V.advance (outbound-peer-event (PS.finishMonitorClose)) outbound-peer25 ≡ just outbound-peer26
    outbound-peer-edge26 = refl
    outbound-peer-events : List V.Event
    outbound-peer-events = outbound-peer-event (PS.scope Scope.beginUnwind) ∷
      outbound-peer-event (PS.scope Scope.requestCancel) ∷
      outbound-peer-event (PS.scope Scope.deliverCancel) ∷
      outbound-peer-event (PS.scope (Scope.bodyExit Scope.churn)) ∷
      outbound-peer-event (PS.scope (Scope.publishResult Scope.churn)) ∷
      outbound-peer-event (PS.scope Scope.join) ∷
      outbound-peer-event (PS.scope Scope.requestCancel) ∷
      outbound-peer-event (PS.scope Scope.deliverCancel) ∷
      outbound-peer-event (PS.run (GP.beginClose [])) ∷
      outbound-peer-event (PS.run GP.finishClose) ∷
      outbound-peer-event (PS.scope (Scope.bodyExit Scope.governor)) ∷
      outbound-peer-event (PS.scope (Scope.publishResult Scope.governor)) ∷
      outbound-peer-event (PS.scope Scope.join) ∷
      outbound-peer-event (PS.scope Scope.requestCancel) ∷
      outbound-peer-event (PS.scope Scope.deliverCancel) ∷
      outbound-peer-event (PS.scope (Scope.bodyExit Scope.localRoot)) ∷
      outbound-peer-event (PS.scope (Scope.publishResult Scope.localRoot)) ∷
      outbound-peer-event (PS.scope Scope.join) ∷
      outbound-peer-event (PS.scope Scope.requestCancel) ∷
      outbound-peer-event (PS.scope Scope.deliverCancel) ∷
      outbound-peer-event (PS.scope (Scope.bodyExit Scope.ledger)) ∷
      outbound-peer-event (PS.scope (Scope.publishResult Scope.ledger)) ∷
      outbound-peer-event (PS.scope Scope.join) ∷
      outbound-peer-event (PS.scope Scope.finishClose) ∷
      outbound-peer-event (PS.beginMonitorClose []) ∷
      outbound-peer-event (PS.finishMonitorClose) ∷
      []
    outbound-peer-path : V.Runs outbound12 outbound-peer-events outbound-peer26
    outbound-peer-path = V.more {a = outbound-peer-event (PS.scope Scope.beginUnwind)} outbound-peer-edge1
      (V.more {a = outbound-peer-event (PS.scope Scope.requestCancel)} outbound-peer-edge2
      (V.more {a = outbound-peer-event (PS.scope Scope.deliverCancel)} outbound-peer-edge3
      (V.more {a = outbound-peer-event (PS.scope (Scope.bodyExit Scope.churn))} outbound-peer-edge4
      (V.more {a = outbound-peer-event (PS.scope (Scope.publishResult Scope.churn))} outbound-peer-edge5
      (V.more {a = outbound-peer-event (PS.scope Scope.join)} outbound-peer-edge6
      (V.more {a = outbound-peer-event (PS.scope Scope.requestCancel)} outbound-peer-edge7
      (V.more {a = outbound-peer-event (PS.scope Scope.deliverCancel)} outbound-peer-edge8
      (V.more {a = outbound-peer-event (PS.run (GP.beginClose []))} outbound-peer-edge9
      (V.more {a = outbound-peer-event (PS.run GP.finishClose)} outbound-peer-edge10
      (V.more {a = outbound-peer-event (PS.scope (Scope.bodyExit Scope.governor))} outbound-peer-edge11
      (V.more {a = outbound-peer-event (PS.scope (Scope.publishResult Scope.governor))} outbound-peer-edge12
      (V.more {a = outbound-peer-event (PS.scope Scope.join)} outbound-peer-edge13
      (V.more {a = outbound-peer-event (PS.scope Scope.requestCancel)} outbound-peer-edge14
      (V.more {a = outbound-peer-event (PS.scope Scope.deliverCancel)} outbound-peer-edge15
      (V.more {a = outbound-peer-event (PS.scope (Scope.bodyExit Scope.localRoot))} outbound-peer-edge16
      (V.more {a = outbound-peer-event (PS.scope (Scope.publishResult Scope.localRoot))} outbound-peer-edge17
      (V.more {a = outbound-peer-event (PS.scope Scope.join)} outbound-peer-edge18
      (V.more {a = outbound-peer-event (PS.scope Scope.requestCancel)} outbound-peer-edge19
      (V.more {a = outbound-peer-event (PS.scope Scope.deliverCancel)} outbound-peer-edge20
      (V.more {a = outbound-peer-event (PS.scope (Scope.bodyExit Scope.ledger))} outbound-peer-edge21
      (V.more {a = outbound-peer-event (PS.scope (Scope.publishResult Scope.ledger))} outbound-peer-edge22
      (V.more {a = outbound-peer-event (PS.scope Scope.join)} outbound-peer-edge23
      (V.more {a = outbound-peer-event (PS.scope Scope.finishClose)} outbound-peer-edge24
      (V.more {a = outbound-peer-event (PS.beginMonitorClose [])} outbound-peer-edge25
      (V.more {a = outbound-peer-event (PS.finishMonitorClose)} outbound-peer-edge26 (V.stop))))))))))))))))))))))))))
    outbound-initial-ig outbound-inactive-ig outbound-exited-ig : IG.Runtime
    outbound-initial-ig = Machine.inboundGovernor (O.core (K.source (V.base outbound12)))
    outbound-inactive-ig = record outbound-initial-ig
      { continuation = IG.exitFlush; execution = record (IG.execution outbound-initial-ig) { active = false } }
    outbound-exited-ig = record outbound-inactive-ig { continuation = IG.exited }
    -- Preserve the observed IG exception and its empty final-callback snapshot.
    outbound-ig-caught outbound-ig-done outbound-ig-published : E.Exit
    outbound-ig-caught = E.caughtExit (E.receipt E.loopBoundary OB.err nothing)
    outbound-ig-done = record outbound-ig-caught { phase = E.bodyDone }
    outbound-ig-published = record outbound-ig-done { result = just (S.async OB.err) }
    outbound-exit-at : S.Stage → E.Exit
    outbound-exit-at S.igCancelDelivered = outbound-ig-caught
    outbound-exit-at S.igInactive = outbound-ig-caught
    outbound-exit-at S.igFlushed = outbound-ig-caught
    outbound-exit-at S.igBodyExited = outbound-ig-done
    outbound-exit-at S.igResultAvailable = outbound-ig-published
    outbound-exit-at S.igJoined = outbound-ig-published
    outbound-exit-at S.closingCM = outbound-ig-published
    outbound-exit-at _ = E.emptyExit
    outbound-owned-at : B.State → S.Stage → Bool → IG.Runtime → V.Runtime
    outbound-owned-at b stage listener ig = V.runtime (record ownedBase
      { server = record (K.server ownedBase) { base = record (E.base (K.server ownedBase)) { stage = stage; listenerOpen = listener }; exit = outbound-exit-at stage } }) V.empty
      where
      original = render-outbound b ordinary
      source = K.source (V.base original)
      updated = record source { core = record (O.core source) { inboundGovernor = ig } }
      ownedBase = record (V.base original)
        { context = outbound-context Fixtures.q22 GP.Pool.closedPool PS.Pool.closedPool
        ; server = K.setSource updated (K.server (V.base original)) }
    outbound-exit-event : E.Action → V.Event
    outbound-exit-event action = V.dispatch (K.serverStep action)
    outbound-scope-event : S.ScopeAction → V.Event
    outbound-scope-event action = V.dispatch (K.serverStep (E.run (S.scope action)))
    outbound-scope1 : V.Runtime
    outbound-scope1 = outbound-owned-at OB.p12 S.actionBodyExited true outbound-initial-ig
    outbound-scope-edge1 : V.advance (outbound-scope-event S.returnAction) outbound-peer26 ≡ just outbound-scope1
    outbound-scope-edge1 = refl
    outbound-scope2 : V.Runtime
    outbound-scope2 = outbound-owned-at OB.p12 S.actionResultAvailable true outbound-initial-ig
    outbound-scope-edge2 : V.advance (outbound-scope-event S.publishActionResult) outbound-scope1 ≡ just outbound-scope2
    outbound-scope-edge2 = refl
    outbound-scope3 : V.Runtime
    outbound-scope3 = outbound-owned-at OB.p12 S.closingAccept true outbound-initial-ig
    outbound-scope-edge3 : V.advance (outbound-scope-event S.selectActionWinner) outbound-scope2 ≡ just outbound-scope3
    outbound-scope-edge3 = refl
    outbound-scope4 : V.Runtime
    outbound-scope4 = outbound-owned-at OB.p12 S.acceptCancelRequested true outbound-initial-ig
    outbound-scope-edge4 : V.advance (outbound-scope-event S.requestAcceptCancel) outbound-scope3 ≡ just outbound-scope4
    outbound-scope-edge4 = refl
    outbound-scope5 : V.Runtime
    outbound-scope5 = outbound-owned-at OB.p12 S.acceptCancelDelivered true outbound-initial-ig
    outbound-scope-edge5 : V.advance (outbound-scope-event S.deliverAcceptAtWait) outbound-scope4 ≡ just outbound-scope5
    outbound-scope-edge5 = refl
    outbound-scope6 : V.Runtime
    outbound-scope6 = outbound-owned-at OB.p12 S.acceptBodyExited false outbound-initial-ig
    outbound-scope-edge6 : V.advance (outbound-scope-event S.closeListener) outbound-scope5 ≡ just outbound-scope6
    outbound-scope-edge6 = refl
    outbound-scope7 : V.Runtime
    outbound-scope7 = outbound-owned-at OB.p12 S.acceptResultAvailable false outbound-initial-ig
    outbound-scope-edge7 : V.advance (outbound-scope-event S.publishAcceptResult) outbound-scope6 ≡ just outbound-scope7
    outbound-scope-edge7 = refl
    outbound-scope8 : V.Runtime
    outbound-scope8 = outbound-owned-at OB.p12 S.acceptJoined false outbound-initial-ig
    outbound-scope-edge8 : V.advance (outbound-scope-event S.joinAccept) outbound-scope7 ≡ just outbound-scope8
    outbound-scope-edge8 = refl
    outbound-scope9 : V.Runtime
    outbound-scope9 = outbound-owned-at OB.p12 S.serverStopped false outbound-initial-ig
    outbound-scope-edge9 : V.advance (outbound-scope-event S.traceStopped) outbound-scope8 ≡ just outbound-scope9
    outbound-scope-edge9 = refl
    outbound-scope10 : V.Runtime
    outbound-scope10 = outbound-owned-at OB.p12 S.actionJoined false outbound-initial-ig
    outbound-scope-edge10 : V.advance (outbound-scope-event S.cancelJoinReturnedAction) outbound-scope9 ≡ just outbound-scope10
    outbound-scope-edge10 = refl
    outbound-scope11 : V.Runtime
    outbound-scope11 = outbound-owned-at OB.p12 S.igCancelRequested false outbound-initial-ig
    outbound-scope-edge11 : V.advance (outbound-scope-event S.requestIGCancel) outbound-scope10 ≡ just outbound-scope11
    outbound-scope-edge11 = refl
    outbound-scope12 : V.Runtime
    outbound-scope12 = outbound-owned-at OB.p12 S.igCancelDelivered false outbound-initial-ig
    outbound-scope-edge12 : V.advance (outbound-exit-event (E.receive E.loopBoundary OB.err)) outbound-scope11 ≡ just outbound-scope12
    outbound-scope-edge12 = refl
    outbound-scope13 : V.Runtime
    outbound-scope13 = outbound-owned-at OB.p12 S.igInactive false outbound-inactive-ig
    outbound-scope-edge13 : V.advance (outbound-scope-event S.deactivateIG) outbound-scope12 ≡ just outbound-scope13
    outbound-scope-edge13 = refl
    outbound-scope14 : V.Runtime
    outbound-scope14 = outbound-owned-at OB.p12 S.igFlushed false outbound-exited-ig
    outbound-scope-edge14 : V.advance (outbound-scope-event S.flushIG) outbound-scope13 ≡ just outbound-scope14
    outbound-scope-edge14 = refl
    outbound-ig-snapshot : V.Runtime
    outbound-ig-snapshot = record outbound-scope14 { base = record (V.base outbound-scope14)
      { server = record (K.server (V.base outbound-scope14)) { exit = record outbound-ig-caught { phase = E.traversing } } } }
    outbound-snapshot-edge : V.advance (outbound-exit-event E.captureSnapshot) outbound-scope14 ≡ just outbound-ig-snapshot
    outbound-snapshot-edge = refl
    outbound-scope15 : V.Runtime
    outbound-scope15 = outbound-owned-at OB.p12 S.igBodyExited false outbound-exited-ig
    outbound-scope-edge15 : V.advance (outbound-exit-event E.finishFinal) outbound-ig-snapshot ≡ just outbound-scope15
    outbound-scope-edge15 = refl
    outbound-scope16 : V.Runtime
    outbound-scope16 = outbound-owned-at OB.p12 S.igResultAvailable false outbound-exited-ig
    outbound-scope-edge16 : V.advance (outbound-scope-event S.publishIGResult) outbound-scope15 ≡ just outbound-scope16
    outbound-scope-edge16 = refl
    outbound-scope17 : V.Runtime
    outbound-scope17 = outbound-owned-at OB.p12 S.igJoined false outbound-exited-ig
    outbound-scope-edge17 : V.advance (outbound-scope-event S.joinIG) outbound-scope16 ≡ just outbound-scope17
    outbound-scope-edge17 = refl
    outbound-scope18 : V.Runtime
    outbound-scope18 = outbound-owned-at OB.p12 S.closingCM false outbound-exited-ig
    outbound-scope-edge18 : V.advance (outbound-scope-event S.beginCM) outbound-scope17 ≡ just outbound-scope18
    outbound-scope-edge18 = refl
    outbound-scope-events : List V.Event
    outbound-scope-events = outbound-scope-event S.returnAction ∷
      outbound-scope-event S.publishActionResult ∷
      outbound-scope-event S.selectActionWinner ∷
      outbound-scope-event S.requestAcceptCancel ∷
      outbound-scope-event S.deliverAcceptAtWait ∷
      outbound-scope-event S.closeListener ∷
      outbound-scope-event S.publishAcceptResult ∷
      outbound-scope-event S.joinAccept ∷
      outbound-scope-event S.traceStopped ∷
      outbound-scope-event S.cancelJoinReturnedAction ∷
      outbound-scope-event S.requestIGCancel ∷
      outbound-exit-event (E.receive E.loopBoundary OB.err) ∷
      outbound-scope-event S.deactivateIG ∷
      outbound-scope-event S.flushIG ∷
      outbound-exit-event E.captureSnapshot ∷
      outbound-exit-event E.finishFinal ∷
      outbound-scope-event S.publishIGResult ∷
      outbound-scope-event S.joinIG ∷
      outbound-scope-event S.beginCM ∷
      []
    outbound-scope-path : V.Runs outbound-peer26 outbound-scope-events outbound-scope18
    outbound-scope-path = V.more {a = outbound-scope-event S.returnAction} outbound-scope-edge1
      (V.more {a = outbound-scope-event S.publishActionResult} outbound-scope-edge2
      (V.more {a = outbound-scope-event S.selectActionWinner} outbound-scope-edge3
      (V.more {a = outbound-scope-event S.requestAcceptCancel} outbound-scope-edge4
      (V.more {a = outbound-scope-event S.deliverAcceptAtWait} outbound-scope-edge5
      (V.more {a = outbound-scope-event S.closeListener} outbound-scope-edge6
      (V.more {a = outbound-scope-event S.publishAcceptResult} outbound-scope-edge7
      (V.more {a = outbound-scope-event S.joinAccept} outbound-scope-edge8
      (V.more {a = outbound-scope-event S.traceStopped} outbound-scope-edge9
      (V.more {a = outbound-scope-event S.cancelJoinReturnedAction} outbound-scope-edge10
      (V.more {a = outbound-scope-event S.requestIGCancel} outbound-scope-edge11
      (V.more {a = outbound-exit-event (E.receive E.loopBoundary OB.err)} outbound-scope-edge12
      (V.more {a = outbound-scope-event S.deactivateIG} outbound-scope-edge13
      (V.more {a = outbound-scope-event S.flushIG} outbound-scope-edge14
      (V.more {a = outbound-exit-event E.captureSnapshot} outbound-snapshot-edge
      (V.more {a = outbound-exit-event E.finishFinal} outbound-scope-edge15
      (V.more {a = outbound-scope-event S.publishIGResult} outbound-scope-edge16
      (V.more {a = outbound-scope-event S.joinIG} outbound-scope-edge17
      (V.more {a = outbound-scope-event S.beginCM} outbound-scope-edge18 (V.stop)))))))))))))))))))
    outbound13 : V.Runtime
    outbound13 = outbound-owned-at OB.p13 S.closingCM false outbound-exited-ig
    outbound14 : V.Runtime
    outbound14 = outbound-owned-at OB.p14 S.closingCM false outbound-exited-ig
    outbound15 : V.Runtime
    outbound15 = outbound-owned-at OB.p15 S.closingCM false outbound-exited-ig
    outbound16 : V.Runtime
    outbound16 = outbound-owned-at OB.p16 S.closingCM false outbound-exited-ig
    outbound17 : V.Runtime
    outbound17 = outbound-owned-at OB.p17 S.closingCM false outbound-exited-ig
    outbound18 : V.Runtime
    outbound18 = outbound-owned-at OB.p18 S.closingCM false outbound-exited-ig
    outbound19 : V.Runtime
    outbound19 = outbound-owned-at OB.p19 S.closingCM false outbound-exited-ig
    outbound20 : V.Runtime
    outbound20 = outbound-owned-at OB.p20 S.closingCM false outbound-exited-ig
    outbound21 : V.Runtime
    outbound21 = outbound-owned-at OB.p21 S.closingCM false outbound-exited-ig
    outbound22 : V.Runtime
    outbound22 = outbound-owned-at OB.p22 S.closingCM false outbound-exited-ig
    outbound23 : V.Runtime
    outbound23 = outbound-owned-at OB.p23 S.closingCM false outbound-exited-ig
    outbound24 : V.Runtime
    outbound24 = outbound-owned-at OB.p24 S.closingCM false outbound-exited-ig
    outbound25 : V.Runtime
    outbound25 = outbound-owned-at OB.p25 S.closingCM false outbound-exited-ig
    outbound26 : V.Runtime
    outbound26 = outbound-owned-at OB.p26 S.closingCM false outbound-exited-ig
    outbound27 : V.Runtime
    outbound27 = outbound-owned-at OB.p27 S.closingCM false outbound-exited-ig
    outbound28 : V.Runtime
    outbound28 = outbound-owned-at OB.p28 S.closingCM false outbound-exited-ig
    call : Acquire.Action → V.Event
    call action = Resources.call-event (Resources.acquireCall OA.caller action)
    edge1 : V.advance (Resources.call-event (Resources.beginCall OA.caller OA.req)) start ≡ just outbound1
    edge1 = refl
    edge2 : V.advance (call (Acquire.select nothing)) outbound1 ≡ just outbound2
    edge2 = refl
    edge3 : V.advance (call Acquire.readCounters) outbound2 ≡ just outbound3
    edge3 = refl
    edge4 : V.advance (call Acquire.newPromise) outbound3 ≡ just outbound4
    edge4 = refl
    edge5 : V.advance (call Acquire.openOK) outbound4 ≡ just outbound5
    edge5 = refl
    edge6 : V.advance (call Acquire.configureOK) outbound5 ≡ just outbound6
    edge6 = refl
    edge7 : V.advance (call Acquire.connectOK) outbound6 ≡ just outbound7
    edge7 = refl
    edge8 : V.advance (call (Acquire.gotLocal (ConnectionManagement.Domain.local A.key₀))) outbound7 ≡ just outbound8
    edge8 = refl
    edge9 : V.advance (call Acquire.updateLocalAddress) outbound8 ≡ just outbound9
    edge9 = refl
    edge10 : V.advance (call Acquire.forkOK) outbound9 ≡ just outbound10
    edge10 = refl
    child-enters : V.advance (Resources.handler-event (H.enterHandshake OA.child)) outbound10 ≡ just outbound11
    child-enters = refl
    handoff : V.advance (V.dispatch (K.peerStep (PS.run (GP.handoff OA.caller)))) outbound11 ≡ just handed
    handoff = refl
    commit-connected : V.advance (call Acquire.commitConnected) handed ≡ just outbound12
    commit-connected = refl
    edge13 : V.advance (Joins.handler-event (W.shutdownStep Close.captureSnapshot)) outbound-scope18 ≡ just outbound13
    edge13 = refl
    edge14 : V.advance (Joins.handler-event (W.shutdownStep Close.readEntry)) outbound13 ≡ just outbound14
    edge14 = refl
    edge15 : V.advance (Joins.handler-event (W.shutdownStep Close.requestCancellation)) outbound14 ≡ just outbound15
    edge15 = refl
    edge16 : V.advance (Resources.handler-event (H.deliverShutdownHandshake OB.err)) outbound15 ≡ just outbound16
    edge16 = refl
    edge17 : V.advance (Resources.handler-event (H.publishCaught OA.child)) outbound16 ≡ just outbound17
    edge17 = refl
    edge18 : V.advance (Resources.handler-event (H.rethrowCaught OA.child)) outbound17 ≡ just outbound18
    edge18 = refl
    edge19 : V.advance (Resources.handler-event (H.enterFinalizer OA.child)) outbound18 ≡ just outbound19
    edge19 = refl
    edge20 : V.advance (Resources.handler-event (H.cleanup OA.child Cleanup.takeCleanupMap)) outbound19 ≡ just outbound20
    edge20 = refl
    edge21 : V.advance (Resources.handler-event (H.cleanup OA.child Cleanup.selectCleanupEntry)) outbound20 ≡ just outbound21
    edge21 = refl
    edge22 : V.advance (Resources.handler-event (H.cleanup OA.child Cleanup.closeHandlerSocket)) outbound21 ≡ just outbound22
    edge22 = refl
    edge23 : V.advance (Resources.handler-event (H.cleanup OA.child Cleanup.publishCleanupMap)) outbound22 ≡ just outbound23
    edge23 = refl
    edge24 : V.advance (Resources.handler-event (H.cleanup OA.child Cleanup.readCleanupCounters)) outbound23 ≡ just outbound24
    edge24 = refl
    edge25 : V.advance (Resources.handler-event (H.finishCleanup OA.child)) outbound24 ≡ just outbound25
    edge25 = refl
    edge26 : V.advance (Resources.handler-event (H.publishAsyncResult OA.child)) outbound25 ≡ just outbound26
    edge26 = refl
    edge27 : V.advance (Joins.handler-event (W.shutdownStep Close.finishTraversal)) outbound26 ≡ just outbound27
    edge27 = refl
    edge28 : V.advance (Joins.handler-event (W.shutdownStep Close.finishClose)) outbound27 ≡ just outbound28
    edge28 = refl
    before-allocation : Resources.AcquisitionRuns start
      (Resources.beginCall OA.caller OA.req ∷ Resources.acquireCall OA.caller (Acquire.select nothing) ∷ Resources.acquireCall OA.caller Acquire.readCounters ∷ []) outbound3
    before-allocation = Resources.acquisitionNext {action = Resources.beginCall OA.caller OA.req} edge1
      (Resources.acquisitionNext {action = Resources.acquireCall OA.caller (Acquire.select nothing)} edge2
      (Resources.acquisitionNext {action = Resources.acquireCall OA.caller Acquire.readCounters} edge3 Resources.acquisitionDone))
    before-fork : Resources.AcquisitionRuns outbound4
      (Resources.acquireCall OA.caller Acquire.openOK ∷ Resources.acquireCall OA.caller Acquire.configureOK ∷ Resources.acquireCall OA.caller Acquire.connectOK ∷ Resources.acquireCall OA.caller (Acquire.gotLocal (ConnectionManagement.Domain.local A.key₀)) ∷ Resources.acquireCall OA.caller Acquire.updateLocalAddress ∷ []) outbound9
    before-fork = Resources.acquisitionNext {action = Resources.acquireCall OA.caller Acquire.openOK} edge5
      (Resources.acquisitionNext {action = Resources.acquireCall OA.caller Acquire.configureOK} edge6
      (Resources.acquisitionNext {action = Resources.acquireCall OA.caller Acquire.connectOK} edge7
      (Resources.acquisitionNext {action = Resources.acquireCall OA.caller (Acquire.gotLocal (ConnectionManagement.Domain.local A.key₀))} edge8
      (Resources.acquisitionNext {action = Resources.acquireCall OA.caller Acquire.updateLocalAddress} edge9 Resources.acquisitionDone))))
    outbound-born-origin : Resources.OutboundOrigin start outbound10 OA.child
    outbound-born-origin = Resources.initialized-outbound-origin OA.caller OA.req (ident 0) A.key₀ outbound-initialized
      before-allocation refl edge4 before-fork refl edge10 V.stop
    outbound-original-descriptor : Resources.OutboundOrigin.captured outbound-born-origin ≡ OB.captured
    outbound-original-descriptor = refl
    outbound-original-promise-allocated : ident 0 ∈ Shared.promises (Resources.shared outbound4)
    outbound-original-promise-allocated = Resources.OutboundOrigin.promise-allocated outbound-born-origin
    outbound-connected-events : List V.Event
    outbound-connected-events = Resources.handler-event (H.enterHandshake OA.child) ∷ V.dispatch (K.peerStep (PS.run (GP.handoff OA.caller))) ∷ call Acquire.commitConnected ∷ []
    outbound-connected-path : V.Runs outbound10 outbound-connected-events outbound12
    outbound-connected-path = V.more {a = Resources.handler-event (H.enterHandshake OA.child)} child-enters
      (V.more {a = V.dispatch (K.peerStep (PS.run (GP.handoff OA.caller)))} handoff
      (V.more {a = call Acquire.commitConnected} commit-connected (V.stop)))
    outbound-finalizer-events : List V.Event
    outbound-finalizer-events = Joins.handler-event (W.shutdownStep Close.captureSnapshot) ∷
      Joins.handler-event (W.shutdownStep Close.readEntry) ∷
      Joins.handler-event (W.shutdownStep Close.requestCancellation) ∷
      Resources.handler-event (H.deliverShutdownHandshake OB.err) ∷
      Resources.handler-event (H.publishCaught OA.child) ∷
      Resources.handler-event (H.rethrowCaught OA.child) ∷
      Resources.handler-event (H.enterFinalizer OA.child) ∷
      Resources.handler-event (H.cleanup OA.child Cleanup.takeCleanupMap) ∷
      Resources.handler-event (H.cleanup OA.child Cleanup.selectCleanupEntry) ∷
      Resources.handler-event (H.cleanup OA.child Cleanup.closeHandlerSocket) ∷
      Resources.handler-event (H.cleanup OA.child Cleanup.publishCleanupMap) ∷
      Resources.handler-event (H.cleanup OA.child Cleanup.readCleanupCounters) ∷
      Resources.handler-event (H.finishCleanup OA.child) ∷
      []
    outbound-finalizer-path : V.Runs outbound-scope18 outbound-finalizer-events outbound25
    outbound-finalizer-path = V.more {a = Joins.handler-event (W.shutdownStep Close.captureSnapshot)} edge13
      (V.more {a = Joins.handler-event (W.shutdownStep Close.readEntry)} edge14
      (V.more {a = Joins.handler-event (W.shutdownStep Close.requestCancellation)} edge15
      (V.more {a = Resources.handler-event (H.deliverShutdownHandshake OB.err)} edge16
      (V.more {a = Resources.handler-event (H.publishCaught OA.child)} edge17
      (V.more {a = Resources.handler-event (H.rethrowCaught OA.child)} edge18
      (V.more {a = Resources.handler-event (H.enterFinalizer OA.child)} edge19
      (V.more {a = Resources.handler-event (H.cleanup OA.child Cleanup.takeCleanupMap)} edge20
      (V.more {a = Resources.handler-event (H.cleanup OA.child Cleanup.selectCleanupEntry)} edge21
      (V.more {a = Resources.handler-event (H.cleanup OA.child Cleanup.closeHandlerSocket)} edge22
      (V.more {a = Resources.handler-event (H.cleanup OA.child Cleanup.publishCleanupMap)} edge23
      (V.more {a = Resources.handler-event (H.cleanup OA.child Cleanup.readCleanupCounters)} edge24
      (V.more {a = Resources.handler-event (H.finishCleanup OA.child)} edge25 (V.stop)))))))))))))
    cleanup-events : List V.Event
    cleanup-events = outbound-connected-events ++ (outbound-peer-events ++ (outbound-scope-events ++ outbound-finalizer-events))
    through-cleanup : V.Runs outbound10 cleanup-events outbound25
    through-cleanup = Facts.append-protocols outbound-connected-path
      (Facts.append-protocols outbound-peer-path (Facts.append-protocols outbound-scope-path outbound-finalizer-path))
    cleanup-origin : Resources.OutboundOrigin start outbound25 OA.child
    cleanup-origin = Resources.extend-outbound through-cleanup outbound-born-origin
    published-origin : Resources.OutboundAtPublication start outbound25 outbound26 OA.child
    published-origin = Resources.outbound-publication-origin cleanup-origin edge26
    waiting-origin : Resources.OutboundOrigin start outbound27 OA.child
    waiting-origin = Resources.extend-outbound (V.more {a = Joins.handler-event (W.shutdownStep Close.finishTraversal)} edge27 V.stop)
      (Resources.OutboundAtPublication.following published-origin)
    waited-origin : Resources.OutboundAtWait start outbound27 outbound28 OA.child
    waited-origin = Resources.outbound-wait-origin waiting-origin edge28 (here refl)
    outbound-retained-at-wait : ResourceFacts.Facts OA.child OB.captured (Resources.shared outbound28)
    outbound-retained-at-wait = Resources.OutboundOrigin.retained (Resources.OutboundAtWait.following waited-origin)
    closed-socket-is-still-historical : lookup OA.sock (Shared.sockets (Resources.shared outbound28)) ≡ just Shared.closed
    closed-socket-is-still-historical = refl
    early-fork-refused : V.advance (call Acquire.forkOK) outbound3 ≡ nothing
    early-fork-refused = refl
    parent-needs-handoff : V.advance (call Acquire.commitConnected) outbound11 ≡ nothing
    parent-needs-handoff = refl
    early-publication-refused : V.advance (Resources.handler-event (H.publishAsyncResult OA.child)) outbound24 ≡ nothing
    early-publication-refused = refl
    waiting-before-publication : V.Runtime
    waiting-before-publication = outbound-owned-at (record OB.p25 { shutdown = OB.ownerWaiting }) S.closingCM false outbound-exited-ig
    traversal-before-publication : V.advance (Joins.handler-event (W.shutdownStep Close.finishTraversal)) outbound25 ≡ just waiting-before-publication
    traversal-before-publication = refl
    early-wait-refused : V.advance (Joins.handler-event (W.shutdownStep Close.finishClose)) waiting-before-publication ≡ nothing
    early-wait-refused = refl
    duplicate-publication-refused : V.advance (Resources.handler-event (H.publishAsyncResult OA.child)) outbound26 ≡ nothing
    duplicate-publication-refused = refl
    cm-wait-is-not-server-return : S.stage (E.base (K.server (V.base outbound28))) ≡ S.closingCM
    cm-wait-is-not-server-return = refl
    nested-coordinator-refused : V.advance (Resources.handler-event (H.shutdownStep Close.captureSnapshot)) outbound12 ≡ nothing
    nested-coordinator-refused = refl
    owned-coordinator-before-scope-close-refused : V.advance (Joins.handler-event (W.shutdownStep Close.captureSnapshot)) outbound12 ≡ nothing
    owned-coordinator-before-scope-close-refused = refl


    -- An initialized prefix now crosses peer, Server and IG dispatches while
    -- preserving the outbound caller's actual entry capture and fork identity.
    module Interference where
      private
        module General = Resources.OutboundFrontend
      public-view : V.Runtime → V.Runtime
      public-view current = record current { base = record (V.base current)
        { context = record peerContext { subsystem = record (C.subsystem peerContext) { pc = Sub.sampleInputs } } } }
        where peerContext = K.context (V.base current)
      admitted-view : V.Runtime → V.Runtime
      admitted-view current = record current { base = record (V.base current)
        { server = record updated { base = record (E.base updated)
          { workers = (A.w₀ , S.rawWorker F.r₀ S.calling 0) ∷ [] } } } }
        where
        source = K.source (V.base current)
        world = Machine.world (O.core source)
        changed = record world
          { admissions = (A.w₀ , Shared.admissionWorker F.r₀ Shared.acquireMap) ∷ Shared.admissions world
          ; sockets = (Shared.socketRef F.r₀ , Shared.admitting A.w₀) ∷ Shared.sockets world }
        updated = K.setSource (record source { core = Machine.replaceWorld (O.core source) changed }) (K.server (V.base current))
      mixed : V.Runtime → V.Runtime
      mixed current = admitted-view (public-view current)
      clock-view : V.Runtime → V.Runtime
      clock-view current = record current { base = record (V.base current)
        { server = K.setSource (record source { core = record (O.core source) { inboundGovernor = clocked } }) (K.server (V.base current)) } }
        where
        source = K.source (V.base current)
        governor = Machine.inboundGovernor (O.core source)
        clocked = record governor { continuation = IG.armInactivity 10
          ; execution = record (IG.execution governor) { lastTime = 10 } }
      publish-event admission-event clock-event : V.Event
      publish-event = V.dispatch (K.peerStep (PS.run (GP.run Sub.publishPublicState)))
      admission-event = V.dispatch (K.serverStep (E.run (S.acceptedFork A.w₀ F.r₀)))
      clock-event = V.dispatch (K.serverStep (E.run (S.run (S.runMachine (Machine.igStep (IG.captureTime 10))))))
      published-peer : V.advance publish-event start ≡ just (public-view start)
      published-peer = refl
      mixed-edge1 : V.advance (Resources.call-event (Resources.beginCall OA.caller OA.req)) (public-view start) ≡ just (public-view outbound1)
      mixed-edge1 = refl
      mixed-edge2 : V.advance (call (Acquire.select nothing)) (public-view outbound1) ≡ just (public-view outbound2)
      mixed-edge2 = refl
      mixed-edge3 : V.advance (call Acquire.readCounters) (public-view outbound2) ≡ just (public-view outbound3)
      mixed-edge3 = refl
      admitted-during-acquisition : V.advance admission-event (public-view outbound3) ≡ just (mixed outbound3)
      admitted-during-acquisition = refl
      mixed-allocation : V.advance (call Acquire.newPromise) (mixed outbound3) ≡ just (mixed outbound4)
      mixed-allocation = refl
      mixed-open : V.advance (call Acquire.openOK) (mixed outbound4) ≡ just (mixed outbound5)
      mixed-open = refl
      clock-during-acquisition : V.advance clock-event (mixed outbound5) ≡ just (clock-view (mixed outbound5))
      clock-during-acquisition = refl
      mixed-edge6 : V.advance (call (Acquire.configureOK)) (clock-view (mixed outbound5)) ≡ just (clock-view (mixed outbound6))
      mixed-edge6 = refl
      mixed-edge7 : V.advance (call (Acquire.connectOK)) (clock-view (mixed outbound6)) ≡ just (clock-view (mixed outbound7))
      mixed-edge7 = refl
      mixed-edge8 : V.advance (call (Acquire.gotLocal (ConnectionManagement.Domain.local A.key₀))) (clock-view (mixed outbound7)) ≡ just (clock-view (mixed outbound8))
      mixed-edge8 = refl
      mixed-edge9 : V.advance (call (Acquire.updateLocalAddress)) (clock-view (mixed outbound8)) ≡ just (clock-view (mixed outbound9))
      mixed-edge9 = refl
      mixed-edge10 : V.advance (call (Acquire.forkOK)) (clock-view (mixed outbound9)) ≡ just (clock-view (mixed outbound10))
      mixed-edge10 = refl
      mixed-prefix-events : List V.Event
      mixed-prefix-events = publish-event ∷ Resources.call-event (Resources.beginCall OA.caller OA.req) ∷
        call (Acquire.select nothing) ∷ call Acquire.readCounters ∷ admission-event ∷ []
      mixed-prefix : V.Runs start mixed-prefix-events (mixed outbound3)
      mixed-prefix = V.more {a = publish-event} published-peer
        (V.more {a = Resources.call-event (Resources.beginCall OA.caller OA.req)} mixed-edge1
        (V.more {a = call (Acquire.select nothing)} mixed-edge2
        (V.more {a = call Acquire.readCounters} mixed-edge3
        (V.more {a = admission-event} admitted-during-acquisition V.stop))))
      mixed-route-events : List V.Event
      mixed-route-events = call Acquire.openOK ∷ clock-event ∷ call Acquire.configureOK ∷ call Acquire.connectOK ∷
        call (Acquire.gotLocal (ConnectionManagement.Domain.local A.key₀)) ∷ call Acquire.updateLocalAddress ∷ []
      mixed-route : V.Runs (mixed outbound4) mixed-route-events (clock-view (mixed outbound9))
      mixed-route = V.more {a = call Acquire.openOK} mixed-open
        (V.more {a = clock-event} clock-during-acquisition
        (V.more {a = call Acquire.configureOK} mixed-edge6
        (V.more {a = call Acquire.connectOK} mixed-edge7
        (V.more {a = call (Acquire.gotLocal (ConnectionManagement.Domain.local A.key₀))} mixed-edge8
        (V.more {a = call Acquire.updateLocalAddress} mixed-edge9 V.stop)))))
      mixed-origin : General.History start (clock-view (mixed outbound10)) OA.child
      mixed-origin = General.initialize-history OA.caller OA.req (ident 0) A.key₀ outbound-initialized
        mixed-prefix refl mixed-allocation mixed-route refl mixed-edge10 V.stop
      mixed-original-descriptor : General.History.captured mixed-origin ≡ OB.captured
      mixed-original-descriptor = refl
      mixed-resource-facts : ResourceFacts.Facts OA.child OB.captured (Resources.shared (clock-view (mixed outbound10)))
      mixed-resource-facts = General.History.retained mixed-origin
      independent-admission-remains : lookup A.w₀ (Shared.admissions (Resources.shared (clock-view (mixed outbound10)))) ≡
        just (Shared.admissionWorker F.r₀ Shared.acquireMap)
      independent-admission-remains = refl
      peer-progress-remains : C.SubContext.pc (C.subsystem (K.context (V.base (clock-view (mixed outbound10))))) ≡ Sub.sampleInputs
      peer-progress-remains = refl
      ig-progress-remains : IG.continuation (Machine.inboundGovernor (O.core (K.source (V.base (clock-view (mixed outbound10)))))) ≡ IG.armInactivity 10
      ig-progress-remains = refl
      mixed-child-enters : V.advance (Resources.handler-event (H.enterHandshake OA.child))
        (clock-view (mixed outbound10)) ≡ just (clock-view (mixed outbound11))
      mixed-child-enters = refl
      mixed-child-history : General.History start (clock-view (mixed outbound11)) OA.child
      mixed-child-history = General.extend-history (V.more {a = Resources.handler-event (H.enterHandshake OA.child)} mixed-child-enters V.stop) mixed-origin
      duplicate-admission-refused : V.advance admission-event (mixed outbound3) ≡ nothing
      duplicate-admission-refused = refl
      duplicate-clock-refused : V.advance clock-event (clock-view (mixed outbound5)) ≡ nothing
      duplicate-clock-refused = refl
      raw-acquisition-alias-refused : V.advance
        (Joins.handler-event (Resources.outbound-physical-action (O.acquire OA.caller Acquire.newPromise))) (mixed outbound3) ≡ nothing
      raw-acquisition-alias-refused = refl
      premature-mixed-fork-refused : V.advance (call Acquire.forkOK) (mixed outbound3) ≡ nothing
      premature-mixed-fork-refused = refl

      -- The generalized constructor also retains the already checked owned
      -- shutdown history through the same physical result and CM-wait APIs.
      general-cleanup-history : General.History start outbound25 OA.child
      general-cleanup-history = General.initialize-history OA.caller OA.req (ident 0) A.key₀ outbound-initialized
        (Resources.acquisition-events before-allocation) refl edge4
        (Resources.acquisition-events before-fork) refl edge10 through-cleanup
      general-publication : General.AtResult start outbound25 outbound26 OA.child
      general-publication = General.publication-history general-cleanup-history edge26
      general-waiting-history : General.History start outbound27 OA.child
      general-waiting-history = General.extend-history
        (V.more {a = Joins.handler-event (W.shutdownStep Close.finishTraversal)} edge27 V.stop)
        (General.AtResult.following general-publication)
      general-wait : General.AtCMWait start outbound27 outbound28 OA.child
      general-wait = General.wait-history general-waiting-history edge28 (here refl)
      general-wait-resources : ResourceFacts.Facts OA.child OB.captured (Resources.shared outbound28)
      general-wait-resources = General.History.retained (General.AtCMWait.following general-wait)

  -- Current physical membership now discovers its own earlier fork. These use
  -- initialized frontend histories, not supplied resource-origin certificates.
  module HandlerBirthBackingChecks where
    open import Data.List using (take; _++_)
    import ConnectionManagement.Properties.HandlerBirthBacking as BirthBacking
    import ConnectionManagement.Properties.ServerPeersHandlerResources as ResourcesModel
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.CSP.OutboundAdmission as OA
    import ConnectionManagement.Negative.OutboundHandlerSupervision as OB
    private
      module Back = BirthBacking.Frontend I.bearerClosed Prior.classify capability
      module Resources = ResourcesModel.Frontend I.bearerClosed Prior.classify capability
      module In = HandlerResourceOriginChecks
      module Out = OutboundHandlerResourceOriginChecks
      module W = N.W
    inbound-current-thread : lookup A.child₀ (B.threads (Back.physical-state (wrap (base F.p5)))) ≡
      just (H.handlerThread I.captured H.maskedSetup)
    inbound-current-thread = refl
    abstract
      inbound-backing : Back.Backing initial (wrap (base F.p5)) (take 7 prefixActions) A.child₀ I.captured
      inbound-backing = Back.initialized-birth initializer In.forkPrefix inbound-current-thread
    -- The public output includes both an actual frontend event and its enabled
    -- physical operation, tied to the same original descriptor.
    inbound-physical-capture : lookup A.child₀ (BirthBacking.physical (Back.ForkStep.target (Back.Backing.operation inbound-backing))) ≡ just I.captured
    inbound-physical-capture = Back.Backing.at-physical-fork inbound-backing
    outbound-birth-events : List V.Event
    outbound-birth-events = Resources.call-event (Resources.beginCall OA.caller OA.req) ∷
      Out.call (Acquire.select nothing) ∷ Out.call Acquire.readCounters ∷ Out.call Acquire.newPromise ∷
      Out.call Acquire.openOK ∷ Out.call Acquire.configureOK ∷ Out.call Acquire.connectOK ∷
      Out.call (Acquire.gotLocal (ConnectionManagement.Domain.local A.key₀)) ∷ Out.call Acquire.updateLocalAddress ∷ Out.call Acquire.forkOK ∷ []
    outbound-birth-path : V.Runs Out.start outbound-birth-events Out.outbound10
    outbound-birth-path = V.more Out.edge1 (V.more Out.edge2 (V.more Out.edge3 (V.more Out.edge4
      (V.more Out.edge5 (V.more Out.edge6 (V.more Out.edge7 (V.more Out.edge8 (V.more Out.edge9 (V.more Out.edge10 V.stop)))))))))
    outbound-through-cleanup-events : List V.Event
    outbound-through-cleanup-events = outbound-birth-events ++ Out.cleanup-events
    outbound-through-cleanup : V.Runs Out.start outbound-through-cleanup-events Out.outbound25
    outbound-through-cleanup = Facts.append-protocols outbound-birth-path Out.through-cleanup
    outbound-current-thread : lookup OA.child (B.threads (Back.physical-state Out.outbound25)) ≡
      just (H.handlerThread OB.captured (H.cleanupComplete OB.err Shared.cleanupNormal))
    outbound-current-thread = refl
    abstract
      outbound-backing : Back.Backing Out.start Out.outbound25 outbound-through-cleanup-events OA.child OB.captured
      outbound-backing = Back.initialized-birth Out.outbound-initialized outbound-through-cleanup outbound-current-thread
    outbound-physical-capture : lookup OA.child (BirthBacking.physical (Back.ForkStep.target (Back.Backing.operation outbound-backing))) ≡ just OB.captured
    outbound-physical-capture = Back.Backing.at-physical-fork outbound-backing
    -- Freshness and refusal controls use actual guards/initializers.
    repeated-outbound-fork-refused : V.advance (Out.call Acquire.forkOK) Out.outbound10 ≡ nothing
    repeated-outbound-fork-refused = refl
    outbound-child-not-fresh : B.freshChild OA.child (Back.physical-state Out.outbound10) ≡ false
    outbound-child-not-fresh = refl
    inbound-child-not-fresh : B.freshChild A.child₀ (Back.physical-state (wrap (base F.p5))) ≡ false
    inbound-child-not-fresh = refl
    adoption-source : O.Configuration
    adoption-source = record original { core = Machine.replaceWorld (O.core original)
      (record world { admissions = []; sockets = [] }) }
      where
      original = K.source (V.base Out.outbound10)
      world = Machine.world (O.core original)
    raw-handler-adoption-refused : H.initial (O.core adoption-source) ≡ nothing
    raw-handler-adoption-refused = refl
    initialized-handler-adoption-refused : V.initialize adoption-source L.settings ≡ nothing
    initialized-handler-adoption-refused = refl


    -- The same discovered birth crosses all three shutdown boundaries. Opaque
    -- runs and existing observations are reused instead of replaying a system.
    module ShutdownBatch where
      open import Data.List using (take; drop; _++_)
      open import Data.List.Relation.Unary.Any using (here)
      open import Data.Product using (Σ; _×_)
      open import Relation.Binary.PropositionalEquality using (subst)
      import ConnectionManagement.Properties.ServerPeersMonitorJoins as BirthJoins
      import ConnectionManagement.MuxHandlerExit as HandlerExitModel
      import ConnectionManagement.Rules.CMShutdown as Close
      private
        module Shutdown = ResourcesModel.BackedShutdown I.bearerClosed Prior.classify capability using (InitializedShutdown; birth-command; initialized-handshake-shutdown; result-at-final-wait; same-birth-command; wait-events)
        module Joins = BirthJoins.Frontend I.bearerClosed Prior.classify capability using (handler-event; physical)
      before-scope-events : List V.Event
      before-scope-events = outbound-birth-events ++ (Out.outbound-connected-events ++ (Out.outbound-peer-events ++ Out.outbound-scope-events))
      acknowledgement-prefix-events : List V.Event
      acknowledgement-prefix-events = before-scope-events ++ take 3 Out.outbound-finalizer-events
      cleanup-after-ack-events : List V.Event
      cleanup-after-ack-events = drop 4 Out.outbound-finalizer-events
      traversal-events : List V.Event
      traversal-events = Joins.handler-event (W.shutdownStep Close.finishTraversal) ∷ []
      abstract
        before-scope-run : V.Runs Out.start before-scope-events Out.outbound-scope18
        before-scope-run = Facts.append-protocols outbound-birth-path
          (Facts.append-protocols Out.outbound-connected-path (Facts.append-protocols Out.outbound-peer-path Out.outbound-scope-path))
        before-delivery-run : V.Runs Out.outbound-scope18 (take 3 Out.outbound-finalizer-events) Out.outbound15
        before-delivery-run = V.more {t = Out.outbound13} {a = Joins.handler-event (W.shutdownStep Close.captureSnapshot)} Out.edge13
          (V.more {t = Out.outbound14} {a = Joins.handler-event (W.shutdownStep Close.readEntry)} Out.edge14
          (V.more {t = Out.outbound15} {a = Joins.handler-event (W.shutdownStep Close.requestCancellation)} Out.edge15 V.stop))
        acknowledgement-prefix : V.Runs Out.start acknowledgement-prefix-events Out.outbound15
        acknowledgement-prefix = Facts.append-protocols before-scope-run before-delivery-run
        delivered-prefix : V.Runs Out.outbound-scope18 (take 4 Out.outbound-finalizer-events) Out.outbound16
        delivered-prefix = Facts.append-protocols before-delivery-run
          (V.more {t = Out.outbound16} {a = Resources.handler-event (H.deliverShutdownHandshake OB.err)} Out.edge16 V.stop)
        cleanup-after-ack : V.Runs Out.outbound16 cleanup-after-ack-events Out.outbound25
        cleanup-after-ack = Resources.discard-prefix {suffix = cleanup-after-ack-events} delivered-prefix Out.outbound-finalizer-path
        traversal-run : V.Runs Out.outbound26 traversal-events Out.outbound27
        traversal-run = V.more {t = Out.outbound27} {a = Joins.handler-event (W.shutdownStep Close.finishTraversal)} Out.edge27 V.stop
      physical-before-ack : lookup OA.child (B.threads (Back.physical-state Out.outbound15)) ≡ just (H.handlerThread OB.captured H.handshaking)
      physical-before-ack = refl
      awaiting-this-worker : Close.phase (H.shutdown (Resources.raw-view Out.outbound15)) ≡ Close.awaitDelivery (ident 0) OA.child
      awaiting-this-worker = refl
      abstract
        shutdown : Shutdown.InitializedShutdown Out.start Out.outbound28 OA.child OB.captured
        shutdown = Shutdown.initialized-handshake-shutdown
          {c = O.initial (Machine.initial Shared.responderMode F.empty)} {g = L.settings}
          {start = Out.start} {beforeAck = Out.outbound15} {afterAck = Out.outbound16}
          {beforeResult = Out.outbound25} {afterResult = Out.outbound26} {beforeWait = Out.outbound27} {current = Out.outbound28}
          {prefix = acknowledgement-prefix-events} {cleanup = cleanup-after-ack-events} {traversal = traversal-events}
          {entry = ident 0} {w = OA.child} {thread = H.handlerThread OB.captured H.handshaking} {err = OB.err}
          Out.outbound-initialized acknowledgement-prefix physical-before-ack awaiting-this-worker
          Out.edge16 cleanup-after-ack Out.edge26 traversal-run Out.edge28 (here refl)
        shutdown-wait-position : Shutdown.InitializedShutdown.beforeWait shutdown ≡ Out.outbound27
        shutdown-wait-position = refl
      -- The final certificate recovers the real current physical thread without
      -- a new lookup premise at publication or CM's wait.
      physical-at-final-wait : Σ H.Thread (λ thread → lookup OA.child (B.threads (Back.physical-state Out.outbound28)) ≡ just thread × H.captured thread ≡ OB.captured)
      physical-at-final-wait = Back.current-thread (Shutdown.InitializedShutdown.at-wait shutdown)
      same-discovered-fork : Shutdown.birth-command (Shutdown.InitializedShutdown.at-wait shutdown) ≡ Shutdown.birth-command (Shutdown.InitializedShutdown.birth shutdown)
      same-discovered-fork = Shutdown.same-birth-command shutdown
      final-prewait-result : HandlerExitModel.resultReady I.bearerClosed OA.child (Joins.physical Out.outbound27) ≡ true
      final-prewait-result = subst (λ state → HandlerExitModel.resultReady I.bearerClosed OA.child (Joins.physical state) ≡ true)
        shutdown-wait-position (Shutdown.result-at-final-wait shutdown)
      acknowledgement-is-not-a-result : HandlerExitModel.resultReady I.bearerClosed OA.child (Joins.physical Out.outbound16) ≡ false
      acknowledgement-is-not-a-result = refl
      publication-still-required : V.advance (Joins.handler-event (W.shutdownStep Close.finishClose)) Out.waiting-before-publication ≡ nothing
      publication-still-required = Out.early-wait-refused
      duplicate-publication-refused : V.advance (Resources.handler-event (H.publishAsyncResult OA.child)) Out.outbound26 ≡ nothing
      duplicate-publication-refused = Out.duplicate-publication-refused
      cm-wait-still-is-not-server-return : S.stage (E.base (K.server (V.base Out.outbound28))) ≡ S.closingCM
      cm-wait-still-is-not-server-return = Out.cm-wait-is-not-server-return


  -- Initialized countercontrols keep entry targets distinct from collection.
  module SameEntryFailedForkControl where
    open import Data.List.Membership.Propositional using (_∈_)
    open import Data.Product using (Σ; _×_)
    open import Data.List.Relation.Unary.Any using (here)
    import ConnectionManagement.Negative.ServerAdmissionPrefixFixtures as PrefixFixtures
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.Properties.HandlerBirthBacking as Birth
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
    import ConnectionManagement.Rules.CMShutdown as Close
    private
      module Same = PrefixFixtures 10 A.key₀ using (binding; empty; err; lease₁; live; one; p1; p2; p3; p4; p5; p6; ps₀; r₀; r₁; start; two; unneg)
      module Back = Birth.Frontend I.bearerClosed Prior.classify capability using (physical-state)
      module Joins = MonitorJoins.Frontend I.bearerClosed Prior.classify capability using (physical)
      module W = N.W using (State; acknowledgeFinished; deliverShutdownMux; physical; setShutdown; shutdown; shutdownStep; step)
    -- SAME key, distinct caller/child/socket tokens, fixed hard limit ten.
    -- Same.start is empty, so initialization does not assume an old map entry.
    frontendAt : S.State → V.Runtime
    frontendAt s = V.runtime (K.combined (E.igExitState s E.emptyExit) k0) V.empty
    reuseStart : V.Runtime
    reuseStart = frontendAt Same.start
    reuseInitialized : V.initialize (O.initial (Machine.initial Shared.responderMode Same.empty)) L.settings ≡ just reuseStart
    reuseInitialized = refl
    event : S.Action → V.Event
    event a = V.dispatch (K.serverStep (E.run a))
    step1 : V.advance (event (S.acceptedFork A.w₀ Same.r₀)) reuseStart ≡ just (frontendAt Same.one)
    step1 = refl
    step2 : V.advance (event (S.acceptedFork A.w₁ Same.r₁)) (frontendAt Same.one) ≡ just (frontendAt Same.two)
    step2 = refl
    step3 : V.advance (event (admit A.w₀ Admission.take)) (frontendAt Same.two) ≡ just (frontendAt Same.p1)
    step3 = refl
    step4 : V.advance (event (admit A.w₀ Admission.countLimit)) (frontendAt Same.p1) ≡ just (frontendAt Same.p2)
    step4 = refl
    step5 : V.advance (event (admit A.w₀ Admission.allocatePromise)) (frontendAt Same.p2) ≡ just (frontendAt Same.p3)
    step5 = refl
    step6 : V.advance (event (admit A.w₀ Admission.chooseEntry)) (frontendAt Same.p3) ≡ just (frontendAt Same.p4)
    step6 = refl
    step7 : V.advance (event (admit A.w₀ Admission.fork)) (frontendAt Same.p4) ≡ just (frontendAt Same.p5)
    step7 = refl
    step8 : V.advance (event (admit A.w₀ Admission.putMapBack)) (frontendAt Same.p5) ≡ just (frontendAt Same.p6)
    step8 = refl
    -- Keep the first caller at its post-publication counter read. The second
    -- caller locks the SAME binding and overwrites that mutable EntryId.
    originalPC : Shared.AdmissionPC
    originalPC = Shared.countPublished (ident 0) (ident 0)
    reuseAfter : Shared.ConnectionState → Shared.MapCell → Shared.AdmissionPC →
      List PromiseId → Nat.ℕ → S.State
    reuseAfter st cell pc ps n = Same.live st cell originalPC pc ps n [] []
      (Shared.admitting A.w₁) IG.initial H.maskedSetup []
    secondPromises : List PromiseId
    secondPromises = ident 1 ∷ Same.ps₀
    b1 b2 b3 b4 f1 f2 : S.State
    b1 = reuseAfter Same.unneg (Shared.taken A.w₁) (Shared.count Same.lease₁) Same.ps₀ 1
    b2 = reuseAfter Same.unneg (Shared.taken A.w₁) (Shared.prepare Same.lease₁) Same.ps₀ 1
    b3 = reuseAfter Same.unneg (Shared.taken A.w₁) (Shared.selectEntry Same.lease₁ (ident 1)) secondPromises 2
    overwritten : Shared.ConnectionState
    overwritten = Shared.unnegotiated inbound A.key₀ A.child₁
    b4 = reuseAfter overwritten (Shared.taken A.w₁) (Shared.forkHandler Same.lease₁ (ident 1) (ident 0)) secondPromises 2
    f1 = reuseAfter overwritten (Shared.taken A.w₁) (Shared.reject Same.lease₁ Shared.forkFailed) secondPromises 2
    f2 = reuseAfter overwritten (Shared.full Same.binding) (Shared.closeSocket Shared.forkFailed) secondPromises 2
    step9 : V.advance (event (admit A.w₁ Admission.take)) (frontendAt Same.p6) ≡ just (frontendAt b1)
    step9 = refl
    step10 : V.advance (event (admit A.w₁ Admission.countLimit)) (frontendAt b1) ≡ just (frontendAt b2)
    step10 = refl
    step11 : V.advance (event (admit A.w₁ Admission.allocatePromise)) (frontendAt b2) ≡ just (frontendAt b3)
    step11 = refl
    step12 : V.advance (event (admit A.w₁ Admission.chooseEntry)) (frontendAt b3) ≡ just (frontendAt b4)
    step12 = refl
    step13 : V.advance (event (admit A.w₁ Admission.failFork)) (frontendAt b4) ≡ just (frontendAt f1)
    step13 = refl
    step14 : V.advance (event (admit A.w₁ Admission.restore)) (frontendAt f1) ≡ just (frontendAt f2)
    step14 = refl
    prefix : List V.Event
    prefix = event (S.acceptedFork A.w₀ Same.r₀) ∷ event (S.acceptedFork A.w₁ Same.r₁) ∷
      event (admit A.w₀ Admission.take) ∷ event (admit A.w₀ Admission.countLimit) ∷
      event (admit A.w₀ Admission.allocatePromise) ∷ event (admit A.w₀ Admission.chooseEntry) ∷
      event (admit A.w₀ Admission.fork) ∷ event (admit A.w₀ Admission.putMapBack) ∷
      event (admit A.w₁ Admission.take) ∷ event (admit A.w₁ Admission.countLimit) ∷
      event (admit A.w₁ Admission.allocatePromise) ∷ event (admit A.w₁ Admission.chooseEntry) ∷
      event (admit A.w₁ Admission.failFork) ∷ event (admit A.w₁ Admission.restore) ∷ []
    abstract
      same-entry-failed-fork-restored : V.Runs reuseStart prefix (frontendAt f2)
      same-entry-failed-fork-restored = V.more step1 (V.more step2 (V.more step3 (V.more step4
        (V.more step5 (V.more step6 (V.more step7 (V.more step8 (V.more step9 (V.more step10
        (V.more step11 (V.more step12 (V.more step13 (V.more step14 V.stop)))))))))))))
    restored-map-still-names-the-same-entry : Shared.lookupConnection A.key₀ (Shared.savedMap Same.lease₁) ≡ just (ident 0)
    restored-map-still-names-the-same-entry = refl
    restored-actual-map : Shared.mapCell (Shared.cm (S.shared f2)) ≡ Shared.full Same.binding
    restored-actual-map = refl
    restore-retains-overwrite : lookup (ident 0) (Shared.entries (Shared.cm (S.shared f2))) ≡ just overwritten
    restore-retains-overwrite = refl
    old-handler-still-physical : lookup A.child₀ (B.threads (Back.physical-state (frontendAt f2))) ≡ just (H.handlerThread I.captured H.maskedSetup)
    old-handler-still-physical = refl
    failed-new-child-not-physical : lookup A.child₁ (B.threads (Back.physical-state (frontendAt f2))) ≡ nothing
    failed-new-child-not-physical = refl
    failed-new-child-not-in-handler-heap : lookup A.child₁ (Shared.handlers (S.shared f2)) ≡ nothing
    failed-new-child-not-in-handler-heap = refl
    entry-target-is-unforked-child : Close.getConnThread overwritten ≡ just A.child₁
    entry-target-is-unforked-child = refl
    -- Pending fork b4 has exactly the same unbacked entry target. Its map is
    -- taken, so snapshot capture cannot yet proceed; failed restore exposes it.
    pending-new-child-not-physical : lookup A.child₁ (B.threads (Back.physical-state (frontendAt b4))) ≡ nothing
    pending-new-child-not-physical = refl
    -- Keep raw-coordinator checks separate: frontend capture remains gated on
    -- actual Server closingCM, which this finite prefix has not reached.
    raw : W.State
    raw = Joins.physical (frontendAt f2)
    snapshot read rawRequested : W.State
    snapshot = W.setShutdown (Close.shutdownState Close.reading (ident 0 ∷ []) (ident 0 ∷ []) []) raw
    read = W.setShutdown (Close.shutdownState (Close.sendReady (ident 0) A.child₁) (ident 0 ∷ []) [] []) raw
    rawRequested = W.setShutdown (Close.shutdownState (Close.awaitDelivery (ident 0) A.child₁) (ident 0 ∷ []) [] []) raw
    raw-capture : W.step (W.shutdownStep Close.captureSnapshot) raw ≡ just snapshot
    raw-capture = refl
    raw-read : W.step (W.shutdownStep Close.readEntry) snapshot ≡ just read
    raw-read = refl
    raw-request : W.step (W.shutdownStep Close.requestCancellation) read ≡ just rawRequested
    raw-request = refl
    no-fabricated-ack : W.step (W.shutdownStep Close.acknowledgeDelivery) rawRequested ≡ nothing
    no-fabricated-ack = refl
    no-finished-ack : W.step W.acknowledgeFinished rawRequested ≡ nothing
    no-finished-ack = refl
    no-prehandshake-delivery : H.step (H.deliverShutdownHandshake Same.err) (B.view (W.physical rawRequested)) ≡ nothing
    no-prehandshake-delivery = refl
    no-blocked-setup-delivery : H.step (H.deliverShutdownBlockedSetup Same.err) (B.view (W.physical rawRequested)) ≡ nothing
    no-blocked-setup-delivery = refl
    no-mux-delivery : W.step (W.deliverShutdownMux Same.err) rawRequested ≡ nothing
    no-mux-delivery = refl
    raw-selected-is-not-collected : Close.collected (W.shutdown rawRequested) ≡ []
    raw-selected-is-not-collected = refl
    -- Expected additional raw H delivery controls all refuse child₁ because its
    -- physical lookup is absent. Do not bypass frontend closingCM via a record
    -- stage update and call that an initialized frontend shutdown witness.


  module PreloadedEntryCountercontrol where
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.Properties.HandlerBirthBacking as Birth
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
    import ConnectionManagement.Rules.CMShutdown as Close
    private
      module Back = Birth.Frontend I.bearerClosed Prior.classify capability using (physical-state)
      module Joins = MonitorJoins.Frontend I.bearerClosed Prior.classify capability using (handler-event; physical)
      module W = N.W using (shutdown; shutdownStep)
    named : WorkerId
    named = ident 999
    seeded : Shared.State
    seeded = record F.empty { cm = Shared.cmStore
      (Shared.full (Shared.insertConnection A.key₀ (ident 0) []))
      ((ident 0 , Shared.unnegotiated inbound A.key₀ named) ∷ []) 1 }
    configuration : O.Configuration
    configuration = O.initial (Machine.initial Shared.responderMode seeded)
    preloaded : V.Runtime
    preloaded = V.runtime (K.combined
      (E.igExitState (S.serverState (F.wrap (I.pre (Machine.initial Shared.responderMode seeded))) [] S.serving true) E.emptyExit)
      k0) V.empty
    accepts-unbacked-entry : V.initialize configuration L.settings ≡ just preloaded
    accepts-unbacked-entry = refl
    named-worker-not-physical : lookup named (B.threads (Back.physical-state preloaded)) ≡ nothing
    named-worker-not-physical = refl
    -- Successful initialization is NOT whole-CM-entry coverage. It starts the
    -- coordinator empty and permits no direct acknowledgment alias.
    initialized-collected-empty : Close.collected (W.shutdown (Joins.physical preloaded)) ≡ []
    initialized-collected-empty = refl
    no-early-frontend-capture : V.advance (Joins.handler-event (W.shutdownStep Close.captureSnapshot)) preloaded ≡ nothing
    no-early-frontend-capture = refl
    -- Optional raw-local suffix to show why selected/awaited is weaker than
    -- collected: use SameEntryFailedForkControl's snapshot/read/request shape
    -- with named = ident 999. It must still fail delivery/result guards.


  -- Collected membership discovers a physical thread and its original fork.
  module InitializedCollectedExamples where
    open import Data.Product using (Σ; _×_)
    open import Data.List.Membership.Propositional using (_∈_)
    open import Data.List.Relation.Unary.Any using (here)
    import ConnectionManagement.Properties.ServerPeersHandlerResources as ResourceModel
    import ConnectionManagement.Properties.CollectedHandlerBirth as CombinedBacking
    import ConnectionManagement.Properties.HandlerBirthBacking as Birth
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as MonitorJoins
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.CSP.OutboundAdmission as OA
    import ConnectionManagement.Rules.CMShutdown as Close
    private
      module Resources = ResourceModel.Frontend I.bearerClosed Prior.classify capability using (handler-event)
      module CB = CombinedBacking.Frontend I.bearerClosed Prior.classify capability using (initialized-member; initialized-birth)
      module Back = Birth.Frontend I.bearerClosed Prior.classify capability using (Backing; physical-state)
      module Joins = MonitorJoins.Frontend I.bearerClosed Prior.classify capability using (handler-event; physical; server-event; server-runs)
      module D = Reactivation.Shutdown using (finalCM; handlerFinishEdge11)
      module In = HandlerResourceOriginChecks using (entryPrefix; initialized-entry)
      module Wait = CMResultLifecycleChecks using (actual-wait-prefix; waitPrefix)
      module Out = OutboundHandlerResourceOriginChecks using (edge26; edge27; edge28; outbound-initialized; outbound25; outbound28; start)
      module OldBirth = HandlerBirthBackingChecks using (outbound-through-cleanup; outbound-through-cleanup-events)
      module W = N.W using (shutdown; shutdownStep)
    -- The old inbound history reaches CM entry through actual initialized
    -- monitor/scopes/callback/Server cleanup; then reuse its opaque finalizer path.
    inbound-events : List V.Event
    inbound-events = In.entryPrefix ++ (map Joins.server-event Wait.waitPrefix ++
      (Joins.handler-event (W.shutdownStep Close.finishClose) ∷ []))
    abstract
      inbound-through-final-wait : V.Runs initial inbound-events D.finalCM
      inbound-through-final-wait = Facts.append-protocols In.initialized-entry
        (Facts.append-protocols (Joins.server-runs Wait.actual-wait-prefix)
          (V.more {a = Joins.handler-event (W.shutdownStep Close.finishClose)}
            D.handlerFinishEdge11 V.stop))
    inbound-collected : A.child₀ ∈ Close.collected (W.shutdown (Joins.physical D.finalCM))
    inbound-collected = here refl
    abstract
      inbound-derived-membership : Σ H.Thread (λ thread →
        lookup A.child₀ (B.threads (Back.physical-state D.finalCM)) ≡ just thread)
      inbound-derived-membership = CB.initialized-member initializer
        inbound-through-final-wait inbound-collected
      inbound-derived-birth : Σ Shared.HandlerStart (λ captured →
        Back.Backing initial D.finalCM inbound-events A.child₀ captured)
      inbound-derived-birth = CB.initialized-birth initializer
        inbound-through-final-wait inbound-collected
    -- The backing records its actual selected fork and descriptor; neither
    -- application supplies a physical lookup or a resource-origin certificate.

    outbound-final-events : List V.Event
    outbound-final-events =
      Resources.handler-event (H.publishAsyncResult OA.child) ∷
      Joins.handler-event (W.shutdownStep Close.finishTraversal) ∷
      Joins.handler-event (W.shutdownStep Close.finishClose) ∷ []
    outbound-events : List V.Event
    outbound-events = OldBirth.outbound-through-cleanup-events ++ outbound-final-events
    abstract
      outbound-final-run : V.Runs Out.outbound25 outbound-final-events Out.outbound28
      outbound-final-run = V.more Out.edge26 (V.more Out.edge27 (V.more Out.edge28 V.stop))
      outbound-through-final-wait : V.Runs Out.start outbound-events Out.outbound28
      outbound-through-final-wait = Facts.append-protocols OldBirth.outbound-through-cleanup outbound-final-run
    outbound-collected : OA.child ∈ Close.collected (W.shutdown (Joins.physical Out.outbound28))
    outbound-collected = here refl
    abstract
      outbound-derived-membership : Σ H.Thread (λ thread →
        lookup OA.child (B.threads (Back.physical-state Out.outbound28)) ≡ just thread)
      outbound-derived-membership = CB.initialized-member Out.outbound-initialized
        outbound-through-final-wait outbound-collected
      outbound-derived-birth : Σ Shared.HandlerStart (λ captured →
        Back.Backing Out.start Out.outbound28 outbound-events OA.child captured)
      outbound-derived-birth = CB.initialized-birth Out.outbound-initialized
        outbound-through-final-wait outbound-collected


  -- Initializer scope and witnessed resource histories with enabled gaps.
  module PreloadedAcquisitionForkControl where
    open import Data.List.Membership.Propositional using (_∈_)
    open import Data.Empty using (⊥)
    import ConnectionManagement.OutboundHandlerSupervision as B
    import ConnectionManagement.Properties.HandlerResourceFacts as ResourceFacts
    import ConnectionManagement.Rules.CMShutdown as Close
    -- Direct model projection keeps the large birth proof out of this control.
    controlPhysical : V.Runtime → B.State
    controlPhysical s = N.W.physical (N.R.base (N.raw (S.base (E.base (K.server (V.base s))))))
    preCaller preChild : WorkerId
    preCaller = ident 10
    preChild = ident 11
    preSocket : SocketId
    preSocket = ident 10
    missingEntry : EntryId
    missingEntry = ident 99
    missingPromise : PromiseId
    missingPromise = ident 88
    preRequest : Acquire.Request
    preRequest = Acquire.acquireRequest (remote A.key₀) preChild preSocket outbound nothing
    preDescriptor : Shared.HandlerStart
    preDescriptor = Shared.handlerStart missingEntry preSocket missingPromise A.key₀

    -- Entry zero names the fresh child, but is NOT the descriptor's entry99.
    -- All handler/socket/promise tables remain empty at initialization.
    seededWorld : Shared.State
    seededWorld = record F.empty
      { cm = Shared.cmStore (Shared.full (Shared.insertConnection A.key₀ (ident 0) []))
        ((ident 0 , Shared.unnegotiated inbound A.key₀ preChild) ∷ []) 1 }
    seededCore : Machine.Configuration
    seededCore = Machine.initial Shared.responderMode seededWorld
    seededConfiguration : O.Configuration
    seededConfiguration = record (O.initial seededCore)
      { acquiring = (preCaller , Acquire.frame preRequest (Acquire.forkHandler missingEntry missingPromise A.key₀)) ∷ [] }

    -- Flat physical adapter, source and context snapshots. The post-fork origin
    -- and forkedBeforeHandoff region are actual dispatch effects, not assumptions.
    renderPreloaded : B.State → Store WorkerId Provenance → Store WorkerId Cancel.Context → V.Runtime
    renderPreloaded physical origins regions = V.runtime
      (K.combined
        (E.igExitState
          (S.serverState
            (F.wrap (P.protocolState (U.supervised physical origins []) [] [])) [] S.serving true)
          E.emptyExit)
        (record k0 { regions = regions })) V.empty
    preloadedStart : V.Runtime
    preloadedStart = renderPreloaded (B.supervised seededConfiguration [] Close.initialState) [] []
    preloadedInitializer : V.initialize seededConfiguration L.settings ≡ just preloadedStart
    preloadedInitializer = refl
    preloadedForkEvent : V.Event
    preloadedForkEvent = V.dispatch (K.coreStep (O.acquire preCaller Acquire.forkOK))
    preloadedCallerAllowed : K.coreAllowed (O.acquire preCaller Acquire.forkOK) (V.base preloadedStart) ≡ true
    preloadedCallerAllowed = refl
    preloadedChildFresh : B.freshChild preChild (controlPhysical preloadedStart) ≡ true
    preloadedChildFresh = refl

    forkedWorld : Shared.State
    forkedWorld = record seededWorld
      { handlers = (preChild , preDescriptor) ∷ []
      ; sockets = (preSocket , Shared.handling preChild) ∷ [] }
    forkedConfiguration : O.Configuration
    forkedConfiguration = record seededConfiguration
      { core = Machine.replaceWorld seededCore forkedWorld
      ; acquiring = (preCaller , Acquire.frame preRequest (Acquire.connectedCommit missingEntry missingPromise A.key₀)) ∷ [] }
    preloadedForked : V.Runtime
    preloadedForked = renderPreloaded
      (B.supervised forkedConfiguration ((preChild , H.handlerThread preDescriptor H.maskedSetup) ∷ []) Close.initialState)
      ((preChild , outbound) ∷ []) ((preCaller , Cancel.forkedBeforeHandoff) ∷ [])
    preloadedActualFork : V.advance preloadedForkEvent preloadedStart ≡ just preloadedForked
    preloadedActualFork = refl
    abstract
      preloadedForkRun : V.Runs preloadedStart (preloadedForkEvent ∷ []) preloadedForked
      preloadedForkRun = V.more {a = preloadedForkEvent} preloadedActualFork V.stop
    preloadedPhysicalDescriptor : lookup preChild (B.threads (controlPhysical preloadedForked)) ≡
      just (H.handlerThread preDescriptor H.maskedSetup)
    preloadedPhysicalDescriptor = refl
    missingCapturedEntry : lookup missingEntry (Shared.entries (Shared.cm forkedWorld)) ≡ nothing
    missingCapturedEntry = refl
    preloadedResourcesImpossible : ResourceFacts.Facts preChild preDescriptor forkedWorld → ⊥
    preloadedResourcesImpossible (_ , (_ , ()) , _)
    missingCapturedPromise : missingPromise ∈ Shared.promises forkedWorld → ⊥
    missingCapturedPromise ()
    noPromiseAllocationInWorld : Shared.promises forkedWorld ≡ []
    noPromiseAllocationInWorld = refl
    socketCreatedAtActualFork : lookup preSocket (Shared.sockets forkedWorld) ≡ just (Shared.handling preChild)
    socketCreatedAtActualFork = refl
    differentEntryStillNamesPhysicalChild : lookup (ident 0) (Shared.entries (Shared.cm forkedWorld)) ≡
      just (Shared.unnegotiated inbound A.key₀ preChild)
    differentEntryStillNamesPhysicalChild = refl
    forkHasNotCollected : Close.collected (B.shutdown (controlPhysical preloadedForked)) ≡ []
    forkHasNotCollected = refl
    missingEntryPreventsLowerCommit : O.advance (O.acquire preCaller Acquire.commitConnected) forkedConfiguration ≡ nothing
    missingEntryPreventsLowerCommit = refl

    -- The established O.initial-core profile erases this injected frame while
    -- retaining exactly the same core heaps. Its immediate fork must be refused.
    ordinaryConfiguration : O.Configuration
    ordinaryConfiguration = O.initial seededCore
    ordinaryStart : V.Runtime
    ordinaryStart = renderPreloaded (B.supervised ordinaryConfiguration [] Close.initialState) [] []
    ordinaryInitializer : V.initialize ordinaryConfiguration L.settings ≡ just ordinaryStart
    ordinaryInitializer = refl
    ordinaryImmediateForkRefused : V.advance preloadedForkEvent ordinaryStart ≡ nothing
    ordinaryImmediateForkRefused = refl

    -- No collected malformed-history suffix is asserted here.
    -- Do not fake Server's closingCM stage. Missing entry99 also prevents the
    -- normal captured-entry cleanup from completing; a closed-resource theorem
    -- cannot be justified by pretending this malformed handler finishes cleanup.


  module InboundTwoGapOriginChecks where
    open import Relation.Binary.PropositionalEquality using (subst)
    open import Data.List using (take)
    open import Data.List.Membership.Propositional using (_∈_)
    open import Data.List.Relation.Unary.Any using (here)
    open import Data.Empty using (⊥)
    import ConnectionManagement.Properties.ServerPeersHandlerResources as ResourceModel
    import ConnectionManagement.Properties.HandlerResourceFacts as ResourceFacts
    import ConnectionManagement.OutboundHandlerSupervision as B
    private
      module Resource = ResourceModel.Frontend I.bearerClosed Prior.classify capability using (allocation-lower; core; event; fork-lower; selection-lower; shared)
      module Old = HandlerResourceOriginChecks using (beforeAllocation; born-origin; forkPrefix; entryPrefix; initialized-entry)

    gapPhysical : V.Runtime → B.State
    gapPhysical s = N.W.physical (N.R.base (N.raw (S.base (E.base (K.server (V.base s))))))

    -- Replace only the genuine shared source's IG runtime. Every surrounding
    -- physical pool/handler/Server/peer/frontend field retains its old snapshot.
    withInboundIG : IG.Runtime → V.Runtime → V.Runtime
    withInboundIG governor state = V.runtime
      (record (V.base state)
        { server = K.setSource updated (K.server (V.base state)) }) (V.front state)
      where
      previous : O.Configuration
      previous = K.source (V.base state)
      updated : O.Configuration
      updated = record previous { core = record (O.core previous) { inboundGovernor = governor } }
    sampledIG : IG.Runtime
    sampledIG = IG.runtimeState IG.emptyPublished 0 (IG.armInactivity 10)
      (record IG.emptyEngine { lastTime = 10 })
    registeredIG : IG.Runtime
    registeredIG = IG.runtimeState IG.emptyPublished 1 (IG.awaitBatch 10 (ident 0))
      (record IG.emptyEngine { lastTime = 10; timers = (ident 0 , ticking) ∷ [] })
    gapAllocateEvent gapSelectEvent gapForkEvent clockGapEvent timerGapEvent : V.Event
    gapAllocateEvent = Resource.event A.w₀ Admission.allocatePromise
    gapSelectEvent = Resource.event A.w₀ Admission.chooseEntry
    gapForkEvent = Resource.event A.w₀ Admission.fork
    clockGapEvent = V.dispatch (K.serverStep (E.run (S.run (S.runMachine (Machine.igStep (IG.captureTime 10))))))
    timerGapEvent = V.dispatch (K.serverStep (E.run (S.run (S.runMachine (Machine.igStep IG.registerInactivity)))))
    gapAllocated gapAfterClock gapSelected gapBeforeFork gapBorn : V.Runtime
    gapAllocated = wrap (base F.p3)
    gapAfterClock = withInboundIG sampledIG (wrap (base F.p3))
    gapSelected = withInboundIG sampledIG (wrap (base F.p4))
    gapBeforeFork = withInboundIG registeredIG (wrap (base F.p4))
    gapBorn = withInboundIG registeredIG (wrap (base F.p5))
    gapAllocation : V.advance gapAllocateEvent (wrap (base F.p2)) ≡ just gapAllocated
    gapAllocation = p5
    clockBetweenAllocationAndSelection : V.advance clockGapEvent gapAllocated ≡ just gapAfterClock
    clockBetweenAllocationAndSelection = refl
    gapSelection : V.advance gapSelectEvent gapAfterClock ≡ just gapSelected
    gapSelection = refl
    timerBetweenSelectionAndFork : V.advance timerGapEvent gapSelected ≡ just gapBeforeFork
    timerBetweenSelectionAndFork = refl
    gapFork : V.advance gapForkEvent gapBeforeFork ≡ just gapBorn
    gapFork = refl
    allocationGap selectionGap : List V.Event
    allocationGap = clockGapEvent ∷ []
    selectionGap = timerGapEvent ∷ []
    allocationGapNonempty : allocationGap ≡ [] → ⊥
    allocationGapNonempty ()
    selectionGapNonempty : selectionGap ≡ [] → ⊥
    selectionGapNonempty ()
    abstract
      actualAllocationGap : V.Runs gapAllocated allocationGap gapAfterClock
      actualAllocationGap = V.more {a = clockGapEvent} clockBetweenAllocationAndSelection V.stop
      actualSelectionGap : V.Runs gapSelected selectionGap gapBeforeFork
      actualSelectionGap = V.more {a = timerGapEvent} timerBetweenSelectionAndFork V.stop
    twoGapEvents : List V.Event
    twoGapEvents = take 4 prefixActions ++
      (gapAllocateEvent ∷ clockGapEvent ∷ gapSelectEvent ∷ timerGapEvent ∷ gapForkEvent ∷ [])
    abstract
      initializedTwoGapRun : V.Runs initial twoGapEvents gapBorn
      initializedTwoGapRun = Facts.append-protocols Old.beforeAllocation
        (V.more {a = gapAllocateEvent} gapAllocation
          (V.more {a = clockGapEvent} clockBetweenAllocationAndSelection
            (V.more {a = gapSelectEvent} gapSelection
              (V.more {a = timerGapEvent} timerBetweenSelectionAndFork
                (V.more {a = gapForkEvent} gapFork V.stop)))))
    twoGapPhysicalCapture : lookup A.child₀ (B.threads (gapPhysical gapBorn)) ≡
      just (H.handlerThread I.captured H.maskedSetup)
    twoGapPhysicalCapture = refl
    twoGapPromise : Shared.handlerPromise I.captured ∈ Shared.promises (Resource.shared gapAllocated)
    twoGapPromise = here refl
    twoGapResources : ResourceFacts.Facts A.child₀ I.captured (Resource.shared gapBorn)
    twoGapResources = refl , (Shared.unnegotiated inbound A.key₀ A.child₀ , refl) , (Shared.handling A.child₀ , refl)
    derivedAllocationAcrossProfile : Machine.advance (Machine.admissionStep A.w₀ Admission.allocatePromise)
      (Resource.core (wrap (base F.p2))) ≡ just (Resource.core gapAllocated)
    derivedAllocationAcrossProfile = Resource.allocation-lower A.w₀ (wrap (base F.p2)) gapAllocation
    derivedSelectionAfterFirstGap : Machine.advance (Machine.admissionStep A.w₀ Admission.chooseEntry)
      (Resource.core gapAfterClock) ≡ just (Resource.core gapSelected)
    derivedSelectionAfterFirstGap = Resource.selection-lower A.w₀ gapAfterClock gapSelection
    derivedForkAfterSecondGap : Machine.advance (Machine.admissionStep A.w₀ Admission.fork)
      (Resource.core gapBeforeFork) ≡ just (Resource.core gapBorn)
    derivedForkAfterSecondGap = Resource.fork-lower A.w₀ gapBeforeFork gapFork

    -- Neither action accepts a supplied promise/entry argument. A mismatch is
    -- therefore a REFUTED DESCRIPTOR/CERTIFICATE, not a new runtime refusal.
    mismatchedPromiseDescriptor : lookup A.child₀ (Shared.handlers (Resource.shared gapBorn)) ≡
      just (Shared.handlerStart (ident 0) (ident 0) (ident 88) A.key₀) → ⊥
    mismatchedPromiseDescriptor ()
    mismatchedEntryDescriptor : lookup A.child₀ (Shared.handlers (Resource.shared gapBorn)) ≡
      just (Shared.handlerStart (ident 99) (ident 0) (ident 0) A.key₀) → ⊥
    mismatchedEntryDescriptor ()
    mismatchedPromiseSelectionPC : lookup A.w₀ (Shared.admissions (Resource.shared gapAfterClock)) ≡
      just (Shared.admissionWorker F.r₀ (Shared.selectEntry (Shared.lease A.w₀ []) (ident 88))) → ⊥
    mismatchedPromiseSelectionPC ()
    mismatchedDerivedEntryPC : lookup A.w₀ (Shared.admissions (Resource.shared gapSelected)) ≡
      just (Shared.admissionWorker F.r₀ (Shared.forkHandler (Shared.lease A.w₀ []) (ident 0) (ident 99))) → ⊥
    mismatchedDerivedEntryPC ()
    actualSelectedEntry : lookup (ident 0) (Shared.entries (Shared.cm (Resource.shared gapSelected))) ≡
      just (Shared.unnegotiated inbound A.key₀ A.child₀)
    actualSelectedEntry = refl
    unselectedEntryAbsent : lookup (ident 99) (Shared.entries (Shared.cm (Resource.shared gapSelected))) ≡ nothing
    unselectedEntryAbsent = refl

    -- Empty-gap compatibility retains the existing adjacent origin API.
    emptyAllocationGap : V.Runs (wrap (base F.p3)) [] (wrap (base F.p3))
    emptyAllocationGap = V.stop
    emptySelectionGap : V.Runs (wrap (base F.p4)) [] (wrap (base F.p4))
    emptySelectionGap = V.stop
    abstract
      oldAdjacentBirthRun : V.Runs initial (take 7 prefixActions) (wrap (base F.p5))
      oldAdjacentBirthRun = Old.forkPrefix


    import ConnectionManagement.Properties.HandlerOriginHistory as GapModel
    import ConnectionManagement.Properties.ServerPeersHandlerResources as OldResourceModel
    private
      module Gaps = GapModel.Frontend I.bearerClosed Prior.classify capability using (History; initialize-history; empty-gaps-origin; extend-history; events; execution)
      module OldResource = OldResourceModel.Frontend I.bearerClosed Prior.classify capability using (Origin)
    abstract
      initializedTwoGapOrigin : Gaps.History initial gapBorn A.child₀
      initializedTwoGapOrigin = Gaps.initialize-history A.w₀ F.r₀ (Shared.lease A.w₀ []) (ident 0)
        initializer Old.beforeAllocation refl gapAllocation
        actualAllocationGap refl gapSelection refl actualSelectionGap refl gapFork V.stop
      -- Keep empty-history construction and its projection equalities in this
      -- SAME abstract block. Passing refl outside would unfold an opaque value.
      emptyGapOrigin : Gaps.History initial (wrap (base F.p5)) A.child₀
      emptyGapOrigin = Gaps.initialize-history A.w₀ F.r₀ (Shared.lease A.w₀ []) (ident 0)
        initializer Old.beforeAllocation refl p5
        emptyAllocationGap refl p6 refl emptySelectionGap refl p7 V.stop
      emptyGapOldOrigin : OldResource.Origin initial (wrap (base F.p5)) A.child₀
      emptyGapOldOrigin = Gaps.empty-gaps-origin emptyGapOrigin refl refl

      birthAllocationGap : Gaps.History.allocationGap initializedTwoGapOrigin ≡ allocationGap
      birthAllocationGap = refl
      birthForkGap : Gaps.History.forkGap initializedTwoGapOrigin ≡ selectionGap
      birthForkGap = refl
      birthDescriptor : Gaps.History.captured initializedTwoGapOrigin ≡ I.captured
      birthDescriptor = refl

    open import Data.List using (take; drop)
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as JoinModel
    import ConnectionManagement.Rules.CMShutdown as Close
    private
      module Joins = JoinModel.Frontend I.bearerClosed Prior.classify capability using (physical; handler-event; server-runs)
      module OldOrigin = HandlerResourceOriginChecks using (entryPrefix; initialized-entry; forkPrefix)
      module Wait = CMResultLifecycleChecks using (actual-wait-prefix; waitPrefix)
      module D = Reactivation.Shutdown using (cmEntry; handler10; finalCM; handlerFinishEdge10; handlerFinishEdge11)
      module W = N.W using (shutdownStep)
    -- Remove only the already checked prefix from the opaque initialized run.
    private module Drop = ResourceModel.Frontend I.bearerClosed Prior.classify capability using (discard-prefix)

    -- Preserve the complete current engine. Overwriting it with registeredIG's
    -- empty engine after U.allocateHandle would erase the freshly installed mux.
    overlayEarlyTimer : V.Runtime → V.Runtime
    overlayEarlyTimer state = withInboundIG (record current
      { nextTimer = 1
      ; continuation = IG.awaitBatch 10 (ident 0)
      ; execution = record (IG.execution current)
        { lastTime = 10; timers = (ident 0 , ticking) ∷ [] } }) state
      where
      current : IG.Runtime
      current = Machine.inboundGovernor (O.core (K.source (V.base state)))
    earlyTimerAtBirth : overlayEarlyTimer (wrap (base F.p5)) ≡ gapBorn
    earlyTimerAtBirth = refl
    earlyTimerRejoin : overlayEarlyTimer (wrap X.admitted) ≡ wrap X.g2
    earlyTimerRejoin = refl


    early8 : V.advance (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.putMapBack)))) gapBorn ≡ just (overlayEarlyTimer (wrap (base F.p6)))
    early8 = refl
    early9 : V.advance (V.dispatch (K.serverStep (E.run (admit A.w₀ Admission.readCounters)))) (overlayEarlyTimer (wrap (base F.p6))) ≡ just (overlayEarlyTimer (wrap (base F.p7)))
    early9 = refl
    early10 : V.advance (V.dispatch (K.serverStep (E.run (handler (H.enterHandshake A.child₀))))) (overlayEarlyTimer (wrap (base F.p7))) ≡ just (overlayEarlyTimer (wrap (base F.s1)))
    early10 = refl
    early11 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.negotiate A.child₀ I.ps duplex))))) (overlayEarlyTimer (wrap (base F.s1))) ≡ just (overlayEarlyTimer (wrap (base F.s2)))
    early11 = refl
    early12 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.allocateHandle A.child₀ (ident 0) (ident 0)))))) (overlayEarlyTimer (wrap (base F.s2))) ≡ just (overlayEarlyTimer (wrap (base F.s3)))
    early12 = refl
    early13 : V.advance (V.dispatch (K.serverStep (E.run (mux (U.publishSuccess A.child₀))))) (overlayEarlyTimer (wrap (base F.s3))) ≡ just (overlayEarlyTimer (wrap (base F.s4)))
    early13 = refl
    early14 : V.advance (V.dispatch (K.serverStep (E.run (consume Handshake.readResult)))) (overlayEarlyTimer (wrap (base F.s4))) ≡ just (overlayEarlyTimer (wrap (base F.s5)))
    early14 = refl
    early15 : V.advance (V.dispatch (K.serverStep (E.run (consume Handshake.commitResult)))) (overlayEarlyTimer (wrap (base F.s5))) ≡ just (overlayEarlyTimer (wrap (base F.s6)))
    early15 = refl
    early16 : V.advance (V.dispatch (K.serverStep (E.run (consume Handshake.readResultCounters)))) (overlayEarlyTimer (wrap (base F.s6))) ≡ just (overlayEarlyTimer (wrap (base F.s7)))
    early16 = refl
    early17 : V.advance (V.dispatch (K.serverStep (E.run (consume Handshake.enqueueInbound)))) (overlayEarlyTimer (wrap (base F.s7))) ≡ just (overlayEarlyTimer (wrap (base F.s8)))
    early17 = refl
    early18 : V.advance (V.dispatch (K.serverStep (E.run (consume Handshake.returnResult)))) (overlayEarlyTimer (wrap (base F.s8))) ≡ just (overlayEarlyTimer (wrap (base F.s9)))
    early18 = refl
    early19 : V.advance (V.dispatch (K.serverStep (E.run (S.workerReturned A.w₀)))) (overlayEarlyTimer (wrap (base F.s9))) ≡ just (overlayEarlyTimer (wrap (base F.s10)))
    early19 = refl
    early20 : V.advance (V.dispatch (K.serverStep (E.run (S.workerResult A.w₀)))) (overlayEarlyTimer (wrap (base F.s10))) ≡ just (wrap X.g2)
    early20 = refl

    earlyBridgeEvents : List V.Event
    earlyBridgeEvents = take 13 (drop 7 prefixActions)
    abstract
      earlyBridge : V.Runs gapBorn earlyBridgeEvents (wrap X.g2)
      earlyBridge = V.more early8 (V.more early9 (V.more early10 (V.more early11 (V.more early12 (V.more early13 (V.more early14 (V.more early15 (V.more early16 (V.more early17 (V.more early18 (V.more early19 (V.more early20 (V.stop)))))))))))))

    -- Old p21/p22 are already realized in the earlier two origin gaps. Use them
    -- ONLY to peel the old opaque initialized-entry trace, not in earlyBridge.
    oldPrefix22Events : List V.Event
    oldPrefix22Events = take 22 OldOrigin.entryPrefix
    abstract
      oldPrefix22 : V.Runs initial oldPrefix22Events (wrap X.g2)
      oldPrefix22 = V.more p1 (V.more p2 (V.more p3 (V.more p4 (V.more p5 (V.more p6 (V.more p7 (V.more p8 (V.more p9 (V.more p10 (V.more p11 (V.more p12 (V.more p13 (V.more p14 (V.more p15 (V.more p16 (V.more p17 (V.more p18 (V.more p19 (V.more p20 (V.more p21 (V.more p22 (V.stop))))))))))))))))))))))
      joinedToCMEntry : V.Runs (wrap X.g2) (drop 22 OldOrigin.entryPrefix) D.cmEntry
      joinedToCMEntry = Drop.discard-prefix {suffix = drop 22 OldOrigin.entryPrefix} oldPrefix22 OldOrigin.initialized-entry
      gapBirthToCMEntry : V.Runs gapBorn (earlyBridgeEvents ++ drop 22 OldOrigin.entryPrefix) D.cmEntry
      gapBirthToCMEntry = Facts.append-protocols earlyBridge joinedToCMEntry

    -- Apply to the SAME nonempty-gap History, not a fresh empty-gap occurrence.
    abstract
      nonemptyHistoryAtCMEntry : Gaps.History initial D.cmEntry A.child₀
      nonemptyHistoryAtCMEntry = Gaps.extend-history gapBirthToCMEntry initializedTwoGapOrigin
      nonemptyHistoryAtPublication : Gaps.History initial D.handler10 A.child₀
      nonemptyHistoryAtPublication = Gaps.extend-history (Joins.server-runs Wait.actual-wait-prefix) nonemptyHistoryAtCMEntry
      nonemptyHistoryAtFinalWait : Gaps.History initial D.finalCM A.child₀
      nonemptyHistoryAtFinalWait = Gaps.extend-history
        (V.more {a = Joins.handler-event (W.shutdownStep Close.finishClose)} D.handlerFinishEdge11 V.stop)
        nonemptyHistoryAtPublication
      -- These resource facts retain exactly the History's original descriptor.
      nonemptyResourcesAtPublication : ResourceFacts.Facts A.child₀
        (Gaps.History.captured nonemptyHistoryAtPublication) (Resource.shared D.handler10)
      nonemptyResourcesAtPublication = Gaps.History.retained nonemptyHistoryAtPublication
      nonemptyResourcesAtFinalWait : ResourceFacts.Facts A.child₀
        (Gaps.History.captured nonemptyHistoryAtFinalWait) (Resource.shared D.finalCM)
      nonemptyResourcesAtFinalWait = Gaps.History.retained nonemptyHistoryAtFinalWait

      finalAllocationGap : Gaps.History.allocationGap nonemptyHistoryAtFinalWait ≡ allocationGap
      finalAllocationGap = birthAllocationGap
      finalForkGap : Gaps.History.forkGap nonemptyHistoryAtFinalWait ≡ selectionGap
      finalForkGap = birthForkGap
      finalDescriptor : Gaps.History.captured nonemptyHistoryAtFinalWait ≡ I.captured
      finalDescriptor = birthDescriptor
      publicationDescriptor : Gaps.History.captured nonemptyHistoryAtPublication ≡ I.captured
      publicationDescriptor = birthDescriptor
      fixedResourcesAtPublication : ResourceFacts.Facts A.child₀ I.captured (Resource.shared D.handler10)
      fixedResourcesAtPublication = subst (λ captured → ResourceFacts.Facts A.child₀ captured (Resource.shared D.handler10))
        publicationDescriptor nonemptyResourcesAtPublication
      fixedResourcesAtFinalWait : ResourceFacts.Facts A.child₀ I.captured (Resource.shared D.finalCM)
      fixedResourcesAtFinalWait = subst (λ captured → ResourceFacts.Facts A.child₀ captured (Resource.shared D.finalCM))
        finalDescriptor nonemptyResourcesAtFinalWait

    import ConnectionManagement.Properties.CollectedHandlerBirth as CollectedBirth
    import ConnectionManagement.Properties.HandlerBirthBacking as BirthBacking
    open import Data.Product using (Σ)
    open import Relation.Binary.PropositionalEquality using (sym)
    private
      module Collected = CollectedBirth.Frontend I.bearerClosed Prior.classify capability using (initialized-birth; initialized-member)
      module Back = BirthBacking.Frontend I.bearerClosed Prior.classify capability using (Backing; capture-of-found; physical-state)
    finalGapWorkerCollected : A.child₀ ∈ Close.collected (N.W.shutdown (N.R.base (N.raw (S.base (E.base (K.server (V.base D.finalCM)))))))
    finalGapWorkerCollected = here refl
    finalPhysicalDescriptor : lookup A.child₀ (B.threads (Back.physical-state D.finalCM)) ≡ just (H.handlerThread I.captured H.handshaking)
    finalPhysicalDescriptor = refl
    abstract
      gapCollectedBirth : Σ Shared.HandlerStart (λ captured → Back.Backing initial D.finalCM (Gaps.events nonemptyHistoryAtFinalWait) A.child₀ captured)
      gapCollectedBirth = Collected.initialized-birth initializer (Gaps.execution nonemptyHistoryAtFinalWait) finalGapWorkerCollected
      gapCollectedPhysical : Σ H.Thread (λ thread → lookup A.child₀ (B.threads (Back.physical-state D.finalCM)) ≡ just thread)
      gapCollectedPhysical = Collected.initialized-member initializer (Gaps.execution nonemptyHistoryAtFinalWait) finalGapWorkerCollected
      gapCollectedDescriptor : proj₁ gapCollectedBirth ≡ I.captured
      gapCollectedDescriptor = sym (Back.capture-of-found (proj₂ gapCollectedBirth) finalPhysicalDescriptor)


  -- Recover the actual nonempty-gap origin automatically, then extend the SAME
  -- reconstructed occurrence through handler publication and CM's final wait.
  module AutomaticInboundWaitChecks where
    open import Data.List using (take; drop)
    open import Data.List.Membership.Propositional using (_∈_)
    open import Data.Product using (Σ)
    open import Data.Maybe.Properties using (just-injective)
    open import Relation.Binary.PropositionalEquality using (sym; cong; subst; trans)
    import ConnectionManagement.Properties.InboundOriginResources as AutoModel
    import ConnectionManagement.Properties.InboundOriginRuntime as RuntimeModel
    import ConnectionManagement.Properties.HandlerResourceFacts as ResourceFacts
    import ConnectionManagement.Properties.ServerPeersMonitorJoins as JoinModel
    import ConnectionManagement.Properties.CollectedHandlerBirth as CollectedModel
    import ConnectionManagement.Properties.HandlerBirthBacking as BackModel
    import ConnectionManagement.Rules.CMShutdown as Close
    private
      module Auto = AutoModel.Frontend I.bearerClosed Prior.classify capability using (RecoveredOrigin; initialize-origin; extend-origin; events; execution; canonicalFork; shared)
      module Located = RuntimeModel.Frontend.Located I.bearerClosed Prior.classify capability using (ForkOrigin)
      module FOrigin = RuntimeModel.Frontend.Located.ForkOrigin I.bearerClosed Prior.classify capability using (request; selection)
      module Selected = RuntimeModel.Frontend.Located.History.SelectedOrigin I.bearerClosed Prior.classify capability using (current-PC; decomposition; prefix; allocationLabel; allocationGap; selectionLabel; forkGap)
      module Rcv = Auto.RecoveredOrigin using (reconstructed; captured; at-birth; current-facts)
      module GapCases = InboundTwoGapOriginChecks using (gapAllocateEvent; gapSelectEvent; gapForkEvent; gapAllocated; gapAfterClock; gapSelected; gapBeforeFork; gapBorn; gapAllocation; gapSelection; gapFork; allocationGap; selectionGap; actualAllocationGap; actualSelectionGap; gapBirthToCMEntry; earlyBridgeEvents; finalGapWorkerCollected; finalPhysicalDescriptor)
      module Old = HandlerResourceOriginChecks using (beforeAllocation; entryPrefix)
      module Joins = JoinModel.Frontend I.bearerClosed Prior.classify capability using (handler-event; server-event; server-runs)
      module Wait = CMResultLifecycleChecks using (actual-wait-prefix; waitPrefix)
      module D = Reactivation.Shutdown using (cmEntry; handler10; finalCM; handlerFinishEdge11)
      module W = N.W using (shutdownStep)
      module Collected = CollectedModel.Frontend I.bearerClosed Prior.classify capability using (initialized-birth)
      module Back = BackModel.Frontend I.bearerClosed Prior.classify capability using (Backing; capture-of-found)

    inputConfig : O.Configuration
    inputConfig = O.initial (Machine.initial Shared.responderMode F.empty)
    -- These are the exact old prefix and two genuine gaps, stopping just before
    -- the fork. No allocation/selection labels or gaps are rebuilt by discovery.
    beforeForkEvents : List V.Event
    beforeForkEvents = take 4 prefixActions ++
      (GapCases.gapAllocateEvent ∷ (GapCases.allocationGap ++ (GapCases.gapSelectEvent ∷ GapCases.selectionGap)))
    abstract
      actualBeforeFork : V.Runs initial beforeForkEvents GapCases.gapBeforeFork
      actualBeforeFork = Facts.append-protocols Old.beforeAllocation
        (V.more {a = GapCases.gapAllocateEvent} GapCases.gapAllocation
          (Facts.append-protocols GapCases.actualAllocationGap
            (V.more {a = GapCases.gapSelectEvent} GapCases.gapSelection GapCases.actualSelectionGap)))

    entrySuffix publicationSuffix finalSuffix : List V.Event
    entrySuffix = GapCases.earlyBridgeEvents ++ drop 22 Old.entryPrefix
    publicationSuffix = entrySuffix ++ map Joins.server-event Wait.waitPrefix
    finalSuffix = publicationSuffix ++
      (Joins.handler-event (W.shutdownStep Close.finishClose) ∷ [])
    OriginAt : List V.Event → V.Runtime → Set
    OriginAt suffix current = Auto.RecoveredOrigin inputConfig L.settings initial beforeForkEvents
      GapCases.gapBeforeFork GapCases.gapBorn A.w₀ GapCases.gapForkEvent suffix current

    -- The dependent decomposition proof must be transported when its packet
    -- changes syntactically, even though extension preserves the whole packet.
    Decomposition : Located.ForkOrigin initial beforeForkEvents GapCases.gapBeforeFork GapCases.gapBorn A.w₀ GapCases.gapForkEvent → Set
    Decomposition recovered = beforeForkEvents ≡
      Selected.prefix (FOrigin.selection recovered) ++
      (Selected.allocationLabel (FOrigin.selection recovered) ∷
        (Selected.allocationGap (FOrigin.selection recovered) ++
          (Selected.selectionLabel (FOrigin.selection recovered) ∷ Selected.forkGap (FOrigin.selection recovered))))

    decomposition-preserved :
      (first second : Located.ForkOrigin initial beforeForkEvents GapCases.gapBeforeFork GapCases.gapBorn A.w₀ GapCases.gapForkEvent) →
      (same : second ≡ first) →
      subst Decomposition (sym same) (Selected.decomposition (FOrigin.selection first)) ≡
      Selected.decomposition (FOrigin.selection second)
    decomposition-preserved first .first refl = refl

    abstract
      automaticAtBirth : OriginAt [] GapCases.gapBorn
      automaticAtBirth = Auto.initialize-origin inputConfig L.settings initializer actualBeforeFork
        Auto.canonicalFork GapCases.gapFork V.stop
      automaticAtCMEntry : OriginAt entrySuffix D.cmEntry
      automaticAtCMEntry = Auto.extend-origin GapCases.gapBirthToCMEntry automaticAtBirth
      automaticAtPublication : OriginAt publicationSuffix D.handler10
      automaticAtPublication = Auto.extend-origin (Joins.server-runs Wait.actual-wait-prefix) automaticAtCMEntry
      automaticAtFinalWait : OriginAt finalSuffix D.finalCM
      automaticAtFinalWait = Auto.extend-origin
        (V.more {a = Joins.handler-event (W.shutdownStep Close.finishClose)} D.handlerFinishEdge11 V.stop)
        automaticAtPublication

      -- Extension copies the whole automatically reconstructed packet, which
      -- includes its exact original observed-label decomposition and both gaps.
      sameReconstructionAtPublication : Rcv.reconstructed automaticAtPublication ≡ Rcv.reconstructed automaticAtBirth
      sameReconstructionAtPublication = refl
      sameReconstructionAtFinalWait : Rcv.reconstructed automaticAtFinalWait ≡ Rcv.reconstructed automaticAtBirth
      sameReconstructionAtFinalWait = refl
      sameCaptureAtPublication : Rcv.captured automaticAtPublication ≡ Rcv.captured automaticAtBirth
      sameCaptureAtPublication = refl
      sameCaptureAtFinalWait : Rcv.captured automaticAtFinalWait ≡ Rcv.captured automaticAtBirth
      sameCaptureAtFinalWait = refl
    -- Keep the reconstructed origin opaque here. Use the proved projection
    -- equalities instead of reducing the complete initialized occurrence again.
    retainedOriginalDecomposition :
      subst Decomposition (sym sameReconstructionAtFinalWait)
        (Selected.decomposition (FOrigin.selection (Rcv.reconstructed automaticAtBirth))) ≡
      Selected.decomposition (FOrigin.selection (Rcv.reconstructed automaticAtFinalWait))
    retainedOriginalDecomposition = decomposition-preserved
      (Rcv.reconstructed automaticAtBirth) (Rcv.reconstructed automaticAtFinalWait) sameReconstructionAtFinalWait
    originalObservedLabels : Auto.events automaticAtFinalWait ≡ beforeForkEvents ++ (GapCases.gapForkEvent ∷ finalSuffix)
    originalObservedLabels = refl

    -- Identify the fixture only from the recovered terminal PC and logical
    -- handler fact. No resource/physical-lookup premise enters initialize-origin.
    recoveredRequest : FOrigin.request (Rcv.reconstructed automaticAtBirth) ≡ F.r₀
    recoveredRequest = sym (cong Shared.request
      (just-injective (Selected.current-PC (FOrigin.selection (Rcv.reconstructed automaticAtBirth)))))
    recoveredChild : Shared.child (FOrigin.request (Rcv.reconstructed automaticAtBirth)) ≡ A.child₀
    recoveredChild = cong Shared.child recoveredRequest
    automaticLogicalAtBirth : ResourceFacts.Facts A.child₀ (Rcv.captured automaticAtBirth) (Auto.shared GapCases.gapBorn)
    automaticLogicalAtBirth = subst
      (λ worker → ResourceFacts.Facts worker (Rcv.captured automaticAtBirth) (Auto.shared GapCases.gapBorn))
      recoveredChild (Rcv.at-birth automaticAtBirth)
    recoveredDescriptor : Rcv.captured automaticAtBirth ≡ I.captured
    recoveredDescriptor = sym (just-injective (proj₁ automaticLogicalAtBirth))
    automaticLogicalAtPublication : ResourceFacts.Facts A.child₀ (Rcv.captured automaticAtBirth) (Auto.shared D.handler10)
    automaticLogicalAtPublication = subst
      (λ captured → ResourceFacts.Facts A.child₀ captured (Auto.shared D.handler10)) sameCaptureAtPublication
      (subst (λ worker → ResourceFacts.Facts worker (Rcv.captured automaticAtPublication) (Auto.shared D.handler10))
        (trans (cong (λ packet → Shared.child (FOrigin.request packet)) sameReconstructionAtPublication) recoveredChild)
        (Rcv.current-facts automaticAtPublication))
    automaticLogicalAtFinalWait : ResourceFacts.Facts A.child₀ (Rcv.captured automaticAtBirth) (Auto.shared D.finalCM)
    automaticLogicalAtFinalWait = subst
      (λ captured → ResourceFacts.Facts A.child₀ captured (Auto.shared D.finalCM)) sameCaptureAtFinalWait
      (subst (λ worker → ResourceFacts.Facts worker (Rcv.captured automaticAtFinalWait) (Auto.shared D.finalCM))
        (trans (cong (λ packet → Shared.child (FOrigin.request packet)) sameReconstructionAtFinalWait) recoveredChild)
        (Rcv.current-facts automaticAtFinalWait))
    fixedResourcesAtPublication : ResourceFacts.Facts A.child₀ I.captured (Auto.shared D.handler10)
    fixedResourcesAtPublication = subst
      (λ captured → ResourceFacts.Facts A.child₀ captured (Auto.shared D.handler10))
      recoveredDescriptor automaticLogicalAtPublication
    fixedResourcesAtFinalWait : ResourceFacts.Facts A.child₀ I.captured (Auto.shared D.finalCM)
    fixedResourcesAtFinalWait = subst
      (λ captured → ResourceFacts.Facts A.child₀ captured (Auto.shared D.finalCM))
      recoveredDescriptor automaticLogicalAtFinalWait

    -- Feed the exact automatic packet's execution into the existing closed
    -- collected-birth theorem; its physical membership remains derived there.
    automaticCollectedBirth : Σ Shared.HandlerStart (λ captured →
      Back.Backing initial D.finalCM (Auto.events automaticAtFinalWait) A.child₀ captured)
    automaticCollectedBirth = Collected.initialized-birth initializer
      (Auto.execution automaticAtFinalWait) GapCases.finalGapWorkerCollected
    automaticCollectedDescriptor : proj₁ automaticCollectedBirth ≡ I.captured
    automaticCollectedDescriptor = sym (Back.capture-of-found (proj₂ automaticCollectedBirth) GapCases.finalPhysicalDescriptor)


-- Independent initialized controls and automatic origin applications.
module AutomaticInboundChecks where
  open import Data.Bool using (Bool; true; false)
  open import Data.Nat using (ℕ)
  open import Data.List using (List; []; _∷_; _++_; take)
  open import Data.Maybe using (just; nothing)
  open import Data.Maybe.Properties using (just-injective)
  open import Data.Product using (_,_; proj₁)
  open import Data.Empty using (⊥)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
  open import ConnectionManagement.Domain hiding (worker; local; mux; job)
  open import ConnectionManagement.Store using (Store; lookup; put)
  open import ConnectionManagement.Properties.HandlerResourceFacts using (Facts)
  import ConnectionManagement.Properties.InboundOriginResources as Automatic
  import ConnectionManagement.Properties.InboundOriginRuntime as AutoRuntime
  import ConnectionManagement.State as Shared
  import ConnectionManagement.Machine as Machine
  import ConnectionManagement.OutboundMachine as O
  import ConnectionManagement.ServerAdmission as Server
  import ConnectionManagement.ServerIGExit as Exit
  import ConnectionManagement.ServerPeers as Combined
  import ConnectionManagement.PeerSupervision as Supervision
  import ConnectionManagement.PeerContext as Context
  import ConnectionManagement.Rules.Server as Admission
  import ConnectionManagement.Rules.Handshake as Handshake
  import ConnectionManagement.Rules.IGRegistration as IG
  import ConnectionManagement.Rules.OutboundGovernor as Governor
  import ConnectionManagement.Subsystem as Sub
  import ConnectionManagement.HandlerSupervision as H
  import ConnectionManagement.OutboundHandlerSupervision as B
  import ConnectionManagement.MuxPublicationUnwind as Publication
  import ConnectionManagement.MuxProtocolJobs as ProtocolModel
  import ConnectionManagement.MuxHandlerSupervision as MuxModel
  import ConnectionManagement.Rules.MuxJobTypes as Types
  import ConnectionManagement.MuxCatchUnwind as CatchModel
  import ConnectionManagement.MuxDeltaQ as DeltaModel
  import ConnectionManagement.MuxStartupUnwind as UnwindModel
  import ConnectionManagement.MuxExitCancellation as CancellationModel
  import ConnectionManagement.MuxHandlerExit as ExitModel
  import ConnectionManagement.MuxGroupShutdown as GroupModel
  import ConnectionManagement.MuxResultMonitor as MonitorModel
  import ConnectionManagement.GovernorPool as GovernorPoolModel
  import ConnectionManagement.Scenarios.Admission as A
  import ConnectionManagement.Negative.ServerAdmissionPrefixFixtures as DataFixtures
  import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I

  classify : ErrorId → Bool
  classify _ = false
  capability : HandleId → ℕ → Bool
  capability _ _ = false
  private
   module K = Combined I.bearerClosed classify using (combined; coreAllowed; coreStep; peerStep; server; serverStep; setSource; source)
   module V = Combined.Protocols I.bearerClosed classify capability using (Event; Runs; Runtime; advance; base; dispatch; empty; front; initialize; more; physical; runtime; setPhysical; stop)
   module S = Server I.bearerClosed using (Action; State; acceptedFork; async; base; calling; closeException; rawWorker; run; runMachine; runOutbound; setWorld; shared; source; workerException; workerResult; workerReturned; workers)
   module E = Exit I.bearerClosed using (base; emptyExit; igExitState; run)
   module PS = Supervision classify using (initial; run)
   module GP = GovernorPoolModel classify using (run)
   module C = Context classify using (Context; capture)
   module N = Publication I.bearerClosed using (raw; run)
   module Catch = CatchModel I.bearerClosed using (run)
   module Delta = DeltaModel I.bearerClosed using (run)
   module Unwind = UnwindModel I.bearerClosed using (base; run)
   module X = CancellationModel I.bearerClosed using (run)
   module W = ExitModel I.bearerClosed using (physical; run)
   module G = GroupModel I.bearerClosed using (run)
   module M = MonitorModel I.bearerClosed using (run)
   module P = ProtocolModel using (base; run)
   module U = MuxModel Types.TypedResult using (Action; allocateHandle; negotiate; origins; publishSuccess; run)
   module F = DataFixtures 10 A.key₀ using (b1; b2; b3; b4; binding; empty; lease₁; live; one; p1; p2; p3; p4; p5; p6; p7; ps₀; r₀; r₁; s1; s10; s11; s2; s3; s4; s5; s6; s7; s8; s9; start; two; unneg)

  settings : Governor.State
  settings = Governor.governorState (Governor.targets 0 0 0) [] [] [] [] [] [] [] [] []
  configuration : O.Configuration
  configuration = O.initial (Machine.initial Shared.responderMode F.empty)
  context : C.Context
  context = C.capture (PS.initial configuration settings)
  frontendAt : S.State → V.Runtime
  frontendAt s = V.runtime (K.combined (E.igExitState s E.emptyExit) context) V.empty
  start : V.Runtime
  start = frontendAt F.start
  initialized : V.initialize configuration settings ≡ just start
  initialized = refl
  canonical : WorkerId → Admission.AdmissionAction → V.Event
  canonical w a = V.dispatch (K.serverStep (E.run (S.run (S.runMachine (Machine.admissionStep w a)))))
  coreAlias : WorkerId → Admission.AdmissionAction → V.Event
  coreAlias w a = V.dispatch (K.coreStep (O.inbound (Machine.admissionStep w a)))
  serverEvent : S.Action → V.Event
  serverEvent a = V.dispatch (K.serverStep (E.run a))
  handlerEvent : H.Action → V.Event
  handlerEvent a = serverEvent (S.run (N.run (Catch.run (Delta.run (Unwind.run (X.run
   (W.run (G.run (M.run (P.run (U.run (B.handler a))))))))))))
  muxEvent : U.Action → V.Event
  muxEvent a = serverEvent (S.run (N.run (Catch.run (Delta.run (Unwind.run (X.run
   (W.run (G.run (M.run (P.run a))))))))))
  consumeEvent : Handshake.HandshakeAction → V.Event
  consumeEvent a = serverEvent (S.run (S.runMachine (Machine.handshakeStep A.w₀ a)))
  physicalAt : V.Runtime → B.State
  physicalAt s = W.physical (Unwind.base (N.raw (S.base (E.base (K.server (V.base s))))))
  append : ∀ {s as t bs u} → V.Runs s as t → V.Runs t bs u → V.Runs s (as ++ bs) u
  append V.stop tail = tail
  append (V.more actual rest) tail = V.more actual (append rest tail)

  -- Same-key raw admissions are real accepted forks. Only the first acts here.

  c1 : V.advance (serverEvent (S.acceptedFork A.w₀ F.r₀)) (start) ≡ just (frontendAt F.one)
  c1 = refl
  c2 : V.advance (serverEvent (S.acceptedFork A.w₁ F.r₁)) (frontendAt F.one) ≡ just (frontendAt F.two)
  c2 = refl
  c3 : V.advance (canonical A.w₀ Admission.take) (frontendAt F.two) ≡ just (frontendAt F.p1)
  c3 = refl
  c4 : V.advance (canonical A.w₀ Admission.countLimit) (frontendAt F.p1) ≡ just (frontendAt F.p2)
  c4 = refl
  c5 : V.advance (canonical A.w₀ Admission.allocatePromise) (frontendAt F.p2) ≡ just (frontendAt F.p3)
  c5 = refl
  c6 : V.advance (canonical A.w₀ Admission.chooseEntry) (frontendAt F.p3) ≡ just (frontendAt F.p4)
  c6 = refl
  c7 : V.advance (canonical A.w₀ Admission.fork) (frontendAt F.p4) ≡ just (frontendAt F.p5)
  c7 = refl
  c8 : V.advance (canonical A.w₀ Admission.putMapBack) (frontendAt F.p5) ≡ just (frontendAt F.p6)
  c8 = refl
  c9 : V.advance (canonical A.w₀ Admission.readCounters) (frontendAt F.p6) ≡ just (frontendAt F.p7)
  c9 = refl
  c10 : V.advance (handlerEvent (H.enterHandshake A.child₀)) (frontendAt F.p7) ≡ just (frontendAt F.s1)
  c10 = refl
  c11 : V.advance (muxEvent (U.negotiate A.child₀ I.ps duplex)) (frontendAt F.s1) ≡ just (frontendAt F.s2)
  c11 = refl
  c12 : V.advance (muxEvent (U.allocateHandle A.child₀ (ident 0) (ident 0))) (frontendAt F.s2) ≡ just (frontendAt F.s3)
  c12 = refl
  c13 : V.advance (muxEvent (U.publishSuccess A.child₀)) (frontendAt F.s3) ≡ just (frontendAt F.s4)
  c13 = refl
  c14 : V.advance (consumeEvent Handshake.readResult) (frontendAt F.s4) ≡ just (frontendAt F.s5)
  c14 = refl
  c15 : V.advance (consumeEvent Handshake.commitResult) (frontendAt F.s5) ≡ just (frontendAt F.s6)
  c15 = refl
  c16 : V.advance (consumeEvent Handshake.readResultCounters) (frontendAt F.s6) ≡ just (frontendAt F.s7)
  c16 = refl
  c17 : V.advance (consumeEvent Handshake.enqueueInbound) (frontendAt F.s7) ≡ just (frontendAt F.s8)
  c17 = refl
  c18 : V.advance (consumeEvent Handshake.returnResult) (frontendAt F.s8) ≡ just (frontendAt F.s9)
  c18 = refl
  c19 : V.advance (serverEvent (S.workerReturned A.w₀)) (frontendAt F.s9) ≡ just (frontendAt F.s10)
  c19 = refl
  c20 : V.advance (serverEvent (S.workerResult A.w₀)) (frontendAt F.s10) ≡ just (frontendAt F.s11)
  c20 = refl

  prefix4 prefix7 prefix20 : List V.Event
  prefix4 = (serverEvent (S.acceptedFork A.w₀ F.r₀)) ∷ (serverEvent (S.acceptedFork A.w₁ F.r₁)) ∷ (canonical A.w₀ Admission.take) ∷ (canonical A.w₀ Admission.countLimit) ∷ []
  prefix7 = (serverEvent (S.acceptedFork A.w₀ F.r₀)) ∷ (serverEvent (S.acceptedFork A.w₁ F.r₁)) ∷ (canonical A.w₀ Admission.take) ∷ (canonical A.w₀ Admission.countLimit) ∷ (canonical A.w₀ Admission.allocatePromise) ∷ (canonical A.w₀ Admission.chooseEntry) ∷ (canonical A.w₀ Admission.fork) ∷ []
  prefix20 = (serverEvent (S.acceptedFork A.w₀ F.r₀)) ∷ (serverEvent (S.acceptedFork A.w₁ F.r₁)) ∷ (canonical A.w₀ Admission.take) ∷ (canonical A.w₀ Admission.countLimit) ∷ (canonical A.w₀ Admission.allocatePromise) ∷ (canonical A.w₀ Admission.chooseEntry) ∷ (canonical A.w₀ Admission.fork) ∷ (canonical A.w₀ Admission.putMapBack) ∷ (canonical A.w₀ Admission.readCounters) ∷ (handlerEvent (H.enterHandshake A.child₀)) ∷ (muxEvent (U.negotiate A.child₀ I.ps duplex)) ∷ (muxEvent (U.allocateHandle A.child₀ (ident 0) (ident 0))) ∷ (muxEvent (U.publishSuccess A.child₀)) ∷ (consumeEvent Handshake.readResult) ∷ (consumeEvent Handshake.commitResult) ∷ (consumeEvent Handshake.readResultCounters) ∷ (consumeEvent Handshake.enqueueInbound) ∷ (consumeEvent Handshake.returnResult) ∷ (serverEvent (S.workerReturned A.w₀)) ∷ (serverEvent (S.workerResult A.w₀)) ∷ []
  abstract
   beforeAllocation : V.Runs start prefix4 (frontendAt F.p2)
   beforeAllocation = V.more c1 (V.more c2 (V.more c3 (V.more c4 (V.stop))))
   canonicalEmpty : V.Runs start prefix7 (frontendAt F.p5)
   canonicalEmpty = V.more c1 (V.more c2 (V.more c3 (V.more c4 (V.more c5 (V.more c6 (V.more c7 (V.stop)))))))
   firstAdmissionComplete : V.Runs start prefix20 (frontendAt F.s11)
   firstAdmissionComplete = V.more c1 (V.more c2 (V.more c3 (V.more c4 (V.more c5 (V.more c6 (V.more c7 (V.more c8 (V.more c9 (V.more c10 (V.more c11 (V.more c12 (V.more c13 (V.more c14 (V.more c15 (V.more c16 (V.more c17 (V.more c18 (V.more c19 (V.more c20 (V.stop))))))))))))))))))))


  -- Actual core/canonical alias mixture; never relabel this trace.
  coreAllocationAllowed : K.coreAllowed (O.inbound (Machine.admissionStep A.w₀ Admission.allocatePromise)) (V.base (frontendAt F.p2)) ≡ true
  coreAllocationAllowed = refl
  mixedAllocation : V.advance (coreAlias A.w₀ Admission.allocatePromise) (frontendAt F.p2) ≡ just (frontendAt F.p3)
  mixedAllocation = refl
  mixedFork : V.advance (coreAlias A.w₀ Admission.fork) (frontendAt F.p4) ≡ just (frontendAt F.p5)
  mixedFork = refl
  mixedEvents : List V.Event
  mixedEvents = prefix4 ++ (coreAlias A.w₀ Admission.allocatePromise ∷ canonical A.w₀ Admission.chooseEntry ∷ coreAlias A.w₀ Admission.fork ∷ [])
  abstract
   mixedRun : V.Runs start mixedEvents (frontendAt F.p5)
   mixedRun = append beforeAllocation (V.more mixedAllocation (V.more c6 (V.more mixedFork V.stop)))
  coreAndCanonicalDiffer : coreAlias A.w₀ Admission.allocatePromise ≡ canonical A.w₀ Admission.allocatePromise → ⊥
  coreAndCanonicalDiffer ()
  peerRawAliasRefused : V.advance (V.dispatch (K.peerStep (PS.run (GP.run (Sub.core
   (O.inbound (Machine.admissionStep A.w₀ Admission.allocatePromise))))))) (frontendAt F.p2) ≡ nothing
  peerRawAliasRefused = refl
  outboundRawAliasRefused : V.advance (serverEvent (S.run (S.runOutbound
   (O.inbound (Machine.admissionStep A.w₀ Admission.allocatePromise))))) (frontendAt F.p2) ≡ nothing
  outboundRawAliasRefused = refl

  -- Genuine nonempty gaps, independent of the cached full acceptance module.
  withIG : IG.Runtime → V.Runtime → V.Runtime
  withIG governor s = V.runtime (record (V.base s)
   { server = K.setSource updated (K.server (V.base s)) }) (V.front s)
   where
   original = K.source (V.base s)
   updated = record original { core = record (O.core original) { inboundGovernor = governor } }
  sampledIG registeredIG : IG.Runtime
  sampledIG = IG.runtimeState IG.emptyPublished 0 (IG.armInactivity 10) (record IG.emptyEngine { lastTime = 10 })
  registeredIG = IG.runtimeState IG.emptyPublished 1 (IG.awaitBatch 10 (ident 0))
   (record IG.emptyEngine { lastTime = 10; timers = (ident 0 , ticking) ∷ [] })
  clockEvent timerEvent : V.Event
  clockEvent = serverEvent (S.run (S.runMachine (Machine.igStep (IG.captureTime 10))))
  timerEvent = serverEvent (S.run (S.runMachine (Machine.igStep IG.registerInactivity)))
  afterClock selectedWithClock beforeGapFork gapBorn : V.Runtime
  afterClock = withIG sampledIG (frontendAt F.p3)
  selectedWithClock = withIG sampledIG (frontendAt F.p4)
  beforeGapFork = withIG registeredIG (frontendAt F.p4)
  gapBorn = withIG registeredIG (frontendAt F.p5)
  gap1 : V.advance clockEvent (frontendAt F.p3) ≡ just afterClock
  gap1 = refl
  gapSelect : V.advance (canonical A.w₀ Admission.chooseEntry) afterClock ≡ just selectedWithClock
  gapSelect = refl
  gap2 : V.advance timerEvent selectedWithClock ≡ just beforeGapFork
  gap2 = refl
  gapFork : V.advance (canonical A.w₀ Admission.fork) beforeGapFork ≡ just gapBorn
  gapFork = refl
  gapEvents : List V.Event
  gapEvents = prefix4 ++ (canonical A.w₀ Admission.allocatePromise ∷ clockEvent ∷ canonical A.w₀ Admission.chooseEntry ∷ timerEvent ∷ canonical A.w₀ Admission.fork ∷ [])
  abstract
   canonicalNonempty : V.Runs start gapEvents gapBorn
   canonicalNonempty = append beforeAllocation (V.more c5 (V.more gap1 (V.more gapSelect (V.more gap2 (V.more gapFork V.stop)))))

  -- Denial is an enabled selection branch; it is NOT a successful fork PC.
  deniedTake : V.advance (canonical A.w₁ Admission.take) (frontendAt F.s11) ≡ just (frontendAt F.b1)
  deniedTake = refl
  deniedCount : V.advance (canonical A.w₁ Admission.countLimit) (frontendAt F.b1) ≡ just (frontendAt F.b2)
  deniedCount = refl
  deniedAllocate : V.advance (coreAlias A.w₁ Admission.allocatePromise) (frontendAt F.b2) ≡ just (frontendAt F.b3)
  deniedAllocate = refl
  deniedChoose : V.advance (coreAlias A.w₁ Admission.chooseEntry) (frontendAt F.b3) ≡ just (frontendAt F.b4)
  deniedChoose = refl
  deniedEvents : List V.Event
  deniedEvents = prefix20 ++ (canonical A.w₁ Admission.take ∷ canonical A.w₁ Admission.countLimit ∷ coreAlias A.w₁ Admission.allocatePromise ∷ coreAlias A.w₁ Admission.chooseEntry ∷ [])
  abstract
   initializedDenied : V.Runs start deniedEvents (frontendAt F.b4)
   initializedDenied = append firstAdmissionComplete (V.more deniedTake (V.more deniedCount (V.more deniedAllocate (V.more deniedChoose V.stop))))
  deniedForkRefused : V.advance (coreAlias A.w₁ Admission.fork) (frontendAt F.b4) ≡ nothing
  deniedForkRefused = refl
  completedCallerCannotBeAcceptedAgain : V.advance (serverEvent (S.acceptedFork A.w₀ F.r₀)) (frontendAt F.s11) ≡ nothing
  completedCallerCannotBeAcceptedAgain = refl

  -- Real caller exception observation does not reset its source admission PC.
  cancelError : ErrorId
  cancelError = errorId 250
  cancelledParent : S.State
  cancelledParent = record F.p7
   { workers = put A.w₀ (S.rawWorker F.r₀ (S.closeException (S.async cancelError)) 0) (S.workers F.p7) }
  callerCancellation : V.advance (serverEvent (S.workerException A.w₀ (S.async cancelError))) (frontendAt F.p7) ≡ just (frontendAt cancelledParent)
  callerCancellation = refl
  cancelledPCUnchanged : lookup A.w₀ (Shared.admissions (S.shared cancelledParent)) ≡ just (Shared.admissionWorker F.r₀ (Shared.awaitHandshake (ident 0) (ident 0)))
  cancelledPCUnchanged = refl
  cancelledAllocationRefused : V.advance (coreAlias A.w₀ Admission.allocatePromise) (frontendAt cancelledParent) ≡ nothing
  cancelledAllocationRefused = refl



  -- A real unrelated accepted-fork writes another admission row while the target
  -- is between allocation and selection. Its own take would be blocked by the map.
  otherParent otherChild : WorkerId
  otherParent = ident 20
  otherChild = ident 21
  otherRequest : Shared.Admission
  otherRequest = Shared.admission A.key₁ (ident 20) otherChild 10
  withOtherParent : S.State → S.State
  withOtherParent s = record (S.setWorld (record (S.shared s)
   { admissions = put otherParent (Shared.admissionWorker otherRequest Shared.acquireMap)
       (Shared.admissions (S.shared s))
   ; sockets = put (ident 20) (Shared.admitting otherParent) (Shared.sockets (S.shared s)) }) s)
   { workers = put otherParent (S.rawWorker otherRequest S.calling 0) (S.workers s) }
  otherAccepted : V.advance (serverEvent (S.acceptedFork otherParent otherRequest))
   (frontendAt F.p3) ≡ just (frontendAt (withOtherParent F.p3))
  otherAccepted = refl
  otherCoreSelection : V.advance (coreAlias A.w₀ Admission.chooseEntry)
   (frontendAt (withOtherParent F.p3)) ≡ just (frontendAt (withOtherParent F.p4))
  otherCoreSelection = refl
  otherCanonicalFork : V.advance (canonical A.w₀ Admission.fork)
   (frontendAt (withOtherParent F.p4)) ≡ just (frontendAt (withOtherParent F.p5))
  otherCanonicalFork = refl
  otherCannotTakeHeldMap : V.advance (canonical otherParent Admission.take)
   (frontendAt (withOtherParent F.p3)) ≡ nothing
  otherCannotTakeHeldMap = refl
  otherEvents : List V.Event
  otherEvents = prefix4 ++ (canonical A.w₀ Admission.allocatePromise ∷
   serverEvent (S.acceptedFork otherParent otherRequest) ∷
   coreAlias A.w₀ Admission.chooseEntry ∷ canonical A.w₀ Admission.fork ∷ [])
  abstract
   unrelatedParentGap : V.Runs start otherEvents (frontendAt (withOtherParent F.p5))
   unrelatedParentGap = append beforeAllocation
    (V.more c5 (V.more otherAccepted (V.more otherCoreSelection (V.more otherCanonicalFork V.stop))))

  -- Same entry identity is overwritten by a second genuine selection. The two
  -- origins have distinct parent/request/promise/child; old descriptor is retained.
  secondPromises : List PromiseId
  secondPromises = ident 1 ∷ F.ps₀
  secondAt : Shared.ConnectionState → Shared.MapCell → Shared.AdmissionPC → List PromiseId → ℕ → S.State
  secondAt st cell pc promises next = F.live st cell
   (Shared.countPublished (ident 0) (ident 0)) pc promises next [] []
   (Shared.admitting A.w₁) IG.initial H.maskedSetup []
  second1 second2 second3 second4 secondFailed secondRestored : S.State
  second1 = secondAt F.unneg (Shared.taken A.w₁) (Shared.count F.lease₁) F.ps₀ 1
  second2 = secondAt F.unneg (Shared.taken A.w₁) (Shared.prepare F.lease₁) F.ps₀ 1
  second3 = secondAt F.unneg (Shared.taken A.w₁) (Shared.selectEntry F.lease₁ (ident 1)) secondPromises 2
  secondOverwrite : Shared.ConnectionState
  secondOverwrite = Shared.unnegotiated inbound A.key₀ A.child₁
  second4 = secondAt secondOverwrite (Shared.taken A.w₁)
   (Shared.forkHandler F.lease₁ (ident 1) (ident 0)) secondPromises 2
  secondFailed = secondAt secondOverwrite (Shared.taken A.w₁)
   (Shared.reject F.lease₁ Shared.forkFailed) secondPromises 2
  secondRestored = secondAt secondOverwrite (Shared.full F.binding)
   (Shared.closeSocket Shared.forkFailed) secondPromises 2
  secondTake : V.advance (canonical A.w₁ Admission.take) (frontendAt F.p6) ≡ just (frontendAt second1)
  secondTake = refl
  secondCount : V.advance (canonical A.w₁ Admission.countLimit) (frontendAt second1) ≡ just (frontendAt second2)
  secondCount = refl
  secondAllocate : V.advance (coreAlias A.w₁ Admission.allocatePromise) (frontendAt second2) ≡ just (frontendAt second3)
  secondAllocate = refl
  secondSelect : V.advance (coreAlias A.w₁ Admission.chooseEntry) (frontendAt second3) ≡ just (frontendAt second4)
  secondSelect = refl
  secondBeforeForkEvents : List V.Event
  secondBeforeForkEvents = prefix7 ++ (canonical A.w₀ Admission.putMapBack ∷
   canonical A.w₁ Admission.take ∷ canonical A.w₁ Admission.countLimit ∷
   coreAlias A.w₁ Admission.allocatePromise ∷ coreAlias A.w₁ Admission.chooseEntry ∷ [])
  abstract
   secondBeforeFork : V.Runs start secondBeforeForkEvents (frontendAt second4)
   secondBeforeFork = append canonicalEmpty (V.more c8 (V.more secondTake
    (V.more secondCount (V.more secondAllocate (V.more secondSelect V.stop)))))
  secondFailure : V.advance (canonical A.w₁ Admission.failFork) (frontendAt second4) ≡ just (frontendAt secondFailed)
  secondFailure = refl
  secondRestore : V.advance (canonical A.w₁ Admission.restore) (frontendAt secondFailed) ≡ just (frontendAt secondRestored)
  secondRestore = refl
  secondForkAfterRestoreRefused : V.advance (coreAlias A.w₁ Admission.fork) (frontendAt secondRestored) ≡ nothing
  secondForkAfterRestoreRefused = refl
  secondEntryStillOverwritten : lookup (ident 0) (Shared.entries (Shared.cm (S.shared secondRestored))) ≡ just secondOverwrite
  secondEntryStillOverwritten = refl
  secondOldCapture : lookup A.child₀ (B.threads (physicalAt (frontendAt secondRestored))) ≡
   just (H.handlerThread I.captured H.maskedSetup)
  secondOldCapture = refl

  -- Exact physical expected state after a successful second fork. Do not use only
  -- S.setWorld: that would omit the actual supervised child and provenance writes.
  secondDescriptor : Shared.HandlerStart
  secondDescriptor = Shared.handlerStart (ident 0) (ident 1) (ident 1) A.key₀
  secondForkWorld : Shared.State
  secondForkWorld = record (S.shared second4)
   { admissions = put A.w₁ (Shared.admissionWorker F.r₁ (Shared.publish F.lease₁ (ident 1) (ident 0)))
       (Shared.admissions (S.shared second4))
   ; handlers = put A.child₁ secondDescriptor (Shared.handlers (S.shared second4))
   ; sockets = put (ident 1) (Shared.handling A.child₁) (Shared.sockets (S.shared second4)) }
  secondForkSource : O.Configuration
  secondForkSource = record (S.source second4)
   { core = Machine.replaceWorld (O.core (S.source second4)) secondForkWorld }
  secondForkPhysical : B.State
  secondForkPhysical = B.supervised secondForkSource
   (put A.child₁ (H.handlerThread secondDescriptor H.maskedSetup)
    (B.threads (physicalAt (frontendAt second4))))
   (B.shutdown (physicalAt (frontendAt second4)))
  secondBorn : V.Runtime
  secondBorn = V.runtime (V.setPhysical
   (record original { base = record (P.base original)
     { base = secondForkPhysical
     ; origins = put A.child₁ inbound (U.origins (P.base original)) } })
   (V.base (frontendAt second4))) (V.front (frontendAt second4))
   where original = V.physical (V.base (frontendAt second4))
  secondFork : V.advance (coreAlias A.w₁ Admission.fork) (frontendAt second4) ≡ just secondBorn
  secondFork = refl
  secondBothCaptures :
   lookup A.child₀ (B.threads (physicalAt secondBorn)) ≡ just (H.handlerThread I.captured H.maskedSetup)
  secondBothCaptures = refl
  secondNewCapture :
   lookup A.child₁ (B.threads (physicalAt secondBorn)) ≡ just (H.handlerThread secondDescriptor H.maskedSetup)
  secondNewCapture = refl
  abstract
   secondSuccessfulRun : V.Runs start (secondBeforeForkEvents ++ (coreAlias A.w₁ Admission.fork ∷ [])) secondBorn
   secondSuccessfulRun = append secondBeforeFork (V.more secondFork V.stop)

  private
   module Auto = Automatic.Frontend I.bearerClosed classify capability using (RecoveredOrigin; canonicalFork; coreFork; events; execution; initialize-origin; shared)
   module Rcv = Auto.RecoveredOrigin using (captured; current-facts; reconstructed)
   module RecoveredFork = AutoRuntime.Frontend.Located.ForkOrigin I.bearerClosed classify capability using (request; selection)
   module RecoveredHistory = AutoRuntime.Frontend.Located.History.SelectedOrigin I.bearerClosed classify capability using (current-PC)

  emptyBeforeEvents mixedBeforeEvents gapBeforeEvents unrelatedBeforeEvents : List V.Event
  emptyBeforeEvents = prefix4 ++ (canonical A.w₀ Admission.allocatePromise ∷ canonical A.w₀ Admission.chooseEntry ∷ [])
  mixedBeforeEvents = prefix4 ++ (coreAlias A.w₀ Admission.allocatePromise ∷ canonical A.w₀ Admission.chooseEntry ∷ [])
  gapBeforeEvents = prefix4 ++ (canonical A.w₀ Admission.allocatePromise ∷ clockEvent ∷ canonical A.w₀ Admission.chooseEntry ∷ timerEvent ∷ [])
  unrelatedBeforeEvents = prefix4 ++ (canonical A.w₀ Admission.allocatePromise ∷
   serverEvent (S.acceptedFork otherParent otherRequest) ∷ coreAlias A.w₀ Admission.chooseEntry ∷ [])
  abstract
   emptyBeforeFork : V.Runs start emptyBeforeEvents (frontendAt F.p4)
   emptyBeforeFork = append beforeAllocation (V.more c5 (V.more c6 V.stop))
   mixedBeforeFork : V.Runs start mixedBeforeEvents (frontendAt F.p4)
   mixedBeforeFork = append beforeAllocation (V.more mixedAllocation (V.more c6 V.stop))
   gapBeforeFork : V.Runs start gapBeforeEvents beforeGapFork
   gapBeforeFork = append beforeAllocation (V.more c5 (V.more gap1 (V.more gapSelect (V.more gap2 V.stop))))
   unrelatedBeforeFork : V.Runs start unrelatedBeforeEvents (frontendAt (withOtherParent F.p4))
   unrelatedBeforeFork = append beforeAllocation (V.more c5 (V.more otherAccepted (V.more otherCoreSelection V.stop)))

  -- These are the complete API inputs: initialize, actual observed prefix,
  -- classified actual fork label and actual fork, then an enabled suffix.
  -- Allocation/selection PCs and resource/physical lookups are not inputs.
  abstract
   automaticEmpty : Auto.RecoveredOrigin configuration settings start emptyBeforeEvents
    (frontendAt F.p4) (frontendAt F.p5) A.w₀ (canonical A.w₀ Admission.fork) [] (frontendAt F.p5)
   automaticEmpty = Auto.initialize-origin configuration settings initialized emptyBeforeFork Auto.canonicalFork c7 V.stop
   automaticNonempty : Auto.RecoveredOrigin configuration settings start gapBeforeEvents
    beforeGapFork gapBorn A.w₀ (canonical A.w₀ Admission.fork) [] gapBorn
   automaticNonempty = Auto.initialize-origin configuration settings initialized gapBeforeFork Auto.canonicalFork gapFork V.stop
   automaticMixed : Auto.RecoveredOrigin configuration settings start mixedBeforeEvents
    (frontendAt F.p4) (frontendAt F.p5) A.w₀ (coreAlias A.w₀ Admission.fork) [] (frontendAt F.p5)
   automaticMixed = Auto.initialize-origin configuration settings initialized mixedBeforeFork Auto.coreFork mixedFork V.stop
   automaticUnrelated : Auto.RecoveredOrigin configuration settings start unrelatedBeforeEvents
    (frontendAt (withOtherParent F.p4)) (frontendAt (withOtherParent F.p5)) A.w₀
    (canonical A.w₀ Admission.fork) [] (frontendAt (withOtherParent F.p5))
   automaticUnrelated = Auto.initialize-origin configuration settings initialized unrelatedBeforeFork Auto.canonicalFork otherCanonicalFork V.stop
   automaticSecond : Auto.RecoveredOrigin configuration settings start secondBeforeForkEvents
    (frontendAt second4) secondBorn A.w₁ (coreAlias A.w₁ Admission.fork) [] secondBorn
   automaticSecond = Auto.initialize-origin configuration settings initialized secondBeforeFork Auto.coreFork secondFork V.stop

  -- Event-list indices retain exact observed labels even though the reconstructed
  -- creator search consumes opaque Runs. No refl on recovered creator labels.
  emptyObservedExactly : Auto.events automaticEmpty ≡ prefix7
  emptyObservedExactly = refl
  nonemptyObservedExactly : Auto.events automaticNonempty ≡ gapEvents
  nonemptyObservedExactly = refl
  mixedObservedExactly : Auto.events automaticMixed ≡ mixedEvents
  mixedObservedExactly = refl
  unrelatedObservedExactly : Auto.events automaticUnrelated ≡ otherEvents
  unrelatedObservedExactly = refl
  secondObservedExactly : Auto.events automaticSecond ≡ (secondBeforeForkEvents ++ (coreAlias A.w₁ Admission.fork ∷ []))
  secondObservedExactly = refl
  abstract
   automaticEmptyExecution : V.Runs start prefix7 (frontendAt F.p5)
   automaticEmptyExecution = Auto.execution automaticEmpty
   automaticNonemptyExecution : V.Runs start gapEvents gapBorn
   automaticNonemptyExecution = Auto.execution automaticNonempty
   automaticMixedExecution : V.Runs start mixedEvents (frontendAt F.p5)
   automaticMixedExecution = Auto.execution automaticMixed
   automaticUnrelatedExecution : V.Runs start otherEvents (frontendAt (withOtherParent F.p5))
   automaticUnrelatedExecution = Auto.execution automaticUnrelated
   automaticSecondExecution : V.Runs start (secondBeforeForkEvents ++ (coreAlias A.w₁ Admission.fork ∷ [])) secondBorn
   automaticSecondExecution = Auto.execution automaticSecond

  -- Read the recovered PC/output facts to check the exact concrete descriptor.
  -- This does not give the initializer API any operational alignment premise.
  emptyRequestExact : RecoveredFork.request (Rcv.reconstructed automaticEmpty) ≡ F.r₀
  emptyRequestExact = sym (cong Shared.request (just-injective
   (RecoveredHistory.current-PC (RecoveredFork.selection (Rcv.reconstructed automaticEmpty)))))
  emptyCapturedExact : Rcv.captured automaticEmpty ≡ I.captured
  emptyCapturedExact = sym (just-injective (subst
   (λ request → lookup (Shared.child request) (Shared.handlers (Auto.shared (frontendAt F.p5))) ≡
    just (Rcv.captured automaticEmpty)) emptyRequestExact
   (proj₁ (Rcv.current-facts automaticEmpty))))
  secondRequestExact : RecoveredFork.request (Rcv.reconstructed automaticSecond) ≡ F.r₁
  secondRequestExact = sym (cong Shared.request (just-injective
   (RecoveredHistory.current-PC (RecoveredFork.selection (Rcv.reconstructed automaticSecond)))))
  secondCapturedExact : Rcv.captured automaticSecond ≡ secondDescriptor
  secondCapturedExact = sym (just-injective (subst
   (λ request → lookup (Shared.child request) (Shared.handlers (Auto.shared secondBorn)) ≡
    just (Rcv.captured automaticSecond)) secondRequestExact
   (proj₁ (Rcv.current-facts automaticSecond))))

  -- Derived Facts have the exact expected captured descriptors, even after an
  -- existing mutable entry is selected for a different parent/promise/child.
  emptyDerivedFacts : Facts A.child₀ I.captured (Auto.shared (frontendAt F.p5))
  emptyDerivedFacts = subst (λ captured → Facts A.child₀ captured (Auto.shared (frontendAt F.p5))) emptyCapturedExact
   (subst (λ request → Facts (Shared.child request) (Rcv.captured automaticEmpty)
     (Auto.shared (frontendAt F.p5))) emptyRequestExact (Rcv.current-facts automaticEmpty))
  secondDerivedFacts : Facts A.child₁ secondDescriptor (Auto.shared secondBorn)
  secondDerivedFacts = subst (λ captured → Facts A.child₁ captured (Auto.shared secondBorn)) secondCapturedExact
   (subst (λ request → Facts (Shared.child request) (Rcv.captured automaticSecond)
     (Auto.shared secondBorn)) secondRequestExact (Rcv.current-facts automaticSecond))
  wrongDescriptor : Shared.HandlerStart
  wrongDescriptor = record I.captured { handlerPromise = ident 77 }
  wrongDescriptorRefused : Facts A.child₀ wrongDescriptor (Auto.shared (frontendAt F.p5)) → ⊥
  wrongDescriptorRefused (() , rest)
  wrongRecoveredDescriptorRefused : Rcv.captured automaticEmpty ≡ wrongDescriptor → ⊥
  wrongRecoveredDescriptorRefused equality = wrongCapturedEquality (trans (sym emptyCapturedExact) equality)
   where
   wrongCapturedEquality : I.captured ≡ wrongDescriptor → ⊥
   wrongCapturedEquality ()

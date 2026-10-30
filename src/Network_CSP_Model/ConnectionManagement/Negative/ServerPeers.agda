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

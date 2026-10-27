{-# OPTIONS --guardedness #-}

-- CM/IG/Server dispatcher plus ordinary-peer OG, jobs and peer monitoring.
-- Policy picks/delays, clocks and IO completions are explicit environment inputs.
module ConnectionManagement.Subsystem where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.Nat using (ℕ; suc; _≤?_)
open import Data.List using (List; []; _∷_; _++_; map; filterᵇ)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (RunResult; clean; errored)
import ConnectionManagement.State as S
open import ConnectionManagement.Store using (Store; lookup; put; delete)
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.HandlerLifecycle as Life

data Selected : Set where
  policy : G.Decision → Selected
  completion : G.Completion → Selected
  monitor : List (PeerAddr × P.Status) → Store PeerAddr ℕ → Selected
  targets : G.Targets → Selected
  wakeup : ℕ → Selected

data PC : Set where
  publishPublic sampleInputs prepareWait selecting : PC
  cancelTimer : Selected → PC
  apply : Selected → PC
  publishView traceDecision : List G.Job → PC
  launch : List G.Job → PC
  register : JobId → List G.Job → PC
  completionAssertionFailed : G.Completion → PC

record JobFrame : Set where
  constructor jobFrame
  field execution : J.Frame
        queued : Bool
        deregistered : Bool
open JobFrame public

record Configuration : Set where
  constructor configuration
  field world : J.World
        privateState publicState : G.State
        pc : PC
        now : ℕ
        targetInput : G.Targets
        jobs : Store JobId JobFrame
        pool : List JobId
        completions : List G.Completion
        monitors : Store PeerConnectionId J.Frame
        nextJob nextPeer : ℕ
        maxRetries clearFailDelay : ℕ
        wakeupAt : Maybe ℕ
        wakeupReady : Bool
open Configuration public

initial : CM.Configuration → G.State → Configuration
initial c s = configuration (J.world c []) s s publishPublic 0 (G.target s)
  [] [] [] [] 0 0 5 60 nothing false

sameTargets : G.Targets → G.Targets → Bool
sameTargets a b = does (G.knownTarget a ≟ G.knownTarget b) ∧
  does (G.establishedTarget a ≟ G.establishedTarget b) ∧ does (G.activeTarget a ≟ G.activeTarget b)
noMonitor : Configuration → Bool
noMonitor c with G.monitored (J.peers (world c)) (privateState c)
... | [] = true
... | _ ∷ _ = false
noCompletions : Configuration → Bool
noCompletions c with completions c
... | [] = true
... | _ ∷ _ = false
noTargets : Configuration → Bool
noTargets c = sameTargets (targetInput c) (G.target (privateState c))

-- Job identity is distinct from caller, child and peer-handle identities.
workerFree : WorkerId → Configuration → Bool
workerFree w c with lookup w (CM.acquiring (J.cm (world c))) | lookup w (CM.releasing (J.cm (world c)))
... | nothing | nothing = freeJobs (jobs c)
  where
  freeJobs : Store JobId JobFrame → Bool
  freeJobs [] = true
  freeJobs ((_ , j) ∷ js) with J.caller (execution j) ≟ w
  ... | yes _ = false
  ... | no _ = freeJobs js
... | _ | _ = false

-- Every selection has the source alternative priority. Policy chooses peers,
-- not which enabled alternative wins over monitors/completions/target changes.
data Action : Set where
  core : CM.Action → Action
  publishPublicState : Action
  sampleTime applyAt : ℕ → Action
  setTargets : G.Targets → Action
  selectMonitor : Store PeerAddr ℕ → Action
  selectCompletion selectTargets selectWakeup registerWakeup expireWakeup cancelWakeup publishCounters traceSelection : Action
  selectPolicy : List PeerAddr → Action
  forkJob : WorkerId → WorkerId → SocketId → Action
  registerJob finishLaunch : Action
  jobStep : JobId → J.Action → Action
  enqueueCompletion : JobId → ℕ → Action
  deregisterJob : JobId → Action
  protocolResult : PeerConnectionId → ℕ → RunResult → Action
  publishInitiatorResult : PeerConnectionId → ℕ → Action
  pollPeer : PeerConnectionId → WorkerId → Action
  monitorStep : PeerConnectionId → J.Action → Action
  monitorFinished observeInitiatorFailure : PeerConnectionId → Action

-- Observe established before warm before hot, as the source orElse nesting.
firstResult : P.Peer → Maybe (G.Kind × RunResult)
firstResult p with P.first ConnectionManagement.IGTypes.established (P.runs p)
... | just result = just (G.close , result)
... | nothing with P.first ConnectionManagement.IGTypes.warm (P.runs p)
...   | just result = just (G.close , result)
...   | nothing with P.first ConnectionManagement.IGTypes.hot (P.runs p)
...     | just result = just (G.deactivate , result)
...     | nothing = nothing

-- A cancellable timer is owned only on branches with a finite wakeup.
selectionPC : Configuration → Selected → PC
selectionPC c selected with wakeupAt c
... | nothing = apply selected
... | just _ = cancelTimer selected

validCompletionDelay : G.Job → G.Outcome → ℕ → Bool
validCompletionDelay work G.failed jitter with G.kind work
... | G.establish = does (jitter ≤? 4)
... | _ = true
validCompletionDelay _ _ _ = true

completeDelays : List (PeerAddr × P.Status) → Store PeerAddr ℕ → Bool
completeDelays [] delays = true
completeDelays ((p , _) ∷ rest) delays with lookup p delays
... | nothing = false
... | just _ = completeDelays rest delays

advance : Action → Configuration → Maybe Configuration
advance (core action) c with CM.advance action (J.cm (world c))
... | nothing = nothing
... | just cm′ = just (record c { world = record (world c) { cm = cm′ } })
advance publishPublicState c with pc c
... | publishPublic = just (record c { publicState = privateState c; pc = sampleInputs })
... | _ = nothing
advance (sampleTime t) c with pc c | now c ≤? t
... | sampleInputs | yes _ = just (record c { now = t; privateState = G.advanceTime t (privateState c); pc = prepareWait })
... | _ | _ = nothing
advance (setTargets t) c with G.sane t
... | true = just (record c { targetInput = t })
... | false = nothing
advance (selectMonitor delay) c with pc c | G.monitored (J.peers (world c)) (privateState c)
... | selecting | changes@(_ ∷ _) with completeDelays changes delay
...   | false = nothing
...   | true = just (record c { pc = selectionPC c (monitor changes delay) })
advance (selectMonitor delay) c | _ | _ = nothing
advance selectCompletion c with pc c | noMonitor c | completions c
... | selecting | true | x ∷ xs = just (record c { pc = selectionPC c (completion x); completions = xs })
... | _ | _ | _ = nothing
advance selectTargets c with pc c | noMonitor c | noCompletions c | noTargets c
... | selecting | true | true | false = just (record c { pc = selectionPC c (targets (targetInput c)) })
... | _ | _ | _ | _ = nothing
advance (selectPolicy picked) c with pc c | noMonitor c | noCompletions c | noTargets c
... | selecting | true | true | true with G.choose (now c) picked (privateState c)
...   | nothing = nothing
...   | just d = just (record c { pc = selectionPC c (policy d) })
advance (selectPolicy picked) c | _ | _ | _ | _ = nothing
advance registerWakeup c with pc c
... | prepareWait = just (record c { pc = selecting; wakeupAt = G.nextWakeup (now c) (privateState c); wakeupReady = false })
... | _ = nothing
advance expireWakeup c with pc c | wakeupAt c | wakeupReady c
... | selecting | just _ | false = just (record c { wakeupReady = true })
... | _ | _ | _ = nothing
advance cancelWakeup c with pc c
... | cancelTimer selected = just (record c { pc = apply selected; wakeupAt = nothing; wakeupReady = false })
... | _ = nothing
advance selectWakeup c with pc c | noMonitor c | noCompletions c | noTargets c | wakeupReady c | wakeupAt c | G.firstReady (now c) (privateState c)
... | selecting | true | true | true | true | just deadline | nothing = just (record c { pc = selectionPC c (wakeup deadline) })
... | _ | _ | _ | _ | _ | _ | _ = nothing
advance (applyAt t) c with pc c | now c ≤? t
... | apply (policy d) | yes _ = just (record c { now = t; privateState = G.nextState d; pc = publishView (G.launches d) })
... | apply (completion result) | yes _ with G.completionAssertion result (privateState c)
...   | false = just (record c { now = t; pc = completionAssertionFailed result })
...   | true = just (record c
  { now = t; privateState = G.complete (maxRetries c) (clearFailDelay c) t result (privateState c); pc = publishView [] })
advance (applyAt t) c | apply (monitor changes delay) | yes _ = just (record c
  { now = t; privateState = G.applyMonitorDelays (maxRetries c) t delay changes (privateState c); pc = publishView [] })
advance (applyAt t) c | apply (targets t′) | yes _ = just (record c { now = t; privateState = record (privateState c) { target = t′ }; pc = publishView [] })
advance (applyAt t) c | apply (wakeup deadline) | yes _ with deadline ≤? t
...   | yes _ = just (record c { now = t; pc = publishView [] })
...   | no _ = nothing
advance (applyAt t) c | _ | _ = nothing
advance publishCounters c with pc c
... | publishView work = just (record c { pc = traceDecision work })
... | _ = nothing
advance traceSelection c with pc c
... | traceDecision work = just (record c { pc = launch work })
... | _ = nothing
advance (forkJob caller child sock) c with pc c | workerFree caller c
... | launch [] | _ = nothing
... | launch (work ∷ rest) | true = create (G.captured work)
  where
  create : Maybe PeerConnectionId → Maybe Configuration
  create captured = just (record c
    { jobs = put (ident (nextJob c)) (jobFrame (J.frame work caller child sock (peerRef captured) J.begin) false false) (jobs c)
    ; nextJob = suc (nextJob c); nextPeer = peerSupply captured
    ; pc = register (ident (nextJob c)) rest })
    where
    peerRef : Maybe PeerConnectionId → PeerConnectionId
    peerRef nothing = ident (nextPeer c)
    peerRef (just p) = p
    peerSupply : Maybe PeerConnectionId → ℕ
    peerSupply nothing = suc (nextPeer c)
    peerSupply (just _) = nextPeer c
advance (forkJob caller child sock) c | _ | _ = nothing
advance finishLaunch c with pc c
... | launch [] = just (record c { pc = publishPublic })
... | _ = nothing
advance registerJob c with pc c
... | register j rest = just (record c { pool = j ∷ pool c; pc = launch rest })
... | _ = nothing
advance (jobStep j action) c with lookup j (jobs c)
... | nothing = nothing
... | just frame with queued frame | J.step action (execution frame) (world c)
...   | false | just (f′ , w′) = just (record c { world = w′; jobs = put j (record frame { execution = f′ }) (jobs c) })
...   | _ | _ = nothing
advance (enqueueCompletion j delay) c with lookup j (jobs c)
... | nothing = nothing
... | just frame with queued frame | J.pc (execution frame)
...   | false | J.complete result with validCompletionDelay (J.work (execution frame)) result delay
...     | false = nothing
...     | true = just (record c
  { completions = completions c ++ (G.completion (J.work (execution frame)) result delay ∷ [])
  ; jobs = put j (record frame { queued = true }) (jobs c) })
advance (enqueueCompletion j delay) c | just frame | _ | _ = nothing
advance (deregisterJob j) c with lookup j (jobs c)
... | nothing = nothing
... | just frame with queued frame | deregistered frame | any (λ x → does (x ≟ j)) (pool c)
...   | true | false | true = just (record c
  { pool = filterᵇ (λ x → not (does (x ≟ j))) (pool c)
  ; jobs = put j (record frame { deregistered = true }) (jobs c) })
...   | _ | _ | _ = nothing
advance (protocolResult ref n result) c with lookup ref (J.peers (world c))
... | nothing = nothing
... | just peer with P.step (P.protocolResult n result) peer
  (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
...   | nothing = nothing
...   | just (peer′ , ig′) = just (record c { world = record (world c)
  { peers = put ref peer′ (J.peers (world c)) } })
-- JobPool publication is separate from the initiator result-cell write.
-- Choose a pending occurrence by ordinal, independently of its protocol number
-- and publication order, even after that protocol has restarted.
advance (publishInitiatorResult ref i) c with lookup ref (J.peers (world c))
... | nothing = nothing
... | just peer with P.takePending i (P.pendingResults peer) | lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c))))))
...   | just ((n , result) , retained) | just observedMux with Life.muxAllowed (P.muxRef peer) Life.jobAccess (Inbound.handlerLifecycles (CM.core (J.cm (world c))))
...     | false = nothing
...     | true = just (record c { world = record (world c)
  { peers = put ref (record peer { pendingResults = retained }) (J.peers (world c))
  ; cm = record (J.cm (world c)) { core = record (CM.core (J.cm (world c)))
    { inboundGovernor = IG.setMux (P.muxRef peer) (record observedMux
      { completions = M.completions observedMux ++ (M.jobResult M.initiatorJob n result ∷ []) })
      (Inbound.inboundGovernor (CM.core (J.cm (world c)))) } } } })
advance (publishInitiatorResult ref i) c | just peer | _ | _ = nothing
-- Compatibility observation consumes only an already-queued initiator error at
-- the FIFO head, through the same phase-gated monitor as responder completions.
advance (observeInitiatorFailure ref) c with lookup ref (J.peers (world c))
... | nothing = nothing
... | just peer with lookup (P.muxRef peer) (IG.muxes (IG.execution (Inbound.inboundGovernor (CM.core (J.cm (world c))))))
...   | nothing = nothing
...   | just observedMux with M.completions observedMux
...     | M.jobResult M.initiatorJob n (errored err) ∷ rest with CM.advance
    (CM.inbound (Inbound.igStep (IG.monitorCompletion (P.muxRef peer)))) (J.cm (world c))
...       | nothing = nothing
...       | just cm′ = just (record c { world = record (world c) { cm = cm′ } })
advance (observeInitiatorFailure ref) c | just peer | just observedMux | _ = nothing
advance (pollPeer ref caller) c with lookup ref (J.peers (world c)) | lookup ref (monitors c)
... | just peer | nothing with P.monitorStarted peer | P.status peer
...   | true | P.peerCooling with P.step P.monitorCooling peer
    (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
...     | nothing = nothing
...     | just (peer′ , _) = just (record c { world = record (world c) { peers = put ref peer′ (J.peers (world c)) } })
advance (pollPeer ref caller) c | just peer | nothing | true | P.peerCold =
  just (record c { world = record (world c) { peers = put ref (record peer { monitorStarted = false }) (J.peers (world c)) } })
advance (pollPeer ref caller) c | just peer | nothing | true | _ with firstResult peer
... | nothing = nothing
... | just (_ , errored _) = just (record c { world = record (world c) { peers = put ref (P.cool peer) (J.peers (world c)) } })
... | just (kind , clean) with workerFree caller c
...   | false = nothing
...   | true = just (record c { monitors = put ref
  (J.frame (G.job kind (remote (P.key peer)) (just ref)) caller caller (ident 0) ref J.begin) (monitors c) })
advance (pollPeer ref caller) c | just peer | nothing | false | _ = nothing
advance (pollPeer ref caller) c | just peer | just f with J.pc f
... | J.awaitCold _ with P.step P.monitorCooling peer
    (Inbound.inboundGovernor (CM.core (J.cm (world c)))) (Inbound.world (CM.core (J.cm (world c))))
...   | nothing = nothing
...   | just (peer′ , _) = just (record c { world = record (world c) { peers = put ref peer′ (J.peers (world c)) } })
advance (pollPeer ref caller) c | just peer | just f | _ = nothing
advance (pollPeer ref caller) c | nothing | _ = nothing
advance (monitorStep ref action) c with lookup ref (monitors c)
... | nothing = nothing
... | just f with J.step action f (world c)
...   | nothing = nothing
...   | just (f′ , w′) = just (record c { world = w′; monitors = put ref f′ (monitors c) })
advance (monitorFinished ref) c with lookup ref (monitors c)
... | nothing = nothing
... | just f with J.pc f
...   | J.complete _ = just (record c { monitors = delete ref (monitors c) })
...   | _ = nothing

data Executes : Configuration → List Action → Configuration → Set where
  done : ∀ {c} → Executes c [] c
  next : ∀ {c c₁ c₂ a as} → advance a c ≡ just c₁ → Executes c₁ as c₂ → Executes c (a ∷ as) c₂

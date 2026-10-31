{-# OPTIONS --guardedness #-}

-- Shared Server/PSA/governor composition for the post-setup, normal callback
-- return profile. Protocols below couples peer requests to physical mux jobs;
-- the base adapter continues to refuse raw logical birth/result shortcuts.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.ServerPeers
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (ℕ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.State as Shared
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Subsystem as Sub
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.PeerSupervision as Supervision
import ConnectionManagement.PeerContext as Context
import ConnectionManagement.Rules.PeerJobs as J
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.AsyncScope as Scope
private
  module S = Server isBearerClosed
  module E = Exit isBearerClosed
  module PS = Supervision isIOManagerError
  module GP = PS.GP
  module C = Context isIOManagerError

-- Only server contains a CM configuration. The peer context has no CM field.
record State : Set where
  constructor combined
  field server : E.State
        context : C.Context
open State public
source : State → O.Configuration
source s = E.source (server s)
peers : State → PS.State
peers s = C.assemble (source s) (context s)
setSource : O.Configuration → E.State → E.State
setSource c s = record s { base = S.setSource c (E.base s) }
initial : O.Configuration → G.State → Maybe State
initial c g with E.initial c
... | nothing = nothing
... | just e = just (combined e (C.capture (PS.initial c g)))

-- Source lexical order: all four inner scopes, governor pool and outer PSA
-- monitor pool must finish before the Server callback body can return.
peerClosed : State → Bool
peerClosed s with GP.Pool.phase (C.governorPool (context s)) |
  PS.Pool.phase (C.monitorPool (context s)) | Scope.closed (C.scopes (context s))
... | GP.Pool.closedPool | PS.Pool.closedPool | true = true
... | _ | _ | _ = false
peerOpen : State → Bool
peerOpen s with S.stage (E.base (server s))
... | S.serving = true
... | _ = false

-- Future establishing jobs reserve their socket even before CM opens it.
socketFree : SocketId → List (JobId × Sub.JobFrame) → Bool
socketFree sock [] = true
socketFree sock ((_ , jf) ∷ rest) with G.kind (J.work (Sub.execution jf))
... | G.establish with sock ≟ J.socketRef (Sub.execution jf)
...   | yes _ = false
...   | no _ = socketFree sock rest
socketFree sock ((_ , jf) ∷ rest) | _ = socketFree sock rest
peerSocketFree : SocketId → State → Bool
peerSocketFree sock s = socketFree sock (Sub.jobs (PS.machine (peers s))) ∧
  acquireSocketFree sock (O.acquiring (source s))
  where
  acquireSocketFree : SocketId → A.Runtime → Bool
  acquireSocketFree sock [] = true
  acquireSocketFree sock ((_ , f) ∷ rest) with sock ≟ A.socketRef (A.req f)
  ... | yes _ = false
  ... | no _ = acquireSocketFree sock rest
-- Unowned CM callers also reserve their requested child before physical birth.
acquireChildFree : WorkerId → A.Runtime → Bool
acquireChildFree w [] = true
acquireChildFree w ((_ , f) ∷ rest) with w ≟ A.child (A.req f)
... | yes _ = false
... | no _ = acquireChildFree w rest
fresh : WorkerId → State → Bool
fresh w s = S.fresh w (E.base (server s)) ∧ PS.freshWorker w (peers s) ∧
  acquireChildFree w (O.acquiring (source s))
newActors : WorkerId → WorkerId → SocketId → State → Bool
newActors w child sock s with w ≟ child | lookup sock (Shared.sockets (S.shared (E.base (server s))))
... | no _ | nothing = fresh w s ∧ fresh child s ∧ peerSocketFree sock s
... | _ | _ = false
forkJobAllowed : WorkerId → WorkerId → SocketId → State → Bool
forkJobAllowed w child sock s with Sub.pc (PS.machine (peers s))
... | Sub.launch (work ∷ _) with G.kind work
...   | G.establish = newActors w child sock s
...   | _ = fresh w s
forkJobAllowed _ _ _ _ | _ = false

-- Empty bundle traversal is pure. Starting an actual protocol or independently
-- publishing its logical result would bypass the existing physical adapter.
emptyStart : Maybe J.Frame → Bool
emptyStart (just f) with J.pc f
... | J.startBundle _ [] = true
... | _ = false
emptyStart nothing = false
rawPeerAllowed : Sub.Action → State → Bool
rawPeerAllowed (Sub.core _) _ = false
rawPeerAllowed (Sub.protocolResult _ _ _) _ = false
rawPeerAllowed (Sub.publishInitiatorResult _ _) _ = false
rawPeerAllowed (Sub.jobStep j J.runNext) s with lookup j (Sub.jobs (PS.machine (peers s)))
... | nothing = false
... | just jf = emptyStart (just (Sub.execution jf))
rawPeerAllowed (Sub.monitorStep ref J.runNext) s = emptyStart (lookup ref (Sub.monitors (PS.machine (peers s))))
rawPeerAllowed (Sub.forkJob w child sock) s = forkJobAllowed w child sock s
rawPeerAllowed _ _ = true
peerAllowed : PS.Action → State → Bool
peerAllowed (PS.run (GP.run a)) s = rawPeerAllowed a s
peerAllowed (PS.forkMonitor _ w) s = fresh w s
peerAllowed _ _ = true
serverAllowed : E.Action → State → Bool
serverAllowed (E.run (S.acceptedFork w req)) s = newActors w (Shared.child req) (Shared.socketRef req) s
serverAllowed (E.run (S.scope S.returnAction)) s = peerClosed s
serverAllowed (E.run (S.run a)) s with S.outboundCaller a
... | just _ = false
... | nothing = true
serverAllowed _ _ = true

-- Common outbound steps retain both physical Server permissions and peer-caller
-- cancellation/masking permissions. Raw aliases on either side are unavailable.
coreAction : O.Action → E.Action
coreAction (O.inbound a) = E.run (S.run (S.runMachine a))
coreAction a = E.run (S.run (S.runOutbound a))
coreAllowed : O.Action → State → Bool
coreAllowed (O.beginAcquire w req) s = peerOpen s ∧ newActors w (A.child req) (A.socketRef req) s ∧
  PS.governorAllowed (GP.run (Sub.core (O.beginAcquire w req))) (peers s) ∧
  GP.coreAllowed (O.beginAcquire w req) (PS.governor (peers s))
coreAllowed (O.beginRelease w key) s = peerOpen s ∧
  PS.governorAllowed (GP.run (Sub.core (O.beginRelease w key))) (peers s) ∧
  GP.coreAllowed (O.beginRelease w key) (PS.governor (peers s))
coreAllowed a s = PS.governorAllowed (GP.run (Sub.core a)) (peers s) ∧
  GP.coreAllowed a (PS.governor (peers s))
noteCore : O.Action → O.Configuration → C.Context → C.Context
noteCore a c k = record k { regions = GP.noteRegions (Sub.core a) c (C.regions k) }

data Action : Set where
  serverStep : E.Action → Action
  peerStep : PS.Action → Action
  coreStep : O.Action → Action
step : Action → State → Maybe State
step (serverStep a) s with serverAllowed a s
... | false = nothing
... | true with E.step a (server s)
...   | nothing = nothing
...   | just e = just (record s { server = e })
step (peerStep a) s with peerOpen s ∧ peerAllowed a s
... | false = nothing
... | true with PS.step a (peers s)
...   | nothing = nothing
...   | just p = just (combined (setSource (PS.cm p) (server s)) (C.capture p))
step (coreStep a) s with coreAllowed a s
... | false = nothing
... | true with E.step (coreAction a) (server s)
...   | nothing = nothing
...   | just e = just (combined e (noteCore a (E.source e) (context s)))

-- Finite shared executions retain all real writes; no progress is assumed.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s t u a as} → step a s ≡ just t → Executes t as u → Executes s (a ∷ as) u

-- Initiator capability is the immutable (handle, protocol, initiator-direction)
-- table from the application. The responder descriptor alone does not imply it.
module Protocols (canInitiate : HandleId → ℕ → Bool) where
  open import Data.Nat using (ℕ; zero; suc; pred)
  import Data.Nat as Nat
  open import Data.List using (_++_; length; map)
  open import Data.Maybe using (fromMaybe)
  open import ConnectionManagement.IGTypes using (Protocol; Temperature; RunResult; clean; errored; number)
  import ConnectionManagement.Rules.PeerActions as Peer
  import ConnectionManagement.Rules.ProductionPolicy as Policy
  open import ConnectionManagement.Rules.Pruning using (sortBy)
  open import Relation.Nullary using (does)
  import ConnectionManagement.Rules.MuxRuntime as Mux
  import ConnectionManagement.Rules.MuxJobTypes as Types
  import ConnectionManagement.Rules.CMShutdown as Close
  import ConnectionManagement.MuxPublicationUnwind as Publication
  open import ConnectionManagement.Store using (Store; put)
  private
    module N = Publication isBearerClosed
    module P = N.P
    module U = N.U
    module Pool = P.Pool

  -- Result-action identity is allocated at the caller's STM commit, before the
  -- controller knows the future physical JobId. Old generations remain stored.
  record Call : Set where
    constructor call
    field peerRef : PeerConnectionId
          handleRef : HandleId
          owner : WorkerId
          mux : MuxId
          descriptor : Protocol
          value : Maybe RunResult
          thread : Maybe JobId
  open Call public
  record Command : Set where
    constructor command
    field generation : RunId
          before : ℕ
  open Command public
  data Cursor : Set where
    idleC : Cursor
    selectedC tracingC forkReadyC : RunId → Cursor
    registeringC : RunId → JobId → Cursor
    failedC : RunId → N.R.Exception → Cursor
  record Front : Set where
    constructor frontend
    field calls : Store RunId Call
          commands : Store WorkerId (List Command)
          cursors : Store WorkerId Cursor
  open Front public
  empty : Front
  empty = frontend [] [] []
  record Runtime : Set where
    constructor runtime
    field base : State
          front : Front
  open Runtime public
  initialize : O.Configuration → G.State → Maybe Runtime
  initialize c g with initial c g
  ... | nothing = nothing
  ... | just b = just (runtime b empty)
  sourceOf : Runtime → O.Configuration
  sourceOf s = source (base s)
  publication : State → N.State
  publication b = S.base (E.base (server b))
  group : State → N.G.State
  group b = N.W.base (N.R.base (N.raw (publication b)))
  physical : State → P.State
  physical b = N.G.protocolState (group b)

  -- Replace only physical metadata; every surrounding fault/ticket/scope stays.
  setPhysical : P.State → State → State
  setPhysical p b = record b { server = record (server b)
    { base = record (E.base (server b)) { base = record n { base = record c
      { base = record d { base = record r { base = record w
        { base = N.G.setProtocols p (N.W.base w) } } } } } } } }
    where
    n = publication b
    c = N.base n
    d = N.C.base c
    r = N.D.base d
    w = N.R.base r
  physicalAction : P.Action → Action
  physicalAction a = serverStep (E.run (S.run (N.run (N.C.run (N.D.run (N.D.wrapMonitor (N.M.run a)))))))
  groupAction : Action → Maybe N.G.Action
  groupAction (serverStep (E.run (S.run (N.run (N.C.run (N.D.run (N.R.run (N.D.X.run (N.W.run a))))))))) = just a
  groupAction _ = nothing
  protocolAction : Action → Maybe P.Action
  protocolAction a with groupAction a
  ... | just (N.G.run (N.M.run p)) = just p
  ... | _ = nothing

  pending : WorkerId → Front → List Command
  pending w f = fromMaybe [] (lookup w (commands f))
  cursor : WorkerId → Front → Cursor
  cursor w f = fromMaybe idleC (lookup w (cursors f))
  idle : WorkerId → Front → Bool
  idle w f with cursor w f
  ... | idleC = true
  ... | _ = false
  setCursor : WorkerId → Cursor → Front → Front
  setCursor w c f = record f { cursors = put w c (cursors f) }
  latest : WorkerId → ℕ → Store RunId Call → Maybe (RunId × Call)
  latest w n [] = nothing
  latest w n ((rid , r) ∷ rest) with w ≟ owner r | n Nat.≟ number (descriptor r)
  ... | yes _ | yes _ = just (rid , r)
  ... | _ | _ = latest w n rest
  slotIdle : WorkerId → ℕ → Front → Bool
  slotIdle w n f with latest w n (calls f)
  ... | nothing = true
  ... | just (rid , r) with value r
  ...   | just clean = true
  ...   | _ = false
  byThread : JobId → Store RunId Call → Maybe (RunId × Call)
  byThread j [] = nothing
  byThread j ((rid , r) ∷ rest) with thread r
  ... | nothing = byThread j rest
  ... | just actual with j ≟ actual
  ...   | yes _ = just (rid , r)
  ...   | no _ = byThread j rest
  ownedThread : JobId → Front → Bool
  ownedThread j f with byThread j (calls f)
  ... | just _ = true
  ... | nothing = false

  -- A compact mixed FIFO: before counts legacy commands ahead of this start.
  -- New legacy appends stay behind earlier initiator commands. Every successful
  -- legacy pop decrements all outstanding counts for that same controller.
  legacyMayPop : WorkerId → Front → Bool
  legacyMayPop w f with pending w f
  ... | command rid zero ∷ _ = false
  ... | _ = true
  legacySelector : Action → Maybe WorkerId
  legacySelector a with groupAction a
  ... | just (N.G.run (N.M.run (P.control w P.selectCommand))) = just w
  ... | just (N.G.selectShutdown w) = just w
  ... | _ = nothing
  noteLegacy : Action → Front → Front
  noteLegacy a f with legacySelector a
  ... | nothing = f
  ... | just w = record f { commands = put w (map (λ c → record c { before = pred (before c) }) (pending w f)) (commands f) }
  controllerFree : WorkerId → State → Bool
  controllerFree w b = N.G.controllerOpen w (group b) ∧ N.M.localWaiting w (N.G.base (group b)) ∧
    N.R.free w (N.raw (publication b)) ∧ N.D.free w (N.C.base (N.base (publication b))) ∧ N.free w (publication b)
  inheritedProtocol : P.Action → Front → Bool
  inheritedProtocol (P.forkInitiator _ _ _ _) _ = false
  inheritedProtocol (P.registerProtocol j) f with ownedThread j f
  ... | true = false
  ... | false = true
  inheritedProtocol (P.commitClean j) f with ownedThread j f
  ... | true = false
  ... | false = true
  inheritedProtocol (P.protocolException j _) f with ownedThread j f
  ... | true = false
  ... | false = true
  inheritedProtocol (P.forkResponder _ _ rid) f with lookup rid (calls f)
  ... | nothing = true
  ... | just _ = false
  inheritedProtocol (P.control w (P.demand _)) f with pending w f
  ... | [] = true
  ... | _ ∷ _ = false
  inheritedProtocol _ _ = true
  controllerInheritedAllowed : Action → Runtime → Bool
  controllerInheritedAllowed a s with protocolAction a
  ... | just p with inheritedProtocol p (front s)
  ...   | false = false
  ...   | true = controllerAllowed a (front s)
    where
    controllerAllowed : Action → Front → Bool
    controllerAllowed a f with groupAction a
    ... | just (N.G.run m) with N.D.actorM m
    ...   | just w = idle w f ∧ selectorAllowed a f
      where
      selectorAllowed : Action → Front → Bool
      selectorAllowed a f with legacySelector a
      ... | nothing = true
      ... | just w = legacyMayPop w f
    ...   | nothing = true
    controllerAllowed a f | just (N.G.selectShutdown w) = idle w f ∧ legacyMayPop w f
    controllerAllowed a f | just (N.G.abortOwner w _) = idle w f
    controllerAllowed a f | _ = true
  controllerInheritedAllowed a s | nothing with groupAction a
  ... | just (N.G.run m) with N.D.actorM m
  ...   | just w = idle w (front s)
  ...   | nothing = true
  controllerInheritedAllowed a s | nothing | just (N.G.selectShutdown w) = idle w (front s) ∧ legacyMayPop w (front s)
  controllerInheritedAllowed a s | nothing | just (N.G.abortOwner w _) = idle w (front s)
  controllerInheritedAllowed a s | nothing | _ = true

  -- Resolve the captured handle and direction, never a current CM key binding.
  ownerFor : Peer.Peer → Store WorkerId U.Frame → Maybe WorkerId
  ownerFor peer [] = nothing
  ownerFor peer ((w , f) ∷ rest) with U.progress f
  ... | U.promisePublished hid mid with Peer.handleRef peer ≟ hid | Peer.muxRef peer ≟ mid
  ...   | yes _ | yes _ = just w
  ...   | _ | _ = ownerFor peer rest
  ownerFor peer ((_ , f) ∷ rest) | _ = ownerFor peer rest
  record Request : Set where
    constructor request
    field callerJob : JobId
          peerId : PeerConnectionId
          peer : Peer.Peer
          worker : WorkerId
          protocol : Protocol
  open Request public
  nextRequest : JobId → State → Maybe Request
  nextRequest j b with lookup j (Sub.jobs (PS.machine (peers b)))
  ... | nothing = nothing
  ... | just jf with J.pc (Sub.execution jf)
  ...   | J.startBundle t (n ∷ ns) with lookup (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (context b)))
  ...     | nothing = nothing
  ...     | just peer with ownerFor peer (U.frames (P.base (physical b)))
  ...       | nothing = nothing
  ...       | just w with Mux.findProtocol n (map Peer.descriptor (Peer.runs peer))
  ...         | nothing = nothing
  ...         | just proto = just (request j (J.connectionRef (Sub.execution jf)) peer w proto)
  nextRequest j b | just jf | _ = nothing
  startProblem : Request → Runtime → Maybe Mux.StartError
  startProblem req s with canInitiate (Peer.handleRef (peer req)) (number (protocol req)) |
    P.muxAt (Peer.muxRef (peer req)) (physical (base s))
  ... | false | _ = just Mux.unknownProtocol
  ... | true | nothing = just Mux.unknownProtocol
  ... | true | just m with Mux.status m
  ...   | Mux.stopping = just Mux.shutdownError
  ...   | Mux.stopped = just Mux.shutdownError
  ...   | Mux.failed _ = just Mux.shutdownError
  ...   | Mux.ready with slotIdle (worker req) (number (protocol req)) (front s)
  ...     | false = just Mux.alreadyRunning
  ...     | true = nothing
  enqueue : RunId → Request → Mux.Mux → Front → Front
  enqueue rid req m f = record f
    { calls = (rid , call (peerId req) (Peer.handleRef (peer req)) (worker req) (Peer.muxRef (peer req)) (protocol req) nothing nothing) ∷ calls f
    ; commands = put (worker req) (pending (worker req) f ++ (command rid (length (Mux.commands m)) ∷ [])) (commands f) }

  -- Local results are per generation. A newer start cannot erase an older
  -- completion, and an old body's later result cannot overwrite a current run.
  cacheResult : RunId → Call → RunResult → Front → State → State
  cacheResult rid r outcome f b with latest (owner r) (number (descriptor r)) (calls f)
  ... | nothing = b
  ... | just (current , _) with current ≟ rid
  ...   | no _ = b
  ...   | yes _ with lookup (peerRef r) (C.SubContext.peers (C.subsystem (context b)))
  ...     | nothing = b
  ...     | just peer with Peer.handleRef peer ≟ handleRef r | Peer.muxRef peer ≟ mux r
  ...       | yes _ | yes _ with Peer.finishRun (number (descriptor r)) outcome (Peer.runs peer)
  ...         | nothing = b
  ...         | just rs = record b { context = record (context b) { subsystem = record (C.subsystem (context b))
    { peers = put (peerRef r) (record peer { runs = rs }) (C.SubContext.peers (C.subsystem (context b))) } } }
  cacheResult rid r outcome f b | just (current , _) | yes _ | just peer | _ | _ = b
  data Observation : Set where
    localResult : RunResult → Observation
    shutdownResult : Mux.Status → Observation
  observe : RunId → Runtime → Maybe Observation
  observe rid s with lookup rid (calls (front s))
  ... | nothing = nothing
  ... | just r with value r
  ...   | just result = just (localResult result)
  ...   | nothing with P.muxAt (mux r) (physical (base s))
  ...     | nothing = nothing
  ...     | just m with Mux.status m
  ...       | Mux.ready = nothing
  ...       | status = just (shutdownResult status)


  -- Only published result actions are read. Unpublished caller cells cannot
  -- wake a waiter; NotRunning is constant, including across a later restart.
  data ReadCell : Set where
    never : ReadCell
    retired : RunResult → ReadCell
    blocked : ReadCell
    available : Observation → ReadCell
  publishedCell : PeerConnectionId → Peer.Peer → Peer.ProtocolRun → Runtime → ReadCell
  publishedCell ref p r s with Peer.published r
  ... | Peer.notStarted = never
  ... | Peer.notRunning result = retired result
  ... | Peer.returned result = available (localResult result)
  ... | Peer.running with ownerFor p (U.frames (P.base (physical (base s))))
  ...   | nothing = blocked
  ...   | just w with latest w (number (Peer.descriptor r)) (calls (front s))
  ...     | nothing = blocked
  ...     | just (rid , captured) with peerRef captured ≟ ref | handleRef captured ≟ Peer.handleRef p | mux captured ≟ Peer.muxRef p
  ...       | yes _ | yes _ | yes _ with observe rid s
  ...         | nothing = blocked
  ...         | just result = available result
  publishedCell ref p r s | Peer.running | just w | just (rid , captured) | _ | _ | _ = blocked

  -- The outer retry for NotStarted/NotRunning is after the ordered orElse.
  -- A retrying live action tries later numbers; a constant inactive first
  -- action blocks the entire bundle even when a later action has a result.
  firstCells : Temperature → PeerConnectionId → Peer.Peer → List Peer.ProtocolRun → Runtime → Maybe (ℕ × Observation)
  firstCells t ref p [] s = nothing
  firstCells t ref p (r ∷ rs) s with Peer.belongs t r
  ... | false = firstCells t ref p rs s
  ... | true with publishedCell ref p r s
  ...   | never = nothing
  ...   | retired _ = nothing
  ...   | blocked = firstCells t ref p rs s
  ...   | available result = just (number (Peer.descriptor r) , result)
  firstPublished : Temperature → PeerConnectionId → Peer.Peer → Runtime → Maybe (ℕ × Observation)
  firstPublished t ref p s = firstCells t ref p
    (sortBy (λ a b → does (Nat._<?_ (number (Peer.descriptor a)) (number (Peer.descriptor b)))) (Peer.runs p)) s
  allCells : Temperature → PeerConnectionId → Peer.Peer → List Peer.ProtocolRun → Runtime → Maybe (List (ℕ × Observation))
  allCells t ref p [] s = just []
  allCells t ref p (r ∷ rs) s with Peer.belongs t r
  ... | false = allCells t ref p rs s
  ... | true with publishedCell ref p r s | allCells t ref p rs s
  ...   | never | rest = rest
  ...   | retired result | just rest = just ((number (Peer.descriptor r) , localResult result) ∷ rest)
  ...   | available result | just rest = just ((number (Peer.descriptor r) , result) ∷ rest)
  ...   | _ | _ = nothing
  allPublished : Temperature → PeerConnectionId → Peer.Peer → Runtime → Maybe (List (ℕ × Observation))
  allPublished t ref p s = allCells t ref p
    (sortBy (λ a b → does (Nat._<?_ (number (Peer.descriptor a)) (number (Peer.descriptor b)))) (Peer.runs p)) s
  cleanObservation : Observation → Bool
  cleanObservation (localResult clean) = true
  cleanObservation _ = false
  allClean : List (ℕ × Observation) → Bool
  allClean [] = true
  allClean ((_ , result) ∷ rest) = cleanObservation result ∧ allClean rest
  firstPeer : PeerConnectionId → Peer.Peer → Runtime → Maybe (G.Kind × Observation)
  firstPeer ref p s with firstPublished ConnectionManagement.IGTypes.established ref p s
  ... | just (_ , result) = just (G.close , result)
  ... | nothing with firstPublished ConnectionManagement.IGTypes.warm ref p s
  ...   | just (_ , result) = just (G.close , result)
  ...   | nothing with firstPublished ConnectionManagement.IGTypes.hot ref p s
  ...     | just (_ , result) = just (G.deactivate , result)
  ...     | nothing = nothing

  -- This is a result read/continuation update, never a write to a physical
  -- completion cell, CM state or Async pool. Failed waits reach the existing
  -- failed-operation boundary; observed synchronous exception handling remains
  -- separate in PeerSupervision.
  record ReadState : Set where
    constructor readState
    field peerRows : Peer.Runtime
          jobRows : Store JobId Sub.JobFrame
          followups : Store PeerConnectionId J.Frame
  readStateOf : State → ReadState
  readStateOf b = readState (C.SubContext.peers k) (C.SubContext.jobs k) (C.SubContext.monitors k)
    where k = C.subsystem (context b)
  setReadState : ReadState → State → State
  setReadState r b = record b { context = record (context b) { subsystem = record (C.subsystem (context b))
    { peers = ReadState.peerRows r; jobs = ReadState.jobRows r; monitors = ReadState.followups r } } }
  readAllowed : Sub.Action → State → Bool
  readAllowed a b with C.policyStage (context b)
  ... | Policy.stopped _ = false
  ... | _ with GP.normalPool a (PS.governor (peers b))
  ...   | nothing = false
  ...   | just _ = peerOpen b ∧ peerAllowed (PS.run (GP.run a)) b ∧ PS.governorAllowed (GP.run a) (peers b)
  readAlias : Action → Bool
  readAlias (peerStep (PS.run (GP.run (Sub.pollPeer _ _)))) = true
  readAlias (peerStep (PS.run (GP.run (Sub.jobStep _ J.observeHot)))) = true
  readAlias (peerStep (PS.run (GP.run (Sub.jobStep _ J.observeAll)))) = true
  readAlias (peerStep (PS.run (GP.run (Sub.monitorStep _ J.observeHot)))) = true
  readAlias (peerStep (PS.run (GP.run (Sub.monitorStep _ J.observeAll)))) = true
  readAlias _ = false

  -- Physical reads have their own events; raw logical aliases cannot select
  -- an obsolete cached result instead of the current completion action.
  inheritAllowed : Action → Runtime → Bool
  inheritAllowed a s with readAlias a
  ... | true = false
  ... | false = controllerInheritedAllowed a s


  -- The eager start tracer runs in the restored pool body, before forkJob's
  -- masked birth/registration. Capture only an actually invoked, uncompleted
  -- start. The ignored initiator IG leg has no responder counter/queue effects.
  startTraceSelection : WorkerId → N.R.Exception → Runtime → Maybe (RunId × Store WorkerId N.R.Fault)
  startTraceSelection w result s with cursor w (front s) | controllerFree w (base s) |
    N.M.ownerContext w (N.G.base (group (base s)))
  ... | tracingC rid | true | just (f , mid) with lookup rid (calls (front s))
  ...   | just r with owner r ≟ w | mux r ≟ mid | thread r | value r
  ...     | yes _ | yes _ | nothing | nothing with N.R.start w result (λ _ _ → just N.R.poolBody) (N.raw (publication (base s)))
  ...       | just (N.R.local fs) = just (rid , fs)
  ...       | _ = nothing
  startTraceSelection w result s | tracingC rid | true | just (f , mid) | just r | _ | _ | _ | _ = nothing
  startTraceSelection w result s | tracingC rid | true | just (f , mid) | nothing = nothing
  startTraceSelection _ _ _ | _ | _ | _ = nothing

  -- Add the selected fault to the existing unwind layer without replacing its
  -- pool, source, tickets, handler or independent children.
  setStartFaults : Store WorkerId N.R.Fault → State → State
  setStartFaults fs b = record b { server = record (server b)
    { base = record (E.base (server b)) { base = record n { base = record c
      { base = record d { base = record r { faults = fs } } } } } } }
    where
    n = publication b
    c = N.base n
    d = N.C.base c
    r = N.D.base d
  startFaultState : WorkerId → RunId → N.R.Exception → Store WorkerId N.R.Fault → Runtime → Runtime
  startFaultState w rid result fs s = runtime (setStartFaults fs (base s))
    (setCursor w (failedC rid result) (front s))
  setStartShutdown : Close.State → State → State
  setStartShutdown coordinator b = record b { server = record (server b)
    { base = record (E.base (server b)) { base = record n { base = record c
      { base = record d { base = record r { base = N.W.setShutdown coordinator (N.R.base r) } } } } } } }
    where
    n = publication b
    c = N.base n
    d = N.C.base c
    r = N.D.base d

  -- Plans keep reusable proofs independent of normalization of the full stack.
  data Plan : Set where
    inherit : Action → Front → Plan
    caller : PS.Action → Front → Plan
    local : Front → Plan
    birth : WorkerId → U.Frame → Pool.State → JobId → RunId → Call → Front → Plan
    complete : Action → RunId → Call → RunResult → Plan
    reading : ReadState → Plan
    traceFault : WorkerId → RunId → N.R.Exception → Store WorkerId N.R.Fault → Plan
    deliverTraceFault : WorkerId → RunId → N.R.Exception → Store WorkerId N.R.Fault → Close.State → Plan
  data Event : Set where
    dispatch : Action → Event
    startNext : JobId → RunId → Event
    selectStart invokeStartTrace returnStartTrace : WorkerId → Event
    forkStart : WorkerId → JobId → Event
    registerStart commitClean : JobId → Event
    commitError : JobId → ErrorId → Event
    pollResults : PeerConnectionId → WorkerId → Event
    waitJobResults : JobId → Event
    waitMonitorResults : PeerConnectionId → Event
    observeStartTraceException : WorkerId → N.R.Exception → Event
    deliverStartTraceShutdown : ErrorId → Event

  -- Cold/demotion polling and successful local-result continuations retain the
  -- existing lower steps. Shutdown/error reads use the same permissions, but
  -- cannot be implemented by filling a fake protocol result in that layer.
  pollResultsPlan : PeerConnectionId → WorkerId → Runtime → Maybe Plan
  pollResultsPlan ref w s with readAllowed (Sub.pollPeer ref w) (base s) |
    lookup ref (C.SubContext.peers (C.subsystem (context (base s)))) |
    lookup ref (C.SubContext.monitors (C.subsystem (context (base s))))
  ... | true | just p | nothing with Peer.status p
  ...   | Peer.peerCold = just (inherit (peerStep (PS.run (GP.run (Sub.pollPeer ref w)))) (front s))
  ...   | Peer.peerCooling = just (inherit (peerStep (PS.run (GP.run (Sub.pollPeer ref w)))) (front s))
  ...   | _ with firstPeer ref p s
  ...     | nothing = nothing
  ...     | just (_ , result) with cleanObservation result
  ...       | true = just (inherit (peerStep (PS.run (GP.run (Sub.pollPeer ref w)))) (front s))
  ...       | false = just (reading (record (readStateOf (base s))
    { peerRows = put ref (Peer.cool p) (ReadState.peerRows (readStateOf (base s))) }))
  pollResultsPlan ref w s | true | just p | just f = just (inherit (peerStep (PS.run (GP.run (Sub.pollPeer ref w)))) (front s))
  pollResultsPlan _ _ _ | _ | _ | _ = nothing

  waitResults : J.Frame → Peer.Peer → Runtime → Maybe (List (ℕ × Observation))
  waitResults f p s with J.pc f
  ... | J.awaitHot = allPublished ConnectionManagement.IGTypes.hot (J.connectionRef f) p s
  ... | J.awaitAll with allPublished ConnectionManagement.IGTypes.hot (J.connectionRef f) p s |
    allPublished ConnectionManagement.IGTypes.warm (J.connectionRef f) p s |
    allPublished ConnectionManagement.IGTypes.established (J.connectionRef f) p s
  ...   | just hotResults | just warmResults | just establishedResults = just (hotResults ++ warmResults ++ establishedResults)
  ...   | _ | _ | _ = nothing
  waitResults _ _ _ | _ = nothing
  waitAction : J.Frame → J.Action
  waitAction f with J.pc f
  ... | J.awaitHot = J.observeHot
  ... | _ = J.observeAll
  failedPeer : J.Frame → Peer.Peer → Peer.Peer
  failedPeer f p with J.pc f
  ... | J.awaitHot = Peer.cool p
  ... | _ = p
  failedFrame : J.Frame → J.Frame
  failedFrame f = record f { pc = J.awaitCold G.failed }
  waitJobPlan : JobId → Runtime → Maybe Plan
  waitJobPlan j s with lookup j (C.SubContext.jobs (C.subsystem (context (base s))))
  ... | nothing = nothing
  ... | just jf with Sub.queued jf | lookup (J.connectionRef (Sub.execution jf)) (C.SubContext.peers (C.subsystem (context (base s)))) |
    readAllowed (Sub.jobStep j (waitAction (Sub.execution jf))) (base s)
  ...   | false | just p | true with waitResults (Sub.execution jf) p s
  ...     | nothing = nothing
  ...     | just results with allClean results
  ...       | true = just (inherit (peerStep (PS.run (GP.run (Sub.jobStep j (waitAction (Sub.execution jf)))))) (front s))
  ...       | false = just (reading (record (readStateOf (base s))
    { peerRows = put (J.connectionRef (Sub.execution jf)) (failedPeer (Sub.execution jf) p) (ReadState.peerRows (readStateOf (base s)))
    ; jobRows = put j (record jf { execution = failedFrame (Sub.execution jf) }) (ReadState.jobRows (readStateOf (base s))) }))
  waitJobPlan _ _ | just jf | _ | _ | _ = nothing
  waitMonitorPlan : PeerConnectionId → Runtime → Maybe Plan
  waitMonitorPlan ref s with lookup ref (C.SubContext.monitors (C.subsystem (context (base s))))
  ... | nothing = nothing
  ... | just f with lookup (J.connectionRef f) (C.SubContext.peers (C.subsystem (context (base s)))) |
    readAllowed (Sub.monitorStep ref (waitAction f)) (base s)
  ...   | just p | true with waitResults f p s
  ...     | nothing = nothing
  ...     | just results with allClean results
  ...       | true = just (inherit (peerStep (PS.run (GP.run (Sub.monitorStep ref (waitAction f))))) (front s))
  ...       | false = just (reading (record (readStateOf (base s))
    { peerRows = put (J.connectionRef f) (failedPeer f p) (ReadState.peerRows (readStateOf (base s)))
    ; followups = put ref (failedFrame f) (ReadState.followups (readStateOf (base s))) }))
  waitMonitorPlan _ _ | just f | _ | _ = nothing

  selectPlan : WorkerId → Runtime → Maybe Plan
  selectPlan w s with idle w (front s) | pending w (front s) | controllerFree w (base s) |
    N.M.ownerContext w (N.G.base (group (base s)))
  ... | true | command rid zero ∷ rest | true | just (f , mid) with
    P.muxAt mid (physical (base s)) | P.noParent (P.poolAt w (physical (base s))) |
    P.noResults (P.poolAt w (physical (base s))) | Pool.phase (P.poolAt w (physical (base s)))
  ...   | just m | true | true | Pool.openPool with Mux.status m | Mux.callback m
  ...     | Mux.ready | Mux.returned = just (local (setCursor w (selectedC rid)
    (record (front s) { commands = put w rest (commands (front s)) })))
  ...     | _ | _ = nothing
  selectPlan w s | true | command rid zero ∷ rest | true | just (f , mid) | _ | _ | _ | _ = nothing
  selectPlan _ _ | _ | _ | _ | _ = nothing
  forkPlan : WorkerId → JobId → Runtime → Maybe Plan
  forkPlan w j s with cursor w (front s) | controllerFree w (base s) |
    lookup w (U.frames (P.base (physical (base s))))
  ... | forkReadyC rid | true | just f with lookup rid (calls (front s)) |
    P.fresh j rid (physical (base s)) | P.noParent (P.poolAt w (physical (base s)))
  ...   | just r | true | true with owner r ≟ w | thread r | value r | Pool.step (Pool.fork j) (P.poolAt w (physical (base s)))
  ...     | yes _ | nothing | nothing | just p = just (birth w f p j rid r
    (setCursor w (registeringC rid j) (record (front s) { calls = put rid (record r { thread = just j }) (calls (front s)) })))
  ...     | _ | _ | _ | _ = nothing
  forkPlan w j s | forkReadyC rid | true | just f | _ | _ | _ = nothing
  forkPlan _ _ _ | _ | _ | _ = nothing
  registerPlan : JobId → Runtime → Maybe Plan
  registerPlan j s with byThread j (calls (front s))
  ... | nothing = nothing
  ... | just (rid , r) with cursor (owner r) (front s)
  ...   | registeringC actual target with rid ≟ actual | j ≟ target
  ...     | yes _ | yes _ = just (inherit (physicalAction (P.registerProtocol j)) (setCursor (owner r) idleC (front s)))
  ...     | _ | _ = nothing
  registerPlan j s | just (rid , r) | _ = nothing
  completionPlan : JobId → RunResult → Runtime → Maybe Plan
  completionPlan j result s with byThread j (calls (front s)) | lookup j (P.jobs (physical (base s)))
  ... | just (rid , r) | just physicalJob with value r | Types.owner physicalJob ≟ owner r | Types.generation physicalJob ≟ rid |
    Types.protocolNumber physicalJob Nat.≟ number (descriptor r) | Types.direction physicalJob
  ...   | nothing | yes _ | yes _ | yes _ | Mux.initiatorJob = just (complete (physicalAction (action result)) rid r result)
    where
    action : RunResult → P.Action
    action clean = P.commitClean j
    action (errored err) = P.protocolException j err
  ...   | _ | _ | _ | _ | _ = nothing
  completionPlan _ _ _ | _ | _ = nothing
  choose : Event → Runtime → Maybe Plan
  choose (dispatch a) s with inheritAllowed a s
  ... | true = just (inherit a (noteLegacy a (front s)))
  ... | false = nothing
  choose (startNext j rid) s with peerOpen (base s) | nextRequest j (base s) | lookup rid (calls (front s)) |
    P.generationFresh rid (P.jobs (physical (base s)))
  ... | true | just req | nothing | true with startProblem req s | P.muxAt (Peer.muxRef (peer req)) (physical (base s))
  ...   | nothing | just m = just (caller (PS.run (GP.run (Sub.jobStep j J.runNext))) (enqueue rid req m (front s)))
  ...   | _ | _ = nothing
  choose (startNext _ _) _ | _ | _ | _ | _ = nothing
  choose (selectStart w) s = selectPlan w s
  choose (invokeStartTrace w) s with cursor w (front s) | controllerFree w (base s)
  ... | selectedC rid | true = just (local (setCursor w (tracingC rid) (front s)))
  ... | _ | _ = nothing
  choose (returnStartTrace w) s with cursor w (front s) | controllerFree w (base s)
  ... | tracingC rid | true = just (local (setCursor w (forkReadyC rid) (front s)))
  ... | _ | _ = nothing
  choose (forkStart w j) s = forkPlan w j s
  choose (registerStart j) s = registerPlan j s
  choose (commitClean j) s = completionPlan j clean s
  choose (commitError j err) s = completionPlan j (errored err) s
  choose (pollResults ref w) s = pollResultsPlan ref w s
  choose (waitJobResults j) s = waitJobPlan j s
  choose (waitMonitorResults ref) s = waitMonitorPlan ref s
  choose (observeStartTraceException w result) s with startTraceSelection w result s
  ... | just (rid , fs) = just (traceFault w rid result fs)
  ... | nothing = nothing
  choose (deliverStartTraceShutdown err) s with S.inCMClose (S.stage (E.base (server (base s)))) |
    Close.phase (N.W.shutdown (N.R.base (N.raw (publication (base s)))))
  ... | true | Close.awaitDelivery _ w with startTraceSelection w (N.R.async err) s
  ...   | just (rid , fs) with N.W.control Close.acknowledgeDelivery (N.R.base (N.raw (publication (base s))))
  ...     | just received = just (deliverTraceFault w rid (N.R.async err) fs (N.W.shutdown received))
  ...     | nothing = nothing
  choose (deliverStartTraceShutdown err) s | true | Close.awaitDelivery _ w | nothing = nothing
  choose (deliverStartTraceShutdown _) _ | _ | _ = nothing
  enact : Plan → Runtime → Maybe Runtime
  enact (inherit a f) s with step a (base s)
  ... | nothing = nothing
  ... | just b = just (runtime b f)
  enact (caller a f) s with PS.step a (peers (base s))
  ... | nothing = nothing
  ... | just p = just (runtime (combined (setSource (PS.cm p) (server (base s))) (C.capture p)) f)
  enact (local f) s = just (record s { front = f })
  enact (reading r) s = just (record s { base = setReadState r (base s) })
  enact (traceFault w rid result fs) s = just (startFaultState w rid result fs s)
  enact (deliverTraceFault w rid result fs coordinator) s = just
    (record (startFaultState w rid result fs s)
      { base = setStartShutdown coordinator (base (startFaultState w rid result fs s)) })
  enact (birth w capturedFrame pool j rid r f) s = just (runtime (setPhysical
    (record (P.setPool w capturedFrame pool (physical (base s)))
      { jobs = put j (Types.protocolJob w (mux r) Mux.initiatorJob (number (descriptor r)) rid Types.executing) (P.jobs (physical (base s))) })
    (base s)) f)
  enact (complete a rid r result) s with step a (base s)
  ... | nothing = nothing
  ... | just b = just (runtime (cacheResult rid r result (front s) b)
    (record (front s) { calls = put rid (record r { value = just result }) (calls (front s)) }))
  advance : Event → Runtime → Maybe Runtime
  advance a s with choose a s
  ... | nothing = nothing
  ... | just p = enact p s
  data Runs : Runtime → List Event → Runtime → Set where
    stop : ∀ {s} → Runs s [] s
    more : ∀ {s t u a as} → advance a s ≡ just t → Runs t as u → Runs s (a ∷ as) u

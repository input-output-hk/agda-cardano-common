{-# OPTIONS --guardedness #-}

-- Shared Server/PSA/governor composition for the post-setup, normal callback
-- return profile. Peer protocol birth/results still require physical coupling;
-- their raw logical shortcuts are refused rather than adopted as actual jobs.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.ServerPeers
  (isBearerClosed isIOManagerError : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
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

{-# OPTIONS --guardedness #-}

-- Source peer actions and governor jobs, with separate CM calls and returns.
module ConnectionManagement.Rules.PeerJobs where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (Temperature; RunResult; clean; errored; number)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.PeerActions as P
import ConnectionManagement.Rules.OutboundGovernor as G
import ConnectionManagement.Rules.IGRegistration as IG

data PC : Set where
  begin awaitAcquire : PC
  startBundle : Temperature → List ℕ → PC
  publishBundle : Temperature → PC
  markWarm forkMonitor finishActivation awaitHot awaitAll callRelease awaitRelease : PC
  delayFailure : PC
  awaitCold : G.Outcome → PC
  complete : G.Outcome → PC
  -- Retain the returned exception across policy selection and delivery.
  acquirePolicy nodeDelivery nodeRethrow : Cases.Fault → PC
record Frame : Set where
  constructor frame
  field work : G.Job
        caller child : WorkerId
        socketRef : SocketId
        connectionRef : PeerConnectionId
        pc : PC
open Frame public

record World : Set where
  constructor world
  field cm : CM.Configuration
        peers : P.Runtime
open World public

-- Operate on the captured peer handle, never re-look it up by remote address.
peerStep : P.Action → Frame → World → Maybe World
peerStep action f w with lookup (connectionRef f) (peers w)
... | nothing = nothing
... | just p with P.step action p (Inbound.inboundGovernor (CM.core (cm w))) (Inbound.world (CM.core (cm w)))
...   | nothing = nothing
...   | just (p′ , ig′) = just (world
  (record (cm w) { core = record (CM.core (cm w)) { inboundGovernor = ig′ } })
  (put (connectionRef f) p′ (peers w)))
set : Frame → PC → World → Frame × World
set f pc w = record f { pc = pc } , w
protocols : Temperature → P.Peer → List ℕ
protocols t p = map (λ r → number (P.descriptor r)) (filterᵇ (P.belongs t) (P.runs p))
start : Temperature → Frame → World → Maybe (Frame × World)
start t f w with lookup (connectionRef f) (peers w)
... | nothing = nothing
... | just p = just (set f (startBundle t (protocols t p)) w)

-- Completion production is separate from publishing into the governor queue.
data Action : Set where
  enter collectAcquire runNext publishStarted markEstablished launchMonitor : Action
  finishHotAt : ℕ → Action
  observeHot observeAll requestRelease collectRelease observeCold : Action
  operationTimeout demotionTimeout failureDelayElapsed : Action
  startFailed : ErrorId → Action
  choosePeerPolicy chooseNodePolicy deliverNodeException rethrowNodeException : Action

-- A failed establishment's bracket restores PeerCold. The policy PCs retain
-- the returned fault; the final governor outcome still erases it to failed.
failedEstablishment : Frame → World → Frame × World
failedEstablishment f w with lookup (connectionRef f) (peers w)
... | nothing = set f (complete G.failed) w
... | just p = set f (complete G.failed) (record w
  { peers = put (connectionRef f) (record p { status = P.peerCold }) (peers w) })

step : Action → Frame → World → Maybe (Frame × World)
step enter f w with pc f | G.kind (work f)
... | begin | G.establish with CM.advance (CM.beginAcquire (caller f)
    (A.acquireRequest (G.peer (work f)) (child f) (socketRef f) outbound nothing)) (cm w)
...   | nothing = nothing
...   | just c = just (set f awaitAcquire (record w { cm = c }))
step enter f w | begin | G.activate with peerStep P.activate f w
... | nothing = just (set f delayFailure w)
... | just w′ = start ConnectionManagement.IGTypes.hot f w′
step enter f w | begin | G.deactivate with lookup (connectionRef f) (peers w)
... | nothing = nothing
... | just p with P.status p
...   | P.peerWarm = just (set f (complete G.succeeded) w)
...   | P.peerHot with peerStep P.deactivate f w
...     | nothing = nothing
...     | just w′ = just (set f awaitHot w′)
step enter f w | begin | G.deactivate | just p | _ = just (set f (awaitCold G.failed) w)
step enter f w | begin | G.close with lookup (connectionRef f) (peers w) | peerStep P.close f w
... | just p | just w′ with P.status p
...   | P.peerCooling = just (set f (awaitCold G.succeeded) w′)
...   | P.peerCold = just (set f (awaitCold G.succeeded) w′)
...   | _ = just (set f awaitAll w′)
step enter f w | begin | G.close | _ | _ = nothing
step enter f w | _ | _ = nothing
step collectAcquire f w with pc f | lookup (caller f) (CM.acquired (cm w))
... | awaitAcquire | just (Cases.connected k flow h) with lookup h (IG.handles (IG.execution (Inbound.inboundGovernor (CM.core (cm w))))) | lookup (connectionRef f) (peers w)
...   | just hd | nothing = start ConnectionManagement.IGTypes.warm f
  (record w { peers = put (connectionRef f) (P.initialPeer k h hd) (peers w) })
...   | _ | _ = nothing
step collectAcquire f w | awaitAcquire | just (Cases.raised fault) = just (set f (acquirePolicy fault) w)
step collectAcquire f w | awaitAcquire | just _ = just (failedEstablishment f w)
step collectAcquire f w | _ | _ = nothing
step runNext f w with pc f
... | startBundle t [] = just (set f (publishBundle t) w)
... | startBundle t (n ∷ ns) with peerStep (P.startProtocol t n) f w
...   | nothing = nothing
...   | just w′ = just (set f (startBundle t ns) w′)
step runNext f w | _ = nothing
step publishStarted f w with pc f
... | publishBundle t with peerStep (P.publishProtocols t) f w
...   | nothing = nothing
...   | just w′ with t
...     | ConnectionManagement.IGTypes.warm = start ConnectionManagement.IGTypes.established f w′
...     | ConnectionManagement.IGTypes.established = just (set f markWarm w′)
...     | ConnectionManagement.IGTypes.hot = just (set f finishActivation w′)
step publishStarted f w | _ = nothing
step markEstablished f w with pc f
... | markWarm with peerStep P.markWarm f w
...   | nothing = nothing
...   | just w′ = just (set f forkMonitor w′)
step markEstablished f w | _ = nothing
step launchMonitor f w with pc f
... | forkMonitor with peerStep P.forkMonitor f w
...   | nothing = nothing
...   | just w′ = just (set f (complete (G.establishedOK (connectionRef f))) w′)
step launchMonitor f w | _ = nothing
step (finishHotAt time) f w with pc f
... | finishActivation with peerStep (P.markPromoted time) f w
...   | nothing = nothing
...   | just w′ = just (set f (complete G.succeeded) w′)
step (finishHotAt time) f w | _ = nothing
step observeHot f w with pc f | lookup (connectionRef f) (peers w)
... | awaitHot | just p with P.all ConnectionManagement.IGTypes.hot (P.runs p) | peerStep P.finishDeactivate f w
...   | just clean | just w′ = just (set f (complete G.succeeded)
  (record w′ { peers = put (connectionRef f) (record p { status = finalStatus (P.status p); runs = P.retireHot (P.runs p); promotedAt = nothing }) (peers w′) }))
  where
  finalStatus : P.Status → P.Status
  finalStatus P.peerHot = P.peerWarm
  finalStatus status = status
...   | just (errored _) | just w′ = just (set f (awaitCold G.failed) w′)
...   | _ | _ = nothing
step observeHot f w | _ | _ = nothing
step observeAll f w with pc f | lookup (connectionRef f) (peers w)
... | awaitAll | just p with P.all ConnectionManagement.IGTypes.hot (P.runs p) | P.all ConnectionManagement.IGTypes.warm (P.runs p) | P.all ConnectionManagement.IGTypes.established (P.runs p)
...   | just clean | just clean | just clean = just (set f callRelease w)
...   | just _ | just _ | just _ = just (set f (awaitCold G.failed) w)
...   | _ | _ | _ = nothing
step observeAll f w | _ | _ = nothing
step requestRelease f w with pc f | lookup (connectionRef f) (peers w)
... | callRelease | just p with CM.advance (CM.beginRelease (caller f) (P.key p)) (cm w)
...   | nothing = nothing
...   | just c = just (set f awaitRelease (record w { cm = c }))
step requestRelease f w | _ | _ = nothing
step collectRelease f w with pc f | lookup (caller f) (CM.released (cm w))
... | awaitRelease | just R.assertionFailure = just (set f (awaitCold G.failed) w)
... | awaitRelease | just _ = just (set f (awaitCold G.succeeded) w)
... | _ | _ = nothing
step observeCold f w with pc f | lookup (connectionRef f) (peers w)
... | awaitCold result | just p with P.status p
...   | P.peerCold = just (set f (complete result) w)
...   | _ = nothing
step observeCold f w | _ | _ = nothing
step operationTimeout f w with pc f
... | awaitHot with peerStep P.timeoutDeactivate f w
...   | nothing = nothing
...   | just w′ = just (set f (awaitCold G.failed) w′)
step operationTimeout f w | awaitAll with peerStep P.timeoutClose f w
... | nothing = nothing
... | just w′ = just (set f (awaitCold G.succeeded) w′)
step operationTimeout f w | _ = nothing
step demotionTimeout f w with pc f
... | awaitCold _ = just (set f (complete G.demotionTimedOut) w)
... | _ = nothing
step failureDelayElapsed f w with pc f
... | delayFailure = just (set f (complete G.failed) w)
... | _ = nothing
step (startFailed err) f w with pc f | G.kind (work f)
... | startBundle t (n ∷ _) | G.establish with peerStep (P.startProtocol t n) f w
...   | nothing = just (failedEstablishment f w)
...   | just _ = nothing
step (startFailed err) f w | startBundle t (n ∷ _) | G.activate with peerStep (P.startProtocol t n) f w
... | nothing = just (set f delayFailure w)
... | just _ = nothing
step (startFailed err) f w | _ | _ = nothing
step choosePeerPolicy f w with pc f
... | acquirePolicy fault = just (failedEstablishment f w)
... | _ = nothing
step chooseNodePolicy f w with pc f
... | acquirePolicy fault = just (set f (nodeDelivery fault) w)
... | _ = nothing
-- Delivery acknowledgment precedes the sender's local rethrow and bracket cleanup.
step deliverNodeException f w with pc f
... | nodeDelivery fault = just (set f (nodeRethrow fault) w)
... | _ = nothing
step rethrowNodeException f w with pc f
... | nodeRethrow fault = just (failedEstablishment f w)
... | _ = nothing

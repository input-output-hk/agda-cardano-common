{-# OPTIONS --guardedness #-}

-- Server.hs:147-254 at the network pin. One initialized listener, normal
-- callback/race cleanup, no pending IG CM call at receipt, and empty published
-- IG on exit. Owned infrastructure
-- starts after its withAsync setup; admission Asyncs require actual observed
-- accepted-socket handoff/fork. This is not full Server/whole-node shutdown.
open import ConnectionManagement.Domain using (ErrorId)
open import Data.Bool using (Bool)
module ConnectionManagement.ServerAdmission (isBearerClosed : ErrorId → Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.Nat using (ℕ; suc)
import Data.Nat as Nat
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.MuxPublicationUnwind as Publication
private
  module N = Publication isBearerClosed
  module C = N.C
  module D = N.D
  module R = N.R
  module X = D.X
  module W = N.W
  module G = N.G
  module M = N.M
  module P = N.P
  module U = N.U

-- Close failures retain the replacement exception, including an async fault.
data Fault : Set where
  sync async : ErrorId → Fault
error : Fault → ErrorId
error (sync e) = e
error (async e) = e
data Result : Set where
  returned : Result
  raised : Fault → Result
data WorkerPC : Set where
  calling closeDisconnected : WorkerPC
  closeException : Fault → WorkerPC
  closePrefix : Shared.Failure → Result → WorkerPC
  bodyExited resultAvailable : Result → WorkerPC
record Worker : Set where
  constructor rawWorker
  field request : Shared.Admission
        pc : WorkerPC
        closeCalls : ℕ
open Worker public

-- The Server.with thread's progress through the single-listener async/race
-- tree. Listener close, IG's actual shared cleanup and CM's result wait are
-- distinct.
data Stage : Set where
  serving actionBodyExited actionResultAvailable closingAccept acceptCancelRequested
    acceptCancelDelivered acceptBodyExited acceptResultAvailable acceptJoined
    serverStopped actionJoined igCancelRequested igJoined closingCM serverReturned : Stage
  -- The accept loop raised on its own (a fatal AcceptFailure, or a failure
  -- after accept); its finally has not yet closed the listener.
  acceptFailed : Stage
  -- Bare async threw synchronously before birth; the accepted socket remains
  -- owned by the accept loop's masked onException cleanup until close returns.
  acceptForkClosing : SocketId → ErrorId → Stage
-- The inbound-governor thread's own progress (InboundGovernor.hs 194-235). Its
-- catch body (deactivate, drain, final trace, rethrow) runs on the IG thread,
-- whether it was entered by the Server's cancellation or by the IG's own
-- failure, while the Server thread may still be serving.
data IGPhase : Set where
  igLive igCaught igInactive igFlushed igBodyExited igResultAvailable : IGPhase
-- The IG phase at each Server stage on the cancellation path, outside the IG
-- catch: live until the Server cancels it, finished once it is joined.
cancelPathIG : Stage → IGPhase
cancelPathIG igJoined = igResultAvailable
cancelPathIG closingCM = igResultAvailable
cancelPathIG serverReturned = igResultAvailable
cancelPathIG _ = igLive
record State : Set where
  constructor serverState
  field base : N.State
        workers : Store WorkerId Worker
        stage : Stage
        listenerOpen : Bool
        ig : IGPhase
open State public
source : State → O.Configuration
source s = N.source (base s)
shared : State → Shared.State
shared s = Machine.world (O.core (source s))
setSource : O.Configuration → State → State
setSource c s = record s { base = record (base s)
  { base = record (N.base (base s)) { base = record (C.base (N.base (base s)))
    { base = R.setSource c (N.raw (base s)) } } } }
setWorld : Shared.State → State → State
setWorld world s = setSource (record (source s) { core = Machine.replaceWorld (O.core (source s)) world }) s
initial : O.Configuration → Maybe State
initial c with Shared.admissions (Machine.world (O.core c)) | Shared.sockets (Machine.world (O.core c)) | N.initial c
... | [] | [] | just n = just (serverState n [] serving true igLive)
... | _ | _ | _ = nothing

accepting : Stage → Bool
accepting serving = true
accepting actionBodyExited = true
accepting actionResultAvailable = true
accepting closingAccept = true
accepting acceptCancelRequested = true
accepting _ = false
reservedChild : WorkerId → Store WorkerId Shared.AdmissionWorker → Bool
reservedChild w [] = false
reservedChild w ((_ , a) ∷ rest) with w ≟ Shared.child (Shared.request a)
... | yes _ = true
... | no _ = reservedChild w rest
fresh : WorkerId → State → Bool
fresh w s with lookup w (workers s) | lookup w (Shared.admissions (shared s)) |
  lookup w (Shared.handlers (shared s)) | lookup w (O.acquiring (source s)) |
  lookup w (O.releasing (source s)) | lookup w (O.acquired (source s)) |
  lookup w (O.released (source s)) | lookup w (B.threads (W.physical (R.base (N.raw (base s))))) |
  reservedChild w (Shared.admissions (shared s))
... | nothing | nothing | nothing | nothing | nothing | nothing | nothing | nothing | false = true
... | _ | _ | _ | _ | _ | _ | _ | _ | _ = false

-- Server's captured hard limit is constant. The first immutable worker
-- request observes it; historical workers retain that value after completion.
sameLimit : Shared.Admission → Store WorkerId Worker → Bool
sameLimit req [] = true
sameLimit req ((_ , t) ∷ _) = does (Shared.hardLimit req Nat.≟ Shared.hardLimit (request t))

-- Fresh symbolic identities are incarnation tokens, including the handler's
-- reserved child token. No existing admission is adopted as physical history.
forkAccepted : WorkerId → Shared.Admission → State → Maybe State
forkAccepted w req s with accepting (stage s) | listenerOpen s | sameLimit req (workers s) | fresh w s | fresh (Shared.child req) s |
  w ≟ Shared.child req | lookup (Shared.socketRef req) (Shared.sockets (shared s))
... | true | true | true | true | true | no _ | nothing = just (record
  (setWorld (record (shared s)
    { admissions = put w (Shared.admissionWorker req Shared.acquireMap) (Shared.admissions (shared s))
    ; sockets = put (Shared.socketRef req) (Shared.admitting w) (Shared.sockets (shared s)) }) s)
  { workers = put w (rawWorker req calling 0) (workers s) })
... | _ | _ | _ | _ | _ | _ | _ = nothing
running : WorkerId → State → Bool
running w s with lookup w (workers s)
... | just t with pc t
...   | calling = true
...   | _ = false
running w s | nothing = false
resultOf : WorkerId → State → Maybe Result
resultOf w s with lookup w (workers s)
... | just t with pc t
...   | resultAvailable r = just r
...   | _ = nothing
resultOf w s | nothing = nothing
allResults : Store WorkerId Worker → Bool
allResults [] = true
allResults ((_ , t) ∷ rest) with pc t
... | resultAvailable _ = allResults rest
... | _ = false

-- Exact source dispatch path; the old handler/mux guards remain in force.
runMachine : Machine.Action → N.Action
runMachine a = N.run (C.run (D.run (R.run (X.run (W.run (G.run (M.run (P.run (U.run (B.handler (H.run a)))))))))))
machineAction : N.Action → Maybe Machine.Action
machineAction (N.run (C.run (D.run (R.run (X.run (W.run (G.run (M.run (P.run (U.run (B.handler (H.run a)))))))))))) = just a
machineAction _ = nothing
runOutbound : O.Action → N.Action
runOutbound a = N.run (C.run (D.run (R.run (X.run (W.run (G.run (M.run (P.run (U.run (B.outbound a))))))))))
-- Coupled physical release receipts still belong to their source caller.
-- Keep caller-role and outer governor cancellation checks on these new labels.
releaseReceiptCaller : N.Action → Maybe WorkerId
releaseReceiptCaller (N.run (C.run (D.run (R.run (X.run (W.deliverReleaseMux caller err)))))) = just caller
releaseReceiptCaller (N.run (C.run (D.run (R.run (X.run (W.acknowledgeReleaseFinished caller)))))) = just caller
releaseReceiptCaller (N.run (C.run (D.run (R.run (X.run (W.deliverReleaseTimeWait caller err)))))) = just caller
releaseReceiptCaller _ = nothing
outboundCaller : N.Action → Maybe WorkerId
outboundCaller (N.run (C.run (D.run (R.run (X.run (W.run (G.run (M.run (P.run (U.run (B.outbound a))))))))))) = caller a
  where
  caller : O.Action → Maybe WorkerId
  caller (O.beginAcquire w _) = just w
  caller (O.acquire w _) = just w
  caller (O.beginRelease w _) = just w
  caller (O.release w _) = just w
  caller (O.inbound _) = nothing
outboundCaller a = releaseReceiptCaller a

-- Raw admission workers have one role and historical identities. An unrelated
-- outbound caller cannot reuse that identity after the admission body exits.
foreignCallerAllowed : N.Action → State → Bool
foreignCallerAllowed a s with outboundCaller a
... | nothing = true
... | just w with lookup w (workers s)
...   | nothing = true
...   | just _ = false
cmAction : N.Action → Bool
cmAction (N.run (C.run (D.run (R.run (X.run (W.deliverShutdownHandshake _ _)))))) = true
cmAction (N.run (C.run (D.run (R.run (X.run (W.shutdownStep _)))))) = true
cmAction (N.deliverShutdown _ _) = true
cmAction _ = false
inCMClose : Stage → Bool
inCMClose closingCM = true
inCMClose _ = false
igRunning : IGPhase → Bool
igRunning igLive = true
igRunning _ = false
igBodyAction : IG.IGAction → Bool
igBodyAction (IG.captureTime _) = true
igBodyAction IG.registerInactivity = true
igBodyAction IG.selectBatch = true
igBodyAction IG.readEvent = true
igBodyAction IG.registerIdleTimer = true
igBodyAction IG.runResponders = true
igBodyAction IG.commitDecision = true
igBodyAction IG.requestFailedStop = true
igBodyAction IG.finishBatch = true
igBodyAction IG.pollStopped = true
igBodyAction IG.restart = true
igBodyAction _ = false
machineAllowed : Machine.Action → State → Bool
-- Prefix close is now coupled to the raw worker body. The lower primitive
-- remains unchanged; its unaccompanied alias cannot bypass physical metadata.
machineAllowed (Machine.admissionStep w Admission.close) s = false
machineAllowed (Machine.admissionStep w Admission.restoreBody) s = false
machineAllowed (Machine.admissionStep w _) s = running w s
machineAllowed (Machine.handshakeStep w _) s = running w s
machineAllowed (Machine.igStep IG.deactivateIG) s = false
machineAllowed (Machine.igStep IG.flushOnExit) s = false
machineAllowed (Machine.igStep a) s with igBodyAction a
... | true = igRunning (ig s)
... | false = true
machineAllowed _ s = true
allowed : N.Action → State → Bool
allowed a s with foreignCallerAllowed a s | cmAction a | machineAction a
... | false | _ | _ = false
... | true | true | _ = inCMClose (stage s)
... | true | false | just action = machineAllowed action s
... | true | false | nothing = true
inherit : N.Action → State → Maybe State
inherit a s with allowed a s
... | false = nothing
... | true with N.step a (base s)
...   | nothing = nothing
...   | just n = just (record s { base = n })
setPC : WorkerId → Worker → WorkerPC → State → State
setPC w t next s = record s { workers = put w (record t { pc = next }) (workers s) }
observeReturn : WorkerId → State → Maybe State
observeReturn w s with lookup w (workers s) | lookup w (Shared.admissions (shared s))
... | just t | just a with pc t | Shared.pc a
...   | calling | Shared.completedHandshake (Shared.connected _) = just (setPC w t (bodyExited returned) s)
...   | calling | Shared.completedHandshake (Shared.disconnected _) = just (setPC w t closeDisconnected s)
...   | _ | _ = nothing
observeReturn w s | _ | _ = nothing

-- Hard-limit is a normal Disconnected return; forbidden/fork failure are
-- exceptions propagated after the original map restoration. No close repeats
-- the restore, rewinds the entry heap, or fabricates a handler Async.
prefixReturned : WorkerId → State → Maybe State
prefixReturned w s with lookup w (workers s) | lookup w (Shared.admissions (shared s))
... | just t | just a with pc t | Shared.pc a
...   | calling | Shared.closeSocket Shared.hardLimitReached = just (setPC w t (closePrefix Shared.hardLimitReached returned) s)
...   | _ | _ = nothing
prefixReturned w s | _ | _ = nothing
prefixException : WorkerId → ErrorId → State → Maybe State
prefixException w err s with lookup w (workers s) | lookup w (Shared.admissions (shared s))
... | just t | just a with pc t | Shared.pc a
...   | calling | Shared.closeSocket Shared.forbidden = just (setPC w t (closePrefix Shared.forbidden (raised (sync err))) s)
...   | calling | Shared.closeSocket Shared.forkFailed = just (setPC w t (closePrefix Shared.forkFailed (raised (sync err))) s)
...   | _ | _ = nothing
prefixException w err s | _ | _ = nothing

-- Receipt in the restored include body captures the pending map restoration.
-- The post-publication counter read and promise wait have no map to restore.
-- Body receipts below retain their saved-map continuation until restoration.
observeException : WorkerId → Fault → State → Maybe State
observeException w err s with lookup w (workers s) | lookup w (Shared.admissions (shared s))
... | just t | just a with pc t | Shared.pc a
...   | calling | Shared.count _ = just (setPC w t (closePrefix Shared.bodyFailed (raised err)) s)
...   | calling | Shared.prepare _ = just (setPC w t (closePrefix Shared.bodyFailed (raised err)) s)
...   | calling | Shared.selectEntry _ _ = just (setPC w t (closePrefix Shared.bodyFailed (raised err)) s)
...   | calling | Shared.forkHandler _ _ _ = just (setPC w t (closePrefix Shared.bodyFailed (raised err)) s)
...   | calling | Shared.publish _ _ _ = just (setPC w t (closePrefix Shared.bodyFailed (raised err)) s)
...   | calling | Shared.countPublished _ _ = just (setPC w t (closeException err) s)
...   | calling | Shared.awaitHandshake _ _ = just (setPC w t (closeException err) s)
...   | _ | _ = nothing
observeException w err s | _ | _ = nothing
-- Restoration is a distinct masked source transaction after receipt. Only
-- this captured worker fault can invoke the lower restoreBody primitive; the
-- unaccompanied machine alias is refused by machineAllowed.
restoreWorker : WorkerId → State → Maybe State
restoreWorker w s with lookup w (workers s)
... | just t with pc t
...   | closePrefix Shared.bodyFailed (raised fault) with N.step (runMachine (Machine.admissionStep w Admission.restoreBody)) (base s)
...     | just n = just (record s { base = n })
...     | nothing = nothing
restoreWorker w s | just t | _ = nothing
restoreWorker w s | nothing = nothing

nextNormal : Maybe Fault → WorkerPC
nextNormal nothing = bodyExited returned
nextNormal (just err) = closeException err
nextException : Fault → Maybe Fault → WorkerPC
nextException err nothing = bodyExited (raised err)
nextException err (just replacement) = bodyExited (raised replacement)
socketOutcome : Maybe Fault → Shared.SocketOwner
socketOutcome nothing = Shared.closed
socketOutcome (just err) = Shared.closeUncertain (error err)
enactClose : WorkerId → Worker → Maybe Fault → WorkerPC → State → State
enactClose w t outcome next s = record (setWorld (record (shared s)
  { sockets = put (Shared.socketRef (request t)) (socketOutcome outcome) (Shared.sockets (shared s)) }) s)
  { workers = put w (rawWorker (request t) next (suc (closeCalls t))) (workers s) }
-- A normal prefix close invokes the existing source writer once. A failed
-- hard-limit close enters onException and can attempt close again; failure of
-- an exception-cleanup close replaces the original exception without retry.
prefixCloseFailed : Result → Fault → WorkerPC
prefixCloseFailed returned err = closeException err
prefixCloseFailed (raised original) replacement = bodyExited (raised replacement)
sameFailure : Shared.Failure → Shared.Failure → Bool
sameFailure Shared.hardLimitReached Shared.hardLimitReached = true
sameFailure Shared.forbidden Shared.forbidden = true
sameFailure Shared.forkFailed Shared.forkFailed = true
sameFailure Shared.bodyFailed Shared.bodyFailed = true
sameFailure _ _ = false
prefixMatches : WorkerId → Shared.Failure → State → Bool
prefixMatches w f s with lookup w (Shared.admissions (shared s))
... | nothing = false
... | just a with Shared.pc a
...   | Shared.closeSocket actual = sameFailure f actual
...   | _ = false
enactPrefixClose : WorkerId → Worker → Result → Maybe Fault → State → Maybe State
enactPrefixClose w t result nothing s with N.step (runMachine (Machine.admissionStep w Admission.close)) (base s)
... | nothing = nothing
... | just n = just (record s { base = n
  ; workers = put w (rawWorker (request t) (bodyExited result) (suc (closeCalls t))) (workers s) })
enactPrefixClose w t result (just err) s = just (enactClose w t (just err) (prefixCloseFailed result err) s)
closePrefixWorker : WorkerId → Worker → Shared.Failure → Result → Maybe Fault → State → Maybe State
closePrefixWorker w t f result outcome s with prefixMatches w f s
... | false = nothing
... | true = enactPrefixClose w t result outcome s
closeWorker : WorkerId → Maybe Fault → State → Maybe State
closeWorker w outcome s with lookup w (workers s)
... | nothing = nothing
... | just t with pc t
...   | closeDisconnected = just (enactClose w t outcome (nextNormal outcome) s)
...   | closeException err = just (enactClose w t outcome (nextException err outcome) s)
...   | closePrefix f result = closePrefixWorker w t f result outcome s
...   | _ = nothing
publishWorkerResult : WorkerId → State → Maybe State
publishWorkerResult w s with lookup w (workers s)
... | just t with pc t
...   | bodyExited r = just (setPC w t (resultAvailable r) s)
...   | _ = nothing
publishWorkerResult w s | nothing = nothing

-- Scope steps do not inspect or cancel raw admission Asyncs. Normal listener
failedForkSocket : State → Maybe SocketId
failedForkSocket s with stage s
... | acceptForkClosing sock err = just sock
... | _ = nothing

-- close and tracer return are observed operations, not eventuality premises.
data ScopeAction : Set where
  returnAction publishActionResult selectActionWinner requestAcceptCancel
    deliverAcceptAtWait closeListener publishAcceptResult joinAccept traceStopped
    cancelJoinReturnedAction requestIGCancel deliverIGBody deactivateIG flushIG
    finishIGBody publishIGResult joinIG beginCM finishServer : ScopeAction
  -- The IG thread's own failure enters its catch while it is still live.
  failIGBody : ScopeAction
  -- waitEither returns the failed IG thread before the action thread: the race
  -- then cancels the accept loops while the action thread keeps running.
  igWins : ScopeAction
  -- The accept loop raises (Server.hs 207-249): a fatal AcceptFailure, or a
  -- getLocalAddr/trace failure after accept, which first closes the accepted
  -- socket. Its finally then closes the listener and raceAll rethrows.
  acceptFails : ScopeAction
  forkFailure : SocketId → ErrorId → ScopeAction
  finishForkFailure : ScopeAction
  -- Asynchronous cancellation of the thread running Server.with while it waits
  -- in the race (the node's ordinary shutdown). The race cancels the accept
  -- loops before withAsync cancels the still-running action thread.
  interruptServer : ScopeAction
-- Ordinary scope operations retain the original constructor/API. A socket
-- scope records accept-loop ownership without inventing an admission worker.
data ScopePlan : Set where
  scopePlan : Stage → Bool → IGPhase → Maybe N.Action → ScopePlan
  socketScopePlan : Stage → Bool → IGPhase → SocketId → Shared.SocketOwner → ScopePlan
nextStage : ScopePlan → Stage
nextStage (scopePlan st keep ig action) = st
nextStage (socketScopePlan st keep ig sock owner) = st
keepListener : ScopePlan → Bool
keepListener (scopePlan st keep ig action) = keep
keepListener (socketScopePlan st keep ig sock owner) = keep
nextIG : ScopePlan → IGPhase
nextIG (scopePlan st keep ig action) = ig
nextIG (socketScopePlan st keep ig sock owner) = ig
physicalAction : ScopePlan → Maybe N.Action
physicalAction (scopePlan st keep ig action) = action
physicalAction (socketScopePlan st keep ig sock owner) = nothing
chooseScope : ScopeAction → State → Maybe ScopePlan
-- The supplied failure is a synchronous async-acquisition exception, not an
-- async receipt at the nonblocking masked parent fork. No raw child is born.
chooseScope (forkFailure sock err) s with accepting (stage s) | listenerOpen s | lookup sock (Shared.sockets (shared s))
... | true | true | nothing = just (socketScopePlan (acceptForkClosing sock err) (listenerOpen s) (ig s) sock Shared.acceptPending)
... | _ | _ | _ = nothing
chooseScope finishForkFailure s with failedForkSocket s
... | just sock with lookup sock (Shared.sockets (shared s))
...   | just Shared.closed = just (scopePlan acceptFailed (listenerOpen s) (ig s) nothing)
...   | just (Shared.closeUncertain replacement) = just (scopePlan acceptFailed (listenerOpen s) (ig s) nothing)
...   | _ = nothing
chooseScope finishForkFailure s | nothing = nothing
chooseScope returnAction s with stage s
... | serving = just (scopePlan actionBodyExited (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope publishActionResult s with stage s
... | actionBodyExited = just (scopePlan actionResultAvailable (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope interruptServer s with stage s
... | serving = just (scopePlan closingAccept (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope selectActionWinner s with stage s
... | actionResultAvailable = just (scopePlan closingAccept (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope requestAcceptCancel s with stage s
... | closingAccept = just (scopePlan acceptCancelRequested (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope deliverAcceptAtWait s with stage s
... | acceptCancelRequested = just (scopePlan acceptCancelDelivered (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope closeListener s with stage s
... | acceptCancelDelivered = just (scopePlan acceptBodyExited false (ig s) nothing)
... | acceptFailed = just (scopePlan acceptBodyExited false (ig s) nothing)
... | _ = nothing
chooseScope publishAcceptResult s with stage s
... | acceptBodyExited = just (scopePlan acceptResultAvailable (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope joinAccept s with stage s
... | acceptResultAvailable = just (scopePlan acceptJoined (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope traceStopped s with stage s
... | acceptJoined = just (scopePlan serverStopped (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope cancelJoinReturnedAction s with stage s
... | serverStopped = just (scopePlan actionJoined (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope requestIGCancel s with stage s
... | actionJoined = just (scopePlan igCancelRequested (listenerOpen s) (ig s) nothing)
... | _ = nothing
-- Pending IG CM calls require their own cancellation/unwind adapter. This
-- first exit profile cannot discard such a continuation before deactivation.
-- The IG thread receives the Server's cancellation only after it is requested.
chooseScope deliverIGBody s with stage s | ig s | Machine.inboundRelease (O.core (source s)) | Machine.remoteCall (O.core (source s))
... | igCancelRequested | igLive | nothing | nothing = just (scopePlan (stage s) (listenerOpen s) igCaught nothing)
... | _ | _ | _ | _ = nothing
-- The IG thread's own failure can occur at any Server stage while it is live.
chooseScope failIGBody s with ig s | Machine.inboundRelease (O.core (source s)) | Machine.remoteCall (O.core (source s))
... | igLive | nothing | nothing = just (scopePlan (stage s) (listenerOpen s) igCaught nothing)
... | _ | _ | _ = nothing
chooseScope deactivateIG s with ig s
... | igCaught = just (scopePlan (stage s) (listenerOpen s) igInactive (just (runMachine (Machine.igStep IG.deactivateIG))))
... | _ = nothing
chooseScope flushIG s with ig s
... | igInactive = just (scopePlan (stage s) (listenerOpen s) igFlushed (just (runMachine (Machine.igStep IG.flushOnExit))))
... | _ = nothing
chooseScope finishIGBody s with ig s | IG.connections (IG.publishedState (Machine.inboundGovernor (O.core (source s)))) |
  IG.continuation (Machine.inboundGovernor (O.core (source s))) | IG.active (IG.execution (Machine.inboundGovernor (O.core (source s))))
... | igFlushed | [] | IG.exited | false = just (scopePlan (stage s) (listenerOpen s) igBodyExited nothing)
... | _ | _ | _ | _ = nothing
chooseScope publishIGResult s with ig s
... | igBodyExited = just (scopePlan (stage s) (listenerOpen s) igResultAvailable nothing)
... | _ = nothing
-- withAsync's cancellation of a finished IG thread is a no-op; the join waits
-- for its result.
chooseScope joinIG s with stage s | ig s
... | igCancelRequested | igResultAvailable = just (scopePlan igJoined (listenerOpen s) igResultAvailable nothing)
... | _ | _ = nothing
-- The failed IG thread wins waitEither before the action thread's result is
-- selected; the race then closes the accept loops.
-- The accept loop can fail until the race's cancellation reaches it.
chooseScope acceptFails s with stage s
... | serving = just (scopePlan acceptFailed (listenerOpen s) (ig s) nothing)
... | actionBodyExited = just (scopePlan acceptFailed (listenerOpen s) (ig s) nothing)
... | actionResultAvailable = just (scopePlan acceptFailed (listenerOpen s) (ig s) nothing)
... | closingAccept = just (scopePlan acceptFailed (listenerOpen s) (ig s) nothing)
... | acceptCancelRequested = just (scopePlan acceptFailed (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope igWins s with stage s | ig s
... | serving | igResultAvailable = just (scopePlan closingAccept (listenerOpen s) igResultAvailable nothing)
... | actionBodyExited | igResultAvailable = just (scopePlan closingAccept (listenerOpen s) igResultAvailable nothing)
... | actionResultAvailable | igResultAvailable = just (scopePlan closingAccept (listenerOpen s) igResultAvailable nothing)
... | _ | _ = nothing
chooseScope beginCM s with stage s
... | igJoined = just (scopePlan closingCM (listenerOpen s) (ig s) nothing)
... | _ = nothing
chooseScope finishServer s with stage s | Close.phase (W.shutdown (R.base (N.raw (base s))))
... | closingCM | Close.closed = just (scopePlan serverReturned (listenerOpen s) (ig s) nothing)
... | _ | _ = nothing

-- Every scope plan preserves the raw-worker table, even when IG cleanup
-- performs an actual shared-source operation. No cancellation/join is implied.
enactScope : ScopePlan → State → Maybe State
enactScope (scopePlan st keep ig action) s with action
... | nothing = just (record s { stage = st; listenerOpen = keep; ig = ig })
... | just a with N.step a (base s)
...   | nothing = nothing
...   | just n = just (record s { base = n; stage = st; listenerOpen = keep; ig = ig })
enactScope (socketScopePlan st keep ig sock owner) s = just (record
  (setWorld (record (shared s) { sockets = put sock owner (Shared.sockets (shared s)) }) s)
  { stage = st; listenerOpen = keep; ig = ig })
scopeAdvance : ScopeAction → State → Maybe State
scopeAdvance a s with chooseScope a s
... | nothing = nothing
... | just p = enactScope p s

-- A close completion is a separate observed IO outcome. While it is pending,
-- this accept loop cannot fork again or publish its own result. Close failure
-- records the replacement exception; neither outcome fabricates a worker.
isAcceptedSocket : SocketId → State → Bool
isAcceptedSocket sock s with lookup sock (Shared.sockets (shared s))
... | just Shared.acceptPending = true
... | _ = false
closeFailedFork : Maybe Fault → State → Maybe State
closeFailedFork outcome s with failedForkSocket s
... | just sock with isAcceptedSocket sock s
...   | true = just (setWorld (record (shared s)
  { sockets = put sock (socketOutcome outcome) (Shared.sockets (shared s)) }) s)
...   | false = nothing
closeFailedFork outcome s | nothing = nothing

data Action : Set where
  closeForkFailure : Maybe Fault → Action
  acceptedFork : WorkerId → Shared.Admission → Action
  run : N.Action → Action
  workerReturned workerPrefixReturned workerRestore : WorkerId → Action
  workerPrefixException : WorkerId → ErrorId → Action
  workerException : WorkerId → Fault → Action
  workerClose : WorkerId → Maybe Fault → Action
  workerResult : WorkerId → Action
  scope : ScopeAction → Action
step : Action → State → Maybe State
step (closeForkFailure outcome) s = closeFailedFork outcome s
step (acceptedFork w req) s = forkAccepted w req s
step (run a) s = inherit a s
step (workerRestore w) s = restoreWorker w s
step (workerReturned w) s = observeReturn w s
step (workerPrefixReturned w) s = prefixReturned w s
step (workerPrefixException w e) s = prefixException w e s
step (workerException w e) s = observeException w e s
step (workerClose w result) s = closeWorker w result s
step (workerResult w) s = publishWorkerResult w s
step (scope a) s = scopeAdvance a s

data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s t u a as} → step a s ≡ just t → Executes t as u → Executes s (a ∷ as) u

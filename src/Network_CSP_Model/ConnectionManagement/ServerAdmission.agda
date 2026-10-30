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

-- The normal action-return branch of the single-listener async/race tree.
-- Listener close, IG's actual shared cleanup and CM's result wait are distinct.
data Stage : Set where
  serving actionBodyExited actionResultAvailable closingAccept acceptCancelRequested
    acceptCancelDelivered acceptBodyExited acceptResultAvailable acceptJoined
    serverStopped actionJoined igCancelRequested igCancelDelivered igInactive
    igFlushed igBodyExited igResultAvailable igJoined closingCM serverReturned : Stage
record State : Set where
  constructor serverState
  field base : N.State
        workers : Store WorkerId Worker
        stage : Stage
        listenerOpen : Bool
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
... | [] | [] | just n = just (serverState n [] serving true)
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
outboundCaller : N.Action → Maybe WorkerId
outboundCaller (N.run (C.run (D.run (R.run (X.run (W.run (G.run (M.run (P.run (U.run (B.outbound a))))))))))) = caller a
  where
  caller : O.Action → Maybe WorkerId
  caller (O.beginAcquire w _) = just w
  caller (O.acquire w _) = just w
  caller (O.beginRelease w _) = just w
  caller (O.release w _) = just w
  caller (O.inbound _) = nothing
outboundCaller _ = nothing

-- Raw admission workers have one role and historical identities. An unrelated
-- outbound caller cannot reuse that identity after the admission body exits.
foreignCallerAllowed : N.Action → State → Bool
foreignCallerAllowed a s with outboundCaller a
... | nothing = true
... | just w with lookup w (workers s)
...   | nothing = true
...   | just _ = false
cmAction : N.Action → Bool
cmAction (N.run (C.run (D.run (R.run (X.run (W.shutdownStep _)))))) = true
cmAction (N.deliverShutdown _ _) = true
cmAction _ = false
inCMClose : Stage → Bool
inCMClose closingCM = true
inCMClose _ = false
igRunning : Stage → Bool
igRunning igCancelDelivered = false
igRunning igInactive = false
igRunning igFlushed = false
igRunning igBodyExited = false
igRunning igResultAvailable = false
igRunning igJoined = false
igRunning closingCM = false
igRunning serverReturned = false
igRunning _ = true
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
machineAllowed (Machine.admissionStep w _) s = running w s
machineAllowed (Machine.handshakeStep w _) s = running w s
machineAllowed (Machine.igStep IG.deactivateIG) s = false
machineAllowed (Machine.igStep IG.flushOnExit) s = false
machineAllowed (Machine.igStep a) s with igBodyAction a
... | true = igRunning (stage s)
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

-- This direct exception observation covers the post-handoff promise wait.
-- Other async regions still need their own bracket/restore extension.
observeException : WorkerId → Fault → State → Maybe State
observeException w err s with lookup w (workers s) | lookup w (Shared.admissions (shared s))
... | just t | just a with pc t | Shared.pc a
...   | calling | Shared.awaitHandshake _ _ = just (setPC w t (closeException err) s)
...   | _ | _ = nothing
observeException w err s | _ | _ = nothing
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
-- close and tracer return are observed operations, not eventuality premises.
data ScopeAction : Set where
  returnAction publishActionResult selectActionWinner requestAcceptCancel
    deliverAcceptAtWait closeListener publishAcceptResult joinAccept traceStopped
    cancelJoinReturnedAction requestIGCancel deliverIGBody deactivateIG flushIG
    finishIGBody publishIGResult joinIG beginCM finishServer : ScopeAction
record ScopePlan : Set where
  constructor scopePlan
  field nextStage : Stage
        keepListener : Bool
        physicalAction : Maybe N.Action
open ScopePlan public
chooseScope : ScopeAction → State → Maybe ScopePlan
chooseScope returnAction s with stage s
... | serving = just (scopePlan actionBodyExited (listenerOpen s) nothing)
... | _ = nothing
chooseScope publishActionResult s with stage s
... | actionBodyExited = just (scopePlan actionResultAvailable (listenerOpen s) nothing)
... | _ = nothing
chooseScope selectActionWinner s with stage s
... | actionResultAvailable = just (scopePlan closingAccept (listenerOpen s) nothing)
... | _ = nothing
chooseScope requestAcceptCancel s with stage s
... | closingAccept = just (scopePlan acceptCancelRequested (listenerOpen s) nothing)
... | _ = nothing
chooseScope deliverAcceptAtWait s with stage s
... | acceptCancelRequested = just (scopePlan acceptCancelDelivered (listenerOpen s) nothing)
... | _ = nothing
chooseScope closeListener s with stage s
... | acceptCancelDelivered = just (scopePlan acceptBodyExited false nothing)
... | _ = nothing
chooseScope publishAcceptResult s with stage s
... | acceptBodyExited = just (scopePlan acceptResultAvailable (listenerOpen s) nothing)
... | _ = nothing
chooseScope joinAccept s with stage s
... | acceptResultAvailable = just (scopePlan acceptJoined (listenerOpen s) nothing)
... | _ = nothing
chooseScope traceStopped s with stage s
... | acceptJoined = just (scopePlan serverStopped (listenerOpen s) nothing)
... | _ = nothing
chooseScope cancelJoinReturnedAction s with stage s
... | serverStopped = just (scopePlan actionJoined (listenerOpen s) nothing)
... | _ = nothing
chooseScope requestIGCancel s with stage s
... | actionJoined = just (scopePlan igCancelRequested (listenerOpen s) nothing)
... | _ = nothing
-- Pending IG CM calls require their own cancellation/unwind adapter. This
-- first exit profile cannot discard such a continuation before deactivation.
chooseScope deliverIGBody s with stage s | Machine.inboundRelease (O.core (source s)) | Machine.remoteCall (O.core (source s))
... | igCancelRequested | nothing | nothing = just (scopePlan igCancelDelivered (listenerOpen s) nothing)
... | _ | _ | _ = nothing
chooseScope deactivateIG s with stage s
... | igCancelDelivered = just (scopePlan igInactive (listenerOpen s) (just (runMachine (Machine.igStep IG.deactivateIG))))
... | _ = nothing
chooseScope flushIG s with stage s
... | igInactive = just (scopePlan igFlushed (listenerOpen s) (just (runMachine (Machine.igStep IG.flushOnExit))))
... | _ = nothing
chooseScope finishIGBody s with stage s | IG.connections (IG.publishedState (Machine.inboundGovernor (O.core (source s)))) |
  IG.continuation (Machine.inboundGovernor (O.core (source s))) | IG.active (IG.execution (Machine.inboundGovernor (O.core (source s))))
... | igFlushed | [] | IG.exited | false = just (scopePlan igBodyExited (listenerOpen s) nothing)
... | _ | _ | _ | _ = nothing
chooseScope publishIGResult s with stage s
... | igBodyExited = just (scopePlan igResultAvailable (listenerOpen s) nothing)
... | _ = nothing
chooseScope joinIG s with stage s
... | igResultAvailable = just (scopePlan igJoined (listenerOpen s) nothing)
... | _ = nothing
chooseScope beginCM s with stage s
... | igJoined = just (scopePlan closingCM (listenerOpen s) nothing)
... | _ = nothing
chooseScope finishServer s with stage s | Close.phase (W.shutdown (R.base (N.raw (base s))))
... | closingCM | Close.closed = just (scopePlan serverReturned (listenerOpen s) nothing)
... | _ | _ = nothing

-- Every scope plan preserves the raw-worker table, even when IG cleanup
-- performs an actual shared-source operation. No cancellation/join is implied.
enactScope : ScopePlan → State → Maybe State
enactScope p s with physicalAction p
... | nothing = just (record s { stage = nextStage p; listenerOpen = keepListener p })
... | just a with N.step a (base s)
...   | nothing = nothing
...   | just n = just (record s { base = n; stage = nextStage p; listenerOpen = keepListener p })
scopeAdvance : ScopeAction → State → Maybe State
scopeAdvance a s with chooseScope a s
... | nothing = nothing
... | just p = enactScope p s

data Action : Set where
  acceptedFork : WorkerId → Shared.Admission → Action
  run : N.Action → Action
  workerReturned workerPrefixReturned : WorkerId → Action
  workerPrefixException : WorkerId → ErrorId → Action
  workerException : WorkerId → Fault → Action
  workerClose : WorkerId → Maybe Fault → Action
  workerResult : WorkerId → Action
  scope : ScopeAction → Action
step : Action → State → Maybe State
step (acceptedFork w req) s = forkAccepted w req s
step (run a) s = inherit a s
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

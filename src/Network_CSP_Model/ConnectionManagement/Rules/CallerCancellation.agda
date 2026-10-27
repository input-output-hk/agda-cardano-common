{-# OPTIONS --guardedness #-}

-- Async cancellation of a caller, distinct from an ordinary CM error return.
-- Core.hs:1273-1832,1834-2060 at the network pin: bracket ownership determines
-- whether the caller closes/removes its reservation or leaves a handler alive.
module ConnectionManagement.Rules.CallerCancellation where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; delete)
import ConnectionManagement.Machine as Inbound
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.OutboundCases as Cases

-- Region provenance is supplied by the executing adapter, not reconstructed
-- from an exception identifier. In particular count PCs have multiple origins.
-- interruptibleOpen acknowledges blocking interruptibility of masked bracket
-- acquisition; ordinary cancellation cannot invent that delivery window.
data Context : Set where
  ordinary forkedBeforeHandoff protectedCleanup interruptibleOpen : Context

-- Retain the exact detached continuation, including a release's unsent targets.
-- Detachment acknowledges no handler delivery, termination or CM return.
data Call : Set where
  noCaller : Call
  acquiring : A.Frame → Call
  releasing : R.Frame → Call

data Finish : Set where
  abandoned cleanupComplete : Finish
  socketCloseFailed : ErrorId → Finish

data PC : Set where
  cleaning : A.Frame → PC
  finished : Finish → PC

record Frame : Set where
  constructor cancellation
  field
    caller : WorkerId
    cancelError : ErrorId
    original : Call
    pc : PC
open Frame public

-- A plan captures the original reservation identity without looking up a new
-- connection by peer address. Allocation before resource acquisition has no
-- bracket cleanup; an already forked handler owns post-handoff cleanup.
data Plan : Set where
  abandon : Plan
  closeCaptured : EntryId → Plan

ordinaryPlan : A.PC → Maybe Plan
ordinaryPlan A.selecting = just abandon
ordinaryPlan (A.count next) = ordinaryPlan next
ordinaryPlan (A.allocatePromise _) = just abandon
ordinaryPlan (A.openSocket _ _) = nothing
ordinaryPlan (A.configureSocket e _) = just (closeCaptured e)
ordinaryPlan (A.bindSocket e _) = just (closeCaptured e)
ordinaryPlan (A.connectSocket e _) = just (closeCaptured e)
ordinaryPlan (A.localAddress e _) = just (closeCaptured e)
ordinaryPlan (A.updateAddress e _ _) = just (closeCaptured e)
ordinaryPlan (A.forkHandler e _ _) = just (closeCaptured e)
ordinaryPlan (A.connectedCommit _ _ _) = just abandon
ordinaryPlan (A.awaitResult _ _ _) = just abandon
ordinaryPlan (A.commitResult _ _ _) = just abandon
ordinaryPlan (A.waitingInbound _ _) = just abandon
ordinaryPlan (A.closeError _ _) = nothing
ordinaryPlan (A.removeError _ _) = nothing
ordinaryPlan (A.complete _) = just abandon

plan : Context → A.PC → Maybe Plan
plan ordinary p = ordinaryPlan p
plan forkedBeforeHandoff (A.connectedCommit e _ _) = just (closeCaptured e)
plan interruptibleOpen (A.openSocket _ _) = just abandon
plan _ _ = nothing

begin : ErrorId → Plan → A.Frame → PC
begin err abandon f = finished abandoned
begin err (closeCaptured e) f = cleaning (record f { pc = A.closeError e (Cases.ioFailure err) })

-- Start changes only caller bookkeeping; the captured socket/map cleanup is
-- performed later by the actual acquisition writer. No result is synthesized.
start : WorkerId → ErrorId → Context → CM.Configuration → Maybe (Frame × CM.Configuration)
start w err protectedCleanup c = nothing
start w err context c with lookup w (CM.acquiring c) | lookup w (CM.releasing c)
... | just f | nothing with plan context (A.pc f)
...   | nothing = nothing
...   | just chosen = just (cancellation w err (acquiring f) (begin err chosen f) ,
  record c { acquiring = delete w (CM.acquiring c) })
start w err ordinary c | nothing | just f = just
  (cancellation w err (releasing f) (finished abandoned) ,
   record c { releasing = delete w (CM.releasing c) })
start w err ordinary c | nothing | nothing = just
  (cancellation w err noCaller (finished abandoned) , c)
start w err context c | _ | _ = nothing

-- Cleanup is uninterruptible in this source bracket. Its close exception may
-- replace the propagated exception and must skip map removal, exactly as A.step.
data Action : Set where
  closeSocket removeReservation readCounters : Action
  closeFailed : ErrorId → Action

acquireAction : Action → A.Action
acquireAction closeSocket = A.closeOK
acquireAction (closeFailed err) = A.closeFailed err
acquireAction removeReservation = A.removeReservation
acquireAction readCounters = A.readCounters

after : Action → A.Frame → PC
after (closeFailed err) f = finished (socketCloseFailed err)
after a f with A.pc f
... | A.complete _ = finished cleanupComplete
... | _ = cleaning f

-- Expose the exact source writer for invariant/effect reuse. The original
-- detached frame stays available even while this cleanup continuation advances.
step : Action → Frame → CM.Configuration → Maybe (Frame × CM.Configuration)
step a f c with pc f
... | finished _ = nothing
... | cleaning active with A.step (caller f) (Inbound.responder (CM.core c))
    (acquireAction a) active (Inbound.world (CM.core c))
...   | nothing = nothing
...   | just (active′ , shared′) = just (record f { pc = after a active′ } ,
  record c { core = Inbound.replaceWorld (CM.core c) shared′ })

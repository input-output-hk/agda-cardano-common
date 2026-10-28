{-# OPTIONS --guardedness #-}

-- Opt-in post-handshake handler exit paths. Source: Mux.hs:254-278,
-- JobPool.hs:70-110, ConnectionHandler.hs:286-309,452, Core.hs:584-592 at
-- 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d. Pool joins and buffer unwind
-- completion and synchronous rethrow-policy selection remain explicit inputs.
module ConnectionManagement.Rules.HandlerLifecycle where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State hiding (capturedMux)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as M
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote

data Phase : Set where
  monitoring poolClosing poolClosed deadTracing bodyExited finalizing : Phase
  normalClosing normalClosed normalBodyExited : Phase
  syncClosing syncClosed classifying peerRethrow nodeDelivery nodeRethrow
    peerBodyExited nodeBodyExited : ErrorId → Phase

-- Abstract result of runRethrowPolicy in the captured handler's error context.
data Policy : Set where
  shutdownPeer shutdownNode : Policy
record Frame : Set where
  constructor frame
  field capturedMux : MuxId
        cancellationError : ErrorId
        phase : Phase
open Frame public
Runtime = Store WorkerId Frame

-- The error identity stands for this profile's AsyncCancelled exception value.
data Action : Set where
  attach : ErrorId → Action
  jobPoolClosed publishAsyncFailure finishRethrow : Action
  monitorReturned monitorThrew finishBuffer nodeExceptionDelivered rethrow : Action
  choosePolicy : Policy → Action
  tracerThrew : ErrorId → Action

hasMux : MuxId → Runtime → Bool
hasMux mid [] = false
hasMux mid ((_ , f) ∷ rest) with mid ≟ capturedMux f
... | yes _ = true
... | no _ = hasMux mid rest

setPhase : WorkerId → Frame → Phase → Runtime → Runtime
setPhase w f p = put w (record f { phase = p })

-- Attach by the registered handler's promise, never by the current CM entry.
attachMux : WorkerId → ErrorId → Runtime → IG.Runtime → State → Maybe (Runtime × IG.Runtime)
attachMux w err rt ig s with lookup w rt | lookup w (handlers s) | lookup w (cleanups s)
... | nothing | just h | nothing with lookup (handlerPromise h) (handshakeResults s)
...   | just (negotiated hid _) with lookup hid (IG.handles (IG.execution ig))
...     | just hd with lookup (M.muxRef hd) (IG.muxes (IG.execution ig)) | hasMux (M.muxRef hd) rt
...       | just m | false with M.status m | M.callback m
...         | M.ready | M.returned = just (put w (frame (M.muxRef hd) err monitoring) rt , ig)
...         | _ | _ = nothing
attachMux w err rt ig s | nothing | just h | nothing | just (negotiated hid _) | just hd | _ | _ = nothing
attachMux w err rt ig s | nothing | just h | nothing | just (negotiated hid _) | nothing = nothing
attachMux w err rt ig s | nothing | just h | nothing | _ = nothing
attachMux _ _ _ _ _ | _ | _ | _ = nothing

step : WorkerId → Action → Runtime → IG.Runtime → State → Maybe (Runtime × IG.Runtime)
step w (attach err) rt ig s = attachMux w err rt ig s
step w jobPoolClosed rt ig s with lookup w rt
... | nothing = nothing
... | just f with phase f | lookup (capturedMux f) (IG.muxes (IG.execution ig))
...   | poolClosing | just m = just (setPhase w f poolClosed rt ,
      IG.setMux (capturedMux f) (record m { runningJobs = []; waiting = [] }) ig)
...   | normalClosing | just m = just (setPhase w f normalClosed rt ,
      IG.setMux (capturedMux f) (record m { runningJobs = []; waiting = [] }) ig)
...   | syncClosing err | just m = just (setPhase w f (syncClosed err) rt ,
      IG.setMux (capturedMux f) (record m { runningJobs = []; waiting = [] }) ig)
...   | _ | _ = nothing
step w publishAsyncFailure rt ig s with lookup w rt
... | nothing = nothing
... | just f with phase f | lookup (capturedMux f) (IG.muxes (IG.execution ig))
...   | poolClosed | just m = just (setPhase w f deadTracing rt ,
      IG.setMux (capturedMux f) (record m { status = M.failed (cancellationError f)
                                ; callback = IG.traceCallback m M.muxStopped }) ig)
...   | _ | _ = nothing
step w finishRethrow rt ig s with lookup w rt
... | nothing = nothing
... | just f with phase f | lookup (capturedMux f) (IG.muxes (IG.execution ig))
...   | deadTracing | just m with M.callback m
...     | M.returned = just (setPhase w f bodyExited rt , ig)
...     | _ = nothing
step w finishRethrow rt ig s | just f | _ | _ = nothing


-- Monitor outcomes are derived only after the synchronous tracer returns.
-- Unlike async catch, these paths publish terminal mux status BEFORE pool close.
step w monitorReturned rt ig s with lookup w rt
... | nothing = nothing
... | just f with phase f | lookup (capturedMux f) (IG.muxes (IG.execution ig))
...   | monitoring | just m with M.status m | M.callback m
...     | M.stopped | M.returned = just (setPhase w f normalClosing rt , ig)
...     | _ | _ = nothing
step w monitorReturned rt ig s | just f | _ | _ = nothing
step w monitorThrew rt ig s with lookup w rt
... | nothing = nothing
... | just f with phase f | lookup (capturedMux f) (IG.muxes (IG.execution ig))
...   | monitoring | just m with M.status m | M.callback m
...     | M.failed err | M.returned = just (setPhase w f (syncClosing err) rt , ig)
...     | _ | _ = nothing
step w monitorThrew rt ig s | just f | _ | _ = nothing
-- The existing partial-descriptor lookup records a thrown tracer exception.
-- A synchronous callback failure bypasses mux's ASYNC-only catch: no extra
-- Failed write or Dead callback is invented. The exception identity is an input.
step w (tracerThrew err) rt ig s with lookup w rt
... | nothing = nothing
... | just f with phase f | lookup (capturedMux f) (IG.muxes (IG.execution ig))
...   | monitoring | just m with M.callback m
...     | M.tracerFailed _ = just (setPhase w f (syncClosing err) rt , ig)
...     | _ = nothing
step w (tracerThrew err) rt ig s | just f | _ | _ = nothing
-- Successful buffer teardown precedes the outer exception classifier.
step w finishBuffer rt ig s with lookup w rt
... | nothing = nothing
... | just f with phase f
...   | normalClosed = just (setPhase w f normalBodyExited rt , ig)
...   | syncClosed err = just (setPhase w f (classifying err) rt , ig)
...   | _ = nothing
step w (choosePolicy policy) rt ig s with lookup w rt
... | nothing = nothing
... | just f with phase f | policy
...   | classifying err | shutdownPeer = just (setPhase w f (peerRethrow err) rt , ig)
...   | classifying err | shutdownNode = just (setPhase w f (nodeDelivery err) rt , ig)
...   | _ | _ = nothing
-- ShutdownNode's throwTo may block; delivery is neither node exit nor a join.
step w nodeExceptionDelivered rt ig s with lookup w rt
... | nothing = nothing
... | just f with phase f
...   | nodeDelivery err = just (setPhase w f (nodeRethrow err) rt , ig)
...   | _ = nothing
-- Peer rethrow wraps the error in ExceptionInHandler; node rethrow uses the
-- original error after delivering that wrapper to the main thread.
step w rethrow rt ig s with lookup w rt
... | nothing = nothing
... | just f with phase f
...   | peerRethrow err = just (setPhase w f (peerBodyExited err) rt , ig)
...   | nodeRethrow err = just (setPhase w f (nodeBodyExited err) rt , ig)
...   | _ = nothing

-- Delivery acknowledges the sender and records entry into async unwinding;
-- it does not publish Failed or start CM cleanup in that same event.
noteDelivery : WorkerId → Runtime → Runtime
noteDelivery w rt with lookup w rt
... | nothing = rt
... | just f with phase f
...   | monitoring = setPhase w f poolClosing rt
...   | _ = rt

-- This first tracked profile accepts delivery while monitoring, or after the
-- finalizer has completed. Other async/masking windows remain outside it.
mayDeliver : WorkerId → Runtime → State → Bool
mayDeliver w rt s with lookup w rt
... | nothing = true
... | just f with phase f
...   | monitoring = true
...   | finalizing with lookup w (cleanups s)
...     | just (cleanupDone _) = true
...     | _ = false
mayDeliver w rt s | just f | _ = false

allowRelease : Release.Action → Runtime → State → Bool
allowRelease (Release.cancellationDelivered w) = mayDeliver w
allowRelease _ = λ _ _ → true
noteRelease : Release.Action → Runtime → Runtime
noteRelease (Release.cancellationDelivered w) = noteDelivery w
noteRelease _ = λ rt → rt
allowRemote : Remote.Action → Runtime → State → Bool
allowRemote (Remote.pruneCancellationDelivered w) = mayDeliver w
allowRemote _ = λ _ _ → true
noteRemote : Remote.Action → Runtime → Runtime
noteRemote (Remote.pruneCancellationDelivered w) = noteDelivery w
noteRemote _ = λ rt → rt

mayExit : WorkerId → Runtime → Bool
mayExit w rt with lookup w rt
... | nothing = true -- legacy abstract handler-body boundary
... | just f with phase f
...   | bodyExited = true
...   | normalBodyExited = true
...   | peerBodyExited _ = true
...   | nodeBodyExited _ = true
...   | _ = false
noteExit : WorkerId → Runtime → Runtime
noteExit w rt with lookup w rt
... | nothing = rt
... | just f = setPhase w f finalizing rt

-- Once cancellation is received the old monitor continuation cannot run.
-- Job outcomes may still occur until the pool-close input; callbacks of the
-- async handler itself run only in deadTracing. IG decisions remain independent.
data Access : Set where
  monitorAccess tracerAccess jobAccess : Access
muxAction : IG.IGAction → Maybe (MuxId × Access)
muxAction (IG.monitorCommand mid) = just (mid , monitorAccess)
muxAction (IG.monitorCompletion mid) = just (mid , monitorAccess)
muxAction (IG.sampleTracer mid) = just (mid , tracerAccess)
muxAction (IG.commitTracer mid) = just (mid , tracerAccess)
muxAction (IG.finishStart mid) = just (mid , monitorAccess)
muxAction (IG.forkResponder mid) = just (mid , monitorAccess)
muxAction (IG.startOnDemand mid _) = just (mid , monitorAccess)
muxAction (IG.finishStop mid) = just (mid , monitorAccess)
muxAction (IG.finishProtocol mid _ _) = just (mid , jobAccess)
muxAction (IG.publishJobResult mid _) = just (mid , jobAccess)
muxAction (IG.publishJobOccurrence mid _) = just (mid , jobAccess)
muxAction (IG.recordMuxFailure mid _) = just (mid , monitorAccess)
muxAction (IG.recordMuxStopped mid) = just (mid , monitorAccess)
muxAction (IG.traceMuxDead mid) = just (mid , monitorAccess)
muxAction (IG.takeShutdownCommand mid) = just (mid , monitorAccess)
muxAction (IG.recordMuxStopping mid) = just (mid , monitorAccess)
muxAction (IG.completeMuxStopping mid) = just (mid , monitorAccess)
muxAction (IG.discardJobOccurrence mid _) = just (mid , jobAccess)
muxAction (IG.recordAsyncMuxFailure mid _) = just (mid , monitorAccess)
muxAction _ = nothing

phaseAllows : Phase → Access → Bool
phaseAllows monitoring _ = true
phaseAllows poolClosing jobAccess = true
phaseAllows normalClosing jobAccess = true
phaseAllows (syncClosing _) jobAccess = true
phaseAllows deadTracing tracerAccess = true
phaseAllows _ _ = false

muxAllowed : MuxId → Access → Runtime → Bool
muxAllowed mid access [] = true
muxAllowed mid access ((_ , f) ∷ rest) with mid ≟ capturedMux f
... | yes _ = phaseAllows (phase f) access
... | no _ = muxAllowed mid access rest
allowIG : IG.IGAction → Runtime → Bool
allowIG a rt with muxAction a
... | nothing = true
... | just (mid , access) = muxAllowed mid access rt

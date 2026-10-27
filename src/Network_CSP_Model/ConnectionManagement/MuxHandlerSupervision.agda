{-# OPTIONS --guardedness #-}

-- Successful-handshake startup prefix over actual physical handler births.
-- Existing pre-handshake phases remain untouched; a captured success frame
-- protects that handler until a future protocol/unwind adapter extends it.
module ConnectionManagement.MuxHandlerSupervision (Result : Set) where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Nullary using (does; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes using (Protocol)
open import ConnectionManagement.Store using (Store; lookup; put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.MuxStartup as StartupRules
module Startup = StartupRules Result

-- The immutable birth origin chooses inbound vs mode/flow-sensitive outbound
-- tracer attachment. A current CM entry can legitimately belong to a successor.
data Progress : Set where
  returnedSuccess : Progress
  handleAllocated promisePublished : HandleId → MuxId → Progress
record Frame : Set where
  constructor frame
  field captured : Shared.HandlerStart
        birthProvenance : Provenance
        bundle : List Protocol
        flow : DataFlow
        progress : Progress
        startup : Startup.State
open Frame public
record State : Set where
  constructor supervised
  field base : B.State
        origins : Store WorkerId Provenance
        frames : Store WorkerId Frame
open State public

source : State → O.Configuration
source s = B.source (base s)
setSource : O.Configuration → State → State
setSource c s = record s { base = record (base s) { source = c } }
setFrame : WorkerId → Frame → State → State
setFrame w f s = record s { frames = put w f (frames s) }
startupAt : WorkerId → State → Startup.State
startupAt w s with lookup w (frames s)
... | nothing = Startup.initial
... | just f = startup f

-- Neither physical handlers nor prior handles/muxes are adopted at startup.
initial : O.Configuration → Maybe State
initial c with IG.handles (IG.execution (M.inboundGovernor (O.core c))) |
  IG.muxes (IG.execution (M.inboundGovernor (O.core c))) | B.initial c
... | [] | [] | just b = just (supervised b [] [])
... | _ | _ | _ = nothing

-- A birth record is read from the parent request BEFORE the actual base fork.
-- Only a successful base transition commits this record, and no old origin is
-- overwritten. The worker identity remains historical even after map removal.
birth : B.Action → B.State → Maybe (WorkerId × Provenance)
birth (B.handler (H.run (M.admissionStep w Server.fork))) b with
  lookup w (Shared.admissions (M.world (O.core (B.source b))))
... | nothing = nothing
... | just a = just (Shared.child (Shared.request a) , inbound)
birth (B.outbound (O.acquire w A.forkOK)) b with lookup w (O.acquiring (B.source b))
... | nothing = nothing
... | just f = just (A.child (A.req f) , outbound)
birth _ b = nothing
birthFresh : Maybe (WorkerId × Provenance) → Store WorkerId Provenance → Bool
birthFresh nothing history = true
birthFresh (just (w , origin)) history with lookup w history
... | nothing = true
... | just _ = false
noteBirth : Maybe (WorkerId × Provenance) → State → State
noteBirth nothing s = s
noteBirth (just (w , origin)) s = record s { origins = put w origin (origins s) }

unframed : WorkerId → State → Bool
unframed w s with lookup w (frames s)
... | nothing = true
... | just _ = false
shutdownTargetAllowed : State → Bool
shutdownTargetAllowed s with Close.phase (B.shutdown (base s))
... | Close.awaitDelivery e w = unframed w s
... | _ = true
frameMux : Frame → Maybe MuxId
frameMux f with progress f
... | returnedSuccess = nothing
... | handleAllocated hid mid = just mid
... | promisePublished hid mid = just mid
hasMux : MuxId → Store WorkerId Frame → Bool
hasMux mid [] = false
hasMux mid ((_ , f) ∷ rest) with frameMux f
... | nothing = hasMux mid rest
... | just own with mid ≟ own
...   | yes _ = true
...   | no _ = hasMux mid rest

-- The current prefix allocates muxes but does not pretend to implement their
-- monitor/tracer/protocol-job execution or graceful group cancellation.
igAllowed : IG.IGAction → State → Bool
igAllowed (IG.installHandle _ _ _ _ _) s = false
igAllowed (IG.installOutboundHandle _ _ _ _ _) s = false
igAllowed action s with Life.muxAction action
... | nothing = true
... | just (mid , access) = not (hasMux mid (frames s))
machineAllowed : M.Action → State → Bool
machineAllowed (M.igStep action) s = igAllowed action s
machineAllowed _ s = true
handlerAllowed : H.Action → State → Bool
handlerAllowed (H.run action) s = machineAllowed action s
handlerAllowed (H.enterHandshake w) s = unframed w s
handlerAllowed (H.deliverHandshakeCancellation w _) s = unframed w s
handlerAllowed (H.deliverBlockedSetupCancellation w _) s = unframed w s
handlerAllowed (H.publishCaught w) s = unframed w s
handlerAllowed (H.rethrowCaught w) s = unframed w s
handlerAllowed (H.enterFinalizer w) s = unframed w s
handlerAllowed (H.cleanup w _) s = unframed w s
handlerAllowed (H.finishCleanup w) s = unframed w s
handlerAllowed (H.publishAsyncResult w) s = unframed w s
handlerAllowed (H.shutdownStep _) s = true
handlerAllowed (H.deliverShutdownHandshake _) s = shutdownTargetAllowed s
handlerAllowed (H.deliverShutdownBlockedSetup _) s = shutdownTargetAllowed s
handlerAllowed (H.deliverShutdownTimeWait _) s = shutdownTargetAllowed s
handlerAllowed H.acknowledgeFinished s = shutdownTargetAllowed s
baseAllowed : B.Action → State → Bool
baseAllowed (B.handler action) s = handlerAllowed action s
baseAllowed (B.outbound (O.inbound _)) s = false
baseAllowed (B.outbound _) s = true
inherit : B.Action → State → Maybe State
inherit action s with baseAllowed action s ∧ birthFresh (birth action (base s)) (origins s)
... | false = nothing
... | true with B.step action (base s)
...   | nothing = nothing
...   | just b = just (noteBirth (birth action (base s)) (record s { base = b }))

-- Negotiate observes restored handshake success before allocation/publication.
-- It does not write a promise, fabricate a physical child, or consult a CM alias.
negotiateReturned : WorkerId → List Protocol → DataFlow → State → Maybe State
negotiateReturned w ps negotiatedFlow s with lookup w (B.threads (base s)) |
  lookup w (origins s) | lookup w (frames s)
... | just t | just origin | nothing with H.phase t
...   | H.handshaking = just (setFrame w
  (frame (H.captured t) origin ps negotiatedFlow returnedSuccess Startup.initial) s)
...   | _ = nothing
negotiateReturned w ps negotiatedFlow s | _ | _ | _ = nothing
allocationAction : Frame → HandleId → MuxId → IG.IGAction
allocationAction f hid mid with birthProvenance f
... | inbound = IG.installHandle hid mid (Shared.handlerKey (captured f)) (bundle f) (flow f)
... | outbound = IG.installOutboundHandle hid mid (Shared.handlerKey (captured f)) (bundle f) (flow f)
allocate : WorkerId → HandleId → MuxId → State → Maybe State
allocate w hid mid s with lookup w (frames s)
... | nothing = nothing
... | just f with progress f
...   | returnedSuccess with O.advance (O.inbound (M.igStep (allocationAction f hid mid))) (source s)
...     | nothing = nothing
...     | just c = just (setFrame w (record f { progress = handleAllocated hid mid }) (setSource c s))
allocate w hid mid s | just f | _ = nothing

-- Promise publication and startup observation are one coupled event. No
-- standalone observePublication action can create a fictitious published handle.
publish : WorkerId → State → Maybe State
publish w s with lookup w (frames s)
... | nothing = nothing
... | just f with progress f
...   | handleAllocated hid mid with O.advance
    (O.inbound (M.handlerPublication w (Shared.negotiated hid (flow f)) M.resultWritten)) (source s) |
    Startup.step Startup.observePublication (startup f)
...     | just c | just next = just (setFrame w
  (record f { progress = promisePublished hid mid; startup = next }) (setSource c s))
publish w s | just f | handleAllocated hid mid | nothing | _ = nothing
publish w s | just f | handleAllocated hid mid | just c | nothing = nothing
publish w s | just f | _ = nothing

-- Actual Async identities are fresh across ALL captured mux histories, including
-- previously deregistered engine children, rather than only the selected pool.
jobFresh : JobId → Store WorkerId Frame → Bool
jobFresh j [] = true
jobFresh j ((_ , f) ∷ rest) with lookup j (Startup.Pool.handles (Startup.pool (startup f)))
... | nothing = jobFresh j rest
... | just _ = false
startupAllowed : Startup.Action → State → Bool
startupAllowed Startup.observePublication s = false
startupAllowed (Startup.forkMuxer j) s = jobFresh j (frames s)
startupAllowed (Startup.forkDemuxer j) s = jobFresh j (frames s)
startupAllowed _ s = true
advanceStartup : WorkerId → Startup.Action → State → Maybe State
advanceStartup w action s with lookup w (frames s)
... | nothing = nothing
... | just f with progress f | startupAllowed action s
...   | promisePublished hid mid | true with Startup.step action (startup f)
...     | nothing = nothing
...     | just next = just (setFrame w (record f { startup = next }) s)
advanceStartup w action s | just f | _ | _ = nothing

data Action : Set where
  run : B.Action → Action
  negotiate : WorkerId → List Protocol → DataFlow → Action
  allocateHandle : WorkerId → HandleId → MuxId → Action
  publishSuccess : WorkerId → Action
  startupStep : WorkerId → Startup.Action → Action
step : Action → State → Maybe State
step (run action) s = inherit action s
step (negotiate w ps negotiatedFlow) s = negotiateReturned w ps negotiatedFlow s
step (allocateHandle w hid mid) s = allocate w hid mid s
step (publishSuccess w) s = publish w s
step (startupStep w action) s = advanceStartup w action s

-- Other actors retain their independent interleavings. This prefix exposes no
-- successful-body exit, buffer release, pool close, handler cleanup, or Async
-- result shortcut for captured success frames.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂

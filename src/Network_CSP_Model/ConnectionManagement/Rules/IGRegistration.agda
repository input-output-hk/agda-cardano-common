{-# OPTIONS --guardedness #-}

-- First nonempty IG batch at network 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d,
-- InboundGovernor.hs:242-398, 585-612. Success-only responder-start contract.
-- This is a prefix, not a replacement for the general IG loop/tracer/mux model.
module ConnectionManagement.Rules.IGRegistration where

open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (ResponderMode; responderMode; noResponderMode; NewConnectionInfo; connectionKey; negotiatedFlow; negotiatedHandle)
open import ConnectionManagement.Store using (Store; lookup; put)

-- All responders have been submitted to runMiniProtocolSTM in one successful
-- transaction. This does NOT mean that a responder has begun running on the mux.
record Registration : Set where
  constructor registered
  field
    notification : NewConnectionInfo
    idleTimer : TimerId
open Registration public

-- Version data is opaque in this slice, referenced through its immutable handle.
record FreshPeer : Set where
  constructor freshPeer
  field
    observedAt : ℕ
    versionFromHandle : HandleId
open FreshPeer public

record Published : Set where
  constructor published
  field
    connections : Store ConnectionKey Registration
    freshPeers : Store PeerAddr FreshPeer
open Published public

emptyPublished : Published
emptyPublished = published [] []

-- Captured state is retained across the IO timer allocation and STM publication.
-- A duplicate takes the source's later StateWithPeerTransition write path.
data PC : Set where
  sampleTime : PC
  armInactivity : ℕ → PC
  awaitFirstBatch : ℕ → TimerId → PC
  readNext : ℕ → List NewConnectionInfo → PC
  prepareNew : ℕ → NewConnectionInfo → List NewConnectionInfo → Published → PC
  startResponders : ℕ → NewConnectionInfo → List NewConnectionInfo → Published → TimerId → PC
  publishDuplicate : ℕ → List NewConnectionInfo → Published → PC

record Runtime : Set where
  constructor runtime
  field
    publishedState : Published
    nextTimer : ℕ
    continuation : PC
open Runtime public

initial : Runtime
initial = runtime emptyPublished 0 sampleTime

data IGAction : Set where
  captureTime : ℕ → IGAction
  registerInactivity drainFirstBatch readEvent registerIdleTimer
    successfulResponderStart commitDuplicate : IGAction

-- Queue replacement is the only effect on the pre-existing CM world. Returning
-- both parts lets Machine commit a drain and its retained batch together.
Result = Runtime × List NewConnectionInfo

-- Preserve the source distinction: only duplex registration enters freshness.
addFresh : ℕ → NewConnectionInfo → Published → Store PeerAddr FreshPeer
addFresh time info old with negotiatedFlow info
... | unidirectional = freshPeers old
... | duplex = put (remote (connectionKey info))
  (freshPeer time (negotiatedHandle info)) (freshPeers old)

stepWorker : IGAction → Runtime → List NewConnectionInfo → Maybe Result
stepWorker (captureTime time) (runtime old n sampleTime) queue =
  just (runtime old n (armInactivity time) , queue)
stepWorker registerInactivity (runtime old n (armInactivity time)) queue =
  just (runtime old (suc n) (awaitFirstBatch time (ident n)) , queue)
-- Empty registry/freshness justify absence of maturity/peer-commit alternatives.
-- A nonempty queue precedes inactivity regardless of that timer's readiness.
-- Do not reuse this rule for a later iteration with registered connections.
stepWorker drainFirstBatch (runtime (published [] []) n (awaitFirstBatch time timerRef)) queue@(_ ∷ _) =
  just (runtime emptyPublished n (readNext time queue) , [])
stepWorker readEvent (runtime old n (readNext time (info ∷ rest))) queue
  with lookup (connectionKey info) (connections old)
... | nothing = just (runtime old n (prepareNew time info rest old) , queue)
... | just _ = just (runtime old n (publishDuplicate time rest old) , queue)
stepWorker registerIdleTimer (runtime old n (prepareNew time info rest captured)) queue =
  just (runtime old (suc n) (startResponders time info rest captured (ident n)) , queue)
-- Explicit external success boundary: all runResponder calls succeed. There is
-- no independently schedulable responder-start/registry-write interval. Failure,
-- cancellation, tracer effects and actual protocol execution are not implemented.
stepWorker successfulResponderStart (runtime old n (startResponders time info rest captured timerRef)) queue =
  just (runtime (published
    (put (connectionKey info) (registered info timerRef) (connections captured))
    (addFresh time info captured)) n (readNext time rest) , queue)
stepWorker commitDuplicate (runtime old n (publishDuplicate time rest captured)) queue =
  just (runtime captured n (readNext time rest) , queue)
stepWorker _ _ _ = nothing

-- No IG is installed for an initiator-only configuration.
step : ResponderMode → IGAction → Runtime → List NewConnectionInfo → Maybe Result
step noResponderMode _ _ _ = nothing
step responderMode a ig queue = stepWorker a ig queue

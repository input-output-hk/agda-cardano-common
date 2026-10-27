{-# OPTIONS --guardedness #-}

-- A single-spawning-owner pool, with explicit completion-queue policy.
-- Source: JobPool.hs:105-109,119-164 at the network pin. The supplied close
-- order represents the source map traversal order; this module checks its
-- membership, not a concrete ThreadId ordering. No CM unwind/join is invented.
open import Data.Bool using (Bool)
module ConnectionManagement.Rules.JobPoolKernel (Result : Set) (queued : Bool) where

open import Data.Bool using (Bool; true; false; not; _∧_)
open import Data.List using (List; []; _∷_; _++_; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put)

-- Body completion, queue publication, deregistration and Async terminal-result
-- availability are different events. A cancelled body produces no queue result.
data Exit : Set where
  normalExit cancelledExit : Exit

data ThreadPhase : Set where
  bodyRunning : ThreadPhase
  bodyReturned : Result → ThreadPhase
  bodyUnwinding : ThreadPhase
  deregisterPending deregistered resultAvailable : Exit → ThreadPhase

-- The snapshot tail remains intact until the current handle is actually joined.
data ClosePC : Set where
  openPool closing closedPool : ClosePC
  cancelPending joinPending : JobId → ClosePC

record State : Set where
  constructor poolState
  field
    handles : Store JobId ThreadPhase
    registered : List JobId
    parentFork : Maybe JobId
    phase : ClosePC
    snapshot remaining joined : List JobId
    completions : List Result
open State public

-- Start with an empty scope, without pre-seeded completion or join evidence.
initial : State
initial = poolState [] [] nothing openPool [] [] [] []

-- Job identities denote captured Async handles and are never recycled.
member : JobId → List JobId → Bool
member j [] = false
member j (k ∷ ks) with j ≟ k
... | yes _ = true
... | no _ = member j ks
unique : List JobId → Bool
unique [] = true
unique (j ∷ js) = not (member j js) ∧ unique js
allMembers : List JobId → List JobId → Bool
allMembers [] ys = true
allMembers (j ∷ js) ys = member j ys ∧ allMembers js ys

-- Map traversal is represented by an explicit order, with exact unique current
-- registry membership. Historical handles removed earlier are not recaptured.
sameSnapshot : List JobId → List JobId → Bool
sameSnapshot order current = unique order ∧ unique current ∧
  allMembers order current ∧ allMembers current order

-- The source child deregister operation removes only its own current registry
-- binding; the Async handle remains in historical storage and captured snapshots.
remove : JobId → List JobId → List JobId
remove j = filterᵇ (λ k → not (does (j ≟ k)))

-- Thread operations may interleave with the sequential closing owner.
data Action : Set where
  fork : JobId → Action
  register : Action
  bodyReturnedWith : JobId → Result → Action
  publishCompletion bodyUnwound deregister publishAsyncResult : JobId → Action
  resumeAfterUnwindError : JobId → Action
  beginClose : List JobId → Action
  requestCancel deliverCancel join finishClose : Action

-- Only a terminal result of the current captured handle advances the close
-- cursor. Registry membership and queue entries are deliberately irrelevant.
joinHead : JobId → State → Maybe State
joinHead current s with remaining s | lookup current (handles s)
... | j ∷ rest | just (resultAvailable exit) with current ≟ j
...   | yes _ = just (record s { phase = closing; remaining = rest; joined = joined s ++ (j ∷ []) })
...   | no _ = nothing
joinHead current s | _ | _ = nothing

-- WithoutQueue has no publication event or completion queue. Its returned
-- result is discarded before the child attempts deregistration.
returnedPhase : Bool → Result → ThreadPhase
returnedPhase true result = bodyReturned result
returnedPhase false result = deregisterPending normalExit

-- The publication operation exists only in the WithQueue specialization.
publishQueued : Bool → JobId → State → Maybe State
publishQueued false j s = nothing
publishQueued true j s with lookup j (handles s)
... | just (bodyReturned result) = just (record s
  { handles = put j (deregisterPending normalExit) (handles s)
  ; completions = completions s ++ (result ∷ []) })
... | _ = nothing

-- Owner fork and registration are separate source boundaries. While the parent
-- is masked in this gap it cannot start its own lexical close operation.
step : Action → State → Maybe State
step (fork j) s with phase s | parentFork s | lookup j (handles s)
... | openPool | nothing | nothing = just (record s
  { handles = put j bodyRunning (handles s); parentFork = just j })
... | _ | _ | _ = nothing
step register s with phase s | parentFork s
... | openPool | just j with member j (registered s)
...   | false = just (record s { registered = j ∷ registered s; parentFork = nothing })
...   | true = nothing
step register s | _ | _ = nothing

-- The body-return boundary carries the actual job/handler result, not a promise
-- of thread termination. Publication occurs before ordinary deregistration.
step (bodyReturnedWith j result) s with lookup j (handles s)
... | just bodyRunning = just (record s { handles = put j (returnedPhase queued result) (handles s) })
... | _ = nothing
step (publishCompletion j) s = publishQueued queued j s

-- This is an explicit local body-unwind completion boundary. It does not assert
-- that any unmodeled CM bracket, socket cleanup or exception mask was verified.
step (bodyUnwound j) s with lookup j (handles s)
... | just bodyUnwinding = just (record s { handles = put j (deregisterPending cancelledExit) (handles s) })
... | _ = nothing

-- A throwing bracket finalizer can replace AsyncCancelled by a synchronous
-- error. An integrating adapter must establish that replacement before using
-- this action; its ordinary exception handler may then produce a job result.
step (resumeAfterUnwindError j) s with lookup j (handles s)
... | just bodyUnwinding = just (record s { handles = put j bodyRunning (handles s) })
... | _ = nothing
step (deregister j) s with lookup j (handles s) | member j (registered s)
... | just (deregisterPending exit) | true = just (record s
  { handles = put j (deregistered exit) (handles s); registered = remove j (registered s) })
... | _ | _ = nothing

-- The Async wrapper exposes its terminal result only after the child has
-- deregistered; neither cancellation delivery nor an empty registry suffices.
step (publishAsyncResult j) s with lookup j (handles s)
... | just (deregistered exit) = just (record s { handles = put j (resultAvailable exit) (handles s) })
... | _ = nothing

-- Read the current registry ONCE after the spawning owner leaves its body.
-- The model is for the governor pool's single spawning owner; peer-monitor and
-- transport pools require their own owners and independently ordered snapshots.
step (beginClose order) s with phase s | parentFork s | sameSnapshot order (registered s)
... | openPool | nothing | true = just (record s
  { phase = closing; snapshot = order; remaining = order; joined = [] })
... | _ | _ | _ = nothing
step requestCancel s with phase s | remaining s
... | closing | j ∷ rest with lookup j (handles s)
...   | nothing = nothing
...   | just (resultAvailable exit) = just (record s { phase = joinPending j })
...   | just _ = just (record s { phase = cancelPending j })
step requestCancel s | _ | _ = nothing

-- Delivery requires the restored interruptible running body. Masked normal
-- publication/deregistration may instead finish before delivery; no fictitious
-- asynchronous exception is inserted at every syntactic post-return gap.
step deliverCancel s with phase s
... | cancelPending j with lookup j (handles s)
...   | just bodyRunning = just (record s
  { phase = joinPending j; handles = put j bodyUnwinding (handles s) })
...   | _ = nothing
step deliverCancel s | _ = nothing

-- A normal exit can outrun the pending cancel, and an already completed Async
-- needs no delivery. In either case join still observes the captured handle.
step join s with phase s
... | cancelPending j = joinHead j s
... | joinPending j = joinHead j s
... | _ = nothing
step finishClose s with phase s | remaining s
... | closing | [] = just (record s { phase = closedPool })
... | _ | _ = nothing

-- Closure is finite operational evidence, not a fairness or termination axiom.
data Executes : State → List Action → State → Set where
  done : ∀ {s} → Executes s [] s
  next : ∀ {s s₁ s₂ a as} → step a s ≡ just s₁ → Executes s₁ as s₂ → Executes s (a ∷ as) s₂

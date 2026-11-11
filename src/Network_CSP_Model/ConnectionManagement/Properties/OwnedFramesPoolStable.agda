{-# OPTIONS --guardedness #-}

-- Pool operations that preserve running/non-running status can be transported
-- without inspecting the processes that own those historical handles.
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.OwnedFramesPoolStable (Result : Set) (queued : Bool) where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (JobId)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Rules.JobPoolKernel as Kernel
module Pool = Kernel Result queued

-- Running owners survive, and detached non-running handles remain represented.
record Stable (before after : Pool.State) : Set where
  field
    running : ∀ j → lookup j (Pool.handles before) ≡ just Pool.bodyRunning → lookup j (Pool.handles after) ≡ just Pool.bodyRunning
    stopped : ∀ j phase → lookup j (Pool.handles before) ≡ just phase → phase ≢ Pool.bodyRunning →
      Σ Pool.ThreadPhase (λ next → lookup j (Pool.handles after) ≡ just next × next ≢ Pool.bodyRunning)

-- Cursor, registry and queue changes with identical handle tables are stable.
same-stable : ∀ p p′ → Pool.handles p′ ≡ Pool.handles p → Stable p p′
same-stable p p′ handles = record
  { running = λ j found → trans (cong (lookup j) handles) found
  ; stopped = λ j phase found apart → phase , trans (cong (lookup j) handles) found , apart }

-- Replacing a known non-running handle by a non-running phase is stable.
put-stable : ∀ p p′ tid old next → lookup tid (Pool.handles p) ≡ just old → old ≢ Pool.bodyRunning → next ≢ Pool.bodyRunning →
  Pool.handles p′ ≡ put tid next (Pool.handles p) → Stable p p′
put-stable p p′ tid old next saved old-stopped next-stopped handles = record { running = runs; stopped = stops }
  where
  runs : ∀ j → lookup j (Pool.handles p) ≡ just Pool.bodyRunning → lookup j (Pool.handles p′) ≡ just Pool.bodyRunning
  runs j found with j ≟ tid
  ... | yes refl = ⊥-elim (old-stopped (just-injective (trans (sym saved) found)))
  ... | no apart = trans (cong (lookup j) handles) (trans (lookup-put-other tid j next (Pool.handles p) apart) found)
  stops : ∀ j phase → lookup j (Pool.handles p) ≡ just phase → phase ≢ Pool.bodyRunning →
    Σ Pool.ThreadPhase (λ phase′ → lookup j (Pool.handles p′) ≡ just phase′ × phase′ ≢ Pool.bodyRunning)
  stops j phase found apart with j ≟ tid
  ... | yes refl = next , trans (cong (lookup tid) handles) (lookup-put tid next (Pool.handles p)) , next-stopped
  ... | no other = phase , trans (cong (lookup j) handles) (trans (lookup-put-other tid j next (Pool.handles p) other) found) , apart

-- A fresh fork preserves every previously represented handle's status.
fresh-stable : ∀ p p′ tid next → lookup tid (Pool.handles p) ≡ nothing → Pool.handles p′ ≡ put tid next (Pool.handles p) → Stable p p′
fresh-stable p p′ tid next fresh handles = record { running = runs; stopped = stops }
  where
  runs : ∀ j → lookup j (Pool.handles p) ≡ just Pool.bodyRunning → lookup j (Pool.handles p′) ≡ just Pool.bodyRunning
  runs j found with j ≟ tid
  ... | yes refl = case trans (sym fresh) found of λ ()
  ... | no apart = trans (cong (lookup j) handles) (trans (lookup-put-other tid j next (Pool.handles p) apart) found)
  stops : ∀ j phase → lookup j (Pool.handles p) ≡ just phase → phase ≢ Pool.bodyRunning →
    Σ Pool.ThreadPhase (λ phase′ → lookup j (Pool.handles p′) ≡ just phase′ × phase′ ≢ Pool.bodyRunning)
  stops j phase found apart with j ≟ tid
  ... | yes refl = case trans (sym fresh) found of λ ()
  ... | no other = phase , trans (cong (lookup j) handles) (trans (lookup-put-other tid j next (Pool.handles p) other) found) , apart

-- Joining consumes only cursor metadata and never edits handle phases.
join-stable : ∀ j p {p′} → Pool.joinHead j p ≡ just p′ → Stable p p′
join-stable j p eq with Pool.remaining p | lookup j (Pool.handles p)
... | k ∷ rest | just (Pool.resultAvailable exit) with j ≟ k
...   | yes same = case just-injective eq of λ { refl → same-stable p _ refl }
...   | no apart = case eq of λ ()
join-stable j p eq | [] | handle = case eq of λ ()
join-stable j p eq | k ∷ rest | nothing = case eq of λ ()
join-stable j p eq | k ∷ rest | just Pool.bodyRunning = case eq of λ ()
join-stable j p eq | k ∷ rest | just Pool.bodyUnwinding = case eq of λ ()
join-stable j p eq | k ∷ rest | just (Pool.bodyReturned _) = case eq of λ ()
join-stable j p eq | k ∷ rest | just (Pool.deregisterPending _) = case eq of λ ()
join-stable j p eq | k ∷ rest | just (Pool.deregistered _) = case eq of λ ()

-- Expose the queue policy as a function argument, rather than splitting a module parameter.
fork-concurrent-stable : ∀ mode j p {p′} → Pool.concurrentFork mode j p ≡ just p′ → Stable p p′
fork-concurrent-stable true j p eq = case eq of λ ()
fork-concurrent-stable false j p eq with Pool.phase p | lookup j (Pool.handles p) in fresh
...   | Pool.openPool | nothing = case just-injective eq of λ { refl → fresh-stable p _ j Pool.bodyRunning fresh refl }
fork-concurrent-stable false j p eq | Pool.openPool | just phase = case eq of λ ()
fork-concurrent-stable false j p eq | Pool.closing | handle = case eq of λ ()
fork-concurrent-stable false j p eq | Pool.closedPool | handle = case eq of λ ()
fork-concurrent-stable false j p eq | Pool.cancelPending tid | handle = case eq of λ ()
fork-concurrent-stable false j p eq | Pool.joinPending tid | handle = case eq of λ ()

-- Expose the queue policy as a function argument, rather than splitting a module parameter.
register-concurrent-stable : ∀ mode j p {p′} → Pool.concurrentRegister mode j p ≡ just p′ → Stable p p′
register-concurrent-stable true j p eq = case eq of λ ()
register-concurrent-stable false j p eq with Pool.phase p | lookup j (Pool.handles p) | Pool.member j (Pool.registered p)
...   | Pool.openPool | just phase | false with Pool.awaitingRegistration phase
...     | true = case just-injective eq of λ { refl → same-stable p _ refl }
...     | false = case eq of λ ()
register-concurrent-stable false j p eq | Pool.openPool | nothing | member = case eq of λ ()
register-concurrent-stable false j p eq | Pool.openPool | just phase | true = case eq of λ ()
register-concurrent-stable false j p eq | Pool.closing | handle | member = case eq of λ ()
register-concurrent-stable false j p eq | Pool.closedPool | handle | member = case eq of λ ()
register-concurrent-stable false j p eq | Pool.cancelPending tid | handle | member = case eq of λ ()
register-concurrent-stable false j p eq | Pool.joinPending tid | handle | member = case eq of λ ()

-- Expose the queue policy as a function argument, rather than splitting a module parameter.
publish-queued-stable : ∀ mode j p {p′} → Pool.publishQueued mode j p ≡ just p′ → Stable p p′
publish-queued-stable false j p eq = case eq of λ ()
publish-queued-stable true j p eq with lookup j (Pool.handles p) in found
...   | just (Pool.bodyReturned captured) = case just-injective eq of λ { refl → put-stable p _ j (Pool.bodyReturned captured) (Pool.deregisterPending Pool.normalExit) found (λ ()) (λ ()) refl }
publish-queued-stable true j p eq | nothing = case eq of λ ()
publish-queued-stable true j p eq | just Pool.bodyRunning = case eq of λ ()
publish-queued-stable true j p eq | just Pool.bodyUnwinding = case eq of λ ()
publish-queued-stable true j p eq | just (Pool.deregisterPending exit) = case eq of λ ()
publish-queued-stable true j p eq | just (Pool.deregistered exit) = case eq of λ ()
publish-queued-stable true j p eq | just (Pool.resultAvailable exit) = case eq of λ ()


-- Expose the queue policy as a function argument, rather than splitting a module parameter.
consume-queued-stable : ∀ mode p {p′} → Pool.consumeQueued mode p ≡ just p′ → Stable p p′
consume-queued-stable false p eq = case eq of λ ()
consume-queued-stable true p eq with Pool.phase p | Pool.completions p
...   | Pool.openPool | captured ∷ rest = case just-injective eq of λ { refl → same-stable p _ refl }
consume-queued-stable true p eq | Pool.openPool | [] = case eq of λ ()
consume-queued-stable true p eq | Pool.closing | queue = case eq of λ ()
consume-queued-stable true p eq | Pool.closedPool | queue = case eq of λ ()
consume-queued-stable true p eq | (Pool.cancelPending tid) | queue = case eq of λ ()
consume-queued-stable true p eq | (Pool.joinPending tid) | queue = case eq of λ ()


-- Four running-status writers need their process-specific ownership proofs.
stable-action : Pool.Action → Bool
stable-action (Pool.bodyReturnedWith _ _) = false
stable-action Pool.deliverCancel = false
stable-action (Pool.resumeAfterUnwindError _) = false
stable-action (Pool.interruptJob _) = false
stable-action _ = true

-- All other actual kernel actions preserve both status clauses.
step-stable : ∀ a p {p′} → stable-action a ≡ true → Pool.step a p ≡ just p′ → Stable p p′
step-stable (Pool.bodyReturnedWith j captured) p () eq
step-stable Pool.deliverCancel p () eq
step-stable (Pool.resumeAfterUnwindError j) p () eq
step-stable (Pool.interruptJob j) p () eq
step-stable (Pool.fork j) p permit eq with Pool.phase p | Pool.parentFork p | lookup j (Pool.handles p) in fresh
... | Pool.openPool | nothing | nothing = case just-injective eq of λ { refl → fresh-stable p _ j Pool.bodyRunning fresh refl }
step-stable (Pool.fork j) p permit eq | Pool.openPool | just parent | handle = case eq of λ ()
step-stable (Pool.fork j) p permit eq | Pool.openPool | nothing | just phase = case eq of λ ()
step-stable (Pool.fork j) p permit eq | Pool.closing | parent | handle = case eq of λ ()
step-stable (Pool.fork j) p permit eq | Pool.closedPool | parent | handle = case eq of λ ()
step-stable (Pool.fork j) p permit eq | Pool.cancelPending tid | parent | handle = case eq of λ ()
step-stable (Pool.fork j) p permit eq | Pool.joinPending tid | parent | handle = case eq of λ ()
step-stable Pool.register p permit eq with Pool.phase p | Pool.parentFork p
... | Pool.openPool | just j with Pool.member j (Pool.registered p)
...   | false = case just-injective eq of λ { refl → same-stable p _ refl }
...   | true = case eq of λ ()
step-stable Pool.register p permit eq | Pool.openPool | nothing = case eq of λ ()
step-stable Pool.register p permit eq | Pool.closing | parent = case eq of λ ()
step-stable Pool.register p permit eq | Pool.closedPool | parent = case eq of λ ()
step-stable Pool.register p permit eq | Pool.cancelPending j | parent = case eq of λ ()
step-stable Pool.register p permit eq | Pool.joinPending j | parent = case eq of λ ()
step-stable (Pool.forkConcurrent j) p permit eq = fork-concurrent-stable queued j p eq
step-stable (Pool.registerConcurrent j) p permit eq = register-concurrent-stable queued j p eq
step-stable (Pool.publishCompletion j) p permit eq = publish-queued-stable queued j p eq
step-stable Pool.consumeCompletion p permit eq = consume-queued-stable queued p eq
step-stable (Pool.bodyUnwound j) p permit eq with lookup j (Pool.handles p) in found
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → put-stable p _ j Pool.bodyUnwinding (Pool.deregisterPending Pool.cancelledExit) found (λ ()) (λ ()) refl }
step-stable (Pool.bodyUnwound j) p permit eq | nothing = case eq of λ ()
step-stable (Pool.bodyUnwound j) p permit eq | just Pool.bodyRunning = case eq of λ ()
step-stable (Pool.bodyUnwound j) p permit eq | just (Pool.bodyReturned captured) = case eq of λ ()
step-stable (Pool.bodyUnwound j) p permit eq | just (Pool.deregisterPending exit) = case eq of λ ()
step-stable (Pool.bodyUnwound j) p permit eq | just (Pool.deregistered exit) = case eq of λ ()
step-stable (Pool.bodyUnwound j) p permit eq | just (Pool.resultAvailable exit) = case eq of λ ()

step-stable (Pool.deregister j) p permit eq with lookup j (Pool.handles p) in found | Pool.member j (Pool.registered p)
... | just (Pool.deregisterPending exit) | true = case just-injective eq of λ { refl → put-stable p _ j (Pool.deregisterPending exit) (Pool.deregistered exit) found (λ ()) (λ ()) refl }
step-stable (Pool.deregister j) p permit eq | just (Pool.deregisterPending exit) | false = case eq of λ ()
step-stable (Pool.deregister j) p permit eq | nothing | member = case eq of λ ()
step-stable (Pool.deregister j) p permit eq | just Pool.bodyRunning | member = case eq of λ ()
step-stable (Pool.deregister j) p permit eq | just Pool.bodyUnwinding | member = case eq of λ ()
step-stable (Pool.deregister j) p permit eq | just (Pool.bodyReturned captured) | member = case eq of λ ()
step-stable (Pool.deregister j) p permit eq | just (Pool.deregistered exit) | member = case eq of λ ()
step-stable (Pool.deregister j) p permit eq | just (Pool.resultAvailable exit) | member = case eq of λ ()

step-stable (Pool.publishAsyncResult j) p permit eq with lookup j (Pool.handles p) in found
... | just (Pool.deregistered exit) = case just-injective eq of λ { refl → put-stable p _ j (Pool.deregistered exit) (Pool.resultAvailable exit) found (λ ()) (λ ()) refl }
step-stable (Pool.publishAsyncResult j) p permit eq | nothing = case eq of λ ()
step-stable (Pool.publishAsyncResult j) p permit eq | just Pool.bodyRunning = case eq of λ ()
step-stable (Pool.publishAsyncResult j) p permit eq | just Pool.bodyUnwinding = case eq of λ ()
step-stable (Pool.publishAsyncResult j) p permit eq | just (Pool.bodyReturned captured) = case eq of λ ()
step-stable (Pool.publishAsyncResult j) p permit eq | just (Pool.deregisterPending exit) = case eq of λ ()
step-stable (Pool.publishAsyncResult j) p permit eq | just (Pool.resultAvailable exit) = case eq of λ ()

step-stable (Pool.beginClose order) p permit eq with Pool.phase p | Pool.parentFork p | Pool.canSnapshot queued order p
... | Pool.openPool | nothing | true = case just-injective eq of λ { refl → same-stable p _ refl }
step-stable (Pool.beginClose order) p permit eq | Pool.openPool | nothing | false = case eq of λ ()
step-stable (Pool.beginClose order) p permit eq | Pool.openPool | just parent | valid = case eq of λ ()
step-stable (Pool.beginClose order) p permit eq | Pool.closing | parent | valid = case eq of λ ()
step-stable (Pool.beginClose order) p permit eq | Pool.closedPool | parent | valid = case eq of λ ()
step-stable (Pool.beginClose order) p permit eq | (Pool.cancelPending tid) | parent | valid = case eq of λ ()
step-stable (Pool.beginClose order) p permit eq | (Pool.joinPending tid) | parent | valid = case eq of λ ()

step-stable Pool.requestCancel p permit eq with Pool.phase p | Pool.remaining p
... | Pool.closing | j ∷ rest with lookup j (Pool.handles p)
...   | nothing = case eq of λ ()
...   | just Pool.bodyRunning = case just-injective eq of λ { refl → same-stable p _ refl }
...   | just Pool.bodyUnwinding = case just-injective eq of λ { refl → same-stable p _ refl }
...   | just (Pool.bodyReturned captured) = case just-injective eq of λ { refl → same-stable p _ refl }
...   | just (Pool.deregisterPending exit) = case just-injective eq of λ { refl → same-stable p _ refl }
...   | just (Pool.deregistered exit) = case just-injective eq of λ { refl → same-stable p _ refl }
...   | just (Pool.resultAvailable exit) = case just-injective eq of λ { refl → same-stable p _ refl }
step-stable Pool.requestCancel p permit eq | Pool.closing | [] = case eq of λ ()
step-stable Pool.requestCancel p permit eq | Pool.openPool | rest = case eq of λ ()
step-stable Pool.requestCancel p permit eq | Pool.closedPool | rest = case eq of λ ()
step-stable Pool.requestCancel p permit eq | (Pool.cancelPending tid) | rest = case eq of λ ()
step-stable Pool.requestCancel p permit eq | (Pool.joinPending tid) | rest = case eq of λ ()

step-stable Pool.join p permit eq with Pool.phase p
... | Pool.cancelPending j = join-stable j p eq
... | Pool.joinPending j = join-stable j p eq
step-stable Pool.join p permit eq | Pool.openPool = case eq of λ ()
step-stable Pool.join p permit eq | Pool.closing = case eq of λ ()
step-stable Pool.join p permit eq | Pool.closedPool = case eq of λ ()

step-stable Pool.finishClose p permit eq with Pool.phase p | Pool.remaining p
... | Pool.closing | [] = case just-injective eq of λ { refl → same-stable p _ refl }
step-stable Pool.finishClose p permit eq | Pool.closing | j ∷ rest = case eq of λ ()
step-stable Pool.finishClose p permit eq | Pool.openPool | rest = case eq of λ ()
step-stable Pool.finishClose p permit eq | Pool.closedPool | rest = case eq of λ ()
step-stable Pool.finishClose p permit eq | (Pool.cancelPending tid) | rest = case eq of λ ()
step-stable Pool.finishClose p permit eq | (Pool.joinPending tid) | rest = case eq of λ ()

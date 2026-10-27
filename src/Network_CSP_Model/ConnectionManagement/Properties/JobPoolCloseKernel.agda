{-# OPTIONS --guardedness #-}

-- A finished pool close certifies Async results for its captured handles.
-- This concerns one pool snapshot, not every historical child or diffusion exit.
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.JobPoolCloseKernel (Result : Set) (queued : Bool) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.Rules.JobPoolKernel as Lifecycle
module Pool = Lifecycle Result queued

-- Terminal means the Async result is available, rather than registry absence.
Terminal : Pool.State → JobId → Set
Terminal c j = Σ Pool.Exit (λ ex → lookup j (Pool.handles c) ≡ just (Pool.resultAvailable ex))

-- A snapshot member is still to be joined, or already has an observable result.
Covered : Pool.State → Set
Covered c = ∀ j → j ∈ Pool.snapshot c → (j ∈ Pool.remaining c) ⊎ Terminal c j

-- The closed control point has exhausted its immutable snapshot cursor.
ClosedEmpty : Pool.State → Set
ClosedEmpty c = Pool.phase c ≡ Pool.closedPool → Pool.remaining c ≡ []

-- Restore the unabstracted cursor after an inspected projection equality.
restore-covered : ∀ c rest → Pool.remaining c ≡ rest →
  (∀ j → j ∈ Pool.snapshot c → (j ∈ rest) ⊎ Terminal c j) → Covered c
restore-covered c rest eq valid = subst
  (λ todo → ∀ j → j ∈ Pool.snapshot c → (j ∈ todo) ⊎ Terminal c j)
  (sym eq) valid

-- Changes to a different handle preserve the complete terminal observation.
other-write : ∀ c k phase j → j ≢ k → Terminal c j →
  Σ Pool.Exit (λ ex → lookup j (put k phase (Pool.handles c)) ≡ just (Pool.resultAvailable ex))
other-write c k phase j apart (ex , found) =
  ex , trans (lookup-put-other k j phase (Pool.handles c) apart) found

-- Updating a nonterminal handle cannot invalidate another handle's result.
nonterminal-write : ∀ c k old phase →
  lookup k (Pool.handles c) ≡ just old →
  (∀ ex → old ≢ Pool.resultAvailable ex) → ∀ j → Terminal c j →
  Σ Pool.Exit (λ ex → lookup j (put k phase (Pool.handles c)) ≡ just (Pool.resultAvailable ex))
nonterminal-write c k old phase found nonterminal j terminal with j ≟ k
... | no apart = other-write c k phase j apart terminal
... | yes refl with terminal
...   | ex , available = ⊥-elim (nonterminal ex (just-injective (trans (sym found) available)))

-- Fresh allocation cannot replace a previously observed Async result.
fresh-write : ∀ c k phase → lookup k (Pool.handles c) ≡ nothing →
  ∀ j → Terminal c j →
  Σ Pool.Exit (λ ex → lookup j (put k phase (Pool.handles c)) ≡ just (Pool.resultAvailable ex))
fresh-write c k phase absent j terminal with j ≟ k
... | no apart = other-write c k phase j apart terminal
... | yes refl with terminal
...   | ex , available with trans (sym absent) available
...     | ()

-- Cursor-preserving writes retain the certificate for every snapshot member.
write-preserves : ∀ c k old phase →
  lookup k (Pool.handles c) ≡ just old →
  (∀ ex → old ≢ Pool.resultAvailable ex) → Covered c →
  Covered (record c { handles = put k phase (Pool.handles c) })
write-preserves c k old phase found nonterminal valid j member with valid j member
... | inj₁ pending = inj₁ pending
... | inj₂ terminal = inj₂ (nonterminal-write c k old phase found nonterminal j terminal)

-- Allocation is fresh even with respect to already deregistered Async handles.
fresh-preserves : ∀ c k phase → lookup k (Pool.handles c) ≡ nothing → Covered c →
  Covered (record c { handles = put k phase (Pool.handles c) })
fresh-preserves c k phase absent valid j member with valid j member
... | inj₁ pending = inj₁ pending
... | inj₂ terminal = inj₂ (fresh-write c k phase absent j terminal)

-- A successful join removes only a head whose actual Async result is observed.
join-preserves : ∀ current c {c′} →
  Pool.joinHead current c ≡ just c′ → Covered c → Covered c′
join-preserves current c eq valid with Pool.remaining c | lookup current (Pool.handles c) in found
... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
...   | no _ = case eq of λ ()
...   | yes refl with just-injective eq
...     | refl = λ j member → joined j member (valid j member)
  where
  joined : ∀ j → j ∈ Pool.snapshot c →
    (j ∈ (head ∷ rest)) ⊎ Terminal c j →
    (j ∈ rest) ⊎ Terminal c j
  joined j member (inj₂ terminal) = inj₂ terminal
  joined j member (inj₁ pending) with pending
  ... | here refl = inj₂ (exit , found)
  ... | there tail = inj₁ tail
join-preserves current c eq valid | [] | _ = case eq of λ ()
join-preserves current c eq valid | _ ∷ _ | nothing = case eq of λ ()
join-preserves current c eq valid | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
join-preserves current c eq valid | _ ∷ _ | just (Pool.bodyReturned _) = case eq of λ ()
join-preserves current c eq valid | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
join-preserves current c eq valid | _ ∷ _ | just (Pool.deregisterPending _) = case eq of λ ()
join-preserves current c eq valid | _ ∷ _ | just (Pool.deregistered _) = case eq of λ ()

-- Queue-free pools have no publication transition to project.
publish-covered : ∀ enabled k c {c′} → Pool.publishQueued enabled k c ≡ just c′ → Covered c → Covered c′
publish-covered false k c () valid
publish-covered true k c eq valid with lookup k (Pool.handles c) in found
... | just (Pool.bodyReturned result) = case just-injective eq of λ { refl →
  write-preserves c k (Pool.bodyReturned result) (Pool.deregisterPending Pool.normalExit) found (λ _ ()) valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()

-- Queue-free pools have no publication transition to project.
publish-empty : ∀ enabled k c {c′} → Pool.publishQueued enabled k c ≡ just c′ → ClosedEmpty c → ClosedEmpty c′
publish-empty false k c () valid
publish-empty true k c eq valid with lookup k (Pool.handles c)
... | just (Pool.bodyReturned result) = case just-injective eq of λ { refl → valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()

-- Every successful primitive preserves coverage; no scheduling restriction is
-- imposed on body completion, deregistration or Async result publication.
step-preserves : ∀ a c {c′} → Pool.step a c ≡ just c′ → Covered c → Covered c′
step-preserves (Pool.fork k) c eq valid with Pool.phase c | Pool.parentFork c | lookup k (Pool.handles c) in absent
... | Pool.openPool | nothing | nothing with just-injective eq
...   | refl = fresh-preserves c k Pool.bodyRunning absent valid
step-preserves (Pool.fork k) c eq valid | Pool.closing | _ | _ = case eq of λ ()
step-preserves (Pool.fork k) c eq valid | Pool.closedPool | _ | _ = case eq of λ ()
step-preserves (Pool.fork k) c eq valid | (Pool.cancelPending k₁) | _ | _ = case eq of λ ()
step-preserves (Pool.fork k) c eq valid | (Pool.joinPending k₁) | _ | _ = case eq of λ ()
step-preserves (Pool.fork k) c eq valid | Pool.openPool | just pending | _ = case eq of λ ()
step-preserves (Pool.fork k) c eq valid | Pool.openPool | nothing | just old = case eq of λ ()
step-preserves Pool.register c eq valid with Pool.phase c | Pool.parentFork c
... | Pool.openPool | just k with Pool.member k (Pool.registered c)
...   | false = case just-injective eq of λ { refl → valid }
...   | true = case eq of λ ()
step-preserves Pool.register c eq valid | Pool.closing | _ = case eq of λ ()
step-preserves Pool.register c eq valid | Pool.closedPool | _ = case eq of λ ()
step-preserves Pool.register c eq valid | (Pool.cancelPending k₁) | _ = case eq of λ ()
step-preserves Pool.register c eq valid | (Pool.joinPending k₁) | _ = case eq of λ ()
step-preserves Pool.register c eq valid | Pool.openPool | nothing = case eq of λ ()
step-preserves (Pool.bodyReturnedWith k result) c eq valid with lookup k (Pool.handles c) in found
... | just Pool.bodyRunning = case just-injective eq of λ { refl →
  write-preserves c k Pool.bodyRunning (Pool.returnedPhase queued result) found (λ _ ()) valid }
... | nothing = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-preserves (Pool.publishCompletion k) c eq valid = publish-covered queued k c eq valid
step-preserves (Pool.bodyUnwound k) c eq valid with lookup k (Pool.handles c) in found
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl →
  write-preserves c k Pool.bodyUnwinding (Pool.deregisterPending Pool.cancelledExit) found (λ _ ()) valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-preserves (Pool.resumeAfterUnwindError k) c eq valid with lookup k (Pool.handles c) in found
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl →
  write-preserves c k Pool.bodyUnwinding Pool.bodyRunning found (λ _ ()) valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-preserves (Pool.deregister k) c eq valid with lookup k (Pool.handles c) in found | Pool.member k (Pool.registered c)
... | just (Pool.deregisterPending exit) | true = case just-injective eq of λ { refl →
  write-preserves c k (Pool.deregisterPending exit) (Pool.deregistered exit) found (λ _ ()) valid }
... | nothing | _ = case eq of λ ()
... | just (Pool.deregisterPending exit) | false = case eq of λ ()
... | just Pool.bodyRunning | _ = case eq of λ ()
... | just (Pool.bodyReturned value) | _ = case eq of λ ()
... | just Pool.bodyUnwinding | _ = case eq of λ ()
... | just (Pool.deregistered ex) | _ = case eq of λ ()
... | just (Pool.resultAvailable ex) | _ = case eq of λ ()
step-preserves (Pool.publishAsyncResult k) c eq valid with lookup k (Pool.handles c) in found
... | just (Pool.deregistered exit) = case just-injective eq of λ { refl →
  write-preserves c k (Pool.deregistered exit) (Pool.resultAvailable exit) found (λ _ ()) valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-preserves (Pool.beginClose order) c eq valid with Pool.phase c | Pool.parentFork c | Pool.sameSnapshot order (Pool.registered c)
... | Pool.openPool | nothing | true = case just-injective eq of λ { refl → λ j member → inj₁ member }
... | Pool.closing | _ | _ = case eq of λ ()
... | Pool.closedPool | _ | _ = case eq of λ ()
... | (Pool.cancelPending k₁) | _ | _ = case eq of λ ()
... | (Pool.joinPending k₁) | _ | _ = case eq of λ ()
... | Pool.openPool | just pending | _ = case eq of λ ()
... | Pool.openPool | nothing | false = case eq of λ ()
step-preserves Pool.requestCancel c eq valid with Pool.phase c | Pool.remaining c in restEq
... | Pool.closing | k ∷ rest with lookup k (Pool.handles c)
...   | nothing = case eq of λ ()
...   | just (Pool.resultAvailable exit) = case just-injective eq of λ { refl → restore-covered c (k ∷ rest) restEq valid }
...   | just Pool.bodyRunning = case just-injective eq of λ { refl → restore-covered c (k ∷ rest) restEq valid }
...   | just (Pool.bodyReturned result) = case just-injective eq of λ { refl → restore-covered c (k ∷ rest) restEq valid }
...   | just Pool.bodyUnwinding = case just-injective eq of λ { refl → restore-covered c (k ∷ rest) restEq valid }
...   | just (Pool.deregisterPending exit) = case just-injective eq of λ { refl → restore-covered c (k ∷ rest) restEq valid }
...   | just (Pool.deregistered exit) = case just-injective eq of λ { refl → restore-covered c (k ∷ rest) restEq valid }
step-preserves Pool.requestCancel c eq valid | Pool.openPool | _ = case eq of λ ()
step-preserves Pool.requestCancel c eq valid | Pool.closedPool | _ = case eq of λ ()
step-preserves Pool.requestCancel c eq valid | (Pool.cancelPending k₁) | _ = case eq of λ ()
step-preserves Pool.requestCancel c eq valid | (Pool.joinPending k₁) | _ = case eq of λ ()
step-preserves Pool.requestCancel c eq valid | Pool.closing | [] = case eq of λ ()
step-preserves Pool.deliverCancel c eq valid with Pool.phase c
... | Pool.cancelPending k with lookup k (Pool.handles c) in found
...   | just Pool.bodyRunning = case just-injective eq of λ { refl →
  write-preserves c k Pool.bodyRunning Pool.bodyUnwinding found (λ _ ()) valid }
...   | nothing = case eq of λ ()
...   | just (Pool.bodyReturned value) = case eq of λ ()
...   | just Pool.bodyUnwinding = case eq of λ ()
...   | just (Pool.deregisterPending ex) = case eq of λ ()
...   | just (Pool.deregistered ex) = case eq of λ ()
...   | just (Pool.resultAvailable ex) = case eq of λ ()
step-preserves Pool.deliverCancel c eq valid | Pool.openPool = case eq of λ ()
step-preserves Pool.deliverCancel c eq valid | Pool.closing = case eq of λ ()
step-preserves Pool.deliverCancel c eq valid | Pool.closedPool = case eq of λ ()
step-preserves Pool.deliverCancel c eq valid | (Pool.joinPending k₁) = case eq of λ ()
step-preserves Pool.join c eq valid with Pool.phase c
... | Pool.cancelPending k = join-preserves k c eq valid
... | Pool.joinPending k = join-preserves k c eq valid
... | Pool.openPool = case eq of λ ()
... | Pool.closing = case eq of λ ()
... | Pool.closedPool = case eq of λ ()
step-preserves Pool.finishClose c eq valid with Pool.phase c | Pool.remaining c in restEq
... | Pool.closing | [] = case just-injective eq of λ { refl → restore-covered c [] restEq valid }
... | Pool.openPool | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | (Pool.cancelPending k₁) | _ = case eq of λ ()
... | (Pool.joinPending k₁) | _ = case eq of λ ()
... | Pool.closing | _ ∷ _ = case eq of λ ()

-- The real empty initializer carries no forged historical join certificate.
initial-covered : Covered Pool.initial
initial-covered j ()

-- Arbitrary finite interleavings retain every captured member's coverage.
exec-preserves : ∀ {c actions c′} → Pool.Executes c actions c′ → Covered c → Covered c′
exec-preserves Pool.done valid = valid
exec-preserves (Pool.next {s = c} {a = a} eq path) valid =
  exec-preserves path (step-preserves a c eq valid)

-- Joining always returns to the nonterminal closing cursor.
join-empty : ∀ current c {c′} → Pool.joinHead current c ≡ just c′ → ClosedEmpty c′
join-empty current c eq with Pool.remaining c | lookup current (Pool.handles c)
... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
...   | yes _ = case just-injective eq of λ { refl → λ () }
...   | no _ = case eq of λ ()
join-empty current c eq | [] | _ = case eq of λ ()
join-empty current c eq | _ ∷ _ | nothing = case eq of λ ()
join-empty current c eq | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
join-empty current c eq | _ ∷ _ | just (Pool.bodyReturned _) = case eq of λ ()
join-empty current c eq | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
join-empty current c eq | _ ∷ _ | just (Pool.deregisterPending _) = case eq of λ ()
join-empty current c eq | _ ∷ _ | just (Pool.deregistered _) = case eq of λ ()

-- Finish is the sole transition into closedPool, and requires an empty cursor.
step-empty : ∀ a c {c′} → Pool.step a c ≡ just c′ → ClosedEmpty c → ClosedEmpty c′
step-empty (Pool.fork k) c eq valid with Pool.phase c in phaseEq | Pool.parentFork c | lookup k (Pool.handles c)
... | Pool.openPool | nothing | nothing = case just-injective eq of λ { refl → λ closed → case trans (sym phaseEq) closed of λ () }
... | Pool.closing | _ | _ = case eq of λ ()
... | Pool.closedPool | _ | _ = case eq of λ ()
... | Pool.cancelPending pending | _ | _ = case eq of λ ()
... | Pool.joinPending pending | _ | _ = case eq of λ ()
... | Pool.openPool | just pending | _ = case eq of λ ()
... | Pool.openPool | nothing | just old = case eq of λ ()
step-empty Pool.register c eq valid with Pool.phase c in phaseEq | Pool.parentFork c
... | Pool.openPool | just k with Pool.member k (Pool.registered c)
...   | false = case just-injective eq of λ { refl → λ closed → case trans (sym phaseEq) closed of λ () }
...   | true = case eq of λ ()
step-empty Pool.register c eq valid | Pool.closing | _ = case eq of λ ()
step-empty Pool.register c eq valid | Pool.closedPool | _ = case eq of λ ()
step-empty Pool.register c eq valid | (Pool.cancelPending k₁) | _ = case eq of λ ()
step-empty Pool.register c eq valid | (Pool.joinPending k₁) | _ = case eq of λ ()
step-empty Pool.register c eq valid | Pool.openPool | nothing = case eq of λ ()
step-empty (Pool.bodyReturnedWith k result) c eq valid with lookup k (Pool.handles c)
... | just Pool.bodyRunning = case just-injective eq of λ { refl → valid }
... | nothing = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-empty (Pool.publishCompletion k) c eq valid = publish-empty queued k c eq valid
step-empty (Pool.bodyUnwound k) c eq valid with lookup k (Pool.handles c)
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-empty (Pool.resumeAfterUnwindError k) c eq valid with lookup k (Pool.handles c)
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-empty (Pool.deregister k) c eq valid with lookup k (Pool.handles c) | Pool.member k (Pool.registered c)
... | just (Pool.deregisterPending exit) | true = case just-injective eq of λ { refl → valid }
... | nothing | _ = case eq of λ ()
... | just (Pool.deregisterPending exit) | false = case eq of λ ()
... | just Pool.bodyRunning | _ = case eq of λ ()
... | just (Pool.bodyReturned value) | _ = case eq of λ ()
... | just Pool.bodyUnwinding | _ = case eq of λ ()
... | just (Pool.deregistered ex) | _ = case eq of λ ()
... | just (Pool.resultAvailable ex) | _ = case eq of λ ()
step-empty (Pool.publishAsyncResult k) c eq valid with lookup k (Pool.handles c)
... | just (Pool.deregistered exit) = case just-injective eq of λ { refl → valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-empty (Pool.beginClose order) c eq valid with Pool.phase c | Pool.parentFork c | Pool.sameSnapshot order (Pool.registered c)
... | Pool.openPool | nothing | true = case just-injective eq of λ { refl → λ () }
... | Pool.closing | _ | _ = case eq of λ ()
... | Pool.closedPool | _ | _ = case eq of λ ()
... | (Pool.cancelPending k₁) | _ | _ = case eq of λ ()
... | (Pool.joinPending k₁) | _ | _ = case eq of λ ()
... | Pool.openPool | just pending | _ = case eq of λ ()
... | Pool.openPool | nothing | false = case eq of λ ()
step-empty Pool.requestCancel c eq valid with Pool.phase c | Pool.remaining c
... | Pool.closing | k ∷ rest with lookup k (Pool.handles c)
...   | nothing = case eq of λ ()
...   | just (Pool.resultAvailable exit) = case just-injective eq of λ { refl → λ () }
...   | just Pool.bodyRunning = case just-injective eq of λ { refl → λ () }
...   | just (Pool.bodyReturned result) = case just-injective eq of λ { refl → λ () }
...   | just Pool.bodyUnwinding = case just-injective eq of λ { refl → λ () }
...   | just (Pool.deregisterPending exit) = case just-injective eq of λ { refl → λ () }
...   | just (Pool.deregistered exit) = case just-injective eq of λ { refl → λ () }
step-empty Pool.requestCancel c eq valid | Pool.openPool | _ = case eq of λ ()
step-empty Pool.requestCancel c eq valid | Pool.closedPool | _ = case eq of λ ()
step-empty Pool.requestCancel c eq valid | (Pool.cancelPending k₁) | _ = case eq of λ ()
step-empty Pool.requestCancel c eq valid | (Pool.joinPending k₁) | _ = case eq of λ ()
step-empty Pool.requestCancel c eq valid | Pool.closing | [] = case eq of λ ()
step-empty Pool.deliverCancel c eq valid with Pool.phase c
... | Pool.cancelPending k with lookup k (Pool.handles c)
...   | just Pool.bodyRunning = case just-injective eq of λ { refl → λ () }
...   | nothing = case eq of λ ()
...   | just (Pool.bodyReturned value) = case eq of λ ()
...   | just Pool.bodyUnwinding = case eq of λ ()
...   | just (Pool.deregisterPending ex) = case eq of λ ()
...   | just (Pool.deregistered ex) = case eq of λ ()
...   | just (Pool.resultAvailable ex) = case eq of λ ()
step-empty Pool.deliverCancel c eq valid | Pool.openPool = case eq of λ ()
step-empty Pool.deliverCancel c eq valid | Pool.closing = case eq of λ ()
step-empty Pool.deliverCancel c eq valid | Pool.closedPool = case eq of λ ()
step-empty Pool.deliverCancel c eq valid | (Pool.joinPending k₁) = case eq of λ ()
step-empty Pool.join c eq valid with Pool.phase c
... | Pool.cancelPending k = join-empty k c eq
... | Pool.joinPending k = join-empty k c eq
... | Pool.openPool = case eq of λ ()
... | Pool.closing = case eq of λ ()
... | Pool.closedPool = case eq of λ ()
step-empty Pool.finishClose c eq valid with Pool.phase c | Pool.remaining c in restEq
... | Pool.closing | [] = case just-injective eq of λ { refl → λ _ → restEq }
... | Pool.openPool | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | (Pool.cancelPending k₁) | _ = case eq of λ ()
... | (Pool.joinPending k₁) | _ = case eq of λ ()
... | Pool.closing | _ ∷ _ = case eq of λ ()

-- The empty-cursor invariant is independent of any thread-result premise.
exec-empty : ∀ {c actions c′} → Pool.Executes c actions c′ → ClosedEmpty c → ClosedEmpty c′
exec-empty Pool.done valid = valid
exec-empty (Pool.next {s = c} {a = a} eq path) valid =
  exec-empty path (step-empty a c eq valid)

-- In the completed close, no snapshot member remains on the pending cursor.
closed-results : ∀ c → Pool.remaining c ≡ [] → Covered c →
  ∀ j → j ∈ Pool.snapshot c → Terminal c j
closed-results c empty valid j member with valid j member
... | inj₂ terminal = terminal
... | inj₁ pending = case subst (λ xs → j ∈ xs) empty pending of λ ()

-- This is a snapshot safety theorem, conditional on the actual finite run.
-- It asserts neither eventual closure nor results for removed historical jobs.
from-initial : ∀ {actions c} → Pool.Executes Pool.initial actions c →
  Pool.phase c ≡ Pool.closedPool → ∀ j → j ∈ Pool.snapshot c → Terminal c j
from-initial {c = c} path closed = closed-results c
  (exec-empty path (λ ()) closed) (exec-preserves path initial-covered)

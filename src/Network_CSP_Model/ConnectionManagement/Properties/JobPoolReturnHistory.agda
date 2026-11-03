{-# OPTIONS --guardedness #-}

-- Actual body-return history in the WithQueue lifecycle, independent of Async
-- availability and of the integrating governor's source completion queue.
module ConnectionManagement.Properties.JobPoolReturnHistory (Result : Set) where
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (JobId)
open import ConnectionManagement.Store using (put; lookup)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.Rules.JobPoolKernel as Lifecycle
private module Pool = Lifecycle Result true

-- Every handle change is either quiet, non-returning, or the exact actual
-- bodyReturnedWith operation; none of the other operations can forge that phase.
data HandleEffect : Pool.Action → Pool.State → Pool.State → Set where
 h-quiet : ∀ {a c d} → Pool.handles d ≡ Pool.handles c → HandleEffect a c d
 h-write : ∀ {a c d} k phase → (∀ value → phase ≢ Pool.bodyReturned value) →
   Pool.handles d ≡ put k phase (Pool.handles c) → HandleEffect a c d
 h-return : ∀ {c d} k value → Pool.handles d ≡ put k (Pool.bodyReturned value) (Pool.handles c) →
   HandleEffect (Pool.bodyReturnedWith k value) c d
publish-handles : ∀ k c {d} → Pool.publishQueued true k c ≡ just d → HandleEffect (Pool.publishCompletion k) c d
publish-handles k c eq with lookup k (Pool.handles c) in found
... | just (Pool.bodyReturned result) = case just-injective eq of λ { refl → h-write k (Pool.deregisterPending Pool.normalExit) (λ _ ()) refl }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()

-- Queue consumption leaves the historical handle table intact.
consume-handles : ∀ c {d} → Pool.consumeQueued true c ≡ just d → HandleEffect Pool.consumeCompletion c d
consume-handles c eq with Pool.phase c | Pool.completions c
... | Pool.openPool | x ∷ xs = case just-injective eq of λ { refl → h-quiet refl }
... | Pool.openPool | [] = case eq of λ ()
... | Pool.closing | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | Pool.cancelPending _ | _ = case eq of λ ()
... | Pool.joinPending _ | _ = case eq of λ ()
join-handles : ∀ current c {d} → Pool.joinHead current c ≡ just d → HandleEffect Pool.join c d
join-handles current c eq with Pool.remaining c | lookup current (Pool.handles c)
... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
...   | no _ = case eq of λ ()
...   | yes refl = case just-injective eq of λ { refl → h-quiet refl }
join-handles current c eq | [] | _ = case eq of λ ()
join-handles current c eq | _ ∷ _ | nothing = case eq of λ ()
join-handles current c eq | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
join-handles current c eq | _ ∷ _ | just (Pool.bodyReturned _) = case eq of λ ()
join-handles current c eq | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
join-handles current c eq | _ ∷ _ | just (Pool.deregisterPending _) = case eq of λ ()
join-handles current c eq | _ ∷ _ | just (Pool.deregistered _) = case eq of λ ()
handle-effect : ∀ a c {d} → Pool.step a c ≡ just d → HandleEffect a c d
handle-effect (Pool.fork k) c eq with Pool.phase c | Pool.parentFork c | lookup k (Pool.handles c) in absent
... | Pool.openPool | nothing | nothing with just-injective eq
...   | refl = h-write k Pool.bodyRunning (λ _ ()) refl
handle-effect (Pool.fork k) c eq | Pool.closing | _ | _ = case eq of λ ()
handle-effect (Pool.fork k) c eq | Pool.closedPool | _ | _ = case eq of λ ()
handle-effect (Pool.fork k) c eq | (Pool.cancelPending k₁) | _ | _ = case eq of λ ()
handle-effect (Pool.fork k) c eq | (Pool.joinPending k₁) | _ | _ = case eq of λ ()
handle-effect (Pool.fork k) c eq | Pool.openPool | just pending | _ = case eq of λ ()
handle-effect (Pool.fork k) c eq | Pool.openPool | nothing | just old = case eq of λ ()
handle-effect (Pool.forkConcurrent k) c eq = case eq of λ ()
handle-effect (Pool.registerConcurrent k) c eq = case eq of λ ()
handle-effect Pool.register c eq with Pool.phase c | Pool.parentFork c
... | Pool.openPool | just k with Pool.member k (Pool.registered c)
...   | false = case just-injective eq of λ { refl → h-quiet refl }
...   | true = case eq of λ ()
handle-effect Pool.register c eq | Pool.closing | _ = case eq of λ ()
handle-effect Pool.register c eq | Pool.closedPool | _ = case eq of λ ()
handle-effect Pool.register c eq | (Pool.cancelPending k₁) | _ = case eq of λ ()
handle-effect Pool.register c eq | (Pool.joinPending k₁) | _ = case eq of λ ()
handle-effect Pool.register c eq | Pool.openPool | nothing = case eq of λ ()
handle-effect (Pool.bodyReturnedWith k result) c eq with lookup k (Pool.handles c) in found
... | just Pool.bodyRunning = case just-injective eq of λ { refl → h-return k result refl }
... | nothing = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
handle-effect (Pool.publishCompletion k) c eq = publish-handles k c eq
handle-effect Pool.consumeCompletion c eq = consume-handles c eq
handle-effect (Pool.interruptJob k) c eq with Pool.phase c | lookup k (Pool.handles c) in found
... | Pool.openPool | just Pool.bodyRunning = case just-injective eq of λ { refl → h-write k Pool.bodyUnwinding (λ _ ()) refl }
... | Pool.closing | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | Pool.cancelPending j | _ = case eq of λ ()
... | Pool.joinPending j | _ = case eq of λ ()
... | Pool.openPool | nothing = case eq of λ ()
... | Pool.openPool | just (Pool.bodyReturned value) = case eq of λ ()
... | Pool.openPool | just Pool.bodyUnwinding = case eq of λ ()
... | Pool.openPool | just (Pool.deregisterPending ex) = case eq of λ ()
... | Pool.openPool | just (Pool.deregistered ex) = case eq of λ ()
... | Pool.openPool | just (Pool.resultAvailable ex) = case eq of λ ()
handle-effect (Pool.bodyUnwound k) c eq with lookup k (Pool.handles c) in found
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → h-write k (Pool.deregisterPending Pool.cancelledExit) (λ _ ()) refl }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
handle-effect (Pool.resumeAfterUnwindError k) c eq with lookup k (Pool.handles c) in found
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → h-write k Pool.bodyRunning (λ _ ()) refl }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
handle-effect (Pool.deregister k) c eq with lookup k (Pool.handles c) in found | Pool.member k (Pool.registered c)
... | just (Pool.deregisterPending exit) | true = case just-injective eq of λ { refl → h-write k (Pool.deregistered exit) (λ _ ()) refl }
... | nothing | _ = case eq of λ ()
... | just (Pool.deregisterPending exit) | false = case eq of λ ()
... | just Pool.bodyRunning | _ = case eq of λ ()
... | just (Pool.bodyReturned value) | _ = case eq of λ ()
... | just Pool.bodyUnwinding | _ = case eq of λ ()
... | just (Pool.deregistered ex) | _ = case eq of λ ()
... | just (Pool.resultAvailable ex) | _ = case eq of λ ()
handle-effect (Pool.publishAsyncResult k) c eq with lookup k (Pool.handles c) in found
... | just (Pool.deregistered exit) = case just-injective eq of λ { refl → h-write k (Pool.resultAvailable exit) (λ _ ()) refl }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
handle-effect (Pool.beginClose order) c eq with Pool.phase c | Pool.parentFork c | Pool.canSnapshot true order c
... | Pool.openPool | nothing | true = case just-injective eq of λ { refl → h-quiet refl }
... | Pool.closing | _ | _ = case eq of λ ()
... | Pool.closedPool | _ | _ = case eq of λ ()
... | (Pool.cancelPending k₁) | _ | _ = case eq of λ ()
... | (Pool.joinPending k₁) | _ | _ = case eq of λ ()
... | Pool.openPool | just pending | _ = case eq of λ ()
... | Pool.openPool | nothing | false = case eq of λ ()
handle-effect Pool.requestCancel c eq with Pool.phase c | Pool.remaining c in restEq
... | Pool.closing | k ∷ rest with lookup k (Pool.handles c)
...   | nothing = case eq of λ ()
...   | just (Pool.resultAvailable exit) = case just-injective eq of λ { refl → h-quiet refl }
...   | just Pool.bodyRunning = case just-injective eq of λ { refl → h-quiet refl }
...   | just (Pool.bodyReturned result) = case just-injective eq of λ { refl → h-quiet refl }
...   | just Pool.bodyUnwinding = case just-injective eq of λ { refl → h-quiet refl }
...   | just (Pool.deregisterPending exit) = case just-injective eq of λ { refl → h-quiet refl }
...   | just (Pool.deregistered exit) = case just-injective eq of λ { refl → h-quiet refl }
handle-effect Pool.requestCancel c eq | Pool.openPool | _ = case eq of λ ()
handle-effect Pool.requestCancel c eq | Pool.closedPool | _ = case eq of λ ()
handle-effect Pool.requestCancel c eq | (Pool.cancelPending k₁) | _ = case eq of λ ()
handle-effect Pool.requestCancel c eq | (Pool.joinPending k₁) | _ = case eq of λ ()
handle-effect Pool.requestCancel c eq | Pool.closing | [] = case eq of λ ()
handle-effect Pool.deliverCancel c eq with Pool.phase c
... | Pool.cancelPending k with lookup k (Pool.handles c) in found
...   | just Pool.bodyRunning = case just-injective eq of λ { refl → h-write k Pool.bodyUnwinding (λ _ ()) refl }
...   | nothing = case eq of λ ()
...   | just (Pool.bodyReturned value) = case eq of λ ()
...   | just Pool.bodyUnwinding = case eq of λ ()
...   | just (Pool.deregisterPending ex) = case eq of λ ()
...   | just (Pool.deregistered ex) = case eq of λ ()
...   | just (Pool.resultAvailable ex) = case eq of λ ()
handle-effect Pool.deliverCancel c eq | Pool.openPool = case eq of λ ()
handle-effect Pool.deliverCancel c eq | Pool.closing = case eq of λ ()
handle-effect Pool.deliverCancel c eq | Pool.closedPool = case eq of λ ()
handle-effect Pool.deliverCancel c eq | (Pool.joinPending k₁) = case eq of λ ()
handle-effect Pool.join c eq with Pool.phase c
... | Pool.cancelPending k = join-handles k c eq
... | Pool.joinPending k = join-handles k c eq
... | Pool.openPool = case eq of λ ()
... | Pool.closing = case eq of λ ()
... | Pool.closedPool = case eq of λ ()
handle-effect Pool.finishClose c eq with Pool.phase c | Pool.remaining c in restEq
... | Pool.closing | [] = case just-injective eq of λ { refl → h-quiet refl }
... | Pool.openPool | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | (Pool.cancelPending k₁) | _ = case eq of λ ()
... | (Pool.joinPending k₁) | _ = case eq of λ ()
... | Pool.closing | _ ∷ _ = case eq of λ ()



-- A return is anchored in a real prefix from the given initial pool, then
-- retained through the actual following primitive transitions.
data Returned (start : Pool.State) (j : JobId) (value : Result) : Pool.State → Set where
 at-return : ∀ {actions c d} → Pool.Executes start actions c →
   Pool.step (Pool.bodyReturnedWith j value) c ≡ just d → Returned start j value d
 after-step : ∀ {a c d} → Returned start j value c → Pool.step a c ≡ just d → Returned start j value d
Backed : Pool.State → Pool.State → Set
Backed start current = ∀ j value → lookup j (Pool.handles current) ≡ just (Pool.bodyReturned value) → Returned start j value current
append : ∀ {start xs middle ys end} → Pool.Executes start xs middle → Pool.Executes middle ys end → Pool.Executes start (xs ++ ys) end
append Pool.done right = right
append (Pool.next eq left) right = Pool.next eq (append left right)
return-injective : ∀ {a b} → Pool.bodyReturned a ≡ Pool.bodyReturned b → a ≡ b
return-injective refl = refl

-- The write classifier excludes all non-return phases for the observed key.
-- Writes to other keys transport the exact old body and its return history.
step-backed : ∀ {start prefix c d} a → Pool.Executes start prefix c → Pool.step a c ≡ just d → Backed start c → Backed start d
step-backed {c = c} {d} a prefix stepped backed j value observed with handle-effect a c stepped
... | h-quiet same = after-step {a = a} (backed j value (trans (sym (cong (lookup j) same)) observed)) stepped
... | h-write k phase other same with j ≟ k
...   | no apart = after-step {a = a} (backed j value (trans (sym (lookup-put-other k j phase (Pool.handles c) apart))
      (trans (sym (cong (lookup j) same)) observed))) stepped
...   | yes refl = ⊥-elim (other value (just-injective (trans (sym (lookup-put k phase (Pool.handles c)))
      (trans (sym (cong (lookup k) same)) observed))))
step-backed {c = c} a prefix stepped backed j value observed | h-return k result same with j ≟ k
... | no apart = after-step {a = a} (backed j value (trans (sym (lookup-put-other k j (Pool.bodyReturned result) (Pool.handles c) apart))
    (trans (sym (cong (lookup j) same)) observed))) stepped
... | yes refl with return-injective (just-injective (trans (sym (lookup-put k (Pool.bodyReturned result) (Pool.handles c)))
    (trans (sym (cong (lookup k) same)) observed)))
...   | refl = at-return prefix stepped
run-backed : ∀ {start prefix c suffix d} → Pool.Executes start prefix c → Backed start c → Pool.Executes c suffix d → Backed start d
run-backed prefix backed Pool.done = backed
run-backed prefix backed (Pool.next {a = a} eq rest) = run-backed (append prefix (Pool.next {a = a} eq Pool.done)) (step-backed a prefix eq backed) rest
from-initial : ∀ {actions current} → Pool.Executes Pool.initial actions current → Backed Pool.initial current
from-initial path = run-backed Pool.done (λ j value ()) path

-- Historical handles persist even after queue publication or Async completion.
Present : JobId → Pool.State → Set
Present j c = Σ Pool.ThreadPhase (λ phase → lookup j (Pool.handles c) ≡ just phase)
put-present : ∀ j k phase c {d} → Pool.handles d ≡ put k phase (Pool.handles c) → Present j c → Present j d
put-present j k phase c same (old , found) with j ≟ k
... | yes refl = phase , trans (cong (lookup k) same) (lookup-put k phase (Pool.handles c))
... | no apart = old , trans (cong (lookup j) same) (trans (lookup-put-other k j phase (Pool.handles c) apart) found)
step-present : ∀ a c {d} j → Pool.step a c ≡ just d → Present j c → Present j d
step-present a c {d} j stepped present with handle-effect a c stepped
... | h-quiet same = case present of λ { (phase , found) → phase , trans (cong (lookup j) same) found }
... | h-write k phase other same = put-present j k phase c {d = d} same present
... | h-return k value same = put-present j k (Pool.bodyReturned value) c {d = d} same present
return-present : ∀ j value c {d} → Pool.step (Pool.bodyReturnedWith j value) c ≡ just d → Present j d
return-present j value c eq with lookup j (Pool.handles c)
... | just Pool.bodyRunning = case just-injective eq of λ { refl → Pool.bodyReturned value , lookup-put j (Pool.bodyReturned value) (Pool.handles c) }
... | nothing = case eq of λ ()
... | just (Pool.bodyReturned _) = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending _) = case eq of λ ()
... | just (Pool.deregistered _) = case eq of λ ()
... | just (Pool.resultAvailable _) = case eq of λ ()
returned-present : ∀ {start j value c} → Returned start j value c → Present j c
returned-present {j = j} {value = value} (at-return {c = c} prefix stepped) = return-present j value c stepped
returned-present {j = j} (after-step {a = a} {c = c} history stepped) = step-present a c j stepped (returned-present history)
extend : ∀ {start j value c actions d} → Pool.Executes c actions d → Returned start j value c → Returned start j value d
extend Pool.done history = history
extend (Pool.next {a = a} stepped rest) history = extend rest (after-step {a = a} history stepped)

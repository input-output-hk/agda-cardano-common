{-# OPTIONS --guardedness #-}

-- Payload preservation for every queued-pool primitive. New return values need
-- writer evidence; publication uses the old returned-body certificate.
module ConnectionManagement.Properties.LiveTrackerPoolContent (Result : Set) where
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Relation.Unary.All as All using (All; []; _∷_)
open import Data.List.Relation.Unary.All.Properties using (++⁺)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (JobId)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (Present; lookup-put; put-preserves-present)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.Rules.JobPoolKernel as Kernel
module Pool = Kernel Result true
import ConnectionManagement.Properties.JobPoolReturnHistory as History
module H = History Result

record Content (C : Result → Set) (p : Pool.State) : Set where
 field queued : All C (Pool.completions p)
       returned : ∀ j value → lookup j (Pool.handles p) ≡ just (Pool.bodyReturned value) → C value

-- All queue writes are either append of an actual body result or FIFO pop.
data QueueEffect (c d : Pool.State) : Set where
 quiet : Pool.completions d ≡ Pool.completions c → QueueEffect c d
 append : ∀ j value → lookup j (Pool.handles c) ≡ just (Pool.bodyReturned value) →
   Pool.completions d ≡ Pool.completions c ++ (value ∷ []) → QueueEffect c d
 pop : ∀ value rest → Pool.completions c ≡ value ∷ rest → Pool.completions d ≡ rest → QueueEffect c d
publish-queue : ∀ k c {d} → Pool.step (Pool.publishCompletion k) c ≡ just d → QueueEffect c d
publish-queue k c eq with lookup k (Pool.handles c) in found
... | just (Pool.bodyReturned value) = case just-injective eq of λ { refl → append k value found refl }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending _) = case eq of λ ()
... | just (Pool.deregistered _) = case eq of λ ()
... | just (Pool.resultAvailable _) = case eq of λ ()
consume-queue : ∀ c {d} → Pool.step Pool.consumeCompletion c ≡ just d → QueueEffect c d
consume-queue c eq with Pool.phase c | Pool.completions c in queue
... | Pool.openPool | value ∷ rest = case just-injective eq of λ { refl → pop value rest queue refl }
... | Pool.openPool | [] = case eq of λ ()
... | Pool.closing | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | Pool.cancelPending _ | _ = case eq of λ ()
... | Pool.joinPending _ | _ = case eq of λ ()
join-queue : ∀ current c {d} → Pool.joinHead current c ≡ just d → QueueEffect c d
join-queue current c eq with Pool.remaining c | lookup current (Pool.handles c)
... | head ∷ rest | just (Pool.resultAvailable exit) with current ≟ head
...   | no _ = case eq of λ ()
...   | yes refl = case just-injective eq of λ { refl → quiet refl }
join-queue current c eq | [] | _ = case eq of λ ()
join-queue current c eq | _ ∷ _ | nothing = case eq of λ ()
join-queue current c eq | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
join-queue current c eq | _ ∷ _ | just (Pool.bodyReturned _) = case eq of λ ()
join-queue current c eq | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
join-queue current c eq | _ ∷ _ | just (Pool.deregisterPending _) = case eq of λ ()
join-queue current c eq | _ ∷ _ | just (Pool.deregistered _) = case eq of λ ()
queue-effect : ∀ a c {d} → Pool.step a c ≡ just d → QueueEffect c d
queue-effect (Pool.fork k) c eq with Pool.phase c | Pool.parentFork c | lookup k (Pool.handles c) in absent
... | Pool.openPool | nothing | nothing with just-injective eq
...   | refl = quiet refl
queue-effect (Pool.fork k) c eq | Pool.closing | _ | _ = case eq of λ ()
queue-effect (Pool.fork k) c eq | Pool.closedPool | _ | _ = case eq of λ ()
queue-effect (Pool.fork k) c eq | (Pool.cancelPending k₁) | _ | _ = case eq of λ ()
queue-effect (Pool.fork k) c eq | (Pool.joinPending k₁) | _ | _ = case eq of λ ()
queue-effect (Pool.fork k) c eq | Pool.openPool | just pending | _ = case eq of λ ()
queue-effect (Pool.fork k) c eq | Pool.openPool | nothing | just old = case eq of λ ()
queue-effect (Pool.forkConcurrent k) c eq = case eq of λ ()
queue-effect (Pool.registerConcurrent k) c eq = case eq of λ ()
queue-effect Pool.register c eq with Pool.phase c | Pool.parentFork c
... | Pool.openPool | just k with Pool.member k (Pool.registered c)
...   | false = case just-injective eq of λ { refl → quiet refl }
...   | true = case eq of λ ()
queue-effect Pool.register c eq | Pool.closing | _ = case eq of λ ()
queue-effect Pool.register c eq | Pool.closedPool | _ = case eq of λ ()
queue-effect Pool.register c eq | (Pool.cancelPending k₁) | _ = case eq of λ ()
queue-effect Pool.register c eq | (Pool.joinPending k₁) | _ = case eq of λ ()
queue-effect Pool.register c eq | Pool.openPool | nothing = case eq of λ ()
queue-effect (Pool.bodyReturnedWith k result) c eq with lookup k (Pool.handles c) in found
... | just Pool.bodyRunning = case just-injective eq of λ { refl → quiet refl }
... | nothing = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
queue-effect (Pool.publishCompletion k) c eq = publish-queue k c eq
queue-effect Pool.consumeCompletion c eq = consume-queue c eq
queue-effect (Pool.interruptJob k) c eq with Pool.phase c | lookup k (Pool.handles c) in found
... | Pool.openPool | just Pool.bodyRunning = case just-injective eq of λ { refl → quiet refl }
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
queue-effect (Pool.bodyUnwound k) c eq with lookup k (Pool.handles c) in found
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → quiet refl }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
queue-effect (Pool.resumeAfterUnwindError k) c eq with lookup k (Pool.handles c) in found
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → quiet refl }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
queue-effect (Pool.deregister k) c eq with lookup k (Pool.handles c) in found | Pool.member k (Pool.registered c)
... | just (Pool.deregisterPending exit) | true = case just-injective eq of λ { refl → quiet refl }
... | nothing | _ = case eq of λ ()
... | just (Pool.deregisterPending exit) | false = case eq of λ ()
... | just Pool.bodyRunning | _ = case eq of λ ()
... | just (Pool.bodyReturned value) | _ = case eq of λ ()
... | just Pool.bodyUnwinding | _ = case eq of λ ()
... | just (Pool.deregistered ex) | _ = case eq of λ ()
... | just (Pool.resultAvailable ex) | _ = case eq of λ ()
queue-effect (Pool.publishAsyncResult k) c eq with lookup k (Pool.handles c) in found
... | just (Pool.deregistered exit) = case just-injective eq of λ { refl → quiet refl }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
queue-effect (Pool.beginClose order) c eq with Pool.phase c | Pool.parentFork c | Pool.canSnapshot true order c
... | Pool.openPool | nothing | true = case just-injective eq of λ { refl → quiet refl }
... | Pool.closing | _ | _ = case eq of λ ()
... | Pool.closedPool | _ | _ = case eq of λ ()
... | (Pool.cancelPending k₁) | _ | _ = case eq of λ ()
... | (Pool.joinPending k₁) | _ | _ = case eq of λ ()
... | Pool.openPool | just pending | _ = case eq of λ ()
... | Pool.openPool | nothing | false = case eq of λ ()
queue-effect Pool.requestCancel c eq with Pool.phase c | Pool.remaining c in restEq
... | Pool.closing | k ∷ rest with lookup k (Pool.handles c)
...   | nothing = case eq of λ ()
...   | just (Pool.resultAvailable exit) = case just-injective eq of λ { refl → quiet refl }
...   | just Pool.bodyRunning = case just-injective eq of λ { refl → quiet refl }
...   | just (Pool.bodyReturned result) = case just-injective eq of λ { refl → quiet refl }
...   | just Pool.bodyUnwinding = case just-injective eq of λ { refl → quiet refl }
...   | just (Pool.deregisterPending exit) = case just-injective eq of λ { refl → quiet refl }
...   | just (Pool.deregistered exit) = case just-injective eq of λ { refl → quiet refl }
queue-effect Pool.requestCancel c eq | Pool.openPool | _ = case eq of λ ()
queue-effect Pool.requestCancel c eq | Pool.closedPool | _ = case eq of λ ()
queue-effect Pool.requestCancel c eq | (Pool.cancelPending k₁) | _ = case eq of λ ()
queue-effect Pool.requestCancel c eq | (Pool.joinPending k₁) | _ = case eq of λ ()
queue-effect Pool.requestCancel c eq | Pool.closing | [] = case eq of λ ()
queue-effect Pool.deliverCancel c eq with Pool.phase c
... | Pool.cancelPending k with lookup k (Pool.handles c) in found
...   | just Pool.bodyRunning = case just-injective eq of λ { refl → quiet refl }
...   | nothing = case eq of λ ()
...   | just (Pool.bodyReturned value) = case eq of λ ()
...   | just Pool.bodyUnwinding = case eq of λ ()
...   | just (Pool.deregisterPending ex) = case eq of λ ()
...   | just (Pool.deregistered ex) = case eq of λ ()
...   | just (Pool.resultAvailable ex) = case eq of λ ()
queue-effect Pool.deliverCancel c eq | Pool.openPool = case eq of λ ()
queue-effect Pool.deliverCancel c eq | Pool.closing = case eq of λ ()
queue-effect Pool.deliverCancel c eq | Pool.closedPool = case eq of λ ()
queue-effect Pool.deliverCancel c eq | (Pool.joinPending k₁) = case eq of λ ()
queue-effect Pool.join c eq with Pool.phase c
... | Pool.cancelPending k = join-queue k c eq
... | Pool.joinPending k = join-queue k c eq
... | Pool.openPool = case eq of λ ()
... | Pool.closing = case eq of λ ()
... | Pool.closedPool = case eq of λ ()
queue-effect Pool.finishClose c eq with Pool.phase c | Pool.remaining c in restEq
... | Pool.closing | [] = case just-injective eq of λ { refl → quiet refl }
... | Pool.openPool | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | (Pool.cancelPending k₁) | _ = case eq of λ ()
... | (Pool.joinPending k₁) | _ = case eq of λ ()
... | Pool.closing | _ ∷ _ = case eq of λ ()



-- Primitive content preservation, including cancellation, unwind replacement,
-- deregistration, whole close and consumption. No reference is manufactured.
NewReturn : Pool.Action → (Result → Set) → Set
NewReturn (Pool.bodyReturnedWith j value) C = C value
NewReturn _ C = ⊤
returned-content : ∀ C a c {d} → Pool.step a c ≡ just d → Content C c → NewReturn a C →
  ∀ j value → lookup j (Pool.handles d) ≡ just (Pool.bodyReturned value) → C value
returned-content C a c {d} actual good new j value found with H.handle-effect a c actual
... | H.h-quiet same = Content.returned good j value (trans (sym (cong (lookup j) same)) found)
... | H.h-write k phase nonreturn same with j ≟ k
...   | no apart = Content.returned good j value (trans (sym (lookup-put-other k j phase (Pool.handles c) apart))
      (trans (sym (cong (lookup j) same)) found))
...   | yes refl = ⊥-elim (nonreturn value (just-injective (trans (sym (lookup-put k phase (Pool.handles c)))
      (trans (sym (cong (lookup k) same)) found))))
returned-content C .(Pool.bodyReturnedWith k result) c actual good new j value found | H.h-return k result same with j ≟ k
... | no apart = Content.returned good j value (trans (sym (lookup-put-other k j (Pool.bodyReturned result) (Pool.handles c) apart))
      (trans (sym (cong (lookup j) same)) found))
... | yes refl = subst C (H.return-injective (just-injective (trans (sym (lookup-put k (Pool.bodyReturned result) (Pool.handles c)))
      (trans (sym (cong (lookup k) same)) found)))) new
step-preserves : ∀ C a c {d} → Pool.step a c ≡ just d → Content C c → NewReturn a C → Content C d
step-preserves C a c {d} actual good new = record
 { queued = queued; returned = returned-content C a c actual good new }
 where
 queued : All C (Pool.completions d)
 queued with queue-effect a c actual
 ... | quiet same = subst (All C) (sym same) (Content.queued good)
 ... | append j value found same = subst (All C) (sym same) (++⁺ (Content.queued good) (Content.returned good j value found ∷ []))
 ... | pop value rest before after = subst (All C) (sym after) (All.tail (subst (All C) before (Content.queued good)))

-- Retarget a static payload predicate before applying the actual pool writer.
map-content : ∀ {C E p} → (∀ value → C value → E value) → Content C p → Content E p
map-content f good = record { queued = All.map (λ {value} → f value) (Content.queued good)
 ; returned = λ j value found → f value (Content.returned good j value found) }
initial : ∀ C → Content C Pool.initial
initial C = record { queued = []; returned = λ j value () }

-- Physical handle history is monotone even when its phase changes.
handles-retained : ∀ a c {d} → Pool.step a c ≡ just d →
  ∀ j → Present j (Pool.handles c) → Present j (Pool.handles d)
handles-retained a c {d} actual j old with H.handle-effect a c actual
... | H.h-quiet same = subst (Present j) (sym same) old
... | H.h-write k phase nonreturn same = subst (Present j) (sym same)
 (put-preserves-present k j phase (Pool.handles c) old)
... | H.h-return k value same = subst (Present j) (sym same)
 (put-preserves-present k j (Pool.bodyReturned value) (Pool.handles c) old)
exec-handles-retained : ∀ {p actions q} → Pool.Executes p actions q →
  ∀ j → Present j (Pool.handles p) → Present j (Pool.handles q)
exec-handles-retained Pool.done j old = old
exec-handles-retained (Pool.next {s = p} {a = a} actual path) j old =
 exec-handles-retained path j (handles-retained a p actual j old)

-- A body-return observation is guarded by the actual running handle.
return-running : ∀ j value p {q} → Pool.step (Pool.bodyReturnedWith j value) p ≡ just q →
 lookup j (Pool.handles p) ≡ just Pool.bodyRunning
return-running j value p actual with lookup j (Pool.handles p) in found
... | just Pool.bodyRunning = refl
... | nothing = case actual of λ ()
... | just (Pool.bodyReturned _) = case actual of λ ()
... | just Pool.bodyUnwinding = case actual of λ ()
... | just (Pool.deregisterPending _) = case actual of λ ()
... | just (Pool.deregistered _) = case actual of λ ()
... | just (Pool.resultAvailable _) = case actual of λ ()

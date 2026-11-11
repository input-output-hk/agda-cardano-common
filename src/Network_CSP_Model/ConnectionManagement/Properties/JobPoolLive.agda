{-# OPTIONS --guardedness #-}

-- A closed pool has no running or unwinding handle, for any historical job,
-- not only for snapshot members. Every live handle is registered (or is the
-- masked parent fork) while the pool is open, and is on the close cursor's
-- pending tail afterwards; a closed pool has an empty tail.
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.JobPoolLive (Result : Set) (queued : Bool) where

open import Data.Bool using (true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; subst; cong)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (JobId)
open import ConnectionManagement.Store using (Store; lookup; put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
open import ConnectionManagement.Properties.Entries using (lookup-put)
import ConnectionManagement.Rules.JobPoolKernel as Lifecycle
import ConnectionManagement.Properties.JobPoolCloseKernel as CloseKernel
module Pool = Lifecycle Result queued
private
  module Close = CloseKernel Result queued

-- A body that is running or unwinding has not yet produced any exit.
live : Maybe Pool.ThreadPhase → Bool
live (just Pool.bodyRunning) = true
live (just Pool.bodyUnwinding) = true
live _ = false

Live : Pool.State → JobId → Set
Live c j = live (lookup j (Pool.handles c)) ≡ true

-- Open: a live handle is registered or is the masked parent fork (only the
-- single-owner WithQueue pool forks without registering concurrently).
-- Closing: a live handle is on the pending tail, as is the cursor's handle.
record Inv (c : Pool.State) : Set where
  field
    opened : queued ≡ true → Pool.phase c ≡ Pool.openPool → ∀ j → Live c j →
      Pool.member j (Pool.registered c) ≡ true ⊎ Pool.parentFork c ≡ just j
    pending : Pool.phase c ≢ Pool.openPool → ∀ j → Live c j → Pool.member j (Pool.remaining c) ≡ true
    cursor : ∀ j → Pool.phase c ≡ Pool.cancelPending j ⊎ Pool.phase c ≡ Pool.joinPending j →
      Pool.member j (Pool.remaining c) ≡ true
open Inv public

-- Store and list facts.
put-live : ∀ (h : Store JobId Pool.ThreadPhase) (k : JobId) v (j : JobId) → live (lookup j (put k v h)) ≡ true →
  (j ≡ k × live (just v) ≡ true) ⊎ (j ≢ k × live (lookup j h) ≡ true)
put-live h k v j l with j ≟ k
... | yes refl = inj₁ (refl , trans (cong live (sym (lookup-put k v h))) l)
... | no apart = inj₂ (apart , trans (cong live (sym (lookup-put-other k j v h apart))) l)
member-head : ∀ j js → Pool.member j (j ∷ js) ≡ true
member-head j js with j ≟ j
... | yes _ = refl
... | no neq = ⊥-elim (neq refl)
member-cons : ∀ j k js → Pool.member j js ≡ true → Pool.member j (k ∷ js) ≡ true
member-cons j k js m with j ≟ k
... | yes _ = refl
... | no _ = m
member-tail : ∀ j k js → j ≢ k → Pool.member j (k ∷ js) ≡ true → Pool.member j js ≡ true
member-tail j k js apart m with j ≟ k
... | yes eq = ⊥-elim (apart eq)
... | no _ = m
member-remove : ∀ j k js → j ≢ k → Pool.member j js ≡ true → Pool.member j (Pool.remove k js) ≡ true
member-remove j k [] apart ()
member-remove j k (x ∷ xs) apart m with k ≟ x | j ≟ x
... | yes refl | yes refl = ⊥-elim (apart refl)
... | yes refl | no _ = member-remove j k xs apart m
... | no _ | yes refl = member-head j (Pool.remove k xs)
... | no _ | no _ = member-cons j x (Pool.remove k xs)
  (member-remove j k xs apart m)
∧-true : ∀ a b → a ∧ b ≡ true → a ≡ true × b ≡ true
∧-true true true refl = refl , refl
∧-true true false ()
∧-true false b ()
all-member : ∀ j xs ys → Pool.allMembers xs ys ≡ true → Pool.member j xs ≡ true → Pool.member j ys ≡ true
all-member j [] ys all ()
all-member j (x ∷ xs) ys all m with j ≟ x
... | yes refl = proj₁ (∧-true (Pool.member j ys) _ all)
... | no _ = all-member j xs ys (proj₂ (∧-true _ _ all)) m
settled-member : ∀ h cur j → Pool.registrationsSettled h cur ≡ true → live (lookup j h) ≡ true →
  Pool.member j cur ≡ true
settled-member [] cur j settled ()
settled-member ((k , st) ∷ rest) cur j settled l with j ≟ k
settled-member ((k , Pool.bodyRunning) ∷ rest) cur j settled l | yes refl = proj₁ (∧-true _ _ settled)
settled-member ((k , Pool.bodyUnwinding) ∷ rest) cur j settled l | yes refl = proj₁ (∧-true _ _ settled)
settled-member ((k , Pool.bodyReturned _) ∷ rest) cur j settled () | yes refl
settled-member ((k , Pool.deregisterPending _) ∷ rest) cur j settled () | yes refl
settled-member ((k , Pool.deregistered _) ∷ rest) cur j settled () | yes refl
settled-member ((k , Pool.resultAvailable _) ∷ rest) cur j settled () | yes refl
settled-member ((k , Pool.bodyRunning) ∷ rest) cur j settled l | no _ = settled-member rest cur j (proj₂ (∧-true _ _ settled)) l
settled-member ((k , Pool.bodyUnwinding) ∷ rest) cur j settled l | no _ = settled-member rest cur j (proj₂ (∧-true _ _ settled)) l
settled-member ((k , Pool.bodyReturned _) ∷ rest) cur j settled l | no _ = settled-member rest cur j (proj₂ (∧-true _ _ settled)) l
settled-member ((k , Pool.deregisterPending _) ∷ rest) cur j settled l | no _ = settled-member rest cur j (proj₂ (∧-true _ _ settled)) l
settled-member ((k , Pool.deregistered _) ∷ rest) cur j settled l | no _ = settled-member rest cur j settled l
settled-member ((k , Pool.resultAvailable _) ∷ rest) cur j settled l | no _ = settled-member rest cur j settled l

-- Phase contradictions.
open-not-pending : ∀ {c j} → Pool.phase c ≡ Pool.openPool →
  Pool.phase c ≡ Pool.cancelPending j ⊎ Pool.phase c ≡ Pool.joinPending j → ⊥
open-not-pending o (inj₁ p) = case trans (sym o) p of λ ()
open-not-pending o (inj₂ p) = case trans (sym o) p of λ ()
closing-not-pending : ∀ {c j} → Pool.phase c ≡ Pool.closing →
  Pool.phase c ≡ Pool.cancelPending j ⊎ Pool.phase c ≡ Pool.joinPending j → ⊥
closing-not-pending o (inj₁ p) = case trans (sym o) p of λ ()
closing-not-pending o (inj₂ p) = case trans (sym o) p of λ ()
closing-not-open : ∀ {c} → Pool.phase c ≡ Pool.closing → Pool.phase c ≢ Pool.openPool
closing-not-open o p = case trans (sym o) p of λ ()
returned-dead : ∀ b r → live (just (Pool.returnedPhase b r)) ≡ false
returned-dead true r = refl
returned-dead false r = refl

-- A write that keeps every surviving live handle live where it was live.
-- Handles written to a dead phase lose liveness; a live write must be at a
-- handle that was live before (resume, interruption, delivery).
write-dead : ∀ c k v → live (just v) ≡ false → ∀ j → live (lookup j (put k v (Pool.handles c))) ≡ true →
  j ≢ k × Live c j
write-dead c k v dead j l with put-live (Pool.handles c) k v j l
... | inj₁ (refl , alive) = case trans (sym dead) alive of λ ()
... | inj₂ other = other
write-live : ∀ c k v old → lookup k (Pool.handles c) ≡ just old → live (just old) ≡ true →
  ∀ j → live (lookup j (put k v (Pool.handles c))) ≡ true → Live c j
write-live c k v old found wasLive j l with put-live (Pool.handles c) k v j l
... | inj₁ (refl , _) = trans (cong live found) wasLive
... | inj₂ (_ , other) = other

-- Queue-policy helpers are generic in the policy flag. Named writes keep the
-- written phase out of with-abstracted goals.
running-at : JobId → Pool.State → Pool.State
running-at k c = record c { handles = put k Pool.bodyRunning (Pool.handles c) }
registered-at : JobId → Pool.State → Pool.State
registered-at k c = record c { registered = k ∷ Pool.registered c }
concurrent-fork : ∀ b k c {c′} → Pool.concurrentFork b k c ≡ just c′ →
  b ≡ false × Pool.phase c ≡ Pool.openPool × c′ ≡ running-at k c
concurrent-fork true k c ()
concurrent-fork false k c eq with Pool.phase c in ph | lookup k (Pool.handles c)
... | Pool.openPool | nothing = refl , refl , sym (just-injective eq)
... | Pool.openPool | just _ = case eq of λ ()
... | Pool.closing | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | Pool.cancelPending _ | _ = case eq of λ ()
... | Pool.joinPending _ | _ = case eq of λ ()
concurrent-register : ∀ b k c {c′} → Pool.concurrentRegister b k c ≡ just c′ →
  Pool.phase c ≡ Pool.openPool × c′ ≡ registered-at k c
concurrent-register true k c ()
concurrent-register false k c eq with Pool.phase c in ph | lookup k (Pool.handles c) | Pool.member k (Pool.registered c)
... | Pool.openPool | just state | false with Pool.awaitingRegistration state
...   | true = refl , sym (just-injective eq)
...   | false = case eq of λ ()
concurrent-register false k c eq | Pool.openPool | just _ | true = case eq of λ ()
concurrent-register false k c eq | Pool.openPool | nothing | _ = case eq of λ ()
concurrent-register false k c eq | Pool.closing | _ | _ = case eq of λ ()
concurrent-register false k c eq | Pool.closedPool | _ | _ = case eq of λ ()
concurrent-register false k c eq | Pool.cancelPending _ | _ | _ = case eq of λ ()
concurrent-register false k c eq | Pool.joinPending _ | _ | _ = case eq of λ ()
publish-queued : ∀ b k c {c′} → Pool.publishQueued b k c ≡ just c′ →
  Pool.phase c′ ≡ Pool.phase c × Pool.remaining c′ ≡ Pool.remaining c × Pool.registered c′ ≡ Pool.registered c ×
  Pool.parentFork c′ ≡ Pool.parentFork c × (∀ j → Live c′ j → Live c j)
publish-queued false k c ()
publish-queued true k c eq with lookup k (Pool.handles c)
... | just (Pool.bodyReturned result) = case just-injective eq of λ { refl →
  refl , refl , refl , refl , λ j l → proj₂ (write-dead c k (Pool.deregisterPending Pool.normalExit) refl j l) }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending _) = case eq of λ ()
... | just (Pool.deregistered _) = case eq of λ ()
... | just (Pool.resultAvailable _) = case eq of λ ()
-- Phase, cursor, registry and parent fork are kept; liveness only shrinks.
Kept : Pool.State → Pool.State → Set
Kept c c′ = Pool.phase c′ ≡ Pool.phase c × Pool.remaining c′ ≡ Pool.remaining c × Pool.registered c′ ≡ Pool.registered c ×
  Pool.parentFork c′ ≡ Pool.parentFork c × (∀ j → Live c′ j → Live c j)
consume-queued : ∀ b c {c′} → Pool.consumeQueued b c ≡ just c′ → Kept c c′
consume-queued false c ()
consume-queued true c eq with Pool.phase c in ph | Pool.completions c
... | Pool.openPool | result ∷ rest = case just-injective eq of λ { refl → ph , refl , refl , refl , λ j l → l }
... | Pool.openPool | [] = case eq of λ ()
... | Pool.closing | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | Pool.cancelPending _ | _ = case eq of λ ()
... | Pool.joinPending _ | _ = case eq of λ ()

-- Any step that keeps phase, cursor, registry and parent fork and only removes
-- liveness preserves the invariant.
shrink : ∀ c c′ → Pool.phase c′ ≡ Pool.phase c → Pool.remaining c′ ≡ Pool.remaining c →
  Pool.registered c′ ≡ Pool.registered c → Pool.parentFork c′ ≡ Pool.parentFork c →
  (∀ j → Live c′ j → Live c j) → Inv c → Inv c′
shrink c c′ ph rem reg pf back inv = record
  { opened = λ q o j l → case opened inv q (trans (sym ph) o) j (back j l) of λ
      { (inj₁ m) → inj₁ (subst (λ r → Pool.member j r ≡ true) (sym reg) m)
      ; (inj₂ p) → inj₂ (trans pf p) }
  ; pending = λ notOpen j l → subst (λ r → Pool.member j r ≡ true) (sym rem)
      (pending inv (λ o → notOpen (trans ph o)) j (back j l))
  ; cursor = λ j p → subst (λ r → Pool.member j r ≡ true) (sym rem)
      (cursor inv j (case p of λ { (inj₁ e) → inj₁ (trans (sym ph) e) ; (inj₂ e) → inj₂ (trans (sym ph) e) })) }

-- Join removes only the joined head, whose handle is not live.
join-head : ∀ current c {c′} → Pool.phase c ≢ Pool.openPool → Pool.joinHead current c ≡ just c′ → Inv c → Inv c′
join-head current c notOpen eq inv with Pool.remaining c in rem | lookup current (Pool.handles c) in found
... | j ∷ rest | just (Pool.resultAvailable exit) with current ≟ j
...   | yes refl = case just-injective eq of λ { refl → record
  { opened = λ q o → case o of λ ()
  ; pending = λ _ k l → member-tail k current rest
      (λ { refl → case trans (sym (cong live found)) l of λ () })
      (subst (λ r → Pool.member k r ≡ true) rem (pending inv notOpen k l))
  ; cursor = λ k p → case p of λ { (inj₁ ()) ; (inj₂ ()) } } }
...   | no _ = case eq of λ ()
join-head current c notOpen eq inv | j ∷ rest | just Pool.bodyRunning = case eq of λ ()
join-head current c notOpen eq inv | j ∷ rest | just Pool.bodyUnwinding = case eq of λ ()
join-head current c notOpen eq inv | j ∷ rest | just (Pool.bodyReturned _) = case eq of λ ()
join-head current c notOpen eq inv | j ∷ rest | just (Pool.deregisterPending _) = case eq of λ ()
join-head current c notOpen eq inv | j ∷ rest | just (Pool.deregistered _) = case eq of λ ()
join-head current c notOpen eq inv | j ∷ rest | nothing = case eq of λ ()
join-head current c notOpen eq inv | [] | _ = case eq of λ ()

same-current : ∀ order cur → Pool.sameSnapshot order cur ≡ true → Pool.allMembers cur order ≡ true
same-current order cur s =
  proj₂ (∧-true (Pool.allMembers order cur) (Pool.allMembers cur order)
  (proj₂ (∧-true (Pool.unique cur) (Pool.allMembers order cur ∧ Pool.allMembers cur order)
  (proj₂ (∧-true (Pool.unique order) (Pool.unique cur ∧ (Pool.allMembers order cur ∧ Pool.allMembers cur order)) s)))))

-- The close snapshot contains every live handle: the WithQueue owner's
-- registry, or the settled concurrent registry of the WithoutQueue policy.
snapshot-member : ∀ b order c → Pool.canSnapshot b order c ≡ true →
  (b ≡ true → ∀ k → Live c k → Pool.member k (Pool.registered c) ≡ true ⊎ Pool.parentFork c ≡ just k) →
  Pool.parentFork c ≡ nothing → ∀ k → Live c k → Pool.member k order ≡ true
snapshot-member true order c snap op pf k l with op refl k l
... | inj₁ m = all-member k (Pool.registered c) order (same-current order (Pool.registered c) snap) m
... | inj₂ p = case trans (sym pf) p of λ ()
snapshot-member false order c snap op pf k l with ∧-true (Pool.registrationsSettled (Pool.handles c) (Pool.registered c))
  (Pool.sameSnapshot order (Pool.registered c)) snap
... | settled , same = all-member k (Pool.registered c) order (same-current order (Pool.registered c) same)
  (settled-member (Pool.handles c) (Pool.registered c) k settled l)

-- The cursor moves to the pending head without changing handles or the tail.
request-inv : ∀ c j rest phase → Pool.phase c ≡ Pool.closing → Pool.remaining c ≡ j ∷ rest →
  (∀ k → phase ≡ Pool.cancelPending k ⊎ phase ≡ Pool.joinPending k → k ≡ j) → phase ≢ Pool.openPool →
  Inv c → Inv (record c { phase = phase })
request-inv c j rest phase ph rem same notOpen inv = record
  { opened = λ q o → ⊥-elim (notOpen o)
  ; pending = λ _ k l → pending inv (closing-not-open {c = c} ph) k l
  ; cursor = λ k p → case same k p of λ { refl →
      subst (λ r → Pool.member k r ≡ true) (sym rem) (member-head k rest) } }
cancel-same : ∀ j k → Pool.cancelPending j ≡ Pool.cancelPending k ⊎ Pool.cancelPending j ≡ Pool.joinPending k → k ≡ j
cancel-same j k (inj₁ refl) = refl
cancel-same j k (inj₂ ())
join-same : ∀ j k → Pool.joinPending j ≡ Pool.cancelPending k ⊎ Pool.joinPending j ≡ Pool.joinPending k → k ≡ j
join-same j k (inj₁ ())
join-same j k (inj₂ refl) = refl

-- Every kernel step preserves the invariant.
step-preserves : ∀ a c {c′} → Pool.step a c ≡ just c′ → Inv c → Inv c′
step-preserves (Pool.fork j) c eq inv with Pool.phase c in ph | Pool.parentFork c in pf | lookup j (Pool.handles c)
... | Pool.openPool | nothing | nothing = case just-injective eq of λ { refl → record
  { opened = λ q o k l → case put-live (Pool.handles c) j Pool.bodyRunning k l of λ
      { (inj₁ (refl , _)) → inj₂ refl
      ; (inj₂ (_ , old)) → case opened inv q ph k old of λ
          { (inj₁ m) → inj₁ m ; (inj₂ p) → case trans (sym pf) p of λ () } }
  ; pending = λ notOpen → ⊥-elim (notOpen ph)
  ; cursor = λ k p → ⊥-elim (open-not-pending {c = c} ph p) } }
... | Pool.openPool | nothing | just _ = case eq of λ ()
... | Pool.openPool | just _ | _ = case eq of λ ()
... | Pool.closing | _ | _ = case eq of λ ()
... | Pool.closedPool | _ | _ = case eq of λ ()
... | Pool.cancelPending _ | _ | _ = case eq of λ ()
... | Pool.joinPending _ | _ | _ = case eq of λ ()
step-preserves Pool.register c eq inv with Pool.phase c in ph | Pool.parentFork c in pf
... | Pool.openPool | just j with Pool.member j (Pool.registered c)
...   | false = case just-injective eq of λ { refl → record
  { opened = λ q o k l → case opened inv q ph k l of λ
      { (inj₁ m) → inj₁ (member-cons k j (Pool.registered c) m)
      ; (inj₂ p) → case trans (sym pf) p of λ { refl → inj₁ (member-head k (Pool.registered c)) } }
  ; pending = λ notOpen → ⊥-elim (notOpen ph)
  ; cursor = λ k p → ⊥-elim (open-not-pending {c = c} ph p) } }
...   | true = case eq of λ ()
step-preserves Pool.register c eq inv | Pool.openPool | nothing = case eq of λ ()
step-preserves Pool.register c eq inv | Pool.closing | _ = case eq of λ ()
step-preserves Pool.register c eq inv | Pool.closedPool | _ = case eq of λ ()
step-preserves Pool.register c eq inv | Pool.cancelPending _ | _ = case eq of λ ()
step-preserves Pool.register c eq inv | Pool.joinPending _ | _ = case eq of λ ()
step-preserves (Pool.forkConcurrent j) c eq inv with concurrent-fork queued j c eq
... | policy , ph , refl = record
  { opened = λ q → case trans (sym q) policy of λ ()
  ; pending = λ notOpen → ⊥-elim (notOpen ph)
  ; cursor = λ k p → ⊥-elim (open-not-pending {c = c} ph p) }
step-preserves (Pool.registerConcurrent j) c eq inv with concurrent-register queued j c eq
... | ph , refl = record
  { opened = λ q o k l → case opened inv q ph k l of λ
      { (inj₁ m) → inj₁ (member-cons k j (Pool.registered c) m) ; (inj₂ p) → inj₂ p }
  ; pending = λ notOpen → ⊥-elim (notOpen ph)
  ; cursor = λ k p → ⊥-elim (open-not-pending {c = c} ph p) }
step-preserves (Pool.bodyReturnedWith j r) c eq inv with lookup j (Pool.handles c)
... | just Pool.bodyRunning = case just-injective eq of λ { refl → shrink c _ refl refl refl refl
  (λ k l → proj₂ (write-dead c j (Pool.returnedPhase queued r) (returned-dead queued r) k l)) inv }
... | nothing = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.bodyReturned _) = case eq of λ ()
... | just (Pool.deregisterPending _) = case eq of λ ()
... | just (Pool.deregistered _) = case eq of λ ()
... | just (Pool.resultAvailable _) = case eq of λ ()
step-preserves (Pool.publishCompletion j) c {c′} eq inv with publish-queued queued j c eq
... | ph , rem , reg , pf , back = shrink c c′ ph rem reg pf back inv
step-preserves Pool.consumeCompletion c {c′} eq inv with consume-queued queued c eq
... | ph , rem , reg , pf , back = shrink c c′ ph rem reg pf back inv
step-preserves (Pool.interruptJob j) c eq inv with Pool.phase c | lookup j (Pool.handles c) in found
... | Pool.openPool | just Pool.bodyRunning = case just-injective eq of λ { refl → shrink c _ refl refl refl refl
  (write-live c j Pool.bodyUnwinding Pool.bodyRunning found refl) inv }
... | Pool.openPool | nothing = case eq of λ ()
... | Pool.openPool | just Pool.bodyUnwinding = case eq of λ ()
... | Pool.openPool | just (Pool.bodyReturned _) = case eq of λ ()
... | Pool.openPool | just (Pool.deregisterPending _) = case eq of λ ()
... | Pool.openPool | just (Pool.deregistered _) = case eq of λ ()
... | Pool.openPool | just (Pool.resultAvailable _) = case eq of λ ()
... | Pool.closing | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | Pool.cancelPending _ | _ = case eq of λ ()
... | Pool.joinPending _ | _ = case eq of λ ()
step-preserves (Pool.bodyUnwound j) c eq inv with lookup j (Pool.handles c)
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → shrink c _ refl refl refl refl
  (λ k l → proj₂ (write-dead c j (Pool.deregisterPending Pool.cancelledExit) refl k l)) inv }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned _) = case eq of λ ()
... | just (Pool.deregisterPending _) = case eq of λ ()
... | just (Pool.deregistered _) = case eq of λ ()
... | just (Pool.resultAvailable _) = case eq of λ ()
step-preserves (Pool.resumeAfterUnwindError j) c eq inv with lookup j (Pool.handles c) in found
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → shrink c _ refl refl refl refl
  (write-live c j Pool.bodyRunning Pool.bodyUnwinding found refl) inv }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned _) = case eq of λ ()
... | just (Pool.deregisterPending _) = case eq of λ ()
... | just (Pool.deregistered _) = case eq of λ ()
... | just (Pool.resultAvailable _) = case eq of λ ()
step-preserves (Pool.deregister j) c eq inv with lookup j (Pool.handles c) | Pool.member j (Pool.registered c)
... | just (Pool.deregisterPending exit) | true = case just-injective eq of λ { refl → record
  { opened = λ q o k l → case write-dead c j (Pool.deregistered exit) refl k l of λ
      { (apart , old) → case opened inv q o k old of λ
          { (inj₁ m) → inj₁ (member-remove k j (Pool.registered c) apart m) ; (inj₂ p) → inj₂ p } }
  ; pending = λ notOpen k l → pending inv notOpen k (proj₂ (write-dead c j (Pool.deregistered exit) refl k l))
  ; cursor = cursor inv } }
... | just (Pool.deregisterPending exit) | false = case eq of λ ()
... | nothing | _ = case eq of λ ()
... | just Pool.bodyRunning | _ = case eq of λ ()
... | just Pool.bodyUnwinding | _ = case eq of λ ()
... | just (Pool.bodyReturned _) | _ = case eq of λ ()
... | just (Pool.deregistered _) | _ = case eq of λ ()
... | just (Pool.resultAvailable _) | _ = case eq of λ ()
step-preserves (Pool.publishAsyncResult j) c eq inv with lookup j (Pool.handles c)
... | just (Pool.deregistered exit) = case just-injective eq of λ { refl → shrink c _ refl refl refl refl
  (λ k l → proj₂ (write-dead c j (Pool.resultAvailable exit) refl k l)) inv }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.bodyReturned _) = case eq of λ ()
... | just (Pool.deregisterPending _) = case eq of λ ()
... | just (Pool.resultAvailable _) = case eq of λ ()
step-preserves (Pool.beginClose order) c eq inv with Pool.phase c in ph | Pool.parentFork c in pf | Pool.canSnapshot queued order c in snap
... | Pool.openPool | nothing | true = case just-injective eq of λ { refl → record
  { opened = λ q o → case o of λ ()
  ; pending = λ _ k l → snapshot-member queued order c snap (λ q → opened inv q ph) pf k l
  ; cursor = λ k p → case p of λ { (inj₁ ()) ; (inj₂ ()) } } }
... | Pool.openPool | nothing | false = case eq of λ ()
... | Pool.openPool | just _ | _ = case eq of λ ()
... | Pool.closing | _ | _ = case eq of λ ()
... | Pool.closedPool | _ | _ = case eq of λ ()
... | Pool.cancelPending _ | _ | _ = case eq of λ ()
... | Pool.joinPending _ | _ | _ = case eq of λ ()
step-preserves Pool.requestCancel c eq inv with Pool.phase c in ph | Pool.remaining c in rem
... | Pool.closing | j ∷ rest with lookup j (Pool.handles c)
...   | just (Pool.resultAvailable exit) = case just-injective eq of λ { refl →
  request-inv c j rest (Pool.joinPending j) ph rem (join-same j) (λ ()) inv }
...   | just Pool.bodyRunning = case just-injective eq of λ { refl →
  request-inv c j rest (Pool.cancelPending j) ph rem (cancel-same j) (λ ()) inv }
...   | just Pool.bodyUnwinding = case just-injective eq of λ { refl →
  request-inv c j rest (Pool.cancelPending j) ph rem (cancel-same j) (λ ()) inv }
...   | just (Pool.bodyReturned _) = case just-injective eq of λ { refl →
  request-inv c j rest (Pool.cancelPending j) ph rem (cancel-same j) (λ ()) inv }
...   | just (Pool.deregisterPending _) = case just-injective eq of λ { refl →
  request-inv c j rest (Pool.cancelPending j) ph rem (cancel-same j) (λ ()) inv }
...   | just (Pool.deregistered _) = case just-injective eq of λ { refl →
  request-inv c j rest (Pool.cancelPending j) ph rem (cancel-same j) (λ ()) inv }
...   | nothing = case eq of λ ()
step-preserves Pool.requestCancel c eq inv | Pool.closing | [] = case eq of λ ()
step-preserves Pool.requestCancel c eq inv | Pool.openPool | _ = case eq of λ ()
step-preserves Pool.requestCancel c eq inv | Pool.closedPool | _ = case eq of λ ()
step-preserves Pool.requestCancel c eq inv | Pool.cancelPending _ | _ = case eq of λ ()
step-preserves Pool.requestCancel c eq inv | Pool.joinPending _ | _ = case eq of λ ()
step-preserves Pool.deliverCancel c eq inv with Pool.phase c in ph
... | Pool.cancelPending j with lookup j (Pool.handles c)
...   | just Pool.bodyRunning = case just-injective eq of λ { refl → record
  { opened = λ q o → case o of λ ()
  ; pending = λ _ k l → case put-live (Pool.handles c) j Pool.bodyUnwinding k l of λ
      { (inj₁ (refl , _)) → cursor inv k (inj₁ ph)
      ; (inj₂ (_ , old)) → pending inv (λ o → case trans (sym ph) o of λ ()) k old }
  ; cursor = λ k p → case p of λ { (inj₁ ()) ; (inj₂ refl) → cursor inv j (inj₁ ph) } } }
...   | nothing = case eq of λ ()
...   | just Pool.bodyUnwinding = case eq of λ ()
...   | just (Pool.bodyReturned _) = case eq of λ ()
...   | just (Pool.deregisterPending _) = case eq of λ ()
...   | just (Pool.deregistered _) = case eq of λ ()
...   | just (Pool.resultAvailable _) = case eq of λ ()
step-preserves Pool.deliverCancel c eq inv | Pool.openPool = case eq of λ ()
step-preserves Pool.deliverCancel c eq inv | Pool.closing = case eq of λ ()
step-preserves Pool.deliverCancel c eq inv | Pool.closedPool = case eq of λ ()
step-preserves Pool.deliverCancel c eq inv | Pool.joinPending _ = case eq of λ ()
step-preserves Pool.join c eq inv with Pool.phase c in ph
... | Pool.cancelPending j = join-head j c (λ o → case trans (sym ph) o of λ ()) eq inv
... | Pool.joinPending j = join-head j c (λ o → case trans (sym ph) o of λ ()) eq inv
... | Pool.openPool = case eq of λ ()
... | Pool.closing = case eq of λ ()
... | Pool.closedPool = case eq of λ ()
step-preserves Pool.finishClose c eq inv with Pool.phase c in ph | Pool.remaining c in rem
... | Pool.closing | [] = case just-injective eq of λ { refl → record
  { opened = λ q o → case o of λ ()
  ; pending = λ _ k l → case subst (λ r → Pool.member k r ≡ true) rem
      (pending inv (closing-not-open {c = c} ph) k l) of λ ()
  ; cursor = λ k p → case p of λ { (inj₁ ()) ; (inj₂ ()) } } }
... | Pool.closing | _ ∷ _ = case eq of λ ()
... | Pool.openPool | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | Pool.cancelPending _ | _ = case eq of λ ()
... | Pool.joinPending _ | _ = case eq of λ ()

initial-inv : Inv Pool.initial
initial-inv = record
  { opened = λ _ _ j ()
  ; pending = λ notOpen → ⊥-elim (notOpen refl)
  ; cursor = λ j p → case p of λ { (inj₁ ()) ; (inj₂ ()) } }
exec-preserves : ∀ {c as c′} → Pool.Executes c as c′ → Inv c → Inv c′
exec-preserves Pool.done inv = inv
exec-preserves (Pool.next {s = c} {a = a} eq path) inv = exec-preserves path (step-preserves a c eq inv)

-- At a closed pool reached from the initial pool, no handle is live.
closed-dead : ∀ {as c} → Pool.Executes Pool.initial as c → Pool.phase c ≡ Pool.closedPool →
  ∀ j → live (lookup j (Pool.handles c)) ≡ false
closed-dead {c = c} path closed j with live (lookup j (Pool.handles c)) in l
... | false = refl
... | true = case subst (λ r → Pool.member j r ≡ true) (Close.exec-empty path (λ ()) closed)
  (pending (exec-preserves path initial-inv) (λ o → case trans (sym closed) o of λ ()) j l) of λ ()

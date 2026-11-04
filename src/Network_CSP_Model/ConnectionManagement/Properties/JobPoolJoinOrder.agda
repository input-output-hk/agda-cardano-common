{-# OPTIONS --guardedness #-}

-- The immutable close snapshot is cut into its joined prefix and pending tail.
open import Data.Bool using (Bool)
module ConnectionManagement.Properties.JobPoolJoinOrder (Result : Set) (queued : Bool) where
open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-assoc)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Any using (here; there)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (JobId)
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Rules.JobPoolKernel as Kernel
module Pool = Kernel Result queued

Partition : Pool.State → Set
Partition c = Pool.snapshot c ≡ Pool.joined c ++ Pool.remaining c

-- Both waiting phases may join, independently of the observed exit cause.
data Waiting (current : JobId) : Pool.ClosePC → Set where
 cancel-requested : Waiting current (Pool.cancelPending current)
 join-waiting : Waiting current (Pool.joinPending current)
record Head (current : JobId) (before after : Pool.State) : Set where
 constructor head-step
 field
  result : Pool.Exit
  tail : List JobId
  head : Pool.remaining before ≡ current ∷ tail
  available : lookup current (Pool.handles before) ≡ just (Pool.resultAvailable result)
  state : after ≡ record before { phase = Pool.closing; remaining = tail; joined = Pool.joined before ++ (current ∷ []) }

-- Inspect the actual head and terminal result; registry absence is insufficient.
inspect-head : ∀ current c {d} → Pool.joinHead current c ≡ just d → Head current c d
inspect-head current c eq with Pool.remaining c in remainingEq | lookup current (Pool.handles c) in availableEq
... | head ∷ rest | just (Pool.resultAvailable result) with current ≟ head
...   | yes refl = head-step result rest remainingEq availableEq (sym (just-injective eq))
...   | no _ = case eq of λ ()
inspect-head current c eq | [] | _ = case eq of λ ()
inspect-head current c eq | _ ∷ _ | nothing = case eq of λ ()
inspect-head current c eq | _ ∷ _ | just Pool.bodyRunning = case eq of λ ()
inspect-head current c eq | _ ∷ _ | just (Pool.bodyReturned _) = case eq of λ ()
inspect-head current c eq | _ ∷ _ | just Pool.bodyUnwinding = case eq of λ ()
inspect-head current c eq | _ ∷ _ | just (Pool.deregisterPending _) = case eq of λ ()
inspect-head current c eq | _ ∷ _ | just (Pool.deregistered _) = case eq of λ ()
record Join (before after : Pool.State) : Set where
 constructor actual-join
 field
  current : JobId
  waiting : Waiting current (Pool.phase before)
  head : Head current before after
inspect-join : ∀ c {d} → Pool.step Pool.join c ≡ just d → Join c d
inspect-join c eq with Pool.phase c in phaseEq
... | Pool.cancelPending current = actual-join current (subst (Waiting current) (sym phaseEq) cancel-requested) (inspect-head current c eq)
... | Pool.joinPending current = actual-join current (subst (Waiting current) (sym phaseEq) join-waiting) (inspect-head current c eq)
... | Pool.openPool = case eq of λ ()
... | Pool.closing = case eq of λ ()
... | Pool.closedPool = case eq of λ ()

join-partition : ∀ current c {d} → Pool.joinHead current c ≡ just d → Partition c → Partition d
join-partition current c eq valid with inspect-head current c eq
... | head-step result tail head available refl = trans
 (trans valid (cong (Pool.joined c ++_) head)) (sym (++-assoc (Pool.joined c) (current ∷ []) tail))

publish-partition : ∀ enabled k c {c′} → Pool.publishQueued enabled k c ≡ just c′ → Partition c → Partition c′
publish-partition false k c () valid
publish-partition true k c eq valid with lookup k (Pool.handles c)
... | just (Pool.bodyReturned result) = case just-injective eq of λ { refl → valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()

fork-partition : ∀ policy k c {c′} → Pool.concurrentFork policy k c ≡ just c′ → Partition c → Partition c′
fork-partition true k c () valid
fork-partition false k c eq valid with Pool.phase c in phaseEq | lookup k (Pool.handles c) in absent
... | Pool.openPool | nothing = case just-injective eq of λ { refl → valid }
fork-partition false k c eq valid | Pool.closing | _ = case eq of λ ()
fork-partition false k c eq valid | Pool.closedPool | _ = case eq of λ ()
fork-partition false k c eq valid | (Pool.cancelPending current) | _ = case eq of λ ()
fork-partition false k c eq valid | (Pool.joinPending current) | _ = case eq of λ ()
fork-partition false k c eq valid | Pool.openPool | just old = case eq of λ ()
register-partition : ∀ policy k c {c′} → Pool.concurrentRegister policy k c ≡ just c′ → Partition c → Partition c′
register-partition true k c () valid
register-partition false k c eq valid with Pool.phase c in phaseEq | lookup k (Pool.handles c) | Pool.member k (Pool.registered c)
... | Pool.openPool | just state | false with Pool.awaitingRegistration state
...   | true = case just-injective eq of λ { refl → valid }
...   | false = case eq of λ ()
register-partition false k c eq valid | Pool.closing | _ | _ = case eq of λ ()
register-partition false k c eq valid | Pool.closedPool | _ | _ = case eq of λ ()
register-partition false k c eq valid | (Pool.cancelPending current) | _ | _ = case eq of λ ()
register-partition false k c eq valid | (Pool.joinPending current) | _ | _ = case eq of λ ()
register-partition false k c eq valid | Pool.openPool | nothing | _ = case eq of λ ()
register-partition false k c eq valid | Pool.openPool | just state | true = case eq of λ ()

consume-partition : ∀ enabled c {c′} → Pool.consumeQueued enabled c ≡ just c′ → Partition c → Partition c′
consume-partition false c () valid
consume-partition true c eq valid with Pool.phase c in phaseEq | Pool.completions c
... | Pool.openPool | result ∷ rest = case just-injective eq of λ { refl → valid }
... | Pool.openPool | [] = case eq of λ ()
... | Pool.closing | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | Pool.cancelPending j | _ = case eq of λ ()
... | Pool.joinPending j | _ = case eq of λ ()

step-partition : ∀ a c {c′} → Pool.step a c ≡ just c′ → Partition c → Partition c′
step-partition (Pool.fork k) c eq valid with Pool.phase c in phaseEq | Pool.parentFork c | lookup k (Pool.handles c)
... | Pool.openPool | nothing | nothing = case just-injective eq of λ { refl → valid }
... | Pool.closing | _ | _ = case eq of λ ()
... | Pool.closedPool | _ | _ = case eq of λ ()
... | Pool.cancelPending pending | _ | _ = case eq of λ ()
... | Pool.joinPending pending | _ | _ = case eq of λ ()
... | Pool.openPool | just pending | _ = case eq of λ ()
... | Pool.openPool | nothing | just old = case eq of λ ()
step-partition (Pool.forkConcurrent k) c eq valid = fork-partition queued k c eq valid
step-partition (Pool.registerConcurrent k) c eq valid = register-partition queued k c eq valid
step-partition Pool.register c eq valid with Pool.phase c in phaseEq | Pool.parentFork c
... | Pool.openPool | just k with Pool.member k (Pool.registered c)
...   | false = case just-injective eq of λ { refl → valid }
...   | true = case eq of λ ()
step-partition Pool.register c eq valid | Pool.closing | _ = case eq of λ ()
step-partition Pool.register c eq valid | Pool.closedPool | _ = case eq of λ ()
step-partition Pool.register c eq valid | (Pool.cancelPending k₁) | _ = case eq of λ ()
step-partition Pool.register c eq valid | (Pool.joinPending k₁) | _ = case eq of λ ()
step-partition Pool.register c eq valid | Pool.openPool | nothing = case eq of λ ()
step-partition (Pool.bodyReturnedWith k result) c eq valid with lookup k (Pool.handles c)
... | just Pool.bodyRunning = case just-injective eq of λ { refl → valid }
... | nothing = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-partition (Pool.publishCompletion k) c eq valid = publish-partition queued k c eq valid
step-partition Pool.consumeCompletion c eq valid = consume-partition queued c eq valid
step-partition (Pool.interruptJob k) c eq valid with Pool.phase c in phaseEq | lookup k (Pool.handles c)
... | Pool.openPool | just Pool.bodyRunning = case just-injective eq of λ { refl → valid }
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
step-partition (Pool.bodyUnwound k) c eq valid with lookup k (Pool.handles c)
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-partition (Pool.resumeAfterUnwindError k) c eq valid with lookup k (Pool.handles c)
... | just Pool.bodyUnwinding = case just-injective eq of λ { refl → valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.deregistered ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-partition (Pool.deregister k) c eq valid with lookup k (Pool.handles c) | Pool.member k (Pool.registered c)
... | just (Pool.deregisterPending exit) | true = case just-injective eq of λ { refl → valid }
... | nothing | _ = case eq of λ ()
... | just (Pool.deregisterPending exit) | false = case eq of λ ()
... | just Pool.bodyRunning | _ = case eq of λ ()
... | just (Pool.bodyReturned value) | _ = case eq of λ ()
... | just Pool.bodyUnwinding | _ = case eq of λ ()
... | just (Pool.deregistered ex) | _ = case eq of λ ()
... | just (Pool.resultAvailable ex) | _ = case eq of λ ()
step-partition (Pool.publishAsyncResult k) c eq valid with lookup k (Pool.handles c)
... | just (Pool.deregistered exit) = case just-injective eq of λ { refl → valid }
... | nothing = case eq of λ ()
... | just Pool.bodyRunning = case eq of λ ()
... | just (Pool.bodyReturned value) = case eq of λ ()
... | just Pool.bodyUnwinding = case eq of λ ()
... | just (Pool.deregisterPending ex) = case eq of λ ()
... | just (Pool.resultAvailable ex) = case eq of λ ()
step-partition (Pool.beginClose order) c eq valid with Pool.phase c | Pool.parentFork c | Pool.canSnapshot queued order c
... | Pool.openPool | nothing | true = case just-injective eq of λ { refl → refl }
... | Pool.closing | _ | _ = case eq of λ ()
... | Pool.closedPool | _ | _ = case eq of λ ()
... | (Pool.cancelPending k₁) | _ | _ = case eq of λ ()
... | (Pool.joinPending k₁) | _ | _ = case eq of λ ()
... | Pool.openPool | just pending | _ = case eq of λ ()
... | Pool.openPool | nothing | false = case eq of λ ()
step-partition Pool.requestCancel c eq valid with Pool.phase c | Pool.remaining c in remainingEq
... | Pool.closing | k ∷ rest with lookup k (Pool.handles c)
...   | nothing = case eq of λ ()
...   | just (Pool.resultAvailable exit) = case just-injective eq of λ { refl → trans valid (cong (Pool.joined c ++_) (sym remainingEq)) }
...   | just Pool.bodyRunning = case just-injective eq of λ { refl → trans valid (cong (Pool.joined c ++_) (sym remainingEq)) }
...   | just (Pool.bodyReturned result) = case just-injective eq of λ { refl → trans valid (cong (Pool.joined c ++_) (sym remainingEq)) }
...   | just Pool.bodyUnwinding = case just-injective eq of λ { refl → trans valid (cong (Pool.joined c ++_) (sym remainingEq)) }
...   | just (Pool.deregisterPending exit) = case just-injective eq of λ { refl → trans valid (cong (Pool.joined c ++_) (sym remainingEq)) }
...   | just (Pool.deregistered exit) = case just-injective eq of λ { refl → trans valid (cong (Pool.joined c ++_) (sym remainingEq)) }
step-partition Pool.requestCancel c eq valid | Pool.openPool | _ = case eq of λ ()
step-partition Pool.requestCancel c eq valid | Pool.closedPool | _ = case eq of λ ()
step-partition Pool.requestCancel c eq valid | (Pool.cancelPending k₁) | _ = case eq of λ ()
step-partition Pool.requestCancel c eq valid | (Pool.joinPending k₁) | _ = case eq of λ ()
step-partition Pool.requestCancel c eq valid | Pool.closing | [] = case eq of λ ()
step-partition Pool.deliverCancel c eq valid with Pool.phase c
... | Pool.cancelPending k with lookup k (Pool.handles c)
...   | just Pool.bodyRunning = case just-injective eq of λ { refl → valid }
...   | nothing = case eq of λ ()
...   | just (Pool.bodyReturned value) = case eq of λ ()
...   | just Pool.bodyUnwinding = case eq of λ ()
...   | just (Pool.deregisterPending ex) = case eq of λ ()
...   | just (Pool.deregistered ex) = case eq of λ ()
...   | just (Pool.resultAvailable ex) = case eq of λ ()
step-partition Pool.deliverCancel c eq valid | Pool.openPool = case eq of λ ()
step-partition Pool.deliverCancel c eq valid | Pool.closing = case eq of λ ()
step-partition Pool.deliverCancel c eq valid | Pool.closedPool = case eq of λ ()
step-partition Pool.deliverCancel c eq valid | (Pool.joinPending k₁) = case eq of λ ()
step-partition Pool.join c eq valid with Pool.phase c
... | Pool.cancelPending k = join-partition k c eq valid
... | Pool.joinPending k = join-partition k c eq valid
... | Pool.openPool = case eq of λ ()
... | Pool.closing = case eq of λ ()
... | Pool.closedPool = case eq of λ ()
step-partition Pool.finishClose c eq valid with Pool.phase c | Pool.remaining c in restEq
... | Pool.closing | [] = case just-injective eq of λ { refl → trans valid (cong (Pool.joined c ++_) (sym restEq)) }
... | Pool.openPool | _ = case eq of λ ()
... | Pool.closedPool | _ = case eq of λ ()
... | (Pool.cancelPending k₁) | _ = case eq of λ ()
... | (Pool.joinPending k₁) | _ = case eq of λ ()
... | Pool.closing | _ ∷ _ = case eq of λ ()


-- Initialization and every enabled interleaving preserve the exact order cut.
exec-partition : ∀ {c actions d} → Pool.Executes c actions d → Partition c → Partition d
exec-partition Pool.done valid = valid
exec-partition (Pool.next {s = c} {a = a} advanced rest) valid = exec-partition rest (step-partition a c advanced valid)
from-initial : ∀ {actions c} → Pool.Executes Pool.initial actions c → Partition c
from-initial path = exec-partition path refl
in-suffix : ∀ {j : JobId} {ys : List JobId} xs → j ∈ ys → j ∈ (xs ++ ys)
in-suffix [] member = member
in-suffix (x ∷ xs) member = there (in-suffix xs member)
captured : ∀ {c d} → Partition c → (step : Join c d) → Join.current step ∈ Pool.snapshot c
captured {c} valid (actual-join current waiting (head-step result tail head available state)) =
 subst (current ∈_) (sym (trans valid (cong (Pool.joined c ++_) head))) (in-suffix (Pool.joined c) (here refl))

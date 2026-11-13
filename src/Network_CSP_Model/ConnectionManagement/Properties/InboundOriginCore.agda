{-# OPTIONS --guardedness #-}

-- Atomic admission-continuation effects. Only allocation and positive entry
-- selection create the two continuations whose earlier events must be recovered.
module ConnectionManagement.Properties.InboundOriginCore where

open import Data.Bool using (Bool; true; false)
open import Data.Bool.ListAction using (any)
open import Data.Nat using (suc; _≤?_; _∸_)
open import Data.List using (length; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (Σ; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Nullary using (yes; no; does)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; subst)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain using (WorkerId; EntryId; PromiseId; ident)
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.Properties.Entries using (lookup-put)
open import ConnectionManagement.Properties.Stores using (lookup-put-other)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.Rules.Server as Admission
import ConnectionManagement.Rules.CM as CM
import ConnectionManagement.Rules.Handshake as H

-- Other continuations require no pre-fork origin certificate.
relevant : S.AdmissionPC → Bool
relevant (S.selectEntry saved promise) = true
relevant (S.forkHandler saved promise entry) = true
relevant _ = false

-- An outer event must have one atomic admission writer; there is deliberately
-- no arbitrary sequential-composition constructor that could duplicate labels.
data Change (before after : S.State) : Set where
 same : S.admissions after ≡ S.admissions before → Change before after
 reset : ∀ worker row → relevant (S.pc row) ≡ false →
   S.admissions after ≡ put worker row (S.admissions before) → Change before after
 allocated : ∀ worker request saved →
   lookup worker (S.admissions before) ≡ just (S.admissionWorker request (S.prepare saved)) →
   S.admissions after ≡ put worker
     (S.admissionWorker request (S.selectEntry saved (ident (S.nextPromise before)))) (S.admissions before) → Change before after
 selected : ∀ worker request saved promise entry →
   lookup worker (S.admissions before) ≡ just (S.admissionWorker request (S.selectEntry saved promise)) →
   S.admissions after ≡ put worker (S.admissionWorker request (S.forkHandler saved promise entry)) (S.admissions before) → Change before after

-- Backward lookup evidence distinguishes an old continuation from its creator.
data SelectBefore (before after : S.State) (worker : WorkerId) (request : S.Admission) (saved : S.Lease) (promise : PromiseId) : Set where
 carried-select : lookup worker (S.admissions before) ≡ just (S.admissionWorker request (S.selectEntry saved promise)) → SelectBefore before after worker request saved promise
 new-allocation : promise ≡ ident (S.nextPromise before) →
   lookup worker (S.admissions before) ≡ just (S.admissionWorker request (S.prepare saved)) → SelectBefore before after worker request saved promise
data ForkBefore (before after : S.State) (worker : WorkerId) (request : S.Admission) (saved : S.Lease) (promise : PromiseId) (entry : EntryId) : Set where
 carried-fork : lookup worker (S.admissions before) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry)) → ForkBefore before after worker request saved promise entry
 new-selection : lookup worker (S.admissions before) ≡ just (S.admissionWorker request (S.selectEntry saved promise)) → ForkBefore before after worker request saved promise entry

-- A write to another worker retains the complete admission row.
prior-other : ∀ {before after} writer worker row target → worker ≢ writer →
  S.admissions after ≡ put writer row (S.admissions before) →
  lookup worker (S.admissions after) ≡ just target → lookup worker (S.admissions before) ≡ just target
prior-other {before} writer worker row target different changed found = trans
  (sym (lookup-put-other writer worker row (S.admissions before) different))
  (trans (sym (cong (lookup worker) changed)) found)
written-row : ∀ {before after} worker row target →
  S.admissions after ≡ put worker row (S.admissions before) →
  lookup worker (S.admissions after) ≡ just target → row ≡ target
written-row {before} worker row target changed found = just-injective (trans
  (sym (lookup-put worker row (S.admissions before)))
  (trans (sym (cong (lookup worker) changed)) found))

select-before : ∀ {before after worker request saved promise} → Change before after →
 lookup worker (S.admissions after) ≡ just (S.admissionWorker request (S.selectEntry saved promise)) →
 SelectBefore before after worker request saved promise
select-before {worker = worker} (same unchanged) found = carried-select (trans (sym (cong (lookup worker) unchanged)) found)
select-before {before} {after} {worker} {request} {saved} {promise} (reset writer row outside changed) found with worker ≟ writer
... | no different = carried-select (prior-other {before = before} {after = after} writer worker row (S.admissionWorker request (S.selectEntry saved promise)) different changed found)
... | yes refl with written-row {before = before} {after = after} worker row (S.admissionWorker request (S.selectEntry saved promise)) changed found
...   | refl = case outside of λ ()
select-before {before} {after} {worker} {request} {saved} {promise} (allocated writer req held owned changed) found with worker ≟ writer
... | no different = carried-select (prior-other {before = before} {after = after} writer worker (S.admissionWorker req (S.selectEntry held (ident (S.nextPromise before)))) (S.admissionWorker request (S.selectEntry saved promise)) different changed found)
... | yes refl with written-row {before = before} {after = after} worker (S.admissionWorker req (S.selectEntry held (ident (S.nextPromise before)))) (S.admissionWorker request (S.selectEntry saved promise)) changed found
...   | refl = new-allocation refl owned
select-before {before} {after} {worker} {request} {saved} {promise} (selected writer req held pid entry owned changed) found with worker ≟ writer
... | no different = carried-select (prior-other {before = before} {after = after} writer worker (S.admissionWorker req (S.forkHandler held pid entry)) (S.admissionWorker request (S.selectEntry saved promise)) different changed found)
... | yes refl with written-row {before = before} {after = after} worker (S.admissionWorker req (S.forkHandler held pid entry)) (S.admissionWorker request (S.selectEntry saved promise)) changed found
...   | ()

fork-before : ∀ {before after worker request saved promise entry} → Change before after →
 lookup worker (S.admissions after) ≡ just (S.admissionWorker request (S.forkHandler saved promise entry)) →
 ForkBefore before after worker request saved promise entry
fork-before {worker = worker} (same unchanged) found = carried-fork (trans (sym (cong (lookup worker) unchanged)) found)
fork-before {before} {after} {worker} {request} {saved} {promise} {entry} (reset writer row outside changed) found with worker ≟ writer
... | no different = carried-fork (prior-other {before = before} {after = after} writer worker row (S.admissionWorker request (S.forkHandler saved promise entry)) different changed found)
... | yes refl with written-row {before = before} {after = after} worker row (S.admissionWorker request (S.forkHandler saved promise entry)) changed found
...   | refl = case outside of λ ()
fork-before {before} {after} {worker} {request} {saved} {promise} {entry} (allocated writer req held owned changed) found with worker ≟ writer
... | no different = carried-fork (prior-other {before = before} {after = after} writer worker (S.admissionWorker req (S.selectEntry held (ident (S.nextPromise before)))) (S.admissionWorker request (S.forkHandler saved promise entry)) different changed found)
... | yes refl with written-row {before = before} {after = after} worker (S.admissionWorker req (S.selectEntry held (ident (S.nextPromise before)))) (S.admissionWorker request (S.forkHandler saved promise entry)) changed found
...   | ()
fork-before {before} {after} {worker} {request} {saved} {promise} {entry} (selected writer req held pid chosen owned changed) found with worker ≟ writer
... | no different = carried-fork (prior-other {before = before} {after = after} writer worker (S.admissionWorker req (S.forkHandler held pid chosen)) (S.admissionWorker request (S.forkHandler saved promise entry)) different changed found)
... | yes refl with written-row {before = before} {after = after} worker (S.admissionWorker req (S.forkHandler held pid chosen)) (S.admissionWorker request (S.forkHandler saved promise entry)) changed found
...   | refl = new-selection owned

-- Quiet source actions cannot write any admission continuation.
QuietMachine : M.Action → Set
QuietMachine (M.admissionStep _ _) = ⊥
QuietMachine (M.handshakeStep _ _) = ⊥
QuietMachine _ = ⊤
QuietOutbound : O.Action → Set
QuietOutbound (O.inbound _) = ⊥
QuietOutbound _ = ⊤

-- Origin-creating effects also identify their actual source operation.
Cause : ∀ {before after} → M.Action → Change before after → Set
Cause action (same unchanged) = ⊤
Cause action (reset worker row outside changed) = ⊤
Cause action (allocated worker request saved owned changed) = action ≡ M.admissionStep worker Admission.allocatePromise
Cause action (selected worker request saved promise entry owned changed) = action ≡ M.admissionStep worker Admission.chooseEntry
OutboundCause : ∀ {before after} → O.Action → Change before after → Set
OutboundCause action (same unchanged) = ⊤
OutboundCause action (reset worker row outside changed) = ⊤
OutboundCause action (allocated worker request saved owned changed) = action ≡ O.inbound (M.admissionStep worker Admission.allocatePromise)
OutboundCause action (selected worker request saved promise entry owned changed) = action ≡ O.inbound (M.admissionStep worker Admission.chooseEntry)

-- Result helpers keep ordinary row updates separate from origin creators.
private
 reset-result : ∀ {before after} (native : M.Action) worker row → relevant (S.pc row) ≡ false →
   S.admissions after ≡ put worker row (S.admissions before) → Σ (Change before after) (Cause native)
 reset-result native worker row outside changed = reset worker row outside changed , tt

 prefix-worker : ∀ act w a s {s′} → lookup w (S.admissions s) ≡ just a → Admission.stepWorker w a act s ≡ just s′ →
   Σ (Change s s′) (Cause (M.admissionStep w act))
 prefix-worker Admission.take w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.take w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.take w a@(S.admissionWorker r S.acquireMap) s owned eq with CM.takeMap w (S.cm s) in takenEq
 ... | nothing = case eq of λ ()
 ... | just (l , c′) = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.count l)) refl refl , tt }
 prefix-worker Admission.countLimit w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.countLimit w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.countLimit w a@(S.admissionWorker r (S.count l)) s owned eq with S.countIncoming (S.entries (S.cm s)) (S.savedMap l)
 ... | nothing = case eq of λ ()
 ... | just n with suc n ≤? S.hardLimit r
 ...   | yes _ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.prepare l)) refl refl , tt }
 ...   | no _ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.reject l S.hardLimitReached)) refl refl , tt }
 prefix-worker Admission.allocatePromise w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.allocatePromise w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.allocatePromise w a@(S.admissionWorker r (S.prepare l)) s owned eq = case just-injective eq of λ { refl → allocated w r l owned refl , refl }
 prefix-worker Admission.chooseEntry w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.chooseEntry w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.chooseEntry w a@(S.admissionWorker r (S.selectEntry l p)) s owned eq with CM.selectInbound l r (S.cm s) in selectedEq
 ... | nothing = case eq of λ ()
 ... | just CM.denied = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.reject l S.forbidden)) refl refl , tt }
 ... | just (CM.selected e c′) = case just-injective eq of λ { refl → selected w r l p e owned refl , refl }
 prefix-worker Admission.fork w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.fork w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.fork w a@(S.admissionWorker r (S.forkHandler l p e)) s owned eq with lookup (S.child r) (S.handlers s) in absent | lookup (S.child r) (S.admissions s)
 ... | just _ | _ = case eq of λ ()
 ... | nothing | just _ = case eq of λ ()
 ... | nothing | nothing = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.publish l p e)) refl refl , tt }

 prefix-worker Admission.failFork w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.failFork w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.failFork w a@(S.admissionWorker r (S.forkHandler l p e)) s owned eq = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.reject l S.forkFailed)) refl refl , tt }
 prefix-worker Admission.readCounters w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.readCounters w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.readCounters w a@(S.admissionWorker r (S.countPublished p e)) s owned eq with S.mapCell (S.cm s)
 ... | S.taken _ = case eq of λ ()
 ... | S.full m with S.countIncoming (S.entries (S.cm s)) m
 ...   | nothing = case eq of λ ()
 ...   | just _ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.awaitHandshake p e)) refl refl , tt }
 prefix-worker Admission.close w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.reject l reason)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.close w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.close w a@(S.admissionWorker r (S.closeSocket reason)) s owned eq = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.finished reason)) refl refl , tt }
 prefix-worker Admission.putMapBack w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.reject l S.forbidden)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.reject l S.bodyFailed)) s owned ()
 prefix-worker Admission.putMapBack w (S.admissionWorker r (S.reject l S.forkFailed)) s owned ()
 prefix-worker Admission.putMapBack w a@(S.admissionWorker r (S.publish l p e)) s owned eq with CM.putMap l (S.insertConnection (S.key r) e (S.savedMap l)) (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.countPublished p e)) refl refl , tt }
 prefix-worker Admission.putMapBack w a@(S.admissionWorker r (S.reject l S.hardLimitReached)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.closeSocket S.hardLimitReached)) refl refl , tt }
 prefix-worker Admission.restore w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.count l)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.prepare l)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.selectEntry l p)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.forkHandler l p e)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.publish l p e)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.restore w (S.admissionWorker r (S.reject l S.hardLimitReached)) s owned ()
 prefix-worker Admission.restore w a@(S.admissionWorker r (S.reject l S.forbidden)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.closeSocket S.forbidden)) refl refl , tt }
 prefix-worker Admission.restore w a@(S.admissionWorker r (S.reject l S.bodyFailed)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.closeSocket S.bodyFailed)) refl refl , tt }
 prefix-worker Admission.restore w a@(S.admissionWorker r (S.reject l S.forkFailed)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.closeSocket S.forkFailed)) refl refl , tt }


 prefix-worker Admission.restoreBody w a@(S.admissionWorker r (S.count l)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.closeSocket S.bodyFailed)) refl refl , tt }
 prefix-worker Admission.restoreBody w a@(S.admissionWorker r (S.prepare l)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.closeSocket S.bodyFailed)) refl refl , tt }
 prefix-worker Admission.restoreBody w a@(S.admissionWorker r (S.selectEntry l p)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.closeSocket S.bodyFailed)) refl refl , tt }
 prefix-worker Admission.restoreBody w a@(S.admissionWorker r (S.forkHandler l p e)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.closeSocket S.bodyFailed)) refl refl , tt }
 prefix-worker Admission.restoreBody w a@(S.admissionWorker r (S.publish l p e)) s owned eq with CM.restoreMap l (S.cm s) in putEq
 ... | nothing = case eq of λ ()
 ... | just c′ = case just-injective eq of λ { refl → reset w (S.admissionWorker r (S.closeSocket S.bodyFailed)) refl refl , tt }
 prefix-worker Admission.restoreBody w (S.admissionWorker r S.acquireMap) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.closeSocket reason)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.finished reason)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.countPublished p e)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.awaitHandshake p e)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.commitHandshake e result)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.countHandshake result)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.notifyInbound info)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.returnHandshake result)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.completedHandshake result)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r S.impossibleHandshake) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.reject l S.hardLimitReached)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.reject l S.forbidden)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.reject l S.bodyFailed)) s owned ()
 prefix-worker Admission.restoreBody w (S.admissionWorker r (S.reject l S.forkFailed)) s owned ()
 success-result : ∀ native w a e h f decision s →
   Σ (Change s (H.applySuccess w a e h f decision s)) (Cause native)
 success-result native w a e h f (H.update st provenance) s = reset-result native w (S.admissionWorker (S.request a) (S.countHandshake (S.connected (S.newConnectionInfo provenance (S.key (S.request a)) f h)))) refl refl
 success-result native w a e h f (H.retain provenance) s = reset-result native w (S.admissionWorker (S.request a) (S.countHandshake (S.connected (S.newConnectionInfo provenance (S.key (S.request a)) f h)))) refl refl
 success-result native w a e h f (H.disconnect reason) s = reset-result native w (S.admissionWorker (S.request a) (S.countHandshake (S.disconnected reason))) refl refl
 success-result native w a e h f H.impossible s = reset-result native w (S.admissionWorker (S.request a) S.impossibleHandshake) refl refl

 terminate-result : ∀ native w a e reason s {s′} → H.terminateResult w a e reason s ≡ just s′ →
   Σ (Change s s′) (Cause native)
 terminate-result native w a e reason s eq with lookup e (S.entries (S.cm s)) | S.mapCell (S.cm s)
 ... | nothing | _ = case eq of λ ()
 ... | just _ | S.taken _ = case eq of λ ()
 ... | just _ | S.full m with S.lookupConnection (S.key (S.request a)) m
 ...   | nothing = case just-injective eq of λ { refl → reset-result native w (S.admissionWorker (S.request a) (S.countHandshake (S.disconnected reason))) refl refl }
 ...   | just current with e ≟ current
 ...     | no _ = case just-injective eq of λ { refl → reset-result native w (S.admissionWorker (S.request a) (S.countHandshake (S.disconnected reason))) refl refl }
 ...     | yes _ = case just-injective eq of λ { refl → reset-result native w (S.admissionWorker (S.request a) (S.countHandshake (S.disconnected reason))) refl refl }

 handshake-worker : ∀ native act mode w a s {s′} → H.stepWorker mode w a act s ≡ just s′ →
   Σ (Change s s′) (Cause native)
 handshake-worker native H.readResult mode w (S.admissionWorker r S.acquireMap) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.count l)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.prepare l)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.selectEntry l p)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.forkHandler l p e)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.publish l p e)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.reject l reason)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.closeSocket reason)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.finished reason)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.countPublished p e)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.commitHandshake e result)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.countHandshake result)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.notifyInbound info)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.returnHandshake result)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r (S.completedHandshake result)) s ()
 handshake-worker native H.readResult mode w (S.admissionWorker r S.impossibleHandshake) s ()
 handshake-worker native H.readResult mode w a@(S.admissionWorker r (S.awaitHandshake p e)) s eq with lookup p (S.handshakeResults s)
 ... | nothing = case eq of λ ()
 ... | just result = case just-injective eq of λ { refl → reset-result native w (S.admissionWorker r (S.commitHandshake e result)) refl refl }
 handshake-worker native H.commitResult mode w (S.admissionWorker r S.acquireMap) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.count l)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.prepare l)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.selectEntry l p)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.forkHandler l p e)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.publish l p e)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.reject l reason)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.closeSocket reason)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.finished reason)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.countPublished p e)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.awaitHandshake p e)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.countHandshake result)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.notifyInbound info)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.returnHandshake result)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r (S.completedHandshake result)) s ()
 handshake-worker native H.commitResult mode w (S.admissionWorker r S.impossibleHandshake) s ()
 handshake-worker native H.commitResult mode w a@(S.admissionWorker r (S.commitHandshake e (S.negotiated h f))) s eq with lookup e (S.entries (S.cm s))
 ... | nothing = case eq of λ ()
 ... | just st = case just-injective eq of λ { refl → success-result native w a e h f (H.decideSuccess r h f st) s }
 handshake-worker native H.commitResult mode w a@(S.admissionWorker r (S.commitHandshake e S.query)) s eq = terminate-result native w a e S.handshakeQuery s eq
 handshake-worker native H.commitResult mode w a@(S.admissionWorker r (S.commitHandshake e (S.handlerError cls err))) s eq = terminate-result native w a e (S.handshakeError cls err) s eq
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r S.acquireMap) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.count l)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.prepare l)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.selectEntry l p)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.forkHandler l p e)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.publish l p e)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.reject l reason)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.closeSocket reason)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.finished reason)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.countPublished p e)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.awaitHandshake p e)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.commitHandshake e result)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.notifyInbound info)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.returnHandshake result)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r (S.completedHandshake result)) s ()
 handshake-worker native H.readResultCounters mode w (S.admissionWorker r S.impossibleHandshake) s ()
 handshake-worker native H.readResultCounters mode w a@(S.admissionWorker r (S.countHandshake result)) s eq with S.mapCell (S.cm s)
 ... | S.taken _ = case eq of λ ()
 ... | S.full m with S.countIncoming (S.entries (S.cm s)) m
 ...   | nothing = case eq of λ ()
 ...   | just _ with result | mode
 ...     | S.connected info | S.responderMode = case just-injective eq of λ { refl → reset-result native w (S.admissionWorker r (S.notifyInbound info)) refl refl }
 ...     | S.connected info | S.noResponderMode = case just-injective eq of λ { refl → reset-result native w (S.admissionWorker r (S.returnHandshake (S.connected info))) refl refl }
 ...     | S.disconnected reason | _ = case just-injective eq of λ { refl → reset-result native w (S.admissionWorker r (S.returnHandshake (S.disconnected reason))) refl refl }
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r S.acquireMap) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.count l)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.prepare l)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.selectEntry l p)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.forkHandler l p e)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.publish l p e)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.reject l reason)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.closeSocket reason)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.finished reason)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.countPublished p e)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.awaitHandshake p e)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.commitHandshake e result)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.countHandshake result)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.returnHandshake result)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r (S.completedHandshake result)) s ()
 handshake-worker native H.enqueueInbound mode w (S.admissionWorker r S.impossibleHandshake) s ()
 handshake-worker native H.enqueueInbound mode w a@(S.admissionWorker r (S.notifyInbound info)) s eq with suc (length (S.inboundInfo s)) ≤? 100
 ... | no _ = case eq of λ ()
 ... | yes _ = case just-injective eq of λ { refl → reset-result native w (S.admissionWorker r (S.returnHandshake (S.connected info))) refl refl }
 handshake-worker native H.returnResult mode w (S.admissionWorker r S.acquireMap) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.count l)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.prepare l)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.selectEntry l p)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.forkHandler l p e)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.publish l p e)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.reject l reason)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.closeSocket reason)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.finished reason)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.countPublished p e)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.awaitHandshake p e)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.commitHandshake e result)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.countHandshake result)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.notifyInbound info)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r (S.completedHandshake result)) s ()
 handshake-worker native H.returnResult mode w (S.admissionWorker r S.impossibleHandshake) s ()
 handshake-worker native H.returnResult mode w a@(S.admissionWorker r (S.returnHandshake result)) s eq = case just-injective eq of λ { refl → reset-result native w (S.admissionWorker r (S.completedHandshake result)) refl refl }



-- Primitive dispatcher lifting retains the exact source action as its cause.
admission-result : ∀ worker action c {d} → M.advance (M.admissionStep worker action) c ≡ just d →
 Σ (Change (M.world c) (M.world d)) (Cause (M.admissionStep worker action))
admission-result worker action c eq with lookup worker (S.admissions (M.world c)) in owned
... | nothing = case eq of λ ()
... | just row with Admission.stepWorker worker row action (M.world c) in actual
...   | nothing = case eq of λ ()
...   | just next with just-injective eq
...     | refl = prefix-worker action worker row (M.world c) owned actual
handshake-result : ∀ worker action c {d} → M.advance (M.handshakeStep worker action) c ≡ just d →
 Σ (Change (M.world c) (M.world d)) (Cause (M.handshakeStep worker action))
handshake-result worker action c eq with lookup worker (S.admissions (M.world c))
... | nothing = case eq of λ ()
... | just row with H.stepWorker (M.responder c) worker row action (M.world c) in actual
...   | nothing = case eq of λ ()
...   | just next with just-injective eq
...     | refl = handshake-worker (M.handshakeStep worker action) action (M.responder c) worker row (M.world c) actual

import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as Release
import ConnectionManagement.Rules.InboundRelease as InRelease
import ConnectionManagement.Rules.Pruning as Prune
import ConnectionManagement.Rules.Cleanup as Cleanup
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Rules.HandlerLifecycle as Life
import ConnectionManagement.Rules.IGRegistration as IG

private
 module OrdinaryQuiet where
  open import Data.Bool using (true; false)
  open import Data.Bool.ListAction using (any)
  open import Data.List using (List; []; _∷_)
  open import Data.Maybe using (just; nothing)
  open import Data.Maybe.Properties using (just-injective)
  open import Data.Product using (_,_)
  open import Relation.Nullary using (yes; no; does)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; trans)
  open import Function using (case_of_)
  open import Class.DecEq using (_≟_)
  open import ConnectionManagement.Domain using (entry; worker)
  open import ConnectionManagement.Store using (lookup)
  open import ConnectionManagement.State using (admission; admissions; cleanupAcquire; cleanupClose; cleanupCount; cleanupDone; cleanupFinalize; cleanupPublish; cleanupRestore; cleanupSelect; cleanupWaiting; cleanups; cm; countIncoming; entries; full; handlerEntry; handlerPromise; handlers; handshakeResults; mapCell; owner; pc; promises; result; savedMap; state; taken)
  import ConnectionManagement.Rules.Cleanup as Cleanup
  import ConnectionManagement.Rules.CM as CM
  import ConnectionManagement.Rules.Handshake as H
  import ConnectionManagement.Rules.InboundRelease as Release
  import ConnectionManagement.Rules.Pruning as Prune

  -- Selection modifies entry/cleanup state, never admission continuations.
  select-admissions : ∀ w h l decision s →
    admissions (Cleanup.selectCleanup w h l decision s) ≡ admissions s
  select-admissions w h l Cleanup.terminateAndPurge s = refl
  select-admissions w h l Cleanup.purgeOnly s = refl
  select-admissions w h l (Cleanup.waitBeforePurge st) s = refl

  worker-admissions : ∀ action w h p s {s′} → Cleanup.stepWorker w h p action s ≡ just s′ →
    admissions s′ ≡ admissions s
  worker-admissions Cleanup.takeCleanupMap w h (cleanupSelect l) s ()
  worker-admissions Cleanup.takeCleanupMap w h (cleanupClose l m tail) s ()
  worker-admissions Cleanup.takeCleanupMap w h (cleanupPublish l m tail) s ()
  worker-admissions Cleanup.takeCleanupMap w h (cleanupRestore l err) s ()
  worker-admissions Cleanup.takeCleanupMap w h (cleanupWaiting st) s ()
  worker-admissions Cleanup.takeCleanupMap w h (cleanupFinalize st outcome) s ()
  worker-admissions Cleanup.takeCleanupMap w h (cleanupCount outcome) s ()
  worker-admissions Cleanup.takeCleanupMap w h (cleanupDone outcome) s ()
  worker-admissions Cleanup.takeCleanupMap w h cleanupAcquire s eq with CM.takeMap w (cm s) in takenEq
  ... | nothing = case eq of λ ()
  ... | just (l , c′) = subst (λ t → admissions t ≡ admissions s) (just-injective eq) refl
  worker-admissions Cleanup.selectCleanupEntry w h cleanupAcquire s ()
  worker-admissions Cleanup.selectCleanupEntry w h (cleanupClose l m tail) s ()
  worker-admissions Cleanup.selectCleanupEntry w h (cleanupPublish l m tail) s ()
  worker-admissions Cleanup.selectCleanupEntry w h (cleanupRestore l err) s ()
  worker-admissions Cleanup.selectCleanupEntry w h (cleanupWaiting st) s ()
  worker-admissions Cleanup.selectCleanupEntry w h (cleanupFinalize st outcome) s ()
  worker-admissions Cleanup.selectCleanupEntry w h (cleanupCount outcome) s ()
  worker-admissions Cleanup.selectCleanupEntry w h (cleanupDone outcome) s ()
  worker-admissions Cleanup.selectCleanupEntry w h (cleanupSelect l) s eq with mapCell (cm s)
  ... | full _ = case eq of λ ()
  ... | taken owner with owner ≟ w
  ...   | no _ = case eq of λ ()
  ...   | yes _ with lookup (handlerEntry h) (entries (cm s)) in found
  ...     | nothing = case eq of λ ()
  ...     | just st = subst (λ t → admissions t ≡ admissions s) (just-injective eq) (select-admissions w h l (Cleanup.decideCleanup st) s)
  worker-admissions Cleanup.closeHandlerSocket w h cleanupAcquire s ()
  worker-admissions Cleanup.closeHandlerSocket w h (cleanupSelect l) s ()
  worker-admissions Cleanup.closeHandlerSocket w h (cleanupPublish l m tail) s ()
  worker-admissions Cleanup.closeHandlerSocket w h (cleanupRestore l err) s ()
  worker-admissions Cleanup.closeHandlerSocket w h (cleanupWaiting st) s ()
  worker-admissions Cleanup.closeHandlerSocket w h (cleanupFinalize st outcome) s ()
  worker-admissions Cleanup.closeHandlerSocket w h (cleanupCount outcome) s ()
  worker-admissions Cleanup.closeHandlerSocket w h (cleanupDone outcome) s ()
  worker-admissions Cleanup.closeHandlerSocket w h (cleanupClose l m tail) s eq = subst (λ t → admissions t ≡ admissions s) (just-injective eq) refl
  worker-admissions (Cleanup.failSocketClose error) w h cleanupAcquire s ()
  worker-admissions (Cleanup.failSocketClose error) w h (cleanupSelect l) s ()
  worker-admissions (Cleanup.failSocketClose error) w h (cleanupPublish l m tail) s ()
  worker-admissions (Cleanup.failSocketClose error) w h (cleanupRestore l err) s ()
  worker-admissions (Cleanup.failSocketClose error) w h (cleanupWaiting st) s ()
  worker-admissions (Cleanup.failSocketClose error) w h (cleanupFinalize st outcome) s ()
  worker-admissions (Cleanup.failSocketClose error) w h (cleanupCount outcome) s ()
  worker-admissions (Cleanup.failSocketClose error) w h (cleanupDone outcome) s ()
  worker-admissions (Cleanup.failSocketClose error) w h (cleanupClose l m tail) s eq = subst (λ t → admissions t ≡ admissions s) (just-injective eq) refl
  worker-admissions Cleanup.publishCleanupMap w h cleanupAcquire s ()
  worker-admissions Cleanup.publishCleanupMap w h (cleanupSelect l) s ()
  worker-admissions Cleanup.publishCleanupMap w h (cleanupClose l m tail) s ()
  worker-admissions Cleanup.publishCleanupMap w h (cleanupRestore l err) s ()
  worker-admissions Cleanup.publishCleanupMap w h (cleanupWaiting st) s ()
  worker-admissions Cleanup.publishCleanupMap w h (cleanupFinalize st outcome) s ()
  worker-admissions Cleanup.publishCleanupMap w h (cleanupCount outcome) s ()
  worker-admissions Cleanup.publishCleanupMap w h (cleanupDone outcome) s ()
  worker-admissions Cleanup.publishCleanupMap w h (cleanupPublish l m tail) s eq with CM.putMap l m (cm s) in putEq
  ... | nothing = case eq of λ ()
  ... | just c′ = subst (λ t → admissions t ≡ admissions s) (just-injective eq) refl
  worker-admissions Cleanup.restoreCleanupMap w h cleanupAcquire s ()
  worker-admissions Cleanup.restoreCleanupMap w h (cleanupSelect l) s ()
  worker-admissions Cleanup.restoreCleanupMap w h (cleanupClose l m tail) s ()
  worker-admissions Cleanup.restoreCleanupMap w h (cleanupPublish l m tail) s ()
  worker-admissions Cleanup.restoreCleanupMap w h (cleanupWaiting st) s ()
  worker-admissions Cleanup.restoreCleanupMap w h (cleanupFinalize st outcome) s ()
  worker-admissions Cleanup.restoreCleanupMap w h (cleanupCount outcome) s ()
  worker-admissions Cleanup.restoreCleanupMap w h (cleanupDone outcome) s ()
  worker-admissions Cleanup.restoreCleanupMap w h (cleanupRestore l err) s eq with CM.putMap l (savedMap l) (cm s) in putEq
  ... | nothing = case eq of λ ()
  ... | just c′ = subst (λ t → admissions t ≡ admissions s) (just-injective eq) refl
  worker-admissions Cleanup.timeWaitElapsed w h cleanupAcquire s ()
  worker-admissions Cleanup.timeWaitElapsed w h (cleanupSelect l) s ()
  worker-admissions Cleanup.timeWaitElapsed w h (cleanupClose l m tail) s ()
  worker-admissions Cleanup.timeWaitElapsed w h (cleanupPublish l m tail) s ()
  worker-admissions Cleanup.timeWaitElapsed w h (cleanupRestore l err) s ()
  worker-admissions Cleanup.timeWaitElapsed w h (cleanupFinalize st outcome) s ()
  worker-admissions Cleanup.timeWaitElapsed w h (cleanupCount outcome) s ()
  worker-admissions Cleanup.timeWaitElapsed w h (cleanupDone outcome) s ()
  worker-admissions Cleanup.timeWaitElapsed w h (cleanupWaiting st) s eq = subst (λ t → admissions t ≡ admissions s) (just-injective eq) refl
  worker-admissions (Cleanup.interruptTimeWait error) w h cleanupAcquire s ()
  worker-admissions (Cleanup.interruptTimeWait error) w h (cleanupSelect l) s ()
  worker-admissions (Cleanup.interruptTimeWait error) w h (cleanupClose l m tail) s ()
  worker-admissions (Cleanup.interruptTimeWait error) w h (cleanupPublish l m tail) s ()
  worker-admissions (Cleanup.interruptTimeWait error) w h (cleanupRestore l err) s ()
  worker-admissions (Cleanup.interruptTimeWait error) w h (cleanupFinalize st outcome) s ()
  worker-admissions (Cleanup.interruptTimeWait error) w h (cleanupCount outcome) s ()
  worker-admissions (Cleanup.interruptTimeWait error) w h (cleanupDone outcome) s ()
  worker-admissions (Cleanup.interruptTimeWait error) w h (cleanupWaiting st) s eq = subst (λ t → admissions t ≡ admissions s) (just-injective eq) refl
  worker-admissions Cleanup.finishTimeWait w h cleanupAcquire s ()
  worker-admissions Cleanup.finishTimeWait w h (cleanupSelect l) s ()
  worker-admissions Cleanup.finishTimeWait w h (cleanupClose l m tail) s ()
  worker-admissions Cleanup.finishTimeWait w h (cleanupPublish l m tail) s ()
  worker-admissions Cleanup.finishTimeWait w h (cleanupRestore l err) s ()
  worker-admissions Cleanup.finishTimeWait w h (cleanupWaiting st) s ()
  worker-admissions Cleanup.finishTimeWait w h (cleanupCount outcome) s ()
  worker-admissions Cleanup.finishTimeWait w h (cleanupDone outcome) s ()
  worker-admissions Cleanup.finishTimeWait w h (cleanupFinalize st outcome) s eq with mapCell (cm s)
  ... | taken _ = case eq of λ ()
  ... | full m with lookup (handlerEntry h) (entries (cm s)) in found
  ...   | nothing = case eq of λ ()
  ...   | just _ = subst (λ t → admissions t ≡ admissions s) (just-injective eq)
    refl
  worker-admissions Cleanup.readCleanupCounters w h cleanupAcquire s ()
  worker-admissions Cleanup.readCleanupCounters w h (cleanupSelect l) s ()
  worker-admissions Cleanup.readCleanupCounters w h (cleanupClose l m tail) s ()
  worker-admissions Cleanup.readCleanupCounters w h (cleanupPublish l m tail) s ()
  worker-admissions Cleanup.readCleanupCounters w h (cleanupRestore l err) s ()
  worker-admissions Cleanup.readCleanupCounters w h (cleanupWaiting st) s ()
  worker-admissions Cleanup.readCleanupCounters w h (cleanupFinalize st outcome) s ()
  worker-admissions Cleanup.readCleanupCounters w h (cleanupDone outcome) s ()
  worker-admissions Cleanup.readCleanupCounters w h (cleanupCount outcome) s eq with mapCell (cm s)
  ... | taken _ = case eq of λ ()
  ... | full m with countIncoming (entries (cm s)) m
  ...   | nothing = case eq of λ ()
  ...   | just _ = subst (λ t → admissions t ≡ admissions s) (just-injective eq) refl

  -- Lift every cleanup worker rule through lookup and the actual dispatcher.
  cleanup-admissions : ∀ w a s {s′} → Cleanup.stepCleanup w a s ≡ just s′ → admissions s′ ≡ admissions s
  cleanup-admissions w a s eq with lookup w (handlers s) | lookup w (cleanups s)
  ... | nothing | _ = case eq of λ ()
  ... | just _ | nothing = case eq of λ ()
  ... | just h | just pc = worker-admissions a w h pc s eq

  -- The explicit handler-exit boundary only adds its cleanup PC.
  begin-cleanup-admissions : ∀ w s {t} → Cleanup.beginCleanupBoundary w s ≡ just t →
    admissions t ≡ admissions s
  begin-cleanup-admissions w s eq with lookup w (handlers s) | lookup w (cleanups s)
  ... | nothing | _ = case eq of λ ()
  ... | just _ | just _ = case eq of λ ()
  ... | just h | nothing = case just-injective eq of λ { refl → refl }

  -- Actual publication may report a duplicate write; the written result case is
  -- the only branch returning a shared state and it changes only result storage.
  publication-admissions : ∀ w result s {t} → H.publishBoundary w result s ≡ just (H.published t) →
    admissions t ≡ admissions s
  publication-admissions w result s eq with lookup w (handlers s) | lookup w (cleanups s)
  ... | nothing | _ = case eq of λ ()
  ... | just _ | just _ = case eq of λ ()
  ... | just h | nothing with any (λ p → does (p ≟ handlerPromise h)) (promises s)
  ...   | false = case eq of λ ()
  ...   | true with lookup (handlerPromise h) (handshakeResults s)
  ...     | just _ = case eq of λ ()
  ...     | nothing = case just-injective eq of λ { refl → refl }

  -- Atomic CM entry writes leave the admission table untouched.
  edit-admissions : ∀ edit s {t} → Release.applyEdit edit s ≡ just t →
    admissions t ≡ admissions s
  edit-admissions nothing s eq = case just-injective eq of λ { refl → refl }
  edit-admissions (just (e , st)) s eq with lookup e (entries (cm s))
  ... | nothing = case eq of λ ()
  ... | just old = case just-injective eq of λ { refl → refl }
  edits-admissions : ∀ edits s {t} → Prune.applyEdits edits s ≡ just t →
    admissions t ≡ admissions s
  edits-admissions [] s eq = case just-injective eq of λ { refl → refl }
  edits-admissions (edit ∷ edits) s eq with Release.applyEdit (just edit) s in edited
  ... | nothing = case eq of λ ()
  ... | just mid = trans (edits-admissions edits mid eq) (edit-admissions (just edit) s edited)

open OrdinaryQuiet using (cleanup-admissions; begin-cleanup-admissions; publication-admissions; edit-admissions; edits-admissions)
private
 module AcquireQuiet where
  open import Data.Bool using (true; false)
  open import Data.Maybe using (just; nothing)
  open import Data.Maybe.Properties using (just-injective)
  open import Data.Product using (_×_; _,_; proj₂)
  open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
  open import Function using (case_of_)
  open import ConnectionManagement.Domain using (entry; ident; inbound; local; outbound; socket)
  open import ConnectionManagement.State using (State; admissions; admitting; child; closeUncertain; closed; cm; commitHandshake; connected; count; countIncoming; descriptor; disconnected; duplexActive; entries; forkHandler; full; handlerError; handlerSocket; handlerStart; handlers; handling; handshakeError; handshakeQuery; handshakeResults; inboundActive; inboundIdle; inboundInfo; mapCell; negotiated; newConnection; newConnectionInfo; nextEntry; nextPromise; noResponderMode; outboundDup; outboundIdle; outboundUni; owner; pc; peer; query; reservedOutbound; responderMode; result; selectEntry; socketRef; sockets; state; taken; terminated; terminating; unnegotiated)
  open import ConnectionManagement.Store using (lookup; put)
  import ConnectionManagement.Rules.OutboundAcquire as A
  import ConnectionManagement.Rules.OutboundCases as C
  import ConnectionManagement.Rules.InformationChannel as Queue

  -- Every outbound-acquire write targets a different component of the shared state.
  Effects : State → State → Set
  Effects s s′ = admissions s′ ≡ admissions s
  identity : ∀ s → Effects s s
  identity s = refl
  entry-write : ∀ e st s → Effects s
    (record s { cm = record (cm s) { entries = put e st (entries (cm s)) } })
  entry-write e st s = refl
  socket-write : ∀ sock owner s → Effects s (record s { sockets = put sock owner (sockets s) })
  socket-write sock owner s = refl
  fork-write : ∀ child descriptor s → lookup child (handlers s) ≡ nothing → Effects s
    (record s { handlers = put child descriptor (handlers s)
              ; sockets = put (handlerSocket descriptor) (handling child) (sockets s) })
  fork-write child descriptor s absent = refl

  -- Transport store effects through an exact pair result.
  result-retains : ∀ {before} {pair pair′ : A.Frame × State} → just pair ≡ just pair′ →
    Effects before (proj₂ pair) → Effects before (proj₂ pair′)
  result-retains {before} eq = subst (λ pair → Effects before (proj₂ pair)) (just-injective eq)

  -- Reuse decisions retain immutable lookups and allocated resource identities.
  choice-retains : ∀ first e d f s {out} → A.applyChoice first e d f s ≡ just out → Effects s (proj₂ out)
  choice-retains first e C.retry f s ()
  choice-retains first e (C.waitInbound k) f s eq = result-retains {before = s} eq (identity s)
  choice-retains true e (C.refuse err) f s eq = result-retains {before = s} eq (identity s)
  choice-retains false e (C.refuse err) f s eq = result-retains {before = s} eq (identity s)
  choice-retains first e (C.gone result) f s eq = result-retains {before = s} eq (identity s)
  choice-retains true e (C.reuse st result) f s eq = result-retains {before = s} eq (entry-write e st s)
  choice-retains false e (C.reuse st result) f s eq = result-retains {before = s} eq (entry-write e st s)

  -- Reservation either reuses a branch or adds a fresh entry.
  known-retains : ∀ chosen m f s {out} → A.selectKnown chosen m f s ≡ just out → Effects s (proj₂ out)
  known-retains (just e) m f s eq with lookup e (entries (cm s)) in found
  ... | nothing = case eq of λ ()
  ... | just st = choice-retains true e (C.acquireCase st) f s eq
  known-retains nothing m f s eq with A.provenance (A.req f)
  ... | inbound = result-retains {before = s} eq (identity s)
  ... | outbound with lookup (ident (nextEntry (cm s))) (entries (cm s))
  ...   | just _ = case eq of λ ()
  ...   | nothing = result-retains {before = s} eq
    (entry-write (ident (nextEntry (cm s))) reservedOutbound s)

  -- Selection preserves effects of the actual guarded reservation branch.
  selection-retains : ∀ chosen f s {out} → A.selectEntry chosen f s ≡ just out → Effects s (proj₂ out)
  selection-retains chosen f s eq with mapCell (cm s)
  ... | taken _ = case eq of λ ()
  ... | full m with A.validSelection (A.peer (A.req f)) chosen m
  ...   | false = case eq of λ ()
  ...   | true = known-retains chosen m f s eq

  -- Handshake success changes entries and notification queues only.
  success-retains : ∀ mode e k h flow f s {out} → A.commitSuccess mode e k h flow f s ≡ just out → Effects s (proj₂ out)
  success-retains mode e k h flow f s eq with lookup e (entries (cm s))
  ... | nothing = case eq of λ ()
  ... | just st with C.successCase k (A.child (A.req f)) h flow st
  ...   | C.decision replacement notify (C.raised err) = result-retains {before = s} eq (identity s)
  ...   | C.decision replacement false (C.connected k′ flow′ h′) with replacement
  ...     | nothing = result-retains {before = s} eq (identity s)
  ...     | just replacement′ = result-retains {before = s} eq (entry-write e replacement′ s)
  success-retains mode e k h flow f s eq | just st | C.decision replacement false (C.disconnected k′ reason) with replacement
  ... | nothing = result-retains {before = s} eq (identity s)
  ... | just replacement′ = result-retains {before = s} eq (entry-write e replacement′ s)
  success-retains noResponderMode e k h flow f s eq | just st | C.decision replacement true result with result | replacement
  ... | C.connected _ _ _ | nothing = result-retains {before = s} eq (identity s)
  ... | C.connected _ _ _ | just replacement′ = result-retains {before = s} eq (entry-write e replacement′ s)
  ... | C.disconnected _ _ | nothing = result-retains {before = s} eq (identity s)
  ... | C.disconnected _ _ | just replacement′ = result-retains {before = s} eq (entry-write e replacement′ s)
  ... | C.raised _ | _ = result-retains {before = s} eq (identity s)
  success-retains responderMode e k h flow f s eq | just st | C.decision replacement true result
    with Queue.writeMessage (newConnection (newConnectionInfo outbound k flow h)) (inboundInfo s) in enqueued | result | replacement
  ... | nothing | C.connected _ _ _ | _ rewrite enqueued = case eq of λ ()
  ... | nothing | C.disconnected _ _ | _ rewrite enqueued = case eq of λ ()
  ... | just queue | C.connected _ _ _ | nothing rewrite enqueued = result-retains {before = s} eq (identity s)
  ... | just queue | C.connected _ _ _ | just replacement′ rewrite enqueued = result-retains {before = s} eq (entry-write e replacement′ s)
  ... | just queue | C.disconnected _ _ | nothing rewrite enqueued = result-retains {before = s} eq (identity s)
  ... | just queue | C.disconnected _ _ | just replacement′ rewrite enqueued = result-retains {before = s} eq (entry-write e replacement′ s)
  ... | _ | C.raised _ | _ = result-retains {before = s} eq (identity s)

  -- Error/query cleanup retains historical resources and immutable lookups.
  error-retains : ∀ e k reason f s {out} → A.commitError e k reason f s ≡ just out → Effects s (proj₂ out)
  error-retains e k reason f s eq with lookup e (entries (cm s)) | mapCell (cm s)
  ... | nothing | _ = case eq of λ ()
  ... | just _ | taken _ = case eq of λ ()
  ... | just st | full m = result-retains {before = s} eq (identity s)

  -- Exhaust every successful action without a savedFrame-validity premise.
  step-admissions : ∀ caller mode action f s {out} → A.step caller mode action f s ≡ just out → Effects s (proj₂ out)
  step-admissions caller mode (A.select chosen) f s eq with A.pc f
  ... | A.selecting = selection-retains chosen f s eq
  step-admissions caller mode (A.select chosen) f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.openSocket e p) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.configureSocket e p) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.bindSocket e p) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.connectSocket e p) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.localAddress e p) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.closeError e err′) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode (A.select chosen) f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq with A.pc f | mapCell (cm s)
  ... | A.count next | full m with countIncoming (entries (cm s)) m
  ...   | nothing = case eq of λ ()
  ...   | just _ = result-retains {before = s} eq (identity s)
  step-admissions caller mode A.readCounters f s eq | A.selecting | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.complete result) | _ = case eq of λ ()
  step-admissions caller mode A.readCounters f s eq | (A.count p) | taken w = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq with A.pc f
  ... | A.allocatePromise e with lookup (ident (nextPromise s)) (handshakeResults s)
  ...   | just _ = case eq of λ ()
  ...   | nothing = result-retains {before = s} eq (identity s)
  step-admissions caller mode A.newPromise f s eq | A.selecting = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.openSocket e p) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.configureSocket e p) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.bindSocket e p) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.connectSocket e p) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.localAddress e p) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.commitResult e k result) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.closeError e err′) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode A.newPromise f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode A.openOK f s eq with A.pc f | lookup (A.socketRef (A.req f)) (sockets s)
  ... | A.openSocket e p | nothing = result-retains {before = s} eq (socket-write (A.socketRef (A.req f)) (admitting caller) s)
  step-admissions caller mode A.openOK f s eq | A.selecting | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.count p) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.complete result) | _ = case eq of λ ()
  step-admissions caller mode A.openOK f s eq | (A.openSocket e p) | just sock = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq with A.pc f | A.bindLocal (A.req f)
  ... | A.configureSocket e p | nothing = result-retains {before = s} eq (identity s)
  ... | A.configureSocket e p | just _ = result-retains {before = s} eq (identity s)
  step-admissions caller mode A.configureOK f s eq | A.selecting | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.count p) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-admissions caller mode A.configureOK f s eq | (A.complete result) | _ = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq with A.pc f
  ... | A.bindSocket e p = result-retains {before = s} eq (identity s)
  step-admissions caller mode A.bindOK f s eq | A.selecting = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.allocatePromise e) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.openSocket e p) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.configureSocket e p) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.connectSocket e p) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.localAddress e p) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.commitResult e k result) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.closeError e err′) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode A.bindOK f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq with A.pc f
  ... | A.connectSocket e p = result-retains {before = s} eq (identity s)
  step-admissions caller mode A.connectOK f s eq | A.selecting = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.allocatePromise e) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.openSocket e p) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.configureSocket e p) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.bindSocket e p) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.localAddress e p) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.commitResult e k result) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.closeError e err′) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode A.connectOK f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq with A.pc f
  ... | A.localAddress e p = result-retains {before = s} eq (identity s)
  step-admissions caller mode (A.gotLocal local) f s eq | A.selecting = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.openSocket e p) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.configureSocket e p) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.bindSocket e p) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.connectSocket e p) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.closeError e err′) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode (A.gotLocal local) f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq with A.pc f | mapCell (cm s)
  ... | A.updateAddress e p k | full m with A.updateLocal k m
  ...   | true , m′ = result-retains {before = s} eq (identity s)
  ...   | false , m′ = result-retains {before = s} eq (identity s)
  step-admissions caller mode A.updateLocalAddress f s eq | A.selecting | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.count p) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.complete result) | _ = case eq of λ ()
  step-admissions caller mode A.updateLocalAddress f s eq | (A.updateAddress e p k) | taken w = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq with A.pc f | lookup (A.child (A.req f)) (handlers s) in absent
  ... | A.forkHandler e p k | nothing = result-retains {before = s} eq (fork-write (A.child (A.req f)) (handlerStart e (A.socketRef (A.req f)) p k) s absent)
  step-admissions caller mode A.forkOK f s eq | A.selecting | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.count p) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.removeError e err′) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.complete result) | _ = case eq of λ ()
  step-admissions caller mode A.forkOK f s eq | (A.forkHandler e p k) | just h = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq with A.pc f
  ... | A.connectedCommit e p k with lookup e (entries (cm s)) in found
  ...   | nothing = case eq of λ ()
  ...   | just reservedOutbound = result-retains {before = s} eq
    (entry-write e (unnegotiated outbound k (A.child (A.req f))) s)
  ...   | just (unnegotiated inbound _ _) = result-retains {before = s} eq
    (entry-write e (unnegotiated outbound k (A.child (A.req f))) s)
  ...   | just old@(unnegotiated outbound _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(outboundUni _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(outboundDup _ _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(outboundIdle _ _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(inboundIdle _ _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(inboundActive _ _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(duplexActive _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(terminating _ _ _) = result-retains {before = s} eq (identity s)
  ...   | just old@(terminated _) = result-retains {before = s} eq (identity s)
  step-admissions caller mode A.commitConnected f s eq | A.selecting = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.allocatePromise e) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.openSocket e p) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.configureSocket e p) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.bindSocket e p) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.connectSocket e p) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.localAddress e p) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.commitResult e k result) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.closeError e err′) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode A.commitConnected f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq with A.pc f
  ... | A.awaitResult e p k with lookup p (handshakeResults s)
  ...   | nothing = case eq of λ ()
  ...   | just result = result-retains {before = s} eq (identity s)
  step-admissions caller mode A.readResult f s eq | A.selecting = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.allocatePromise e) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.openSocket e p) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.configureSocket e p) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.bindSocket e p) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.connectSocket e p) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.localAddress e p) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.commitResult e k result) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.closeError e err′) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode A.readResult f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq with A.pc f
  ... | A.commitResult e k (negotiated h flow) = success-retains mode e k h flow f s eq
  ... | A.commitResult e k query = error-retains e k handshakeQuery f s eq
  ... | A.commitResult e k (handlerError cls err) = error-retains e k (handshakeError cls err) f s eq
  step-admissions caller mode A.commitHandshake f s eq | A.selecting = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.allocatePromise e) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.openSocket e p) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.configureSocket e p) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.bindSocket e p) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.connectSocket e p) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.localAddress e p) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.closeError e err′) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode A.commitHandshake f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq with A.pc f
  ... | A.waitingInbound e k with lookup e (entries (cm s)) in found
  ...   | nothing = case eq of λ ()
  ...   | just st = choice-retains false e (C.waitCase k st) f s eq
  step-admissions caller mode A.waitNegotiated f s eq | A.selecting = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.allocatePromise e) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.openSocket e p) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.configureSocket e p) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.bindSocket e p) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.connectSocket e p) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.localAddress e p) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.commitResult e k result) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.closeError e err′) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode A.waitNegotiated f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode (A.failIO err) f s eq with A.pc f
  ... | A.openSocket e p = result-retains {before = s} eq (identity s)
  ... | A.configureSocket e p = result-retains {before = s} eq (identity s)
  ... | A.bindSocket e p = result-retains {before = s} eq (identity s)
  ... | A.connectSocket e p = result-retains {before = s} eq (identity s)
  ... | A.localAddress e p = result-retains {before = s} eq (identity s)
  ... | A.forkHandler e p k = result-retains {before = s} eq (identity s)
  step-admissions caller mode (A.failIO err) f s eq | A.selecting = case eq of λ ()
  step-admissions caller mode (A.failIO err) f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode (A.failIO err) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-admissions caller mode (A.failIO err) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode (A.failIO err) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-admissions caller mode (A.failIO err) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-admissions caller mode (A.failIO err) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-admissions caller mode (A.failIO err) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-admissions caller mode (A.failIO err) f s eq | (A.closeError e err′) = case eq of λ ()
  step-admissions caller mode (A.failIO err) f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode (A.failIO err) f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq with A.pc f
  ... | A.closeError e err = result-retains {before = s} eq (socket-write (A.socketRef (A.req f)) closed s)
  step-admissions caller mode A.closeOK f s eq | A.selecting = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.allocatePromise e) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.openSocket e p) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.configureSocket e p) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.bindSocket e p) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.connectSocket e p) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.localAddress e p) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.commitResult e k result) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode A.closeOK f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq with A.pc f
  ... | A.closeError e _ = result-retains {before = s} eq (socket-write (A.socketRef (A.req f)) (closeUncertain err) s)
  step-admissions caller mode (A.closeFailed err) f s eq | A.selecting = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.count p) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.allocatePromise e) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.openSocket e p) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.configureSocket e p) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.bindSocket e p) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.connectSocket e p) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.localAddress e p) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.updateAddress e p k) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.forkHandler e p k) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.connectedCommit e p k) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.awaitResult e p k) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.commitResult e k result) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.waitingInbound e k) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.removeError e err′) = case eq of λ ()
  step-admissions caller mode (A.closeFailed err) f s eq | (A.complete result) = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq with A.pc f | mapCell (cm s)
  ... | A.removeError e err | full m = result-retains {before = s} eq (entry-write e (terminated nothing) s)
  step-admissions caller mode A.removeReservation f s eq | A.selecting | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.count p) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.openSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.localAddress e p) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.closeError e err′) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.complete result) | _ = case eq of λ ()
  step-admissions caller mode A.removeReservation f s eq | (A.removeError e err′) | taken w = case eq of λ ()
  step-admissions caller mode A.returnResult f s ()

  -- Pair-projection-free form for the enclosing outbound-machine invariant.
  acquire-admissions : ∀ caller mode action savedFrame before {savedFrame′ after} →
    A.step caller mode action savedFrame before ≡ just (savedFrame′ , after) →
    admissions after ≡ admissions before
  acquire-admissions caller mode action savedFrame before =
    step-admissions caller mode action savedFrame before

acquire-admissions : ∀ caller mode action savedFrame before {savedFrame′ after} → A.step caller mode action savedFrame before ≡ just (savedFrame′ , after) → S.admissions after ≡ S.admissions before
acquire-admissions = AcquireQuiet.acquire-admissions

private
 module ReleaseQuiet where
  open S using (State; cm; mapCell; full; taken; lookupConnection; entries; countIncoming; terminated; terminating)
  -- Transport store effects through an exact pair result.
  release-result : ∀ {before} {pair pair′ : Release.Frame × State} → just pair ≡ just pair′ →
    S.admissions (proj₂ pair) ≡ S.admissions before → S.admissions (proj₂ pair′) ≡ S.admissions before
  release-result {before} eq = subst (λ pair → S.admissions (proj₂ pair) ≡ S.admissions before) (just-injective eq)

  -- A release branch writes only an entry value.
  release-apply-admissions : ∀ e d f s → S.admissions (proj₂ (Release.apply e d f s)) ≡ S.admissions s
  release-apply-admissions e d f s with Release.replacement d
  ... | nothing = refl
  ... | just st = refl

  -- Atomic pruning transports all shared-store effects.
  release-capacity : ∀ limit scores m e old d f s {out} → Release.capacity limit scores m e old d f s ≡ just out → S.admissions (proj₂ out) ≡ S.admissions s
  release-capacity limit scores m e old d f s eq with Release.needsCapacity d
  ... | false with scores
  ...   | nothing = release-result {before = s} eq (release-apply-admissions e d f s)
  ...   | just _ = case eq of λ ()
  release-capacity limit scores m e old d f s eq | true with countIncoming (entries (cm s)) m
  ... | nothing = case eq of λ ()
  ... | just n with suc n ≤? limit
  ...   | yes _ with scores
  ...     | nothing = release-result {before = s} eq (release-apply-admissions e d f s)
  ...     | just _ = case eq of λ ()
  release-capacity limit scores m e old d f s eq | true | just n | no _
    with scores | Release.replacement d | Prune.candidates m (entries (cm s))
  ... | just draws | just st | just candidates with Prune.candidateFor (Release.key f) e st
  ...   | nothing = case eq of λ ()
  ...   | just self with Prune.makePlan (suc n ∸ limit) self st candidates draws
  ...     | nothing = case eq of λ ()
  ...     | just selectedPlan with Prune.applyEdits (map (λ c → Prune.entryRef c , terminated nothing) (Prune.victims selectedPlan)) s in edited
  ...       | nothing = case eq of λ ()
  ...       | just s′ = release-result {before = s} eq (edits-admissions (map (λ c → Prune.entryRef c , terminated nothing) (Prune.victims selectedPlan)) s edited)
  release-capacity limit scores m e old d f s eq | true | just n | no _ | nothing | _ | _ = case eq of λ ()
  release-capacity limit scores m e old d f s eq | true | just n | no _ | just _ | nothing | _ = case eq of λ ()
  release-capacity limit scores m e old d f s eq | true | just n | no _ | just _ | just _ | nothing = case eq of λ ()

  -- The transaction selects one of the checked release branches.
  release-transact : ∀ limit scores f s {out} → Release.transact limit scores f s ≡ just out → S.admissions (proj₂ out) ≡ S.admissions s
  release-transact limit scores f s eq with mapCell (cm s)
  ... | taken _ = case eq of λ ()
  ... | full m with lookupConnection (Release.key f) m
  ...   | nothing with scores
  ...     | nothing = release-result {before = s} eq (refl)
  ...     | just _ = case eq of λ ()
  release-transact limit scores f s eq | full m | just e with lookup e (entries (cm s))
  ... | nothing = case eq of λ ()
  ... | just st = release-capacity limit scores m e st (Release.branch (Release.key f) e st) f s eq

  -- Exhaust every successful action without a savedFrame-validity premise.
  release-step-admissions : ∀ limit action f s {out} → Release.step limit action f s ≡ just out → S.admissions (proj₂ out) ≡ S.admissions s
  release-step-admissions limit Release.transactionStep f s eq with Release.pc f
  ... | Release.transaction = release-transact limit nothing f s eq
  release-step-admissions limit Release.transactionStep f s eq | (Release.check flag p) = case eq of λ ()
  release-step-admissions limit Release.transactionStep f s eq | (Release.count p) = case eq of λ ()
  release-step-admissions limit Release.transactionStep f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-admissions limit Release.transactionStep f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-admissions limit Release.transactionStep f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-admissions limit Release.transactionStep f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-admissions limit Release.transactionStep f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-admissions limit Release.transactionStep f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-admissions limit Release.transactionStep f s eq | (Release.complete result) = case eq of λ ()
  release-step-admissions limit (Release.transactionPruning scores) f s eq with Release.pc f
  ... | Release.transaction = release-transact limit (just scores) f s eq
  release-step-admissions limit (Release.transactionPruning scores) f s eq | (Release.check flag p) = case eq of λ ()
  release-step-admissions limit (Release.transactionPruning scores) f s eq | (Release.count p) = case eq of λ ()
  release-step-admissions limit (Release.transactionPruning scores) f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-admissions limit (Release.transactionPruning scores) f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-admissions limit (Release.transactionPruning scores) f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-admissions limit (Release.transactionPruning scores) f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-admissions limit (Release.transactionPruning scores) f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-admissions limit (Release.transactionPruning scores) f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-admissions limit (Release.transactionPruning scores) f s eq | (Release.complete result) = case eq of λ ()
  release-step-admissions limit Release.checkAssertion f s eq with Release.pc f
  ... | Release.check true next = release-result {before = s} eq (refl)
  ... | Release.check false next = release-result {before = s} eq (refl)
  release-step-admissions limit Release.checkAssertion f s eq | (Release.transaction) = case eq of λ ()
  release-step-admissions limit Release.checkAssertion f s eq | (Release.count p) = case eq of λ ()
  release-step-admissions limit Release.checkAssertion f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-admissions limit Release.checkAssertion f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-admissions limit Release.checkAssertion f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-admissions limit Release.checkAssertion f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-admissions limit Release.checkAssertion f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-admissions limit Release.checkAssertion f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-admissions limit Release.checkAssertion f s eq | (Release.complete result) = case eq of λ ()
  release-step-admissions limit Release.readCounters f s eq with Release.pc f | mapCell (cm s)
  ... | Release.count next | full m with countIncoming (entries (cm s)) m
  ...   | nothing = case eq of λ ()
  ...   | just _ = release-result {before = s} eq (refl)
  release-step-admissions limit Release.readCounters f s eq | (Release.transaction) | _ = case eq of λ ()
  release-step-admissions limit Release.readCounters f s eq | (Release.check flag p) | _ = case eq of λ ()
  release-step-admissions limit Release.readCounters f s eq | (Release.armTimer e v) | _ = case eq of λ ()
  release-step-admissions limit Release.readCounters f s eq | (Release.waitIdle e v) | _ = case eq of λ ()
  release-step-admissions limit Release.readCounters f s eq | (Release.timeoutWrite e v) | _ = case eq of λ ()
  release-step-admissions limit Release.readCounters f s eq | (Release.cancel v p) | _ = case eq of λ ()
  release-step-admissions limit Release.readCounters f s eq | (Release.delivering v p) | _ = case eq of λ ()
  release-step-admissions limit Release.readCounters f s eq | (Release.prune victims result) | _ = case eq of λ ()
  release-step-admissions limit Release.readCounters f s eq | (Release.complete result) | _ = case eq of λ ()
  release-step-admissions limit Release.readCounters f s eq | (Release.count p) | taken w = case eq of λ ()
  release-step-admissions limit Release.registerTimer f s eq with Release.pc f
  ... | Release.armTimer e w = release-result {before = s} eq (refl)
  release-step-admissions limit Release.registerTimer f s eq | (Release.transaction) = case eq of λ ()
  release-step-admissions limit Release.registerTimer f s eq | (Release.check flag p) = case eq of λ ()
  release-step-admissions limit Release.registerTimer f s eq | (Release.count p) = case eq of λ ()
  release-step-admissions limit Release.registerTimer f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-admissions limit Release.registerTimer f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-admissions limit Release.registerTimer f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-admissions limit Release.registerTimer f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-admissions limit Release.registerTimer f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-admissions limit Release.registerTimer f s eq | (Release.complete result) = case eq of λ ()
  release-step-admissions limit Release.expireTimer f s eq with Release.pc f | Release.timerReady f
  ... | Release.waitIdle e w | false = release-result {before = s} eq (refl)
  release-step-admissions limit Release.expireTimer f s eq | (Release.transaction) | _ = case eq of λ ()
  release-step-admissions limit Release.expireTimer f s eq | (Release.check flag p) | _ = case eq of λ ()
  release-step-admissions limit Release.expireTimer f s eq | (Release.count p) | _ = case eq of λ ()
  release-step-admissions limit Release.expireTimer f s eq | (Release.armTimer e v) | _ = case eq of λ ()
  release-step-admissions limit Release.expireTimer f s eq | (Release.timeoutWrite e v) | _ = case eq of λ ()
  release-step-admissions limit Release.expireTimer f s eq | (Release.cancel v p) | _ = case eq of λ ()
  release-step-admissions limit Release.expireTimer f s eq | (Release.delivering v p) | _ = case eq of λ ()
  release-step-admissions limit Release.expireTimer f s eq | (Release.prune victims result) | _ = case eq of λ ()
  release-step-admissions limit Release.expireTimer f s eq | (Release.complete result) | _ = case eq of λ ()
  release-step-admissions limit Release.expireTimer f s eq | (Release.waitIdle e v) | true = case eq of λ ()
  release-step-admissions limit Release.selectWakeup f s eq with Release.pc f
  ... | Release.waitIdle e w with lookup e (entries (cm s))
  ...   | nothing = case eq of λ ()
  ...   | just st with Release.isIdle st | Release.isTerminated st | Release.timerReady f
  ...     | false | true | _ = release-result {before = s} eq (refl)
  ...     | false | false | _ = release-result {before = s} eq (refl)
  ...     | true | _ | true = release-result {before = s} eq (refl)
  ...     | true | _ | false = case eq of λ ()
  release-step-admissions limit Release.selectWakeup f s eq | (Release.transaction) = case eq of λ ()
  release-step-admissions limit Release.selectWakeup f s eq | (Release.check flag p) = case eq of λ ()
  release-step-admissions limit Release.selectWakeup f s eq | (Release.count p) = case eq of λ ()
  release-step-admissions limit Release.selectWakeup f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-admissions limit Release.selectWakeup f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-admissions limit Release.selectWakeup f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-admissions limit Release.selectWakeup f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-admissions limit Release.selectWakeup f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-admissions limit Release.selectWakeup f s eq | (Release.complete result) = case eq of λ ()
  release-step-admissions limit Release.commitTimeout f s eq with Release.pc f
  ... | Release.timeoutWrite e w with lookup e (entries (cm s))
  ...   | nothing = case eq of λ ()
  ...   | just _ = release-result {before = s} eq (refl)
  release-step-admissions limit Release.commitTimeout f s eq | (Release.transaction) = case eq of λ ()
  release-step-admissions limit Release.commitTimeout f s eq | (Release.check flag p) = case eq of λ ()
  release-step-admissions limit Release.commitTimeout f s eq | (Release.count p) = case eq of λ ()
  release-step-admissions limit Release.commitTimeout f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-admissions limit Release.commitTimeout f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-admissions limit Release.commitTimeout f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-admissions limit Release.commitTimeout f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-admissions limit Release.commitTimeout f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-admissions limit Release.commitTimeout f s eq | (Release.complete result) = case eq of λ ()
  release-step-admissions limit Release.requestCancellation f s eq with Release.pc f
  ... | Release.cancel w next = release-result {before = s} eq (refl)
  ... | Release.prune [] result = release-result {before = s} eq (refl)
  ... | Release.prune (victim ∷ rest) result = release-result {before = s} eq (refl)
  release-step-admissions limit Release.requestCancellation f s eq | (Release.transaction) = case eq of λ ()
  release-step-admissions limit Release.requestCancellation f s eq | (Release.check flag p) = case eq of λ ()
  release-step-admissions limit Release.requestCancellation f s eq | (Release.count p) = case eq of λ ()
  release-step-admissions limit Release.requestCancellation f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-admissions limit Release.requestCancellation f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-admissions limit Release.requestCancellation f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-admissions limit Release.requestCancellation f s eq | (Release.delivering v p) = case eq of λ ()
  release-step-admissions limit Release.requestCancellation f s eq | (Release.complete result) = case eq of λ ()
  release-step-admissions limit (Release.cancellationDelivered w) f s eq with Release.pc f
  ... | Release.delivering v next with w ≟ v
  ...   | yes _ = release-result {before = s} eq (refl)
  ...   | no _ = case eq of λ ()
  release-step-admissions limit (Release.cancellationDelivered w) f s eq | (Release.transaction) = case eq of λ ()
  release-step-admissions limit (Release.cancellationDelivered w) f s eq | (Release.check flag p) = case eq of λ ()
  release-step-admissions limit (Release.cancellationDelivered w) f s eq | (Release.count p) = case eq of λ ()
  release-step-admissions limit (Release.cancellationDelivered w) f s eq | (Release.armTimer e v) = case eq of λ ()
  release-step-admissions limit (Release.cancellationDelivered w) f s eq | (Release.waitIdle e v) = case eq of λ ()
  release-step-admissions limit (Release.cancellationDelivered w) f s eq | (Release.timeoutWrite e v) = case eq of λ ()
  release-step-admissions limit (Release.cancellationDelivered w) f s eq | (Release.cancel v p) = case eq of λ ()
  release-step-admissions limit (Release.cancellationDelivered w) f s eq | (Release.prune victims result) = case eq of λ ()
  release-step-admissions limit (Release.cancellationDelivered w) f s eq | (Release.complete result) = case eq of λ ()
  release-step-admissions limit Release.returnResult f s ()

release-admissions : ∀ limit action savedFrame before {savedFrame′ after} → Release.step limit action savedFrame before ≡ just (savedFrame′ , after) → S.admissions after ≡ S.admissions before
release-admissions limit action savedFrame before actual = ReleaseQuiet.release-step-admissions limit action savedFrame before actual

-- Source actions outside admission/handshake preserve the whole admission table.
machine-same : ∀ action c {d} → M.advance action c ≡ just d → QuietMachine action → S.admissions (M.world d) ≡ S.admissions (M.world c)
machine-same (M.admissionStep worker action) c actual ()
machine-same (M.handshakeStep worker action) c actual ()
machine-same (M.handlerStep worker action) c eq quiet with Life.step worker action (M.handlerLifecycles c) (M.inboundGovernor c) (M.world c)
... | nothing = case eq of λ ()
... | just (runtime , governor) = case just-injective eq of λ { refl → refl }
machine-same (M.remoteStep action) c eq quiet with Life.allowRemote action (M.handlerLifecycles c) (M.world c)
... | false = case eq of λ ()
... | true with Remote.step (M.promotionHardLimit c) (M.pruningGeneration c) action (M.remoteCall c) (M.inboundGovernor c) (M.world c)
...   | nothing = case eq of λ ()
...   | just plan with Prune.applyEdits (Remote.edits plan) (M.world c) in actual
...     | nothing = case eq of λ ()
...     | just next with just-injective eq
...       | refl = edits-admissions (Remote.edits plan) (M.world c) actual
machine-same (M.releaseStep action) c eq quiet with Life.allowRelease action (M.handlerLifecycles c) (M.world c)
... | false = case eq of λ ()
... | true with InRelease.step action (M.inboundRelease c) (M.inboundGovernor c) (M.world c)
...   | nothing = case eq of λ ()
...   | just plan with InRelease.applyEdit (InRelease.edit plan) (M.world c) in actual
...     | nothing = case eq of λ ()
...     | just next with just-injective eq
...       | refl = edit-admissions (InRelease.edit plan) (M.world c) actual
machine-same (M.igStep action) c eq quiet with Life.allowIG action (M.handlerLifecycles c)
... | false = case eq of λ ()
... | true with IG.step (M.responder c) action (M.inboundGovernor c) (S.inboundInfo (M.world c))
...   | nothing = case eq of λ ()
...   | just (governor , queue) = case just-injective eq of λ { refl → refl }
machine-same (M.cleanupStep worker action) c eq quiet with Cleanup.stepCleanup worker action (M.world c) in actual
... | nothing = case eq of λ ()
... | just next with just-injective eq
...   | refl = cleanup-admissions worker action (M.world c) actual
machine-same (M.handlerExit worker) c eq quiet with Life.mayExit worker (M.handlerLifecycles c)
... | false = case eq of λ ()
... | true with Cleanup.beginCleanupBoundary worker (M.world c) in actual
...   | nothing = case eq of λ ()
...   | just next with just-injective eq
...     | refl = begin-cleanup-admissions worker (M.world c) actual
machine-same (M.handlerPublication worker result outcome) c eq quiet with any (λ other → does (other ≟ worker)) (M.publicationFaults c)
... | true = case eq of λ ()
... | false with H.publishBoundary worker result (M.world c) in actual | outcome
...   | nothing | _ = case eq of λ ()
...   | just (H.published next) | M.resultWritten with just-injective eq
...     | refl = publication-admissions worker result (M.world c) actual
machine-same (M.handlerPublication worker result outcome) c eq quiet | false | just (H.published next) | M.duplicateWrite = case eq of λ ()
machine-same (M.handlerPublication worker result outcome) c eq quiet | false | just H.writerBlocked | M.resultWritten = case eq of λ ()
machine-same (M.handlerPublication worker result outcome) c eq quiet | false | just H.writerBlocked | M.duplicateWrite = case just-injective eq of λ { refl → refl }

private
 machine-result : ∀ action c {d} → M.advance action c ≡ just d → Σ (Change (M.world c) (M.world d)) (Cause action)
 machine-result (M.admissionStep worker action) c actual = admission-result worker action c actual
 machine-result (M.handshakeStep worker action) c actual = handshake-result worker action c actual
 machine-result (M.cleanupStep worker action) c actual = same (machine-same (M.cleanupStep worker action) c actual tt) , tt
 machine-result (M.handlerStep worker action) c actual = same (machine-same (M.handlerStep worker action) c actual tt) , tt
 machine-result (M.handlerPublication worker result outcome) c actual = same (machine-same (M.handlerPublication worker result outcome) c actual tt) , tt
 machine-result (M.handlerExit worker) c actual = same (machine-same (M.handlerExit worker) c actual tt) , tt
 machine-result (M.remoteStep action) c actual = same (machine-same (M.remoteStep action) c actual tt) , tt
 machine-result (M.releaseStep action) c actual = same (machine-same (M.releaseStep action) c actual tt) , tt
 machine-result (M.igStep action) c actual = same (machine-same (M.igStep action) c actual tt) , tt

machine-effect : ∀ action c {d} → M.advance action c ≡ just d → Change (M.world c) (M.world d)
machine-effect action c actual = proj₁ (machine-result action c actual)
machine-cause : ∀ action c {d} (actual : M.advance action c ≡ just d) → Cause action (machine-effect action c actual)
machine-cause action c actual = proj₂ (machine-result action c actual)

private
 acquire-wrapper : ∀ worker action c {d} → O.advanceAcquire worker action c ≡ just d → S.admissions (M.world (O.core d)) ≡ S.admissions (M.world (O.core c))
 acquire-wrapper worker A.returnResult c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.pc savedFrame
 ...   | A.complete result = case just-injective eq of λ { refl → refl }
 ...   | A.selecting = case eq of λ ()
 ...   | A.count pc = case eq of λ ()
 ...   | A.allocatePromise entry = case eq of λ ()
 ...   | A.openSocket entry promise = case eq of λ ()
 ...   | A.configureSocket entry promise = case eq of λ ()
 ...   | A.bindSocket entry promise = case eq of λ ()
 ...   | A.connectSocket entry promise = case eq of λ ()
 ...   | A.localAddress entry promise = case eq of λ ()
 ...   | A.updateAddress entry promise key = case eq of λ ()
 ...   | A.forkHandler entry promise key = case eq of λ ()
 ...   | A.connectedCommit entry promise key = case eq of λ ()
 ...   | A.awaitResult entry promise key = case eq of λ ()
 ...   | A.commitResult entry key result = case eq of λ ()
 ...   | A.waitingInbound entry key = case eq of λ ()
 ...   | A.closeError entry error = case eq of λ ()
 ...   | A.removeError entry error = case eq of λ ()
 acquire-wrapper worker (A.select chosen) c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) (A.select chosen) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) (A.select chosen) savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.readCounters c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.readCounters savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.readCounters savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.newPromise c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.newPromise savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.newPromise savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.openOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.openOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.openOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.configureOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.configureOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.configureOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.bindOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.bindOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.bindOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.connectOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.connectOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.connectOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker (A.gotLocal local) c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) (A.gotLocal local) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) (A.gotLocal local) savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.updateLocalAddress c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.updateLocalAddress savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.updateLocalAddress savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.forkOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.forkOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.forkOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.commitConnected c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.commitConnected savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.commitConnected savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.readResult c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.readResult savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.readResult savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.commitHandshake c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.commitHandshake savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.commitHandshake savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker (A.failIO error) c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) (A.failIO error) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) (A.failIO error) savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker (A.closeFailed error) c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) (A.closeFailed error) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) (A.closeFailed error) savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.closeOK c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.closeOK savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.closeOK savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.removeReservation c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.removeReservation savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.removeReservation savedFrame (M.world (O.core c)) actual
 acquire-wrapper worker A.waitNegotiated c eq with lookup worker (O.acquiring c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with A.step worker (M.responder (O.core c)) A.waitNegotiated savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = acquire-admissions worker (M.responder (O.core c)) A.waitNegotiated savedFrame (M.world (O.core c)) actual
 release-wrapper : ∀ worker action c {d} → O.advanceRelease worker action c ≡ just d → S.admissions (M.world (O.core d)) ≡ S.admissions (M.world (O.core c))
 release-wrapper worker Release.returnResult c eq with lookup worker (O.releasing c)
 ... | nothing = case eq of λ ()
 ... | just savedFrame with Release.pc savedFrame
 ...   | Release.complete result = case just-injective eq of λ { refl → refl }
 ...   | Release.transaction = case eq of λ ()
 ...   | Release.check flag pc = case eq of λ ()
 ...   | Release.count pc = case eq of λ ()
 ...   | Release.armTimer entry target = case eq of λ ()
 ...   | Release.waitIdle entry target = case eq of λ ()
 ...   | Release.timeoutWrite entry target = case eq of λ ()
 ...   | Release.cancel target pc = case eq of λ ()
 ...   | Release.delivering target pc = case eq of λ ()
 ...   | Release.prune victims result = case eq of λ ()
 release-wrapper worker Release.transactionStep c eq with lookup worker (O.releasing c) | O.canDeliver Release.transactionStep c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.transactionStep savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-admissions (M.promotionHardLimit (O.core c)) Release.transactionStep savedFrame (M.world (O.core c)) actual
 release-wrapper worker (Release.transactionPruning scores) c eq with lookup worker (O.releasing c) | O.canDeliver (Release.transactionPruning scores) c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) (Release.transactionPruning scores) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-admissions (M.promotionHardLimit (O.core c)) (Release.transactionPruning scores) savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.checkAssertion c eq with lookup worker (O.releasing c) | O.canDeliver Release.checkAssertion c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.checkAssertion savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-admissions (M.promotionHardLimit (O.core c)) Release.checkAssertion savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.readCounters c eq with lookup worker (O.releasing c) | O.canDeliver Release.readCounters c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.readCounters savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-admissions (M.promotionHardLimit (O.core c)) Release.readCounters savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.registerTimer c eq with lookup worker (O.releasing c) | O.canDeliver Release.registerTimer c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.registerTimer savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-admissions (M.promotionHardLimit (O.core c)) Release.registerTimer savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.expireTimer c eq with lookup worker (O.releasing c) | O.canDeliver Release.expireTimer c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.expireTimer savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-admissions (M.promotionHardLimit (O.core c)) Release.expireTimer savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.selectWakeup c eq with lookup worker (O.releasing c) | O.canDeliver Release.selectWakeup c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.selectWakeup savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-admissions (M.promotionHardLimit (O.core c)) Release.selectWakeup savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.commitTimeout c eq with lookup worker (O.releasing c) | O.canDeliver Release.commitTimeout c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.commitTimeout savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-admissions (M.promotionHardLimit (O.core c)) Release.commitTimeout savedFrame (M.world (O.core c)) actual
 release-wrapper worker Release.requestCancellation c eq with lookup worker (O.releasing c) | O.canDeliver Release.requestCancellation c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) Release.requestCancellation savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-admissions (M.promotionHardLimit (O.core c)) Release.requestCancellation savedFrame (M.world (O.core c)) actual
 release-wrapper worker (Release.cancellationDelivered target) c eq with lookup worker (O.releasing c) | O.canDeliver (Release.cancellationDelivered target) c
 ... | nothing | _ = case eq of λ ()
 ... | just savedFrame | false = case eq of λ ()
 ... | just savedFrame | true with Release.step (M.promotionHardLimit (O.core c)) (Release.cancellationDelivered target) savedFrame (M.world (O.core c)) in actual
 ...   | nothing = case eq of λ ()
 ...   | just (savedFrame′ , next) with just-injective eq
 ...     | refl = release-admissions (M.promotionHardLimit (O.core c)) (Release.cancellationDelivered target) savedFrame (M.world (O.core c)) actual

outbound-same : ∀ action c {d} → O.advance action c ≡ just d → QuietOutbound action → S.admissions (M.world (O.core d)) ≡ S.admissions (M.world (O.core c))
outbound-same (O.inbound action) c actual ()
outbound-same (O.acquire worker action) c actual quiet = acquire-wrapper worker action c actual
outbound-same (O.release worker action) c actual quiet = release-wrapper worker action c actual
outbound-same (O.beginAcquire worker request) c actual quiet with lookup worker (O.acquiring c) | lookup worker (O.releasing c)
... | nothing | nothing = case just-injective actual of λ { refl → refl }
... | nothing | just _ = case actual of λ ()
... | just _ | _ = case actual of λ ()
outbound-same (O.beginRelease worker key) c actual quiet with lookup worker (O.acquiring c) | lookup worker (O.releasing c)
... | nothing | nothing = case just-injective actual of λ { refl → refl }
... | nothing | just _ = case actual of λ ()
... | just _ | _ = case actual of λ ()

private
 inbound-cause : ∀ action {before after} (change : Change before after) → Cause action change → OutboundCause (O.inbound action) change
 inbound-cause action (same unchanged) cause = tt
 inbound-cause action (reset worker row outside changed) cause = tt
 inbound-cause action (allocated worker request saved owned changed) cause = cong O.inbound cause
 inbound-cause action (selected worker request saved promise entry owned changed) cause = cong O.inbound cause

 outbound-result : ∀ action c {d} → O.advance action c ≡ just d → Σ (Change (M.world (O.core c)) (M.world (O.core d))) (OutboundCause action)
 outbound-result (O.inbound action) c eq with M.advance action (O.core c) in actual
 ... | nothing = case eq of λ ()
 ... | just next with just-injective eq
 ...   | refl with machine-result action (O.core c) actual
 ...     | change , cause = change , inbound-cause action change cause
 outbound-result (O.beginAcquire worker request) c eq = same (outbound-same (O.beginAcquire worker request) c eq tt) , tt
 outbound-result (O.beginRelease worker key) c eq = same (outbound-same (O.beginRelease worker key) c eq tt) , tt
 outbound-result (O.acquire worker action) c eq = same (outbound-same (O.acquire worker action) c eq tt) , tt
 outbound-result (O.release worker action) c eq = same (outbound-same (O.release worker action) c eq tt) , tt

outbound-effect : ∀ action c {d} → O.advance action c ≡ just d → Change (M.world (O.core c)) (M.world (O.core d))
outbound-effect action c actual = proj₁ (outbound-result action c actual)
outbound-cause : ∀ action c {d} (actual : O.advance action c ≡ just d) → OutboundCause action (outbound-effect action c actual)
outbound-cause action c actual = proj₂ (outbound-result action c actual)

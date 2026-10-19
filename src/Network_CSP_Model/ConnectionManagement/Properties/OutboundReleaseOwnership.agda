{-# OPTIONS --guardedness #-}

-- Release preserves the map lease census across pruning, timers and cancellation.
module ConnectionManagement.Properties.OutboundReleaseOwnership where

open import Data.Bool using (true; false)
open import Data.Nat using (suc; _≤?_; _∸_)
open import Data.List using ([]; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Ownership using (Ownership; Owns; claims)
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.Pruning as P
import ConnectionManagement.Properties.OwnershipInvariant as Inbound

-- Transport the exact ownership statement through a release result.
result-preserves : ∀ {pair pair′ : R.Frame × State} → just pair ≡ just pair′ →
  Ownership (proj₂ pair) → Ownership (proj₂ pair′)
result-preserves eq = subst (λ pair → Ownership (proj₂ pair)) (just-injective eq)

-- Branch writes affect entries, not the map cell or lease-bearing continuations.
apply-preserves : ∀ e d f s → Ownership s → Ownership (proj₂ (R.apply e d f s))
apply-preserves e d f s own with R.replacement d
... | nothing = own
... | just st = own

-- Atomic victim edits reuse the inbound ownership-preservation helper.
capacity-preserves : ∀ limit scores m e old d f s {out} → Ownership s →
  R.capacity limit scores m e old d f s ≡ just out → Ownership (proj₂ out)
capacity-preserves limit scores m e old d f s own eq with R.needsCapacity d
... | false with scores
...   | nothing = result-preserves eq (apply-preserves e d f s own)
...   | just _ = case eq of λ ()
capacity-preserves limit scores m e old d f s own eq | true with countIncoming (entries (cm s)) m
... | nothing = case eq of λ ()
... | just n with suc n ≤? limit
...   | yes _ with scores
...     | nothing = result-preserves eq (apply-preserves e d f s own)
...     | just _ = case eq of λ ()
capacity-preserves limit scores m e old d f s own eq | true | just n | no _
  with scores | R.replacement d | P.candidates m (entries (cm s))
... | just draws | just st | just candidates with P.candidateFor (R.key f) e st
...   | nothing = case eq of λ ()
...   | just self with P.makePlan (suc n ∸ limit) self st candidates draws
...     | nothing = case eq of λ ()
...     | just selectedPlan with P.applyEdits (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s in edited
...       | nothing = case eq of λ ()
...       | just s′ = result-preserves eq
  (Inbound.prune-edits-preserves
    (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s edited own)
capacity-preserves limit scores m e old d f s own eq | true | just n | no _ | nothing | _ | _ = case eq of λ ()
capacity-preserves limit scores m e old d f s own eq | true | just n | no _ | just _ | nothing | _ = case eq of λ ()
capacity-preserves limit scores m e old d f s own eq | true | just n | no _ | just _ | just _ | nothing = case eq of λ ()



-- Transactional selection does not take or release a map lease.
transact-preserves : ∀ limit scores f s {out} → Ownership s →
  R.transact limit scores f s ≡ just out → Ownership (proj₂ out)
transact-preserves limit scores f s own eq with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with lookupConnection (R.key f) m
...   | nothing with scores
...     | nothing = result-preserves eq
  (subst (λ cell → Owns cell (claims s)) (sym cell) own)
...     | just _ = case eq of λ ()
transact-preserves limit scores f s own eq | full m | just e with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just st = capacity-preserves limit scores m e st (R.branch (R.key f) e st) f s
  (subst (λ cell → Owns cell (claims s)) (sym cell) own) eq


-- Every successful release step preserves ownership, without frame premises.
step-preserves : ∀ limit action f s {out} → Ownership s →
  R.step limit action f s ≡ just out → Ownership (proj₂ out)
step-preserves limit R.transactionStep f s own eq with R.pc f
... | R.transaction = transact-preserves limit nothing f s own eq
step-preserves limit R.transactionStep f s own eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.transactionStep f s own eq | (R.count p) = case eq of λ ()
step-preserves limit R.transactionStep f s own eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.transactionStep f s own eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.transactionStep f s own eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.transactionStep f s own eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.transactionStep f s own eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.transactionStep f s own eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.transactionStep f s own eq | (R.complete result) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s own eq with R.pc f
... | R.transaction = transact-preserves limit (just scores) f s own eq
step-preserves limit (R.transactionPruning scores) f s own eq | (R.check flag p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s own eq | (R.count p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s own eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s own eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s own eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s own eq | (R.cancel v p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s own eq | (R.delivering v p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s own eq | (R.prune victims result) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s own eq | (R.complete result) = case eq of λ ()
step-preserves limit R.checkAssertion f s own eq with R.pc f
... | R.check true next = result-preserves eq own
... | R.check false next = result-preserves eq own
step-preserves limit R.checkAssertion f s own eq | (R.transaction) = case eq of λ ()
step-preserves limit R.checkAssertion f s own eq | (R.count p) = case eq of λ ()
step-preserves limit R.checkAssertion f s own eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.checkAssertion f s own eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.checkAssertion f s own eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.checkAssertion f s own eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.checkAssertion f s own eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.checkAssertion f s own eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.checkAssertion f s own eq | (R.complete result) = case eq of λ ()
step-preserves limit R.readCounters f s own eq with R.pc f | mapCell (cm s) in cell
... | R.count next | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = result-preserves eq
  (subst (λ cell → Owns cell (claims s)) (sym cell) own)
step-preserves limit R.readCounters f s own eq | (R.transaction) | _ = case eq of λ ()
step-preserves limit R.readCounters f s own eq | (R.check flag p) | _ = case eq of λ ()
step-preserves limit R.readCounters f s own eq | (R.armTimer e v) | _ = case eq of λ ()
step-preserves limit R.readCounters f s own eq | (R.waitIdle e v) | _ = case eq of λ ()
step-preserves limit R.readCounters f s own eq | (R.timeoutWrite e v) | _ = case eq of λ ()
step-preserves limit R.readCounters f s own eq | (R.cancel v p) | _ = case eq of λ ()
step-preserves limit R.readCounters f s own eq | (R.delivering v p) | _ = case eq of λ ()
step-preserves limit R.readCounters f s own eq | (R.prune victims result) | _ = case eq of λ ()
step-preserves limit R.readCounters f s own eq | (R.complete result) | _ = case eq of λ ()
step-preserves limit R.readCounters f s own eq | (R.count p) | taken w = case eq of λ ()
step-preserves limit R.registerTimer f s own eq with R.pc f
... | R.armTimer e w = result-preserves eq own
step-preserves limit R.registerTimer f s own eq | (R.transaction) = case eq of λ ()
step-preserves limit R.registerTimer f s own eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.registerTimer f s own eq | (R.count p) = case eq of λ ()
step-preserves limit R.registerTimer f s own eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.registerTimer f s own eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.registerTimer f s own eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.registerTimer f s own eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.registerTimer f s own eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.registerTimer f s own eq | (R.complete result) = case eq of λ ()
step-preserves limit R.expireTimer f s own eq with R.pc f | R.timerReady f
... | R.waitIdle e w | false = result-preserves eq own
step-preserves limit R.expireTimer f s own eq | (R.transaction) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s own eq | (R.check flag p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s own eq | (R.count p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s own eq | (R.armTimer e v) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s own eq | (R.timeoutWrite e v) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s own eq | (R.cancel v p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s own eq | (R.delivering v p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s own eq | (R.prune victims result) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s own eq | (R.complete result) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s own eq | (R.waitIdle e v) | true = case eq of λ ()
step-preserves limit R.selectWakeup f s own eq with R.pc f
... | R.waitIdle e w with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just st with R.isIdle st | R.isTerminated st | R.timerReady f
...     | false | true | _ = result-preserves eq own
...     | false | false | _ = result-preserves eq own
...     | true | _ | true = result-preserves eq own
...     | true | _ | false = case eq of λ ()
step-preserves limit R.selectWakeup f s own eq | (R.transaction) = case eq of λ ()
step-preserves limit R.selectWakeup f s own eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.selectWakeup f s own eq | (R.count p) = case eq of λ ()
step-preserves limit R.selectWakeup f s own eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.selectWakeup f s own eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.selectWakeup f s own eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.selectWakeup f s own eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.selectWakeup f s own eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.selectWakeup f s own eq | (R.complete result) = case eq of λ ()
step-preserves limit R.commitTimeout f s own eq with R.pc f
... | R.timeoutWrite e w with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just _ = result-preserves eq
  own
step-preserves limit R.commitTimeout f s own eq | (R.transaction) = case eq of λ ()
step-preserves limit R.commitTimeout f s own eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.commitTimeout f s own eq | (R.count p) = case eq of λ ()
step-preserves limit R.commitTimeout f s own eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.commitTimeout f s own eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.commitTimeout f s own eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.commitTimeout f s own eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.commitTimeout f s own eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.commitTimeout f s own eq | (R.complete result) = case eq of λ ()
step-preserves limit R.requestCancellation f s own eq with R.pc f
... | R.cancel w next = result-preserves eq own
... | R.prune [] result = result-preserves eq own
... | R.prune (victim ∷ rest) result = result-preserves eq own
step-preserves limit R.requestCancellation f s own eq | (R.transaction) = case eq of λ ()
step-preserves limit R.requestCancellation f s own eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.requestCancellation f s own eq | (R.count p) = case eq of λ ()
step-preserves limit R.requestCancellation f s own eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.requestCancellation f s own eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.requestCancellation f s own eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.requestCancellation f s own eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.requestCancellation f s own eq | (R.complete result) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s own eq with R.pc f
... | R.delivering v next with w ≟ v
...   | yes _ = result-preserves eq own
...   | no _ = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s own eq | (R.transaction) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s own eq | (R.check flag p) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s own eq | (R.count p) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s own eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s own eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s own eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s own eq | (R.cancel v p) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s own eq | (R.prune victims result) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s own eq | (R.complete result) = case eq of λ ()
step-preserves limit R.returnResult f s own ()

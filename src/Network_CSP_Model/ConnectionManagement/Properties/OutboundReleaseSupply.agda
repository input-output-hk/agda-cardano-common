{-# OPTIONS --guardedness #-}

-- Release preserves entry/promise supply bounds, including pruning and timeout.
module ConnectionManagement.Properties.OutboundReleaseSupply where

open import Data.Bool using (true; false)
open import Data.Nat using (suc; _<_; _≤?_; _∸_)
open import Data.List using ([]; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.SupplyBounds
open import ConnectionManagement.Properties.Stores using (put-keys)
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.Pruning as P
import ConnectionManagement.Properties.SupplyInvariant as Inbound

-- Transport bounds through a successful release result.
result-preserves : ∀ {pair pair′ : R.Frame × State} → just pair ≡ just pair′ →
  SupplyBounds (proj₂ pair) → SupplyBounds (proj₂ pair′)
result-preserves eq = subst (λ pair → SupplyBounds (proj₂ pair)) (just-injective eq)

-- A lookup supplies the selected identity's allocation bound.
bound-found : ∀ e s {old} → lookup e (entries (cm s)) ≡ just old →
  SupplyBounds s → serial e < nextEntry (cm s)
bound-found e s found bounded = lookup-key (λ e → serial e < nextEntry (cm s))
  e (entries (cm s)) (proj₁ bounded) found

-- A branch decision changes only the value at its selected bounded identity.
apply-preserves : ∀ e d f s → serial e < nextEntry (cm s) → SupplyBounds s →
  SupplyBounds (proj₂ (R.apply e d f s))
apply-preserves e d f s bound bounded with R.replacement d
... | nothing = bounded
... | just st = put-keys (λ e → serial e < nextEntry (cm s))
  e st (entries (cm s)) bound (proj₁ bounded) , proj₂ bounded

-- Pruning uses the existing checked entry-edit supply law.
capacity-preserves : ∀ limit scores m e old d f s {out} →
  serial e < nextEntry (cm s) → SupplyBounds s →
  R.capacity limit scores m e old d f s ≡ just out → SupplyBounds (proj₂ out)
capacity-preserves limit scores m e old d f s bound bounded eq with R.needsCapacity d
... | false with scores
...   | nothing = result-preserves eq (apply-preserves e d f s bound bounded)
...   | just _ = case eq of λ ()
capacity-preserves limit scores m e old d f s bound bounded eq | true with countIncoming (entries (cm s)) m
... | nothing = case eq of λ ()
... | just n with suc n ≤? limit
...   | yes _ with scores
...     | nothing = result-preserves eq (apply-preserves e d f s bound bounded)
...     | just _ = case eq of λ ()
capacity-preserves limit scores m e old d f s bound bounded eq | true | just n | no _
  with scores | R.replacement d | P.candidates m (entries (cm s))
... | just draws | just st | just candidates with P.candidateFor (R.key f) e st
...   | nothing = case eq of λ ()
...   | just self with P.makePlan (suc n ∸ limit) self st candidates draws
...     | nothing = case eq of λ ()
...     | just selectedPlan with P.applyEdits (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s in edited
...       | nothing = case eq of λ ()
...       | just s′ = result-preserves eq
  (Inbound.prune-edits-preserves
    (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s edited bounded)
capacity-preserves limit scores m e old d f s bound bounded eq | true | just n | no _ | nothing | _ | _ = case eq of λ ()
capacity-preserves limit scores m e old d f s bound bounded eq | true | just n | no _ | just _ | nothing | _ = case eq of λ ()
capacity-preserves limit scores m e old d f s bound bounded eq | true | just n | no _ | just _ | just _ | nothing = case eq of λ ()


-- Exact transactional lookup discharges the bound for every branch decision.
transact-preserves : ∀ limit scores f s {out} → SupplyBounds s →
  R.transact limit scores f s ≡ just out → SupplyBounds (proj₂ out)
transact-preserves limit scores f s bounded eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with lookupConnection (R.key f) m
...   | nothing with scores
...     | nothing = result-preserves eq bounded
...     | just _ = case eq of λ ()
transact-preserves limit scores f s bounded eq | full m | just e with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just st = capacity-preserves limit scores m e st (R.branch (R.key f) e st) f s
  (bound-found e s found bounded) bounded eq

-- No release-frame validity premise is needed: entry writes look up their target.
step-preserves : ∀ limit action f s {out} → SupplyBounds s →
  R.step limit action f s ≡ just out → SupplyBounds (proj₂ out)
step-preserves limit R.transactionStep f s bounded eq with R.pc f
... | R.transaction = transact-preserves limit nothing f s bounded eq
step-preserves limit R.transactionStep f s bounded eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.transactionStep f s bounded eq | (R.count p) = case eq of λ ()
step-preserves limit R.transactionStep f s bounded eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.transactionStep f s bounded eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.transactionStep f s bounded eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.transactionStep f s bounded eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.transactionStep f s bounded eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.transactionStep f s bounded eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.transactionStep f s bounded eq | (R.complete result) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s bounded eq with R.pc f
... | R.transaction = transact-preserves limit (just scores) f s bounded eq
step-preserves limit (R.transactionPruning scores) f s bounded eq | (R.check flag p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s bounded eq | (R.count p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s bounded eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s bounded eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s bounded eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s bounded eq | (R.cancel v p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s bounded eq | (R.delivering v p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s bounded eq | (R.prune victims result) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s bounded eq | (R.complete result) = case eq of λ ()
step-preserves limit R.checkAssertion f s bounded eq with R.pc f
... | R.check true next = result-preserves eq bounded
... | R.check false next = result-preserves eq bounded
step-preserves limit R.checkAssertion f s bounded eq | (R.transaction) = case eq of λ ()
step-preserves limit R.checkAssertion f s bounded eq | (R.count p) = case eq of λ ()
step-preserves limit R.checkAssertion f s bounded eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.checkAssertion f s bounded eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.checkAssertion f s bounded eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.checkAssertion f s bounded eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.checkAssertion f s bounded eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.checkAssertion f s bounded eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.checkAssertion f s bounded eq | (R.complete result) = case eq of λ ()
step-preserves limit R.readCounters f s bounded eq with R.pc f | mapCell (cm s)
... | R.count next | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = result-preserves eq bounded
step-preserves limit R.readCounters f s bounded eq | (R.transaction) | _ = case eq of λ ()
step-preserves limit R.readCounters f s bounded eq | (R.check flag p) | _ = case eq of λ ()
step-preserves limit R.readCounters f s bounded eq | (R.armTimer e v) | _ = case eq of λ ()
step-preserves limit R.readCounters f s bounded eq | (R.waitIdle e v) | _ = case eq of λ ()
step-preserves limit R.readCounters f s bounded eq | (R.timeoutWrite e v) | _ = case eq of λ ()
step-preserves limit R.readCounters f s bounded eq | (R.cancel v p) | _ = case eq of λ ()
step-preserves limit R.readCounters f s bounded eq | (R.delivering v p) | _ = case eq of λ ()
step-preserves limit R.readCounters f s bounded eq | (R.prune victims result) | _ = case eq of λ ()
step-preserves limit R.readCounters f s bounded eq | (R.complete result) | _ = case eq of λ ()
step-preserves limit R.readCounters f s bounded eq | (R.count p) | taken w = case eq of λ ()
step-preserves limit R.registerTimer f s bounded eq with R.pc f
... | R.armTimer e w = result-preserves eq bounded
step-preserves limit R.registerTimer f s bounded eq | (R.transaction) = case eq of λ ()
step-preserves limit R.registerTimer f s bounded eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.registerTimer f s bounded eq | (R.count p) = case eq of λ ()
step-preserves limit R.registerTimer f s bounded eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.registerTimer f s bounded eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.registerTimer f s bounded eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.registerTimer f s bounded eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.registerTimer f s bounded eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.registerTimer f s bounded eq | (R.complete result) = case eq of λ ()
step-preserves limit R.expireTimer f s bounded eq with R.pc f | R.timerReady f
... | R.waitIdle e w | false = result-preserves eq bounded
step-preserves limit R.expireTimer f s bounded eq | (R.transaction) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s bounded eq | (R.check flag p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s bounded eq | (R.count p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s bounded eq | (R.armTimer e v) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s bounded eq | (R.timeoutWrite e v) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s bounded eq | (R.cancel v p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s bounded eq | (R.delivering v p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s bounded eq | (R.prune victims result) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s bounded eq | (R.complete result) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s bounded eq | (R.waitIdle e v) | true = case eq of λ ()
step-preserves limit R.selectWakeup f s bounded eq with R.pc f
... | R.waitIdle e w with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just st with R.isIdle st | R.isTerminated st | R.timerReady f
...     | false | true | _ = result-preserves eq bounded
...     | false | false | _ = result-preserves eq bounded
...     | true | _ | true = result-preserves eq bounded
...     | true | _ | false = case eq of λ ()
step-preserves limit R.selectWakeup f s bounded eq | (R.transaction) = case eq of λ ()
step-preserves limit R.selectWakeup f s bounded eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.selectWakeup f s bounded eq | (R.count p) = case eq of λ ()
step-preserves limit R.selectWakeup f s bounded eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.selectWakeup f s bounded eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.selectWakeup f s bounded eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.selectWakeup f s bounded eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.selectWakeup f s bounded eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.selectWakeup f s bounded eq | (R.complete result) = case eq of λ ()
step-preserves limit R.commitTimeout f s bounded eq with R.pc f
... | R.timeoutWrite e w with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just _ = result-preserves eq
  (overwrite-bound (nextEntry (cm s)) e (terminating (R.key f) w nothing)
    (entries (cm s)) (proj₁ bounded) found , proj₂ bounded)
step-preserves limit R.commitTimeout f s bounded eq | (R.transaction) = case eq of λ ()
step-preserves limit R.commitTimeout f s bounded eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.commitTimeout f s bounded eq | (R.count p) = case eq of λ ()
step-preserves limit R.commitTimeout f s bounded eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.commitTimeout f s bounded eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.commitTimeout f s bounded eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.commitTimeout f s bounded eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.commitTimeout f s bounded eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.commitTimeout f s bounded eq | (R.complete result) = case eq of λ ()
step-preserves limit R.requestCancellation f s bounded eq with R.pc f
... | R.cancel w next = result-preserves eq bounded
... | R.prune [] result = result-preserves eq bounded
... | R.prune (victim ∷ rest) result = result-preserves eq bounded
step-preserves limit R.requestCancellation f s bounded eq | (R.transaction) = case eq of λ ()
step-preserves limit R.requestCancellation f s bounded eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.requestCancellation f s bounded eq | (R.count p) = case eq of λ ()
step-preserves limit R.requestCancellation f s bounded eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.requestCancellation f s bounded eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.requestCancellation f s bounded eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.requestCancellation f s bounded eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.requestCancellation f s bounded eq | (R.complete result) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s bounded eq with R.pc f
... | R.delivering v next with w ≟ v
...   | yes _ = result-preserves eq bounded
...   | no _ = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s bounded eq | (R.transaction) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s bounded eq | (R.check flag p) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s bounded eq | (R.count p) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s bounded eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s bounded eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s bounded eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s bounded eq | (R.cancel v p) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s bounded eq | (R.prune victims result) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s bounded eq | (R.complete result) = case eq of λ ()
step-preserves limit R.returnResult f s bounded ()

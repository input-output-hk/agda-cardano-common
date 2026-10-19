{-# OPTIONS --guardedness #-}

-- Release preserves all current and captured maps across pruning and timers.
module ConnectionManagement.Properties.OutboundReleaseMapUnique where

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
open import ConnectionManagement.Properties.StateMapUniqueness
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.Pruning as P
import ConnectionManagement.Properties.MapUniqueInvariant as Inbound

-- Transport the exact validership statement through a release result.
result-preserves : ∀ {pair pair′ : R.Frame × State} → just pair ≡ just pair′ →
  Valid (proj₂ pair) → Valid (proj₂ pair′)
result-preserves eq = subst (λ pair → Valid (proj₂ pair)) (just-injective eq)

-- Entry writes retain the current map cell and all captured maps.
apply-preserves : ∀ e d f s → Valid s → Valid (proj₂ (R.apply e d f s))
apply-preserves e d f s valid with R.replacement d
... | nothing = valid
... | just st = valid

-- Atomic victim edits reuse the inbound validership-preservation helper.
capacity-preserves : ∀ limit scores m e old d f s {out} → Valid s →
  R.capacity limit scores m e old d f s ≡ just out → Valid (proj₂ out)
capacity-preserves limit scores m e old d f s valid eq with R.needsCapacity d
... | false with scores
...   | nothing = result-preserves eq (apply-preserves e d f s valid)
...   | just _ = case eq of λ ()
capacity-preserves limit scores m e old d f s valid eq | true with countIncoming (entries (cm s)) m
... | nothing = case eq of λ ()
... | just n with suc n ≤? limit
...   | yes _ with scores
...     | nothing = result-preserves eq (apply-preserves e d f s valid)
...     | just _ = case eq of λ ()
capacity-preserves limit scores m e old d f s valid eq | true | just n | no _
  with scores | R.replacement d | P.candidates m (entries (cm s))
... | just draws | just st | just candidates with P.candidateFor (R.key f) e st
...   | nothing = case eq of λ ()
...   | just self with P.makePlan (suc n ∸ limit) self st candidates draws
...     | nothing = case eq of λ ()
...     | just selectedPlan with P.applyEdits (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s in edited
...       | nothing = case eq of λ ()
...       | just s′ = result-preserves eq
  (Inbound.prune-edits-preserves
    (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s edited valid)
capacity-preserves limit scores m e old d f s valid eq | true | just n | no _ | nothing | _ | _ = case eq of λ ()
capacity-preserves limit scores m e old d f s valid eq | true | just n | no _ | just _ | nothing | _ = case eq of λ ()
capacity-preserves limit scores m e old d f s valid eq | true | just n | no _ | just _ | just _ | nothing = case eq of λ ()



-- Transactional selection retains current and captured maps.
transact-preserves : ∀ limit scores f s {out} → Valid s →
  R.transact limit scores f s ≡ just out → Valid (proj₂ out)
transact-preserves limit scores f s valid eq with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with lookupConnection (R.key f) m
...   | nothing with scores
...     | nothing = result-preserves eq
  (restore-current s (full m) cell valid)
...     | just _ = case eq of λ ()
transact-preserves limit scores f s valid eq | full m | just e with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just st = capacity-preserves limit scores m e st (R.branch (R.key f) e st) f s
  (restore-current s (full m) cell valid) eq


-- Every successful release step preserves validership, without frame premises.
step-preserves : ∀ limit action f s {out} → Valid s →
  R.step limit action f s ≡ just out → Valid (proj₂ out)
step-preserves limit R.transactionStep f s valid eq with R.pc f
... | R.transaction = transact-preserves limit nothing f s valid eq
step-preserves limit R.transactionStep f s valid eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.transactionStep f s valid eq | (R.count p) = case eq of λ ()
step-preserves limit R.transactionStep f s valid eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.transactionStep f s valid eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.transactionStep f s valid eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.transactionStep f s valid eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.transactionStep f s valid eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.transactionStep f s valid eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.transactionStep f s valid eq | (R.complete result) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s valid eq with R.pc f
... | R.transaction = transact-preserves limit (just scores) f s valid eq
step-preserves limit (R.transactionPruning scores) f s valid eq | (R.check flag p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s valid eq | (R.count p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s valid eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s valid eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s valid eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s valid eq | (R.cancel v p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s valid eq | (R.delivering v p) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s valid eq | (R.prune victims result) = case eq of λ ()
step-preserves limit (R.transactionPruning scores) f s valid eq | (R.complete result) = case eq of λ ()
step-preserves limit R.checkAssertion f s valid eq with R.pc f
... | R.check true next = result-preserves eq valid
... | R.check false next = result-preserves eq valid
step-preserves limit R.checkAssertion f s valid eq | (R.transaction) = case eq of λ ()
step-preserves limit R.checkAssertion f s valid eq | (R.count p) = case eq of λ ()
step-preserves limit R.checkAssertion f s valid eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.checkAssertion f s valid eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.checkAssertion f s valid eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.checkAssertion f s valid eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.checkAssertion f s valid eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.checkAssertion f s valid eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.checkAssertion f s valid eq | (R.complete result) = case eq of λ ()
step-preserves limit R.readCounters f s valid eq with R.pc f | mapCell (cm s) in cell
... | R.count next | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = result-preserves eq
  (restore-current s (full m) cell valid)
step-preserves limit R.readCounters f s valid eq | (R.transaction) | _ = case eq of λ ()
step-preserves limit R.readCounters f s valid eq | (R.check flag p) | _ = case eq of λ ()
step-preserves limit R.readCounters f s valid eq | (R.armTimer e v) | _ = case eq of λ ()
step-preserves limit R.readCounters f s valid eq | (R.waitIdle e v) | _ = case eq of λ ()
step-preserves limit R.readCounters f s valid eq | (R.timeoutWrite e v) | _ = case eq of λ ()
step-preserves limit R.readCounters f s valid eq | (R.cancel v p) | _ = case eq of λ ()
step-preserves limit R.readCounters f s valid eq | (R.delivering v p) | _ = case eq of λ ()
step-preserves limit R.readCounters f s valid eq | (R.prune victims result) | _ = case eq of λ ()
step-preserves limit R.readCounters f s valid eq | (R.complete result) | _ = case eq of λ ()
step-preserves limit R.readCounters f s valid eq | (R.count p) | taken w = case eq of λ ()
step-preserves limit R.registerTimer f s valid eq with R.pc f
... | R.armTimer e w = result-preserves eq valid
step-preserves limit R.registerTimer f s valid eq | (R.transaction) = case eq of λ ()
step-preserves limit R.registerTimer f s valid eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.registerTimer f s valid eq | (R.count p) = case eq of λ ()
step-preserves limit R.registerTimer f s valid eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.registerTimer f s valid eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.registerTimer f s valid eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.registerTimer f s valid eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.registerTimer f s valid eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.registerTimer f s valid eq | (R.complete result) = case eq of λ ()
step-preserves limit R.expireTimer f s valid eq with R.pc f | R.timerReady f
... | R.waitIdle e w | false = result-preserves eq valid
step-preserves limit R.expireTimer f s valid eq | (R.transaction) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s valid eq | (R.check flag p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s valid eq | (R.count p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s valid eq | (R.armTimer e v) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s valid eq | (R.timeoutWrite e v) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s valid eq | (R.cancel v p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s valid eq | (R.delivering v p) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s valid eq | (R.prune victims result) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s valid eq | (R.complete result) | _ = case eq of λ ()
step-preserves limit R.expireTimer f s valid eq | (R.waitIdle e v) | true = case eq of λ ()
step-preserves limit R.selectWakeup f s valid eq with R.pc f
... | R.waitIdle e w with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just st with R.isIdle st | R.isTerminated st | R.timerReady f
...     | false | true | _ = result-preserves eq valid
...     | false | false | _ = result-preserves eq valid
...     | true | _ | true = result-preserves eq valid
...     | true | _ | false = case eq of λ ()
step-preserves limit R.selectWakeup f s valid eq | (R.transaction) = case eq of λ ()
step-preserves limit R.selectWakeup f s valid eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.selectWakeup f s valid eq | (R.count p) = case eq of λ ()
step-preserves limit R.selectWakeup f s valid eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.selectWakeup f s valid eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.selectWakeup f s valid eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.selectWakeup f s valid eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.selectWakeup f s valid eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.selectWakeup f s valid eq | (R.complete result) = case eq of λ ()
step-preserves limit R.commitTimeout f s valid eq with R.pc f
... | R.timeoutWrite e w with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just _ = result-preserves eq
  valid
step-preserves limit R.commitTimeout f s valid eq | (R.transaction) = case eq of λ ()
step-preserves limit R.commitTimeout f s valid eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.commitTimeout f s valid eq | (R.count p) = case eq of λ ()
step-preserves limit R.commitTimeout f s valid eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.commitTimeout f s valid eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.commitTimeout f s valid eq | (R.cancel v p) = case eq of λ ()
step-preserves limit R.commitTimeout f s valid eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.commitTimeout f s valid eq | (R.prune victims result) = case eq of λ ()
step-preserves limit R.commitTimeout f s valid eq | (R.complete result) = case eq of λ ()
step-preserves limit R.requestCancellation f s valid eq with R.pc f
... | R.cancel w next = result-preserves eq valid
... | R.prune [] result = result-preserves eq valid
... | R.prune (victim ∷ rest) result = result-preserves eq valid
step-preserves limit R.requestCancellation f s valid eq | (R.transaction) = case eq of λ ()
step-preserves limit R.requestCancellation f s valid eq | (R.check flag p) = case eq of λ ()
step-preserves limit R.requestCancellation f s valid eq | (R.count p) = case eq of λ ()
step-preserves limit R.requestCancellation f s valid eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit R.requestCancellation f s valid eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit R.requestCancellation f s valid eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit R.requestCancellation f s valid eq | (R.delivering v p) = case eq of λ ()
step-preserves limit R.requestCancellation f s valid eq | (R.complete result) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s valid eq with R.pc f
... | R.delivering v next with w ≟ v
...   | yes _ = result-preserves eq valid
...   | no _ = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s valid eq | (R.transaction) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s valid eq | (R.check flag p) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s valid eq | (R.count p) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s valid eq | (R.armTimer e v) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s valid eq | (R.waitIdle e v) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s valid eq | (R.timeoutWrite e v) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s valid eq | (R.cancel v p) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s valid eq | (R.prune victims result) = case eq of λ ()
step-preserves limit (R.cancellationDelivered w) f s valid eq | (R.complete result) = case eq of λ ()
step-preserves limit R.returnResult f s valid ()

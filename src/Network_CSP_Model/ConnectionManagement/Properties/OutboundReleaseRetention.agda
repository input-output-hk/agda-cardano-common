{-# OPTIONS --guardedness #-}

-- Outbound release changes entry values but never removes heap identities.
module ConnectionManagement.Properties.OutboundReleaseRetention where

open import Data.Bool using (true; false)
open import Data.Nat using (suc; _≤?_; _∸_)
open import Data.List using ([]; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Nullary using (yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.Pruning as P
import ConnectionManagement.Properties.ReleaseRetention as Edits
import ConnectionManagement.Properties.CleanupRetention as Retention

-- Transport a retained entry through the successful release result.
result-retains : ∀ {pair pair′ : R.Frame × State} q → just pair ≡ just pair′ →
  Present q (entries (cm (proj₂ pair))) → Present q (entries (cm (proj₂ pair′)))
result-retains q eq = subst (λ pair → Present q (entries (cm (proj₂ pair)))) (just-injective eq)

-- A single branch decision either leaves the heap or overwrites one entry.
apply-retains : ∀ e d f s q → Present q (entries (cm s)) →
  Present q (entries (cm (proj₂ (R.apply e d f s))))
apply-retains e d f s q present with R.replacement d
... | nothing = present
... | just st = put-preserves-present e q st (entries (cm s)) present

-- Capacity handling retains all old entries, including every pruning victim.
capacity-retains : ∀ limit scores m e old d f s {out} q → Present q (entries (cm s)) →
  R.capacity limit scores m e old d f s ≡ just out → Present q (entries (cm (proj₂ out)))
capacity-retains limit scores m e old d f s q present eq with R.needsCapacity d
... | false with scores
...   | nothing = result-retains q eq (apply-retains e d f s q present)
...   | just _ = case eq of λ ()
capacity-retains limit scores m e old d f s q present eq | true with countIncoming (entries (cm s)) m
... | nothing = case eq of λ ()
... | just n with suc n ≤? limit
...   | yes _ with scores
...     | nothing = result-retains q eq (apply-retains e d f s q present)
...     | just _ = case eq of λ ()
capacity-retains limit scores m e old d f s q present eq | true | just n | no _
  with scores | R.replacement d | P.candidates m (entries (cm s))
... | just draws | just st | just candidates with P.candidateFor (R.key f) e st
...   | nothing = case eq of λ ()
...   | just self with P.makePlan (suc n ∸ limit) self st candidates draws
...     | nothing = case eq of λ ()
...     | just selectedPlan with P.applyEdits (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s in edited
...       | nothing = case eq of λ ()
...       | just s′ = result-retains q eq (Retention.entriesRetained
  (Edits.edits-retains (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s edited) q present)
capacity-retains limit scores m e old d f s q present eq | true | just n | no _ | nothing | _ | _ = case eq of λ ()
capacity-retains limit scores m e old d f s q present eq | true | just n | no _ | just _ | nothing | _ = case eq of λ ()
capacity-retains limit scores m e old d f s q present eq | true | just n | no _ | just _ | just _ | nothing = case eq of λ ()

-- Transactional lookup only chooses which retention-preserving branch runs.
transact-retains : ∀ limit scores f s {out} q → Present q (entries (cm s)) →
  R.transact limit scores f s ≡ just out → Present q (entries (cm (proj₂ out)))
transact-retains limit scores f s q present eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with lookupConnection (R.key f) m
...   | nothing with scores
...     | nothing = result-retains q eq present
...     | just _ = case eq of λ ()
transact-retains limit scores f s q present eq | full m | just e with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st = capacity-retains limit scores m e st (R.branch (R.key f) e st) f s q present eq

-- Every release action preserves entries held by concurrent acquisitions.
step-retains : ∀ limit action f s {out} q → Present q (entries (cm s)) →
  R.step limit action f s ≡ just out → Present q (entries (cm (proj₂ out)))
step-retains limit R.transactionStep f s q present eq with R.pc f
... | R.transaction = transact-retains limit nothing f s q present eq
step-retains limit R.transactionStep f s q present eq | (R.check flag p) = case eq of λ ()
step-retains limit R.transactionStep f s q present eq | (R.count p) = case eq of λ ()
step-retains limit R.transactionStep f s q present eq | (R.armTimer e v) = case eq of λ ()
step-retains limit R.transactionStep f s q present eq | (R.waitIdle e v) = case eq of λ ()
step-retains limit R.transactionStep f s q present eq | (R.timeoutWrite e v) = case eq of λ ()
step-retains limit R.transactionStep f s q present eq | (R.cancel v p) = case eq of λ ()
step-retains limit R.transactionStep f s q present eq | (R.delivering v p) = case eq of λ ()
step-retains limit R.transactionStep f s q present eq | (R.prune victims result) = case eq of λ ()
step-retains limit R.transactionStep f s q present eq | (R.complete result) = case eq of λ ()
step-retains limit (R.transactionPruning scores) f s q present eq with R.pc f
... | R.transaction = transact-retains limit (just scores) f s q present eq
step-retains limit (R.transactionPruning scores) f s q present eq | (R.check flag p) = case eq of λ ()
step-retains limit (R.transactionPruning scores) f s q present eq | (R.count p) = case eq of λ ()
step-retains limit (R.transactionPruning scores) f s q present eq | (R.armTimer e v) = case eq of λ ()
step-retains limit (R.transactionPruning scores) f s q present eq | (R.waitIdle e v) = case eq of λ ()
step-retains limit (R.transactionPruning scores) f s q present eq | (R.timeoutWrite e v) = case eq of λ ()
step-retains limit (R.transactionPruning scores) f s q present eq | (R.cancel v p) = case eq of λ ()
step-retains limit (R.transactionPruning scores) f s q present eq | (R.delivering v p) = case eq of λ ()
step-retains limit (R.transactionPruning scores) f s q present eq | (R.prune victims result) = case eq of λ ()
step-retains limit (R.transactionPruning scores) f s q present eq | (R.complete result) = case eq of λ ()
step-retains limit R.checkAssertion f s q present eq with R.pc f
... | R.check true next = result-retains q eq present
... | R.check false next = result-retains q eq present
step-retains limit R.checkAssertion f s q present eq | (R.transaction) = case eq of λ ()
step-retains limit R.checkAssertion f s q present eq | (R.count p) = case eq of λ ()
step-retains limit R.checkAssertion f s q present eq | (R.armTimer e v) = case eq of λ ()
step-retains limit R.checkAssertion f s q present eq | (R.waitIdle e v) = case eq of λ ()
step-retains limit R.checkAssertion f s q present eq | (R.timeoutWrite e v) = case eq of λ ()
step-retains limit R.checkAssertion f s q present eq | (R.cancel v p) = case eq of λ ()
step-retains limit R.checkAssertion f s q present eq | (R.delivering v p) = case eq of λ ()
step-retains limit R.checkAssertion f s q present eq | (R.prune victims result) = case eq of λ ()
step-retains limit R.checkAssertion f s q present eq | (R.complete result) = case eq of λ ()
step-retains limit R.readCounters f s q present eq with R.pc f | mapCell (cm s)
... | R.count next | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = result-retains q eq present
step-retains limit R.readCounters f s q present eq | (R.transaction) | _ = case eq of λ ()
step-retains limit R.readCounters f s q present eq | (R.check flag p) | _ = case eq of λ ()
step-retains limit R.readCounters f s q present eq | (R.armTimer e v) | _ = case eq of λ ()
step-retains limit R.readCounters f s q present eq | (R.waitIdle e v) | _ = case eq of λ ()
step-retains limit R.readCounters f s q present eq | (R.timeoutWrite e v) | _ = case eq of λ ()
step-retains limit R.readCounters f s q present eq | (R.cancel v p) | _ = case eq of λ ()
step-retains limit R.readCounters f s q present eq | (R.delivering v p) | _ = case eq of λ ()
step-retains limit R.readCounters f s q present eq | (R.prune victims result) | _ = case eq of λ ()
step-retains limit R.readCounters f s q present eq | (R.complete result) | _ = case eq of λ ()
step-retains limit R.readCounters f s q present eq | (R.count p) | taken w = case eq of λ ()
step-retains limit R.registerTimer f s q present eq with R.pc f
... | R.armTimer e w = result-retains q eq present
step-retains limit R.registerTimer f s q present eq | (R.transaction) = case eq of λ ()
step-retains limit R.registerTimer f s q present eq | (R.check flag p) = case eq of λ ()
step-retains limit R.registerTimer f s q present eq | (R.count p) = case eq of λ ()
step-retains limit R.registerTimer f s q present eq | (R.waitIdle e v) = case eq of λ ()
step-retains limit R.registerTimer f s q present eq | (R.timeoutWrite e v) = case eq of λ ()
step-retains limit R.registerTimer f s q present eq | (R.cancel v p) = case eq of λ ()
step-retains limit R.registerTimer f s q present eq | (R.delivering v p) = case eq of λ ()
step-retains limit R.registerTimer f s q present eq | (R.prune victims result) = case eq of λ ()
step-retains limit R.registerTimer f s q present eq | (R.complete result) = case eq of λ ()
step-retains limit R.expireTimer f s q present eq with R.pc f | R.timerReady f
... | R.waitIdle e w | false = result-retains q eq present
step-retains limit R.expireTimer f s q present eq | (R.transaction) | _ = case eq of λ ()
step-retains limit R.expireTimer f s q present eq | (R.check flag p) | _ = case eq of λ ()
step-retains limit R.expireTimer f s q present eq | (R.count p) | _ = case eq of λ ()
step-retains limit R.expireTimer f s q present eq | (R.armTimer e v) | _ = case eq of λ ()
step-retains limit R.expireTimer f s q present eq | (R.timeoutWrite e v) | _ = case eq of λ ()
step-retains limit R.expireTimer f s q present eq | (R.cancel v p) | _ = case eq of λ ()
step-retains limit R.expireTimer f s q present eq | (R.delivering v p) | _ = case eq of λ ()
step-retains limit R.expireTimer f s q present eq | (R.prune victims result) | _ = case eq of λ ()
step-retains limit R.expireTimer f s q present eq | (R.complete result) | _ = case eq of λ ()
step-retains limit R.expireTimer f s q present eq | (R.waitIdle e v) | true = case eq of λ ()
step-retains limit R.selectWakeup f s q present eq with R.pc f
... | R.waitIdle e w with lookup e (entries (cm s))
...   | nothing = case eq of λ ()
...   | just st with R.isIdle st | R.isTerminated st | R.timerReady f
...     | false | true | _ = result-retains q eq present
...     | false | false | _ = result-retains q eq present
...     | true | _ | true = result-retains q eq present
...     | true | _ | false = case eq of λ ()
step-retains limit R.selectWakeup f s q present eq | (R.transaction) = case eq of λ ()
step-retains limit R.selectWakeup f s q present eq | (R.check flag p) = case eq of λ ()
step-retains limit R.selectWakeup f s q present eq | (R.count p) = case eq of λ ()
step-retains limit R.selectWakeup f s q present eq | (R.armTimer e v) = case eq of λ ()
step-retains limit R.selectWakeup f s q present eq | (R.timeoutWrite e v) = case eq of λ ()
step-retains limit R.selectWakeup f s q present eq | (R.cancel v p) = case eq of λ ()
step-retains limit R.selectWakeup f s q present eq | (R.delivering v p) = case eq of λ ()
step-retains limit R.selectWakeup f s q present eq | (R.prune victims result) = case eq of λ ()
step-retains limit R.selectWakeup f s q present eq | (R.complete result) = case eq of λ ()
step-retains limit R.commitTimeout f s q present eq with R.pc f
... | R.timeoutWrite e w with lookup e (entries (cm s))
...   | nothing = case eq of λ ()
...   | just _ = result-retains q eq (put-preserves-present e q (terminating (R.key f) w nothing) (entries (cm s)) present)
step-retains limit R.commitTimeout f s q present eq | (R.transaction) = case eq of λ ()
step-retains limit R.commitTimeout f s q present eq | (R.check flag p) = case eq of λ ()
step-retains limit R.commitTimeout f s q present eq | (R.count p) = case eq of λ ()
step-retains limit R.commitTimeout f s q present eq | (R.armTimer e v) = case eq of λ ()
step-retains limit R.commitTimeout f s q present eq | (R.waitIdle e v) = case eq of λ ()
step-retains limit R.commitTimeout f s q present eq | (R.cancel v p) = case eq of λ ()
step-retains limit R.commitTimeout f s q present eq | (R.delivering v p) = case eq of λ ()
step-retains limit R.commitTimeout f s q present eq | (R.prune victims result) = case eq of λ ()
step-retains limit R.commitTimeout f s q present eq | (R.complete result) = case eq of λ ()
step-retains limit R.requestCancellation f s q present eq with R.pc f
... | R.cancel w next = result-retains q eq present
... | R.prune [] result = result-retains q eq present
... | R.prune (victim ∷ rest) result = result-retains q eq present
step-retains limit R.requestCancellation f s q present eq | (R.transaction) = case eq of λ ()
step-retains limit R.requestCancellation f s q present eq | (R.check flag p) = case eq of λ ()
step-retains limit R.requestCancellation f s q present eq | (R.count p) = case eq of λ ()
step-retains limit R.requestCancellation f s q present eq | (R.armTimer e v) = case eq of λ ()
step-retains limit R.requestCancellation f s q present eq | (R.waitIdle e v) = case eq of λ ()
step-retains limit R.requestCancellation f s q present eq | (R.timeoutWrite e v) = case eq of λ ()
step-retains limit R.requestCancellation f s q present eq | (R.delivering v p) = case eq of λ ()
step-retains limit R.requestCancellation f s q present eq | (R.complete result) = case eq of λ ()
step-retains limit (R.cancellationDelivered w) f s q present eq with R.pc f
... | R.delivering v next with w ≟ v
...   | yes _ = result-retains q eq present
...   | no _ = case eq of λ ()
step-retains limit (R.cancellationDelivered w) f s q present eq | (R.transaction) = case eq of λ ()
step-retains limit (R.cancellationDelivered w) f s q present eq | (R.check flag p) = case eq of λ ()
step-retains limit (R.cancellationDelivered w) f s q present eq | (R.count p) = case eq of λ ()
step-retains limit (R.cancellationDelivered w) f s q present eq | (R.armTimer e v) = case eq of λ ()
step-retains limit (R.cancellationDelivered w) f s q present eq | (R.waitIdle e v) = case eq of λ ()
step-retains limit (R.cancellationDelivered w) f s q present eq | (R.timeoutWrite e v) = case eq of λ ()
step-retains limit (R.cancellationDelivered w) f s q present eq | (R.cancel v p) = case eq of λ ()
step-retains limit (R.cancellationDelivered w) f s q present eq | (R.prune victims result) = case eq of λ ()
step-retains limit (R.cancellationDelivered w) f s q present eq | (R.complete result) = case eq of λ ()
step-retains limit R.returnResult f s q present ()

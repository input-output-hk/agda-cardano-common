{-# OPTIONS --guardedness #-}

-- Full shared-store retention for every successful outbound release action.
module ConnectionManagement.Properties.OutboundReleaseEffects where

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
import ConnectionManagement.Rules.OutboundRelease as R
import ConnectionManagement.Rules.Pruning as P
import ConnectionManagement.Properties.ReleaseRetention as Edits
import ConnectionManagement.Properties.CleanupRetention as Retention

open import ConnectionManagement.Properties.SharedStateEffects

-- Transport store effects through an exact pair result.
result-retains : ∀ {before} {pair pair′ : R.Frame × State} → just pair ≡ just pair′ →
  Effects before (proj₂ pair) → Effects before (proj₂ pair′)
result-retains {before} eq = subst (λ pair → Effects before (proj₂ pair)) (just-injective eq)

-- A release branch writes only an entry value.
apply-retains : ∀ e d f s → Effects s (proj₂ (R.apply e d f s))
apply-retains e d f s with R.replacement d
... | nothing = identity s
... | just st = entry-write e st s

-- Atomic pruning transports all shared-store effects.
capacity-retains : ∀ limit scores m e old d f s {out} → R.capacity limit scores m e old d f s ≡ just out → Effects s (proj₂ out)
capacity-retains limit scores m e old d f s eq with R.needsCapacity d
... | false with scores
...   | nothing = result-retains {before = s} eq (apply-retains e d f s)
...   | just _ = case eq of λ ()
capacity-retains limit scores m e old d f s eq | true with countIncoming (entries (cm s)) m
... | nothing = case eq of λ ()
... | just n with suc n ≤? limit
...   | yes _ with scores
...     | nothing = result-retains {before = s} eq (apply-retains e d f s)
...     | just _ = case eq of λ ()
capacity-retains limit scores m e old d f s eq | true | just n | no _
  with scores | R.replacement d | P.candidates m (entries (cm s))
... | just draws | just st | just candidates with P.candidateFor (R.key f) e st
...   | nothing = case eq of λ ()
...   | just self with P.makePlan (suc n ∸ limit) self st candidates draws
...     | nothing = case eq of λ ()
...     | just selectedPlan with P.applyEdits (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s in edited
...       | nothing = case eq of λ ()
...       | just s′ = result-retains {before = s} eq (from-cleanup
  (Edits.edits-retains (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s edited))
capacity-retains limit scores m e old d f s eq | true | just n | no _ | nothing | _ | _ = case eq of λ ()
capacity-retains limit scores m e old d f s eq | true | just n | no _ | just _ | nothing | _ = case eq of λ ()
capacity-retains limit scores m e old d f s eq | true | just n | no _ | just _ | just _ | nothing = case eq of λ ()

-- The transaction selects one of the checked release branches.
transact-retains : ∀ limit scores f s {out} → R.transact limit scores f s ≡ just out → Effects s (proj₂ out)
transact-retains limit scores f s eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with lookupConnection (R.key f) m
...   | nothing with scores
...     | nothing = result-retains {before = s} eq (identity s)
...     | just _ = case eq of λ ()
transact-retains limit scores f s eq | full m | just e with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st = capacity-retains limit scores m e st (R.branch (R.key f) e st) f s eq

-- Exhaust every successful action without a frame-validity premise.
step-effects : ∀ limit action f s {out} → R.step limit action f s ≡ just out → Effects s (proj₂ out)
step-effects limit R.transactionStep f s eq with R.pc f
... | R.transaction = transact-retains limit nothing f s eq
step-effects limit R.transactionStep f s eq | (R.check flag p) = case eq of λ ()
step-effects limit R.transactionStep f s eq | (R.count p) = case eq of λ ()
step-effects limit R.transactionStep f s eq | (R.armTimer e v) = case eq of λ ()
step-effects limit R.transactionStep f s eq | (R.waitIdle e v) = case eq of λ ()
step-effects limit R.transactionStep f s eq | (R.timeoutWrite e v) = case eq of λ ()
step-effects limit R.transactionStep f s eq | (R.cancel v p) = case eq of λ ()
step-effects limit R.transactionStep f s eq | (R.delivering v p) = case eq of λ ()
step-effects limit R.transactionStep f s eq | (R.prune victims result) = case eq of λ ()
step-effects limit R.transactionStep f s eq | (R.complete result) = case eq of λ ()
step-effects limit (R.transactionPruning scores) f s eq with R.pc f
... | R.transaction = transact-retains limit (just scores) f s eq
step-effects limit (R.transactionPruning scores) f s eq | (R.check flag p) = case eq of λ ()
step-effects limit (R.transactionPruning scores) f s eq | (R.count p) = case eq of λ ()
step-effects limit (R.transactionPruning scores) f s eq | (R.armTimer e v) = case eq of λ ()
step-effects limit (R.transactionPruning scores) f s eq | (R.waitIdle e v) = case eq of λ ()
step-effects limit (R.transactionPruning scores) f s eq | (R.timeoutWrite e v) = case eq of λ ()
step-effects limit (R.transactionPruning scores) f s eq | (R.cancel v p) = case eq of λ ()
step-effects limit (R.transactionPruning scores) f s eq | (R.delivering v p) = case eq of λ ()
step-effects limit (R.transactionPruning scores) f s eq | (R.prune victims result) = case eq of λ ()
step-effects limit (R.transactionPruning scores) f s eq | (R.complete result) = case eq of λ ()
step-effects limit R.checkAssertion f s eq with R.pc f
... | R.check true next = result-retains {before = s} eq (identity s)
... | R.check false next = result-retains {before = s} eq (identity s)
step-effects limit R.checkAssertion f s eq | (R.transaction) = case eq of λ ()
step-effects limit R.checkAssertion f s eq | (R.count p) = case eq of λ ()
step-effects limit R.checkAssertion f s eq | (R.armTimer e v) = case eq of λ ()
step-effects limit R.checkAssertion f s eq | (R.waitIdle e v) = case eq of λ ()
step-effects limit R.checkAssertion f s eq | (R.timeoutWrite e v) = case eq of λ ()
step-effects limit R.checkAssertion f s eq | (R.cancel v p) = case eq of λ ()
step-effects limit R.checkAssertion f s eq | (R.delivering v p) = case eq of λ ()
step-effects limit R.checkAssertion f s eq | (R.prune victims result) = case eq of λ ()
step-effects limit R.checkAssertion f s eq | (R.complete result) = case eq of λ ()
step-effects limit R.readCounters f s eq with R.pc f | mapCell (cm s)
... | R.count next | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = result-retains {before = s} eq (identity s)
step-effects limit R.readCounters f s eq | (R.transaction) | _ = case eq of λ ()
step-effects limit R.readCounters f s eq | (R.check flag p) | _ = case eq of λ ()
step-effects limit R.readCounters f s eq | (R.armTimer e v) | _ = case eq of λ ()
step-effects limit R.readCounters f s eq | (R.waitIdle e v) | _ = case eq of λ ()
step-effects limit R.readCounters f s eq | (R.timeoutWrite e v) | _ = case eq of λ ()
step-effects limit R.readCounters f s eq | (R.cancel v p) | _ = case eq of λ ()
step-effects limit R.readCounters f s eq | (R.delivering v p) | _ = case eq of λ ()
step-effects limit R.readCounters f s eq | (R.prune victims result) | _ = case eq of λ ()
step-effects limit R.readCounters f s eq | (R.complete result) | _ = case eq of λ ()
step-effects limit R.readCounters f s eq | (R.count p) | taken w = case eq of λ ()
step-effects limit R.registerTimer f s eq with R.pc f
... | R.armTimer e w = result-retains {before = s} eq (identity s)
step-effects limit R.registerTimer f s eq | (R.transaction) = case eq of λ ()
step-effects limit R.registerTimer f s eq | (R.check flag p) = case eq of λ ()
step-effects limit R.registerTimer f s eq | (R.count p) = case eq of λ ()
step-effects limit R.registerTimer f s eq | (R.waitIdle e v) = case eq of λ ()
step-effects limit R.registerTimer f s eq | (R.timeoutWrite e v) = case eq of λ ()
step-effects limit R.registerTimer f s eq | (R.cancel v p) = case eq of λ ()
step-effects limit R.registerTimer f s eq | (R.delivering v p) = case eq of λ ()
step-effects limit R.registerTimer f s eq | (R.prune victims result) = case eq of λ ()
step-effects limit R.registerTimer f s eq | (R.complete result) = case eq of λ ()
step-effects limit R.expireTimer f s eq with R.pc f | R.timerReady f
... | R.waitIdle e w | false = result-retains {before = s} eq (identity s)
step-effects limit R.expireTimer f s eq | (R.transaction) | _ = case eq of λ ()
step-effects limit R.expireTimer f s eq | (R.check flag p) | _ = case eq of λ ()
step-effects limit R.expireTimer f s eq | (R.count p) | _ = case eq of λ ()
step-effects limit R.expireTimer f s eq | (R.armTimer e v) | _ = case eq of λ ()
step-effects limit R.expireTimer f s eq | (R.timeoutWrite e v) | _ = case eq of λ ()
step-effects limit R.expireTimer f s eq | (R.cancel v p) | _ = case eq of λ ()
step-effects limit R.expireTimer f s eq | (R.delivering v p) | _ = case eq of λ ()
step-effects limit R.expireTimer f s eq | (R.prune victims result) | _ = case eq of λ ()
step-effects limit R.expireTimer f s eq | (R.complete result) | _ = case eq of λ ()
step-effects limit R.expireTimer f s eq | (R.waitIdle e v) | true = case eq of λ ()
step-effects limit R.selectWakeup f s eq with R.pc f
... | R.waitIdle e w with lookup e (entries (cm s))
...   | nothing = case eq of λ ()
...   | just st with R.isIdle st | R.isTerminated st | R.timerReady f
...     | false | true | _ = result-retains {before = s} eq (identity s)
...     | false | false | _ = result-retains {before = s} eq (identity s)
...     | true | _ | true = result-retains {before = s} eq (identity s)
...     | true | _ | false = case eq of λ ()
step-effects limit R.selectWakeup f s eq | (R.transaction) = case eq of λ ()
step-effects limit R.selectWakeup f s eq | (R.check flag p) = case eq of λ ()
step-effects limit R.selectWakeup f s eq | (R.count p) = case eq of λ ()
step-effects limit R.selectWakeup f s eq | (R.armTimer e v) = case eq of λ ()
step-effects limit R.selectWakeup f s eq | (R.timeoutWrite e v) = case eq of λ ()
step-effects limit R.selectWakeup f s eq | (R.cancel v p) = case eq of λ ()
step-effects limit R.selectWakeup f s eq | (R.delivering v p) = case eq of λ ()
step-effects limit R.selectWakeup f s eq | (R.prune victims result) = case eq of λ ()
step-effects limit R.selectWakeup f s eq | (R.complete result) = case eq of λ ()
step-effects limit R.commitTimeout f s eq with R.pc f
... | R.timeoutWrite e w with lookup e (entries (cm s))
...   | nothing = case eq of λ ()
...   | just _ = result-retains {before = s} eq (entry-write e (terminating (R.key f) w nothing) s)
step-effects limit R.commitTimeout f s eq | (R.transaction) = case eq of λ ()
step-effects limit R.commitTimeout f s eq | (R.check flag p) = case eq of λ ()
step-effects limit R.commitTimeout f s eq | (R.count p) = case eq of λ ()
step-effects limit R.commitTimeout f s eq | (R.armTimer e v) = case eq of λ ()
step-effects limit R.commitTimeout f s eq | (R.waitIdle e v) = case eq of λ ()
step-effects limit R.commitTimeout f s eq | (R.cancel v p) = case eq of λ ()
step-effects limit R.commitTimeout f s eq | (R.delivering v p) = case eq of λ ()
step-effects limit R.commitTimeout f s eq | (R.prune victims result) = case eq of λ ()
step-effects limit R.commitTimeout f s eq | (R.complete result) = case eq of λ ()
step-effects limit R.requestCancellation f s eq with R.pc f
... | R.cancel w next = result-retains {before = s} eq (identity s)
... | R.prune [] result = result-retains {before = s} eq (identity s)
... | R.prune (victim ∷ rest) result = result-retains {before = s} eq (identity s)
step-effects limit R.requestCancellation f s eq | (R.transaction) = case eq of λ ()
step-effects limit R.requestCancellation f s eq | (R.check flag p) = case eq of λ ()
step-effects limit R.requestCancellation f s eq | (R.count p) = case eq of λ ()
step-effects limit R.requestCancellation f s eq | (R.armTimer e v) = case eq of λ ()
step-effects limit R.requestCancellation f s eq | (R.waitIdle e v) = case eq of λ ()
step-effects limit R.requestCancellation f s eq | (R.timeoutWrite e v) = case eq of λ ()
step-effects limit R.requestCancellation f s eq | (R.delivering v p) = case eq of λ ()
step-effects limit R.requestCancellation f s eq | (R.complete result) = case eq of λ ()
step-effects limit (R.cancellationDelivered w) f s eq with R.pc f
... | R.delivering v next with w ≟ v
...   | yes _ = result-retains {before = s} eq (identity s)
...   | no _ = case eq of λ ()
step-effects limit (R.cancellationDelivered w) f s eq | (R.transaction) = case eq of λ ()
step-effects limit (R.cancellationDelivered w) f s eq | (R.check flag p) = case eq of λ ()
step-effects limit (R.cancellationDelivered w) f s eq | (R.count p) = case eq of λ ()
step-effects limit (R.cancellationDelivered w) f s eq | (R.armTimer e v) = case eq of λ ()
step-effects limit (R.cancellationDelivered w) f s eq | (R.waitIdle e v) = case eq of λ ()
step-effects limit (R.cancellationDelivered w) f s eq | (R.timeoutWrite e v) = case eq of λ ()
step-effects limit (R.cancellationDelivered w) f s eq | (R.cancel v p) = case eq of λ ()
step-effects limit (R.cancellationDelivered w) f s eq | (R.prune victims result) = case eq of λ ()
step-effects limit (R.cancellationDelivered w) f s eq | (R.complete result) = case eq of λ ()
step-effects limit R.returnResult f s ()

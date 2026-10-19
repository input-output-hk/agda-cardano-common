{-# OPTIONS --guardedness #-}

-- All successful outbound release steps preserve a fixed handler and its resources.
module ConnectionManagement.Properties.OutboundReleaseResources where

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

open import ConnectionManagement.Properties.HandlerResourceFacts

-- The observer may differ from the caller and the newly forked child.
module For (q : WorkerId) (captured : HandlerStart) where

  -- Transport facts through the exact successful result.
  result-retains : ∀ {pair pair′ : R.Frame × State} → just pair ≡ just pair′ →
    Facts q captured (proj₂ pair) → Facts q captured (proj₂ pair′)
  result-retains eq = subst (λ pair → Facts q captured (proj₂ pair)) (just-injective eq)

  -- A release decision may overwrite an entry but retains its identity.
  apply-retains : ∀ e d f s → Facts q captured s →
    Facts q captured (proj₂ (R.apply e d f s))
  apply-retains e d f s facts with R.replacement d
  ... | nothing = facts
  ... | just st = entry-write e st s facts

  -- Pruning transports facts for every existing handler, including victims.
  capacity-retains : ∀ limit scores m e old d f s {out} → Facts q captured s →
    R.capacity limit scores m e old d f s ≡ just out → Facts q captured (proj₂ out)
  capacity-retains limit scores m e old d f s facts eq with R.needsCapacity d
  ... | false with scores
  ...   | nothing = result-retains eq (apply-retains e d f s facts)
  ...   | just _ = case eq of λ ()
  capacity-retains limit scores m e old d f s facts eq | true with countIncoming (entries (cm s)) m
  ... | nothing = case eq of λ ()
  ... | just n with suc n ≤? limit
  ...   | yes _ with scores
  ...     | nothing = result-retains eq (apply-retains e d f s facts)
  ...     | just _ = case eq of λ ()
  capacity-retains limit scores m e old d f s facts eq | true | just n | no _
    with scores | R.replacement d | P.candidates m (entries (cm s))
  ... | just draws | just st | just candidates with P.candidateFor (R.key f) e st
  ...   | nothing = case eq of λ ()
  ...   | just self with P.makePlan (suc n ∸ limit) self st candidates draws
  ...     | nothing = case eq of λ ()
  ...     | just selectedPlan with P.applyEdits (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s in edited
  ...       | nothing = case eq of λ ()
  ...       | just s′ = result-retains eq (cleanup-retained
    (Edits.edits-retains (map (λ c → P.entryRef c , terminated nothing) (P.victims selectedPlan)) s edited) facts)
  capacity-retains limit scores m e old d f s facts eq | true | just n | no _ | nothing | _ | _ = case eq of λ ()
  capacity-retains limit scores m e old d f s facts eq | true | just n | no _ | just _ | nothing | _ = case eq of λ ()
  capacity-retains limit scores m e old d f s facts eq | true | just n | no _ | just _ | just _ | nothing = case eq of λ ()

  -- Transactional lookup selects one of the proved release branches.
  transact-retains : ∀ limit scores f s {out} → Facts q captured s →
    R.transact limit scores f s ≡ just out → Facts q captured (proj₂ out)
  transact-retains limit scores f s facts eq with mapCell (cm s)
  ... | taken _ = case eq of λ ()
  ... | full m with lookupConnection (R.key f) m
  ...   | nothing with scores
  ...     | nothing = result-retains eq facts
  ...     | just _ = case eq of λ ()
  transact-retains limit scores f s facts eq | full m | just e with lookup e (entries (cm s))
  ... | nothing = case eq of λ ()
  ... | just st = capacity-retains limit scores m e st (R.branch (R.key f) e st) f s facts eq

  -- Exhaust all successful actions, including fork, socket close and IO failure.
  step-retains : ∀ limit action f s {out} → Facts q captured s →
    R.step limit action f s ≡ just out → Facts q captured (proj₂ out)
  step-retains limit R.transactionStep f s facts eq with R.pc f
  ... | R.transaction = transact-retains limit nothing f s facts eq
  step-retains limit R.transactionStep f s facts eq | (R.check flag p) = case eq of λ ()
  step-retains limit R.transactionStep f s facts eq | (R.count p) = case eq of λ ()
  step-retains limit R.transactionStep f s facts eq | (R.armTimer e v) = case eq of λ ()
  step-retains limit R.transactionStep f s facts eq | (R.waitIdle e v) = case eq of λ ()
  step-retains limit R.transactionStep f s facts eq | (R.timeoutWrite e v) = case eq of λ ()
  step-retains limit R.transactionStep f s facts eq | (R.cancel v p) = case eq of λ ()
  step-retains limit R.transactionStep f s facts eq | (R.delivering v p) = case eq of λ ()
  step-retains limit R.transactionStep f s facts eq | (R.prune victims result) = case eq of λ ()
  step-retains limit R.transactionStep f s facts eq | (R.complete result) = case eq of λ ()
  step-retains limit (R.transactionPruning scores) f s facts eq with R.pc f
  ... | R.transaction = transact-retains limit (just scores) f s facts eq
  step-retains limit (R.transactionPruning scores) f s facts eq | (R.check flag p) = case eq of λ ()
  step-retains limit (R.transactionPruning scores) f s facts eq | (R.count p) = case eq of λ ()
  step-retains limit (R.transactionPruning scores) f s facts eq | (R.armTimer e v) = case eq of λ ()
  step-retains limit (R.transactionPruning scores) f s facts eq | (R.waitIdle e v) = case eq of λ ()
  step-retains limit (R.transactionPruning scores) f s facts eq | (R.timeoutWrite e v) = case eq of λ ()
  step-retains limit (R.transactionPruning scores) f s facts eq | (R.cancel v p) = case eq of λ ()
  step-retains limit (R.transactionPruning scores) f s facts eq | (R.delivering v p) = case eq of λ ()
  step-retains limit (R.transactionPruning scores) f s facts eq | (R.prune victims result) = case eq of λ ()
  step-retains limit (R.transactionPruning scores) f s facts eq | (R.complete result) = case eq of λ ()
  step-retains limit R.checkAssertion f s facts eq with R.pc f
  ... | R.check true next = result-retains eq facts
  ... | R.check false next = result-retains eq facts
  step-retains limit R.checkAssertion f s facts eq | (R.transaction) = case eq of λ ()
  step-retains limit R.checkAssertion f s facts eq | (R.count p) = case eq of λ ()
  step-retains limit R.checkAssertion f s facts eq | (R.armTimer e v) = case eq of λ ()
  step-retains limit R.checkAssertion f s facts eq | (R.waitIdle e v) = case eq of λ ()
  step-retains limit R.checkAssertion f s facts eq | (R.timeoutWrite e v) = case eq of λ ()
  step-retains limit R.checkAssertion f s facts eq | (R.cancel v p) = case eq of λ ()
  step-retains limit R.checkAssertion f s facts eq | (R.delivering v p) = case eq of λ ()
  step-retains limit R.checkAssertion f s facts eq | (R.prune victims result) = case eq of λ ()
  step-retains limit R.checkAssertion f s facts eq | (R.complete result) = case eq of λ ()
  step-retains limit R.readCounters f s facts eq with R.pc f | mapCell (cm s)
  ... | R.count next | full m with countIncoming (entries (cm s)) m
  ...   | nothing = case eq of λ ()
  ...   | just _ = result-retains eq facts
  step-retains limit R.readCounters f s facts eq | (R.transaction) | _ = case eq of λ ()
  step-retains limit R.readCounters f s facts eq | (R.check flag p) | _ = case eq of λ ()
  step-retains limit R.readCounters f s facts eq | (R.armTimer e v) | _ = case eq of λ ()
  step-retains limit R.readCounters f s facts eq | (R.waitIdle e v) | _ = case eq of λ ()
  step-retains limit R.readCounters f s facts eq | (R.timeoutWrite e v) | _ = case eq of λ ()
  step-retains limit R.readCounters f s facts eq | (R.cancel v p) | _ = case eq of λ ()
  step-retains limit R.readCounters f s facts eq | (R.delivering v p) | _ = case eq of λ ()
  step-retains limit R.readCounters f s facts eq | (R.prune victims result) | _ = case eq of λ ()
  step-retains limit R.readCounters f s facts eq | (R.complete result) | _ = case eq of λ ()
  step-retains limit R.readCounters f s facts eq | (R.count p) | taken w = case eq of λ ()
  step-retains limit R.registerTimer f s facts eq with R.pc f
  ... | R.armTimer e w = result-retains eq facts
  step-retains limit R.registerTimer f s facts eq | (R.transaction) = case eq of λ ()
  step-retains limit R.registerTimer f s facts eq | (R.check flag p) = case eq of λ ()
  step-retains limit R.registerTimer f s facts eq | (R.count p) = case eq of λ ()
  step-retains limit R.registerTimer f s facts eq | (R.waitIdle e v) = case eq of λ ()
  step-retains limit R.registerTimer f s facts eq | (R.timeoutWrite e v) = case eq of λ ()
  step-retains limit R.registerTimer f s facts eq | (R.cancel v p) = case eq of λ ()
  step-retains limit R.registerTimer f s facts eq | (R.delivering v p) = case eq of λ ()
  step-retains limit R.registerTimer f s facts eq | (R.prune victims result) = case eq of λ ()
  step-retains limit R.registerTimer f s facts eq | (R.complete result) = case eq of λ ()
  step-retains limit R.expireTimer f s facts eq with R.pc f | R.timerReady f
  ... | R.waitIdle e w | false = result-retains eq facts
  step-retains limit R.expireTimer f s facts eq | (R.transaction) | _ = case eq of λ ()
  step-retains limit R.expireTimer f s facts eq | (R.check flag p) | _ = case eq of λ ()
  step-retains limit R.expireTimer f s facts eq | (R.count p) | _ = case eq of λ ()
  step-retains limit R.expireTimer f s facts eq | (R.armTimer e v) | _ = case eq of λ ()
  step-retains limit R.expireTimer f s facts eq | (R.timeoutWrite e v) | _ = case eq of λ ()
  step-retains limit R.expireTimer f s facts eq | (R.cancel v p) | _ = case eq of λ ()
  step-retains limit R.expireTimer f s facts eq | (R.delivering v p) | _ = case eq of λ ()
  step-retains limit R.expireTimer f s facts eq | (R.prune victims result) | _ = case eq of λ ()
  step-retains limit R.expireTimer f s facts eq | (R.complete result) | _ = case eq of λ ()
  step-retains limit R.expireTimer f s facts eq | (R.waitIdle e v) | true = case eq of λ ()
  step-retains limit R.selectWakeup f s facts eq with R.pc f
  ... | R.waitIdle e w with lookup e (entries (cm s))
  ...   | nothing = case eq of λ ()
  ...   | just st with R.isIdle st | R.isTerminated st | R.timerReady f
  ...     | false | true | _ = result-retains eq facts
  ...     | false | false | _ = result-retains eq facts
  ...     | true | _ | true = result-retains eq facts
  ...     | true | _ | false = case eq of λ ()
  step-retains limit R.selectWakeup f s facts eq | (R.transaction) = case eq of λ ()
  step-retains limit R.selectWakeup f s facts eq | (R.check flag p) = case eq of λ ()
  step-retains limit R.selectWakeup f s facts eq | (R.count p) = case eq of λ ()
  step-retains limit R.selectWakeup f s facts eq | (R.armTimer e v) = case eq of λ ()
  step-retains limit R.selectWakeup f s facts eq | (R.timeoutWrite e v) = case eq of λ ()
  step-retains limit R.selectWakeup f s facts eq | (R.cancel v p) = case eq of λ ()
  step-retains limit R.selectWakeup f s facts eq | (R.delivering v p) = case eq of λ ()
  step-retains limit R.selectWakeup f s facts eq | (R.prune victims result) = case eq of λ ()
  step-retains limit R.selectWakeup f s facts eq | (R.complete result) = case eq of λ ()
  step-retains limit R.commitTimeout f s facts eq with R.pc f
  ... | R.timeoutWrite e w with lookup e (entries (cm s))
  ...   | nothing = case eq of λ ()
  ...   | just _ = result-retains eq (entry-write e (terminating (R.key f) w nothing) s facts)
  step-retains limit R.commitTimeout f s facts eq | (R.transaction) = case eq of λ ()
  step-retains limit R.commitTimeout f s facts eq | (R.check flag p) = case eq of λ ()
  step-retains limit R.commitTimeout f s facts eq | (R.count p) = case eq of λ ()
  step-retains limit R.commitTimeout f s facts eq | (R.armTimer e v) = case eq of λ ()
  step-retains limit R.commitTimeout f s facts eq | (R.waitIdle e v) = case eq of λ ()
  step-retains limit R.commitTimeout f s facts eq | (R.cancel v p) = case eq of λ ()
  step-retains limit R.commitTimeout f s facts eq | (R.delivering v p) = case eq of λ ()
  step-retains limit R.commitTimeout f s facts eq | (R.prune victims result) = case eq of λ ()
  step-retains limit R.commitTimeout f s facts eq | (R.complete result) = case eq of λ ()
  step-retains limit R.requestCancellation f s facts eq with R.pc f
  ... | R.cancel w next = result-retains eq facts
  ... | R.prune [] result = result-retains eq facts
  ... | R.prune (victim ∷ rest) result = result-retains eq facts
  step-retains limit R.requestCancellation f s facts eq | (R.transaction) = case eq of λ ()
  step-retains limit R.requestCancellation f s facts eq | (R.check flag p) = case eq of λ ()
  step-retains limit R.requestCancellation f s facts eq | (R.count p) = case eq of λ ()
  step-retains limit R.requestCancellation f s facts eq | (R.armTimer e v) = case eq of λ ()
  step-retains limit R.requestCancellation f s facts eq | (R.waitIdle e v) = case eq of λ ()
  step-retains limit R.requestCancellation f s facts eq | (R.timeoutWrite e v) = case eq of λ ()
  step-retains limit R.requestCancellation f s facts eq | (R.delivering v p) = case eq of λ ()
  step-retains limit R.requestCancellation f s facts eq | (R.complete result) = case eq of λ ()
  step-retains limit (R.cancellationDelivered w) f s facts eq with R.pc f
  ... | R.delivering v next with w ≟ v
  ...   | yes _ = result-retains eq facts
  ...   | no _ = case eq of λ ()
  step-retains limit (R.cancellationDelivered w) f s facts eq | (R.transaction) = case eq of λ ()
  step-retains limit (R.cancellationDelivered w) f s facts eq | (R.check flag p) = case eq of λ ()
  step-retains limit (R.cancellationDelivered w) f s facts eq | (R.count p) = case eq of λ ()
  step-retains limit (R.cancellationDelivered w) f s facts eq | (R.armTimer e v) = case eq of λ ()
  step-retains limit (R.cancellationDelivered w) f s facts eq | (R.waitIdle e v) = case eq of λ ()
  step-retains limit (R.cancellationDelivered w) f s facts eq | (R.timeoutWrite e v) = case eq of λ ()
  step-retains limit (R.cancellationDelivered w) f s facts eq | (R.cancel v p) = case eq of λ ()
  step-retains limit (R.cancellationDelivered w) f s facts eq | (R.prune victims result) = case eq of λ ()
  step-retains limit (R.cancellationDelivered w) f s facts eq | (R.complete result) = case eq of λ ()
  step-retains limit R.returnResult f s facts ()

{-# OPTIONS --guardedness #-}

-- Resource preservation through all outbound-machine interleavings.
module ConnectionManagement.Properties.OutboundRuntimeResources where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
open import ConnectionManagement.OutboundMachine
open import ConnectionManagement.Store using (lookup)
open import Data.List using ([]; _∷_)
open import ConnectionManagement.Properties.HandlerResourceFacts
open import ConnectionManagement.Properties.HandlerResources using (Resources; original)
import ConnectionManagement.Properties.HandlerDispatcherInterference as Inbound
import ConnectionManagement.Properties.OutboundAcquireResources as Acquire
import ConnectionManagement.Properties.OutboundReleaseResources as Release
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R


-- Fixing the descriptor also excludes retargeting the original handler.
module For (q : WorkerId) (captured : S.HandlerStart) where

  -- Observe fixed handler/resource facts in the shared world.
  RuntimeValid : A.Runtime → S.State → Set
  RuntimeValid rt s = Facts q captured s

  -- Outbound frames do not add premises to the observed resource facts.
  Valid : Configuration → Set
  Valid c = RuntimeValid (acquiring c) (I.world (core c))

  -- Apply the selected acquisition frame proof to the shared world.
  acquisition-resources : ∀ w action c f {f′ s′} →
    A.step w (I.responder (core c)) action f (I.world (core c)) ≡ just (f′ , s′) →
    Valid c → Facts q captured s′
  acquisition-resources w action c f stepped valid =
    Acquire.For.step-retains q captured w (I.responder (core c)) action f (I.world (core c)) valid stepped

  -- Returning deletes only the caller frame; all other actions use the writer proof.
  acquire-preserves : ∀ w action c {c′} → advanceAcquire w action c ≡ just c′ →
    Valid c → Valid c′
  acquire-preserves w A.returnResult c eq valid with lookup w (acquiring c)
  ... | nothing = case eq of λ ()
  ... | just f with A.pc f
  ...   | A.complete result = subst Valid (just-injective eq)
    valid
  ...   | A.selecting = case eq of λ ()
  ...   | A.count p = case eq of λ ()
  ...   | A.allocatePromise e = case eq of λ ()
  ...   | A.openSocket e p = case eq of λ ()
  ...   | A.configureSocket e p = case eq of λ ()
  ...   | A.bindSocket e p = case eq of λ ()
  ...   | A.connectSocket e p = case eq of λ ()
  ...   | A.localAddress e p = case eq of λ ()
  ...   | A.updateAddress e p k = case eq of λ ()
  ...   | A.forkHandler e p k = case eq of λ ()
  ...   | A.connectedCommit e p k = case eq of λ ()
  ...   | A.awaitResult e p k = case eq of λ ()
  ...   | A.commitResult e k result = case eq of λ ()
  ...   | A.waitingInbound e k = case eq of λ ()
  ...   | A.closeError e err = case eq of λ ()
  ...   | A.removeError e err = case eq of λ ()
  acquire-preserves w (A.select chosen) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.select chosen) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.select chosen) c f stepped valid)
  acquire-preserves w (A.readCounters) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.readCounters) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.readCounters) c f stepped valid)
  acquire-preserves w (A.newPromise) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.newPromise) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.newPromise) c f stepped valid)
  acquire-preserves w (A.openOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.openOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.openOK) c f stepped valid)
  acquire-preserves w (A.configureOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.configureOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.configureOK) c f stepped valid)
  acquire-preserves w (A.bindOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.bindOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.bindOK) c f stepped valid)
  acquire-preserves w (A.connectOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.connectOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.connectOK) c f stepped valid)
  acquire-preserves w (A.gotLocal local) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.gotLocal local) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.gotLocal local) c f stepped valid)
  acquire-preserves w (A.updateLocalAddress) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.updateLocalAddress) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.updateLocalAddress) c f stepped valid)
  acquire-preserves w (A.forkOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.forkOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.forkOK) c f stepped valid)
  acquire-preserves w (A.commitConnected) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.commitConnected) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.commitConnected) c f stepped valid)
  acquire-preserves w (A.readResult) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.readResult) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.readResult) c f stepped valid)
  acquire-preserves w (A.commitHandshake) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.commitHandshake) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.commitHandshake) c f stepped valid)
  acquire-preserves w (A.failIO err) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.failIO err) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.failIO err) c f stepped valid)
  acquire-preserves w (A.closeFailed err) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.closeFailed err) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.closeFailed err) c f stepped valid)
  acquire-preserves w (A.closeOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.closeOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.closeOK) c f stepped valid)
  acquire-preserves w (A.removeReservation) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.removeReservation) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.removeReservation) c f stepped valid)
  acquire-preserves w (A.waitNegotiated) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.waitNegotiated) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-resources w (A.waitNegotiated) c f stepped valid)



  -- Cancellation delivery and release writes cover every release action.
  release-preserves : ∀ w action c {c′} → advanceRelease w action c ≡ just c′ →
    Valid c → Valid c′
  release-preserves w R.returnResult c eq valid with lookup w (releasing c)
  ... | nothing = case eq of λ ()
  ... | just f with R.pc f
  ...   | R.complete result = subst Valid (just-injective eq) valid
  ...   | R.transaction = case eq of λ ()
  ...   | R.check flag p = case eq of λ ()
  ...   | R.count p = case eq of λ ()
  ...   | R.armTimer e v = case eq of λ ()
  ...   | R.waitIdle e v = case eq of λ ()
  ...   | R.timeoutWrite e v = case eq of λ ()
  ...   | R.cancel v p = case eq of λ ()
  ...   | R.delivering v p = case eq of λ ()
  ...   | R.prune victims result = case eq of λ ()
  release-preserves w (R.transactionStep) c eq valid with lookup w (releasing c) | canDeliver (R.transactionStep) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.transactionStep) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (Release.For.step-retains q captured (I.promotionHardLimit (core c)) (R.transactionStep) f (I.world (core c)) valid stepped)
  release-preserves w (R.transactionPruning scores) c eq valid with lookup w (releasing c) | canDeliver (R.transactionPruning scores) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.transactionPruning scores) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (Release.For.step-retains q captured (I.promotionHardLimit (core c)) (R.transactionPruning scores) f (I.world (core c)) valid stepped)
  release-preserves w (R.checkAssertion) c eq valid with lookup w (releasing c) | canDeliver (R.checkAssertion) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.checkAssertion) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (Release.For.step-retains q captured (I.promotionHardLimit (core c)) (R.checkAssertion) f (I.world (core c)) valid stepped)
  release-preserves w (R.readCounters) c eq valid with lookup w (releasing c) | canDeliver (R.readCounters) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.readCounters) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (Release.For.step-retains q captured (I.promotionHardLimit (core c)) (R.readCounters) f (I.world (core c)) valid stepped)
  release-preserves w (R.registerTimer) c eq valid with lookup w (releasing c) | canDeliver (R.registerTimer) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.registerTimer) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (Release.For.step-retains q captured (I.promotionHardLimit (core c)) (R.registerTimer) f (I.world (core c)) valid stepped)
  release-preserves w (R.expireTimer) c eq valid with lookup w (releasing c) | canDeliver (R.expireTimer) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.expireTimer) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (Release.For.step-retains q captured (I.promotionHardLimit (core c)) (R.expireTimer) f (I.world (core c)) valid stepped)
  release-preserves w (R.selectWakeup) c eq valid with lookup w (releasing c) | canDeliver (R.selectWakeup) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.selectWakeup) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (Release.For.step-retains q captured (I.promotionHardLimit (core c)) (R.selectWakeup) f (I.world (core c)) valid stepped)
  release-preserves w (R.commitTimeout) c eq valid with lookup w (releasing c) | canDeliver (R.commitTimeout) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.commitTimeout) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (Release.For.step-retains q captured (I.promotionHardLimit (core c)) (R.commitTimeout) f (I.world (core c)) valid stepped)
  release-preserves w (R.requestCancellation) c eq valid with lookup w (releasing c) | canDeliver (R.requestCancellation) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.requestCancellation) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (Release.For.step-retains q captured (I.promotionHardLimit (core c)) (R.requestCancellation) f (I.world (core c)) valid stepped)
  release-preserves w (R.cancellationDelivered v) c eq valid with lookup w (releasing c) | canDeliver (R.cancellationDelivered v) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.cancellationDelivered v) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (Release.For.step-retains q captured (I.promotionHardLimit (core c)) (R.cancellationDelivered v) f (I.world (core c)) valid stepped)



  -- Preserve the fixed handler descriptor using the exhaustive inbound effects.
  inbound-facts : ∀ a c {c′} → I.advance a c ≡ just c′ →
    Facts q captured (I.world c) → Facts q captured (I.world c′)
  inbound-facts a c eq valid with Inbound.all-actions (a ∷ [])
  ... | Inbound.more covered rest = state-retained (proj₁ (Inbound.step-effects a covered c eq)) valid

  -- Every outbound action preserves the fixed descriptor and its stored resources.
  advance-preserves : ∀ a c {c′} → advance a c ≡ just c′ → Valid c → Valid c′
  advance-preserves (inbound a) c eq valid with I.advance a (core c) in stepped
  ... | nothing = case eq of λ ()
  ... | just c′ = subst Valid (just-injective eq)
    (inbound-facts a (core c) stepped valid)
  advance-preserves (beginAcquire w req) c eq valid with lookup w (acquiring c) | lookup w (releasing c)
  ... | nothing | nothing = subst Valid (just-injective eq) valid
  ... | just _ | _ = case eq of λ ()
  ... | nothing | just _ = case eq of λ ()
  advance-preserves (acquire w a) c = acquire-preserves w a c
  advance-preserves (beginRelease w key) c eq valid with lookup w (acquiring c) | lookup w (releasing c)
  ... | nothing | nothing = subst Valid (just-injective eq) valid
  ... | just _ | _ = case eq of λ ()
  ... | nothing | just _ = case eq of λ ()
  advance-preserves (release w a) c eq valid = release-preserves w a c eq valid


  -- Induct over an arbitrary finite execution without a scheduling premise.
  exec-preserves : ∀ {c actions c′} → Valid c → Executes c actions c′ → Valid c′
  exec-preserves valid done = valid
  exec-preserves valid (next {c = c} {a = a} eq rest) =
    exec-preserves (advance-preserves a c eq valid) rest

  -- Existing resources remain present from the real outbound initializer.
  from-initial : ∀ {c actions c′} → Facts q captured (I.world c) →
    Executes (initial c) actions c′ → Valid c′
  from-initial valid = exec-preserves valid

-- Public wrappers retain the existing Resources predicate without new premises.
resources-step : ∀ a c {c′ q} → advance a c ≡ just c′ →
  Resources q (I.world (core c)) → Resources q (I.world (core c′))
resources-step a c {q = q} eq resources = to-resources
  (For.advance-preserves q (original resources) a c eq (from-resources resources))
resources-exec : ∀ {c actions c′ q} → Executes c actions c′ →
  Resources q (I.world (core c)) → Resources q (I.world (core c′))
resources-exec {q = q} path resources = to-resources
  (For.exec-preserves q (original resources) (from-resources resources) path)

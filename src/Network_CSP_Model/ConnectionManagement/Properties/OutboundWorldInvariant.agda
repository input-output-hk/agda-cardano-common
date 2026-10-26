{-# OPTIONS --guardedness #-}

-- Lift predicates observing shared stores AND IG handles/muxes through outbound execution.
module ConnectionManagement.Properties.OutboundWorldInvariant where

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
import ConnectionManagement.Properties.HandlerDispatcherInterference as Inbound
import ConnectionManagement.Properties.OutboundAcquireEffects as Acquire
import ConnectionManagement.Properties.OutboundReleaseEffects as Release
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R


import ConnectionManagement.Properties.StateRetention as State
import ConnectionManagement.Properties.IGTableRetention as Table
open import ConnectionManagement.Properties.SharedStateEffects using (to-retains)
open import ConnectionManagement.Properties.HandlerAnchors using (anchors-refl)
import ConnectionManagement.Rules.IGRegistration as IG

-- Stability under retained lookups is supplied by each concrete observer.
module Lift
  (Predicate : S.State → IG.Runtime → Set)
  (stable : ∀ {s s′ ig ig′} → State.Retains s s′ → Table.Retains ig ig′ →
    Predicate s ig → Predicate s′ ig′) where

  -- Observe both shared stores and IG execution tables.
  Valid : Configuration → Set
  Valid c = Predicate (I.world (core c)) (I.inboundGovernor (core c))

  -- Apply the selected acquisition frame proof to the shared world.
  acquisition-preserves : ∀ w action c f {f′ s′} →
    A.step w (I.responder (core c)) action f (I.world (core c)) ≡ just (f′ , s′) →
    Valid c → Predicate s′ (I.inboundGovernor (core c))
  acquisition-preserves w action c f {s′ = s′} stepped valid =
    stable (to-retains {s = I.world (core c)} {s′ = s′}
      (Acquire.step-effects w (I.responder (core c)) action f (I.world (core c)) stepped))
      (Table.from-anchors (anchors-refl (I.inboundGovernor (core c)))) valid

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
    (acquisition-preserves w (A.select chosen) c f stepped valid)
  acquire-preserves w (A.readCounters) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.readCounters) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.readCounters) c f stepped valid)
  acquire-preserves w (A.newPromise) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.newPromise) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.newPromise) c f stepped valid)
  acquire-preserves w (A.openOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.openOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.openOK) c f stepped valid)
  acquire-preserves w (A.configureOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.configureOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.configureOK) c f stepped valid)
  acquire-preserves w (A.bindOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.bindOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.bindOK) c f stepped valid)
  acquire-preserves w (A.connectOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.connectOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.connectOK) c f stepped valid)
  acquire-preserves w (A.gotLocal local) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.gotLocal local) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.gotLocal local) c f stepped valid)
  acquire-preserves w (A.updateLocalAddress) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.updateLocalAddress) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.updateLocalAddress) c f stepped valid)
  acquire-preserves w (A.forkOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.forkOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.forkOK) c f stepped valid)
  acquire-preserves w (A.commitConnected) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.commitConnected) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.commitConnected) c f stepped valid)
  acquire-preserves w (A.readResult) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.readResult) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.readResult) c f stepped valid)
  acquire-preserves w (A.commitHandshake) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.commitHandshake) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.commitHandshake) c f stepped valid)
  acquire-preserves w (A.failIO err) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.failIO err) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.failIO err) c f stepped valid)
  acquire-preserves w (A.closeFailed err) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.closeFailed err) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.closeFailed err) c f stepped valid)
  acquire-preserves w (A.closeOK) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.closeOK) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.closeOK) c f stepped valid)
  acquire-preserves w (A.removeReservation) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.removeReservation) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.removeReservation) c f stepped valid)
  acquire-preserves w (A.waitNegotiated) c eq valid with lookup w (acquiring c) in found
  ... | nothing = case eq of λ ()
  ... | just f with A.step w (I.responder (core c)) (A.waitNegotiated) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (acquisition-preserves w (A.waitNegotiated) c f stepped valid)



  -- Release effects retain immutable shared lookups and mutable resource keys.
  release-state : ∀ action f c {out} → Valid c →
    R.step (I.promotionHardLimit (core c)) action f (I.world (core c)) ≡ just out →
    Predicate (Data.Product.proj₂ out) (I.inboundGovernor (core c))
  release-state action f c {out} valid stepped =
    stable (to-retains {s = I.world (core c)} {s′ = Data.Product.proj₂ out}
      (Release.step-effects (I.promotionHardLimit (core c)) action f (I.world (core c)) stepped))
      (Table.from-anchors (anchors-refl (I.inboundGovernor (core c)))) valid

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
    (release-state (R.transactionStep) f c valid stepped)
  release-preserves w (R.transactionPruning scores) c eq valid with lookup w (releasing c) | canDeliver (R.transactionPruning scores) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.transactionPruning scores) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (release-state (R.transactionPruning scores) f c valid stepped)
  release-preserves w (R.checkAssertion) c eq valid with lookup w (releasing c) | canDeliver (R.checkAssertion) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.checkAssertion) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (release-state (R.checkAssertion) f c valid stepped)
  release-preserves w (R.readCounters) c eq valid with lookup w (releasing c) | canDeliver (R.readCounters) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.readCounters) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (release-state (R.readCounters) f c valid stepped)
  release-preserves w (R.registerTimer) c eq valid with lookup w (releasing c) | canDeliver (R.registerTimer) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.registerTimer) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (release-state (R.registerTimer) f c valid stepped)
  release-preserves w (R.expireTimer) c eq valid with lookup w (releasing c) | canDeliver (R.expireTimer) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.expireTimer) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (release-state (R.expireTimer) f c valid stepped)
  release-preserves w (R.selectWakeup) c eq valid with lookup w (releasing c) | canDeliver (R.selectWakeup) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.selectWakeup) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (release-state (R.selectWakeup) f c valid stepped)
  release-preserves w (R.commitTimeout) c eq valid with lookup w (releasing c) | canDeliver (R.commitTimeout) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.commitTimeout) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (release-state (R.commitTimeout) f c valid stepped)
  release-preserves w (R.requestCancellation) c eq valid with lookup w (releasing c) | canDeliver (R.requestCancellation) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.requestCancellation) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (release-state (R.requestCancellation) f c valid stepped)
  release-preserves w (R.cancellationDelivered v) c eq valid with lookup w (releasing c) | canDeliver (R.cancellationDelivered v) c
  ... | nothing | _ = case eq of λ ()
  ... | just f | false = case eq of λ ()
  ... | just f | true with R.step (I.promotionHardLimit (core c)) (R.cancellationDelivered v) f (I.world (core c)) in stepped
  ...   | nothing = case eq of λ ()
  ...   | just (f′ , s′) = subst Valid (just-injective eq)
    (release-state (R.cancellationDelivered v) f c valid stepped)



  -- Apply exhaustive inbound store/table effects to the supplied observer.
  inbound-facts : ∀ a c {c′} → I.advance a c ≡ just c′ →
    Predicate (I.world c) (I.inboundGovernor c) → Predicate (I.world c′) (I.inboundGovernor c′)
  inbound-facts a c eq valid with Inbound.all-actions (a ∷ [])
  ... | Inbound.more covered rest = stable (proj₁ (Inbound.step-effects a covered c eq)) (Data.Product.proj₂ (Inbound.step-effects a covered c eq)) valid

  -- Exhaust all outbound actions using their checked store/table effects.
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

  -- Any initially certified observer is preserved from the outbound initializer.
  from-initial : ∀ {c actions c′} → Predicate (I.world c) (I.inboundGovernor c) →
    Executes (initial c) actions c′ → Valid c′
  from-initial valid = exec-preserves valid

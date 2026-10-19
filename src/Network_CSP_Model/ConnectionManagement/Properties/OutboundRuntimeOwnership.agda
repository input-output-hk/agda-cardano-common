{-# OPTIONS --guardedness #-}

-- Every outbound dispatcher action preserves exclusive map-lease ownership.
module ConnectionManagement.Properties.OutboundRuntimeOwnership where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
open import ConnectionManagement.OutboundMachine
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Ownership using (Ownership)
import ConnectionManagement.Properties.OwnershipInvariant as Inbound
import ConnectionManagement.Properties.OutboundAcquireOwnership as Acquire
import ConnectionManagement.Properties.OutboundReleaseOwnership as Release
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R

-- Ownership depends on the shared state's lease census, not acquisition frames.
RuntimeValid : A.Runtime → S.State → Set
RuntimeValid rt s = Ownership s

Valid : Configuration → Set
Valid c = RuntimeValid (acquiring c) (I.world (core c))

-- The selected local acquisition step preserves the same exact census.
acquisition-owns : ∀ w action c f {f′ s′} →
  A.step w (I.responder (core c)) action f (I.world (core c)) ≡ just (f′ , s′) →
  Valid c → Ownership s′
acquisition-owns w action c f stepped own =
  Acquire.step-preserves w (I.responder (core c)) action f (I.world (core c)) own stepped

-- Runtime changes on return leave shared ownership unchanged.
acquire-preserves : ∀ w action c {c′} → advanceAcquire w action c ≡ just c′ →
  Valid c → Valid c′
acquire-preserves w A.returnResult c eq own with lookup w (acquiring c)
... | nothing = case eq of λ ()
... | just f with A.pc f
...   | A.complete result = subst Valid (just-injective eq)
  own
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
acquire-preserves w (A.select chosen) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.select chosen) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.select chosen) c f stepped own)
acquire-preserves w (A.readCounters) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.readCounters) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.readCounters) c f stepped own)
acquire-preserves w (A.newPromise) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.newPromise) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.newPromise) c f stepped own)
acquire-preserves w (A.openOK) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.openOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.openOK) c f stepped own)
acquire-preserves w (A.configureOK) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.configureOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.configureOK) c f stepped own)
acquire-preserves w (A.bindOK) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.bindOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.bindOK) c f stepped own)
acquire-preserves w (A.connectOK) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.connectOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.connectOK) c f stepped own)
acquire-preserves w (A.gotLocal local) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.gotLocal local) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.gotLocal local) c f stepped own)
acquire-preserves w (A.updateLocalAddress) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.updateLocalAddress) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.updateLocalAddress) c f stepped own)
acquire-preserves w (A.forkOK) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.forkOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.forkOK) c f stepped own)
acquire-preserves w (A.commitConnected) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.commitConnected) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.commitConnected) c f stepped own)
acquire-preserves w (A.readResult) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.readResult) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.readResult) c f stepped own)
acquire-preserves w (A.commitHandshake) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.commitHandshake) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.commitHandshake) c f stepped own)
acquire-preserves w (A.failIO err) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.failIO err) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.failIO err) c f stepped own)
acquire-preserves w (A.closeFailed err) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.closeFailed err) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.closeFailed err) c f stepped own)
acquire-preserves w (A.closeOK) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.closeOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.closeOK) c f stepped own)
acquire-preserves w (A.removeReservation) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.removeReservation) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.removeReservation) c f stepped own)
acquire-preserves w (A.waitNegotiated) c eq own with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.waitNegotiated) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (acquisition-owns w (A.waitNegotiated) c f stepped own)



-- Release, cancellation and timer actions retain the same lease census.
release-preserves : ∀ w action c {c′} → advanceRelease w action c ≡ just c′ →
  Valid c → Valid c′
release-preserves w R.returnResult c eq own with lookup w (releasing c)
... | nothing = case eq of λ ()
... | just f with R.pc f
...   | R.complete result = subst Valid (just-injective eq) own
...   | R.transaction = case eq of λ ()
...   | R.check flag p = case eq of λ ()
...   | R.count p = case eq of λ ()
...   | R.armTimer e v = case eq of λ ()
...   | R.waitIdle e v = case eq of λ ()
...   | R.timeoutWrite e v = case eq of λ ()
...   | R.cancel v p = case eq of λ ()
...   | R.delivering v p = case eq of λ ()
...   | R.prune victims result = case eq of λ ()
release-preserves w (R.transactionStep) c eq own with lookup w (releasing c) | canDeliver (R.transactionStep) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.transactionStep) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.transactionStep) f (I.world (core c)) own stepped)
release-preserves w (R.transactionPruning scores) c eq own with lookup w (releasing c) | canDeliver (R.transactionPruning scores) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.transactionPruning scores) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.transactionPruning scores) f (I.world (core c)) own stepped)
release-preserves w (R.checkAssertion) c eq own with lookup w (releasing c) | canDeliver (R.checkAssertion) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.checkAssertion) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.checkAssertion) f (I.world (core c)) own stepped)
release-preserves w (R.readCounters) c eq own with lookup w (releasing c) | canDeliver (R.readCounters) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.readCounters) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.readCounters) f (I.world (core c)) own stepped)
release-preserves w (R.registerTimer) c eq own with lookup w (releasing c) | canDeliver (R.registerTimer) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.registerTimer) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.registerTimer) f (I.world (core c)) own stepped)
release-preserves w (R.expireTimer) c eq own with lookup w (releasing c) | canDeliver (R.expireTimer) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.expireTimer) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.expireTimer) f (I.world (core c)) own stepped)
release-preserves w (R.selectWakeup) c eq own with lookup w (releasing c) | canDeliver (R.selectWakeup) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.selectWakeup) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.selectWakeup) f (I.world (core c)) own stepped)
release-preserves w (R.commitTimeout) c eq own with lookup w (releasing c) | canDeliver (R.commitTimeout) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.commitTimeout) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.commitTimeout) f (I.world (core c)) own stepped)
release-preserves w (R.requestCancellation) c eq own with lookup w (releasing c) | canDeliver (R.requestCancellation) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.requestCancellation) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.requestCancellation) f (I.world (core c)) own stepped)
release-preserves w (R.cancellationDelivered v) c eq own with lookup w (releasing c) | canDeliver (R.cancellationDelivered v) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.cancellationDelivered v) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Valid (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.cancellationDelivered v) f (I.world (core c)) own stepped)



-- Existing inbound ownership is reused; outbound begins only change runtimes.
advance-preserves : ∀ a c {c′} → advance a c ≡ just c′ → Valid c → Valid c′
advance-preserves (inbound a) c eq own with I.advance a (core c) in stepped
... | nothing = case eq of λ ()
... | just c′ = subst Valid (just-injective eq)
  (Inbound.advance-preserves a (core c) stepped own)
advance-preserves (beginAcquire w req) c eq own with lookup w (acquiring c) | lookup w (releasing c)
... | nothing | nothing = subst Valid (just-injective eq) own
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
advance-preserves (acquire w a) c = acquire-preserves w a c
advance-preserves (beginRelease w key) c eq own with lookup w (acquiring c) | lookup w (releasing c)
... | nothing | nothing = subst Valid (just-injective eq) own
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
advance-preserves (release w a) c eq own = release-preserves w a c eq own


-- No restriction on caller or action scheduling in finite executions.
exec-preserves : ∀ {c actions c′} → Valid c → Executes c actions c′ → Valid c′
exec-preserves own done = own
exec-preserves own (next {c = c} {a = a} eq rest) =
  exec-preserves (advance-preserves a c eq own) rest

-- The initial shared world must satisfy ownership; runtime premises are absent.
from-initial : ∀ {c actions c′} → Ownership (I.world c) →
  Executes (initial c) actions c′ → Valid c′
from-initial own = exec-preserves own

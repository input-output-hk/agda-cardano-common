{-# OPTIONS --guardedness #-}

-- Combine allocated-capture validity with entry and promise supply bounds.
module ConnectionManagement.Properties.OutboundRuntimeSupply where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
open import ConnectionManagement.OutboundMachine
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Counters using (lookup-all)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.Properties.SupplyInvariant as Inbound
import ConnectionManagement.Properties.OutboundRuntimeCapture as Runtime
import ConnectionManagement.Properties.OutboundCapture as Capture
import ConnectionManagement.Properties.OutboundAcquireSupply as Acquire
import ConnectionManagement.Properties.OutboundReleaseSupply as Release
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R

-- Bounds alone are insufficient for arbitrary injected acquisition frames.
Bounded : Configuration → Set
Bounded c = SupplyBounds (I.world (core c))

-- This predicate is the induction invariant carried into peer jobs/subsystem.
RuntimeValid : A.Runtime → S.State → Set
RuntimeValid rt s = Runtime.RuntimeValid rt s × SupplyBounds s

Valid : Configuration → Set
Valid c = RuntimeValid (acquiring c) (I.world (core c))

-- Retrieve the selected frame's capture certificate from the runtime store.
acquisition-supply : ∀ w action c f {f′ s′} →
  lookup w (acquiring c) ≡ just f →
  A.step w (I.responder (core c)) action f (I.world (core c)) ≡ just (f′ , s′) →
  Runtime.Captures c → Bounded c → SupplyBounds s′
acquisition-supply w action c f found stepped captured bounded =
  Acquire.step-preserves w (I.responder (core c)) action f (I.world (core c))
    (lookup-all (λ f → Capture.Valid f (I.world (core c))) w (acquiring c) captured found)
    bounded stepped

-- Acquisition return changes only runtime stores; all other cases use local bounds.
acquire-preserves : ∀ w action c {c′} → advanceAcquire w action c ≡ just c′ →
  Runtime.Captures c → Bounded c → Bounded c′
acquire-preserves w A.returnResult c eq captured bounded with lookup w (acquiring c)
... | nothing = case eq of λ ()
... | just f with A.pc f
...   | A.complete result = subst Bounded (just-injective eq)
  bounded
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
acquire-preserves w (A.select chosen) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.select chosen) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.select chosen) c f found stepped captured bounded)
acquire-preserves w (A.readCounters) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.readCounters) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.readCounters) c f found stepped captured bounded)
acquire-preserves w (A.newPromise) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.newPromise) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.newPromise) c f found stepped captured bounded)
acquire-preserves w (A.openOK) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.openOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.openOK) c f found stepped captured bounded)
acquire-preserves w (A.configureOK) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.configureOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.configureOK) c f found stepped captured bounded)
acquire-preserves w (A.bindOK) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.bindOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.bindOK) c f found stepped captured bounded)
acquire-preserves w (A.connectOK) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.connectOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.connectOK) c f found stepped captured bounded)
acquire-preserves w (A.gotLocal local) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.gotLocal local) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.gotLocal local) c f found stepped captured bounded)
acquire-preserves w (A.updateLocalAddress) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.updateLocalAddress) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.updateLocalAddress) c f found stepped captured bounded)
acquire-preserves w (A.forkOK) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.forkOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.forkOK) c f found stepped captured bounded)
acquire-preserves w (A.commitConnected) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.commitConnected) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.commitConnected) c f found stepped captured bounded)
acquire-preserves w (A.readResult) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.readResult) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.readResult) c f found stepped captured bounded)
acquire-preserves w (A.commitHandshake) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.commitHandshake) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.commitHandshake) c f found stepped captured bounded)
acquire-preserves w (A.failIO err) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.failIO err) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.failIO err) c f found stepped captured bounded)
acquire-preserves w (A.closeFailed err) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.closeFailed err) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.closeFailed err) c f found stepped captured bounded)
acquire-preserves w (A.closeOK) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.closeOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.closeOK) c f found stepped captured bounded)
acquire-preserves w (A.removeReservation) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.removeReservation) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.removeReservation) c f found stepped captured bounded)
acquire-preserves w (A.waitNegotiated) c eq captured bounded with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.waitNegotiated) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (acquisition-supply w (A.waitNegotiated) c f found stepped captured bounded)


-- Release entry writes always look up their targets; no frame premise is needed.
release-preserves : ∀ w action c {c′} → advanceRelease w action c ≡ just c′ →
  Bounded c → Bounded c′
release-preserves w R.returnResult c eq bounded with lookup w (releasing c)
... | nothing = case eq of λ ()
... | just f with R.pc f
...   | R.complete result = subst Bounded (just-injective eq) bounded
...   | R.transaction = case eq of λ ()
...   | R.check flag p = case eq of λ ()
...   | R.count p = case eq of λ ()
...   | R.armTimer e v = case eq of λ ()
...   | R.waitIdle e v = case eq of λ ()
...   | R.timeoutWrite e v = case eq of λ ()
...   | R.cancel v p = case eq of λ ()
...   | R.delivering v p = case eq of λ ()
...   | R.prune victims result = case eq of λ ()
release-preserves w (R.transactionStep) c eq bounded with lookup w (releasing c) | canDeliver (R.transactionStep) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.transactionStep) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.transactionStep) f (I.world (core c)) bounded stepped)
release-preserves w (R.transactionPruning scores) c eq bounded with lookup w (releasing c) | canDeliver (R.transactionPruning scores) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.transactionPruning scores) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.transactionPruning scores) f (I.world (core c)) bounded stepped)
release-preserves w (R.checkAssertion) c eq bounded with lookup w (releasing c) | canDeliver (R.checkAssertion) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.checkAssertion) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.checkAssertion) f (I.world (core c)) bounded stepped)
release-preserves w (R.readCounters) c eq bounded with lookup w (releasing c) | canDeliver (R.readCounters) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.readCounters) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.readCounters) f (I.world (core c)) bounded stepped)
release-preserves w (R.registerTimer) c eq bounded with lookup w (releasing c) | canDeliver (R.registerTimer) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.registerTimer) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.registerTimer) f (I.world (core c)) bounded stepped)
release-preserves w (R.expireTimer) c eq bounded with lookup w (releasing c) | canDeliver (R.expireTimer) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.expireTimer) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.expireTimer) f (I.world (core c)) bounded stepped)
release-preserves w (R.selectWakeup) c eq bounded with lookup w (releasing c) | canDeliver (R.selectWakeup) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.selectWakeup) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.selectWakeup) f (I.world (core c)) bounded stepped)
release-preserves w (R.commitTimeout) c eq bounded with lookup w (releasing c) | canDeliver (R.commitTimeout) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.commitTimeout) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.commitTimeout) f (I.world (core c)) bounded stepped)
release-preserves w (R.requestCancellation) c eq bounded with lookup w (releasing c) | canDeliver (R.requestCancellation) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.requestCancellation) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.requestCancellation) f (I.world (core c)) bounded stepped)
release-preserves w (R.cancellationDelivered v) c eq bounded with lookup w (releasing c) | canDeliver (R.cancellationDelivered v) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.cancellationDelivered v) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Bounded (just-injective eq)
  (Release.step-preserves (I.promotionHardLimit (core c)) (R.cancellationDelivered v) f (I.world (core c)) bounded stepped)


-- Bounds are preserved when every pending acquisition has a valid capture.
advance-bounds : ∀ a c {c′} → advance a c ≡ just c′ →
  Runtime.Captures c → Bounded c → Bounded c′
advance-bounds (inbound a) c eq captured bounded with I.advance a (core c) in stepped
... | nothing = case eq of λ ()
... | just c′ = subst Bounded (just-injective eq)
  (Inbound.advance-preserves a (core c) stepped bounded)
advance-bounds (beginAcquire w req) c eq captured bounded with lookup w (acquiring c) | lookup w (releasing c)
... | nothing | nothing = subst Bounded (just-injective eq) bounded
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
advance-bounds (acquire w a) c = acquire-preserves w a c
advance-bounds (beginRelease w key) c eq captured bounded with lookup w (acquiring c) | lookup w (releasing c)
... | nothing | nothing = subst Bounded (just-injective eq) bounded
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
advance-bounds (release w a) c eq captured bounded = release-preserves w a c eq bounded

-- Carry the capture certificate alongside bounds so induction is closed.
advance-preserves : ∀ a c {c′} → advance a c ≡ just c′ → Valid c → Valid c′
advance-preserves a c eq (captured , bounded) =
  Runtime.advance-preserves a c eq captured , advance-bounds a c eq captured bounded

-- Arbitrary finite inbound/acquisition/release interleavings preserve both parts.
exec-preserves : ∀ {c actions c′} → Valid c → Executes c actions c′ → Valid c′
exec-preserves valid done = valid
exec-preserves valid (next {c = c} {a = a} eq rest) =
  exec-preserves (advance-preserves a c eq valid) rest

-- Empty pending frames are derived; only the initial world bound is assumed.
from-initial : ∀ {c actions c′} → SupplyBounds (I.world c) →
  Executes (initial c) actions c′ → Valid c′
from-initial {c} bounded = exec-preserves (Runtime.initial-valid c , bounded)

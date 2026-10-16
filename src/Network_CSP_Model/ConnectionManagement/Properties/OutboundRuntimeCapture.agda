{-# OPTIONS --guardedness #-}

-- Every pending acquisition retains its captured entry across arbitrary
-- OutboundMachine interleavings, including the full inbound dispatcher.
module ConnectionManagement.Properties.OutboundRuntimeCapture where

open import Data.Bool using (true; false)
open import Data.List using ([]; _∷_)
open import Data.List.Relation.Unary.All using (All; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (tt)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
open import ConnectionManagement.OutboundMachine
open import ConnectionManagement.Store using (lookup; put; delete)
open import ConnectionManagement.Properties.Entries using (Present)
open import ConnectionManagement.Properties.Stores using (put-values; delete-values)
open import ConnectionManagement.Properties.Counters using (lookup-all)
import ConnectionManagement.Properties.OutboundCapture as Capture
import ConnectionManagement.Properties.OutboundAcquireRetention as Acquire
import ConnectionManagement.Properties.OutboundReleaseRetention as Release
import ConnectionManagement.Properties.HandlerDispatcherInterference as Inbound
import ConnectionManagement.Properties.StateRetention as Retention
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundRelease as R

-- All frames are checked, without a worker-ID uniqueness assumption.
RuntimeValid : A.Runtime → S.State → Set
RuntimeValid rt s = All (λ binding → Capture.Valid (proj₂ binding) s) rt

-- The public invariant refers to all pending acquisition frames.
Captures : Configuration → Set
Captures c = RuntimeValid (acquiring c) (I.world (core c))

-- Every initially empty acquisition runtime is valid.
initial-valid : ∀ c → Captures (initial c)
initial-valid c = []

-- Heap retention transports all existing frames, not just a selected caller.
runtime-retained : ∀ rt s s′ →
  (∀ e → Present e (S.entries (S.cm s)) → Present e (S.entries (S.cm s′))) →
  RuntimeValid rt s → RuntimeValid rt s′
runtime-retained rt s s′ retains = map (λ { {x = w , f} → Capture.retained-valid f s s′ retains })

-- Extract exhaustive inbound coverage from its existing dispatcher theorem.
inbound-covered : ∀ a → Inbound.Covered a
inbound-covered a with Inbound.all-actions (a ∷ [])
... | Inbound.more covered rest = covered

-- Existing inbound steps retain allocated entries despite map removal.
inbound-retained : ∀ a c {c′} → I.advance a c ≡ just c′ →
  ∀ e → Present e (S.entries (S.cm (I.world c))) → Present e (S.entries (S.cm (I.world c′)))
inbound-retained a c eq = Retention.entriesRetained
  (proj₁ (Inbound.step-effects a (inbound-covered a) c eq))

-- Update the active frame using its step proof, transport every other frame.
update-acquisition : ∀ w action c f {f′ s′} →
  lookup w (acquiring c) ≡ just f →
  A.step w (I.responder (core c)) action f (I.world (core c)) ≡ just (f′ , s′) →
  Captures c → RuntimeValid (put w f′ (acquiring c)) s′
update-acquisition w action c f {f′} {s′} found stepped valid =
  put-values (λ f → Capture.Valid f s′) w f′ (acquiring c)
    (Capture.step-valid w (I.responder (core c)) action f (I.world (core c))
      (lookup-all (λ f → Capture.Valid f (I.world (core c))) w (acquiring c) valid found) stepped)
    (runtime-retained (acquiring c) (I.world (core c)) s′
      (λ e present → Acquire.step-retains w (I.responder (core c)) action f (I.world (core c)) e present stepped) valid)

-- Acquiring workers preserve the complete runtime, including on return.
acquire-preserves : ∀ w action c {c′} → advanceAcquire w action c ≡ just c′ → Captures c → Captures c′
acquire-preserves w A.returnResult c eq valid with lookup w (acquiring c)
... | nothing = case eq of λ ()
... | just f with A.pc f
...   | A.complete result = subst Captures (just-injective eq)
  (delete-values (λ f → Capture.Valid f (I.world (core c))) w (acquiring c) valid)
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
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.select chosen) c f found stepped valid)
acquire-preserves w (A.readCounters) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.readCounters) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.readCounters) c f found stepped valid)
acquire-preserves w (A.newPromise) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.newPromise) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.newPromise) c f found stepped valid)
acquire-preserves w (A.openOK) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.openOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.openOK) c f found stepped valid)
acquire-preserves w (A.configureOK) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.configureOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.configureOK) c f found stepped valid)
acquire-preserves w (A.bindOK) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.bindOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.bindOK) c f found stepped valid)
acquire-preserves w (A.connectOK) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.connectOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.connectOK) c f found stepped valid)
acquire-preserves w (A.gotLocal local) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.gotLocal local) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.gotLocal local) c f found stepped valid)
acquire-preserves w (A.updateLocalAddress) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.updateLocalAddress) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.updateLocalAddress) c f found stepped valid)
acquire-preserves w (A.forkOK) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.forkOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.forkOK) c f found stepped valid)
acquire-preserves w (A.commitConnected) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.commitConnected) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.commitConnected) c f found stepped valid)
acquire-preserves w (A.readResult) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.readResult) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.readResult) c f found stepped valid)
acquire-preserves w (A.commitHandshake) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.commitHandshake) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.commitHandshake) c f found stepped valid)
acquire-preserves w (A.failIO err) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.failIO err) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.failIO err) c f found stepped valid)
acquire-preserves w (A.closeFailed err) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.closeFailed err) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.closeFailed err) c f found stepped valid)
acquire-preserves w (A.closeOK) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.closeOK) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.closeOK) c f found stepped valid)
acquire-preserves w (A.removeReservation) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.removeReservation) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.removeReservation) c f found stepped valid)
acquire-preserves w (A.waitNegotiated) c eq valid with lookup w (acquiring c) in found
... | nothing = case eq of λ ()
... | just f with A.step w (I.responder (core c)) (A.waitNegotiated) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (update-acquisition w (A.waitNegotiated) c f found stepped valid)

-- Release workers retain every acquisition capture, including victim entries.
release-preserves : ∀ w action c {c′} → advanceRelease w action c ≡ just c′ → Captures c → Captures c′
release-preserves w R.returnResult c eq valid with lookup w (releasing c)
... | nothing = case eq of λ ()
... | just f with R.pc f
...   | R.complete result = subst Captures (just-injective eq) valid
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
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (runtime-retained (acquiring c) (I.world (core c)) s′
    (λ e present → Release.step-retains (I.promotionHardLimit (core c)) (R.transactionStep) f (I.world (core c)) e present stepped) valid)
release-preserves w (R.transactionPruning scores) c eq valid with lookup w (releasing c) | canDeliver (R.transactionPruning scores) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.transactionPruning scores) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (runtime-retained (acquiring c) (I.world (core c)) s′
    (λ e present → Release.step-retains (I.promotionHardLimit (core c)) (R.transactionPruning scores) f (I.world (core c)) e present stepped) valid)
release-preserves w (R.checkAssertion) c eq valid with lookup w (releasing c) | canDeliver (R.checkAssertion) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.checkAssertion) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (runtime-retained (acquiring c) (I.world (core c)) s′
    (λ e present → Release.step-retains (I.promotionHardLimit (core c)) (R.checkAssertion) f (I.world (core c)) e present stepped) valid)
release-preserves w (R.readCounters) c eq valid with lookup w (releasing c) | canDeliver (R.readCounters) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.readCounters) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (runtime-retained (acquiring c) (I.world (core c)) s′
    (λ e present → Release.step-retains (I.promotionHardLimit (core c)) (R.readCounters) f (I.world (core c)) e present stepped) valid)
release-preserves w (R.registerTimer) c eq valid with lookup w (releasing c) | canDeliver (R.registerTimer) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.registerTimer) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (runtime-retained (acquiring c) (I.world (core c)) s′
    (λ e present → Release.step-retains (I.promotionHardLimit (core c)) (R.registerTimer) f (I.world (core c)) e present stepped) valid)
release-preserves w (R.expireTimer) c eq valid with lookup w (releasing c) | canDeliver (R.expireTimer) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.expireTimer) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (runtime-retained (acquiring c) (I.world (core c)) s′
    (λ e present → Release.step-retains (I.promotionHardLimit (core c)) (R.expireTimer) f (I.world (core c)) e present stepped) valid)
release-preserves w (R.selectWakeup) c eq valid with lookup w (releasing c) | canDeliver (R.selectWakeup) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.selectWakeup) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (runtime-retained (acquiring c) (I.world (core c)) s′
    (λ e present → Release.step-retains (I.promotionHardLimit (core c)) (R.selectWakeup) f (I.world (core c)) e present stepped) valid)
release-preserves w (R.commitTimeout) c eq valid with lookup w (releasing c) | canDeliver (R.commitTimeout) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.commitTimeout) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (runtime-retained (acquiring c) (I.world (core c)) s′
    (λ e present → Release.step-retains (I.promotionHardLimit (core c)) (R.commitTimeout) f (I.world (core c)) e present stepped) valid)
release-preserves w (R.requestCancellation) c eq valid with lookup w (releasing c) | canDeliver (R.requestCancellation) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.requestCancellation) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (runtime-retained (acquiring c) (I.world (core c)) s′
    (λ e present → Release.step-retains (I.promotionHardLimit (core c)) (R.requestCancellation) f (I.world (core c)) e present stepped) valid)
release-preserves w (R.cancellationDelivered v) c eq valid with lookup w (releasing c) | canDeliver (R.cancellationDelivered v) c
... | nothing | _ = case eq of λ ()
... | just f | false = case eq of λ ()
... | just f | true with R.step (I.promotionHardLimit (core c)) (R.cancellationDelivered v) f (I.world (core c)) in stepped
...   | nothing = case eq of λ ()
...   | just (f′ , s′) = subst Captures (just-injective eq)
  (runtime-retained (acquiring c) (I.world (core c)) s′
    (λ e present → Release.step-retains (I.promotionHardLimit (core c)) (R.cancellationDelivered v) f (I.world (core c)) e present stepped) valid)

-- Exhaustive dispatcher preservation imposes no scheduling restriction.
advance-preserves : ∀ a c {c′} → advance a c ≡ just c′ → Captures c → Captures c′
advance-preserves (inbound a) c eq valid with I.advance a (core c) in stepped
... | nothing = case eq of λ ()
... | just c′ = subst Captures (just-injective eq)
  (runtime-retained (acquiring c) (I.world (core c)) (I.world c′) (inbound-retained a (core c) stepped) valid)
advance-preserves (beginAcquire w req) c eq valid with lookup w (acquiring c) | lookup w (releasing c)
... | nothing | nothing = subst Captures (just-injective eq)
  (put-values (λ f → Capture.Valid f (I.world (core c))) w (A.frame req A.selecting) (acquiring c) tt valid)
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
advance-preserves (acquire w a) c = acquire-preserves w a c
advance-preserves (beginRelease w key) c eq valid with lookup w (acquiring c) | lookup w (releasing c)
... | nothing | nothing = subst Captures (just-injective eq) valid
... | just _ | _ = case eq of λ ()
... | nothing | just _ = case eq of λ ()
advance-preserves (release w a) c = release-preserves w a c

-- Every finite interleaving preserves the runtime certificate.
exec-preserves : ∀ {c actions c′} → Captures c → Executes c actions c′ → Captures c′
exec-preserves valid done = valid
exec-preserves valid (next {c = c} {a = a} eq rest) = exec-preserves (advance-preserves a c eq valid) rest

-- Validity follows from the real dispatcher initializer, not injected frames.
from-initial : ∀ {c actions c′} → Executes (initial c) actions c′ → Captures c′
from-initial {c} = exec-preserves (initial-valid c)

open import Data.Nat using (_<_)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)

-- Runtime validity supplies the cleanup bound for whichever caller is chosen.
removal-bound : ∀ w c req e err →
  lookup w (acquiring c) ≡ just (A.frame req (A.removeError e err)) →
  Captures c → SupplyBounds (I.world (core c)) → serial e < S.nextEntry (S.cm (I.world (core c)))
removal-bound w c req e err found valid bounded =
  Capture.remove-capture-bound req e err (I.world (core c))
    (lookup-all (λ f → Capture.Valid f (I.world (core c))) w (acquiring c) valid found) bounded

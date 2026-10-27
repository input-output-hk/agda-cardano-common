{-# OPTIONS --guardedness #-}

-- Detached caller cleanup retains the captured entry needed by its future
-- writer; current map membership is neither required nor reconstructed.
module ConnectionManagement.Properties.CallerCancellationCapture where

open import Data.List.Relation.Unary.All using (map)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym; cong₂)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; delete)
open import ConnectionManagement.Properties.Stores using (delete-values)
open import ConnectionManagement.Properties.Counters using (lookup-all)
open import ConnectionManagement.Properties.Entries using (Present)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)
import ConnectionManagement.State as S
import ConnectionManagement.Machine as I
import ConnectionManagement.OutboundMachine as CM
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.CallerCancellation as Cancel
import ConnectionManagement.Properties.CallerCancellation as Writer
import ConnectionManagement.Properties.OutboundCapture as Capture
import ConnectionManagement.Properties.OutboundRuntimeCapture as Runtime
import ConnectionManagement.Properties.OutboundAcquireRetention as Retention
import ConnectionManagement.Properties.OutboundAcquireSupply as Supply

PCValid : Cancel.PC → S.State → Set
PCValid (Cancel.cleaning active) shared = Capture.Valid active shared
PCValid (Cancel.finished _) shared = ⊤
Valid : Cancel.Frame → S.State → Set
Valid f shared = PCValid (Cancel.pc f) shared

PlanValid : Cancel.Plan → S.State → Set
PlanValid Cancel.abandon shared = ⊤
PlanValid (Cancel.closeCaptured e) shared = Present e (S.entries (S.cm shared))

-- Ordinary counter PCs inherit the capture of their nested continuation.
ordinary-plan-valid : ∀ pc shared {chosen} → Cancel.ordinaryPlan pc ≡ just chosen →
  Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared)) → PlanValid chosen shared
ordinary-plan-valid A.selecting shared eq valid = case just-injective eq of λ { refl → tt }
ordinary-plan-valid (A.allocatePromise e) shared eq valid = case just-injective eq of λ { refl → tt }
ordinary-plan-valid (A.openSocket e pid) shared eq valid = case eq of λ ()
ordinary-plan-valid (A.configureSocket e pid) shared eq valid = case just-injective eq of λ { refl → valid }
ordinary-plan-valid (A.bindSocket e pid) shared eq valid = case just-injective eq of λ { refl → valid }
ordinary-plan-valid (A.connectSocket e pid) shared eq valid = case just-injective eq of λ { refl → valid }
ordinary-plan-valid (A.localAddress e pid) shared eq valid = case just-injective eq of λ { refl → valid }
ordinary-plan-valid (A.updateAddress e pid key) shared eq valid = case just-injective eq of λ { refl → valid }
ordinary-plan-valid (A.forkHandler e pid key) shared eq valid = case just-injective eq of λ { refl → valid }
ordinary-plan-valid (A.connectedCommit e pid key) shared eq valid = case just-injective eq of λ { refl → tt }
ordinary-plan-valid (A.awaitResult e pid key) shared eq valid = case just-injective eq of λ { refl → tt }
ordinary-plan-valid (A.commitResult e key result) shared eq valid = case just-injective eq of λ { refl → tt }
ordinary-plan-valid (A.waitingInbound e key) shared eq valid = case just-injective eq of λ { refl → tt }
ordinary-plan-valid (A.closeError e err) shared eq valid = case eq of λ ()
ordinary-plan-valid (A.removeError e err) shared eq valid = case eq of λ ()
ordinary-plan-valid (A.complete result) shared eq valid = case just-injective eq of λ { refl → tt }
ordinary-plan-valid (A.count next) shared eq valid = ordinary-plan-valid next shared eq valid

plan-valid : ∀ context pc shared {chosen} → Cancel.plan context pc ≡ just chosen →
  Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared)) → PlanValid chosen shared
plan-valid Cancel.ordinary pc shared eq valid = ordinary-plan-valid pc shared eq valid
plan-valid Cancel.protectedCleanup pc shared () valid
plan-valid Cancel.forkedBeforeHandoff A.selecting shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.allocatePromise e) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.openSocket e pid) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.configureSocket e pid) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.bindSocket e pid) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.connectSocket e pid) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.localAddress e pid) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.updateAddress e pid key) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.forkHandler e pid key) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.connectedCommit e pid key) shared eq valid = case just-injective eq of λ { refl → valid }
plan-valid Cancel.forkedBeforeHandoff (A.awaitResult e pid key) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.commitResult e key result) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.waitingInbound e key) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.closeError e err) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.removeError e err) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.complete result) shared () valid
plan-valid Cancel.forkedBeforeHandoff (A.count next) shared () valid
plan-valid Cancel.interruptibleOpen A.selecting shared () valid
plan-valid Cancel.interruptibleOpen (A.allocatePromise e) shared () valid
plan-valid Cancel.interruptibleOpen (A.openSocket e pid) shared eq valid = case just-injective eq of λ { refl → tt }
plan-valid Cancel.interruptibleOpen (A.configureSocket e pid) shared () valid
plan-valid Cancel.interruptibleOpen (A.bindSocket e pid) shared () valid
plan-valid Cancel.interruptibleOpen (A.connectSocket e pid) shared () valid
plan-valid Cancel.interruptibleOpen (A.localAddress e pid) shared () valid
plan-valid Cancel.interruptibleOpen (A.updateAddress e pid key) shared () valid
plan-valid Cancel.interruptibleOpen (A.forkHandler e pid key) shared () valid
plan-valid Cancel.interruptibleOpen (A.connectedCommit e pid key) shared () valid
plan-valid Cancel.interruptibleOpen (A.awaitResult e pid key) shared () valid
plan-valid Cancel.interruptibleOpen (A.commitResult e key result) shared () valid
plan-valid Cancel.interruptibleOpen (A.waitingInbound e key) shared () valid
plan-valid Cancel.interruptibleOpen (A.closeError e err) shared () valid
plan-valid Cancel.interruptibleOpen (A.removeError e err) shared () valid
plan-valid Cancel.interruptibleOpen (A.complete result) shared () valid
plan-valid Cancel.interruptibleOpen (A.count next) shared () valid

begin-valid : ∀ err chosen active shared → PlanValid chosen shared →
  PCValid (Cancel.begin err chosen active) shared
begin-valid err Cancel.abandon active shared valid = tt
begin-valid err (Cancel.closeCaptured e) active shared valid = valid

-- Detach only an actual runtime frame, preserving every remaining caller and
-- transferring the selected capture to the separate cancellation interpreter.
start-valid : ∀ w err context c {f c′} → Cancel.start w err context c ≡ just (f , c′) →
  Runtime.Captures c → Runtime.Captures c′ × Valid f (I.world (CM.core c′))
start-valid w err Cancel.protectedCleanup c () captured
start-valid w err Cancel.ordinary c eq captured with lookup w (CM.acquiring c) in found | lookup w (CM.releasing c)
... | just active | nothing with Cancel.plan Cancel.ordinary (A.pc active) in planned
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl →
  delete-values (λ active → Capture.Valid active (I.world (CM.core c))) w (CM.acquiring c) captured ,
  begin-valid err chosen active (I.world (CM.core c))
    (plan-valid Cancel.ordinary (A.pc active) (I.world (CM.core c)) planned
      (lookup-all (λ active → Capture.Valid active (I.world (CM.core c))) w (CM.acquiring c) captured found)) }
start-valid w err Cancel.ordinary c eq captured | nothing | nothing = case just-injective eq of λ { refl → captured , tt }
start-valid w err Cancel.ordinary c eq captured | nothing | just active = case just-injective eq of λ { refl → captured , tt }
start-valid w err Cancel.ordinary c eq captured | just active | just release = case eq of λ ()
start-valid w err Cancel.forkedBeforeHandoff c eq captured with lookup w (CM.acquiring c) in found | lookup w (CM.releasing c)
... | just active | nothing with Cancel.plan Cancel.forkedBeforeHandoff (A.pc active) in planned
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl →
  delete-values (λ active → Capture.Valid active (I.world (CM.core c))) w (CM.acquiring c) captured ,
  begin-valid err chosen active (I.world (CM.core c))
    (plan-valid Cancel.forkedBeforeHandoff (A.pc active) (I.world (CM.core c)) planned
      (lookup-all (λ active → Capture.Valid active (I.world (CM.core c))) w (CM.acquiring c) captured found)) }
start-valid w err Cancel.forkedBeforeHandoff c eq captured | nothing | nothing = case eq of λ ()
start-valid w err Cancel.forkedBeforeHandoff c eq captured | nothing | just active = case eq of λ ()
start-valid w err Cancel.forkedBeforeHandoff c eq captured | just active | just release = case eq of λ ()
start-valid w err Cancel.interruptibleOpen c eq captured with lookup w (CM.acquiring c) in found | lookup w (CM.releasing c)
... | just active | nothing with Cancel.plan Cancel.interruptibleOpen (A.pc active) in planned
...   | nothing = case eq of λ ()
...   | just chosen = case just-injective eq of λ { refl →
  delete-values (λ active → Capture.Valid active (I.world (CM.core c))) w (CM.acquiring c) captured ,
  begin-valid err chosen active (I.world (CM.core c))
    (plan-valid Cancel.interruptibleOpen (A.pc active) (I.world (CM.core c)) planned
      (lookup-all (λ active → Capture.Valid active (I.world (CM.core c))) w (CM.acquiring c) captured found)) }
start-valid w err Cancel.interruptibleOpen c eq captured | nothing | nothing = case eq of λ ()
start-valid w err Cancel.interruptibleOpen c eq captured | nothing | just active = case eq of λ ()
start-valid w err Cancel.interruptibleOpen c eq captured | just active | just release = case eq of λ ()

-- Interference retains allocated identities even after their map aliases vanish.
retained-valid : ∀ f shared shared′ →
  (∀ e → Present e (S.entries (S.cm shared)) → Present e (S.entries (S.cm shared′))) →
  Valid f shared → Valid f shared′
retained-valid f shared shared′ retains valid with Cancel.pc f
... | Cancel.finished _ = tt
... | Cancel.cleaning active = Capture.retained-valid active shared shared′ retains valid

-- The cancellation interpreter erases completed captures, and otherwise keeps
-- the actual successful acquisition continuation's capture certificate.
after-valid : ∀ action active shared → Capture.Valid active shared →
  PCValid (Cancel.after action active) shared
after-valid Cancel.closeSocket active shared valid with A.pc active in pcEq
... | A.selecting = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.allocatePromise e) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.openSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.configureSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.bindSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.connectSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.localAddress e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.updateAddress e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.forkHandler e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.connectedCommit e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.awaitResult e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.commitResult e key result) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.waitingInbound e key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.closeError e err) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.removeError e err) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.complete result) = tt
... | (A.count next) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
after-valid Cancel.removeReservation active shared valid with A.pc active in pcEq
... | A.selecting = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.allocatePromise e) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.openSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.configureSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.bindSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.connectSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.localAddress e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.updateAddress e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.forkHandler e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.connectedCommit e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.awaitResult e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.commitResult e key result) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.waitingInbound e key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.closeError e err) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.removeError e err) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.complete result) = tt
... | (A.count next) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
after-valid Cancel.readCounters active shared valid with A.pc active in pcEq
... | A.selecting = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.allocatePromise e) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.openSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.configureSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.bindSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.connectSocket e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.localAddress e pid) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.updateAddress e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.forkHandler e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.connectedCommit e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.awaitResult e pid key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.commitResult e key result) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.waitingInbound e key) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.closeError e err) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.removeError e err) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
... | (A.complete result) = tt
... | (A.count next) = subst (λ pc → Capture.Allocated (Capture.capture pc) (S.entries (S.cm shared))) (sym pcEq) valid
after-valid (Cancel.closeFailed err) active shared valid = tt

-- Derive advancement and supply preservation from the exact A.step witness.
step-valid : ∀ action f c {f′ c′} → Cancel.step action f c ≡ just (f′ , c′) →
  Valid f (I.world (CM.core c)) → Valid f′ (I.world (CM.core c′))
step-valid action f c eq valid with Writer.step-writer action f c eq
... | Writer.writer active active′ shared′ before source frameEq machineEq = subst
  (λ out → Valid (proj₁ out) (I.world (CM.core (proj₂ out))))
  (cong₂ _,_ (sym frameEq) (sym machineEq))
  (after-valid action active′ shared′
    (Capture.step-valid (Cancel.caller f) (I.responder (CM.core c)) (Cancel.acquireAction action)
      active (I.world (CM.core c))
      (subst (λ pc → PCValid pc (I.world (CM.core c))) before valid) source))

step-bounds : ∀ action f c {f′ c′} → Cancel.step action f c ≡ just (f′ , c′) →
  Valid f (I.world (CM.core c)) → SupplyBounds (I.world (CM.core c)) → SupplyBounds (I.world (CM.core c′))
step-bounds action f c eq valid bounded with Writer.step-writer action f c eq
... | Writer.writer active active′ shared′ before source frameEq machineEq = subst
  (λ out → SupplyBounds (I.world (CM.core out))) (sym machineEq)
  (Supply.step-preserves (Cancel.caller f) (I.responder (CM.core c)) (Cancel.acquireAction action)
    active (I.world (CM.core c))
    (subst (λ pc → PCValid pc (I.world (CM.core c))) before valid) bounded source)

step-retains : ∀ action f c {f′ c′} → Cancel.step action f c ≡ just (f′ , c′) →
  ∀ e → Present e (S.entries (S.cm (I.world (CM.core c)))) →
    Present e (S.entries (S.cm (I.world (CM.core c′))))
step-retains action f c eq e present with Writer.step-writer action f c eq
... | Writer.writer active active′ shared′ before source frameEq machineEq = subst
  (λ out → Present e (S.entries (S.cm (I.world (CM.core out))))) (sym machineEq)
  (Retention.step-retains (Cancel.caller f) (I.responder (CM.core c)) (Cancel.acquireAction action)
    active (I.world (CM.core c)) e present source)

step-runtime : ∀ action f c {f′ c′} → Cancel.step action f c ≡ just (f′ , c′) →
  Runtime.Captures c → Runtime.Captures c′
step-runtime action f c eq captured with Writer.step-writer action f c eq
... | Writer.writer active active′ shared′ before source frameEq machineEq = subst Runtime.Captures (sym machineEq)
  (Runtime.runtime-retained (CM.acquiring c) (I.world (CM.core c)) shared′
    (λ e present → Retention.step-retains (Cancel.caller f) (I.responder (CM.core c))
      (Cancel.acquireAction action) active (I.world (CM.core c)) e present source) captured)

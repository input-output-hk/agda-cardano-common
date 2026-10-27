{-# OPTIONS --guardedness #-}

-- Reachability from a fresh observation ties every ticket to a real descriptor.
module ConnectionManagement.Properties.OriginMonitorInvariant where

open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥-elim)
open import Data.List using ([]; _∷_)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst; sym)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State using (negotiated)
import ConnectionManagement.Machine as Open
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.HandlerLifecycle as L
open import ConnectionManagement.Rules.OriginMonitor
open import ConnectionManagement.Properties.OriginMonitor
open import ConnectionManagement.Properties.HandlerOrigin using (Origin; origin-step)
open import ConnectionManagement.Properties.HandlerResources using (Resources)
import ConnectionManagement.Properties.HandlerDispatcherInterference as Dispatcher

-- An unallocated phase carries no descriptor; both ticket phases carry Origin.
TicketOrigin : Target → Open.Configuration → Phase → Set
TicketOrigin t c awaitingAllocation = ⊤
TicketOrigin t c (awaitingPublication tk) = Origin (workerId t) (handleId t) (muxId tk) (protocols tk) (flow tk) c
TicketOrigin t c (published tk) = Origin (workerId t) (handleId t) (muxId tk) (protocols tk) (flow tk) c

Invariant : Target → State → Set
Invariant t s = Resources (workerId t) (Open.world (machine s)) × TicketOrigin t (machine s) (phase s)

-- The allocation classifier preserves the exact originating machine action.
allocation-action : ∀ t a mid k ps f → classify t a ≡ allocation mid k ps f →
  a ≡ Open.igStep (IG.installHandle (handleId t) mid k ps f)
allocation-action t (Open.igStep (IG.installHandle hid mid k ps f)) mid′ k′ ps′ f′ eq with hid ≟ handleId t
... | no _ = ⊥-elim (impossible eq)
  where
  impossible : other ≡ allocation mid′ k′ ps′ f′ → Data.Empty.⊥
  impossible ()
... | yes same with eq
...   | refl rewrite same = refl
allocation-action t (Open.admissionStep w x) mid k ps fl ()
allocation-action t (Open.handshakeStep w x) mid k ps fl ()
allocation-action t (Open.cleanupStep w x) mid k ps fl ()
allocation-action t (Open.handlerExit w) mid k ps fl ()
allocation-action t (Open.remoteStep x) mid k ps fl ()
allocation-action t (Open.releaseStep x) mid k ps fl ()
allocation-action t (Open.handlerPublication w r o) mid k ps fl eq with w ≟ workerId t
... | yes _ with eq
...   | ()
allocation-action t (Open.handlerPublication w r o) mid k ps fl eq | no _ with eq
... | ()
allocation-action t (Open.handlerStep w (L.attach err)) mid k ps fl eq with w ≟ workerId t
... | yes _ with eq
...   | ()
allocation-action t (Open.handlerStep w (L.attach err)) mid k ps fl eq | no _ with eq
... | ()
allocation-action t (Open.handlerStep w (L.jobPoolClosed)) mid k ps fl ()
allocation-action t (Open.handlerStep w (L.publishAsyncFailure)) mid k ps fl ()
allocation-action t (Open.handlerStep w (L.finishRethrow)) mid k ps fl ()
allocation-action t (Open.handlerStep w (L.monitorReturned)) mid k ps fl ()
allocation-action t (Open.handlerStep w (L.monitorThrew)) mid k ps fl ()
allocation-action t (Open.handlerStep w (L.finishBuffer)) mid k ps fl ()
allocation-action t (Open.handlerStep w (L.nodeExceptionDelivered)) mid k ps fl ()
allocation-action t (Open.handlerStep w (L.rethrow)) mid k ps fl ()
allocation-action t (Open.handlerStep w (L.choosePolicy p)) mid k ps fl ()
allocation-action t (Open.handlerStep w (L.tracerThrew e)) mid k ps fl ()
allocation-action t (Open.igStep (IG.installOutboundHandle hid mid′ k′ ps′ f′)) mid k ps fl ()
allocation-action t (Open.igStep (IG.captureTime n)) mid k ps fl ()
allocation-action t (Open.igStep (IG.registerInactivity)) mid k ps fl ()
allocation-action t (Open.igStep (IG.selectBatch)) mid k ps fl ()
allocation-action t (Open.igStep (IG.readEvent)) mid k ps fl ()
allocation-action t (Open.igStep (IG.registerIdleTimer)) mid k ps fl ()
allocation-action t (Open.igStep (IG.runResponders)) mid k ps fl ()
allocation-action t (Open.igStep (IG.commitDecision)) mid k ps fl ()
allocation-action t (Open.igStep (IG.requestFailedStop)) mid k ps fl ()
allocation-action t (Open.igStep (IG.finishBatch)) mid k ps fl ()
allocation-action t (Open.igStep (IG.pollStopped)) mid k ps fl ()
allocation-action t (Open.igStep (IG.restart)) mid k ps fl ()
allocation-action t (Open.igStep (IG.deactivateIG)) mid k ps fl ()
allocation-action t (Open.igStep (IG.flushOnExit)) mid k ps fl ()
allocation-action t (Open.igStep (IG.expireTimer tid)) mid k ps fl ()
allocation-action t (Open.igStep (IG.monitorCommand m)) mid k ps fl ()
allocation-action t (Open.igStep (IG.monitorCompletion m)) mid k ps fl ()
allocation-action t (Open.igStep (IG.sampleTracer m)) mid k ps fl ()
allocation-action t (Open.igStep (IG.commitTracer m)) mid k ps fl ()
allocation-action t (Open.igStep (IG.finishStart m)) mid k ps fl ()
allocation-action t (Open.igStep (IG.forkResponder m)) mid k ps fl ()
allocation-action t (Open.igStep (IG.finishStop m)) mid k ps fl ()
allocation-action t (Open.igStep (IG.startOnDemand m n)) mid k ps fl ()
allocation-action t (Open.igStep (IG.publishJobResult m n)) mid k ps fl ()
allocation-action t (Open.igStep (IG.finishProtocol m n r)) mid k ps fl ()

-- Existing certificates survive the underlying action independently of phase.
transport-ticket : ∀ t a c {c′} ph → Open.advance a c ≡ just c′ →
  TicketOrigin t c ph → TicketOrigin t c′ ph
transport-ticket t a c awaitingAllocation eq cert = tt
transport-ticket t a c (awaitingPublication tk) eq cert = origin-step a c eq cert
transport-ticket t a c (published tk) eq cert = origin-step a c eq cert

-- Check success either creates a ticket from an allocation or retains its origin.
checked-ticket : ∀ t event s ph c′ → check t event s ≡ just ph →
  TicketOrigin t c′ (phase s) →
  (∀ mid k ps f → event ≡ allocation mid k ps f →
    Origin (workerId t) (handleId t) mid ps f c′) → TicketOrigin t c′ ph
checked-ticket t (allocation mid k ps f) s ph c′ eq old create
  with allocation-checked t mid k ps f s eq
... | h , found , keySame , before , refl = create mid k ps f refl
checked-ticket t (publication (negotiated hid f) Open.resultWritten) s ph c′ eq old create
  with publication-checked t hid f s eq
... | tk , before , same , flowSame , refl =
  subst (TicketOrigin t c′) before old
checked-ticket t (publication (negotiated _ _) Open.duplicateWrite) s ph c′ () old create
checked-ticket t (publication ConnectionManagement.State.query _) s ph c′ () old create
checked-ticket t (publication (ConnectionManagement.State.handlerError _ _) _) s ph c′ () old create
checked-ticket t attachment (observed c awaitingAllocation) ph c′ () old create
checked-ticket t attachment (observed c (awaitingPublication tk)) ph c′ () old create
checked-ticket t attachment (observed c (published tk)) ph c′ eq old create with just-injective eq
... | refl = old
checked-ticket t unsupportedOutboundAllocation s ph c′ () old create
checked-ticket t other s ph c′ eq old create with just-injective eq
... | refl = old

-- Resources persist through every accepted action, including unrelated workers.
invariant-step : ∀ t a s {s′} → step t a s ≡ just s′ → Invariant t s → Invariant t s′
invariant-step t a s {s′} eq (resources , cert) =
  Dispatcher.all-resources {c = machine s} {as = a ∷ []} (Open.next advanced Open.done) resources ,
  checked-ticket t (classify t a) s (phase s′) (machine s′)
    (step-checks t a s eq) (transport-ticket t a (machine s) (phase s) advanced cert) create
  where
  advanced = step-projects t a s eq
  create : ∀ mid k ps f → classify t a ≡ allocation mid k ps f →
    Origin (workerId t) (handleId t) mid ps f (machine s′)
  create mid k ps f classified with allocation-action t a mid k ps f classified
  ... | refl = accepted-allocation t mid k ps f s resources eq

invariant-exec : ∀ {t s as s′} → Executes t s as s′ → Invariant t s → Invariant t s′
invariant-exec done inv = inv
invariant-exec (next {s = s} {a = a} eq path) inv = invariant-exec path (invariant-step _ a s eq inv)

-- No initial ticket is trusted. Resource evidence is the only initial premise.
reachable-invariant : ∀ {t c as s′} → Executes t (start c) as s′ →
  Resources (workerId t) (Open.world c) → Invariant t s′
reachable-invariant path resources = invariant-exec path (resources , tt)

{-# OPTIONS --guardedness #-}

-- Acquisition preserves entry/promise bounds when its captures are allocated.
module ConnectionManagement.Properties.OutboundAcquireSupply where

open import Data.Bool using (true; false)
open import Data.Nat using (suc; _<_)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.SupplyBounds
open import ConnectionManagement.Properties.Stores using (put-keys)
open import ConnectionManagement.Properties.Freshness using (supply-step)
import ConnectionManagement.Properties.OutboundCapture as Capture
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.InformationChannel as Queue

-- Transport bounds through the actual successful pair-valued result.
result-preserves : ∀ {pair pair′ : A.Frame × State} → just pair ≡ just pair′ →
  SupplyBounds (proj₂ pair) → SupplyBounds (proj₂ pair′)
result-preserves eq = subst (λ pair → SupplyBounds (proj₂ pair)) (just-injective eq)

-- Lookup establishes the bound without a heap-key uniqueness assumption.
bound-found : ∀ e s {old} → lookup e (entries (cm s)) ≡ just old →
  SupplyBounds s → serial e < nextEntry (cm s)
bound-found e s found bounded = lookup-key (λ e → serial e < nextEntry (cm s))
  e (entries (cm s)) (proj₁ bounded) found

-- An already bounded identity can be written even after its map alias is gone.
write-preserves : ∀ e st s → serial e < nextEntry (cm s) →
  SupplyBounds s → SupplyBounds (A.write e st s)
write-preserves e st s bound (heap , promises) =
  put-keys (λ e → serial e < nextEntry (cm s)) e st (entries (cm s)) bound heap , promises

-- Choices may overwrite the selected identity but allocate no fresh one.
choice-preserves : ∀ first e d f s {out} → serial e < nextEntry (cm s) →
  SupplyBounds s → A.applyChoice first e d f s ≡ just out → SupplyBounds (proj₂ out)
choice-preserves first e C.retry f s captured bounded ()
choice-preserves first e (C.waitInbound k) f s captured bounded eq = result-preserves eq bounded
choice-preserves true e (C.refuse err) f s captured bounded eq = result-preserves eq bounded
choice-preserves false e (C.refuse err) f s captured bounded eq = result-preserves eq bounded
choice-preserves first e (C.gone result) f s captured bounded eq = result-preserves eq bounded
choice-preserves true e (C.reuse st result) f s captured bounded eq = result-preserves eq (write-preserves e st s captured bounded)
choice-preserves false e (C.reuse st result) f s captured bounded eq = result-preserves eq (write-preserves e st s captured bounded)


-- Known selection derives its bound from lookup; fresh selection advances supply.
known-preserves : ∀ chosen m f s {out} → SupplyBounds s →
  A.selectKnown chosen m f s ≡ just out → SupplyBounds (proj₂ out)
known-preserves (just e) m f s bounded eq with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just st = choice-preserves true e (C.acquireCase st) f s
  (bound-found e s found bounded) bounded eq
known-preserves nothing m f s bounded eq with A.provenance (A.req f)
... | inbound = result-preserves eq bounded
... | outbound with lookup (ident (nextEntry (cm s))) (entries (cm s))
...   | just _ = case eq of λ ()
...   | nothing = result-preserves eq
  (supply-step (nextEntry (cm s)) reservedOutbound (entries (cm s)) (proj₁ bounded) , proj₂ bounded)

-- Map and policy guards introduce no new bound assumptions.
selection-preserves : ∀ chosen f s {out} → SupplyBounds s →
  A.selectEntry chosen f s ≡ just out → SupplyBounds (proj₂ out)
selection-preserves chosen f s bounded eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with A.validSelection (A.peer (A.req f)) chosen m
...   | false = case eq of λ ()
...   | true = known-preserves chosen m f s bounded eq

-- Successful handshake writes use the identity just looked up.
success-preserves : ∀ mode e k h flow f s {out} → SupplyBounds s →
  A.commitSuccess mode e k h flow f s ≡ just out → SupplyBounds (proj₂ out)
success-preserves mode e k h flow f s bounded eq with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just st with C.successCase k (A.child (A.req f)) h flow st
...   | C.decision replacement notify (C.raised err) = result-preserves eq bounded
...   | C.decision replacement false (C.connected k′ flow′ h′) with replacement
...     | nothing = result-preserves eq bounded
...     | just replacement′ = result-preserves eq (write-preserves e replacement′ s (bound-found e s found bounded) bounded)
success-preserves mode e k h flow f s bounded eq | just st | C.decision replacement false (C.disconnected k′ reason) with replacement
... | nothing = result-preserves eq bounded
... | just replacement′ = result-preserves eq (write-preserves e replacement′ s (bound-found e s found bounded) bounded)
success-preserves noResponderMode e k h flow f s bounded eq | just st | C.decision replacement true result with result | replacement
... | C.connected _ _ _ | nothing = result-preserves eq bounded
... | C.connected _ _ _ | just replacement′ = result-preserves eq (write-preserves e replacement′ s (bound-found e s found bounded) bounded)
... | C.disconnected _ _ | nothing = result-preserves eq bounded
... | C.disconnected _ _ | just replacement′ = result-preserves eq (write-preserves e replacement′ s (bound-found e s found bounded) bounded)
... | C.raised _ | _ = result-preserves eq bounded
success-preserves responderMode e k h flow f s bounded eq | just st | C.decision replacement true result
  with Queue.writeMessage (newConnection (newConnectionInfo outbound k flow h)) (inboundInfo s) in enqueued | result | replacement
... | nothing | C.connected _ _ _ | _ rewrite enqueued = case eq of λ ()
... | nothing | C.disconnected _ _ | _ rewrite enqueued = case eq of λ ()
... | just queue | C.connected _ _ _ | nothing rewrite enqueued = result-preserves eq bounded
... | just queue | C.connected _ _ _ | just replacement′ rewrite enqueued = result-preserves eq (write-preserves e replacement′ s (bound-found e s found bounded) bounded)
... | just queue | C.disconnected _ _ | nothing rewrite enqueued = result-preserves eq bounded
... | just queue | C.disconnected _ _ | just replacement′ rewrite enqueued = result-preserves eq (write-preserves e replacement′ s (bound-found e s found bounded) bounded)
... | _ | C.raised _ | _ = result-preserves eq bounded


-- Error/query writes also have a successful entry lookup.
error-preserves : ∀ e k reason f s {out} → SupplyBounds s →
  A.commitError e k reason f s ≡ just out → SupplyBounds (proj₂ out)
error-preserves e k reason f s bounded eq with lookup e (entries (cm s)) in found | mapCell (cm s)
... | nothing | _ = case eq of λ ()
... | just _ | taken _ = case eq of λ ()
... | just st | full m = result-preserves eq
  (write-preserves e _ s (bound-found e s found bounded) bounded)

-- The capture premise is essential only where cleanup writes without lookup.
step-preserves : ∀ caller mode action f s {out} → Capture.Valid f s → SupplyBounds s →
  A.step caller mode action f s ≡ just out → SupplyBounds (proj₂ out)
step-preserves caller mode (A.select chosen) f s valid bounded eq with A.pc f
... | A.selecting = selection-preserves chosen f s bounded eq
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq with A.pc f | mapCell (cm s)
... | A.count next | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = result-preserves eq bounded
step-preserves caller mode A.readCounters f s valid bounded eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s valid bounded eq | (A.count p) | taken w = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq with A.pc f
... | A.allocatePromise e with lookup (ident (nextPromise s)) (handshakeResults s)
...   | just _ = case eq of λ ()
...   | nothing = result-preserves eq
  (proj₁ bounded , promise-step (nextPromise s) (promises s) (proj₂ bounded))
step-preserves caller mode A.newPromise f s valid bounded eq | A.selecting = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.newPromise f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq with A.pc f | lookup (A.socketRef (A.req f)) (sockets s)
... | A.openSocket e p | nothing = result-preserves eq bounded
step-preserves caller mode A.openOK f s valid bounded eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s valid bounded eq | (A.openSocket e p) | just sock = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq with A.pc f | A.bindLocal (A.req f)
... | A.configureSocket e p | nothing = result-preserves eq bounded
... | A.configureSocket e p | just _ = result-preserves eq bounded
step-preserves caller mode A.configureOK f s valid bounded eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s valid bounded eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq with A.pc f
... | A.bindSocket e p = result-preserves eq bounded
step-preserves caller mode A.bindOK f s valid bounded eq | A.selecting = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.bindOK f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq with A.pc f
... | A.connectSocket e p = result-preserves eq bounded
step-preserves caller mode A.connectOK f s valid bounded eq | A.selecting = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.connectOK f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq with A.pc f
... | A.localAddress e p = result-preserves eq bounded
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | A.selecting = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq with A.pc f | mapCell (cm s)
... | A.updateAddress e p k | full m with A.updateLocal k m
...   | true , m′ = result-preserves eq bounded
...   | false , m′ = result-preserves eq bounded
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s valid bounded eq | (A.updateAddress e p k) | taken w = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq with A.pc f | lookup (A.child (A.req f)) (handlers s)
... | A.forkHandler e p k | nothing = result-preserves eq bounded
step-preserves caller mode A.forkOK f s valid bounded eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s valid bounded eq | (A.forkHandler e p k) | just h = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq with A.pc f
... | A.connectedCommit e p k with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just reservedOutbound = result-preserves eq
  (write-preserves e (unnegotiated outbound k (A.child (A.req f))) s (bound-found e s found bounded) bounded)
...   | just (unnegotiated inbound _ _) = result-preserves eq
  (write-preserves e (unnegotiated outbound k (A.child (A.req f))) s (bound-found e s found bounded) bounded)
...   | just old@(unnegotiated outbound _ _) = result-preserves eq bounded
...   | just old@(outboundUni _ _ _) = result-preserves eq bounded
...   | just old@(outboundDup _ _ _ _) = result-preserves eq bounded
...   | just old@(outboundIdle _ _ _ _) = result-preserves eq bounded
...   | just old@(inboundIdle _ _ _ _) = result-preserves eq bounded
...   | just old@(inboundActive _ _ _ _) = result-preserves eq bounded
...   | just old@(duplexActive _ _ _) = result-preserves eq bounded
...   | just old@(terminating _ _ _) = result-preserves eq bounded
...   | just old@(terminated _) = result-preserves eq bounded
step-preserves caller mode A.commitConnected f s valid bounded eq | A.selecting = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.commitConnected f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq with A.pc f
... | A.awaitResult e p k with lookup p (handshakeResults s)
...   | nothing = case eq of λ ()
...   | just result = result-preserves eq bounded
step-preserves caller mode A.readResult f s valid bounded eq | A.selecting = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.readResult f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq with A.pc f
... | A.commitResult e k (negotiated h flow) = success-preserves mode e k h flow f s bounded eq
... | A.commitResult e k query = error-preserves e k handshakeQuery f s bounded eq
... | A.commitResult e k (handlerError cls err) = error-preserves e k (handshakeError cls err) f s bounded eq
step-preserves caller mode A.commitHandshake f s valid bounded eq | A.selecting = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq with A.pc f
... | A.waitingInbound e k with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just st = choice-preserves false e (C.waitCase k st) f s (bound-found e s found bounded) bounded eq
step-preserves caller mode A.waitNegotiated f s valid bounded eq | A.selecting = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s valid bounded eq with A.pc f
... | A.openSocket e p = result-preserves eq bounded
... | A.configureSocket e p = result-preserves eq bounded
... | A.bindSocket e p = result-preserves eq bounded
... | A.connectSocket e p = result-preserves eq bounded
... | A.localAddress e p = result-preserves eq bounded
... | A.forkHandler e p k = result-preserves eq bounded
step-preserves caller mode (A.failIO err) f s valid bounded eq | A.selecting = case eq of λ ()
step-preserves caller mode (A.failIO err) f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s valid bounded eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s valid bounded eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s valid bounded eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s valid bounded eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s valid bounded eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s valid bounded eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq with A.pc f
... | A.closeError e err = result-preserves eq bounded
step-preserves caller mode A.closeOK f s valid bounded eq | A.selecting = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.closeOK f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq with A.pc f
... | A.closeError e _ = result-preserves eq bounded
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | A.selecting = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s valid bounded eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq with A.pc f | mapCell (cm s)
... | A.removeError e err | full m = result-preserves eq (write-preserves e (terminated nothing) s
  (Capture.remove-capture-bound (A.req f) e err s valid bounded) bounded)
step-preserves caller mode A.removeReservation f s valid bounded eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s valid bounded eq | (A.removeError e err′) | taken w = case eq of λ ()
step-preserves caller mode A.returnResult f s valid bounded ()

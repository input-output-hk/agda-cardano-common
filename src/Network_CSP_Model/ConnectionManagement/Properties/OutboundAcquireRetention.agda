{-# OPTIONS --guardedness #-}

-- Every outbound acquisition step retains previously allocated entry keys.
-- Stored allocation is distinct from map membership and source object lifetime.
module ConnectionManagement.Properties.OutboundAcquireRetention where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (Present; put-preserves-present)
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.InformationChannel as Queue

-- Transport entry evidence through an actual successful pair-valued result.
result-retains : ∀ {pair pair′ : A.Frame × State} q → just pair ≡ just pair′ →
  Present q (entries (cm (proj₂ pair))) → Present q (entries (cm (proj₂ pair′)))
result-retains q eq = subst (λ pair → Present q (entries (cm (proj₂ pair)))) (just-injective eq)

-- Every choice preserves previously allocated entries, including on reuse.
choice-retains : ∀ first e d f s {out} q → Present q (entries (cm s)) →
  A.applyChoice first e d f s ≡ just out → Present q (entries (cm (proj₂ out)))
choice-retains first e C.retry f s q present ()
choice-retains first e (C.waitInbound k) f s q present eq = result-retains q eq present
choice-retains true e (C.refuse err) f s q present eq = result-retains q eq present
choice-retains false e (C.refuse err) f s q present eq = result-retains q eq present
choice-retains first e (C.gone result) f s q present eq = result-retains q eq present
choice-retains true e (C.reuse st result) f s q present eq = result-retains q eq (put-preserves-present e q st (entries (cm s)) present)
choice-retains false e (C.reuse st result) f s q present eq = result-retains q eq (put-preserves-present e q st (entries (cm s)) present)

-- Fresh selection preserves every older entry while allocating the new one.
known-retains : ∀ chosen m f s {out} q → Present q (entries (cm s)) →
  A.selectKnown chosen m f s ≡ just out → Present q (entries (cm (proj₂ out)))
known-retains (just e) m f s q present eq with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just st = choice-retains true e (C.acquireCase st) f s q present eq
known-retains nothing m f s q present eq with A.provenance (A.req f)
... | inbound = result-retains q eq present
... | outbound with lookup (ident (nextEntry (cm s))) (entries (cm s))
...   | just _ = case eq of λ ()
...   | nothing = result-retains q eq
  (put-preserves-present (ident (nextEntry (cm s))) q reservedOutbound (entries (cm s)) present)

-- Selection guards do not change the entry-retention guarantee.
selection-retains : ∀ chosen f s {out} q → Present q (entries (cm s)) →
  A.selectEntry chosen f s ≡ just out → Present q (entries (cm (proj₂ out)))
selection-retains chosen f s q present eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with A.validSelection (A.peer (A.req f)) chosen m
...   | false = case eq of λ ()
...   | true = known-retains chosen m f s q present eq

-- Handshake success may overwrite an entry but retains every allocated key.
success-retains : ∀ mode e k h flow f s {out} q → Present q (entries (cm s)) →
  A.commitSuccess mode e k h flow f s ≡ just out → Present q (entries (cm (proj₂ out)))
success-retains mode e k h flow f s q present eq with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st with C.successCase k (A.child (A.req f)) h flow st
...   | C.decision replacement notify (C.raised err) = result-retains q eq present
...   | C.decision replacement false (C.connected k′ flow′ h′) with replacement
...     | nothing = result-retains q eq present
...     | just replacement′ = result-retains q eq (put-preserves-present e q replacement′ (entries (cm s)) present)
success-retains mode e k h flow f s q present eq | just st | C.decision replacement false (C.disconnected k′ reason) with replacement
... | nothing = result-retains q eq present
... | just replacement′ = result-retains q eq (put-preserves-present e q replacement′ (entries (cm s)) present)
success-retains noResponderMode e k h flow f s q present eq | just st | C.decision replacement true result with result | replacement
... | C.connected _ _ _ | nothing = result-retains q eq present
... | C.connected _ _ _ | just replacement′ = result-retains q eq (put-preserves-present e q replacement′ (entries (cm s)) present)
... | C.disconnected _ _ | nothing = result-retains q eq present
... | C.disconnected _ _ | just replacement′ = result-retains q eq (put-preserves-present e q replacement′ (entries (cm s)) present)
... | C.raised _ | _ = result-retains q eq present
success-retains responderMode e k h flow f s q present eq | just st | C.decision replacement true result
  with Queue.writeMessage (newConnection (newConnectionInfo outbound k flow h)) (inboundInfo s) in enqueued | result | replacement
... | nothing | C.connected _ _ _ | _ rewrite enqueued = case eq of λ ()
... | nothing | C.disconnected _ _ | _ rewrite enqueued = case eq of λ ()
... | just queue | C.connected _ _ _ | nothing rewrite enqueued = result-retains q eq present
... | just queue | C.connected _ _ _ | just replacement′ rewrite enqueued = result-retains q eq (put-preserves-present e q replacement′ (entries (cm s)) present)
... | just queue | C.disconnected _ _ | nothing rewrite enqueued = result-retains q eq present
... | just queue | C.disconnected _ _ | just replacement′ rewrite enqueued = result-retains q eq (put-preserves-present e q replacement′ (entries (cm s)) present)
... | _ | C.raised _ | _ = result-retains q eq present

-- Error/query cleanup removes map aliases without deleting heap entries.
error-retains : ∀ e k reason f s {out} q → Present q (entries (cm s)) →
  A.commitError e k reason f s ≡ just out → Present q (entries (cm (proj₂ out)))
error-retains e k reason f s q present eq with lookup e (entries (cm s)) | mapCell (cm s)
... | nothing | _ = case eq of λ ()
... | just _ | taken _ = case eq of λ ()
... | just st | full m = result-retains q eq (put-preserves-present e q _ (entries (cm s)) present)

-- Every acquisition action retains all previously allocated entries.
step-retains : ∀ caller mode action f s {out} q → Present q (entries (cm s)) →
  A.step caller mode action f s ≡ just out → Present q (entries (cm (proj₂ out)))
step-retains caller mode (A.select chosen) f s q present eq with A.pc f
... | A.selecting = selection-retains chosen f s q present eq
step-retains caller mode (A.select chosen) f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.allocatePromise e) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.openSocket e p) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.configureSocket e p) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.bindSocket e p) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.connectSocket e p) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.localAddress e p) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.forkHandler e p k) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.connectedCommit e p k) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.awaitResult e p k) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.commitResult e k result) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.waitingInbound e k) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.closeError e err′) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode (A.select chosen) f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq with A.pc f | mapCell (cm s)
... | A.count next | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = result-retains q eq present
step-retains caller mode A.readCounters f s q present eq | A.selecting | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.allocatePromise e) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.openSocket e p) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.configureSocket e p) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.bindSocket e p) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.connectSocket e p) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.localAddress e p) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.commitResult e k result) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.closeError e err′) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.removeError e err′) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.complete result) | _ = case eq of λ ()
step-retains caller mode A.readCounters f s q present eq | (A.count p) | taken w = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq with A.pc f
... | A.allocatePromise e with lookup (ident (nextPromise s)) (handshakeResults s)
...   | just _ = case eq of λ ()
...   | nothing = result-retains q eq present
step-retains caller mode A.newPromise f s q present eq | A.selecting = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.openSocket e p) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.configureSocket e p) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.bindSocket e p) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.connectSocket e p) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.localAddress e p) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.forkHandler e p k) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.connectedCommit e p k) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.awaitResult e p k) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.commitResult e k result) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.waitingInbound e k) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.closeError e err′) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode A.newPromise f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode A.openOK f s q present eq with A.pc f | lookup (A.socketRef (A.req f)) (sockets s)
... | A.openSocket e p | nothing = result-retains q eq present
step-retains caller mode A.openOK f s q present eq | A.selecting | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.count p) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.allocatePromise e) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.configureSocket e p) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.bindSocket e p) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.connectSocket e p) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.localAddress e p) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.commitResult e k result) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.closeError e err′) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.removeError e err′) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.complete result) | _ = case eq of λ ()
step-retains caller mode A.openOK f s q present eq | (A.openSocket e p) | just sock = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq with A.pc f | A.bindLocal (A.req f)
... | A.configureSocket e p | nothing = result-retains q eq present
... | A.configureSocket e p | just _ = result-retains q eq present
step-retains caller mode A.configureOK f s q present eq | A.selecting | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.count p) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.allocatePromise e) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.openSocket e p) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.bindSocket e p) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.connectSocket e p) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.localAddress e p) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.commitResult e k result) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.closeError e err′) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.removeError e err′) | _ = case eq of λ ()
step-retains caller mode A.configureOK f s q present eq | (A.complete result) | _ = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq with A.pc f
... | A.bindSocket e p = result-retains q eq present
step-retains caller mode A.bindOK f s q present eq | A.selecting = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.allocatePromise e) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.openSocket e p) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.configureSocket e p) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.connectSocket e p) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.localAddress e p) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.forkHandler e p k) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.connectedCommit e p k) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.awaitResult e p k) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.commitResult e k result) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.waitingInbound e k) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.closeError e err′) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode A.bindOK f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq with A.pc f
... | A.connectSocket e p = result-retains q eq present
step-retains caller mode A.connectOK f s q present eq | A.selecting = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.allocatePromise e) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.openSocket e p) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.configureSocket e p) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.bindSocket e p) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.localAddress e p) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.forkHandler e p k) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.connectedCommit e p k) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.awaitResult e p k) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.commitResult e k result) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.waitingInbound e k) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.closeError e err′) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode A.connectOK f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq with A.pc f
... | A.localAddress e p = result-retains q eq present
step-retains caller mode (A.gotLocal local) f s q present eq | A.selecting = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.allocatePromise e) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.openSocket e p) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.configureSocket e p) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.bindSocket e p) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.connectSocket e p) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.forkHandler e p k) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.connectedCommit e p k) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.awaitResult e p k) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.commitResult e k result) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.waitingInbound e k) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.closeError e err′) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode (A.gotLocal local) f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq with A.pc f | mapCell (cm s)
... | A.updateAddress e p k | full m with A.updateLocal k m
...   | true , m′ = result-retains q eq present
...   | false , m′ = result-retains q eq present
step-retains caller mode A.updateLocalAddress f s q present eq | A.selecting | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.count p) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.allocatePromise e) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.openSocket e p) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.configureSocket e p) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.bindSocket e p) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.connectSocket e p) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.localAddress e p) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.commitResult e k result) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.closeError e err′) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.removeError e err′) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.complete result) | _ = case eq of λ ()
step-retains caller mode A.updateLocalAddress f s q present eq | (A.updateAddress e p k) | taken w = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq with A.pc f | lookup (A.child (A.req f)) (handlers s)
... | A.forkHandler e p k | nothing = result-retains q eq present
step-retains caller mode A.forkOK f s q present eq | A.selecting | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.count p) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.allocatePromise e) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.openSocket e p) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.configureSocket e p) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.bindSocket e p) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.connectSocket e p) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.localAddress e p) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.commitResult e k result) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.closeError e err′) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.removeError e err′) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.complete result) | _ = case eq of λ ()
step-retains caller mode A.forkOK f s q present eq | (A.forkHandler e p k) | just h = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq with A.pc f
... | A.connectedCommit e p k with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just reservedOutbound = result-retains q eq
  (put-preserves-present e q (unnegotiated outbound k (A.child (A.req f))) (entries (cm s)) present)
...   | just (unnegotiated inbound _ _) = result-retains q eq
  (put-preserves-present e q (unnegotiated outbound k (A.child (A.req f))) (entries (cm s)) present)
...   | just old@(unnegotiated outbound _ _) = result-retains q eq present
...   | just old@(outboundUni _ _ _) = result-retains q eq present
...   | just old@(outboundDup _ _ _ _) = result-retains q eq present
...   | just old@(outboundIdle _ _ _ _) = result-retains q eq present
...   | just old@(inboundIdle _ _ _ _) = result-retains q eq present
...   | just old@(inboundActive _ _ _ _) = result-retains q eq present
...   | just old@(duplexActive _ _ _) = result-retains q eq present
...   | just old@(terminating _ _ _) = result-retains q eq present
...   | just old@(terminated _) = result-retains q eq present
step-retains caller mode A.commitConnected f s q present eq | A.selecting = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.allocatePromise e) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.openSocket e p) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.configureSocket e p) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.bindSocket e p) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.connectSocket e p) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.localAddress e p) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.forkHandler e p k) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.awaitResult e p k) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.commitResult e k result) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.waitingInbound e k) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.closeError e err′) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode A.commitConnected f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq with A.pc f
... | A.awaitResult e p k with lookup p (handshakeResults s)
...   | nothing = case eq of λ ()
...   | just result = result-retains q eq present
step-retains caller mode A.readResult f s q present eq | A.selecting = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.allocatePromise e) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.openSocket e p) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.configureSocket e p) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.bindSocket e p) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.connectSocket e p) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.localAddress e p) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.forkHandler e p k) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.connectedCommit e p k) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.commitResult e k result) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.waitingInbound e k) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.closeError e err′) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode A.readResult f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq with A.pc f
... | A.commitResult e k (negotiated h flow) = success-retains mode e k h flow f s q present eq
... | A.commitResult e k query = error-retains e k handshakeQuery f s q present eq
... | A.commitResult e k (handlerError cls err) = error-retains e k (handshakeError cls err) f s q present eq
step-retains caller mode A.commitHandshake f s q present eq | A.selecting = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.allocatePromise e) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.openSocket e p) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.configureSocket e p) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.bindSocket e p) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.connectSocket e p) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.localAddress e p) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.forkHandler e p k) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.connectedCommit e p k) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.awaitResult e p k) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.waitingInbound e k) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.closeError e err′) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode A.commitHandshake f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq with A.pc f
... | A.waitingInbound e k with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just st = choice-retains false e (C.waitCase k st) f s q present eq
step-retains caller mode A.waitNegotiated f s q present eq | A.selecting = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.allocatePromise e) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.openSocket e p) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.configureSocket e p) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.bindSocket e p) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.connectSocket e p) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.localAddress e p) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.forkHandler e p k) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.connectedCommit e p k) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.awaitResult e p k) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.commitResult e k result) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.closeError e err′) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode A.waitNegotiated f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode (A.failIO err) f s q present eq with A.pc f
... | A.openSocket e p = result-retains q eq present
... | A.configureSocket e p = result-retains q eq present
... | A.bindSocket e p = result-retains q eq present
... | A.connectSocket e p = result-retains q eq present
... | A.localAddress e p = result-retains q eq present
... | A.forkHandler e p k = result-retains q eq present
step-retains caller mode (A.failIO err) f s q present eq | A.selecting = case eq of λ ()
step-retains caller mode (A.failIO err) f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode (A.failIO err) f s q present eq | (A.allocatePromise e) = case eq of λ ()
step-retains caller mode (A.failIO err) f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode (A.failIO err) f s q present eq | (A.connectedCommit e p k) = case eq of λ ()
step-retains caller mode (A.failIO err) f s q present eq | (A.awaitResult e p k) = case eq of λ ()
step-retains caller mode (A.failIO err) f s q present eq | (A.commitResult e k result) = case eq of λ ()
step-retains caller mode (A.failIO err) f s q present eq | (A.waitingInbound e k) = case eq of λ ()
step-retains caller mode (A.failIO err) f s q present eq | (A.closeError e err′) = case eq of λ ()
step-retains caller mode (A.failIO err) f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode (A.failIO err) f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq with A.pc f
... | A.closeError e err = result-retains q eq present
step-retains caller mode A.closeOK f s q present eq | A.selecting = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.allocatePromise e) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.openSocket e p) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.configureSocket e p) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.bindSocket e p) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.connectSocket e p) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.localAddress e p) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.forkHandler e p k) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.connectedCommit e p k) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.awaitResult e p k) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.commitResult e k result) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.waitingInbound e k) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode A.closeOK f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq with A.pc f
... | A.closeError e _ = result-retains q eq present
step-retains caller mode (A.closeFailed err) f s q present eq | A.selecting = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.count p) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.allocatePromise e) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.openSocket e p) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.configureSocket e p) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.bindSocket e p) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.connectSocket e p) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.localAddress e p) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.updateAddress e p k) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.forkHandler e p k) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.connectedCommit e p k) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.awaitResult e p k) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.commitResult e k result) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.waitingInbound e k) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.removeError e err′) = case eq of λ ()
step-retains caller mode (A.closeFailed err) f s q present eq | (A.complete result) = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq with A.pc f | mapCell (cm s)
... | A.removeError e err | full m = result-retains q eq (put-preserves-present e q (terminated nothing) (entries (cm s)) present)
step-retains caller mode A.removeReservation f s q present eq | A.selecting | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.count p) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.allocatePromise e) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.openSocket e p) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.configureSocket e p) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.bindSocket e p) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.connectSocket e p) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.localAddress e p) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.commitResult e k result) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.closeError e err′) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.complete result) | _ = case eq of λ ()
step-retains caller mode A.removeReservation f s q present eq | (A.removeError e err′) | taken w = case eq of λ ()
step-retains caller mode A.returnResult f s q present ()

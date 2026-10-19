{-# OPTIONS --guardedness #-}

-- Outbound acquisition preserves current and captured nested-map uniqueness.
module ConnectionManagement.Properties.OutboundAcquireMapUnique where

open import Data.Bool using (true; false)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.StateMapUniqueness
open import ConnectionManagement.Properties.MapUniqueness using (MapUnique; insert-unique; delete-connection-unique)
import ConnectionManagement.Properties.OutboundMapUniqueness as Maps
open import Class.DecEq using (_≟_)
open import Relation.Nullary using (yes; no)
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.InformationChannel as Queue

-- Successful pair results transport the unchanged vership proposition.
result-preserves : ∀ {pair pair′ : A.Frame × State} → just pair ≡ just pair′ →
  Valid (proj₂ pair) → Valid (proj₂ pair′)
result-preserves eq = subst (λ pair → Valid (proj₂ pair)) (just-injective eq)

-- Entry writes leave all map-certificate components intact.
write-preserves : ∀ e st s → Valid s → Valid (A.write e st s)
write-preserves e st s v = v

-- Choices change entry values or the outbound frame, not lease vership.
choice-preserves : ∀ first e d f s {out} → Valid s →
  A.applyChoice first e d f s ≡ just out → Valid (proj₂ out)
choice-preserves first e C.retry f s v ()
choice-preserves first e (C.waitInbound k) f s v eq = result-preserves eq v
choice-preserves true e (C.refuse err) f s v eq = result-preserves eq v
choice-preserves false e (C.refuse err) f s v eq = result-preserves eq v
choice-preserves first e (C.gone result) f s v eq = result-preserves eq v
choice-preserves true e (C.reuse st result) f s v eq = result-preserves eq (write-preserves e st s v)
choice-preserves false e (C.reuse st result) f s v eq = result-preserves eq (write-preserves e st s v)



-- Fresh selection publishes a full map only when the current cell is full.
known-preserves : ∀ chosen m f s {out} → mapCell (cm s) ≡ full m → Valid s →
  A.selectKnown chosen m f s ≡ just out → Valid (proj₂ out)
known-preserves (just e) m f s cell v eq with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st = choice-preserves true e (C.acquireCase st) f s v eq
known-preserves nothing m f s cell v eq with A.provenance (A.req f)
... | inbound = result-preserves eq v
... | outbound with lookup (ident (nextEntry (cm s))) (entries (cm s))
...   | just _ = case eq of λ ()
...   | nothing = result-preserves eq
  (insert-unique (A.peer (A.req f)) unknownLocal (ident (nextEntry (cm s))) m
    (subst CellUnique cell (proj₁ v)) , proj₂ v)

-- Selection never takes a map lease on behalf of an outbound caller.
selection-preserves : ∀ chosen f s {out} → Valid s →
  A.selectEntry chosen f s ≡ just out → Valid (proj₂ out)
selection-preserves chosen f s v eq with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with A.validSelection (A.peer (A.req f)) chosen m
...   | false = case eq of λ ()
...   | true = known-preserves chosen m f s cell
  (restore-current s (full m) cell v) eq

-- Successful handshake only changes entry values and the IG information queue.
success-preserves : ∀ mode e k h flow f s {out} → Valid s →
  A.commitSuccess mode e k h flow f s ≡ just out → Valid (proj₂ out)
success-preserves mode e k h flow f s v eq with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just st with C.successCase k (A.child (A.req f)) h flow st
...   | C.decision replacement notify (C.raised err) = result-preserves eq v
...   | C.decision replacement false (C.connected k′ flow′ h′) with replacement
...     | nothing = result-preserves eq v
...     | just replacement′ = result-preserves eq (write-preserves e replacement′ s v)
success-preserves mode e k h flow f s v eq | just st | C.decision replacement false (C.disconnected k′ reason) with replacement
... | nothing = result-preserves eq v
... | just replacement′ = result-preserves eq (write-preserves e replacement′ s v)
success-preserves noResponderMode e k h flow f s v eq | just st | C.decision replacement true result with result | replacement
... | C.connected _ _ _ | nothing = result-preserves eq v
... | C.connected _ _ _ | just replacement′ = result-preserves eq (write-preserves e replacement′ s v)
... | C.disconnected _ _ | nothing = result-preserves eq v
... | C.disconnected _ _ | just replacement′ = result-preserves eq (write-preserves e replacement′ s v)
... | C.raised _ | _ = result-preserves eq v
success-preserves responderMode e k h flow f s v eq | just st | C.decision replacement true result
  with Queue.writeMessage (newConnection (newConnectionInfo outbound k flow h)) (inboundInfo s) in enqueued | result | replacement
... | nothing | C.connected _ _ _ | _ rewrite enqueued = case eq of λ ()
... | nothing | C.disconnected _ _ | _ rewrite enqueued = case eq of λ ()
... | just queue | C.connected _ _ _ | nothing rewrite enqueued = result-preserves eq v
... | just queue | C.connected _ _ _ | just replacement′ rewrite enqueued = result-preserves eq (write-preserves e replacement′ s v)
... | just queue | C.disconnected _ _ | nothing rewrite enqueued = result-preserves eq v
... | just queue | C.disconnected _ _ | just replacement′ rewrite enqueued = result-preserves eq (write-preserves e replacement′ s v)
... | _ | C.raised _ | _ = result-preserves eq v



-- Error/query cleanup deletes only an identity-matching binding.
error-preserves : ∀ e k reason f s {out} → Valid s →
  A.commitError e k reason f s ≡ just out → Valid (proj₂ out)
error-preserves e k reason f s v eq with lookup e (entries (cm s)) | mapCell (cm s) in cell
... | nothing | _ = case eq of λ ()
... | just _ | taken _ = case eq of λ ()
... | just st | full m with lookupConnection k m
...   | nothing = result-preserves eq v
...   | just current with current ≟ e
...     | no _ = result-preserves eq v
...     | yes _ = result-preserves eq (delete-connection-unique k m (proj₁ v) , proj₂ v)

-- All successful acquisition actions preserve vership without capture premises.
step-preserves : ∀ caller mode action f s {out} → Valid s →
  A.step caller mode action f s ≡ just out → Valid (proj₂ out)
step-preserves caller mode (A.select chosen) f s v eq with A.pc f
... | A.selecting = selection-preserves chosen f s v eq
step-preserves caller mode (A.select chosen) f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq with A.pc f | mapCell (cm s) in cell
... | A.count next | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = result-preserves eq
  (restore-current s (full m) cell v)
step-preserves caller mode A.readCounters f s v eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s v eq | (A.count p) | taken w = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq with A.pc f
... | A.allocatePromise e with lookup (ident (nextPromise s)) (handshakeResults s)
...   | just _ = case eq of λ ()
...   | nothing = result-preserves eq
  v
step-preserves caller mode A.newPromise f s v eq | A.selecting = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.newPromise f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.openOK f s v eq with A.pc f | lookup (A.socketRef (A.req f)) (sockets s)
... | A.openSocket e p | nothing = result-preserves eq v
step-preserves caller mode A.openOK f s v eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s v eq | (A.openSocket e p) | just sock = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq with A.pc f | A.bindLocal (A.req f)
... | A.configureSocket e p | nothing = result-preserves eq v
... | A.configureSocket e p | just _ = result-preserves eq v
step-preserves caller mode A.configureOK f s v eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s v eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq with A.pc f
... | A.bindSocket e p = result-preserves eq v
step-preserves caller mode A.bindOK f s v eq | A.selecting = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.bindOK f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq with A.pc f
... | A.connectSocket e p = result-preserves eq v
step-preserves caller mode A.connectOK f s v eq | A.selecting = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.connectOK f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq with A.pc f
... | A.localAddress e p = result-preserves eq v
step-preserves caller mode (A.gotLocal local) f s v eq | A.selecting = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq with A.pc f | mapCell (cm s) in cell
... | A.updateAddress e p k | full m with A.updateLocal k m | Maps.update-local-unique k m (proj₁ v)
...   | true , m′ | unique = result-preserves eq (unique , proj₂ v)
...   | false , m′ | unique = result-preserves eq (unique , proj₂ v)
step-preserves caller mode A.updateLocalAddress f s v eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s v eq | (A.updateAddress e p k) | taken w = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq with A.pc f | lookup (A.child (A.req f)) (handlers s)
... | A.forkHandler e p k | nothing = result-preserves eq v
step-preserves caller mode A.forkOK f s v eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s v eq | (A.forkHandler e p k) | just h = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq with A.pc f
... | A.connectedCommit e p k with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just reservedOutbound = result-preserves eq
  (write-preserves e (unnegotiated outbound k (A.child (A.req f))) s v)
...   | just (unnegotiated inbound _ _) = result-preserves eq
  (write-preserves e (unnegotiated outbound k (A.child (A.req f))) s v)
...   | just old@(unnegotiated outbound _ _) = result-preserves eq v
...   | just old@(outboundUni _ _ _) = result-preserves eq v
...   | just old@(outboundDup _ _ _ _) = result-preserves eq v
...   | just old@(outboundIdle _ _ _ _) = result-preserves eq v
...   | just old@(inboundIdle _ _ _ _) = result-preserves eq v
...   | just old@(inboundActive _ _ _ _) = result-preserves eq v
...   | just old@(duplexActive _ _ _) = result-preserves eq v
...   | just old@(terminating _ _ _) = result-preserves eq v
...   | just old@(terminated _) = result-preserves eq v
step-preserves caller mode A.commitConnected f s v eq | A.selecting = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.commitConnected f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq with A.pc f
... | A.awaitResult e p k with lookup p (handshakeResults s)
...   | nothing = case eq of λ ()
...   | just result = result-preserves eq v
step-preserves caller mode A.readResult f s v eq | A.selecting = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.readResult f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq with A.pc f
... | A.commitResult e k (negotiated h flow) = success-preserves mode e k h flow f s v eq
... | A.commitResult e k query = error-preserves e k handshakeQuery f s v eq
... | A.commitResult e k (handlerError cls err) = error-preserves e k (handshakeError cls err) f s v eq
step-preserves caller mode A.commitHandshake f s v eq | A.selecting = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq with A.pc f
... | A.waitingInbound e k with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just st = choice-preserves false e (C.waitCase k st) f s v eq
step-preserves caller mode A.waitNegotiated f s v eq | A.selecting = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s v eq with A.pc f
... | A.openSocket e p = result-preserves eq v
... | A.configureSocket e p = result-preserves eq v
... | A.bindSocket e p = result-preserves eq v
... | A.connectSocket e p = result-preserves eq v
... | A.localAddress e p = result-preserves eq v
... | A.forkHandler e p k = result-preserves eq v
step-preserves caller mode (A.failIO err) f s v eq | A.selecting = case eq of λ ()
step-preserves caller mode (A.failIO err) f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s v eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s v eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s v eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s v eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s v eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s v eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq with A.pc f
... | A.closeError e err = result-preserves eq v
step-preserves caller mode A.closeOK f s v eq | A.selecting = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.closeOK f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq with A.pc f
... | A.closeError e _ = result-preserves eq v
step-preserves caller mode (A.closeFailed err) f s v eq | A.selecting = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s v eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq with A.pc f | mapCell (cm s) in cell
... | A.removeError e err | full m = result-preserves eq
  (Maps.remove-aliases-unique (A.peer (A.req f)) e m (proj₁ v) , proj₂ v)
step-preserves caller mode A.removeReservation f s v eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s v eq | (A.removeError e err′) | taken w = case eq of λ ()
step-preserves caller mode A.returnResult f s v ()

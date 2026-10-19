{-# OPTIONS --guardedness #-}

-- Outbound acquisition preserves the exact existing map-lease census.
module ConnectionManagement.Properties.OutboundAcquireOwnership where

open import Data.Bool using (true; false)
open import Data.List using ([])
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst; sym)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Ownership using (Ownership; Owns; claims)
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.InformationChannel as Queue

-- Successful pair results transport the unchanged ownership proposition.
result-preserves : ∀ {pair pair′ : A.Frame × State} → just pair ≡ just pair′ →
  Ownership (proj₂ pair) → Ownership (proj₂ pair′)
result-preserves eq = subst (λ pair → Ownership (proj₂ pair)) (just-injective eq)

-- The invariant for a full map is precisely the absence of lease claimants.
full-claims : ∀ s m → mapCell (cm s) ≡ full m → Ownership s → claims s ≡ []
full-claims s m cell = subst (λ cell → Owns cell (claims s)) cell

-- Entry writes do not alter the map cell, admissions, or cleanup continuations.
write-preserves : ∀ e st s → Ownership s → Ownership (A.write e st s)
write-preserves e st s own = own

-- Choices change entry values or the outbound frame, not lease ownership.
choice-preserves : ∀ first e d f s {out} → Ownership s →
  A.applyChoice first e d f s ≡ just out → Ownership (proj₂ out)
choice-preserves first e C.retry f s own ()
choice-preserves first e (C.waitInbound k) f s own eq = result-preserves eq own
choice-preserves true e (C.refuse err) f s own eq = result-preserves eq own
choice-preserves false e (C.refuse err) f s own eq = result-preserves eq own
choice-preserves first e (C.gone result) f s own eq = result-preserves eq own
choice-preserves true e (C.reuse st result) f s own eq = result-preserves eq (write-preserves e st s own)
choice-preserves false e (C.reuse st result) f s own eq = result-preserves eq (write-preserves e st s own)



-- Fresh selection publishes a full map only when the current cell is full.
known-preserves : ∀ chosen m f s {out} → mapCell (cm s) ≡ full m → Ownership s →
  A.selectKnown chosen m f s ≡ just out → Ownership (proj₂ out)
known-preserves (just e) m f s cell own eq with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st = choice-preserves true e (C.acquireCase st) f s own eq
known-preserves nothing m f s cell own eq with A.provenance (A.req f)
... | inbound = result-preserves eq own
... | outbound with lookup (ident (nextEntry (cm s))) (entries (cm s))
...   | just _ = case eq of λ ()
...   | nothing = result-preserves eq (full-claims s m cell own)

-- Selection never takes a map lease on behalf of an outbound caller.
selection-preserves : ∀ chosen f s {out} → Ownership s →
  A.selectEntry chosen f s ≡ just out → Ownership (proj₂ out)
selection-preserves chosen f s own eq with mapCell (cm s) in cell
... | taken _ = case eq of λ ()
... | full m with A.validSelection (A.peer (A.req f)) chosen m
...   | false = case eq of λ ()
...   | true = known-preserves chosen m f s cell
  (subst (λ cell → Owns cell (claims s)) (sym cell) own) eq

-- Successful handshake only changes entry values and the IG information queue.
success-preserves : ∀ mode e k h flow f s {out} → Ownership s →
  A.commitSuccess mode e k h flow f s ≡ just out → Ownership (proj₂ out)
success-preserves mode e k h flow f s own eq with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just st with C.successCase k (A.child (A.req f)) h flow st
...   | C.decision replacement notify (C.raised err) = result-preserves eq own
...   | C.decision replacement false (C.connected k′ flow′ h′) with replacement
...     | nothing = result-preserves eq own
...     | just replacement′ = result-preserves eq (write-preserves e replacement′ s own)
success-preserves mode e k h flow f s own eq | just st | C.decision replacement false (C.disconnected k′ reason) with replacement
... | nothing = result-preserves eq own
... | just replacement′ = result-preserves eq (write-preserves e replacement′ s own)
success-preserves noResponderMode e k h flow f s own eq | just st | C.decision replacement true result with result | replacement
... | C.connected _ _ _ | nothing = result-preserves eq own
... | C.connected _ _ _ | just replacement′ = result-preserves eq (write-preserves e replacement′ s own)
... | C.disconnected _ _ | nothing = result-preserves eq own
... | C.disconnected _ _ | just replacement′ = result-preserves eq (write-preserves e replacement′ s own)
... | C.raised _ | _ = result-preserves eq own
success-preserves responderMode e k h flow f s own eq | just st | C.decision replacement true result
  with Queue.writeMessage (newConnection (newConnectionInfo outbound k flow h)) (inboundInfo s) in enqueued | result | replacement
... | nothing | C.connected _ _ _ | _ rewrite enqueued = case eq of λ ()
... | nothing | C.disconnected _ _ | _ rewrite enqueued = case eq of λ ()
... | just queue | C.connected _ _ _ | nothing rewrite enqueued = result-preserves eq own
... | just queue | C.connected _ _ _ | just replacement′ rewrite enqueued = result-preserves eq (write-preserves e replacement′ s own)
... | just queue | C.disconnected _ _ | nothing rewrite enqueued = result-preserves eq own
... | just queue | C.disconnected _ _ | just replacement′ rewrite enqueued = result-preserves eq (write-preserves e replacement′ s own)
... | _ | C.raised _ | _ = result-preserves eq own



-- Error/query alias deletion preserves a full map and the same empty census.
error-preserves : ∀ e k reason f s {out} → Ownership s →
  A.commitError e k reason f s ≡ just out → Ownership (proj₂ out)
error-preserves e k reason f s own eq with lookup e (entries (cm s)) | mapCell (cm s) in cell
... | nothing | _ = case eq of λ ()
... | just _ | taken _ = case eq of λ ()
... | just st | full m = result-preserves eq own

-- All successful acquisition actions preserve ownership without capture premises.
step-preserves : ∀ caller mode action f s {out} → Ownership s →
  A.step caller mode action f s ≡ just out → Ownership (proj₂ out)
step-preserves caller mode (A.select chosen) f s own eq with A.pc f
... | A.selecting = selection-preserves chosen f s own eq
step-preserves caller mode (A.select chosen) f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.select chosen) f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq with A.pc f | mapCell (cm s) in cell
... | A.count next | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = result-preserves eq
  (subst (λ cell → Owns cell (claims s)) (sym cell) own)
step-preserves caller mode A.readCounters f s own eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.readCounters f s own eq | (A.count p) | taken w = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq with A.pc f
... | A.allocatePromise e with lookup (ident (nextPromise s)) (handshakeResults s)
...   | just _ = case eq of λ ()
...   | nothing = result-preserves eq
  own
step-preserves caller mode A.newPromise f s own eq | A.selecting = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.newPromise f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.openOK f s own eq with A.pc f | lookup (A.socketRef (A.req f)) (sockets s)
... | A.openSocket e p | nothing = result-preserves eq own
step-preserves caller mode A.openOK f s own eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.openOK f s own eq | (A.openSocket e p) | just sock = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq with A.pc f | A.bindLocal (A.req f)
... | A.configureSocket e p | nothing = result-preserves eq own
... | A.configureSocket e p | just _ = result-preserves eq own
step-preserves caller mode A.configureOK f s own eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.configureOK f s own eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq with A.pc f
... | A.bindSocket e p = result-preserves eq own
step-preserves caller mode A.bindOK f s own eq | A.selecting = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.bindOK f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq with A.pc f
... | A.connectSocket e p = result-preserves eq own
step-preserves caller mode A.connectOK f s own eq | A.selecting = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.connectOK f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq with A.pc f
... | A.localAddress e p = result-preserves eq own
step-preserves caller mode (A.gotLocal local) f s own eq | A.selecting = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.gotLocal local) f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq with A.pc f | mapCell (cm s) in cell
... | A.updateAddress e p k | full m with A.updateLocal k m
...   | true , m′ = result-preserves eq own
...   | false , m′ = result-preserves eq own
step-preserves caller mode A.updateLocalAddress f s own eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.updateLocalAddress f s own eq | (A.updateAddress e p k) | taken w = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq with A.pc f | lookup (A.child (A.req f)) (handlers s)
... | A.forkHandler e p k | nothing = result-preserves eq own
step-preserves caller mode A.forkOK f s own eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.removeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.forkOK f s own eq | (A.forkHandler e p k) | just h = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq with A.pc f
... | A.connectedCommit e p k with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just reservedOutbound = result-preserves eq
  (write-preserves e (unnegotiated outbound k (A.child (A.req f))) s own)
...   | just (unnegotiated inbound _ _) = result-preserves eq
  (write-preserves e (unnegotiated outbound k (A.child (A.req f))) s own)
...   | just old@(unnegotiated outbound _ _) = result-preserves eq own
...   | just old@(outboundUni _ _ _) = result-preserves eq own
...   | just old@(outboundDup _ _ _ _) = result-preserves eq own
...   | just old@(outboundIdle _ _ _ _) = result-preserves eq own
...   | just old@(inboundIdle _ _ _ _) = result-preserves eq own
...   | just old@(inboundActive _ _ _ _) = result-preserves eq own
...   | just old@(duplexActive _ _ _) = result-preserves eq own
...   | just old@(terminating _ _ _) = result-preserves eq own
...   | just old@(terminated _) = result-preserves eq own
step-preserves caller mode A.commitConnected f s own eq | A.selecting = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.commitConnected f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq with A.pc f
... | A.awaitResult e p k with lookup p (handshakeResults s)
...   | nothing = case eq of λ ()
...   | just result = result-preserves eq own
step-preserves caller mode A.readResult f s own eq | A.selecting = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.readResult f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq with A.pc f
... | A.commitResult e k (negotiated h flow) = success-preserves mode e k h flow f s own eq
... | A.commitResult e k query = error-preserves e k handshakeQuery f s own eq
... | A.commitResult e k (handlerError cls err) = error-preserves e k (handshakeError cls err) f s own eq
step-preserves caller mode A.commitHandshake f s own eq | A.selecting = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.commitHandshake f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq with A.pc f
... | A.waitingInbound e k with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just st = choice-preserves false e (C.waitCase k st) f s own eq
step-preserves caller mode A.waitNegotiated f s own eq | A.selecting = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.waitNegotiated f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s own eq with A.pc f
... | A.openSocket e p = result-preserves eq own
... | A.configureSocket e p = result-preserves eq own
... | A.bindSocket e p = result-preserves eq own
... | A.connectSocket e p = result-preserves eq own
... | A.localAddress e p = result-preserves eq own
... | A.forkHandler e p k = result-preserves eq own
step-preserves caller mode (A.failIO err) f s own eq | A.selecting = case eq of λ ()
step-preserves caller mode (A.failIO err) f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s own eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s own eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s own eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s own eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s own eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s own eq | (A.closeError e err′) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.failIO err) f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq with A.pc f
... | A.closeError e err = result-preserves eq own
step-preserves caller mode A.closeOK f s own eq | A.selecting = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode A.closeOK f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq with A.pc f
... | A.closeError e _ = result-preserves eq own
step-preserves caller mode (A.closeFailed err) f s own eq | A.selecting = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.count p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.allocatePromise e) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.openSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.configureSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.bindSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.connectSocket e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.localAddress e p) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.updateAddress e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.forkHandler e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.connectedCommit e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.awaitResult e p k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.commitResult e k result) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.waitingInbound e k) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.removeError e err′) = case eq of λ ()
step-preserves caller mode (A.closeFailed err) f s own eq | (A.complete result) = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq with A.pc f | mapCell (cm s) in cell
... | A.removeError e err | full m = result-preserves eq own
step-preserves caller mode A.removeReservation f s own eq | A.selecting | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.count p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.allocatePromise e) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.openSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.configureSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.bindSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.connectSocket e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.localAddress e p) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.commitResult e k result) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.closeError e err′) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.complete result) | _ = case eq of λ ()
step-preserves caller mode A.removeReservation f s own eq | (A.removeError e err′) | taken w = case eq of λ ()
step-preserves caller mode A.returnResult f s own ()

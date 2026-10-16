{-# OPTIONS --guardedness #-}

-- Entry captures are independent of current map membership. Completed frames
-- retain results but no mutable-entry reference needed by another write.
module ConnectionManagement.Properties.OutboundCapture where

open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
open import ConnectionManagement.Properties.Entries using (Present; lookup-put)
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.InformationChannel as Queue

-- Exhaustive PC projection: counter continuations retain the nested capture.
capture : A.PC → Maybe EntryId
capture A.selecting = nothing
capture (A.count p) = capture p
capture (A.allocatePromise e) = just e
capture (A.openSocket e _) = just e
capture (A.configureSocket e _) = just e
capture (A.bindSocket e _) = just e
capture (A.connectSocket e _) = just e
capture (A.localAddress e _) = just e
capture (A.updateAddress e _ _) = just e
capture (A.forkHandler e _ _) = just e
capture (A.connectedCommit e _ _) = just e
capture (A.awaitResult e _ _) = just e
capture (A.commitResult e _ _) = just e
capture (A.waitingInbound e _) = just e
capture (A.closeError e _) = just e
capture (A.removeError e _) = just e
capture (A.complete _) = nothing

-- Capture validity requires allocation, not a current connection-map alias.
Allocated : Maybe EntryId → EntryHeap → Set
Allocated nothing heap = ⊤
Allocated (just e) heap = Present e heap

-- A frame's only mutable-entry reference must remain in the add-only heap.
Valid : A.Frame → State → Set
Valid f s = Allocated (capture (A.pc f)) (entries (cm s))

-- Transport a certificate through the actual successful rule result.
result-valid : ∀ {pair pair′ : A.Frame × State} → just pair ≡ just pair′ →
  Valid (proj₁ pair) (proj₂ pair) → Valid (proj₁ pair′) (proj₂ pair′)
result-valid eq = subst (λ pair → Valid (proj₁ pair) (proj₂ pair)) (just-injective eq)

-- Existing-entry selection either retains that entry or completes the caller.
choice-valid : ∀ first e d f s {out} → Present e (entries (cm s)) →
  A.applyChoice first e d f s ≡ just out → Valid (proj₁ out) (proj₂ out)
choice-valid first e C.retry f s present ()
choice-valid first e (C.waitInbound k) f s present eq = result-valid eq present
choice-valid true e (C.refuse err) f s present eq = result-valid eq tt
choice-valid false e (C.refuse err) f s present eq = result-valid eq tt
choice-valid first e (C.gone result) f s present eq = result-valid eq tt
choice-valid true e (C.reuse st result) f s present eq = result-valid eq tt
choice-valid false e (C.reuse st result) f s present eq = result-valid eq tt

-- Fresh selection allocates the captured entry in the same transaction.
known-valid : ∀ chosen m f s {out} → A.selectKnown chosen m f s ≡ just out →
  Valid (proj₁ out) (proj₂ out)
known-valid (just e) m f s eq with lookup e (entries (cm s)) in found
... | nothing = case eq of λ ()
... | just st = choice-valid true e (C.acquireCase st) f s (st , found) eq
known-valid nothing m f s eq with A.provenance (A.req f)
... | inbound = result-valid eq tt
... | outbound with lookup (ident (nextEntry (cm s))) (entries (cm s))
...   | just _ = case eq of λ ()
...   | nothing = result-valid eq
  (reservedOutbound , lookup-put (ident (nextEntry (cm s))) reservedOutbound (entries (cm s)))

-- The map/selection guards add no further validity premise at acquisition.
selection-valid : ∀ chosen f s {out} → A.selectEntry chosen f s ≡ just out →
  Valid (proj₁ out) (proj₂ out)
selection-valid chosen f s eq with mapCell (cm s)
... | taken _ = case eq of λ ()
... | full m with A.validSelection (A.peer (A.req f)) chosen m
...   | false = case eq of λ ()
...   | true = known-valid chosen m f s eq

-- A committed handshake always completes; it leaves no pending entry write.
success-valid : ∀ mode e k h flow f s {out} →
  A.commitSuccess mode e k h flow f s ≡ just out → Valid (proj₁ out) (proj₂ out)
success-valid mode e k h flow f s eq with lookup e (entries (cm s))
... | nothing = case eq of λ ()
... | just st with C.successCase k (A.child (A.req f)) h flow st
...   | C.decision replacement notify (C.raised err) = result-valid eq tt
...   | C.decision replacement false (C.connected k′ flow′ h′) with replacement
...     | nothing = result-valid eq tt
...     | just _ = result-valid eq tt
success-valid mode e k h flow f s eq | just st | C.decision replacement false (C.disconnected k′ reason) with replacement
... | nothing = result-valid eq tt
... | just _ = result-valid eq tt
success-valid noResponderMode e k h flow f s eq | just st | C.decision replacement true result with result | replacement
... | C.connected _ _ _ | nothing = result-valid eq tt
... | C.connected _ _ _ | just _ = result-valid eq tt
... | C.disconnected _ _ | nothing = result-valid eq tt
... | C.disconnected _ _ | just _ = result-valid eq tt
... | C.raised _ | _ = result-valid eq tt
success-valid responderMode e k h flow f s eq | just st | C.decision replacement true result
  with Queue.writeMessage (newConnection (newConnectionInfo outbound k flow h)) (inboundInfo s) in enqueued | result | replacement
... | nothing | C.connected _ _ _ | _ rewrite enqueued = case eq of λ ()
... | nothing | C.disconnected _ _ | _ rewrite enqueued = case eq of λ ()
... | just queue | C.connected _ _ _ | nothing rewrite enqueued = result-valid eq tt
... | just queue | C.connected _ _ _ | just _ rewrite enqueued = result-valid eq tt
... | just queue | C.disconnected _ _ | nothing rewrite enqueued = result-valid eq tt
... | just queue | C.disconnected _ _ | just _ rewrite enqueued = result-valid eq tt
... | _ | C.raised _ | _ = result-valid eq tt

-- Error/query completion likewise releases the frame's captured reference.
error-valid : ∀ e k reason f s {out} → A.commitError e k reason f s ≡ just out →
  Valid (proj₁ out) (proj₂ out)
error-valid e k reason f s eq with lookup e (entries (cm s)) | mapCell (cm s)
... | nothing | _ = case eq of λ ()
... | just _ | taken _ = case eq of λ ()
... | just st | full m = result-valid eq tt

-- Every acquisition action preserves allocation of the active capture.
step-valid : ∀ caller mode action f s {out} → Valid f s →
  A.step caller mode action f s ≡ just out → Valid (proj₁ out) (proj₂ out)
step-valid caller mode (A.select chosen) f s valid eq with A.pc f
... | A.selecting = selection-valid chosen f s eq
step-valid caller mode (A.select chosen) f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.allocatePromise e) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.openSocket e p) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.configureSocket e p) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.bindSocket e p) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.connectSocket e p) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.localAddress e p) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.forkHandler e p k) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.connectedCommit e p k) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.awaitResult e p k) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.commitResult e k result) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.waitingInbound e k) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.closeError e err′) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode (A.select chosen) f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq with A.pc f | mapCell (cm s)
... | A.count next | full m with countIncoming (entries (cm s)) m
...   | nothing = case eq of λ ()
...   | just _ = result-valid eq valid
step-valid caller mode A.readCounters f s valid eq | A.selecting | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.allocatePromise e) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.openSocket e p) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.configureSocket e p) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.bindSocket e p) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.connectSocket e p) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.localAddress e p) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.commitResult e k result) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.closeError e err′) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.removeError e err′) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.complete result) | _ = case eq of λ ()
step-valid caller mode A.readCounters f s valid eq | (A.count p) | taken w = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq with A.pc f
... | A.allocatePromise e with lookup (ident (nextPromise s)) (handshakeResults s)
...   | just _ = case eq of λ ()
...   | nothing = result-valid eq valid
step-valid caller mode A.newPromise f s valid eq | A.selecting = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.openSocket e p) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.configureSocket e p) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.bindSocket e p) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.connectSocket e p) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.localAddress e p) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.forkHandler e p k) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.connectedCommit e p k) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.awaitResult e p k) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.commitResult e k result) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.waitingInbound e k) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.closeError e err′) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode A.newPromise f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode A.openOK f s valid eq with A.pc f | lookup (A.socketRef (A.req f)) (sockets s)
... | A.openSocket e p | nothing = result-valid eq valid
step-valid caller mode A.openOK f s valid eq | A.selecting | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.count p) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.allocatePromise e) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.configureSocket e p) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.bindSocket e p) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.connectSocket e p) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.localAddress e p) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.commitResult e k result) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.closeError e err′) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.removeError e err′) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.complete result) | _ = case eq of λ ()
step-valid caller mode A.openOK f s valid eq | (A.openSocket e p) | just sock = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq with A.pc f | A.bindLocal (A.req f)
... | A.configureSocket e p | nothing = result-valid eq valid
... | A.configureSocket e p | just _ = result-valid eq valid
step-valid caller mode A.configureOK f s valid eq | A.selecting | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.count p) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.allocatePromise e) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.openSocket e p) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.bindSocket e p) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.connectSocket e p) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.localAddress e p) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.commitResult e k result) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.closeError e err′) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.removeError e err′) | _ = case eq of λ ()
step-valid caller mode A.configureOK f s valid eq | (A.complete result) | _ = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq with A.pc f
... | A.bindSocket e p = result-valid eq valid
step-valid caller mode A.bindOK f s valid eq | A.selecting = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.allocatePromise e) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.openSocket e p) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.configureSocket e p) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.connectSocket e p) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.localAddress e p) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.forkHandler e p k) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.connectedCommit e p k) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.awaitResult e p k) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.commitResult e k result) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.waitingInbound e k) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.closeError e err′) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode A.bindOK f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq with A.pc f
... | A.connectSocket e p = result-valid eq valid
step-valid caller mode A.connectOK f s valid eq | A.selecting = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.allocatePromise e) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.openSocket e p) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.configureSocket e p) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.bindSocket e p) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.localAddress e p) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.forkHandler e p k) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.connectedCommit e p k) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.awaitResult e p k) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.commitResult e k result) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.waitingInbound e k) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.closeError e err′) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode A.connectOK f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq with A.pc f
... | A.localAddress e p = result-valid eq valid
step-valid caller mode (A.gotLocal local) f s valid eq | A.selecting = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.allocatePromise e) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.openSocket e p) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.configureSocket e p) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.bindSocket e p) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.connectSocket e p) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.forkHandler e p k) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.connectedCommit e p k) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.awaitResult e p k) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.commitResult e k result) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.waitingInbound e k) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.closeError e err′) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode (A.gotLocal local) f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq with A.pc f | mapCell (cm s)
... | A.updateAddress e p k | full m with A.updateLocal k m
...   | true , m′ = result-valid eq valid
...   | false , m′ = result-valid eq valid
step-valid caller mode A.updateLocalAddress f s valid eq | A.selecting | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.count p) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.allocatePromise e) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.openSocket e p) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.configureSocket e p) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.bindSocket e p) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.connectSocket e p) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.localAddress e p) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.commitResult e k result) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.closeError e err′) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.removeError e err′) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.complete result) | _ = case eq of λ ()
step-valid caller mode A.updateLocalAddress f s valid eq | (A.updateAddress e p k) | taken w = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq with A.pc f | lookup (A.child (A.req f)) (handlers s)
... | A.forkHandler e p k | nothing = result-valid eq valid
step-valid caller mode A.forkOK f s valid eq | A.selecting | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.count p) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.allocatePromise e) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.openSocket e p) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.configureSocket e p) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.bindSocket e p) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.connectSocket e p) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.localAddress e p) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.commitResult e k result) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.closeError e err′) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.removeError e err′) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.complete result) | _ = case eq of λ ()
step-valid caller mode A.forkOK f s valid eq | (A.forkHandler e p k) | just h = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq with A.pc f
... | A.connectedCommit e p k with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just reservedOutbound = result-valid eq
  (unnegotiated outbound k (A.child (A.req f)) , lookup-put e (unnegotiated outbound k (A.child (A.req f))) (entries (cm s)))
...   | just (unnegotiated inbound _ _) = result-valid eq
  (unnegotiated outbound k (A.child (A.req f)) , lookup-put e (unnegotiated outbound k (A.child (A.req f))) (entries (cm s)))
...   | just old@(unnegotiated outbound _ _) = result-valid eq (old , found)
...   | just old@(outboundUni _ _ _) = result-valid eq (old , found)
...   | just old@(outboundDup _ _ _ _) = result-valid eq (old , found)
...   | just old@(outboundIdle _ _ _ _) = result-valid eq (old , found)
...   | just old@(inboundIdle _ _ _ _) = result-valid eq (old , found)
...   | just old@(inboundActive _ _ _ _) = result-valid eq (old , found)
...   | just old@(duplexActive _ _ _) = result-valid eq (old , found)
...   | just old@(terminating _ _ _) = result-valid eq (old , found)
...   | just old@(terminated _) = result-valid eq (old , found)
step-valid caller mode A.commitConnected f s valid eq | A.selecting = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.allocatePromise e) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.openSocket e p) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.configureSocket e p) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.bindSocket e p) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.connectSocket e p) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.localAddress e p) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.forkHandler e p k) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.awaitResult e p k) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.commitResult e k result) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.waitingInbound e k) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.closeError e err′) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode A.commitConnected f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq with A.pc f
... | A.awaitResult e p k with lookup p (handshakeResults s)
...   | nothing = case eq of λ ()
...   | just result = result-valid eq valid
step-valid caller mode A.readResult f s valid eq | A.selecting = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.allocatePromise e) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.openSocket e p) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.configureSocket e p) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.bindSocket e p) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.connectSocket e p) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.localAddress e p) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.forkHandler e p k) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.connectedCommit e p k) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.commitResult e k result) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.waitingInbound e k) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.closeError e err′) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode A.readResult f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq with A.pc f
... | A.commitResult e k (negotiated h flow) = success-valid mode e k h flow f s eq
... | A.commitResult e k query = error-valid e k handshakeQuery f s eq
... | A.commitResult e k (handlerError cls err) = error-valid e k (handshakeError cls err) f s eq
step-valid caller mode A.commitHandshake f s valid eq | A.selecting = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.allocatePromise e) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.openSocket e p) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.configureSocket e p) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.bindSocket e p) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.connectSocket e p) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.localAddress e p) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.forkHandler e p k) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.connectedCommit e p k) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.awaitResult e p k) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.waitingInbound e k) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.closeError e err′) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode A.commitHandshake f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq with A.pc f
... | A.waitingInbound e k with lookup e (entries (cm s)) in found
...   | nothing = case eq of λ ()
...   | just st = choice-valid false e (C.waitCase k st) f s (st , found) eq
step-valid caller mode A.waitNegotiated f s valid eq | A.selecting = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.allocatePromise e) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.openSocket e p) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.configureSocket e p) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.bindSocket e p) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.connectSocket e p) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.localAddress e p) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.forkHandler e p k) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.connectedCommit e p k) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.awaitResult e p k) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.commitResult e k result) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.closeError e err′) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode A.waitNegotiated f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode (A.failIO err) f s valid eq with A.pc f
... | A.openSocket e p = result-valid eq tt
... | A.configureSocket e p = result-valid eq valid
... | A.bindSocket e p = result-valid eq valid
... | A.connectSocket e p = result-valid eq valid
... | A.localAddress e p = result-valid eq valid
... | A.forkHandler e p k = result-valid eq valid
step-valid caller mode (A.failIO err) f s valid eq | A.selecting = case eq of λ ()
step-valid caller mode (A.failIO err) f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode (A.failIO err) f s valid eq | (A.allocatePromise e) = case eq of λ ()
step-valid caller mode (A.failIO err) f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode (A.failIO err) f s valid eq | (A.connectedCommit e p k) = case eq of λ ()
step-valid caller mode (A.failIO err) f s valid eq | (A.awaitResult e p k) = case eq of λ ()
step-valid caller mode (A.failIO err) f s valid eq | (A.commitResult e k result) = case eq of λ ()
step-valid caller mode (A.failIO err) f s valid eq | (A.waitingInbound e k) = case eq of λ ()
step-valid caller mode (A.failIO err) f s valid eq | (A.closeError e err′) = case eq of λ ()
step-valid caller mode (A.failIO err) f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode (A.failIO err) f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq with A.pc f
... | A.closeError e err = result-valid eq valid
step-valid caller mode A.closeOK f s valid eq | A.selecting = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.allocatePromise e) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.openSocket e p) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.configureSocket e p) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.bindSocket e p) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.connectSocket e p) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.localAddress e p) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.forkHandler e p k) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.connectedCommit e p k) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.awaitResult e p k) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.commitResult e k result) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.waitingInbound e k) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode A.closeOK f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq with A.pc f
... | A.closeError e _ = result-valid eq tt
step-valid caller mode (A.closeFailed err) f s valid eq | A.selecting = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.count p) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.allocatePromise e) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.openSocket e p) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.configureSocket e p) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.bindSocket e p) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.connectSocket e p) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.localAddress e p) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.updateAddress e p k) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.forkHandler e p k) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.connectedCommit e p k) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.awaitResult e p k) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.commitResult e k result) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.waitingInbound e k) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.removeError e err′) = case eq of λ ()
step-valid caller mode (A.closeFailed err) f s valid eq | (A.complete result) = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq with A.pc f | mapCell (cm s)
... | A.removeError e err | full m = result-valid eq tt
step-valid caller mode A.removeReservation f s valid eq | A.selecting | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.count p) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.allocatePromise e) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.openSocket e p) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.configureSocket e p) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.bindSocket e p) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.connectSocket e p) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.localAddress e p) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.updateAddress e p k) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.forkHandler e p k) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.connectedCommit e p k) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.awaitResult e p k) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.commitResult e k result) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.waitingInbound e k) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.closeError e err′) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.complete result) | _ = case eq of λ ()
step-valid caller mode A.removeReservation f s valid eq | (A.removeError e err′) | taken w = case eq of λ ()
step-valid caller mode A.returnResult f s valid ()

open import Data.List using (List; []; _∷_)
open import Data.Nat using (_<_)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds; lookup-key)
import ConnectionManagement.Properties.OutboundSupply as Supply

-- Single-caller finite runs use the actual rule, with no action restriction.
data Runs (caller : WorkerId) (mode : ResponderMode) :
  A.Frame → State → List A.Action → A.Frame → State → Set where
  done : ∀ {f s} → Runs caller mode f s [] f s
  next : ∀ {f s f₁ s₁ f₂ s₂ a as} → A.step caller mode a f s ≡ just (f₁ , s₁) →
    Runs caller mode f₁ s₁ as f₂ s₂ → Runs caller mode f s (a ∷ as) f₂ s₂

-- Preservation extends to every successful finite acquisition run.
run-valid : ∀ {caller mode f s actions f′ s′} → Valid f s →
  Runs caller mode f s actions f′ s′ → Valid f′ s′
run-valid valid done = valid
run-valid {caller} {mode} valid (next {f = f} {s = s} {a = a} eq rest) =
  run-valid (step-valid caller mode a f s valid eq) rest

-- A newly begun acquisition needs no hand-supplied capture certificate.
from-selecting-valid : ∀ {caller mode req s actions f′ s′} →
  Runs caller mode (A.frame req A.selecting) s actions f′ s′ → Valid f′ s′
from-selecting-valid = run-valid tt

-- Abstract interference is permitted only with a proved heap-retention law.
retained-valid : ∀ f s s′ →
  (∀ e → Present e (entries (cm s)) → Present e (entries (cm s′))) →
  Valid f s → Valid f s′
retained-valid f s s′ retains valid with capture (A.pc f)
... | nothing = tt
... | just e = retains e valid

-- Allocated captures inherit the current heap's existing supply bound.
remove-capture-bound : ∀ req e err s → Valid (A.frame req (A.removeError e err)) s →
  SupplyBounds s → serial e < nextEntry (cm s)
remove-capture-bound req e err s (old , found) (bounded , _) =
  lookup-key (λ k → serial k < nextEntry (cm s)) e (entries (cm s)) bounded found

-- The new certificate discharges the explicit cleanup-bound premise without
-- adding a guard to the source-derived transition or weakening SupplyBounds.
valid-removal-preserves-supply : ∀ caller mode req e err s {f′ s′} →
  Valid (A.frame req (A.removeError e err)) s → SupplyBounds s →
  A.step caller mode A.removeReservation (A.frame req (A.removeError e err)) s ≡ just (f′ , s′) →
  SupplyBounds s′
valid-removal-preserves-supply caller mode req e err s valid bounded eq =
  Supply.remove-reservation-preserves caller mode req e err s
    (remove-capture-bound req e err s valid bounded) eq bounded

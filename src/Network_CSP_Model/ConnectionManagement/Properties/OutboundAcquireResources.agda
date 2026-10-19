{-# OPTIONS --guardedness #-}

-- All successful outbound acquire steps preserve a fixed handler and its resources.
module ConnectionManagement.Properties.OutboundAcquireResources where

open import Data.Bool using (true; false)
open import Data.Maybe using (just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; subst)
open import Function using (case_of_)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Store using (lookup)
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.InformationChannel as Queue

open import ConnectionManagement.Properties.HandlerResourceFacts

-- The observer may differ from the caller and the newly forked child.
module For (q : WorkerId) (captured : HandlerStart) where

  -- Transport facts through the exact successful result.
  result-retains : ∀ {pair pair′ : A.Frame × State} → just pair ≡ just pair′ →
    Facts q captured (proj₂ pair) → Facts q captured (proj₂ pair′)
  result-retains eq = subst (λ pair → Facts q captured (proj₂ pair)) (just-injective eq)

  -- Reuse writes retain the captured entry identity.
  choice-retains : ∀ first e d f s {out} → Facts q captured s →
    A.applyChoice first e d f s ≡ just out → Facts q captured (proj₂ out)
  choice-retains first e C.retry f s facts ()
  choice-retains first e (C.waitInbound k) f s facts eq = result-retains eq facts
  choice-retains true e (C.refuse err) f s facts eq = result-retains eq facts
  choice-retains false e (C.refuse err) f s facts eq = result-retains eq facts
  choice-retains first e (C.gone result) f s facts eq = result-retains eq facts
  choice-retains true e (C.reuse st result) f s facts eq = result-retains eq (entry-write e st s facts)
  choice-retains false e (C.reuse st result) f s facts eq = result-retains eq (entry-write e st s facts)

  -- Fresh reservations retain earlier handlers and resources.
  known-retains : ∀ chosen m f s {out} → Facts q captured s →
    A.selectKnown chosen m f s ≡ just out → Facts q captured (proj₂ out)
  known-retains (just e) m f s facts eq with lookup e (entries (cm s)) in found
  ... | nothing = case eq of λ ()
  ... | just st = choice-retains true e (C.acquireCase st) f s facts eq
  known-retains nothing m f s facts eq with A.provenance (A.req f)
  ... | inbound = result-retains eq facts
  ... | outbound with lookup (ident (nextEntry (cm s))) (entries (cm s))
  ...   | just _ = case eq of λ ()
  ...   | nothing = result-retains eq
    (entry-write (ident (nextEntry (cm s))) reservedOutbound s facts)

  -- Selection delegates to the guarded lookup/reservation branch.
  selection-retains : ∀ chosen f s {out} → Facts q captured s →
    A.selectEntry chosen f s ≡ just out → Facts q captured (proj₂ out)
  selection-retains chosen f s facts eq with mapCell (cm s)
  ... | taken _ = case eq of λ ()
  ... | full m with A.validSelection (A.peer (A.req f)) chosen m
  ...   | false = case eq of λ ()
  ...   | true = known-retains chosen m f s facts eq

  -- Handshake writes and notifications preserve existing resources.
  success-retains : ∀ mode e k h flow f s {out} → Facts q captured s →
    A.commitSuccess mode e k h flow f s ≡ just out → Facts q captured (proj₂ out)
  success-retains mode e k h flow f s facts eq with lookup e (entries (cm s))
  ... | nothing = case eq of λ ()
  ... | just st with C.successCase k (A.child (A.req f)) h flow st
  ...   | C.decision replacement notify (C.raised err) = result-retains eq facts
  ...   | C.decision replacement false (C.connected k′ flow′ h′) with replacement
  ...     | nothing = result-retains eq facts
  ...     | just replacement′ = result-retains eq (entry-write e replacement′ s facts)
  success-retains mode e k h flow f s facts eq | just st | C.decision replacement false (C.disconnected k′ reason) with replacement
  ... | nothing = result-retains eq facts
  ... | just replacement′ = result-retains eq (entry-write e replacement′ s facts)
  success-retains noResponderMode e k h flow f s facts eq | just st | C.decision replacement true result with result | replacement
  ... | C.connected _ _ _ | nothing = result-retains eq facts
  ... | C.connected _ _ _ | just replacement′ = result-retains eq (entry-write e replacement′ s facts)
  ... | C.disconnected _ _ | nothing = result-retains eq facts
  ... | C.disconnected _ _ | just replacement′ = result-retains eq (entry-write e replacement′ s facts)
  ... | C.raised _ | _ = result-retains eq facts
  success-retains responderMode e k h flow f s facts eq | just st | C.decision replacement true result
    with Queue.writeMessage (newConnection (newConnectionInfo outbound k flow h)) (inboundInfo s) in enqueued | result | replacement
  ... | nothing | C.connected _ _ _ | _ rewrite enqueued = case eq of λ ()
  ... | nothing | C.disconnected _ _ | _ rewrite enqueued = case eq of λ ()
  ... | just queue | C.connected _ _ _ | nothing rewrite enqueued = result-retains eq facts
  ... | just queue | C.connected _ _ _ | just replacement′ rewrite enqueued = result-retains eq (entry-write e replacement′ s facts)
  ... | just queue | C.disconnected _ _ | nothing rewrite enqueued = result-retains eq facts
  ... | just queue | C.disconnected _ _ | just replacement′ rewrite enqueued = result-retains eq (entry-write e replacement′ s facts)
  ... | _ | C.raised _ | _ = result-retains eq facts

  -- Identity-guarded map deletion does not remove historical heap records.
  error-retains : ∀ e k reason f s {out} → Facts q captured s →
    A.commitError e k reason f s ≡ just out → Facts q captured (proj₂ out)
  error-retains e k reason f s facts eq with lookup e (entries (cm s)) | mapCell (cm s)
  ... | nothing | _ = case eq of λ ()
  ... | just _ | taken _ = case eq of λ ()
  ... | just st | full m = result-retains eq (entry-write e _ s facts)

  -- Exhaust all successful actions, including fork, socket close and IO failure.
  step-retains : ∀ caller mode action f s {out} → Facts q captured s →
    A.step caller mode action f s ≡ just out → Facts q captured (proj₂ out)
  step-retains caller mode (A.select chosen) f s facts eq with A.pc f
  ... | A.selecting = selection-retains chosen f s facts eq
  step-retains caller mode (A.select chosen) f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.allocatePromise e) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.openSocket e p) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.configureSocket e p) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.bindSocket e p) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.connectSocket e p) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.localAddress e p) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.forkHandler e p k) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.connectedCommit e p k) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.awaitResult e p k) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.commitResult e k result) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.waitingInbound e k) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.closeError e err′) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode (A.select chosen) f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq with A.pc f | mapCell (cm s)
  ... | A.count next | full m with countIncoming (entries (cm s)) m
  ...   | nothing = case eq of λ ()
  ...   | just _ = result-retains eq facts
  step-retains caller mode A.readCounters f s facts eq | A.selecting | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.openSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.localAddress e p) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.closeError e err′) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.removeError e err′) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.complete result) | _ = case eq of λ ()
  step-retains caller mode A.readCounters f s facts eq | (A.count p) | taken w = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq with A.pc f
  ... | A.allocatePromise e with lookup (ident (nextPromise s)) (handshakeResults s)
  ...   | just _ = case eq of λ ()
  ...   | nothing = result-retains eq facts
  step-retains caller mode A.newPromise f s facts eq | A.selecting = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.openSocket e p) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.configureSocket e p) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.bindSocket e p) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.connectSocket e p) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.localAddress e p) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.forkHandler e p k) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.connectedCommit e p k) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.awaitResult e p k) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.commitResult e k result) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.waitingInbound e k) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.closeError e err′) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode A.newPromise f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq with A.pc f | lookup (A.socketRef (A.req f)) (sockets s)
  ... | A.openSocket e p | nothing = result-retains eq (socket-write (A.socketRef (A.req f)) (admitting caller) s facts)
  step-retains caller mode A.openOK f s facts eq | A.selecting | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.count p) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.localAddress e p) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.closeError e err′) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.removeError e err′) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.complete result) | _ = case eq of λ ()
  step-retains caller mode A.openOK f s facts eq | (A.openSocket e p) | just sock = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq with A.pc f | A.bindLocal (A.req f)
  ... | A.configureSocket e p | nothing = result-retains eq facts
  ... | A.configureSocket e p | just _ = result-retains eq facts
  step-retains caller mode A.configureOK f s facts eq | A.selecting | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.count p) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.openSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.localAddress e p) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.closeError e err′) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.removeError e err′) | _ = case eq of λ ()
  step-retains caller mode A.configureOK f s facts eq | (A.complete result) | _ = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq with A.pc f
  ... | A.bindSocket e p = result-retains eq facts
  step-retains caller mode A.bindOK f s facts eq | A.selecting = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.allocatePromise e) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.openSocket e p) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.configureSocket e p) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.connectSocket e p) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.localAddress e p) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.forkHandler e p k) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.connectedCommit e p k) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.awaitResult e p k) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.commitResult e k result) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.waitingInbound e k) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.closeError e err′) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode A.bindOK f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq with A.pc f
  ... | A.connectSocket e p = result-retains eq facts
  step-retains caller mode A.connectOK f s facts eq | A.selecting = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.allocatePromise e) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.openSocket e p) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.configureSocket e p) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.bindSocket e p) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.localAddress e p) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.forkHandler e p k) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.connectedCommit e p k) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.awaitResult e p k) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.commitResult e k result) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.waitingInbound e k) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.closeError e err′) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode A.connectOK f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq with A.pc f
  ... | A.localAddress e p = result-retains eq facts
  step-retains caller mode (A.gotLocal local) f s facts eq | A.selecting = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.allocatePromise e) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.openSocket e p) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.configureSocket e p) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.bindSocket e p) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.connectSocket e p) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.forkHandler e p k) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.connectedCommit e p k) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.awaitResult e p k) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.commitResult e k result) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.waitingInbound e k) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.closeError e err′) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode (A.gotLocal local) f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq with A.pc f | mapCell (cm s)
  ... | A.updateAddress e p k | full m with A.updateLocal k m
  ...   | true , m′ = result-retains eq facts
  ...   | false , m′ = result-retains eq facts
  step-retains caller mode A.updateLocalAddress f s facts eq | A.selecting | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.count p) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.openSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.localAddress e p) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.closeError e err′) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.removeError e err′) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.complete result) | _ = case eq of λ ()
  step-retains caller mode A.updateLocalAddress f s facts eq | (A.updateAddress e p k) | taken w = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq with A.pc f | lookup (A.child (A.req f)) (handlers s) in absent
  ... | A.forkHandler e p k | nothing = result-retains eq
    (fork-write (A.child (A.req f)) (handlerStart e (A.socketRef (A.req f)) p k) s absent facts)
  step-retains caller mode A.forkOK f s facts eq | A.selecting | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.count p) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.openSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.localAddress e p) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.closeError e err′) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.removeError e err′) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.complete result) | _ = case eq of λ ()
  step-retains caller mode A.forkOK f s facts eq | (A.forkHandler e p k) | just h = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq with A.pc f
  ... | A.connectedCommit e p k with lookup e (entries (cm s)) in found
  ...   | nothing = case eq of λ ()
  ...   | just reservedOutbound = result-retains eq
    (entry-write e (unnegotiated outbound k (A.child (A.req f))) s facts)
  ...   | just (unnegotiated inbound _ _) = result-retains eq
    (entry-write e (unnegotiated outbound k (A.child (A.req f))) s facts)
  ...   | just old@(unnegotiated outbound _ _) = result-retains eq facts
  ...   | just old@(outboundUni _ _ _) = result-retains eq facts
  ...   | just old@(outboundDup _ _ _ _) = result-retains eq facts
  ...   | just old@(outboundIdle _ _ _ _) = result-retains eq facts
  ...   | just old@(inboundIdle _ _ _ _) = result-retains eq facts
  ...   | just old@(inboundActive _ _ _ _) = result-retains eq facts
  ...   | just old@(duplexActive _ _ _) = result-retains eq facts
  ...   | just old@(terminating _ _ _) = result-retains eq facts
  ...   | just old@(terminated _) = result-retains eq facts
  step-retains caller mode A.commitConnected f s facts eq | A.selecting = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.allocatePromise e) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.openSocket e p) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.configureSocket e p) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.bindSocket e p) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.connectSocket e p) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.localAddress e p) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.forkHandler e p k) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.awaitResult e p k) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.commitResult e k result) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.waitingInbound e k) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.closeError e err′) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode A.commitConnected f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq with A.pc f
  ... | A.awaitResult e p k with lookup p (handshakeResults s)
  ...   | nothing = case eq of λ ()
  ...   | just result = result-retains eq facts
  step-retains caller mode A.readResult f s facts eq | A.selecting = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.allocatePromise e) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.openSocket e p) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.configureSocket e p) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.bindSocket e p) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.connectSocket e p) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.localAddress e p) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.forkHandler e p k) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.connectedCommit e p k) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.commitResult e k result) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.waitingInbound e k) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.closeError e err′) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode A.readResult f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq with A.pc f
  ... | A.commitResult e k (negotiated h flow) = success-retains mode e k h flow f s facts eq
  ... | A.commitResult e k query = error-retains e k handshakeQuery f s facts eq
  ... | A.commitResult e k (handlerError cls err) = error-retains e k (handshakeError cls err) f s facts eq
  step-retains caller mode A.commitHandshake f s facts eq | A.selecting = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.allocatePromise e) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.openSocket e p) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.configureSocket e p) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.bindSocket e p) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.connectSocket e p) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.localAddress e p) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.forkHandler e p k) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.connectedCommit e p k) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.awaitResult e p k) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.waitingInbound e k) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.closeError e err′) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode A.commitHandshake f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq with A.pc f
  ... | A.waitingInbound e k with lookup e (entries (cm s)) in found
  ...   | nothing = case eq of λ ()
  ...   | just st = choice-retains false e (C.waitCase k st) f s facts eq
  step-retains caller mode A.waitNegotiated f s facts eq | A.selecting = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.allocatePromise e) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.openSocket e p) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.configureSocket e p) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.bindSocket e p) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.connectSocket e p) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.localAddress e p) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.forkHandler e p k) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.connectedCommit e p k) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.awaitResult e p k) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.commitResult e k result) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.closeError e err′) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode A.waitNegotiated f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode (A.failIO err) f s facts eq with A.pc f
  ... | A.openSocket e p = result-retains eq facts
  ... | A.configureSocket e p = result-retains eq facts
  ... | A.bindSocket e p = result-retains eq facts
  ... | A.connectSocket e p = result-retains eq facts
  ... | A.localAddress e p = result-retains eq facts
  ... | A.forkHandler e p k = result-retains eq facts
  step-retains caller mode (A.failIO err) f s facts eq | A.selecting = case eq of λ ()
  step-retains caller mode (A.failIO err) f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode (A.failIO err) f s facts eq | (A.allocatePromise e) = case eq of λ ()
  step-retains caller mode (A.failIO err) f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode (A.failIO err) f s facts eq | (A.connectedCommit e p k) = case eq of λ ()
  step-retains caller mode (A.failIO err) f s facts eq | (A.awaitResult e p k) = case eq of λ ()
  step-retains caller mode (A.failIO err) f s facts eq | (A.commitResult e k result) = case eq of λ ()
  step-retains caller mode (A.failIO err) f s facts eq | (A.waitingInbound e k) = case eq of λ ()
  step-retains caller mode (A.failIO err) f s facts eq | (A.closeError e err′) = case eq of λ ()
  step-retains caller mode (A.failIO err) f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode (A.failIO err) f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq with A.pc f
  ... | A.closeError e err = result-retains eq (socket-write (A.socketRef (A.req f)) closed s facts)
  step-retains caller mode A.closeOK f s facts eq | A.selecting = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.allocatePromise e) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.openSocket e p) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.configureSocket e p) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.bindSocket e p) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.connectSocket e p) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.localAddress e p) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.forkHandler e p k) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.connectedCommit e p k) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.awaitResult e p k) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.commitResult e k result) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.waitingInbound e k) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode A.closeOK f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq with A.pc f
  ... | A.closeError e _ = result-retains eq (socket-write (A.socketRef (A.req f)) (closeUncertain err) s facts)
  step-retains caller mode (A.closeFailed err) f s facts eq | A.selecting = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.count p) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.allocatePromise e) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.openSocket e p) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.configureSocket e p) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.bindSocket e p) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.connectSocket e p) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.localAddress e p) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.updateAddress e p k) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.forkHandler e p k) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.connectedCommit e p k) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.awaitResult e p k) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.commitResult e k result) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.waitingInbound e k) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.removeError e err′) = case eq of λ ()
  step-retains caller mode (A.closeFailed err) f s facts eq | (A.complete result) = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq with A.pc f | mapCell (cm s)
  ... | A.removeError e err | full m = result-retains eq (entry-write e (terminated nothing) s facts)
  step-retains caller mode A.removeReservation f s facts eq | A.selecting | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.count p) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.allocatePromise e) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.openSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.configureSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.bindSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.connectSocket e p) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.localAddress e p) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.updateAddress e p k) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.forkHandler e p k) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.connectedCommit e p k) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.awaitResult e p k) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.commitResult e k result) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.waitingInbound e k) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.closeError e err′) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.complete result) | _ = case eq of λ ()
  step-retains caller mode A.removeReservation f s facts eq | (A.removeError e err′) | taken w = case eq of λ ()
  step-retains caller mode A.returnResult f s facts ()

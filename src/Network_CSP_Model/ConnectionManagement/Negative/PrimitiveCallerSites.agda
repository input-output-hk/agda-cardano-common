{-# OPTIONS --guardedness #-}

-- G1 permission-layer equations for every acquisition cancellation PC. These
-- test the existing planner, not physical reachability or arbitrary RTS delivery.
-- Actual caller detach/cleanup witnesses remain in Negative/GovernorPool.
module ConnectionManagement.Negative.PrimitiveCallerSites where

open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import ConnectionManagement.Rules.CallerCancellation as C
import ConnectionManagement.Rules.OutboundAcquire as A

selecting : C.plan C.ordinary A.selecting ≡ just C.abandon
selecting = refl
counters : ∀ pc → C.plan C.ordinary (A.count pc) ≡ C.plan C.ordinary pc
counters pc = refl
counter-enabled : C.plan C.ordinary (A.count A.selecting) ≡ just C.abandon
counter-enabled = refl
counter-open-refused : ∀ e p → C.plan C.ordinary (A.count (A.openSocket e p)) ≡ nothing
counter-open-refused e p = refl
promise : ∀ e → C.plan C.ordinary (A.allocatePromise e) ≡ just C.abandon
promise e = refl
open-blocked : ∀ e p → C.plan C.interruptibleOpen (A.openSocket e p) ≡ just C.abandon
open-blocked e p = refl
open-ordinary-refused : ∀ e p → C.plan C.ordinary (A.openSocket e p) ≡ nothing
open-ordinary-refused e p = refl
configure : ∀ e p → C.plan C.ordinary (A.configureSocket e p) ≡ just (C.closeCaptured e)
configure e p = refl
bind : ∀ e p → C.plan C.ordinary (A.bindSocket e p) ≡ just (C.closeCaptured e)
bind e p = refl
connect : ∀ e p → C.plan C.ordinary (A.connectSocket e p) ≡ just (C.closeCaptured e)
connect e p = refl
local-address : ∀ e p → C.plan C.ordinary (A.localAddress e p) ≡ just (C.closeCaptured e)
local-address e p = refl
update-address : ∀ e p k → C.plan C.ordinary (A.updateAddress e p k) ≡ just (C.closeCaptured e)
update-address e p k = refl
fork : ∀ e p k → C.plan C.ordinary (A.forkHandler e p k) ≡ just (C.closeCaptured e)
fork e p k = refl
before-handoff : ∀ e p k → C.plan C.forkedBeforeHandoff (A.connectedCommit e p k) ≡ just (C.closeCaptured e)
before-handoff e p k = refl
after-handoff : ∀ e p k → C.plan C.ordinary (A.connectedCommit e p k) ≡ just C.abandon
after-handoff e p k = refl
await-result : ∀ e p k → C.plan C.ordinary (A.awaitResult e p k) ≡ just C.abandon
await-result e p k = refl
commit-result : ∀ e k r → C.plan C.ordinary (A.commitResult e k r) ≡ just C.abandon
commit-result e k r = refl
wait-inbound : ∀ e k → C.plan C.ordinary (A.waitingInbound e k) ≡ just C.abandon
wait-inbound e k = refl
complete : ∀ r → C.plan C.ordinary (A.complete r) ≡ just C.abandon
complete r = refl
close-protected : ∀ e err → C.plan C.ordinary (A.closeError e err) ≡ nothing
close-protected e err = refl
remove-protected : ∀ e err → C.plan C.ordinary (A.removeError e err) ≡ nothing
remove-protected e err = refl

-- Each arbitrary PC is refused under the explicit protected-cleanup context.
protected : ∀ pc → C.plan C.protectedCleanup pc ≡ nothing
protected pc = refl
wrong-context : C.plan C.forkedBeforeHandoff A.selecting ≡ nothing
wrong-context = refl

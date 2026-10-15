{-# OPTIONS --guardedness #-}

-- Explicit finite snapshots keep each proof a small single-step computation.
-- These builders describe fixtures, not another operational semantics.
module ConnectionManagement.CSP.Fixtures where

open import Data.Nat using (ℕ)
open import Data.List using (List; []; _∷_; map)
open import Data.Product using (_,_)
open import Data.Maybe using (just; nothing)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store)
open import ConnectionManagement.State
open import ConnectionManagement.Machine
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.Cleanup as Cleanup
open import ConnectionManagement.Scenarios.Admission using
  (fixture; emptyCM; r₀; r₁; w₀; w₁; child₀; key₀)
open import ConnectionManagement.Scenarios.Handshake using (success; info)

entry₀ : EntryId
entry₀ = ident 0
promise₀ : PromiseId
promise₀ = ident 0

unneg : ConnectionState
unneg = unnegotiated inbound key₀ child₀
idle : ConnectionState
idle = inboundIdle key₀ child₀ (ident 0) duplex

binding : ConnMap
binding = insertConnection key₀ entry₀ []
parentLease childLease : Lease
parentLease = lease w₀ []
childLease = lease child₀ binding

requests : AdmissionPC → Store WorkerId AdmissionWorker
requests p = (w₀ , admissionWorker r₀ p) ∷ (w₁ , admissionWorker r₁ acquireMap) ∷ []

-- Before the fork: no handler record, both accepted sockets belong to callers.
pre : CMStore → AdmissionPC → List PromiseId → ℕ → Configuration
pre cm pc ps n = initial responderMode (state cm (requests pc) []
  ((ident 0 , admitting w₀) ∷ (ident 1 , admitting w₁) ∷ []) ps n [] [] [])

-- After the fork, all fixtures retain the same entry/handler/promise identities.
snapshot : ConnectionState → MapCell → AdmissionPC → SocketOwner →
  Store PromiseId HandshakeResult → List NewConnectionInfo → Store WorkerId CleanupPC → Configuration
snapshot st cell pc owner rs queue cs = initial responderMode
  (state (cmStore cell ((entry₀ , st) ∷ []) 1) (requests pc)
    ((child₀ , handlerStart entry₀ (ident 0) promise₀ key₀) ∷ [])
    ((ident 0 , owner) ∷ (ident 1 , admitting w₁) ∷ [])
    (promise₀ ∷ []) 1 rs (map newConnection queue) cs)

resultStore : Store PromiseId HandshakeResult
resultStore = (promise₀ , success) ∷ []

cleanupStore : CleanupPC → Store WorkerId CleanupPC
cleanupStore p = (child₀ , p) ∷ []

start : Configuration
start = initial responderMode (fixture emptyCM)

admit : List Action
admit = admissionStep w₀ Server.take ∷ admissionStep w₀ Server.countLimit ∷
  admissionStep w₀ Server.allocatePromise ∷ admissionStep w₀ Server.chooseEntry ∷
  admissionStep w₀ Server.fork ∷ admissionStep w₀ Server.putMapBack ∷
  admissionStep w₀ Server.readCounters ∷ []

waiting : Configuration
waiting = snapshot unneg (full binding) (awaitHandshake promise₀ entry₀) (handling child₀) [] [] []

admit-path : Executes start admit waiting
admit-path = next {c₁ = a₁} refl (next {c₁ = a₂} refl (next {c₁ = a₃} refl
  (next {c₁ = a₄} refl (next {c₁ = a₅} refl (next {c₁ = a₆} refl (next {c₁ = waiting} refl done))))))
  where
  locked = cmStore (taken w₀) [] 0
  a₁ = pre locked (count parentLease) [] 0
  a₂ = pre locked (prepare parentLease) [] 0
  a₃ = pre locked (selectEntry parentLease promise₀) (promise₀ ∷ []) 1
  a₄ = pre (cmStore (taken w₀) ((entry₀ , unneg) ∷ []) 1)
    (forkHandler parentLease promise₀ entry₀) (promise₀ ∷ []) 1
  a₅ = snapshot unneg (taken w₀) (publish parentLease promise₀ entry₀) (handling child₀) [] [] []
  a₆ = snapshot unneg (full binding) (countPublished promise₀ entry₀) (handling child₀) [] [] []

published : Configuration
published = snapshot unneg (full binding) (awaitHandshake promise₀ entry₀) (handling child₀) resultStore [] []

publication-path : Executes waiting (handlerPublication child₀ success resultWritten ∷ []) published
publication-path = next refl done

committed : Configuration
committed = snapshot idle (full binding) (countHandshake (connected info)) (handling child₀) resultStore [] []

consume : List Action
consume = handshakeStep w₀ Handshake.readResult ∷ handshakeStep w₀ Handshake.commitResult ∷ []

consume-path : Executes published consume committed
consume-path = next {c₁ = read} refl (next {c₁ = committed} refl done)
  where
  read = snapshot unneg (full binding) (commitHandshake entry₀ success) (handling child₀) resultStore [] []

cleanupActions : List Action
cleanupActions = handlerExit child₀ ∷ cleanupStep child₀ Cleanup.takeCleanupMap ∷
  cleanupStep child₀ Cleanup.selectCleanupEntry ∷ cleanupStep child₀ Cleanup.closeHandlerSocket ∷
  cleanupStep child₀ Cleanup.publishCleanupMap ∷ cleanupStep child₀ Cleanup.readCleanupCounters ∷ []

cleaned : AdmissionPC → Configuration
cleaned pc = snapshot (terminated nothing) (full []) pc closed resultStore [] (cleanupStore (cleanupDone cleanupNormal))

-- A proof schema for ordinary cleanup. The branch premise is explicit; it is
-- discharged separately for the two concrete input states used below.
cleanup-path : ∀ st pc → Cleanup.decideCleanup st ≡ Cleanup.terminateAndPurge →
  Executes (snapshot st (full binding) pc (handling child₀) resultStore [] []) cleanupActions (cleaned pc)
cleanup-path st pc decision = next {c₁ = c₁} refl (next {c₁ = c₂} refl
  (next {c₁ = c₃} selectEq (next {c₁ = c₄} refl (next {c₁ = c₅} refl (next {c₁ = cleaned pc} refl done)))))
  where
  c₁ = snapshot st (full binding) pc (handling child₀) resultStore [] (cleanupStore cleanupAcquire)
  c₂ = snapshot st (taken child₀) pc (handling child₀) resultStore [] (cleanupStore (cleanupSelect childLease))
  c₃ = snapshot (terminated nothing) (taken child₀) pc (handling child₀) resultStore []
    (cleanupStore (cleanupClose childLease [] countImmediately))
  c₄ = snapshot (terminated nothing) (taken child₀) pc closed resultStore []
    (cleanupStore (cleanupPublish childLease [] countImmediately))
  c₅ = snapshot (terminated nothing) (full []) pc closed resultStore [] (cleanupStore (cleanupCount cleanupNormal))
  selectEq : advance (cleanupStep child₀ Cleanup.selectCleanupEntry) c₂ ≡ just c₃
  selectEq rewrite decision = refl

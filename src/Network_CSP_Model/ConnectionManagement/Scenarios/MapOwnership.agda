{-# OPTIONS --guardedness #-}

-- Single-step witnesses exercise each proved map action, including both
-- publication tails and admission rejection paths. Not full source reachability.
module ConnectionManagement.Scenarios.MapOwnership where

open import Data.List using ([]; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.Properties.Ownership
open import ConnectionManagement.CSP.Fixtures
open import ConnectionManagement.CSP.Ownership
open import ConnectionManagement.Scenarios.Admission using (w₀; child₀; key₀)
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Cleanup as Cleanup

-- Every witness carries an enabled step and ownership at both endpoints.
OwnedStep : Action → Configuration → Configuration → Set
OwnedStep a c c′ = advance a c ≡ just c′ × Ownership (world c) × Ownership (world c′)

certify : ∀ {a c c′} → MapAction a → advance a c ≡ just c′ → Ownership (world c) → OwnedStep a c c′
certify {a} {c} {c′} covered eq own = eq , own , map-action-preserves {a} {c} {c′} covered eq own

admissionLocked : Configuration
admissionLocked = pre (cmStore (taken w₀) [] 0) (count parentLease) [] 0

admission-takes : OwnedStep (admissionStep w₀ Server.take) start admissionLocked
admission-takes = certify {c = start} {c′ = admissionLocked} (admissionTake w₀) refl refl

beforePublish afterPublish : Configuration
beforePublish = snapshot unneg (taken w₀) (publish parentLease promise₀ entry₀)
  (handling child₀) [] [] []
afterPublish = snapshot unneg (full binding) (countPublished promise₀ entry₀)
  (handling child₀) [] [] []

admission-publishes : OwnedStep (admissionStep w₀ Server.putMapBack) beforePublish afterPublish
admission-publishes = certify {c = beforePublish} {c′ = afterPublish} (admissionPublish w₀) refl (parentLease , refl , refl)

rejected restored : Failure → Configuration
rejected reason = pre (cmStore (taken w₀) [] 0) (reject parentLease reason) [] 0
restored reason = pre (cmStore (full []) [] 0) (closeSocket reason) [] 0

hard-limit-publishes : OwnedStep (admissionStep w₀ Server.putMapBack)
  (rejected hardLimitReached) (restored hardLimitReached)
hard-limit-publishes = certify {c = rejected hardLimitReached} {c′ = restored hardLimitReached} (admissionPublish w₀) refl (parentLease , refl , refl)

forbidden-restores : OwnedStep (admissionStep w₀ Server.restore) (rejected forbidden) (restored forbidden)
forbidden-restores = certify {c = rejected forbidden} {c′ = restored forbidden} (admissionRestore w₀) refl (parentLease , refl , refl)

fork-failure-restores : OwnedStep (admissionStep w₀ Server.restore) (rejected forkFailed) (restored forkFailed)
fork-failure-restores = certify {c = rejected forkFailed} {c′ = restored forkFailed} (admissionRestore w₀) refl (parentLease , refl , refl)

beforeTake afterTake : Configuration
beforeTake = snapshot unneg (full binding) (awaitHandshake promise₀ entry₀)
  (handling child₀) [] [] (cleanupStore cleanupAcquire)
afterTake = snapshot unneg (taken child₀) (awaitHandshake promise₀ entry₀)
  (handling child₀) [] [] (cleanupStore (cleanupSelect childLease))

cleanup-takes : OwnedStep (cleanupStep child₀ Cleanup.takeCleanupMap) beforeTake afterTake
cleanup-takes = certify {c = beforeTake} {c′ = afterTake} (cleanupTake child₀) refl refl

-- Tail parameters permit the actual captured Terminating state for TIME_WAIT.
cleanupBefore cleanupAfter : ConnectionState → ConnMap → CleanupTail → Configuration
cleanupBefore st m tail = snapshot st (taken child₀) (awaitHandshake promise₀ entry₀)
  closed [] [] (cleanupStore (cleanupPublish childLease m tail))
cleanupAfter st m tail = snapshot st (full m) (awaitHandshake promise₀ entry₀)
  closed [] [] (cleanupStore (Cleanup.afterPublish tail))

cleanup-publishes : ∀ st m tail → OwnedStep (cleanupStep child₀ Cleanup.publishCleanupMap)
  (cleanupBefore st m tail) (cleanupAfter st m tail)
cleanup-publishes st m tail = certify {c = cleanupBefore st m tail} {c′ = cleanupAfter st m tail} (cleanupPublish child₀) refl (childLease , refl , refl)

ordinary-publication : OwnedStep (cleanupStep child₀ Cleanup.publishCleanupMap)
  (cleanupBefore (terminated nothing) [] countImmediately)
  (cleanupAfter (terminated nothing) [] countImmediately)
ordinary-publication = cleanup-publishes (terminated nothing) [] countImmediately

private
  terminatingState = terminating key₀ child₀ nothing
  waitingTail = timeWait terminatingState

time-wait-publication : OwnedStep (cleanupStep child₀ Cleanup.publishCleanupMap)
  (cleanupBefore terminatingState binding waitingTail)
  (cleanupAfter terminatingState binding waitingTail)
time-wait-publication = cleanup-publishes terminatingState binding waitingTail

beforeRestore afterRestore : Configuration
beforeRestore = snapshot (terminated nothing) (taken child₀) (awaitHandshake promise₀ entry₀)
  (closeUncertain (errorId 0)) [] [] (cleanupStore (cleanupRestore childLease (errorId 0)))
afterRestore = snapshot (terminated nothing) (full binding) (awaitHandshake promise₀ entry₀)
  (closeUncertain (errorId 0)) [] [] (cleanupStore (cleanupDone (cleanupError (errorId 0))))

cleanup-restores : OwnedStep (cleanupStep child₀ Cleanup.restoreCleanupMap) beforeRestore afterRestore
cleanup-restores = certify {c = beforeRestore} {c′ = afterRestore} (cleanupRestore child₀) refl (childLease , refl , refl)

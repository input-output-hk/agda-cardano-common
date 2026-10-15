{-# OPTIONS --guardedness #-}

-- Concrete CSP traces and refusals assembled from small checked machine steps.
-- Handler publication/exit are environment assumptions, not source-reachability proofs.
module ConnectionManagement.CSP.Scenarios where

open import Data.List using (List; []; _∷_; _++_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Process_Trees
open import ConnectionManagement.Domain
open import ConnectionManagement.State
open import ConnectionManagement.Machine
open import ConnectionManagement.CSP.Process
open import ConnectionManagement.CSP.Correspondence
open import ConnectionManagement.CSP.Hiding
open import ConnectionManagement.CSP.Scope
open import ConnectionManagement.CSP.Fixtures
import ConnectionManagement.Rules.Server as Server
import ConnectionManagement.Rules.Handshake as Handshake
import ConnectionManagement.Rules.Cleanup as Cleanup
open import ConnectionManagement.Scenarios.Admission using (w₀; w₁; child₀)
open import ConnectionManagement.Scenarios.Handshake using (success; info; resultPC)
open import Semantics.LTS {E = Channel} {I = ExtI Channel}
open import Semantics.Failures {E = Channel} {I = ExtI Channel} using (traces; failures)

notificationActions : List Action
notificationActions = handshakeStep w₀ Handshake.readResultCounters ∷
  handshakeStep w₀ Handshake.enqueueInbound ∷ handshakeStep w₀ Handshake.returnResult ∷ []

raceEnd : Configuration
raceEnd = snapshot (terminated nothing) (full []) (completedHandshake (connected info)) closed
  resultStore (info ∷ []) (cleanupStore (cleanupDone cleanupNormal))

notification-path : Executes (cleaned (countHandshake (connected info))) notificationActions raceEnd
notification-path = next {c₁ = n₁} refl (next {c₁ = n₂} refl (next {c₁ = raceEnd} refl done))
  where
  n₁ = snapshot (terminated nothing) (full []) (notifyInbound info) closed resultStore []
    (cleanupStore (cleanupDone cleanupNormal))
  n₂ = snapshot (terminated nothing) (full []) (returnHandshake (connected info)) closed resultStore (info ∷ [])
    (cleanupStore (cleanupDone cleanupNormal))

race : List Action
race = admit ++ (handlerPublication child₀ success resultWritten ∷ []) ++
  consume ++ cleanupActions ++ notificationActions

race-path : Executes start race raceEnd
race-path = exec-append admit-path (exec-append publication-path (exec-append consume-path
  (exec-append (cleanup-path idle (countHandshake (connected info)) refl) notification-path)))

race-trace : traces (Process start) (map label race)
race-trace = trace-intro {c = start} {as = race} {c′ = raceEnd} race-path

race-hidden-trace : traces (HiddenProcess start) (map label (project race))
race-hidden-trace = hidden-trace {c = start} {as = race} {c′ = raceEnd} race-path

race-keeps-notification : inboundInfo (world raceEnd) ≡ newConnection info ∷ []
race-keeps-notification = refl

race-has-no-binding : mapCell (cm (world raceEnd)) ≡ full []
race-has-no-binding = refl

race-returned-connected : resultPC (world raceEnd) ≡ just (completedHandshake (connected info))
race-returned-connected = refl

race-observations : project race ≡
  admissionStep w₀ Server.fork ∷ handlerPublication child₀ success resultWritten ∷
  handlerExit child₀ ∷ cleanupStep child₀ Cleanup.closeHandlerSocket ∷
  handshakeStep w₀ Handshake.returnResult ∷ []
race-observations = refl

-- Same publication but cleanup before consumption returns Disconnected.
disconnectActions : List Action
disconnectActions = consume ++ (handshakeStep w₀ Handshake.readResultCounters ∷ handshakeStep w₀ Handshake.returnResult ∷ [])

cleanupFirstEnd : Configuration
cleanupFirstEnd = cleaned (completedHandshake (disconnected (inTerminated nothing)))

disconnect-path : Executes (cleaned (awaitHandshake promise₀ entry₀)) disconnectActions cleanupFirstEnd
disconnect-path = next {c₁ = d₁} refl (next {c₁ = d₂} refl (next {c₁ = d₃} refl
  (next {c₁ = cleanupFirstEnd} refl done)))
  where
  d₁ = cleaned (commitHandshake entry₀ success)
  d₂ = cleaned (countHandshake (disconnected (inTerminated nothing)))
  d₃ = cleaned (returnHandshake (disconnected (inTerminated nothing)))

cleanupFirst : List Action
cleanupFirst = admit ++ (handlerPublication child₀ success resultWritten ∷ []) ++ cleanupActions ++ disconnectActions

cleanup-first-path : Executes start cleanupFirst cleanupFirstEnd
cleanup-first-path = exec-append admit-path (exec-append publication-path
  (exec-append (cleanup-path unneg (awaitHandshake promise₀ entry₀) refl) disconnect-path))

cleanup-first-trace : traces (Process start) (map label cleanupFirst)
cleanup-first-trace = trace-intro {c = start} {as = cleanupFirst} {c′ = cleanupFirstEnd} cleanup-first-path

cleanup-first-disconnects : resultPC (world cleanupFirstEnd) ≡
  just (completedHandshake (disconnected (inTerminated nothing)))
cleanup-first-disconnects = refl

-- Close has completed but map publication has not: a real blocking point.
lockActions : List Action
lockActions = handlerExit child₀ ∷ cleanupStep child₀ Cleanup.takeCleanupMap ∷
  cleanupStep child₀ Cleanup.selectCleanupEntry ∷ cleanupStep child₀ Cleanup.closeHandlerSocket ∷ []

lockEnd : Configuration
lockEnd = snapshot (terminated nothing) (taken child₀) (awaitHandshake promise₀ entry₀) closed [] []
  (cleanupStore (cleanupPublish childLease [] countImmediately))

lock-path : Executes waiting lockActions lockEnd
lock-path = next {c₁ = l₁} refl (next {c₁ = l₂} refl (next {c₁ = l₃} refl (next {c₁ = lockEnd} refl done)))
  where
  l₁ = snapshot unneg (full binding) (awaitHandshake promise₀ entry₀) (handling child₀) [] [] (cleanupStore cleanupAcquire)
  l₂ = snapshot unneg (taken child₀) (awaitHandshake promise₀ entry₀) (handling child₀) [] [] (cleanupStore (cleanupSelect childLease))
  l₃ = snapshot (terminated nothing) (taken child₀) (awaitHandshake promise₀ entry₀) (handling child₀) [] []
    (cleanupStore (cleanupClose childLease [] countImmediately))

lockTrace : List Action
lockTrace = admit ++ lockActions

lock-trace-path : Executes start lockTrace lockEnd
lock-trace-path = exec-append admit-path lock-path

competingTake : Action
competingTake = admissionStep w₁ Server.take

take-is-refused : advance competingTake lockEnd ≡ nothing
take-is-refused = refl

lock-failure : failures (Process start) (map label lockTrace) (λ e → e ≡ label competingTake)
lock-failure = Process lockEnd , exec-intro {c = start} {as = lockTrace} {c′ = lockEnd} lock-trace-path ,
  singleton-refusal {c = lockEnd} {a = competingTake} take-is-refused

-- Non-vacuity: this singleton refusal is not a global deadlock. The owner can
-- still publish its proposed map in the same raw process state.
publishedAfterLock : Configuration
publishedAfterLock = snapshot (terminated nothing) (full []) (awaitHandshake promise₀ entry₀) closed [] []
  (cleanupStore (cleanupCount cleanupNormal))

lock-still-progresses : Process lockEnd ─[ ev (label (cleanupStep child₀ Cleanup.publishCleanupMap)) ]─►
  Process publishedAfterLock
lock-still-progresses = step-intro {c = lockEnd} {c′ = publishedAfterLock}
  {a = cleanupStep child₀ Cleanup.publishCleanupMap} refl

badTrace : List Action
badTrace = lockTrace ++ (competingTake ∷ [])

bad-trace-excluded : ¬ traces (Process start) (map label badTrace)
bad-trace-excluded = refused-extension {c = start} {as = lockTrace} {c′ = lockEnd} {a = competingTake}
  lock-trace-path take-is-refused

-- Missing-continuation diagnostics do not create process transitions.
at-server-frontier : admissionFrontier (completedHandshake (connected info)) ≡ just serverReturn
at-server-frontier = refl
-- The queued notification now has an implemented IG continuation.
IG-prefix-available : igFrontier (inboundGovernor raceEnd) ≡ nothing
IG-prefix-available = refl

-- Duplicate publication is recorded once, not dropped and not a self-loop.
duplicateEnd : Configuration
duplicateEnd = record published { publicationFaults = child₀ ∷ [] }

duplicateTrace : List Action
duplicateTrace = admit ++ (handlerPublication child₀ success resultWritten ∷ handlerPublication child₀ query duplicateWrite ∷ [])

duplicate-path : Executes start duplicateTrace duplicateEnd
duplicate-path = exec-append admit-path (next {c₁ = published} refl (next {c₁ = duplicateEnd} refl done))

duplicate-is-a-trace : traces (Process start) (map label duplicateTrace)
duplicate-is-a-trace = trace-intro {c = start} {as = duplicateTrace} {c′ = duplicateEnd} duplicate-path

duplicate-recorded : publicationFaults duplicateEnd ≡ child₀ ∷ []
duplicate-recorded = refl
no-repeat-publication-fault : advance (handlerPublication child₀ query duplicateWrite) duplicateEnd ≡ nothing
no-repeat-publication-fault = refl

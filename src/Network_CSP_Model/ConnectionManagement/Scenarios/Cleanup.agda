{-# OPTIONS --guardedness #-}

-- Handler-exit and timeout events are environment assumptions, not a proof of
-- source reachability. State injections are explicitly marked branch fixtures.
module ConnectionManagement.Scenarios.Cleanup where

open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing; map)
open import Data.Product using (_,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Rules.Cleanup
open import ConnectionManagement.Rules.Handshake using
  (stepHandshake; publishBoundary; readResult; commitResult; readResultCounters; enqueueInbound; returnResult)
import ConnectionManagement.Rules.Server as Server
open import ConnectionManagement.Scenarios.Admission using
  (fixture; emptyCM; w₀; w₁; child₀; key₀; runPrefix)
open import ConnectionManagement.Scenarios.Handshake using
  (bind; waiting; success; info; deliver; resume; resultPC; runHandshake; failureActions)
open import ConnectionManagement.Properties.Cleanup using
  (purge-stale; purge-absent; selection-preserves-map-cell;
   selection-preserves-references; finalizer-waits-atomically)

runCleanup : List CleanupAction → State → Maybe State
runCleanup [] s = just s
runCleanup (a ∷ as) s = bind (stepCleanup child₀ a s) (runCleanup as)

start : Maybe State → Maybe State
start s = bind s (beginCleanupBoundary child₀)

closeActions : List CleanupAction
closeActions = takeCleanupMap ∷ selectCleanupEntry ∷ closeHandlerSocket ∷ publishCleanupMap ∷ []

ordinaryActions : List CleanupAction
ordinaryActions = takeCleanupMap ∷ selectCleanupEntry ∷ closeHandlerSocket ∷ publishCleanupMap ∷ readCleanupCounters ∷ []

ordinary : Maybe State
ordinary = bind (start waiting) (runCleanup ordinaryActions)

ordinary-removes-binding : map (λ s → mapCell (cm s)) ordinary ≡ just (full [])
ordinary-removes-binding = refl

ordinary-terminates-entry : map (λ s → lookup (ident 0) (entries (cm s))) ordinary
  ≡ just (just (terminated nothing))
ordinary-terminates-entry = refl

ordinary-closes-socket : map (λ s → lookup (ident 0) (sockets s)) ordinary ≡ just (just closed)
ordinary-closes-socket = refl

ordinary-completes : map (λ s → lookup child₀ (cleanups s)) ordinary
  ≡ just (just (cleanupDone cleanupNormal))
ordinary-completes = refl

-- Handler return cannot write a result later, and cleanup cannot restart.
no-publication-after-exit : bind ordinary (publishBoundary child₀ success) ≡ nothing
no-publication-after-exit = refl

no-second-cleanup : start ordinary ≡ nothing
no-second-cleanup = refl

cleanup-does-not-fill-promise : map handshakeResults ordinary ≡ just []
cleanup-does-not-fill-promise = refl

consumer-still-waits-without-result :
  bind ordinary (stepHandshake responderMode w₀ readResult) ≡ nothing
consumer-still-waits-without-result = refl

-- The accepted handler can exit before the admission caller puts back the map.
forked : Maybe State
forked = runPrefix ((w₀ , Server.take) ∷ (w₀ , Server.countLimit) ∷
  (w₀ , Server.allocatePromise) ∷ (w₀ , Server.chooseEntry) ∷ (w₀ , Server.fork) ∷ [])
  (fixture emptyCM)

cleanup-waits-for-parent-map :
  bind (start forked) (stepCleanup child₀ takeCleanupMap) ≡ nothing
cleanup-waits-for-parent-map = refl

closedBeforePublish : Maybe State
closedBeforePublish = bind (start waiting)
  (runCleanup (takeCleanupMap ∷ selectCleanupEntry ∷ closeHandlerSocket ∷ []))

close-keeps-map-owned : map (λ s → mapCell (cm s)) closedBeforePublish ≡ just (taken child₀)
close-keeps-map-owned = refl

second-caller-cannot-take-during-close : bind closedBeforePublish (Server.stepPrefix w₁ Server.take) ≡ nothing
second-caller-cannot-take-during-close = refl

-- Consumer reads an already-published result after the child has cleaned up.
cleanedWithResult : Maybe State
cleanedWithResult = bind (start (bind waiting (deliver success))) (runCleanup ordinaryActions)

cleanup-before-consume-disconnects :
  map resultPC (bind cleanedWithResult (runHandshake responderMode failureActions))
  ≡ just (just (completedHandshake (disconnected (inTerminated nothing))))
cleanup-before-consume-disconnects = refl

-- Conversely, a successful entry decision is captured before cleanup; later
-- counters do not revalidate it. IG must handle a possibly finished handle.
cleanupAfterDecision : Maybe State
cleanupAfterDecision = bind
  (start (resume success responderMode (readResult ∷ commitResult ∷ [])))
  (runCleanup ordinaryActions)

notification-can-follow-cleanup :
  map inboundInfo (bind cleanupAfterDecision
    (runHandshake responderMode (readResultCounters ∷ enqueueInbound ∷ returnResult ∷ [])))
  ≡ just (newConnection info ∷ [])
notification-can-follow-cleanup = refl

-- Negotiation failure supplies a Terminating entry through implemented consumer
-- rules; cleanup must close first, publish its map, then wait.
terminatingStart : Maybe State
terminatingStart = start (resume (handlerError negotiationFailure (errorId 7)) responderMode failureActions)

waitingTimeWait : Maybe State
waitingTimeWait = bind terminatingStart (runCleanup closeActions)

time-wait-keeps-terminating : map (λ s → lookup (ident 0) (entries (cm s))) waitingTimeWait
  ≡ just (just (terminating key₀ child₀ (just (errorId 7))))
time-wait-keeps-terminating = refl

time-wait-starts-after-close : map (λ s → lookup (ident 0) (sockets s)) waitingTimeWait ≡ just (just closed)
time-wait-starts-after-close = refl

cannot-finalize-before-readiness : bind waitingTimeWait (stepCleanup child₀ finishTimeWait) ≡ nothing
cannot-finalize-before-readiness = refl

elapsed : Maybe State
elapsed = bind waitingTimeWait (runCleanup (timeWaitElapsed ∷ finishTimeWait ∷ readCleanupCounters ∷ []))

elapsed-terminates : map (λ s → lookup (ident 0) (entries (cm s))) elapsed
  ≡ just (just (terminated nothing))
elapsed-terminates = refl

interrupted : Maybe State
interrupted = bind waitingTimeWait (runCleanup
  (interruptTimeWait (errorId 9) ∷ finishTimeWait ∷ readCleanupCounters ∷ []))

interruption-still-terminates : map (λ s → lookup (ident 0) (entries (cm s))) interrupted
  ≡ just (just (terminated nothing))
interruption-still-terminates = refl

interruption-propagates-after-finalizer : map (λ s → lookup child₀ (cleanups s)) interrupted
  ≡ just (just (cleanupDone (cleanupError (errorId 9))))
interruption-propagates-after-finalizer = refl

-- Real second-caller take makes the finalizer block. STM does not expose an
-- early entry write while waiting for the map.
blockedFinalizer : Maybe State
blockedFinalizer = bind
  (bind waitingTimeWait (stepCleanup child₀ timeWaitElapsed))
  (Server.stepPrefix w₁ Server.take)

finalizer-blocked : bind blockedFinalizer (stepCleanup child₀ finishTimeWait) ≡ nothing
finalizer-blocked = refl

blocked-entry-still-terminating : map (λ s → lookup (ident 0) (entries (cm s))) blockedFinalizer
  ≡ just (just (terminating key₀ child₀ (just (errorId 7))))
blocked-entry-still-terminating = refl

-- Close failure restores the saved MAP but retains the committed heap update.
failedClose : Maybe State
failedClose = bind (start waiting) (runCleanup
  (takeCleanupMap ∷ selectCleanupEntry ∷ failSocketClose (errorId 3) ∷ restoreCleanupMap ∷ []))

close-failure-restores-map : map (λ s → mapCell (cm s)) failedClose
  ≡ just (full (insertConnection key₀ (ident 0) []))
close-failure-restores-map = refl

close-failure-keeps-entry-write : map (λ s → lookup (ident 0) (entries (cm s))) failedClose
  ≡ just (just (terminated nothing))
close-failure-keeps-entry-write = refl

close-failure-does-not-claim-closed : map (λ s → lookup (ident 0) (sockets s)) failedClose
  ≡ just (just (closeUncertain (errorId 3)))
close-failure-does-not-claim-closed = refl

-- Branch fixture: a replacement incarnation was installed during TIME_WAIT.
-- Allocation/outbound actions that could install it are outside this slice.
replaceDuringWait : State → State
replaceDuringWait s = record s { cm = record (cm s)
  { mapCell = full (insertConnection key₀ (ident 1) [])
  ; entries = put (ident 1) (unnegotiated inbound key₀ (ident 8)) (entries (cm s))
  ; nextEntry = 2 } }

staleFinalized : Maybe State
staleFinalized = bind (map replaceDuringWait waitingTimeWait)
  (runCleanup (timeWaitElapsed ∷ finishTimeWait ∷ readCleanupCounters ∷ []))

finalizer-retains-replacement : map (λ s → mapCell (cm s)) staleFinalized
  ≡ just (full (insertConnection key₀ (ident 1) []))
finalizer-retains-replacement = refl

finalizer-still-writes-old-entry : map (λ s → lookup (ident 0) (entries (cm s))) staleFinalized
  ≡ just (just (terminated nothing))
finalizer-still-writes-old-entry = refl

-- The immediate path also updates the captured entry even when it is unmapped.
staleImmediate : Maybe State
staleImmediate = bind (start (map replaceDuringWait waiting)) (runCleanup ordinaryActions)

immediate-retains-replacement : map (λ s → mapCell (cm s)) staleImmediate
  ≡ just (full (insertConnection key₀ (ident 1) []))
immediate-retains-replacement = refl

immediate-still-writes-old-entry : map (λ s → lookup (ident 0) (entries (cm s))) staleImmediate
  ≡ just (just (terminated nothing))
immediate-still-writes-old-entry = refl

-- Already-Terminated keeps its stored error, unlike ordinary termination.
alreadyTerminated : Maybe State
alreadyTerminated = bind (start
  (resume (handlerError protocolViolation (errorId 7)) responderMode failureActions))
  (runCleanup ordinaryActions)

terminated-error-retained : map (λ s → lookup (ident 0) (entries (cm s))) alreadyTerminated
  ≡ just (just (terminated (just (errorId 7))))
terminated-error-retained = refl

-- Branch fixture: another actor changed the entry during TIME_WAIT. The finally
-- decision uses captured Terminating, so it writes even if the current entry is
-- already Terminated. A fresh-state test would incorrectly retain error 11.
terminateDuringWait : State → State
terminateDuringWait s = record s { cm = record (cm s)
  { entries = put (ident 0) (terminated (just (errorId 11))) (entries (cm s)) } }

finalizer-uses-captured-state :
  map (λ s → lookup (ident 0) (entries (cm s)))
    (bind (map terminateDuringWait waitingTimeWait)
      (runCleanup (timeWaitElapsed ∷ finishTimeWait ∷ [])))
  ≡ just (just (terminated nothing))
finalizer-uses-captured-state = refl

-- Different worker is not different entry identity. Preserve this distinction
-- for future overlap scenarios; this injected state is not a reachability claim.
overwriteSameEntryDuringWait : State → State
overwriteSameEntryDuringWait s = record s { cm = record (cm s)
  { mapCell = full (insertConnection key₀ (ident 0) [])
  ; entries = put (ident 0) (unnegotiated inbound key₀ (ident 8)) (entries (cm s)) } }

same-entry-worker-change-does-not-protect-binding :
  map (λ s → mapCell (cm s))
    (bind (map overwriteSameEntryDuringWait waitingTimeWait)
      (runCleanup (timeWaitElapsed ∷ finishTimeWait ∷ []))) ≡ just (full [])
same-entry-worker-change-does-not-protect-binding = refl

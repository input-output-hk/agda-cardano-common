{-# OPTIONS --guardedness #-}

-- Core.hs:592-713 at network 96ee6e0e689770b5a3d664c59f2d13b05c5d9c4d.
-- Explicit handler-exit boundary; no model of the preceding mux/handler body.
module ConnectionManagement.Rules.Cleanup where

open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Rules.CM using (takeMap; putMap; restoreMap)

-- Deletion is identity guarded; a captured-entry write is a separate decision.
purgeCaptured : ConnectionKey → EntryId → ConnMap → ConnMap
purgeCaptured k e m with lookupConnection k m
... | nothing = m
... | just current with e ≟ current
...   | no _ = m
...   | yes _ = deleteConnection k m

-- The sole deferred branch is Terminating. Already-Terminated retains its error.
data CleanupDecision : Set where
  terminateAndPurge purgeOnly : CleanupDecision
  waitBeforePurge : ConnectionState → CleanupDecision

decideCleanup : ConnectionState → CleanupDecision
decideCleanup reservedOutbound = terminateAndPurge
decideCleanup (unnegotiated _ _ _) = terminateAndPurge
decideCleanup (outboundUni _ _ _) = terminateAndPurge
decideCleanup (outboundDup _ _ _ _) = terminateAndPurge
decideCleanup (outboundIdle _ _ _ _) = terminateAndPurge
decideCleanup (inboundIdle _ _ _ _) = terminateAndPurge
decideCleanup (inboundActive _ _ _ _) = terminateAndPurge
decideCleanup (duplexActive _ _ _) = terminateAndPurge
decideCleanup st@(terminating _ _ _) = waitBeforePurge st
decideCleanup (terminated _) = purgeOnly

setCleanup : WorkerId → CleanupPC → State → State
setCleanup w p s = record s { cleanups = put w p (cleanups s) }

-- Abstract entrance to finally; not enabled by a reconstructed entry WorkerId.
-- The original handler registration supplies captured key, entry and socket.
beginCleanupBoundary : WorkerId → State → Maybe State
beginCleanupBoundary w s with lookup w (handlers s) | lookup w (cleanups s)
... | just _ | nothing = just (setCleanup w cleanupAcquire s)
... | _ | _ = nothing

selectCleanup : WorkerId → HandlerStart → Lease → CleanupDecision → State → State
selectCleanup w h l terminateAndPurge s =
  setCleanup w (cleanupClose l (purgeCaptured (handlerKey h) (handlerEntry h) (savedMap l)) countImmediately)
    (record s { cm = record (cm s)
      { entries = put (handlerEntry h) (terminated nothing) (entries (cm s)) } })
selectCleanup w h l purgeOnly s =
  setCleanup w (cleanupClose l (purgeCaptured (handlerKey h) (handlerEntry h) (savedMap l)) countImmediately) s
selectCleanup w h l (waitBeforePurge st) s =
  setCleanup w (cleanupClose l (savedMap l) (timeWait st)) s

afterPublish : CleanupTail → CleanupPC
afterPublish countImmediately = cleanupCount cleanupNormal
afterPublish (timeWait st) = cleanupWaiting st

-- TIME_WAIT's captured state is always Terminating in a valid run. Model the
-- source's captured-state abstract-state comparison, not a fresh entry read.
finishEntry : EntryId → ConnectionState → EntryHeap → EntryHeap
finishEntry e (terminated _) heap = heap
finishEntry e _ heap = put e (terminated nothing) heap

data CleanupAction : Set where
  takeCleanupMap selectCleanupEntry closeHandlerSocket publishCleanupMap
    restoreCleanupMap readCleanupCounters finishTimeWait : CleanupAction
  failSocketClose : ErrorId → CleanupAction
  timeWaitElapsed : CleanupAction
  interruptTimeWait : ErrorId → CleanupAction

stepWorker : WorkerId → HandlerStart → CleanupPC → CleanupAction → State → Maybe State
stepWorker w h cleanupAcquire takeCleanupMap s with takeMap w (cm s)
... | nothing = nothing
... | just (l , c) = just (setCleanup w (cleanupSelect l) (record s { cm = c }))
stepWorker w h (cleanupSelect l) selectCleanupEntry s with mapCell (cm s)
... | full _ = nothing
... | taken owner with owner ≟ w
...   | no _ = nothing
...   | yes _ with lookup (handlerEntry h) (entries (cm s))
...     | nothing = nothing -- malformed captured reference
...     | just st = just (selectCleanup w h l (decideCleanup st) s)

-- Closing is IO inside modifyTMVar: the global map is still taken here.
stepWorker w h (cleanupClose l m tail) closeHandlerSocket s =
  just (setCleanup w (cleanupPublish l m tail)
    (record s { sockets = put (handlerSocket h) closed (sockets s) }))
stepWorker w h (cleanupClose l m tail) (failSocketClose err) s =
  just (setCleanup w (cleanupRestore l err)
    (record s { sockets = put (handlerSocket h) (closeUncertain err) (sockets s) }))
stepWorker w h (cleanupPublish l m tail) publishCleanupMap s with putMap l m (cm s)
... | nothing = nothing
... | just c = just (setCleanup w (afterPublish tail) (record s { cm = c }))
stepWorker w h (cleanupRestore l err) restoreCleanupMap s with restoreMap l (cm s)
... | nothing = nothing
... | just c = just (setCleanup w (cleanupDone (cleanupError err)) (record s { cm = c }))

-- Untimed readiness events. Interruption enters the same finally transaction;
-- it does not skip entry termination or deletion before propagating the error.
stepWorker w h (cleanupWaiting captured) timeWaitElapsed s =
  just (setCleanup w (cleanupFinalize captured cleanupNormal) s)
stepWorker w h (cleanupWaiting captured) (interruptTimeWait err) s =
  just (setCleanup w (cleanupFinalize captured (cleanupError err)) s)
stepWorker w h (cleanupFinalize captured outcome) finishTimeWait s with mapCell (cm s)
... | taken _ = nothing
... | full m with lookup (handlerEntry h) (entries (cm s))
...   | nothing = nothing -- malformed captured reference
...   | just _ = just (setCleanup w (cleanupCount outcome)
      (record s { cm = record (cm s)
        { mapCell = full (purgeCaptured (handlerKey h) (handlerEntry h) m)
        ; entries = finishEntry (handlerEntry h) captured (entries (cm s)) } }))

stepWorker w h (cleanupCount outcome) readCleanupCounters s with mapCell (cm s)
... | taken _ = nothing
... | full m with countIncoming (entries (cm s)) m
...   | nothing = nothing
...   | just _ = just (setCleanup w (cleanupDone outcome) s)
stepWorker w h p act s = nothing

stepCleanup : WorkerId → CleanupAction → State → Maybe State
stepCleanup w act s with lookup w (handlers s) | lookup w (cleanups s)
... | just h | just p = stepWorker w h p act s
... | _ | _ = nothing

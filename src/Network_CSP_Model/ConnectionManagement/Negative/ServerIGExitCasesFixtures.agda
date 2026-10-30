{-# OPTIONS --guardedness #-}

-- Data snapshots for selected initialized CM receipts and one-row finalizers.
-- Callback completion has a separate proof; these builders supply no traces.
module ConnectionManagement.Negative.ServerIGExitCasesFixtures where

open import Data.Bool using (false)
open import Data.List using (List; []; _∷_; take; drop)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (put)
import ConnectionManagement.State as Shared
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.RemoteState as Remote
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerIGExitFixtures as X
import ConnectionManagement.Negative.ServerIGExitProtocolFixtures as Y
import ConnectionManagement.Scenarios.Admission as A
private
  module E = Exit I.bearerClosed
  module S = Server I.bearerClosed
module F = Y.F

-- A different admitted worker owns the map. These CM callers only read it.
lock : Y.Model → Y.Model
lock m = record m { world = record (Y.world m)
  { cm = record (Shared.cm (Y.world m)) { mapCell = Shared.taken A.w₁ }
  ; admissions = put A.w₁ (Shared.admissionWorker F.r₁ (Shared.count F.lease₁)) (Shared.admissions (Y.world m)) } }
beforePromotion afterPromotion : Y.Model
beforePromotion = lock Y.g5
afterPromotion = lock Y.g7
pre post demote body : E.Receipt
pre = E.receipt E.promoteRead X.err (just (E.remoteCall Y.promoteFrame))
post = E.receipt E.promoteCounters X.err (just (E.remoteCall (record Y.promotedFrame { pc = Remote.counters })))
demote = E.receipt E.demoteBoundary X.err (just (E.remoteCall Y.demotedFrame))
body = E.receipt E.loopBoundary X.err nothing

-- Clearing local cursors preserves the actual committed shared world.
clear : Y.Model → Y.Model
clear m = record m { cmRelease = nothing; cmRemote = nothing }
inactiveModel : Y.Model → Y.Model
inactiveModel m = record (clear m) { governor = record (Y.governor m)
  { continuation = IG.exitFlush; execution = record (IG.execution (Y.governor m)) { active = false } } }
flushedModel : Y.Model → Y.Model
flushedModel m = record (inactiveModel m)
  { world = record (Y.world m) { inboundInfo = [] }
  ; governor = record (Y.governor (inactiveModel m)) { continuation = IG.exited } }
state : Y.Model → S.Stage → E.Exit → E.State
state m pc e = E.igExitState (record (E.base (Y.render m)) { stage = pc; listenerOpen = false }) e
caught inactive flushed : E.Receipt → Y.Model → E.State
caught r m = state (clear m) S.igCancelDelivered (E.caughtExit r)
inactive r m = state (inactiveModel m) S.igInactive (E.caughtExit r)
flushed r m = state (flushedModel m) S.igFlushed (E.caughtExit r)
rows : Y.Model → List E.Row
rows m = E.snapshotRows (IG.connections (IG.publishedState (Y.governor m)))
snapshotExit : E.Receipt → Y.Model → E.Exit
snapshotExit r m = record (E.caughtExit r) { phase = E.traversing; snapshot = rows m; remaining = rows m }
snapshot invoked returned done published joined : E.Receipt → Y.Model → E.State
snapshot r m = state (flushedModel m) S.igFlushed (snapshotExit r m)
invoked r m = state (flushedModel m) S.igFlushed (record (snapshotExit r m) { phase = E.invoked })
returned r m = state (flushedModel m) S.igFlushed
  (record (snapshotExit r m) { remaining = drop 1 (rows m); returned = take 1 (rows m) })
done r m = record (returned r m) { base = record (E.base (returned r m)) { stage = S.igBodyExited }
  ; exit = record (E.exit (returned r m)) { phase = E.bodyDone } }
published r m = record (done r m) { base = record (E.base (done r m)) { stage = S.igResultAvailable }
  ; exit = record (E.exit (done r m)) { result = just (S.async (E.exception r)) } }
joined r m = record (published r m) { base = record (E.base (published r m)) { stage = S.igJoined } }

-- A mux callback sampled Active=True before catch entry can enqueue AFTER the
-- one source drain. It changes neither the published snapshot nor the outcome.
lateModel : Y.Model
lateModel = Y.sourceMux Y.m4 Y.messages (flushedModel Y.a3)
late : E.State
late = state lateModel S.igFlushed (E.caughtExit body)
lateSnapshot lateInvoked lateReturned lateDone latePublished lateJoined : E.State
lateSnapshot = state lateModel S.igFlushed (snapshotExit body Y.a3)
lateInvoked = state lateModel S.igFlushed (record (snapshotExit body Y.a3) { phase = E.invoked })
lateReturned = state lateModel S.igFlushed (record (snapshotExit body Y.a3) { remaining = []; returned = rows Y.a3 })
lateDone = record lateReturned { base = record (E.base lateReturned) { stage = S.igBodyExited }
  ; exit = record (E.exit lateReturned) { phase = E.bodyDone } }
latePublished = record lateDone { base = record (E.base lateDone) { stage = S.igResultAvailable }
  ; exit = record (E.exit lateDone) { result = just (S.async X.err) } }
lateJoined = record latePublished { base = record (E.base latePublished) { stage = S.igJoined } }

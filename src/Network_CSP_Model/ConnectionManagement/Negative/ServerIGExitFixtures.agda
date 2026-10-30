{-# OPTIONS --guardedness #-}

-- Flat data snapshots for actual inbound birth, successful handshake and IG
-- registration. Prefix proofs live separately; no failed-step/default driver.
module ConnectionManagement.Negative.ServerIGExitFixtures where

open import Data.Bool using (Bool; true; false)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.ServerIGExit as Exit
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Negative.ServerAdmissionPrefixFixtures as Prefix
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.InboundRelease as Release
import ConnectionManagement.Rules.RemoteState as Remote
private
  module S = Server I.bearerClosed
  module E = Exit I.bearerClosed
  module N = Publication I.bearerClosed
  module P = N.P
  module U = N.U
  module Startup = N.S
  module Pool = P.Pool
module F = Prefix 10 A.key₁

wrap : S.State → E.State
wrap server = E.igExitState server E.emptyExit
start admitted : E.State
start = wrap F.start
admitted = wrap F.s11

-- One update from the fixed admitted source avoids growing projection chains.
registeredState : IG.Published
registeredState = IG.published ((A.key₀ , IG.registered F.info (ident 1)) ∷ [])
  ((remote A.key₀ , IG.freshPeer 10 (ident 0)) ∷ [])
newMux armedMux : Mux.Mux
newMux = Mux.muxState A.key₀ Mux.ready ((1 , Mux.idle) ∷ []) [] [] [] [] []
  (IG.initialCounters Mux.igTracer) Mux.returned Mux.igTracer
armedMux = record newMux { protocols = (1 , Mux.demand) ∷ []; commands = Mux.startCommand (IG.protocol 1 IG.hot IG.onDemand) ∷ [] }
e₀ e₁ e₂ e₃ e₄ : IG.Engine
e₀ = IG.execution F.allocatedIG
e₁ = record e₀ { lastTime = 10 }
e₂ = record e₁ { timers = (ident 0 , ticking) ∷ [] }
e₃ = record e₂ { timers = (ident 0 , ticking) ∷ (ident 1 , ticking) ∷ [] }
e₄ = record e₃ { muxes = (ident 0 , armedMux) ∷ [] }
at : Shared.State → IG.Runtime → E.State
at world ig = wrap (S.setSource (record (S.source F.s11)
  { core = record (O.core (S.source F.s11)) { world = world; inboundGovernor = ig } }) F.s11)
withIG : IG.Runtime → List Shared.IGEvent → E.State
withIG ig queue = at (record (S.shared F.s11) { inboundInfo = queue }) ig
g1 g2 g3 g4 g5 g6 g7 : E.State
g1 = withIG (IG.runtimeState IG.emptyPublished 0 (IG.armInactivity 10) e₁) (Shared.newConnection F.info ∷ [])
g2 = withIG (IG.runtimeState IG.emptyPublished 1 (IG.awaitBatch 10 (ident 0)) e₂) (Shared.newConnection F.info ∷ [])
g3 = withIG (IG.runtimeState IG.emptyPublished 1 (IG.readNext 10 (Shared.newConnection F.info ∷ [])) e₂) []
g4 = withIG (IG.runtimeState IG.emptyPublished 1 (IG.prepareNew 10 F.info [] IG.emptyPublished) e₂) []
g5 = withIG (IG.runtimeState IG.emptyPublished 2 (IG.startResponders 10 F.info [] IG.emptyPublished (ident 1)) e₃) []
g6 = withIG (IG.runtimeState registeredState 2 (IG.readNext 10 []) e₄) []
g7 = withIG (IG.runtimeState registeredState 2 IG.sampleTime e₄) []

-- An idle timeout enters the real caller-run release operation.
releaseEngine armedEngine expiredEngine : IG.Engine
releaseEngine = record e₄ { lastTime = 11 }
armedEngine = record releaseEngine { timers = (ident 0 , ticking) ∷ (ident 1 , ticking) ∷ (ident 2 , ticking) ∷ [] }
expiredEngine = record armedEngine { timers = (ident 0 , ticking) ∷ (ident 1 , expired) ∷ (ident 2 , ticking) ∷ [] }
r1 r2 r3 r4 r5 r6 r7 : E.State
r1 = withIG (IG.runtimeState registeredState 2 (IG.armInactivity 11) releaseEngine) []
r2 = withIG (IG.runtimeState registeredState 3 (IG.awaitBatch 11 (ident 2)) armedEngine) []
r3 = withIG (IG.runtimeState registeredState 3 (IG.awaitBatch 11 (ident 2)) expiredEngine) []
r4 = withIG (IG.runtimeState registeredState 3 (IG.readNext 11 (Shared.commitRemote A.key₀ ∷ [])) expiredEngine) []
r5 = withIG (IG.runtimeState registeredState 3 (IG.needsCM 11 [] (Shared.commitRemote A.key₀) registeredState) expiredEngine) []
releaseFrame writtenFrame : Release.Frame
releaseFrame = Release.frame A.key₀ 11 [] registeredState Release.transaction Release.commit nothing false
writtenFrame = record releaseFrame { pc = Release.counters; target = just A.child₀ }
releaseAt : Release.Frame → Shared.State → E.State
releaseAt capturedCall world = E.igExitState (S.setSource (record (S.source F.s11)
  { core = record (O.core (S.source F.s11)) { world = world
    ; inboundGovernor = IG.runtimeState registeredState 3 IG.inCM expiredEngine
    ; inboundRelease = just capturedCall } }) F.s11) E.emptyExit
r6 = releaseAt releaseFrame (record (S.shared F.s11) { inboundInfo = [] })
writtenWorld : Shared.State
writtenWorld = record (S.shared F.s11) { inboundInfo = []; cm = Shared.cmStore (Shared.full F.binding)
  ((ident 0 , Shared.terminating A.key₀ A.child₀ nothing) ∷ []) 1 }
r7 = releaseAt writtenFrame writtenWorld
heldWorld : Shared.State
heldWorld = record writtenWorld
  { cm = record (Shared.cm writtenWorld) { mapCell = Shared.taken A.w₁ }
  ; admissions = put A.w₁ (Shared.admissionWorker F.r₁ (Shared.count F.lease₁)) (Shared.admissions writtenWorld) }
held : E.State
held = releaseAt writtenFrame heldWorld

-- The normal owned-scope prefix ends at an actual pending IG cancellation.
atScope : S.Stage → Bool → E.State → E.State
atScope pc listener s = record s { base = record (E.base s) { stage = pc; listenerOpen = listener } }
err : ErrorId
err = errorId 140
receivedRelease : E.Receipt
receivedRelease = E.receipt E.releaseCounters err (just (E.releaseCall writtenFrame))
caughtRelease : E.State
caughtRelease = E.igExitState
  (record (S.setSource (E.clearPending (E.source held)) (E.base held)) { stage = S.igCancelDelivered; listenerOpen = false })
  (E.caughtExit receivedRelease)
inactiveIG flushedIG : IG.Runtime
inactiveIG = IG.runtimeState registeredState 3 IG.exitFlush (record expiredEngine { active = false })
flushedIG = record inactiveIG { continuation = IG.exited }
afterUnwind : IG.Runtime → S.Stage → E.State
afterUnwind ig pc = E.igExitState
  (record (S.setSource (record (S.source F.s11)
    { core = record (O.core (S.source F.s11)) { world = heldWorld; inboundGovernor = ig } }) F.s11)
    { stage = pc; listenerOpen = false }) (E.caughtExit receivedRelease)
inactive flushed : E.State
inactive = afterUnwind inactiveIG S.igInactive
flushed = afterUnwind flushedIG S.igFlushed

-- The public remote-state projection drops idle timers, retains the registry,
-- and records callback returns separately from invocation and Async result.
rows : List E.Row
rows = (A.key₀ , E.idle) ∷ []
snapshotExit : E.Exit
snapshotExit = record (E.caughtExit receivedRelease) { phase = E.traversing; snapshot = rows; remaining = rows }
snapshot invoked returned bodyDone published joined : E.State
snapshot = record flushed { exit = snapshotExit }
invoked = record flushed { exit = record snapshotExit { phase = E.invoked } }
returned = record flushed { exit = record snapshotExit { remaining = []; returned = rows } }
bodyDone = record returned { base = record (E.base returned) { stage = S.igBodyExited }
  ; exit = record (E.exit returned) { phase = E.bodyDone } }
published = record bodyDone { base = record (E.base bodyDone) { stage = S.igResultAvailable }
  ; exit = record (E.exit bodyDone) { result = just (S.async err) } }
joined = record published { base = record (E.base published) { stage = S.igJoined } }

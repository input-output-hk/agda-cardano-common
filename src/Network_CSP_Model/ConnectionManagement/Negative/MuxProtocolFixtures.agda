{-# OPTIONS --guardedness #-}

-- Lightweight source-data fixtures for the typed-pool acceptance endpoint.
-- The endpoint proves every actual initialized step; these builders import no
-- CSP process closure or pre-existing physical execution.
module ConnectionManagement.Negative.MuxProtocolFixtures where

open import Data.Bool using (true)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.List.Relation.Unary.All as All using ()
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import ConnectionManagement.Domain
open import ConnectionManagement.IGTypes
open import ConnectionManagement.Store using (Store; put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as M
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.Rules.OutboundAcquire as A
import ConnectionManagement.Rules.OutboundCases as Cases
import ConnectionManagement.Rules.CMShutdown as Close
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.MuxJobTypes as Types
import ConnectionManagement.MuxHandlerSupervision as Handler
module U = Handler Types.TypedResult
module Startup = U.Startup
import ConnectionManagement.Scenarios.Admission as Admission
open Admission using (key₀)
open import ConnectionManagement.Properties.SupplyBounds using (SupplyBounds)

module F where
  start : M.Configuration
  start = M.initial Shared.responderMode (Admission.fixture Admission.emptyCM)
module G where
  proto : Protocol
  proto = protocol 1 hot onDemand
  mid : MuxId
  mid = ident 0
  newMux armedMux : Mux.Mux
  newMux = Mux.muxState key₀ Mux.ready ((1 , Mux.idle) ∷ []) [] [] [] [] []
    (just (Mux.counters (+ 0) (+ 0))) Mux.returned Mux.igTracer
  armedMux = record newMux { protocols = (1 , Mux.demand) ∷ []; commands = Mux.startCommand proto ∷ [] }
  installedIG : IG.Runtime
  installedIG = IG.runtimeState IG.emptyPublished 0 IG.sampleTime
    (IG.engine ((ident 0 , Mux.handleState mid (proto ∷ []) duplex) ∷ []) ((mid , newMux) ∷ []) [] true 0)
module Fixture where
  caller child : WorkerId
  caller = ident 10
  child = ident 11
  sock : SocketId
  sock = ident 10
  req : A.Request
  req = A.acquireRequest (remote key₀) child sock outbound nothing
  s₀ reserved promised opened addressed forked connected published negotiated : Shared.State
  s₀ = M.world F.start
  reserved = record s₀ { cm = Shared.cmStore (Shared.full (Shared.insertLocal (remote key₀) unknownLocal (ident 0) []))
    ((ident 0 , Shared.reservedOutbound) ∷ []) 1 }
  promised = record reserved { promises = ident 0 ∷ []; nextPromise = 1 }
  opened = record promised { sockets = put sock (Shared.admitting caller) (Shared.sockets promised) }
  addressed = record opened { cm = record (Shared.cm opened) { mapCell = Shared.full (Shared.insertConnection key₀ (ident 0) []) } }
  forked = record addressed
    { handlers = put child (Shared.handlerStart (ident 0) sock (ident 0) key₀) (Shared.handlers addressed)
    ; sockets = put sock (Shared.handling child) (Shared.sockets addressed) }
  connected = record forked { cm = record (Shared.cm forked)
    { entries = put (ident 0) (Shared.unnegotiated outbound key₀ child) (Shared.entries (Shared.cm forked)) } }
  published = record connected { handshakeResults = (ident 0 , Shared.negotiated (ident 0) duplex) ∷ [] }
  info : NewConnectionInfo
  info = newConnectionInfo outbound key₀ duplex (ident 0)
  negotiated = record published
    { cm = record (Shared.cm published) { entries = (ident 0 , Shared.outboundDup key₀ child (ident 0) ticking) ∷ [] }
    ; inboundInfo = newConnection info ∷ [] }
  at : A.PC → Shared.State → O.Configuration
  at pc shared = record (O.initial (M.replaceWorld F.start shared))
    { acquiring = (caller , A.frame req pc) ∷ []; randomGeneration = 1 }
  begun : O.Configuration
  begun = record (at A.selecting s₀) { randomGeneration = 0 }
  wait : A.PC
  wait = A.awaitResult (ident 0) (ident 0) key₀
  withHandle : O.Configuration → O.Configuration
  withHandle c = record c { core = record (O.core c) { inboundGovernor = G.installedIG } }
  returned : O.Configuration
  returned = record (withHandle (at (A.complete (Cases.connected key₀ duplex (ident 0))) negotiated))
    { acquiring = []; acquired = (caller , Cases.connected key₀ duplex (ident 0)) ∷ [] }
module Prior where
  captured : Shared.HandlerStart
  captured = Shared.handlerStart (ident 0) Fixture.sock (ident 0) key₀
  at : O.Configuration → B.State
  at c = B.supervised c [] Close.initialState
  p₀ p1 p2 p3 p4 p5 p6 p7 p8 p9 p10 p11 p12 : B.State
  p₀ = at (O.initial F.start)
  p1 = at Fixture.begun
  p2 = at (Fixture.at (A.count (A.allocatePromise (ident 0))) Fixture.reserved)
  p3 = at (Fixture.at (A.allocatePromise (ident 0)) Fixture.reserved)
  p4 = at (Fixture.at (A.openSocket (ident 0) (ident 0)) Fixture.promised)
  p5 = at (Fixture.at (A.configureSocket (ident 0) (ident 0)) Fixture.opened)
  p6 = at (Fixture.at (A.connectSocket (ident 0) (ident 0)) Fixture.opened)
  p7 = at (Fixture.at (A.localAddress (ident 0) (ident 0)) Fixture.opened)
  p8 = at (Fixture.at (A.updateAddress (ident 0) (ident 0) key₀) Fixture.opened)
  p9 = at (Fixture.at (A.forkHandler (ident 0) (ident 0) key₀) Fixture.addressed)
  p10 = B.supervised (Fixture.at (A.connectedCommit (ident 0) (ident 0) key₀) Fixture.forked)
    ((Fixture.child , H.handlerThread captured H.maskedSetup) ∷ []) Close.initialState
  p11 = record p10 { threads = (Fixture.child , H.handlerThread captured H.handshaking) ∷ [] }
  connectedSource : O.Configuration
  connectedSource = Fixture.at (A.count Fixture.wait) Fixture.connected
  p12 = record p11 { source = connectedSource }
  initial-bounds : SupplyBounds (M.world F.start)
  initial-bounds = All.[] , All.[]

ps : List Protocol
ps = G.proto ∷ []
born : Store WorkerId Provenance
born = (Fixture.child , outbound) ∷ []
q₀ q1 q2 q3 q4 q5 q6 q7 q8 q9 q10 q11 q12 : U.State
q₀ = U.supervised Prior.p₀ [] []
q1 = U.supervised Prior.p1 [] []
q2 = U.supervised Prior.p2 [] []
q3 = U.supervised Prior.p3 [] []
q4 = U.supervised Prior.p4 [] []
q5 = U.supervised Prior.p5 [] []
q6 = U.supervised Prior.p6 [] []
q7 = U.supervised Prior.p7 [] []
q8 = U.supervised Prior.p8 [] []
q9 = U.supervised Prior.p9 [] []
q10 = U.supervised Prior.p10 born []
q11 = U.supervised Prior.p11 born []
q12 = U.supervised Prior.p12 born []
allocatedBase publishedBase : B.State
allocatedBase = record Prior.p12 { source = Fixture.withHandle Prior.connectedSource }
publishedBase = record Prior.p12 { source = Fixture.withHandle (Fixture.at (A.count Fixture.wait) Fixture.published) }
publishedFrame : U.Frame
publishedFrame = U.frame Prior.captured outbound ps duplex (U.promisePublished (ident 0) G.mid)
  (Startup.startupState Startup.published Startup.Pool.initial)
q15 : U.State
q15 = U.supervised publishedBase born ((Fixture.child , publishedFrame) ∷ [])
c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 : U.State
c1 = U.setSource (Fixture.withHandle (Fixture.at Fixture.wait Fixture.published)) q15
c2 = U.setSource (Fixture.withHandle (Fixture.at (A.commitResult (ident 0) key₀ (Shared.negotiated (ident 0) duplex)) Fixture.published)) q15
c3 = U.setSource (Fixture.withHandle (Fixture.at (A.count (A.complete (Cases.connected key₀ duplex (ident 0)))) Fixture.negotiated)) q15
c4 = U.setSource (Fixture.withHandle (Fixture.at (A.complete (Cases.connected key₀ duplex (ident 0))) Fixture.negotiated)) q15
c5 = U.setSource Fixture.returned q15
withIG : IG.Runtime → List IGEvent → U.State
withIG runtime queue = U.setSource (record Fixture.returned { core = record (O.core Fixture.returned)
  { inboundGovernor = runtime; world = record (M.world (O.core Fixture.returned)) { inboundInfo = queue } } }) q15
engine₀ engine₁ engine₂ : IG.Engine
engine₀ = IG.execution G.installedIG
engine₁ = record engine₀ { timers = (ident 0 , ticking) ∷ [] }
engine₂ = record engine₁ { timers = (ident 0 , ticking) ∷ (ident 1 , ticking) ∷ [] }
c6 = withIG (IG.runtimeState IG.emptyPublished 0 (IG.armInactivity 0) engine₀) (newConnection Fixture.info ∷ [])
c7 = withIG (IG.runtimeState IG.emptyPublished 1 (IG.awaitBatch 0 (ident 0)) engine₁) (newConnection Fixture.info ∷ [])
c8 = withIG (IG.runtimeState IG.emptyPublished 1 (IG.readNext 0 (newConnection Fixture.info ∷ [])) engine₁) []
c9 = withIG (IG.runtimeState IG.emptyPublished 1 (IG.prepareNew 0 Fixture.info [] IG.emptyPublished) engine₁) []
c10 = withIG (IG.runtimeState IG.emptyPublished 2 (IG.startResponders 0 Fixture.info [] IG.emptyPublished (ident 1)) engine₂) []
publishedIG : IG.Published
publishedIG = IG.published ((key₀ , IG.registered Fixture.info (ident 1)) ∷ [])
  ((remote key₀ , freshPeer 0 (ident 0)) ∷ [])
c11 = withIG (IG.runtimeState publishedIG 2 (IG.readNext 0 []) (record engine₂ { muxes = (G.mid , G.armedMux) ∷ [] })) []

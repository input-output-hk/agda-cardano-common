{-# OPTIONS --guardedness #-}

-- Data-only snapshots. Both handoffs precede either CM call; acceptance checks
-- every step. Flat worlds avoid expanding chains of projected record updates.
open import Data.Nat using (ℕ)
open import ConnectionManagement.Domain using (ConnectionKey)
module ConnectionManagement.Negative.ServerAdmissionPrefixFixtures
  (limit : ℕ) (secondKey : ConnectionKey) where

open import Data.Bool using (true)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import ConnectionManagement.Domain hiding (worker; local; mux)
open import ConnectionManagement.Store using (Store; put)
import ConnectionManagement.State as Shared
import ConnectionManagement.Machine as Machine
import ConnectionManagement.OutboundMachine as O
import ConnectionManagement.HandlerSupervision as H
import ConnectionManagement.OutboundHandlerSupervision as B
import ConnectionManagement.ServerAdmission as Server
import ConnectionManagement.MuxPublicationUnwind as Publication
import ConnectionManagement.Negative.MuxPublicationInboundFixtures as I
import ConnectionManagement.Scenarios.Admission as A
import ConnectionManagement.Rules.IGRegistration as IG
import ConnectionManagement.Rules.MuxRuntime as Mux
import ConnectionManagement.Rules.CMShutdown as Close
private
  module S = Server I.bearerClosed
  module N = Publication I.bearerClosed
  module C = N.C
  module D = N.D
  module R = N.R
  module W = N.W
  module G = N.G
  module M = N.M
  module P = N.P
  module U = N.U
  module Startup = N.S

r₀ r₁ : Shared.Admission
r₀ = Shared.admission A.key₀ (ident 0) A.child₀ limit
r₁ = Shared.admission secondKey (ident 1) A.child₁ limit
err closeErr replacement : ErrorId
err = errorId 120
closeErr = errorId 121
replacement = errorId 122
empty : Shared.State
empty = Shared.state A.emptyCM [] [] [] [] 0 [] [] []
workers : Store WorkerId S.Worker
workers = (A.w₀ , S.rawWorker r₀ S.calling 0) ∷ (A.w₁ , S.rawWorker r₁ S.calling 0) ∷ []
wrap : P.State → N.State
wrap p = N.publicationState (C.catchState (D.deltaQState (R.unwinding
  (W.handlerExitState (G.shutdownState (M.monitorState p []) []) []) []) []) []) []
start one two : S.State
start = S.serverState (wrap (I.pre (Machine.initial Shared.responderMode empty))) [] S.serving true
one = S.serverState (wrap (I.pre (Machine.initial Shared.responderMode
  (Shared.state A.emptyCM ((A.w₀ , Shared.admissionWorker r₀ Shared.acquireMap) ∷ []) []
    ((ident 0 , Shared.admitting A.w₀) ∷ []) [] 0 [] [] []))))
  ((A.w₀ , S.rawWorker r₀ S.calling 0) ∷ []) S.serving true

-- Every argument is data, rather than the result of an attempted transition.
world : Shared.CMStore → Shared.AdmissionPC → Shared.AdmissionPC →
  Store WorkerId Shared.HandlerStart → Shared.SocketOwner → Shared.SocketOwner →
  List PromiseId → ℕ → Store PromiseId Shared.HandshakeResult → List Shared.IGEvent → Shared.State
world c pc₀ pc₁ hs socket₀ socket₁ ps n rs queue = Shared.state c
  ((A.w₀ , Shared.admissionWorker r₀ pc₀) ∷ (A.w₁ , Shared.admissionWorker r₁ pc₁) ∷ [])
  hs ((ident 0 , socket₀) ∷ (ident 1 , socket₁) ∷ []) ps n rs queue []
pre : Shared.CMStore → Shared.AdmissionPC → Shared.AdmissionPC →
  List PromiseId → ℕ → Shared.SocketOwner → S.State
pre c pc₀ pc₁ ps n socket₀ = S.serverState (wrap (I.pre (Machine.initial Shared.responderMode
  (world c pc₀ pc₁ [] socket₀ (Shared.admitting A.w₁) ps n [] [])))) workers S.serving true
two = pre A.emptyCM Shared.acquireMap Shared.acquireMap [] 0 (Shared.admitting A.w₀)

-- The only physical birth is the first worker's actual handler fork.
live : Shared.ConnectionState → Shared.MapCell → Shared.AdmissionPC → Shared.AdmissionPC →
  List PromiseId → ℕ → Store PromiseId Shared.HandshakeResult → List Shared.IGEvent →
  Shared.SocketOwner → IG.Runtime → H.Phase → Store WorkerId U.Frame → S.State
live st c pc₀ pc₁ ps n rs queue socket₁ ig phase frames = S.serverState
  (wrap (P.protocolState (U.supervised
    (B.supervised (O.initial (record (Machine.initial Shared.responderMode
      (world (Shared.cmStore c ((ident 0 , st) ∷ []) 1) pc₀ pc₁
        ((A.child₀ , I.captured) ∷ []) (Shared.handling A.child₀) socket₁ ps n rs queue))
      { inboundGovernor = ig }))
      ((A.child₀ , H.handlerThread I.captured phase) ∷ []) Close.initialState)
    ((A.child₀ , inbound) ∷ []) frames) [] [])) workers S.serving true
lease₀ : Shared.Lease
lease₀ = Shared.lease A.w₀ []
binding : Shared.ConnMap
binding = Shared.insertConnection A.key₀ (ident 0) []
lease₁ : Shared.Lease
lease₁ = Shared.lease A.w₁ binding
unneg : Shared.ConnectionState
unneg = Shared.unnegotiated inbound A.key₀ A.child₀
locked : Shared.CMStore
locked = Shared.cmStore (Shared.taken A.w₀) [] 0
allocated : Shared.MapCell → Shared.CMStore
allocated c = Shared.cmStore c ((ident 0 , unneg) ∷ []) 1
await : Shared.AdmissionPC
await = Shared.awaitHandshake (ident 0) (ident 0)
ps₀ : List PromiseId
ps₀ = ident 0 ∷ []
p1 p2 p3 p4 p5 p6 p7 : S.State
p1 = pre locked (Shared.count lease₀) Shared.acquireMap [] 0 (Shared.admitting A.w₀)
p2 = pre locked (Shared.prepare lease₀) Shared.acquireMap [] 0 (Shared.admitting A.w₀)
p3 = pre locked (Shared.selectEntry lease₀ (ident 0)) Shared.acquireMap ps₀ 1 (Shared.admitting A.w₀)
p4 = pre (allocated (Shared.taken A.w₀)) (Shared.forkHandler lease₀ (ident 0) (ident 0))
  Shared.acquireMap ps₀ 1 (Shared.admitting A.w₀)
early : Shared.MapCell → Shared.AdmissionPC → Shared.AdmissionPC → Shared.SocketOwner → S.State
early c pc₀ pc₁ socket₁ = live unneg c pc₀ pc₁ ps₀ 1 [] [] socket₁ IG.initial H.maskedSetup []
p5 = early (Shared.taken A.w₀) (Shared.publish lease₀ (ident 0) (ident 0)) Shared.acquireMap (Shared.admitting A.w₁)
p6 = early (Shared.full binding) (Shared.countPublished (ident 0) (ident 0)) Shared.acquireMap (Shared.admitting A.w₁)
p7 = early (Shared.full binding) await Shared.acquireMap (Shared.admitting A.w₁)

-- Physical close snapshots retain the logical admission on a throwing close.
physicalClose : WorkerId → Shared.Admission → Shared.SocketOwner → S.WorkerPC → ℕ → S.State → S.State
physicalClose w req owner pc calls s = record (S.setWorld (record (S.shared s)
  { sockets = put (Shared.socketRef req) owner (Shared.sockets (S.shared s)) }) s)
  { workers = put w (S.rawWorker req pc calls) (S.workers s) }
raw₀ raw₁ : S.WorkerPC → ℕ → S.State → S.State
raw₀ pc n s = record s { workers = put A.w₀ (S.rawWorker r₀ pc n) workers }
raw₁ pc n s = record s { workers = put A.w₁ (S.rawWorker r₁ pc n) (S.workers s) }

-- Failed fork: restored empty map with committed entry/promise still allocated.
f1 f2 f3 f4 f5 : S.State
f1 = pre (allocated (Shared.taken A.w₀)) (Shared.reject lease₀ Shared.forkFailed)
  Shared.acquireMap ps₀ 1 (Shared.admitting A.w₀)
f2 = pre (allocated (Shared.full [])) (Shared.closeSocket Shared.forkFailed)
  Shared.acquireMap ps₀ 1 (Shared.admitting A.w₀)
f3 = raw₀ (S.closePrefix Shared.forkFailed (S.raised (S.sync err))) 0 f2
f4 = raw₀ (S.bodyExited (S.raised (S.sync err))) 1
  (pre (allocated (Shared.full [])) (Shared.finished Shared.forkFailed) Shared.acquireMap ps₀ 1 Shared.closed)
f5 = raw₀ (S.resultAvailable (S.raised (S.sync err))) 1
  (pre (allocated (Shared.full [])) (Shared.finished Shared.forkFailed) Shared.acquireMap ps₀ 1 Shared.closed)

-- Hard limit: normal Disconnected return after restoring/publishing the map.
h1 h2 h3 h4 h5 h6 : S.State
h1 = early (Shared.taken A.w₁) await (Shared.count lease₁) (Shared.admitting A.w₁)
h2 = early (Shared.taken A.w₁) await (Shared.reject lease₁ Shared.hardLimitReached) (Shared.admitting A.w₁)
h3 = early (Shared.full binding) await (Shared.closeSocket Shared.hardLimitReached) (Shared.admitting A.w₁)
h4 = raw₁ (S.closePrefix Shared.hardLimitReached S.returned) 0 h3
h5 = raw₁ (S.bodyExited S.returned) 1
  (early (Shared.full binding) await (Shared.finished Shared.hardLimitReached) Shared.closed)
h6 = raw₁ (S.resultAvailable S.returned) 1
  (early (Shared.full binding) await (Shared.finished Shared.hardLimitReached) Shared.closed)

-- A real successful handshake supplies the older inboundIdle entry.
allocatedIG : IG.Runtime
allocatedIG = record IG.initial { execution = IG.engine
  ((ident 0 , Mux.handleState (ident 0) I.ps duplex) ∷ [])
  ((ident 0 , Mux.muxState A.key₀ Mux.ready ((1 , Mux.idle) ∷ []) [] [] [] [] []
    (IG.initialCounters Mux.igTracer) Mux.returned Mux.igTracer) ∷ []) [] true 0 }
frame : U.Progress → Startup.State → Store WorkerId U.Frame
frame progress startup = (A.child₀ , U.frame I.captured inbound I.ps duplex progress startup) ∷ []
result : Store PromiseId Shared.HandshakeResult
result = (ident 0 , Shared.negotiated (ident 0) duplex) ∷ []
info : Shared.NewConnectionInfo
info = Shared.newConnectionInfo inbound A.key₀ duplex (ident 0)
idle : Shared.ConnectionState
idle = Shared.inboundIdle A.key₀ A.child₀ (ident 0) duplex
published : Store WorkerId U.Frame
published = frame (U.promisePublished (ident 0) (ident 0)) (record Startup.initial { phase = Startup.published })
successAt : Shared.ConnectionState → Shared.MapCell → Shared.AdmissionPC → Shared.AdmissionPC →
  List PromiseId → ℕ → List Shared.IGEvent → Shared.SocketOwner → S.State
successAt st c pc₀ pc₁ ps n queue socket₁ = live st c pc₀ pc₁ ps n result queue socket₁
  allocatedIG H.handshaking published
s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : S.State
s1 = live unneg (Shared.full binding) await Shared.acquireMap ps₀ 1 [] [] (Shared.admitting A.w₁)
  IG.initial H.handshaking []
s2 = live unneg (Shared.full binding) await Shared.acquireMap ps₀ 1 [] [] (Shared.admitting A.w₁)
  IG.initial H.handshaking (frame U.returnedSuccess Startup.initial)
s3 = live unneg (Shared.full binding) await Shared.acquireMap ps₀ 1 [] [] (Shared.admitting A.w₁)
  allocatedIG H.handshaking (frame (U.handleAllocated (ident 0) (ident 0)) Startup.initial)
s4 = successAt unneg (Shared.full binding) await Shared.acquireMap ps₀ 1 [] (Shared.admitting A.w₁)
s5 = successAt unneg (Shared.full binding) (Shared.commitHandshake (ident 0) (Shared.negotiated (ident 0) duplex))
  Shared.acquireMap ps₀ 1 [] (Shared.admitting A.w₁)
s6 = successAt idle (Shared.full binding) (Shared.countHandshake (Shared.connected info))
  Shared.acquireMap ps₀ 1 [] (Shared.admitting A.w₁)
s7 = successAt idle (Shared.full binding) (Shared.notifyInbound info) Shared.acquireMap ps₀ 1 [] (Shared.admitting A.w₁)
s8 = successAt idle (Shared.full binding) (Shared.returnHandshake (Shared.connected info))
  Shared.acquireMap ps₀ 1 (Shared.newConnection info ∷ []) (Shared.admitting A.w₁)
completed : Shared.AdmissionPC
completed = Shared.completedHandshake (Shared.connected info)
s9 = successAt idle (Shared.full binding) completed Shared.acquireMap ps₀ 1
  (Shared.newConnection info ∷ []) (Shared.admitting A.w₁)
s10 = raw₀ (S.bodyExited S.returned) 0 s9
s11 = raw₀ (S.resultAvailable S.returned) 0 s9

-- Same-key rejection preserves that handler, published result and caller result.
after : Shared.MapCell → Shared.AdmissionPC → List PromiseId → ℕ → Shared.SocketOwner → S.State
after c pc ps n owner = raw₀ (S.resultAvailable S.returned) 0
  (successAt idle c completed pc ps n (Shared.newConnection info ∷ []) owner)
ps₁ : List PromiseId
ps₁ = ident 1 ∷ ps₀
b1 b2 b3 b4 b5 b6 b7 b8 : S.State
b1 = after (Shared.taken A.w₁) (Shared.count lease₁) ps₀ 1 (Shared.admitting A.w₁)
b2 = after (Shared.taken A.w₁) (Shared.prepare lease₁) ps₀ 1 (Shared.admitting A.w₁)
b3 = after (Shared.taken A.w₁) (Shared.selectEntry lease₁ (ident 1)) ps₁ 2 (Shared.admitting A.w₁)
b4 = after (Shared.taken A.w₁) (Shared.reject lease₁ Shared.forbidden) ps₁ 2 (Shared.admitting A.w₁)
b5 = after (Shared.full binding) (Shared.closeSocket Shared.forbidden) ps₁ 2 (Shared.admitting A.w₁)
b6 = raw₁ (S.closePrefix Shared.forbidden (S.raised (S.sync err))) 0 b5
b7 = raw₁ (S.bodyExited (S.raised (S.sync err))) 1
  (after (Shared.full binding) (Shared.finished Shared.forbidden) ps₁ 2 Shared.closed)
b8 = raw₁ (S.resultAvailable (S.raised (S.sync err))) 1
  (after (Shared.full binding) (Shared.finished Shared.forbidden) ps₁ 2 Shared.closed)

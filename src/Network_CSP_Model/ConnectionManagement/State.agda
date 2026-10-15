{-# OPTIONS --guardedness #-}

-- Admission and handshake-consumer state, not the full CM/IG/OG/Server product.
module ConnectionManagement.State where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put; delete)

-- Source State.hs constructors retain their distinct reference fields.
data ConnectionState : Set where
  reservedOutbound : ConnectionState
  unnegotiated : Provenance → ConnectionKey → WorkerId → ConnectionState
  outboundUni : ConnectionKey → WorkerId → HandleId → ConnectionState
  outboundDup : ConnectionKey → WorkerId → HandleId → TimeoutFlag → ConnectionState
  outboundIdle inboundIdle inboundActive :
    ConnectionKey → WorkerId → HandleId → DataFlow → ConnectionState
  duplexActive : ConnectionKey → WorkerId → HandleId → ConnectionState
  terminating : ConnectionKey → WorkerId → Maybe ErrorId → ConnectionState
  terminated : Maybe ErrorId → ConnectionState

EntryHeap = Store EntryId ConnectionState
ConnMap = Store PeerAddr (Store LocalKey EntryId)

-- Exact-key lookup mirrors ConnMap.lookup, including no unknown-local fallback.
lookupConnection : ConnectionKey → ConnMap → Maybe EntryId
lookupConnection k m with lookup (remote k) m
... | nothing = nothing
... | just inner = lookup (knownLocal (local k)) inner

insertLocal : PeerAddr → LocalKey → EntryId → ConnMap → ConnMap
insertLocal r l e m with lookup r m
... | nothing = put r ((l , e) ∷ []) m
... | just inner = put r (put l e inner) m

insertConnection : ConnectionKey → EntryId → ConnMap → ConnMap
insertConnection k = insertLocal (remote k) (knownLocal (local k))

-- ConnMap.delete also drops an empty remote-address bucket.
deleteConnection : ConnectionKey → ConnMap → ConnMap
deleteConnection k m with lookup (remote k) m
... | nothing = m
... | just inner with delete (knownLocal (local k)) inner
...   | [] = delete (remote k) m
...   | xs = put (remote k) xs m

-- The map value is absent while an IO modifier owns it; entry TVars remain live.
data MapCell : Set where
  full : ConnMap → MapCell
  taken : WorkerId → MapCell

record CMStore : Set where
  constructor cmStore
  field
    mapCell : MapCell
    entries : EntryHeap
    nextEntry : ℕ
open CMStore public

record Lease : Set where
  constructor lease
  field
    owner : WorkerId
    savedMap : ConnMap
open Lease public

-- Source Core.hs:174-215, inboundConns projection (not socket ownership count).
inboundCount : ConnectionState → ℕ
inboundCount (unnegotiated inbound _ _) = 1
inboundCount (inboundIdle _ _ _ _) = 1
inboundCount (inboundActive _ _ _ _) = 1
inboundCount (duplexActive _ _ _) = 1
inboundCount _ = 0

-- Missing entry references are malformed fixtures, not source retry conditions.
countInner : EntryHeap → Store LocalKey EntryId → Maybe ℕ
countInner h [] = just 0
countInner h ((_ , e) ∷ xs) with lookup e h | countInner h xs
... | just st | just n = just (inboundCount st + n)
... | _ | _ = nothing

countIncoming : EntryHeap → ConnMap → Maybe ℕ
countIncoming h [] = just 0
countIncoming h ((_ , inner) ∷ xs) with countInner h inner | countIncoming h xs
... | just n | just m = just (n + m)
... | _ | _ = nothing

-- A request starts after accept's masked handoff; child is a reserved symbolic
-- reference for the source's lazy/mfix handler reference, not a runnable worker.
record Admission : Set where
  constructor admission
  field
    key : ConnectionKey
    socketRef : SocketId
    child : WorkerId
    hardLimit : ℕ
open Admission public

data Failure : Set where
  hardLimitReached forbidden forkFailed : Failure

-- Handler errors retain identity separately from the source classifier.
data HandlerErrorClass : Set where
  negotiationFailure protocolViolation : HandlerErrorClass

data HandshakeResult : Set where
  negotiated : HandleId → DataFlow → HandshakeResult
  query : HandshakeResult
  handlerError : HandlerErrorClass → ErrorId → HandshakeResult

data DisconnectReason : Set where
  handshakeQuery : DisconnectReason
  handshakeError : HandlerErrorClass → ErrorId → DisconnectReason
  inTerminating inTerminated : Maybe ErrorId → DisconnectReason

record NewConnectionInfo : Set where
  constructor newConnectionInfo
  field origin : Provenance
        connectionKey : ConnectionKey
        negotiatedFlow : DataFlow
        negotiatedHandle : HandleId
open NewConnectionInfo public

data Completion : Set where
  connected : NewConnectionInfo → Completion
  disconnected : DisconnectReason → Completion

-- The source's InResponderMode gate, supplied as a fixed scenario parameter.
data ResponderMode : Set where
  responderMode noResponderMode : ResponderMode

-- Continuations retain captured entry/result values across distinct STM commits.
data AdmissionPC : Set where
  acquireMap : AdmissionPC
  count : Lease → AdmissionPC
  prepare : Lease → AdmissionPC
  selectEntry : Lease → PromiseId → AdmissionPC
  forkHandler : Lease → PromiseId → EntryId → AdmissionPC
  publish : Lease → PromiseId → EntryId → AdmissionPC
  reject : Lease → Failure → AdmissionPC
  closeSocket : Failure → AdmissionPC
  finished : Failure → AdmissionPC
  countPublished : PromiseId → EntryId → AdmissionPC
  awaitHandshake : PromiseId → EntryId → AdmissionPC
  commitHandshake : EntryId → HandshakeResult → AdmissionPC
  countHandshake : Completion → AdmissionPC
  notifyInbound : NewConnectionInfo → AdmissionPC
  returnHandshake : Completion → AdmissionPC
  completedHandshake : Completion → AdmissionPC
  impossibleHandshake : AdmissionPC

record AdmissionWorker : Set where
  constructor admissionWorker
  field request : Admission
        pc : AdmissionPC
open AdmissionWorker public

record HandlerStart : Set where
  constructor handlerStart
  field handlerEntry : EntryId
        handlerSocket : SocketId
        handlerPromise : PromiseId
        handlerKey : ConnectionKey
open HandlerStart public

data SocketOwner : Set where
  admitting handling : WorkerId → SocketOwner
  closed : SocketOwner
  closeUncertain : ErrorId → SocketOwner

-- Cleanup enters after the handler body exits. The body outcome is external to
-- this slice; these outcomes concern cleanup itself, including TIME_WAIT failure.
data CleanupOutcome : Set where
  cleanupNormal : CleanupOutcome
  cleanupError : ErrorId → CleanupOutcome

data CleanupTail : Set where
  countImmediately : CleanupTail
  timeWait : ConnectionState → CleanupTail

-- The saved map and the proposed map are distinct until putMap completes.
data CleanupPC : Set where
  cleanupAcquire : CleanupPC
  cleanupSelect : Lease → CleanupPC
  cleanupClose : Lease → ConnMap → CleanupTail → CleanupPC
  cleanupPublish : Lease → ConnMap → CleanupTail → CleanupPC
  cleanupRestore : Lease → ErrorId → CleanupPC
  cleanupWaiting : ConnectionState → CleanupPC
  cleanupFinalize : ConnectionState → CleanupOutcome → CleanupPC
  cleanupCount : CleanupOutcome → CleanupPC
  cleanupDone : CleanupOutcome → CleanupPC

record State : Set where
  constructor state
  field
    cm : CMStore
    admissions : Store WorkerId AdmissionWorker
    handlers : Store WorkerId HandlerStart
    sockets : Store SocketId SocketOwner
    promises : List PromiseId
    nextPromise : ℕ
    handshakeResults : Store PromiseId HandshakeResult
    inboundInfo : List NewConnectionInfo
    cleanups : Store WorkerId CleanupPC
open State public

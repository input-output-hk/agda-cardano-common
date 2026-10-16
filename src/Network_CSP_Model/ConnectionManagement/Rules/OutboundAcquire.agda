{-# OPTIONS --guardedness #-}

-- Outbound acquisition PCs follow Core.hs:1273-1832 at the fixed network pin.
-- IO results and random selection are inputs; their sequencing is executable.
module ConnectionManagement.Rules.OutboundAcquire where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; suc)
open import Data.List using (List; []; _∷_; filterᵇ)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_; proj₂)
open import Relation.Nullary using (yes; no; does)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (Store; lookup; put; delete)
open import ConnectionManagement.State hiding (selectEntry; closeSocket)
import ConnectionManagement.Rules.OutboundCases as C
import ConnectionManagement.Rules.InformationChannel as Queue

record Request : Set where
  constructor acquireRequest
  field peer : PeerAddr
        child : WorkerId
        socketRef : SocketId
        provenance : Provenance
        bindLocal : Maybe PeerAddr
open Request public

data PC : Set where
  selecting : PC
  count : PC → PC
  allocatePromise : EntryId → PC
  openSocket configureSocket bindSocket connectSocket localAddress : EntryId → PromiseId → PC
  updateAddress forkHandler connectedCommit : EntryId → PromiseId → ConnectionKey → PC
  awaitResult : EntryId → PromiseId → ConnectionKey → PC
  commitResult : EntryId → ConnectionKey → HandshakeResult → PC
  waitingInbound : EntryId → ConnectionKey → PC
  closeError removeError : EntryId → C.Fault → PC
  complete : C.Result → PC

record Frame : Set where
  constructor frame
  field req : Request
        pc : PC
open Frame public
Runtime = Store WorkerId Frame

-- A caller supplies a member of the remote bucket after a fresh random split.
-- An unknown-local reservation has priority over every known-local entry.
memberEntry : EntryId → Store LocalKey EntryId → Bool
memberEntry e [] = false
memberEntry e ((_ , x) ∷ xs) with e ≟ x
... | yes _ = true
... | no _ = memberEntry e xs
validSelection : PeerAddr → Maybe EntryId → ConnMap → Bool
validSelection p nothing m with lookup p m
... | nothing = true
... | just [] = true
... | just (_ ∷ _) = false
validSelection p (just e) m with lookup p m
... | nothing = false
... | just inner with lookup unknownLocal inner
...   | just reserved = does (e ≟ reserved)
...   | nothing = memberEntry e inner

-- The alias filter is public so map-invariant proofs can share its exact term.
differentEntry : EntryId → EntryId → Bool
differentEntry x y with x ≟ y
... | yes _ = false
... | no _ = true

-- Failure cleanup removes only aliases of this captured entry at this remote.
removeAliases : PeerAddr → EntryId → ConnMap → ConnMap
removeAliases p e m with lookup p m
... | nothing = m
... | just inner = keep (filterᵇ (λ pair → differentEntry (proj₂ pair) e) inner)
  where
  keep : Store LocalKey EntryId → ConnMap
  keep [] = delete p m
  keep xs = put p xs m

-- updateLocalAddr deletes the reservation even if the concrete key collides.
updateLocal : ConnectionKey → ConnMap → Bool × ConnMap
updateLocal k m with lookup (remote k) m
... | nothing = false , m
... | just inner with lookup unknownLocal inner
...   | nothing = false , m
...   | just e with lookup (knownLocal (local k)) inner
...     | just _ = false , put (remote k) (delete unknownLocal inner) m
...     | nothing = true , put (remote k) (put (knownLocal (local k)) e (delete unknownLocal inner)) m

setPC : Frame → PC → State → Frame × State
setPC f p s = record f { pc = p } , s
write : EntryId → ConnectionState → State → State
write e st s = record s { cm = record (cm s) { entries = put e st (entries (cm s)) } }

applyChoice : Bool → EntryId → C.Choice → Frame → State → Maybe (Frame × State)
applyChoice first e C.retry f s = nothing
applyChoice first e (C.waitInbound k) f s = just (setPC f (count (waitingInbound e k)) s)
applyChoice true e (C.refuse err) f s = just (setPC f (count (complete (C.raised err))) s)
applyChoice false e (C.refuse err) f s = just (setPC f (complete (C.raised err)) s)
applyChoice first e (C.gone result) f s = just (setPC f (count (complete result)) s)
applyChoice true e (C.reuse st result) f s = just (setPC f (count (count (complete result))) (write e st s))
applyChoice false e (C.reuse st result) f s = just (setPC f (count (complete result)) (write e st s))

selectKnown : Maybe EntryId → ConnMap → Frame → State → Maybe (Frame × State)
selectKnown (just e) m f s with lookup e (entries (cm s))
... | nothing = nothing
... | just st = applyChoice true e (C.acquireCase st) f s
selectKnown nothing m f s with provenance (req f)
... | inbound = just (setPC f (count (complete (C.raised C.inboundNotFound))) s)
... | outbound with lookup (ident (nextEntry (cm s))) (entries (cm s))
...   | just _ = nothing
...   | nothing = just (setPC f (count (allocatePromise (ident (nextEntry (cm s)))))
  (record s { cm = record (cm s)
    { mapCell = full (insertLocal (peer (req f)) unknownLocal (ident (nextEntry (cm s))) m)
    ; entries = put (ident (nextEntry (cm s))) reservedOutbound (entries (cm s))
    ; nextEntry = suc (nextEntry (cm s)) } }))

selectEntry : Maybe EntryId → Frame → State → Maybe (Frame × State)
selectEntry chosen f s with mapCell (cm s)
... | taken _ = nothing
... | full m with validSelection (peer (req f)) chosen m
...   | false = nothing
...   | true = selectKnown chosen m f s

-- All allocation, socket and handshake boundaries are distinct actions.
data Action : Set where
  select : Maybe EntryId → Action
  readCounters newPromise openOK configureOK bindOK connectOK : Action
  gotLocal : PeerAddr → Action
  updateLocalAddress forkOK commitConnected readResult commitHandshake returnResult : Action
  failIO : ErrorId → Action
  closeFailed : ErrorId → Action
  closeOK removeReservation : Action
  waitNegotiated : Action

-- The negotiated entry write and outbound-duplex IG enqueue share one STM.
commitSuccess : ResponderMode → EntryId → ConnectionKey → HandleId → DataFlow → Frame → State → Maybe (Frame × State)
commitSuccess mode e k h flow f s with lookup e (entries (cm s))
... | nothing = nothing
... | just st = apply mode (C.successCase k (child (req f)) h flow st)
  where
  applyState : C.Negotiated → State
  applyState d with C.replacement d
  ... | nothing = s
  ... | just replacement = write e replacement s
  apply : ResponderMode → C.Negotiated → Maybe (Frame × State)
  apply mode d with C.result d
  ... | C.raised err = just (setPC f (complete (C.raised err)) s)
  ... | result with C.notify d | mode
  ...   | true | responderMode with Queue.writeMessage (newConnection (newConnectionInfo outbound k flow h)) (inboundInfo s)
  ...     | nothing = nothing
  ...     | just queue = just (setPC f (count (complete result)) (record (applyState d) { inboundInfo = queue }))
  apply mode d | result | _ | _ = just (setPC f (count (complete result)) (applyState d))

-- Unlike inbound error cleanup, the captured entry is written even if its map
-- binding has been replaced. Only deletion is guarded by current entry identity.
commitError : EntryId → ConnectionKey → DisconnectReason → Frame → State → Maybe (Frame × State)
commitError e k reason f s with lookup e (entries (cm s)) | mapCell (cm s)
... | nothing | _ = nothing
... | _ | taken _ = nothing
... | just st | full m = just (setPC f (count (complete (C.disconnected k reason)))
  (record s { cm = record (cm s) { entries = put e (replacement reason st) (entries (cm s)); mapCell = full (remove m) } }))
  where
  replacement : DisconnectReason → ConnectionState → ConnectionState
  replacement reason st@(terminated _) = st
  replacement reason _ with reason
  ... | handshakeError negotiationFailure err = terminating k (child (req f)) (just err)
  ... | handshakeError protocolViolation err = terminated (just err)
  ... | _ = terminated nothing
  remove : ConnMap → ConnMap
  remove m with lookupConnection k m
  ... | nothing = m
  ... | just current with current ≟ e
  ...   | yes _ = deleteConnection k m
  ...   | no _ = m

step : WorkerId → ResponderMode → Action → Frame → State → Maybe (Frame × State)
step caller mode (select chosen) f s with pc f
... | selecting = selectEntry chosen f s
... | _ = nothing
step caller mode readCounters f s with pc f | mapCell (cm s)
... | count next | full m with countIncoming (entries (cm s)) m
...   | nothing = nothing
...   | just _ = just (setPC f next s)
step caller mode readCounters f s | _ | _ = nothing
step caller mode newPromise f s with pc f
... | allocatePromise e with lookup (ident (nextPromise s)) (handshakeResults s)
...   | just _ = nothing
...   | nothing = just (setPC f (openSocket e (ident (nextPromise s)))
  (record s { promises = ident (nextPromise s) ∷ promises s; nextPromise = suc (nextPromise s) }))
step caller mode newPromise f s | _ = nothing
step caller mode openOK f s with pc f | lookup (socketRef (req f)) (sockets s)
... | openSocket e p | nothing = just (setPC f (configureSocket e p)
  (record s { sockets = put (socketRef (req f)) (admitting caller) (sockets s) }))
... | _ | _ = nothing
step caller mode configureOK f s with pc f | bindLocal (req f)
... | configureSocket e p | nothing = just (setPC f (connectSocket e p) s)
... | configureSocket e p | just _ = just (setPC f (bindSocket e p) s)
... | _ | _ = nothing
step caller mode bindOK f s with pc f
... | bindSocket e p = just (setPC f (connectSocket e p) s)
... | _ = nothing
step caller mode connectOK f s with pc f
... | connectSocket e p = just (setPC f (localAddress e p) s)
... | _ = nothing
step caller mode (gotLocal local) f s with pc f
... | localAddress e p = just (setPC f (updateAddress e p (connection local (peer (req f)))) s)
... | _ = nothing
step caller mode updateLocalAddress f s with pc f | mapCell (cm s)
... | updateAddress e p k | full m with updateLocal k m
...   | true , m′ = just (setPC f (forkHandler e p k) (record s { cm = record (cm s) { mapCell = full m′ } }))
...   | false , m′ = just (setPC f (closeError e C.connectionExists) (record s { cm = record (cm s) { mapCell = full m′ } }))
step caller mode updateLocalAddress f s | _ | _ = nothing
step caller mode forkOK f s with pc f | lookup (child (req f)) (handlers s)
... | forkHandler e p k | nothing = just (setPC f (connectedCommit e p k)
  (record s { handlers = put (child (req f)) (handlerStart e (socketRef (req f)) p k) (handlers s)
            ; sockets = put (socketRef (req f)) (handling (child (req f))) (sockets s) }))
... | _ | _ = nothing
step caller mode commitConnected f s with pc f
... | connectedCommit e p k with lookup e (entries (cm s))
...   | nothing = nothing
...   | just st = just (setPC f (count (awaitResult e p k)) (update st))
  where
  update : ConnectionState → State
  update reservedOutbound = write e (unnegotiated outbound k (child (req f))) s
  update (unnegotiated inbound _ _) = write e (unnegotiated outbound k (child (req f))) s
  update _ = s -- source traces assert True for the unexpected branch
step caller mode commitConnected f s | _ = nothing
step caller mode readResult f s with pc f
... | awaitResult e p k with lookup p (handshakeResults s)
...   | nothing = nothing
...   | just result = just (setPC f (commitResult e k result) s)
step caller mode readResult f s | _ = nothing
step caller mode commitHandshake f s with pc f
... | commitResult e k (negotiated h flow) = commitSuccess mode e k h flow f s
... | commitResult e k query = commitError e k handshakeQuery f s
... | commitResult e k (handlerError cls err) = commitError e k (handshakeError cls err) f s
... | _ = nothing
step caller mode waitNegotiated f s with pc f
... | waitingInbound e k with lookup e (entries (cm s))
...   | nothing = nothing
...   | just st = applyChoice false e (C.waitCase k st) f s
step caller mode waitNegotiated f s | _ = nothing
step caller mode (failIO err) f s with pc f
... | openSocket e p = just (setPC f (complete (C.raised (C.ioFailure err))) s)
... | configureSocket e p = just (setPC f (closeError e (C.ioFailure err)) s)
... | bindSocket e p = just (setPC f (closeError e (C.ioFailure err)) s)
... | connectSocket e p = just (setPC f (closeError e (C.ioFailure err)) s)
... | localAddress e p = just (setPC f (closeError e (C.ioFailure err)) s)
... | forkHandler e p k = just (setPC f (closeError e (C.ioFailure err)) s)
... | _ = nothing
step caller mode closeOK f s with pc f
... | closeError e err = just (setPC f (removeError e err)
  (record s { sockets = put (socketRef (req f)) closed (sockets s) }))
... | _ = nothing
step caller mode (closeFailed err) f s with pc f
... | closeError e _ = just (setPC f (complete (C.raised (C.ioFailure err)))
  (record s { sockets = put (socketRef (req f)) (closeUncertain err) (sockets s) }))
... | _ = nothing
step caller mode removeReservation f s with pc f | mapCell (cm s)
... | removeError e err | full m = just (setPC f (count (complete (C.raised err)))
  (record s { cm = record (cm s) { mapCell = full (removeAliases (peer (req f)) e m)
                              ; entries = put e (terminated nothing) (entries (cm s)) } }))
... | _ | _ = nothing
step caller mode returnResult f s = nothing -- the subsystem consumes complete frames

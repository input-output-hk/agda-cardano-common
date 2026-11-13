{-# OPTIONS --guardedness #-}

-- One invocation per captured endpoint. Operation returns, legal request sites,
-- registry snapshots and actual exception receipts are certified source inputs.
module ConnectionManagement.ProtocolContracts2 where

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Maybe using (Maybe; just; nothing)
open import ConnectionManagement.Domain using (ErrorId)
open import ConnectionManagement.ProtocolContracts using (Exit; normal; synchronous; cancelled)

data Endpoint : Set where
  txClient txServerV1 txServerV2 keepClient keepServer : Endpoint
data Wait : Set where
  channel snapshot submission initialDelay sharedChange claimableChange : Wait
data Phase : Set where
  fresh idle : Phase
  blocked : Wait → Phase
  txBlocking keepDecision donePending : Phase
  cleaning txRetired keepCancel keepJoin : Exit → Phase
  finished : Exit → Phase

-- The V1/V2 fields are alternatives in a source instantiation, not two servers
-- for one negotiated run. Counts certify actual pipelined requests/collections.
record State : Set where
  constructor state
  field tc ts1 ts2 kc ks : Phase
        depth1 depth2 : ℕ
        dq dying : Bool
open State public
initial : State
initial = state fresh fresh fresh fresh fresh 0 0 false false
at : Endpoint → State → Phase
at txClient = tc
at txServerV1 = ts1
at txServerV2 = ts2
at keepClient = kc
at keepServer = ks
set : Endpoint → Phase → State → State
set txClient p s = record s { tc = p }
set txServerV1 p s = record s { ts1 = p }
set txServerV2 p s = record s { ts2 = p }
set keepClient p s = record s { kc = p }
set keepServer p s = record s { ks = p }

-- KeepAlive start certifies absence/registration and the initial ping send;
-- its next operation is response receive, never an initial control read.
data Action : Set where
  start : Endpoint → Action
  await : Endpoint → Wait → Action
  ready : Endpoint → Action
  blockingRequest : Action
  blockingReply : Endpoint → Action
  acquisitionFailed : Endpoint → Exit → Action
  blockingIds : Endpoint → Action
  issue collect : Endpoint → Action
  terminate : Endpoint → Action
  workAvailable intervalElapsed : Action
  sentDone : Endpoint → Action
  peerDone : Endpoint → Action
  fail : Endpoint → ErrorId → Action
  receiveCancel : Endpoint → Action
  cleanup : Endpoint → Action
  releaseCancelled : Endpoint → Action
  retireTx : Action
  keepSnapshot : Bool → Action
  fetchCancelReceived fetchDone : Action
  cleanupError : Endpoint → ErrorId → Action

waitAllowed : Endpoint → Wait → Bool
waitAllowed txClient channel = true
waitAllowed txClient snapshot = true
waitAllowed txServerV1 channel = true
waitAllowed txServerV1 snapshot = true
waitAllowed txServerV1 submission = true
waitAllowed txServerV1 initialDelay = true
waitAllowed txServerV2 channel = true
waitAllowed txServerV2 snapshot = true
waitAllowed txServerV2 submission = true
waitAllowed txServerV2 initialDelay = true
waitAllowed txServerV2 sharedChange = true
waitAllowed txServerV2 claimableChange = true
waitAllowed keepServer channel = true
waitAllowed _ _ = false

-- Only body phases accept cancellation. KeepAlive's finalizer is entirely
-- uninterruptible; an error is a separate observed synchronous escaping fault.
body : Phase → Bool
body idle = true
body (blocked _) = true
body txBlocking = true
body keepDecision = true
body donePending = true
body _ = false
exit : Endpoint → Exit → State → Maybe State
exit ep e s with body (at ep s)
... | true = just (set ep (cleaning e) s)
... | false = nothing

step : Action → State → Maybe State
step (acquisitionFailed ep normal) s = nothing
step (acquisitionFailed ep e) s with at ep s
... | fresh = just (set ep (finished e) s)
... | _ = nothing
step (blockingReply ep) s with ep | at ep s
... | txServerV1 | txBlocking = just (set ep idle s)
... | txServerV2 | txBlocking = just (set ep idle s)
... | _ | _ = nothing
step (start keepClient) s with kc s | dq s
... | fresh | false = just (record s { kc = blocked channel ; dq = true })
... | _ | _ = nothing
step (start ep) s with at ep s
... | fresh = just (set ep idle s)
... | _ = nothing
step (await ep w) s with at ep s | waitAllowed ep w
... | idle | true = just (set ep (blocked w) s)
... | _ | _ = nothing
-- A KeepAlive response observation includes cookie validation, dq update,
-- tracing and delay registration. Errors during those operations use fail.
step (ready keepClient) s with kc s
... | blocked channel = just (set keepClient keepDecision s)
... | _ = nothing
step (ready ep) s with at ep s
... | blocked _ = just (set ep idle s)
... | _ = nothing
step blockingRequest s with tc s
... | idle = just (set txClient txBlocking s)
... | _ = nothing
step (blockingIds txServerV1) s with ts1 s | depth1 s
... | idle | zero = just (set txServerV1 txBlocking s)
... | _ | _ = nothing
step (blockingIds txServerV2) s with ts2 s | depth2 s
... | idle | zero = just (set txServerV2 txBlocking s)
... | _ | _ = nothing
step (blockingIds _) s = nothing
step (issue txServerV1) s with ts1 s
... | idle = just (record s { depth1 = suc (depth1 s) })
... | _ = nothing
step (issue txServerV2) s with ts2 s
... | idle = just (record s { depth2 = suc (depth2 s) })
... | _ = nothing
step (issue _) s = nothing
step (collect txServerV1) s with ts1 s | depth1 s
... | idle | suc n = just (record s { depth1 = n })
... | _ | _ = nothing
step (collect txServerV2) s with ts2 s | depth2 s
... | idle | suc n = just (record s { depth2 = n })
... | _ | _ = nothing
step (collect _) s = nothing
step (terminate txClient) s with tc s
... | txBlocking = just (set txClient donePending s)
... | _ = nothing
step (terminate keepClient) s with kc s
... | keepDecision = just (set keepClient donePending s)
... | _ = nothing
step (terminate _) s = nothing
step workAvailable s with tc s
... | txBlocking = just (set txClient idle s)
... | _ = nothing
step intervalElapsed s with kc s
... | keepDecision = just (set keepClient (blocked channel) s)
... | _ = nothing
step (sentDone ep) s with at ep s
... | donePending = just (set ep (cleaning normal) s)
... | _ = nothing
step (peerDone txServerV1) s with ts1 s
... | txBlocking = just (set txServerV1 (cleaning normal) s)
... | _ = nothing
step (peerDone txServerV2) s with ts2 s
... | txBlocking = just (set txServerV2 (cleaning normal) s)
... | _ = nothing
step (peerDone keepServer) s with ks s
... | idle = just (set keepServer (cleaning normal) s)
... | blocked channel = just (set keepServer (cleaning normal) s)
... | _ = nothing
step (peerDone _) s = nothing
step (fail ep e) s = exit ep (synchronous e) s
step (receiveCancel ep) s = exit ep cancelled s
-- V2 retires/scrubs in one STM transaction, leaves tier in a second one.
-- Observed async receipt at an interruptible operation in the ordinary V2
-- release mask. It may escape before resource cleanup finishes; KA forbids it.
step (releaseCancelled txServerV2) s with ts2 s
... | cleaning _ = just (set txServerV2 (finished cancelled) s)
... | txRetired _ = just (set txServerV2 (finished cancelled) s)
... | _ = nothing
step (releaseCancelled _) s = nothing
step retireTx s with ts2 s
... | cleaning e = just (set txServerV2 (txRetired e) s)
... | _ = nothing
step (cleanup txServerV2) s with ts2 s
... | txRetired e = just (set txServerV2 (finished e) s)
... | _ = nothing
step (cleanup keepClient) s = nothing
step (cleanup ep) s with at ep s
... | cleaning e = just (set ep (finished e) s)
... | _ = nothing
-- Atomic finalizer snapshot either removes dq immediately or captures the
-- exact fetch thread/doneVar and marks dying before throwTo. No timeout here.
step (keepSnapshot false) s with kc s
... | cleaning e = just (record s { kc = finished e ; dq = false })
... | _ = nothing
step (keepSnapshot true) s with kc s
... | cleaning e = just (record s { kc = keepCancel e ; dying = true })
... | _ = nothing
step fetchCancelReceived s with kc s
... | keepCancel e = just (set keepClient (keepJoin e) s)
... | _ = nothing
step fetchDone s with kc s
... | keepJoin e = just (record s { kc = finished e ; dq = false ; dying = false })
... | _ = nothing
-- An escaping finalizer fault replaces the result; it does not certify
-- resource removal (dq/dying are deliberately retained).
step (cleanupError ep err) s with at ep s
... | cleaning _ = just (set ep (finished (synchronous err)) s)
... | txRetired _ = just (set ep (finished (synchronous err)) s)
... | keepCancel _ = just (set ep (finished (synchronous err)) s)
... | keepJoin _ = just (set ep (finished (synchronous err)) s)
... | _ = nothing

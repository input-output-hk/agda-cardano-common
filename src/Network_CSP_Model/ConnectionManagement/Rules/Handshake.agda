{-# OPTIONS --guardedness #-}

-- Core.hs:897-1101 at the pinned revision. These rules implement the inbound
-- consumer; publishBoundary abstracts a handler that has reached writePromise.
module ConnectionManagement.Rules.Handshake where

open import Data.Nat using (suc; _≤?_)
open import Data.List using ([]; _∷_; _++_; length)
open import Data.Bool using (true; false)
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (yes; no; does)
open import Class.DecEq using (_≟_)
open import ConnectionManagement.Domain
open import ConnectionManagement.Store using (lookup; put)
open import ConnectionManagement.State
open import ConnectionManagement.Rules.Server using (setPC)
import ConnectionManagement.Rules.InformationChannel as InfoChannel

-- Publication is an explicit environment boundary, not a model of allocation,
-- negotiation, mux execution or handler cleanup. A duplicate source write throws;
-- preserve that outcome instead of interpreting it as a disabled transition.
data Publication : Set where
  published : State → Publication
  writerBlocked : Publication

publishBoundary : WorkerId → HandshakeResult → State → Maybe Publication
publishBoundary w result s with lookup w (handlers s) | lookup w (cleanups s)
... | nothing | _ = nothing
... | just _ | just _ = nothing -- the body has already exited
... | just h | nothing with any (λ p → does (p ≟ handlerPromise h)) (promises s)
...   | false = nothing -- malformed, unallocated promise
...   | true with lookup (handlerPromise h) (handshakeResults s)
...     | just _ = just writerBlocked
...     | nothing = just (published (record s
        { handshakeResults = put (handlerPromise h) result (handshakeResults s) }))

-- Exhaustive projection of the successful-result STM. ImpossibleState is an
-- exception outcome, not a missing rule. No map lookup or ownership test occurs.
data SuccessDecision : Set where
  update : ConnectionState → Provenance → SuccessDecision
  retain : Provenance → SuccessDecision
  disconnect : DisconnectReason → SuccessDecision
  impossible : SuccessDecision

decideSuccess : Admission → HandleId → DataFlow → ConnectionState → SuccessDecision
decideSuccess r h f reservedOutbound = impossible
decideSuccess r h f (unnegotiated _ _ _) =
  update (inboundIdle (key r) (child r) h f) inbound
decideSuccess r h f (outboundUni _ _ _) = retain outbound
decideSuccess r h f (outboundDup _ _ _ _) = retain outbound
decideSuccess r h f (outboundIdle _ _ _ oldFlow) =
  update (inboundIdle (key r) (child r) h oldFlow) outbound
decideSuccess r h f (inboundIdle _ _ _ _) = impossible
decideSuccess r h f (inboundActive _ _ _ _) = impossible
decideSuccess r h f (duplexActive _ _ _) = impossible
decideSuccess r h f (terminating _ _ err) = disconnect (inTerminating err)
decideSuccess r h f (terminated err) = disconnect (inTerminated err)

-- Source computeConnStateOnError distinguishes negotiation from protocol errors.
errorState : Admission → DisconnectReason → ConnectionState
errorState r (handshakeError negotiationFailure e) = terminating (key r) (child r) (just e)
errorState r (handshakeError protocolViolation e) = terminated (just e)
errorState r _ = terminated nothing

applySuccess : WorkerId → AdmissionWorker → EntryId → HandleId → DataFlow →
  SuccessDecision → State → State
applySuccess w a e h f (update st provenance) s =
  setPC w a (countHandshake (connected (newConnectionInfo provenance (key (request a)) f h)))
    (record s { cm = record (cm s) { entries = put e st (entries (cm s)) } })
applySuccess w a e h f (retain provenance) s =
  setPC w a (countHandshake (connected (newConnectionInfo provenance (key (request a)) f h))) s
applySuccess w a e h f (disconnect reason) s =
  setPC w a (countHandshake (disconnected reason)) s
applySuccess w a e h f impossible s = setPC w a impossibleHandshake s

-- Error/query removal and captured-entry update share ONE STM commit. A stale
-- entry identity prevents both effects, even when the key has been reused.
terminateResult : WorkerId → AdmissionWorker → EntryId → DisconnectReason →
  State → Maybe State
terminateResult w a e reason s with lookup e (entries (cm s)) | mapCell (cm s)
... | nothing | _ = nothing -- malformed captured reference
... | just _ | taken _ = nothing
... | just _ | full m with lookupConnection (key (request a)) m
...   | nothing = just (setPC w a (countHandshake (disconnected reason)) s)
...   | just current with e ≟ current
...     | no _ = just (setPC w a (countHandshake (disconnected reason)) s)
...     | yes _ = just (setPC w a (countHandshake (disconnected reason))
        (record s { cm = record (cm s)
          { mapCell = full (deleteConnection (key (request a)) m)
          ; entries = put e (errorState (request a) reason) (entries (cm s)) } }))

data HandshakeAction : Set where
  readResult commitResult readResultCounters enqueueInbound returnResult : HandshakeAction

-- Promise reads are non-consuming (Types.hs:297-317). Result commit is later.
stepWorker : ResponderMode → WorkerId → AdmissionWorker → HandshakeAction → State → Maybe State
stepWorker mode w a readResult s with pc a
... | awaitHandshake p e with lookup p (handshakeResults s)
...   | nothing = nothing
...   | just result = just (setPC w a (commitHandshake e result) s)
stepWorker mode w a readResult s | _ = nothing

stepWorker mode w a commitResult s with pc a
... | commitHandshake e (negotiated h f) with lookup e (entries (cm s))
...   | nothing = nothing
...   | just st = just (applySuccess w a e h f (decideSuccess (request a) h f st) s)
stepWorker mode w a commitResult s | commitHandshake e query =
  terminateResult w a e handshakeQuery s
stepWorker mode w a commitResult s | commitHandshake e (handlerError cls err) =
  terminateResult w a e (handshakeError cls err) s
stepWorker mode w a commitResult s | _ = nothing

stepWorker mode w a readResultCounters s with pc a | mapCell (cm s)
... | countHandshake result | full m with countIncoming (entries (cm s)) m
...   | nothing = nothing
...   | just _ with result | mode
...     | connected info | responderMode = just (setPC w a (notifyInbound info) s)
...     | connected info | noResponderMode = just (setPC w a (returnHandshake result) s)
...     | disconnected _ | _ = just (setPC w a (returnHandshake result) s)
stepWorker mode w a readResultCounters s | _ | _ = nothing

-- InformationChannel.hs uses a TBQueue of depth 100; queue-full retries. IG
-- consumption is deliberately absent until the IG batch/registration rules exist.
stepWorker mode w a enqueueInbound s with pc a
... | notifyInbound info with InfoChannel.writeMessage info (inboundInfo s)
...   | nothing = nothing
...   | just queue = just (setPC w a (returnHandshake (connected info))
      (record s { inboundInfo = queue }))
stepWorker mode w a enqueueInbound s | _ = nothing

stepWorker mode w a returnResult s with pc a
... | returnHandshake result = just (setPC w a (completedHandshake result) s)
... | _ = nothing

stepHandshake : ResponderMode → WorkerId → HandshakeAction → State → Maybe State
stepHandshake mode w act s with lookup w (admissions s)
... | nothing = nothing
... | just a = stepWorker mode w a act s

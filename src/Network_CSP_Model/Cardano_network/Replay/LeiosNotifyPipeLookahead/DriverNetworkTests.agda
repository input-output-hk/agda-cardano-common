{-# OPTIONS --guardedness #-}

-- Native paired traces and endpoint witnesses at the pinned driver's trace boundary.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkTests where

open import Data.Nat using (ℕ)
open import Data.Integer using (+_)
open import Data.Bool using (true; false)
open import Data.Fin using (Fin) renaming (zero to fzero)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
import Data.Maybe as Maybe
open import Data.Product using (_,_; proj₁)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (lo; hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyP exactParams using (sendLNP)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ℕ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ℕ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverExecution Notification ℕ notificationEq as Exec
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork exactParams ℕ as Native
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge exactParams ℕ as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverEndpointBridge exactParams ℕ as Endpoints
module B = Bridge.At S.nodeNext fzero fzero hi hi
module E = Endpoints.At S.nodeNext fzero fzero hi hi
open Native.At S.nodeNext fzero fzero hi hi
open Native using (module Traces)

-- A native offer supplies nontrivial exact hash, slot and size fields.
sample : Notification
sample = offer (43 , 47) 53

-- A fresh run may log both receives before their delayed matching Send records.
delayedRows : List D.Event
delayedRows = D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal sample)) ∷
  D.clientSend D.request ∷ D.serverSend (D.reply (S.normal sample)) ∷ []

-- Endpoint continuations and queues after those four records remain explicit.
delayedState : D.State
delayedState = D.pair
  (C.client C.poll (C.inspect (S.normal sample)) [] [] 1 (+ 0) false nothing)
  (S.state S.awaitNext 0 S.sent 0 false) [] [] nothing nothing nothing nothing

-- Commits and decode, rather than record reordering, justify the fresh source schedule.
delayed-source : D.Run S.nodeNext D.initial delayedRows delayedState
delayed-source =
  D.internal (D.clientCallback (D.continue {k = + 1000}) C.continueZero) $
  D.internal (D.clientInternal C.registerResponse) $
  D.internal (D.clientInternal (C.startResponse refl)) $
  D.internal (D.commitClient C.sentRequest) $
  D.internal (D.decodeServer (S.receiveRequest S.atFirst)) $
  D.visible (D.serverReceived (S.receiveRequest S.atFirst)) $
  D.internal (D.serverInternal S.admitted) $
  D.internal (D.serverInternal S.registered) $
  D.internal (D.serverInternal (S.claim refl)) $
  D.internal (D.serverCallback (S.choose refl refl)) $
  D.internal (D.commitServer (S.send refl)) $
  D.internal (D.decodeClient (C.receivedReply refl)) $
  D.visible (D.clientReceived (C.receivedReply refl)) $
  D.visible (D.clientSent C.sentRequest) $
  D.visible (D.serverSent (S.send refl)) D.stop

-- The supplied endpoint-tagged native record order is an actual paired PTree trace.
delayed-native : tree D.initial Traces.⟹∖√⟨ map encode delayedRows ⟩ tree delayedState
delayed-native = B.realize delayed-source

-- The same run has actual native client and server executions with matching local wire order.
delayed-endpoints : E.Endpoints D.initial delayedRows delayedState
delayed-endpoints = E.realize-endpoints delayed-source

-- Cancellation shutdown can receive Done before the server publishes its Send-Done record.
shutdownRows : List D.Event
shutdownRows = D.clientSend D.request ∷ D.serverRecv D.request ∷
  D.clientSend D.quit ∷ D.serverRecv D.quit ∷
  D.serverSend (D.reply S.canceled) ∷ D.clientRecv (D.reply S.canceled) ∷
  D.clientRecv D.done ∷ D.serverSend D.done ∷ []

-- Both endpoints close with the original client return value and empty transport/records.
shutdownState : D.State
shutdownState = D.pair (C.client C.closed C.idle [] [] 0 (+ 1) true (just 73))
  (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing

-- A selected reply drains after Quit with no application delivery on the stopped client.
finish-shutdown-source : (reply : S.Reply) → D.Run S.nodeNext
  (D.pair (C.client C.draining C.awaiting (C.quitMarker ∷ []) [] 2 (+ 0) true (just 73))
    (S.state S.flushing 0 (S.selected reply) 0 true) [] [] nothing nothing nothing nothing)
  (D.serverSend (D.reply reply) ∷ D.clientRecv (D.reply reply) ∷ D.clientRecv D.done ∷ D.serverSend D.done ∷ [])
  shutdownState
finish-shutdown-source reply =
  D.internal (D.commitServer (S.send refl)) $
  D.visible (D.serverSent (S.send refl)) $
  D.internal (D.serverInternal (S.retire refl)) $
  D.internal (D.serverInternal S.flush) $
  D.internal (D.serverInternal S.drained) $
  D.internal (D.decodeClient (C.receivedReply refl)) $
  D.visible (D.clientReceived (C.receivedReply refl)) $
  D.internal (D.clientInternal (C.discardReply refl)) $
  D.internal (D.clientInternal (C.countArrival refl)) $
  D.internal (D.clientInternal (C.publishResponse refl)) $
  D.internal (D.clientInternal (C.startMarker refl)) $
  D.internal (D.clientInternal (C.publishMarker refl)) $
  D.internal (D.clientInternal C.drainResult) $
  D.internal (D.clientInternal C.drainResult) $
  D.internal (D.clientInternal C.drained) $
  D.internal (D.commitServer S.finish) $
  D.internal (D.decodeClient C.receivedDone) $
  D.visible (D.clientReceived C.receivedDone) $
  D.visible (D.serverSent S.finish) D.stop

-- The full source schedule retains the Quit marker and drains cancellation before Done.
shutdown-source : D.Run S.nodeNext D.initial shutdownRows shutdownState
shutdown-source =
  D.internal (D.clientCallback (D.continue {k = + 1000}) C.continueZero) $
  D.internal (D.clientInternal C.registerResponse) $
  D.internal (D.clientInternal (C.startResponse refl)) $
  D.internal (D.commitClient C.sentRequest) $
  D.visible (D.clientSent C.sentRequest) $
  D.internal (D.decodeServer (S.receiveRequest S.atFirst)) $
  D.visible (D.serverReceived (S.receiveRequest S.atFirst)) $
  D.internal (D.serverInternal S.admitted) $
  D.internal (D.serverInternal S.registered) $
  D.internal (D.clientCallback D.terminate (C.stopRequested {x = 73})) $
  D.internal (D.clientInternal C.setStopBusy) $
  D.internal (D.clientInternal C.registerMarker) $
  D.internal (D.commitClient C.sentQuitBusy) $
  D.visible (D.clientSent C.sentQuitBusy) $
  D.internal (D.decodeServer (S.receiveQuit S.atNext)) $
  D.visible (D.serverReceived (S.receiveQuit S.atNext)) $
  D.internal (D.serverInternal S.setQuit) $
  D.internal (D.serverInternal (S.claim refl)) $
  D.internal (D.serverInternal (S.cancel refl)) $
  finish-shutdown-source S.canceled

-- Every native shutdown record retains its endpoint and exact packet fields.
shutdown-native : tree D.initial Traces.⟹∖√⟨ map encode shutdownRows ⟩ tree shutdownState
shutdown-native = B.realize shutdown-source

-- The closed paired state is accompanied by both native endpoint execution certificates.
shutdown-endpoints : E.Endpoints D.initial shutdownRows shutdownState
shutdown-endpoints = E.realize-endpoints shutdown-source

-- A normal reply chosen before Quit remains normal when sent after the true flag.
lateNormalRows : List D.Event
lateNormalRows = D.clientSend D.request ∷ D.serverRecv D.request ∷
  D.clientSend D.quit ∷ D.serverRecv D.quit ∷
  D.serverSend (D.reply (S.normal sample)) ∷ D.clientRecv (D.reply (S.normal sample)) ∷
  D.clientRecv D.done ∷ D.serverSend D.done ∷ []

-- Selection precedes Quit; transmission and stopped-client draining follow it.
late-normal-source : D.Run S.nodeNext D.initial lateNormalRows shutdownState
late-normal-source =
  D.internal (D.clientCallback (D.continue {k = + 1000}) C.continueZero) $
  D.internal (D.clientInternal C.registerResponse) $
  D.internal (D.clientInternal (C.startResponse refl)) $
  D.internal (D.commitClient C.sentRequest) $
  D.visible (D.clientSent C.sentRequest) $
  D.internal (D.decodeServer (S.receiveRequest S.atFirst)) $
  D.visible (D.serverReceived (S.receiveRequest S.atFirst)) $
  D.internal (D.serverInternal S.admitted) $
  D.internal (D.serverInternal S.registered) $
  D.internal (D.serverInternal (S.claim refl)) $
  D.internal (D.serverCallback (S.choose refl refl)) $
  D.internal (D.clientCallback D.terminate (C.stopRequested {x = 73})) $
  D.internal (D.clientInternal C.setStopBusy) $
  D.internal (D.clientInternal C.registerMarker) $
  D.internal (D.commitClient C.sentQuitBusy) $
  D.visible (D.clientSent C.sentQuitBusy) $
  D.internal (D.decodeServer (S.receiveQuit S.atNext)) $
  D.visible (D.serverReceived (S.receiveQuit S.atNext)) $
  D.internal (D.serverInternal S.setQuit) $
  finish-shutdown-source (S.normal sample)

-- The paired native target therefore permits the normal post-Quit reply from the source.
late-normal-native : tree D.initial Traces.⟹∖√⟨ map encode lateNormalRows ⟩ tree shutdownState
late-normal-native = B.realize late-normal-source

-- Both local native endpoints witness that same post-Quit normal exchange.
late-normal-endpoints : E.Endpoints D.initial lateNormalRows shutdownState
late-normal-endpoints = E.realize-endpoints late-normal-source

-- An uncommitted record is unavailable as a direct step from the fresh state.
uncommitted-send : next D.initial (encode (D.clientSend D.request)) ≡ nothing
uncommitted-send = refl

-- A pending selected offer is retained while its server Send record is delayed.
pendingOffer : D.State
pendingOffer = D.pair C.initial (S.state S.awaitNext 0 (S.selected (S.normal sample)) 0 false)
  [] [] nothing (just (D.reply (S.normal sample))) nothing nothing

-- Changing the payload on that pending Send cannot be justified by the same record.
changed-pending-size : next pendingOffer (encode (D.serverSend (D.reply (S.normal (offer (43 , 47) 54))))) ≡ nothing
changed-pending-size = refl

-- Clearing a recorded Send prevents an immediate second emission of that record.
no-duplicate-send : next
  (D.pair C.initial (S.state S.awaitNext 0 S.sent 0 false) [] [] nothing nothing nothing nothing)
  (encode (D.serverSend (D.reply (S.normal sample)))) ≡ nothing
no-duplicate-send = refl

-- The same payload cannot be moved to another endpoint direction by relabeling its row.
wrong-endpoint : next pendingOffer
  (Native.LTS.evLabel _ (Native.atServer (sendLNP fzero lo))
    (Native.serverPacket (D.reply (S.normal sample)))) ≡ nothing
wrong-endpoint = refl

-- A hidden wire-record callback cannot bypass the pending-record mechanism.
no-hidden-record-callback : Exec.hidden S.nodeNext D.initial (Exec.decide C.sendRequest) ≡ nothing
no-hidden-record-callback = refl

-- Two committed responses remain ordered while the client awaits its first receiver.
queuedResponses : D.State
queuedResponses = D.pair
  (C.client C.poll C.awaiting (C.responseJob ∷ []) [] 2 (+ 0) false nothing)
  (S.state S.awaitNext 0 S.idle 2 false) []
  (D.reply (S.normal sample) ∷ D.reply (S.normal (offer (59 , 61) 67)) ∷ [])
  nothing nothing nothing nothing

-- Decode removes precisely the first response and creates its pending Receive record.
decodedHead : D.State
decodedHead = D.pair (D.clientState queuedResponses) (D.serverState queuedResponses) []
  (D.reply (S.normal (offer (59 , 61) 67)) ∷ []) nothing nothing
  (just (D.reply (S.normal sample))) nothing

-- The certified native scheduler preserves FIFO head selection without skipping a packet.
fifo-head-decode : Maybe.map proj₁ (Exec.hidden S.nodeNext queuedResponses Exec.readClient) ≡ just decodedHead
fifo-head-decode = refl

-- The later packet cannot replace the head in the pending native receive record.
no-fifo-skip : next decodedHead (encode (D.clientRecv (D.reply (S.normal (offer (59 , 61) 67))))) ≡ nothing
no-fifo-skip = refl

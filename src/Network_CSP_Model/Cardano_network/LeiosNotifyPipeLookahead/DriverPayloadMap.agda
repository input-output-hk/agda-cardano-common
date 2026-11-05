{-# OPTIONS --safe #-}

-- Payload renaming preserves every generic source rule and its exact driver ordering.
module Cardano_network.LeiosNotifyPipeLookahead.DriverPayloadMap
  (Notification Return : Set) (rename : Notification → Notification) where

open import Data.List using (List; []; _∷_; _∷ʳ_; map)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe as Maybe
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; trans; sym; subst)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D

-- Only normal payloads change; Canceled retains its distinct protocol meaning.
reply : S.Reply → S.Reply
reply (S.normal value) = S.normal (rename value)
reply S.canceled = S.canceled

-- A selected server reply is renamed without changing sender control.
serverSender : S.Sender → S.Sender
serverSender (S.selected value) = S.selected (reply value)
serverSender S.idle = S.idle
serverSender S.claimed = S.claimed
serverSender S.sent = S.sent

-- All server counters, reader control and the shutdown flag are retained exactly.
serverState : S.State → S.State
serverState (S.state r w sender c flag) = S.state r w (serverSender sender) c flag

-- The only source server action data is its exact selected or sent reply.
serverAction : S.Action → S.Action
serverAction S.recvRequest = S.recvRequest
serverAction S.recvQuit = S.recvQuit
serverAction S.sendDone = S.sendDone
serverAction (S.nextReply value) = S.nextReply (reply value)
serverAction (S.sendReply value) = S.sendReply (reply value)

-- Generic and nodeNext callback guards depend on reply kind, never the opaque payload.
allowed : ∀ p value → S.allowed p value ≡ S.allowed p (reply value)
allowed p (S.normal _) = refl
allowed p S.canceled = refl

-- Every independent visible server rule survives arbitrary payload renaming.
serverStep : ∀ {p s a t} → S.Step p s a t → S.Step p (serverState s) (serverAction a) (serverState t)
serverStep (S.receiveRequest reading) = S.receiveRequest reading
serverStep (S.receiveQuit reading) = S.receiveQuit reading
serverStep (S.choose {m = value} active permitted) = S.choose active (trans (sym (allowed _ value)) permitted)
serverStep (S.send active) = S.send active
serverStep S.finish = S.finish

-- Hidden server steps inspect no Notification value and retain their original guards.
serverTau : ∀ {s t} → S.Tau s t → S.Tau (serverState s) (serverState t)
serverTau S.admitted = S.admitted
serverTau S.excessive = S.excessive
serverTau S.registered = S.registered
serverTau S.setQuit = S.setQuit
serverTau (S.claim active) = S.claim active
serverTau (S.cancel active) = S.cancel active
serverTau (S.retire active) = S.retire active
serverTau S.flush = S.flush
serverTau S.drained = S.drained
serverTau S.abort = S.abort

-- Client receiver control retains the exact renamed reply while it is inspected or handled.
clientReceiver : C.Receiver → C.Receiver
clientReceiver (C.inspect value) = C.inspect (reply value)
clientReceiver (C.handling value) = C.handling (reply value)
clientReceiver C.idle = C.idle
clientReceiver C.awaiting = C.awaiting
clientReceiver C.bumpArrival = C.bumpArrival
clientReceiver (C.publish marker) = C.publish marker

-- Registration/collection queues, arithmetic, callback Return and sender control stay unchanged.
clientState : C.State → C.State
clientState (C.client m r js rs n a flag value) = C.client m (clientReceiver r) js rs n a flag value

-- Depth decisions and Return values are fixed; only successful reply callbacks are renamed.
clientAction : C.Action → C.Action
clientAction (C.continue k) = C.continue k
clientAction (C.terminate value) = C.terminate value
clientAction (C.handled value) = C.handled (reply value)
clientAction (C.recvReply value) = C.recvReply (reply value)
clientAction C.sendRequest = C.sendRequest
clientAction C.sendQuit = C.sendQuit
clientAction C.recvDone = C.recvDone

-- Successful client callbacks and visible hooks retain their exact source target structure.
clientStep : ∀ {s a t} → C.Step s a t → C.Step (clientState s) (clientAction a) (clientState t)
clientStep C.continueZero = C.continueZero
clientStep (C.continueBelow bound) = C.continueBelow bound
clientStep (C.continueFull bound arrived) = C.continueFull bound arrived
clientStep C.stopRequested = C.stopRequested
clientStep C.sentRequest = C.sentRequest
clientStep C.sentQuitIdle = C.sentQuitIdle
clientStep C.sentQuitBusy = C.sentQuitBusy
clientStep (C.receivedReply active) = C.receivedReply active
clientStep (C.delivered active) = C.delivered active
clientStep C.receivedDone = C.receivedDone

-- Receiver scheduling and queue operations retain all non-payload fields definitionally.
clientTau : ∀ {s t} → C.Tau s t → C.Tau (clientState s) (clientState t)
clientTau C.registerResponse = C.registerResponse
clientTau C.setStopIdle = C.setStopIdle
clientTau C.setStopBusy = C.setStopBusy
clientTau C.registerMarker = C.registerMarker
clientTau C.optionalEmpty = C.optionalEmpty
clientTau C.optionalResult = C.optionalResult
clientTau C.blockingResult = C.blockingResult
clientTau C.adjustArrival = C.adjustArrival
clientTau C.drainResult = C.drainResult
clientTau C.drained = C.drained
clientTau (C.startResponse active) = C.startResponse active
clientTau (C.startMarker active) = C.startMarker active
clientTau (C.keepReply active) = C.keepReply active
clientTau (C.discardReply active) = C.discardReply active
clientTau (C.countArrival active) = C.countArrival active
clientTau (C.publishResponse active) = C.publishResponse active
clientTau (C.publishMarker active) = C.publishMarker active

-- Driver callback classification is preserved without revealing hidden callback labels.
clientCallback : ∀ {a} → D.ClientCallback a → D.ClientCallback (clientAction a)
clientCallback D.continue = D.continue
clientCallback D.terminate = D.terminate
clientCallback D.handled = D.handled

-- Server packets retain Done and rename only the payload of an exact reply.
serverMessage : D.ServerMessage → D.ServerMessage
serverMessage (D.reply value) = D.reply (reply value)
serverMessage D.done = D.done

-- Endpoint identity, direction, client commands and record order remain exact.
event : D.Event → D.Event
event (D.clientSend value) = D.clientSend value
event (D.serverRecv value) = D.serverRecv value
event (D.serverSend value) = D.serverSend (serverMessage value)
event (D.clientRecv value) = D.clientRecv (serverMessage value)

-- Renaming maps both transport FIFOs and all pending server-packet trace hooks.
state : D.State → D.State
state (D.pair c s cs sc pc ps rc rs) = D.pair (clientState c) (serverState s) cs
  (map serverMessage sc) pc (Maybe.map serverMessage ps) (Maybe.map serverMessage rc) rs

-- Empty fresh source states have no payload to change.
initial : state D.initial ≡ D.initial
initial = refl

-- Client command agency is unchanged by the payload map.
clientSendStep : ∀ {c m c′} → C.Step c (D.clientSendAction m) c′ →
  C.Step (clientState c) (D.clientSendAction m) (clientState c′)
clientSendStep {m = D.request} pr = clientStep pr
clientSendStep {m = D.quit} pr = clientStep pr

-- Server reader commands retain the same exact RequestNext/Quit agency.
serverRecvStep : ∀ {p s m s′} → S.Step p s (D.serverRecvAction m) s′ →
  S.Step p (serverState s) (D.serverRecvAction m) (serverState s′)
serverRecvStep {m = D.request} pr = serverStep pr
serverRecvStep {m = D.quit} pr = serverStep pr

-- Server sends remain justified by the exact renamed selected packet.
serverSendStep : ∀ {p s m s′} → S.Step p s (D.serverSendAction m) s′ →
  S.Step p (serverState s) (D.serverSendAction (serverMessage m)) (serverState s′)
serverSendStep {m = D.reply _} pr = serverStep pr
serverSendStep {m = D.done} pr = serverStep pr

-- Client receives use the renamed packet in the same receiver control state.
clientRecvStep : ∀ {c m c′} → C.Step c (D.clientRecvAction m) c′ →
  C.Step (clientState c) (D.clientRecvAction (serverMessage m)) (clientState c′)
clientRecvStep {m = D.reply _} pr = clientStep pr
clientRecvStep {m = D.done} pr = clientStep pr

-- Every visible driver hook is preserved with the same endpoint and renamed exact packet.
step : ∀ {p s row t} → D.Step p s row t → D.Step p (state s) (event row) (state t)
step (D.clientSent pr) = D.clientSent (clientSendStep pr)
step (D.serverSent pr) = D.serverSent (serverSendStep pr)
step (D.clientReceived pr) = D.clientReceived (clientRecvStep pr)
step (D.serverReceived pr) = D.serverReceived (serverRecvStep pr)

-- Transport append commutes with mapping and retains the packet FIFO order.
server-snoc : ∀ packets packet → map serverMessage (packets ∷ʳ packet) ≡ map serverMessage packets ∷ʳ serverMessage packet
server-snoc [] packet = refl
server-snoc (head ∷ packets) packet = cong (serverMessage head ∷_) (server-snoc packets packet)

-- Hidden commits, decodes, callbacks and source scheduling all survive payload renaming.
tau : ∀ {p s t} → D.Tau p s t → D.Tau p (state s) (state t)
tau (D.clientInternal pr) = D.clientInternal (clientTau pr)
tau (D.serverInternal pr) = D.serverInternal (serverTau pr)
tau (D.clientCallback callback pr) = D.clientCallback (clientCallback callback) (clientStep pr)
tau (D.serverCallback pr) = D.serverCallback (serverStep pr)
tau (D.commitClient pr) = D.commitClient (clientSendStep pr)
tau (D.commitServer {sc = sc} {m = packet} pr) rewrite server-snoc sc packet = D.commitServer (serverSendStep pr)
tau (D.decodeClient pr) = D.decodeClient (clientRecvStep pr)
tau (D.decodeServer pr) = D.decodeServer (serverRecvStep pr)

-- Whole finite driver executions are renamed without changing their length or scheduling.
run : ∀ {p s rows t} → D.Run p s rows t → D.Run p (state s) (map event rows) (state t)
run D.stop = D.stop
run (D.internal pr rest) = D.internal (tau pr) (run rest)
run (D.visible pr rest) = D.visible (step pr) (run rest)

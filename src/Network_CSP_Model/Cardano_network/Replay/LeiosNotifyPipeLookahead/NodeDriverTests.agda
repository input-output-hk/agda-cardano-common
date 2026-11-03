{-# OPTIONS --guardedness #-}

-- Fresh node-policy witnesses, retaining forecast/control inputs and credit effects.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverTests where

open import Data.Bool using (true; false)
open import Data.Empty using (⊥)
open import Data.Integer using (+_)
open import Data.Nat using (ℕ)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as Proof
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork exactParams ⊤ as Native
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverBridge exactParams as Bridge
open import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification
module B = Bridge.At fzero fzero hi hi
open B.N
open Native using (module Traces)

-- An exact native notification supplies hash, slot and size fields.
sample : Notification
sample = offer (43 , 47) 53

-- Both endpoints have closed without issuing a request or consuming a forecast.
idleStopped : State
idleStopped = nodeDriver
  (D.pair (C.client C.closed C.idle [] [] 0 (+ 0) true (just tt))
    (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing)
  Q.initial true false true

-- Terminate bypasses the unavailable forecast, exactly as the node checkDone callback does.
idle-actions : List Action
idle-actions = setTerminate true ∷ wire (D.clientSend D.quit) ∷
  wire (D.serverRecv D.quit) ∷ wire (D.clientRecv D.done) ∷ wire (D.serverSend D.done) ∷ []

-- Successful channel operations may deliver Done before its delayed server Send record.
idle-source : Run initial idle-actions idleStopped
idle-source =
  visible terminateInput $
  internal (terminateReady (Client.terminate C.stopRequested)) $
  internal (clientSchedule (Client.schedule C.setStopIdle)) $
  internal (transport (D.commitClient C.sentQuitIdle) refl) $
  visible (clientRecord sent (D.clientSent C.sentQuitIdle)) $
  internal (transport (D.decodeServer (S.receiveQuit S.atFirst)) refl) $
  visible (serverRecord received (D.serverReceived (S.receiveQuit S.atFirst))) $
  internal (serverSchedule (Server.schedule S.setQuit refl)) $
  internal (serverSchedule (Server.schedule S.drained refl)) $
  internal (transport (D.commitServer S.finish) refl) $
  internal (transport (D.decodeClient C.receivedDone) refl) $
  visible (clientRecord received (D.clientReceived C.receivedDone)) $
  visible (serverRecord sent (D.serverSent S.finish)) stop

-- The restricted policy witness has a real native paired wire realization.
idle-native : tree (driverState initial) Traces.⟹∖√⟨ map encode (wireRows idle-actions) ⟩
  tree (driverState idleStopped)
idle-native = B.realize idle-source

-- Normal operation requires an explicit forecast, admission and one eligible queue entry.
delayed-actions : List Action
delayed-actions = setForecast true ∷ wire (D.serverRecv D.request) ∷ eligible sample ∷
  wire (D.clientRecv (D.reply (S.normal sample))) ∷ wire (D.clientSend D.request) ∷
  wire (D.serverSend (D.reply (S.normal sample))) ∷ []

-- Credit is consumed on enqueue and the exact queued head is selected for the reply.
delayedState : State
delayedState = nodeDriver
  (D.pair (C.client C.poll (C.inspect (S.normal sample)) [] [] 1 (+ 0) false nothing)
    (S.state S.awaitNext 0 S.sent 0 false) [] [] nothing nothing nothing nothing)
  Q.initial true true false

-- Both Receive hooks can precede the delayed Send hooks under the actual node callbacks.
delayed-source : Run initial delayed-actions delayedState
delayed-source =
  visible forecastInput $
  internal (continueReady (Client.continueAtDepth C.continueZero)) $
  internal (clientSchedule (Client.schedule C.registerResponse)) $
  internal (clientSchedule (Client.schedule (C.startResponse refl))) $
  internal (transport (D.commitClient C.sentRequest) refl) $
  internal (transport (D.decodeServer (S.receiveRequest S.atFirst)) refl) $
  visible (serverRecord received (D.serverReceived (S.receiveRequest S.atFirst))) $
  internal (serverSchedule (Server.admitAccepted (Q.admitted (λ ())))) $
  internal (serverSchedule (Server.schedule S.registered refl)) $
  visible (applicationInput (Server.applicationOffer refl Q.enqueued)) $
  internal (serverSchedule (Server.schedule (S.claim refl) refl)) $
  internal (serverSchedule (Server.nextQueued Q.dequeued (S.choose refl refl))) $
  internal (transport (D.commitServer (S.send refl)) refl) $
  internal (transport (D.decodeClient (C.receivedReply refl)) refl) $
  visible (clientRecord received (D.clientReceived (C.receivedReply refl))) $
  visible (clientRecord sent (D.clientSent C.sentRequest)) $
  visible (serverRecord sent (D.serverSent (S.send refl))) stop

-- Canonical native fields and both local endpoint traces come from the same policy run.
delayed-native : tree (driverState initial) Traces.⟹∖√⟨ map encode (wireRows delayed-actions) ⟩
  tree (driverState delayedState)
delayed-native = B.realize delayed-source

-- The endpoint theorem preserves the exact local wire orders of this node witness.
delayed-endpoints : B.E.Endpoints (driverState initial) (wireRows delayed-actions) (driverState delayedState)
delayed-endpoints = B.endpoints delayed-source

-- A successful normal handler publishes its result separately from the wire receive.
handledState : State
handledState = nodeDriver
  (D.pair (C.client C.poll C.idle [] (C.responseToken ∷ []) 1 (+ 1) false nothing)
    (S.state S.awaitNext 0 S.sent 0 false) [] [] nothing nothing nothing nothing)
  Q.initial true true false

-- Ledger/relay validation success is supplied explicitly, with no fabricated wire record.
handled-source : Run delayedState (handledNormal sample ∷ []) handledState
handled-source =
  internal (clientSchedule (Client.schedule (C.keepReply refl))) $
  visible (normalHandler (Client.handled (C.delivered refl))) $
  internal (clientSchedule (Client.schedule (C.countArrival refl))) $
  internal (clientSchedule (Client.schedule (C.publishResponse refl))) stop

-- Wire-only realization hides the successful handler but retains its changed endpoint state.
handled-native : tree (driverState delayedState) Traces.⟹∖√⟨ [] ⟩ tree (driverState handledState)
handled-native = B.realize handled-source

-- Wire shutdown leaves unused callback credits untouched, independently of drained jobs.
closedAt : ℕ → State
closedAt free = nodeDriver
  (D.pair (C.client C.closed C.idle [] [] 0 (+ 1) true (just tt))
    (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing)
  (Q.credits free []) true true true

-- An unused admission credit remains after cancellation with no eligible offers.
shutdownState : State
shutdownState = closedAt 1

-- A reply already selected across Quit is sent unchanged and drained before Done.
finish-stopped : (reply : S.Reply) (free : ℕ) → Run
  (nodeDriver
    (D.pair (C.client C.draining C.awaiting (C.quitMarker ∷ []) [] 2 (+ 0) true (just tt))
      (S.state S.flushing 0 (S.selected reply) 0 true) [] [] nothing nothing nothing nothing)
    (Q.credits free []) true true true)
  (wire (D.serverSend (D.reply reply)) ∷ wire (D.clientRecv (D.reply reply)) ∷
    wire (D.clientRecv D.done) ∷ wire (D.serverSend D.done) ∷ []) (closedAt free)
finish-stopped reply free =
  internal (transport (D.commitServer (S.send refl)) refl) $
  visible (serverRecord sent (D.serverSent (S.send refl))) $
  internal (serverSchedule (Server.schedule (S.retire refl) refl)) $
  internal (serverSchedule (Server.schedule S.flush refl)) $
  internal (serverSchedule (Server.schedule S.drained refl)) $
  internal (transport (D.decodeClient (C.receivedReply refl)) refl) $
  visible (clientRecord received (D.clientReceived (C.receivedReply refl))) $
  internal (clientSchedule (Client.schedule (C.discardReply refl))) $
  internal (clientSchedule (Client.schedule (C.countArrival refl))) $
  internal (clientSchedule (Client.schedule (C.publishResponse refl))) $
  internal (clientSchedule (Client.schedule (C.startMarker refl))) $
  internal (clientSchedule (Client.schedule (C.publishMarker refl))) $
  internal (clientSchedule (Client.schedule C.drainResult)) $
  internal (clientSchedule (Client.schedule C.drainResult)) $
  internal (clientSchedule (Client.schedule C.drained)) $
  internal (transport (D.commitServer S.finish) refl) $
  internal (transport (D.decodeClient C.receivedDone) refl) $
  visible (clientRecord received (D.clientReceived C.receivedDone)) $
  visible (serverRecord sent (D.serverSent S.finish)) stop

-- A single admitted request can be canceled without any eligible normal notification.
shutdown-actions : List Action
shutdown-actions = setForecast true ∷ wire (D.clientSend D.request) ∷ wire (D.serverRecv D.request) ∷
  setTerminate true ∷ wire (D.clientSend D.quit) ∷ wire (D.serverRecv D.quit) ∷
  wire (D.serverSend (D.reply S.canceled)) ∷ wire (D.clientRecv (D.reply S.canceled)) ∷
  wire (D.clientRecv D.done) ∷ wire (D.serverSend D.done) ∷ []

-- Stop is published before this cancellation is handled, so the receiver drains it.
shutdown-source : Run initial shutdown-actions shutdownState
shutdown-source =
  visible forecastInput $
  internal (continueReady (Client.continueAtDepth C.continueZero)) $
  internal (clientSchedule (Client.schedule C.registerResponse)) $
  internal (clientSchedule (Client.schedule (C.startResponse refl))) $
  internal (transport (D.commitClient C.sentRequest) refl) $
  visible (clientRecord sent (D.clientSent C.sentRequest)) $
  internal (transport (D.decodeServer (S.receiveRequest S.atFirst)) refl) $
  visible (serverRecord received (D.serverReceived (S.receiveRequest S.atFirst))) $
  internal (serverSchedule (Server.admitAccepted (Q.admitted (λ ())))) $
  internal (serverSchedule (Server.schedule S.registered refl)) $
  visible terminateInput $
  internal (terminateReady (Client.terminate C.stopRequested)) $
  internal (clientSchedule (Client.schedule C.setStopBusy)) $
  internal (clientSchedule (Client.schedule C.registerMarker)) $
  internal (transport (D.commitClient C.sentQuitBusy) refl) $
  visible (clientRecord sent (D.clientSent C.sentQuitBusy)) $
  internal (transport (D.decodeServer (S.receiveQuit S.atNext)) refl) $
  visible (serverRecord received (D.serverReceived (S.receiveQuit S.atNext))) $
  internal (serverSchedule (Server.schedule S.setQuit refl)) $
  internal (serverSchedule (Server.schedule (S.claim refl) refl)) $
  internal (serverSchedule (Server.schedule (S.cancel refl) refl)) $
  finish-stopped S.canceled 1

-- The fresh cancellation witness realizes the same exact native packet history.
shutdown-native : tree (driverState initial) Traces.⟹∖√⟨ map encode (wireRows shutdown-actions) ⟩
  tree (driverState shutdownState)
shutdown-native = B.realize shutdown-source

-- Eligibility and selection precede Quit, while the normal Send and Receive follow it.
late-normal-actions : List Action
late-normal-actions = setForecast true ∷ wire (D.clientSend D.request) ∷ wire (D.serverRecv D.request) ∷
  eligible sample ∷ setTerminate true ∷ wire (D.clientSend D.quit) ∷ wire (D.serverRecv D.quit) ∷
  wire (D.serverSend (D.reply (S.normal sample))) ∷ wire (D.clientRecv (D.reply (S.normal sample))) ∷
  wire (D.clientRecv D.done) ∷ wire (D.serverSend D.done) ∷ []

-- The node queue supplies the exact normal packet retained across the true Quit flag.
late-normal-source : Run initial late-normal-actions (closedAt 0)
late-normal-source =
  visible forecastInput $
  internal (continueReady (Client.continueAtDepth C.continueZero)) $
  internal (clientSchedule (Client.schedule C.registerResponse)) $
  internal (clientSchedule (Client.schedule (C.startResponse refl))) $
  internal (transport (D.commitClient C.sentRequest) refl) $
  visible (clientRecord sent (D.clientSent C.sentRequest)) $
  internal (transport (D.decodeServer (S.receiveRequest S.atFirst)) refl) $
  visible (serverRecord received (D.serverReceived (S.receiveRequest S.atFirst))) $
  internal (serverSchedule (Server.admitAccepted (Q.admitted (λ ())))) $
  internal (serverSchedule (Server.schedule S.registered refl)) $
  visible (applicationInput (Server.applicationOffer refl Q.enqueued)) $
  internal (serverSchedule (Server.schedule (S.claim refl) refl)) $
  internal (serverSchedule (Server.nextQueued Q.dequeued (S.choose refl refl))) $
  visible terminateInput $
  internal (terminateReady (Client.terminate C.stopRequested)) $
  internal (clientSchedule (Client.schedule C.setStopBusy)) $
  internal (clientSchedule (Client.schedule C.registerMarker)) $
  internal (transport (D.commitClient C.sentQuitBusy) refl) $
  visible (clientRecord sent (D.clientSent C.sentQuitBusy)) $
  internal (transport (D.decodeServer (S.receiveQuit S.atNext)) refl) $
  visible (serverRecord received (D.serverReceived (S.receiveQuit S.atNext))) $
  internal (serverSchedule (Server.schedule S.setQuit refl)) $
  finish-stopped (S.normal sample) 0

-- The normal post-Quit reply remains permitted under the combined production policies.
late-normal-native : tree (driverState initial) Traces.⟹∖√⟨ map encode (wireRows late-normal-actions) ⟩
  tree (driverState (closedAt 0))
late-normal-native = B.realize late-normal-source

-- Final callback accounting records the unused credit instead of equating it with pipe occupancy.
unused-credit : Q.free (queueState shutdownState) ≡ 1
unused-credit = refl

-- The generic callback escape hatch is excluded from the node transport selector.
no-callback-bypass : transportAllowed true
  (D.clientCallback {s = S.initial} {cs = []} {sc = []} {pc = nothing} {ps = nothing}
    {rc = nothing} {rs = nothing} D.continue (C.continueZero {r = C.idle} {js = []}
      {rs = []} {a = + 0} {q = false} {v = nothing} {k = + 1000})) ≡ false
no-callback-bypass = refl

-- Normal continuation cannot change the initial client while forecast readiness is false.
forecast-blocked : ∀ {c′} → Tau initial (nodeDriver (withClient D.initial c′) Q.initial true false false) → ⊥
forecast-blocked (clientSchedule (Client.schedule ()))
forecast-blocked (serverSchedule (Server.schedule () _))
forecast-blocked (transport (D.clientInternal _) ())
forecast-blocked (transport (D.serverInternal _) ())
forecast-blocked (transport (D.clientCallback _ _) ())
forecast-blocked (transport (D.serverCallback _) ())

-- The Cancel handler fault is represented for partial states without claiming fresh reachability.
faultStart : State
faultStart = nodeDriver
  (D.pair (C.client C.poll (C.handling S.canceled) [] [] 1 (+ 0) false nothing)
    S.initial [] [] nothing nothing nothing nothing) Q.initial true false false

-- Rejecting an unexpected Cancel records local failure rather than successful Done.
fault-source : Run faultStart (rejectedCancel ∷ [])
  (nodeDriver (driverState faultStart) Q.initial false false false)
fault-source = visible (canceledHandlerExit (Client.rejectedCancel refl refl)) stop

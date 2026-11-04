{-# OPTIONS --guardedness #-}

-- Fresh production-policy/native Done race and native client shutdown applications.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownNativeTests where

open import Data.Bool using (true; false)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Fin using () renaming (zero to fzero)
open import Data.Empty using (⊥)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as Projection
import Cardano_network.LeiosNotifyPipeLookahead.NodeShutdown Notification as Policy
import Cardano_network.LeiosNotifyPipeLookahead.DriverShutdown Notification ⊤ as Shutdown
import Cardano_network.LeiosNotifyPipeLookahead.ClientShutdown Notification ⊤ as Stopping
import Cardano_network.LeiosNotifyPipeLookahead.ServerShutdown Notification as Final
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork exactParams ⊤ as Native
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverNetworkBridge exactParams ⊤ as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownBridge exactParams ⊤ as Safety

-- Native labels use the same production fixture endpoint coordinates.
module Tree = Native.At S.nodeNext fzero fzero hi hi
-- Existing introduction builds actual native steps/traces for the supplied source run.
module B = Bridge.At S.nodeNext fzero fzero hi hi
-- New inversion obtains safety facts from those native executions.
module Proof = Safety.At S.nodeNext fzero fzero hi hi
open Native using (module LTS; module Traces)

-- The fresh node has decoded Done while the server Send-Done hook is pending.
before-done : Node.State
before-done = Node.nodeDriver
  (D.pair (C.client C.awaitDone C.idle [] [] 0 (+ 0) true (just tt))
    (S.state S.doneReady 0 S.idle 0 true) [] [] nothing (just D.done) (just D.done) nothing)
  Q.initial true false true

-- Forecast is unavailable; the production termination path bypasses it.
actions : List Node.Action
actions = Node.setTerminate true ∷ Node.wire (D.clientSend D.quit) ∷ Node.wire (D.serverRecv D.quit) ∷ []

-- Every prefix step is justified by the production client/server and actual transport rules.
prefix : Node.Run Node.initial actions before-done
prefix =
  Node.visible Node.terminateInput $
  Node.internal (Node.terminateReady (Client.terminate C.stopRequested)) $
  Node.internal (Node.clientSchedule (Client.schedule C.setStopIdle)) $
  Node.internal (Node.transport (D.commitClient C.sentQuitIdle) refl) $
  Node.visible (Node.clientRecord Node.sent (D.clientSent C.sentQuitIdle)) $
  Node.internal (Node.transport (D.decodeServer (S.receiveQuit S.atFirst)) refl) $
  Node.visible (Node.serverRecord Node.received (D.serverReceived (S.receiveQuit S.atFirst))) $
  Node.internal (Node.serverSchedule (Server.schedule S.setQuit refl)) $
  Node.internal (Node.serverSchedule (Server.schedule S.drained refl)) $
  Node.internal (Node.transport (D.commitServer S.finish) refl) $
  Node.internal (Node.transport (D.decodeClient C.receivedDone) refl) Node.stop

-- Done receive closes the client without silently publishing the server trace hook.
after-done : Node.State
after-done = Node.nodeDriver
  (D.pair (C.client C.closed C.idle [] [] 0 (+ 0) true (just tt))
    (S.state S.doneReady 0 S.idle 0 true) [] [] nothing (just D.done) nothing nothing)
  Q.initial true false true

-- This last node wire operation has exactly the expected target.
done-step : Node.Step before-done (Node.wire (D.clientRecv D.done)) after-done
done-step = Node.clientRecord Node.received (D.clientReceived C.receivedDone)

-- Production-policy completion certifies both peers' work and the exact unit return.
node-completed : Shutdown.Completed (Node.driverState after-done)
node-completed = Policy.client-done-completed prefix done-step

-- The same fresh prefix is an actual native execution.
native-prefix : Tree.tree D.initial Traces.⟹∖√⟨ map Tree.encode (Node.wireRows actions) ⟩
  Tree.tree (Node.driverState before-done)
native-prefix = B.realize (Projection.driver prefix)

-- The last native visible step uses the same full-packet Done decoding as the bridge.
native-done-step : Tree.tree (Node.driverState before-done)
  LTS.─[ LTS.ev (LTS.evl (Tree.encode (D.clientRecv D.done))) ]─► Tree.tree (Node.driverState after-done)
native-done-step = B.visible-intro (B.Canonical.decode-encode (D.clientRecv D.done)) (D.clientReceived C.receivedDone)

-- Native inversion establishes completion without assuming an unproved source execution.
native-completed : Σ[ raw ∈ D.State ]
  (Tree.tree (Node.driverState after-done) ≡ Tree.tree raw × Shutdown.Completed raw)
native-completed = Proof.received-done native-prefix (B.Canonical.decode-encode (D.clientRecv D.done)) native-done-step

-- This reachable completed-work state still has a real unpublished Send-Done hook.
pending-hook : D.pendingServerSend (Node.driverState after-done) ≢ nothing
pending-hook ()

-- Its native future cannot publish another client RequestNext.
no-later-request : ∀ {es P e R} → Tree.tree (Node.driverState after-done) Traces.⟹∖√⟨ es ⟩ P →
  Tree.decode e ≡ just (D.clientSend D.request) → P LTS.─[ LTS.ev (LTS.evl e) ]─► R → ⊥
no-later-request = Proof.no-request-after refl

-- Publishing the delayed Done hook then closes the already-drained server.
closed : D.State
closed = D.pair (D.clientState (Node.driverState after-done))
  (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing

-- The final server record is an actual native operation after client completion.
native-server-step : Tree.tree (Node.driverState after-done)
  LTS.─[ LTS.ev (LTS.evl (Tree.encode (D.serverSend D.done))) ]─► Tree.tree closed
native-server-step = B.visible-intro (B.Canonical.decode-encode (D.serverSend D.done)) (D.serverSent S.finish)

-- The native Send-Done theorem retains both final-phase guarantees.
native-server-final : Σ[ raw ∈ D.State ] (Tree.tree closed ≡ Tree.tree raw ×
  Final.Final (D.serverState (Node.driverState after-done)) × Final.Final (D.serverState raw))
native-server-final = Proof.sent-done (B.Canonical.decode-encode (D.serverSend D.done)) native-server-step

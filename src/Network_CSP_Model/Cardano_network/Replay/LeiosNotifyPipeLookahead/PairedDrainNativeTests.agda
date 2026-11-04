{-# OPTIONS --guardedness #-}

-- Full native/runtime closure at fresh production-policy prefixes, including delayed Send-Quit.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PairedDrainNativeTests where

open import Data.Bool using (true; false)
open import Data.Integer using (+_)
open import Data.Nat using (ℕ; _≤_)
open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Data.Fin using () renaming (zero to fzero)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverNetwork exactParams ⊤ as Raw
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as Projection
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownProgress Notification ⊤ as P
import Cardano_network.LeiosNotifyPipeLookahead.RuntimeProgress Notification ⊤ as R
import Cardano_network.LeiosNotifyPipeLookahead.ShutdownWork Notification ⊤ as Work
import Cardano_network.LeiosNotifyPipeLookahead.SchedulingCost Notification ⊤ as Cost
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PairedDrainBridge exactParams ⊤ as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.RunRuntime Notification ⊤ as Runtime
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ShutdownNativeTests as Fixture
open Raw using (module Traces)

-- Production callback policy and endpoint coordinates agree with the existing exact fixture.
module Proof = Bridge.At S.nodeNext fzero fzero hi hi

-- The general theorem applies at an actual fresh production/native Done handoff.
native-completion : Proof.Certificate (Node.driverState Fixture.before-done)
native-completion = Proof.from-source (Projection.driver Fixture.prefix) (refl , refl)

-- Actual native prefix inversion retains its target and general clean-continuation theorem.
native-inversion : Σ[ raw ∈ D.State ]
  (Proof.Tree.tree (Node.driverState Fixture.before-done) ≡ Proof.Tree.tree raw ×
    (Work.BothStopping raw → Proof.Certificate raw))
native-inversion = Proof.from-native Fixture.native-prefix

-- The physical Quit reaches the server before its pending client Send trace hook.
late : Node.State
late = Node.nodeDriver
  (D.pair (C.client (C.writingQuit false) C.idle [] [] 0 (+ 0) true (just tt))
    (S.state S.signalQuit 0 S.idle 0 false) [] [] (just D.quit) nothing nothing nothing)
  Q.initial true false true

-- The production termination branch bypasses unavailable forecast and preserves original row order.
late-prefix : Node.Run Node.initial
  (Node.setTerminate true ∷ Node.wire (D.serverRecv D.quit) ∷ []) late
late-prefix =
  Node.visible Node.terminateInput $
  Node.internal (Node.terminateReady (Client.terminate C.stopRequested)) $
  Node.internal (Node.clientSchedule (Client.schedule C.setStopIdle)) $
  Node.internal (Node.transport (D.commitClient C.sentQuitIdle) refl) $
  Node.internal (Node.transport (D.decodeServer (S.receiveQuit S.atFirst)) refl) $
  Node.visible (Node.serverRecord Node.received (D.serverReceived (S.receiveQuit S.atFirst))) Node.stop

-- Full closure now follows from fresh reachability, with no supplied structural progress premise.
late-certificate : Proof.Certificate (Node.driverState late)
late-certificate = Proof.from-source (Projection.driver late-prefix) (refl , refl)

-- The retained source return is unit and every queue/hook is actually empty at the target.
closed : Node.State
closed = Node.nodeDriver
  (D.pair (C.client C.closed C.idle [] [] 0 (+ 0) true (just tt))
    (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing)
  Q.initial true false true

-- This production-policy path records server Done before the delayed client Quit Send.
late-drain : Node.Run late
  (Node.wire (D.serverSend D.done) ∷ Node.wire (D.clientSend D.quit) ∷ Node.wire (D.clientRecv D.done) ∷ []) closed
late-drain =
  Node.internal (Node.serverSchedule (Server.schedule S.setQuit refl)) $
  Node.internal (Node.serverSchedule (Server.schedule S.drained refl)) $
  Node.internal (Node.transport (D.commitServer S.finish) refl) $
  Node.visible (Node.serverRecord Node.sent (D.serverSent S.finish)) $
  Node.visible (Node.clientRecord Node.sent (D.clientSent C.sentQuitIdle)) $
  Node.internal (Node.transport (D.decodeClient C.receivedDone) refl) $
  Node.visible (Node.clientRecord Node.received (D.clientReceived C.receivedDone)) Node.stop

-- The concrete full production-policy target meets the general paired clean predicate.
clean-target : P.Clean (Node.driverState closed)
clean-target = P.clean

-- This actual policy path is also an actual native continuation with its original record sequence.
late-native : Proof.Tree.tree (Node.driverState late) Traces.⟹∖√⟨ map Proof.Tree.encode
  (D.serverSend D.done ∷ D.clientSend D.quit ∷ D.clientRecv D.done ∷ []) ⟩ Proof.Tree.tree (Node.driverState closed)
late-native = Proof.B.realize (Projection.driver late-drain)

-- The full runtime theorem is inhabited for this concrete seven-operation production-policy path.
late-runtime : Σ[ k ∈ ℕ ] Σ[ rows ∈ List D.Event ] Σ[ trace ∈
  (Proof.Tree.tree (R.state (Runtime.execution (Projection.driver late-drain)) 0)
    Traces.⟹∖√⟨ map Proof.Tree.encode rows ⟩ Proof.Tree.tree (R.state (Runtime.execution (Projection.driver late-drain)) k)) ]
  (0 ≤ k × P.Clean (R.state (Runtime.execution (Projection.driver late-drain)) k) ×
    Proof.Bound.steps trace ≤ Cost.rank (Node.driverState late))
late-runtime = Proof.runtime-from-source (Runtime.execution (Projection.driver late-drain))
  (Runtime.responsive P.Clean (Projection.driver late-drain) clean-target)
  (Runtime.no-failure (Projection.driver late-drain)) (Runtime.maximal (Projection.driver late-drain))
  0 (Projection.driver late-prefix) (refl , refl)

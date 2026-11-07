{-# OPTIONS --guardedness #-}

-- Full-policy native witnesses; explicit input values do not certify deployment truth.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverNetworkTests where

open import Data.Bool using (true; false)
open import Data.Fin using () renaming (zero to fzero)
open import Data.List using (List; []; _∷_; map; mapMaybe)
open import Data.Maybe using (just; nothing)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (Notification; notificationEq)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverNetwork exactParams as Native
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverNetworkBridge exactParams as Bridge
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverTests as Source
import Cardano_network.Replay.LeiosNotifyPipeLookahead.RuntimeCheck Notification notificationEq as Replay
module N = Native.At fzero fzero hi hi
module B = Bridge.At fzero fzero hi hi
open Native using (module LTS; module Traces)

-- Termination still bypasses an unavailable forecast in the full native policy tree.
idle-native : N.tree Node.initial Traces.⟹∖√⟨ map N.encode Source.idle-actions ⟩ N.tree Source.idleStopped
idle-native = B.realize Source.idle-source

-- The inverse applies to an actual native path and reconstructs all input witnesses.
idle-reconstructed : Σ[ inputs ∈ List Node.Action ] Σ[ target ∈ Node.State ]
  (B.Matches (map N.encode Source.idle-actions) inputs × Node.Run Node.initial inputs target ×
   N.tree Source.idleStopped ≡ N.tree target)
idle-reconstructed = B.sound idle-native

-- Fresh request/eligible-offer progress retains Receive-before-delayed-Send ordering.
delayed-native : N.tree Node.initial Traces.⟹∖√⟨ map N.encode Source.delayed-actions ⟩ N.tree Source.delayedState
delayed-native = B.realize Source.delayed-source

-- Application validation success stays visible on the policy channel rather than becoming wire traffic.
handled-native : N.tree Source.delayedState
  Traces.⟹∖√⟨ N.encode (Node.handledNormal Source.sample) ∷ [] ⟩ N.tree Source.handledState
handled-native = B.realize Source.handled-source

-- Request, Quit, Canceled and Done follow the existing full queue/credit policy witness.
cancellation-native : N.tree Node.initial Traces.⟹∖√⟨ map N.encode Source.shutdown-actions ⟩ N.tree Source.shutdownState
cancellation-native = B.realize Source.shutdown-source

-- An inhabited full node-policy wire witness also has a concrete native realization.
cancellation-wire : B.NativeWireTrace Node.initial (Node.wireRows Source.shutdown-actions)
cancellation-wire = B.source-wire-to-native
  (Source.shutdown-actions , Source.shutdownState , Source.shutdown-source , refl)

-- Inverting that witness reconstructs full source inputs instead of generic-only acceptance.
cancellation-wire-source : B.SourceWire Node.initial (Node.wireRows Source.shutdown-actions)
cancellation-wire-source = B.native-wire-to-source cancellation-wire

-- A normal reply selected across Quit remains permitted with its exact original payload.
late-normal-native : N.tree Node.initial Traces.⟹∖√⟨ map N.encode Source.late-normal-actions ⟩ N.tree (Source.closedAt 0)
late-normal-native = B.realize Source.late-normal-source

-- Deleting explicit policy inputs retains the original complete wire list, including delayed hooks.
wire-order : mapMaybe N.observe (map N.encode Source.shutdown-actions) ≡ Node.wireRows Source.shutdown-actions
wire-order = B.wire-observation (B.canonical-matches Source.shutdown-actions)

-- Native decoder roundtrip retains actual eligible notification fields.
eligible-fields : N.decode (N.encode (Node.eligible Source.sample)) ≡ just (Node.eligible Source.sample)
eligible-fields = B.decode-encode _

-- The forecast guard is still enforced before any continuation can register a receiver.
forecast-blocked : Replay.evaluate Node.initial (Replay.hidden Replay.continue ∷ []) ≡ nothing
forecast-blocked = refl

-- Explicit environment updates can return to the initial state without any wire record.
forecast-cycle-actions : List Node.Action
forecast-cycle-actions = Node.setForecast true ∷ Node.setForecast false ∷ []

-- This actual source cycle changes no protocol state and asserts no deployment occurrence.
forecast-cycle-source : Node.Run Node.initial forecast-cycle-actions Node.initial
forecast-cycle-source = Node.visible Node.forecastInput (Node.visible Node.forecastInput Node.stop)

-- The full-policy native tree faithfully retains both visible environment updates.
forecast-cycle-native : N.tree Node.initial
  Traces.⟹∖√⟨ map N.encode forecast-cycle-actions ⟩ N.tree Node.initial
forecast-cycle-native = B.realize forecast-cycle-source

-- Hiding policy inputs creates a zero-wire cycle, outside actual native Tau accessibility.
forecast-cycle-wire : mapMaybe N.observe (map N.encode forecast-cycle-actions) ≡ []
forecast-cycle-wire = B.wire-observation (B.canonical-matches forecast-cycle-actions)

-- An uncommitted visible request cannot be invented by the new native wire wrapper.
uncommitted-wire : N.next Node.initial (N.encode (Node.wire (D.clientSend D.request))) ≡ nothing
uncommitted-wire = refl

-- This source fault is a partial-state witness, not a fresh honest-paired reachability claim.
faultTarget : Node.State
faultTarget = Node.nodeDriver (Node.driverState Source.faultStart) Q.initial false false false

-- Unexpected Cancel handling is an actual native input step ending in local client failure.
fault-native : N.tree Source.faultStart
  Traces.⟹∖√⟨ N.encode Node.rejectedCancel ∷ [] ⟩ N.tree faultTarget
fault-native = B.realize Source.fault-source

-- The supplied-schedule interpreter now covers the same previously omitted failure action.
fault-replay : Replay.evaluate Source.faultStart (Replay.action Node.rejectedCancel ∷ []) ≡ just faultTarget
fault-replay = refl

-- A failed client cannot emit further local wire records.
fault-client-blocked : N.next faultTarget (N.encode (Node.wire (D.clientSend D.request))) ≡ nothing
fault-client-blocked = refl

-- A separate partial state isolates server continuation after client failure.
serverAfterFault : Node.State
serverAfterFault = Node.nodeDriver
  (D.pair C.initial (S.state S.doneReady 0 S.idle 0 true) [] [] nothing (just D.done) nothing nothing)
  Q.initial false false false

-- The failed-client flag is preserved while the server records its already committed Done.
serverAfterDone : Node.State
serverAfterDone = Node.nodeDriver
  (D.pair C.initial (S.state S.closed 0 S.idle 0 true) [] [] nothing nothing nothing nothing)
  Q.initial false false false

-- Local failure never invents whole-product termination or disables the surviving server.
server-progress-after-fault : N.tree serverAfterFault
  LTS.─[ LTS.ev (LTS.evl (N.encode (Node.wire (D.serverSend D.done)))) ]─► N.tree serverAfterDone
server-progress-after-fault = B.visible-intro (B.decode-encode _)
  (Node.serverRecord Node.sent (D.serverSent S.finish))

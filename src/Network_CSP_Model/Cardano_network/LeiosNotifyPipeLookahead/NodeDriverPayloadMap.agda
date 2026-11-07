{-# OPTIONS --safe #-}

-- Arbitrary total payload renaming preserves the full node policy and its wire core.
module Cardano_network.LeiosNotifyPipeLookahead.NodeDriverPayloadMap
  (Notification : Set) (rename : Notification → Notification) where

open import Data.Bool using (Bool; false)
open import Data.List using (List; []; _∷_; map)
open import Data.List.Properties using (map-++)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst₂)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core
import Cardano_network.LeiosNotifyPipeLookahead.DriverPayloadMap as Generic

-- Existing generic driver rules, payload maps and initial-state theorem are reused directly.
module Driver = Generic Notification ⊤ rename

-- Queue order and duplicate positions are retained while every opaque notification is renamed.
queueState : Q.State → Q.State
queueState (Q.credits free queued) = Q.credits free (map rename queued)

-- Admission decisions remain exact; only queue offer/take values are renamed.
queueAction : Q.Action → Q.Action
queueAction Q.admitAccepted = Q.admitAccepted
queueAction Q.admitExcessive = Q.admitExcessive
queueAction (Q.offer message) = Q.offer (rename message)
queueAction (Q.take message) = Q.take (rename message)

-- Free credit is unaffected by payload changes, even for arbitrary raw counter values.
queue-free : ∀ queue → Q.free (queueState queue) ≡ Q.free queue
queue-free (Q.credits _ _) = refl

-- Every actual credit/queue transaction preserves its original guard and mapped exact target.
queueStep : ∀ {s a t} → Q.Step s a t → Q.Step (queueState s) (queueAction a) (queueState t)
queueStep (Q.admitted unequal) = Q.admitted unequal
queueStep (Q.excessive equal) = Q.excessive equal
queueStep (Q.enqueued {qs = queued} {m = message}) rewrite map-++ rename queued (message ∷ []) = Q.enqueued
queueStep Q.dropped = Q.dropped
queueStep Q.dequeued = Q.dequeued

-- Peer control and credit storage are renamed together, without changing server policy.
serverState : Server.State → Server.State
serverState (Server.node peer queue) = Server.node (Driver.serverState peer) (queueState queue)

-- Wire agency and application offers retain their distinct source action families.
serverAction : Server.Action → Server.Action
serverAction (Server.wire action) = Server.wire (Driver.serverAction action)
serverAction (Server.offer message) = Server.offer (rename message)

-- The existing wire whitelist is preserved under the generic server-action map.
serverWire : ∀ {a} → Server.Wire a → Server.Wire (Driver.serverAction a)
serverWire Server.request = Server.request
serverWire Server.quit = Server.quit
serverWire Server.reply = Server.reply
serverWire Server.done = Server.done

-- Source server records and eligible queue transactions remain independent actual rules.
serverStep : ∀ {s a t} → Server.Step s a t → Server.Step (serverState s) (serverAction a) (serverState t)
serverStep (Server.peerRecord agency proof) = Server.peerRecord (serverWire agency) (Driver.serverStep proof)
serverStep (Server.applicationOffer active proof) = Server.applicationOffer active (queueStep proof)

-- Routine classification inspects only the unchanged generic operation constructor.
server-routine : ∀ {s t} (proof : S.Tau s t) → Server.routine (Driver.serverTau proof) ≡ Server.routine proof
server-routine S.admitted = refl
server-routine S.excessive = refl
server-routine S.registered = refl
server-routine S.setQuit = refl
server-routine (S.claim _) = refl
server-routine (S.cancel _) = refl
server-routine (S.retire _) = refl
server-routine S.flush = refl
server-routine S.drained = refl
server-routine S.abort = refl

-- Atomic node-server callbacks keep their queue and generic peer evidence synchronized.
serverTau : ∀ {s t} → Server.Tau s t → Server.Tau (serverState s) (serverState t)
serverTau (Server.schedule proof allowed) = Server.schedule (Driver.serverTau proof) (trans (server-routine proof) allowed)
serverTau (Server.admitAccepted proof) = Server.admitAccepted (queueStep proof)
serverTau (Server.admitExcessive proof) = Server.admitExcessive (queueStep proof)
serverTau (Server.nextQueued proof selected) = Server.nextQueued (queueStep proof) (Driver.serverStep selected)

-- Local failure remains a separate absorbing constructor with its exact mapped client state.
clientState : Client.State → Client.State
clientState (Client.running state) = Client.running (Driver.clientState state)
clientState (Client.unexpectedCancel state) = Client.unexpectedCancel (Driver.clientState state)

-- Forecast depth, unit return and Cancel failure labels are unchanged.
clientAction : Client.Action → Client.Action
clientAction (Client.wire action) = Client.wire (Driver.clientAction action)
clientAction Client.forecastAllows = Client.forecastAllows
clientAction (Client.stopRequested value) = Client.stopRequested value
clientAction (Client.handledNormal message) = Client.handledNormal (rename message)
clientAction Client.handlerRejectedCancel = Client.handlerRejectedCancel

-- Node-client wire records cannot become application callbacks after renaming.
clientWire : ∀ {a} → Client.Wire a → Client.Wire (Driver.clientAction a)
clientWire Client.request = Client.request
clientWire Client.quit = Client.quit
clientWire Client.reply = Client.reply
clientWire Client.done = Client.done

-- Every node-client rule retains its fixed policy guards and actual selected message.
clientStep : ∀ {s a t} → Client.Step s a t → Client.Step (clientState s) (clientAction a) (clientState t)
clientStep (Client.wireRecord agency proof) = Client.wireRecord (clientWire agency) (Driver.clientStep proof)
clientStep (Client.continueAtDepth proof) = Client.continueAtDepth (Driver.clientStep proof)
clientStep (Client.terminate proof) = Client.terminate (Driver.clientStep proof)
clientStep (Client.handled proof) = Client.handled (Driver.clientStep proof)
clientStep (Client.rejectedCancel {c = C.client m _ js rs n a q v} active refl) = Client.rejectedCancel active refl

-- Scheduling uses the existing generic client renaming theorem without changing flags or counters.
clientTau : ∀ {s t} → Client.Tau s t → Client.Tau (clientState s) (clientState t)
clientTau (Client.schedule proof) = Client.schedule (Driver.clientTau proof)

-- Full state mapping preserves client failure and both external readiness snapshots.
nodeState : Node.State → Node.State
nodeState (Node.nodeDriver raw queue live forecast halt) =
  Node.nodeDriver (Driver.state raw) (queueState queue) live forecast halt

-- Only actual wire/application notification values change in full source actions.
nodeAction : Node.Action → Node.Action
nodeAction (Node.wire row) = Node.wire (Driver.event row)
nodeAction (Node.setForecast ready) = Node.setForecast ready
nodeAction (Node.setTerminate requested) = Node.setTerminate requested
nodeAction (Node.eligible message) = Node.eligible (rename message)
nodeAction (Node.handledNormal message) = Node.handledNormal (rename message)
nodeAction Node.rejectedCancel = Node.rejectedCancel

-- Endpoint actor classification survives every mapped client wire record.
clientRow : ∀ {row} → Node.ClientRow row → Node.ClientRow (Driver.event row)
clientRow Node.sent = Node.sent
clientRow Node.received = Node.received

-- Server records retain their endpoint actor as well as exact renamed packet values.
serverRow : ∀ {row} → Node.ServerRow row → Node.ServerRow (Driver.event row)
serverRow Node.sent = Node.sent
serverRow Node.received = Node.received

-- All original visible node rules map, including real queue transactions and abnormal exit.
nodeStep : ∀ {s a t} → Node.Step s a t → Node.Step (nodeState s) (nodeAction a) (nodeState t)
nodeStep (Node.clientRecord agency proof) = Node.clientRecord (clientRow agency) (Driver.step proof)
nodeStep (Node.serverRecord agency proof) = Node.serverRecord (serverRow agency) (Driver.step proof)
nodeStep Node.forecastInput = Node.forecastInput
nodeStep Node.terminateInput = Node.terminateInput
nodeStep (Node.applicationInput {raw = D.pair _ _ _ _ _ _ _ _} proof) = Node.applicationInput (serverStep proof)
nodeStep (Node.normalHandler {raw = D.pair _ _ _ _ _ _ _ _} proof) = Node.normalHandler (clientStep proof)
nodeStep (Node.canceledHandlerExit {raw = D.pair _ _ _ _ _ _ _ _} proof) = Node.canceledHandlerExit (clientStep proof)

-- Physical transport classification depends on operation family and live flag, never payload identity.
transport-allowed : ∀ live {s t} (proof : D.Tau S.nodeNext s t) →
  Node.transportAllowed live (Driver.tau proof) ≡ Node.transportAllowed live proof
transport-allowed live (D.clientInternal _) = refl
transport-allowed live (D.serverInternal _) = refl
transport-allowed live (D.clientCallback _ _) = refl
transport-allowed live (D.serverCallback _) = refl
transport-allowed live (D.commitClient _) = refl
transport-allowed live (D.commitServer {sc = packets} {m = packet} proof) rewrite Driver.server-snoc packets packet = refl
transport-allowed live (D.decodeClient _) = refl
transport-allowed live (D.decodeServer _) = refl

-- Full node scheduling preserves queue coupling, fixed forecast depth and restricted transport.
nodeTau : ∀ {s t} → Node.Tau s t → Node.Tau (nodeState s) (nodeState t)
nodeTau (Node.clientSchedule {raw = D.pair _ _ _ _ _ _ _ _} proof) = Node.clientSchedule (clientTau proof)
nodeTau (Node.continueReady {raw = D.pair _ _ _ _ _ _ _ _} proof) = Node.continueReady (clientStep proof)
nodeTau (Node.terminateReady {raw = D.pair _ _ _ _ _ _ _ _} proof) = Node.terminateReady (clientStep proof)
nodeTau (Node.serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} proof) = Node.serverSchedule (serverTau proof)
nodeTau (Node.transport proof allowed) = Node.transport (Driver.tau proof) (trans (transport-allowed _ proof) allowed)

-- Every finite full source run retains its scheduling and mapped action order.
nodeRun : ∀ {s actions t} → Node.Run s actions t → Node.Run (nodeState s) (map nodeAction actions) (nodeState t)
nodeRun Node.stop = Node.stop
nodeRun (Node.internal proof rest) = Node.internal (nodeTau proof) (nodeRun rest)
nodeRun (Node.visible proof rest) = Node.visible (nodeStep proof) (nodeRun rest)

-- Fresh full source state has no notification payload to change.
node-initial : nodeState Node.initial ≡ Node.initial
node-initial = refl

-- Reduced state mapping preserves every protocol field except the renamed opaque payloads.
coreState : Core.State → Core.State
coreState (Core.core raw queue live) = Core.core (Driver.state raw) (queueState queue) live

-- Mapping commutes with all chosen external snapshots, without erasing the internal stop flag.
nodeState-embed : ∀ state forecast halt → nodeState (Core.embed state forecast halt) ≡ Core.embed (coreState state) forecast halt
nodeState-embed (Core.core _ _ _) _ _ = refl

-- The actual reduced free-credit guard is unchanged by payload mapping.
core-free : ∀ state → Q.free (Core.queueState (coreState state)) ≡ Q.free (Core.queueState state)
core-free (Core.core _ queue _) = queue-free queue

-- Exact source wire guards transport through the canonical representative without new assumptions.
coreVisible : ∀ {s row t} → Core.Visible s row t → Core.Visible (coreState s) (Driver.event row) (coreState t)
coreVisible {s} {row} {t} proof =
  subst₂ (λ before after → Node.Step before (Node.wire (Driver.event row)) after)
    (nodeState-embed s false false) (nodeState-embed t false false) (nodeStep proof)

-- Constructor preservation leaves the basis-restricted offer family definitionally visible.
coreTau : ∀ {s t} → Core.Tau s t → Core.Tau (coreState s) (coreState t)
coreTau {s} {t} (Core.operational {forecast = forecast} {halt = halt} proof) =
  Core.operational {forecast = forecast} {halt = halt}
    (subst₂ Node.Tau (nodeState-embed s forecast halt) (nodeState-embed t forecast halt) (nodeTau proof))
coreTau {s} {t} (Core.offered {msg = message} proof nonzero) = Core.offered {msg = rename message}
  (subst₂ (λ before after → Node.Step before (Node.eligible (rename message)) after)
    (nodeState-embed s false false) (nodeState-embed t false false) (nodeStep proof))
  (λ equal → nonzero (trans (sym (core-free s)) equal))
coreTau {s} {t} (Core.handled {msg = message} proof) = Core.handled {msg = rename message}
  (subst₂ (λ before after → Node.Step before (Node.handledNormal (rename message)) after)
    (nodeState-embed s false false) (nodeState-embed t false false) (nodeStep proof))
coreTau {s} {t} (Core.rejected proof) = Core.rejected
  (subst₂ (λ before after → Node.Step before Node.rejectedCancel after)
    (nodeState-embed s false false) (nodeState-embed t false false) (nodeStep proof))

-- Reduced wire executions retain every exact mapped wire occurrence and their full target state.
coreRun : ∀ {s rows t} → Core.Run s rows t → Core.Run (coreState s) (map Driver.event rows) (coreState t)
coreRun Core.stop = Core.stop
coreRun (Core.internal proof rest) = Core.internal (coreTau proof) (coreRun rest)
coreRun (Core.visible proof rest) = Core.visible (coreVisible proof) (coreRun rest)

-- The fresh reduced state is fixed for every total renaming, without an inhabitance premise.
core-initial : coreState Core.initial ≡ Core.initial
core-initial = refl

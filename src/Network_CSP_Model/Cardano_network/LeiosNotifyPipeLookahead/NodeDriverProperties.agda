{-# OPTIONS --safe #-}

-- Policy-preserving projections of the combined node, with no converse claim.
module Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties (Notification : Set) where

open import Data.Bool using (true; false)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (_≤_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeClientModel Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.NodeModel Notification 1000 as Server
import Cardano_network.LeiosNotifyPipeLookahead.NodeProperties Notification 1000 as SP
import Cardano_network.LeiosNotifyPipeLookahead.CreditModel Notification 1000 as Q
open import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification

-- Each permitted hidden node transaction is an actual generic driver transaction.
driver-tau : ∀ {s t} → Tau s t → D.Tau S.nodeNext (driverState s) (driverState t)
driver-tau (clientSchedule {raw = D.pair _ _ _ _ _ _ _ _} (Client.schedule pr)) = D.clientInternal pr
driver-tau (continueReady {raw = D.pair _ _ _ _ _ _ _ _} (Client.continueAtDepth pr)) = D.clientCallback D.continue pr
driver-tau (terminateReady {raw = D.pair _ _ _ _ _ _ _ _} (Client.terminate pr)) = D.clientCallback D.terminate pr
driver-tau (serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} (Server.schedule pr _)) = D.serverInternal pr
driver-tau (serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} (Server.admitAccepted _)) = D.serverInternal S.admitted
driver-tau (serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} (Server.admitExcessive _)) = D.serverInternal S.excessive
driver-tau (serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} (Server.nextQueued _ pr)) = D.serverCallback pr
driver-tau (transport pr _) = pr

-- Erasing policy inputs gives a generic driver execution with every wire row intact.
driver : ∀ {s actions t} → Run s actions t →
  D.Run S.nodeNext (driverState s) (wireRows actions) (driverState t)
driver stop = D.stop
driver (internal pr run) = D.internal (driver-tau pr) (driver run)
driver (visible (clientRecord _ pr) run) = D.visible pr (driver run)
driver (visible (serverRecord _ pr) run) = D.visible pr (driver run)
driver (visible forecastInput run) = driver run
driver (visible terminateInput run) = driver run
driver (visible (applicationInput _) run) = driver run
driver (visible (normalHandler {raw = D.pair _ _ _ _ _ _ _ _} (Client.handled pr)) run) =
  D.internal (D.clientCallback D.handled pr) (driver run)
driver (visible (canceledHandlerExit _) run) = driver run

-- Transport changes packet buffers and pending hooks, never server callback state.
server-transport : ∀ {raw raw′ live} (pr : D.Tau S.nodeNext raw raw′) →
  transportAllowed live pr ≡ true → D.serverState raw ≡ D.serverState raw′
server-transport (D.clientInternal _) ()
server-transport (D.serverInternal _) ()
server-transport (D.clientCallback _ _) ()
server-transport (D.serverCallback _) ()
server-transport (D.commitClient _) _ = refl
server-transport (D.commitServer _) _ = refl
server-transport (D.decodeClient _) _ = refl
server-transport (D.decodeServer _) _ = refl

-- Every combined schedule retains a concrete node server execution and its credit queue.
server : ∀ {s actions t} → Run s actions t →
  Σ[ inputs ∈ List Server.Action ] Server.Run (serverView s) inputs (serverView t)
server stop = [] , Server.stop
server (internal (clientSchedule {raw = D.pair _ _ _ _ _ _ _ _} _) run) = server run
server (internal (continueReady {raw = D.pair _ _ _ _ _ _ _ _} _) run) = server run
server (internal (terminateReady {raw = D.pair _ _ _ _ _ _ _ _} _) run) = server run
server (internal (serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} pr) run) with server run
... | inputs , source = inputs , Server.internal pr source
server (internal (transport pr allowed) run) rewrite server-transport pr allowed = server run
server (visible (clientRecord sent (D.clientSent _)) run) = server run
server (visible (clientRecord received (D.clientReceived _)) run) = server run
server (visible (serverRecord sent (D.serverSent {m = msg} pr)) run) with server run
... | inputs , source = Server.wire (D.serverSendAction msg) ∷ inputs ,
  Server.visible (Server.peerRecord (send-wire msg) pr) source
  where
  -- The message constructor identifies the exact server wire action.
  send-wire : ∀ msg → Server.Wire (D.serverSendAction msg)
  send-wire (D.reply _) = Server.reply
  send-wire D.done = Server.done
server (visible (serverRecord received (D.serverReceived {m = msg} pr)) run) with server run
... | inputs , source = Server.wire (D.serverRecvAction msg) ∷ inputs ,
  Server.visible (Server.peerRecord (receive-wire msg) pr) source
  where
  -- Request and Quit retain distinct server receive agency.
  receive-wire : ∀ msg → Server.Wire (D.serverRecvAction msg)
  receive-wire D.request = Server.request
  receive-wire D.quit = Server.quit
server (visible forecastInput run) = server run
server (visible terminateInput run) = server run
server (visible (applicationInput {msg = msg} pr) run) with server run
... | inputs , source = Server.offer msg ∷ inputs , Server.visible pr source
server (visible (normalHandler {raw = D.pair _ _ _ _ _ _ _ _} _) run) = server run
server (visible (canceledHandlerExit _) run) = server run

-- The production admission invariant holds even with transport and client interleavings.
initial-free-bounded : ∀ {actions t} → Run initial actions t → Q.free (queueState t) ≤ 1000
initial-free-bounded run with server run
... | inputs , source = SP.initial-free-bounded source

-- Transport retains the local client control even when its trace hook is pending.
client-transport : ∀ {raw raw′ live} (pr : D.Tau S.nodeNext raw raw′) →
  transportAllowed live pr ≡ true → D.clientState raw ≡ D.clientState raw′
client-transport (D.clientInternal _) ()
client-transport (D.serverInternal _) ()
client-transport (D.clientCallback _ _) ()
client-transport (D.serverCallback _) ()
client-transport (D.commitClient _) _ = refl
client-transport (D.commitServer _) _ = refl
client-transport (D.decodeClient _) _ = refl
client-transport (D.decodeServer _) _ = refl

-- The exact command constructor supplies its node client wire classification.
client-send-wire : ∀ msg → Client.Wire (D.clientSendAction msg)
client-send-wire D.request = Client.request
client-send-wire D.quit = Client.quit

-- Reply and Done retain their separate client receive transitions.
client-receive-wire : ∀ msg → Client.Wire (D.clientRecvAction msg)
client-receive-wire (D.reply _) = Client.reply
client-receive-wire D.done = Client.done

-- The projection preserves node-specific normal handlers and the abnormal Cancel exit.
client : ∀ {s actions t} → Run s actions t →
  Σ[ inputs ∈ List Client.Action ] Client.Run (clientView s) inputs (clientView t)
client stop = [] , Client.stop
client (internal (clientSchedule {raw = D.pair _ _ _ _ _ _ _ _} pr) run) with client run
... | inputs , source = inputs , Client.internal pr source
client (internal (continueReady {raw = D.pair _ _ _ _ _ _ _ _} pr) run) with client run
... | inputs , source = Client.forecastAllows ∷ inputs , Client.visible pr source
client (internal (terminateReady {raw = D.pair _ _ _ _ _ _ _ _} pr) run) with client run
... | inputs , source = Client.stopRequested _ ∷ inputs , Client.visible pr source
client (internal (serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} {live = true} _) run) = client run
client (internal (serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} {live = false} _) run) = client run
client (internal (transport {live = true} pr allowed) run)
  rewrite client-transport pr allowed = client run
client (internal (transport {live = false} pr allowed) run)
  rewrite client-transport pr allowed = client run
client (visible (clientRecord sent (D.clientSent {m = msg} pr)) run) with client run
... | inputs , source = Client.wire (D.clientSendAction msg) ∷ inputs ,
  Client.visible (Client.wireRecord (client-send-wire msg) pr) source
client (visible (clientRecord received (D.clientReceived {m = msg} pr)) run) with client run
... | inputs , source = Client.wire (D.clientRecvAction msg) ∷ inputs ,
  Client.visible (Client.wireRecord (client-receive-wire msg) pr) source
client (visible (serverRecord {live = true} sent (D.serverSent _)) run) = client run
client (visible (serverRecord {live = false} sent (D.serverSent _)) run) = client run
client (visible (serverRecord {live = true} received (D.serverReceived _)) run) = client run
client (visible (serverRecord {live = false} received (D.serverReceived _)) run) = client run
client (visible (forecastInput {live = true}) run) = client run
client (visible (forecastInput {live = false}) run) = client run
client (visible (terminateInput {live = true}) run) = client run
client (visible (terminateInput {live = false}) run) = client run
client (visible (applicationInput {live = true} _) run) = client run
client (visible (applicationInput {live = false} _) run) = client run
client (visible (normalHandler {raw = D.pair _ _ _ _ _ _ _ _} {msg = msg} pr) run) with client run
... | inputs , source = Client.handledNormal msg ∷ inputs , Client.visible pr source
client (visible (canceledHandlerExit pr) run) with client run
... | inputs , source = Client.handlerRejectedCancel ∷ inputs , Client.visible pr source

-- Visible work cannot revive an exited local client.
step-dead : ∀ {s a t} → Step s a t → clientAlive s ≡ false → clientAlive t ≡ false
step-dead (clientRecord _ _) ()
step-dead (serverRecord _ _) dead = dead
step-dead forecastInput dead = dead
step-dead terminateInput dead = dead
step-dead (applicationInput _) dead = dead
step-dead (normalHandler _) ()
step-dead (canceledHandlerExit _) ()

-- Remote scheduling and transport also preserve local driver exit.
tau-dead : ∀ {s t} → Tau s t → clientAlive s ≡ false → clientAlive t ≡ false
tau-dead (clientSchedule _) ()
tau-dead (continueReady _) ()
tau-dead (terminateReady _) ()
tau-dead (serverSchedule _) dead = dead
tau-dead (transport _ _) dead = dead

-- Visible remote/input work leaves the failed client's exact control state unchanged.
step-dead-client : ∀ {s a t} → Step s a t → clientAlive s ≡ false →
  D.clientState (driverState s) ≡ D.clientState (driverState t)
step-dead-client (clientRecord _ _) ()
step-dead-client (serverRecord sent (D.serverSent _)) _ = refl
step-dead-client (serverRecord received (D.serverReceived _)) _ = refl
step-dead-client forecastInput _ = refl
step-dead-client terminateInput _ = refl
step-dead-client (applicationInput _) _ = refl
step-dead-client (normalHandler _) ()
step-dead-client (canceledHandlerExit _) ()

-- Hidden remote operations cannot resume client control after abnormal exit.
tau-dead-client : ∀ {s t} → Tau s t → clientAlive s ≡ false →
  D.clientState (driverState s) ≡ D.clientState (driverState t)
tau-dead-client (clientSchedule _) ()
tau-dead-client (continueReady _) ()
tau-dead-client (terminateReady _) ()
tau-dead-client (serverSchedule {raw = D.pair _ _ _ _ _ _ _ _} _) _ = refl
tau-dead-client (transport pr allowed) _ = client-transport pr allowed

-- All continuations of an exited client retain its failure tag and exact local state.
failed-client-stays : ∀ {s actions t} → Run s actions t → clientAlive s ≡ false →
  (clientAlive t ≡ false) × (D.clientState (driverState s) ≡ D.clientState (driverState t))
failed-client-stays stop dead = dead , refl
failed-client-stays (internal pr run) dead with failed-client-stays run (tau-dead pr dead)
... | later , same = later , trans (tau-dead-client pr dead) same
failed-client-stays (visible pr run) dead with failed-client-stays run (step-dead pr dead)
... | later , same = later , trans (step-dead-client pr dead) same

-- Every client wire record requires a live local driver, independently of remote progress.
client-row-requires-live : ∀ {s row t} → Step s (wire row) t → ClientRow row → clientAlive s ≡ true
client-row-requires-live (clientRecord _ _) _ = refl
client-row-requires-live (serverRecord sent _) ()
client-row-requires-live (serverRecord received _) ()

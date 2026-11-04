{-# OPTIONS --safe #-}

-- Production policy inherits client shutdown and both-peer Done work guarantees.
module Cardano_network.LeiosNotifyPipeLookahead.NodeShutdown (Notification : Set) where

open import Data.Bool using (true)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.ClientAccounting Notification ⊤ as Accounting
import Cardano_network.LeiosNotifyPipeLookahead.ClientShutdown Notification ⊤ as Client
import Cardano_network.LeiosNotifyPipeLookahead.DriverShutdown Notification ⊤ as Driver
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as Properties

-- The combined policy uses the pinned node's responder callback contract.
module Paired = Driver.For S.nodeNext

-- Credits, forecast/termination inputs and abnormal-exit tags preserve corrected client work.
client-accounted : ∀ {actions t} → Node.Run Node.initial actions t → Accounting.Accounted (D.clientState (Node.driverState t))
client-accounted run = Paired.client-accounted (Properties.driver run)

-- Arbitrary node continuations cannot restart requests once client shutdown starts.
client-stays-stopping : ∀ {s actions t} → Node.Run s actions t →
  Client.stopping (C.main (D.clientState (Node.driverState s))) ≡ true →
  Client.stopping (C.main (D.clientState (Node.driverState t))) ≡ true
client-stays-stopping run = Paired.client-stays-stopping (Properties.driver run)

-- The node wire profile also excludes new client RequestNext records during shutdown.
no-client-request : ∀ {s t} → Client.stopping (C.main (D.clientState (Node.driverState s))) ≡ true →
  Node.Step s (Node.wire (D.clientSend D.request)) t → ⊥
no-client-request stopped (Node.clientRecord _ pr) = Driver.no-client-request stopped pr
no-client-request _ (Node.serverRecord () _)

-- Production queue/transport scheduling cannot select a new normal after flag publication.
new-selection-after-flag : ∀ {s t msg} → Node.Tau s t →
  S.quitFlag (D.serverState (Node.driverState s)) ≡ true →
  S.sender (D.serverState (Node.driverState s)) ≡ S.claimed →
  S.sender (D.serverState (Node.driverState t)) ≡ S.selected msg → msg ≡ S.canceled
new-selection-after-flag pr = Driver.new-selection-after-flag (Properties.driver-tau pr)

-- The published flag persists through all production-policy and input interleavings.
server-stays-flagged : ∀ {s actions t} → Node.Run s actions t →
  S.quitFlag (D.serverState (Node.driverState s)) ≡ true →
  S.quitFlag (D.serverState (Node.driverState t)) ≡ true
server-stays-flagged run = Paired.server-stays-flagged (Properties.driver run)

-- A fresh node Done receive certifies empty client work and a drained actual responder.
client-done-completed : ∀ {actions s t} → Node.Run Node.initial actions s →
  Node.Step s (Node.wire (D.clientRecv D.done)) t → Driver.Completed (Node.driverState t)
client-done-completed prefix (Node.clientRecord _ pr) = Paired.client-done-completed (Properties.driver prefix) pr
client-done-completed _ (Node.serverRecord () _)

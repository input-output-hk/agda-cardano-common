{-# OPTIONS --safe #-}

-- Production node-policy runs inherit exact server and transport accounting.
module Cardano_network.LeiosNotifyPipeLookahead.NodeConservation
  (Notification : Set) where

open import Data.List using (List; []; mapMaybe)
open import Data.Maybe using (nothing)
open import Data.Nat using (_+_)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Notification ⊤ as Transport
import Cardano_network.LeiosNotifyPipeLookahead.ServerConservation Notification as Server
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification ⊤ as Projection
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverProperties Notification as Properties
-- Extract the actual server execution at the pinned node callback contract.
module Endpoint = Projection.For S.nodeNext

-- Environment inputs, credit transactions and abnormal exit do not invent packets.
transport : ∀ {actions t} → Node.Run Node.initial actions t →
  Transport.Balanced (Transport.observe (Node.wireRows actions) Transport.empty) (Node.driverState t)
transport run = Transport.initial-conservation (Properties.driver run)

-- The counted server actions project to precisely the actual server wire records.
server-accounting : ∀ {actions t} → Node.Run Node.initial actions t →
  Σ[ serverActions ∈ List S.Action ]
    (S.Run S.nodeNext S.initial serverActions (D.serverState (Node.driverState t)) ×
     mapMaybe Projection.serverWire serverActions ≡ Projection.serverRows (Node.wireRows actions) ×
     Server.requests serverActions ≡ Server.replies serverActions + S.owed (D.serverState (Node.driverState t)))
server-accounting run with Endpoint.server (Properties.driver run)
... | serverActions , source , matching = serverActions , source , matching , Server.initial-balance source

-- Settled command histories match without requiring the node to terminate.
commands-settled : ∀ {actions t} → Node.Run Node.initial actions t →
  D.pendingClientSend (Node.driverState t) ≡ nothing →
  D.pendingServerRecv (Node.driverState t) ≡ nothing → D.clientToServer (Node.driverState t) ≡ [] →
  Transport.clientSends (Transport.observe (Node.wireRows actions) Transport.empty) ≡
  Transport.serverReceives (Transport.observe (Node.wireRows actions) Transport.empty)
commands-settled run = Transport.commands-settled (Properties.driver run)

-- A Canceled/normal reply and final Done retain their exact order and multiplicity.
responses-settled : ∀ {actions t} → Node.Run Node.initial actions t →
  D.pendingServerSend (Node.driverState t) ≡ nothing →
  D.pendingClientRecv (Node.driverState t) ≡ nothing → D.serverToClient (Node.driverState t) ≡ [] →
  Transport.serverSends (Transport.observe (Node.wireRows actions) Transport.empty) ≡
  Transport.clientReceives (Transport.observe (Node.wireRows actions) Transport.empty)
responses-settled run = Transport.responses-settled (Properties.driver run)

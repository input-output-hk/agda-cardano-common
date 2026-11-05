{-# OPTIONS --safe #-}

-- Independent endpoint languages are necessary, never sufficient, for an exact paired driver prefix.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.LocalPrecheck
  (Notification Return : Set) where

open import Data.List using (List; []; _∷_; map; mapMaybe)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_×_; _,_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (Dec; yes; no)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification Return as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification Return as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverProjections Notification Return as Projection
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Client Notification as CW
import Cardano_network.LeiosNotifyPipeLookahead.Wire.Server Notification as SW
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientQuotient Notification Return as Client
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerQuotient Notification as Server
module ClientObservation = CW.Observation Return

-- Client agency is unchanged and every exact reply value is reused without a payload conversion.
clientWire : Rows.ClientRow → CW.Wire
clientWire (Rows.sendCommand D.request) = CW.request
clientWire (Rows.sendCommand D.quit) = CW.quit
clientWire (Rows.receiveResponse D.done) = CW.done
clientWire (Rows.receiveResponse (D.reply value)) = CW.reply value

-- The inverse structural map witnesses losslessness rather than a message-kind abstraction.
clientRow : CW.Wire → Rows.ClientRow
clientRow CW.request = Rows.sendCommand D.request
clientRow CW.quit = Rows.sendCommand D.quit
clientRow CW.done = Rows.receiveResponse D.done
clientRow (CW.reply value) = Rows.receiveResponse (D.reply value)

-- Every typed client occurrence returns to its original constructor and exact payload.
client-roundtrip : ∀ row → clientRow (clientWire row) ≡ row
client-roundtrip (Rows.sendCommand D.request) = refl
client-roundtrip (Rows.sendCommand D.quit) = refl
client-roundtrip (Rows.receiveResponse D.done) = refl
client-roundtrip (Rows.receiveResponse (D.reply _)) = refl

-- Server agency retains the corresponding exact command or response without changing its fields.
serverWire : Rows.ServerRow → SW.Wire
serverWire (Rows.receiveCommand D.request) = SW.request
serverWire (Rows.receiveCommand D.quit) = SW.quit
serverWire (Rows.sendResponse D.done) = SW.done
serverWire (Rows.sendResponse (D.reply value)) = SW.reply value

-- Server conversion also has an explicit exact structural inverse.
serverRow : SW.Wire → Rows.ServerRow
serverRow SW.request = Rows.receiveCommand D.request
serverRow SW.quit = Rows.receiveCommand D.quit
serverRow SW.done = Rows.sendResponse D.done
serverRow (SW.reply value) = Rows.sendResponse (D.reply value)

-- The local server view loses neither repeated rows nor any information inside a reply.
server-roundtrip : ∀ row → serverRow (serverWire row) ≡ row
server-roundtrip (Rows.receiveCommand D.request) = refl
server-roundtrip (Rows.receiveCommand D.quit) = refl
server-roundtrip (Rows.sendResponse D.done) = refl
server-roundtrip (Rows.sendResponse (D.reply _)) = refl

-- This proof-only decoder observes one endpoint of an already typed product trace, not arbitrary raw input.
clientDecode : D.Event → Maybe CW.Wire
clientDecode (D.clientSend D.request) = just CW.request
clientDecode (D.clientSend D.quit) = just CW.quit
clientDecode (D.clientRecv D.done) = just CW.done
clientDecode (D.clientRecv (D.reply value)) = just (CW.reply value)
clientDecode _ = nothing

-- The complementary proof decoder retains only the declared server endpoint records.
serverDecode : D.Event → Maybe SW.Wire
serverDecode (D.serverRecv D.request) = just SW.request
serverDecode (D.serverRecv D.quit) = just SW.quit
serverDecode (D.serverSend D.done) = just SW.done
serverDecode (D.serverSend (D.reply value)) = just (SW.reply value)
serverDecode _ = nothing

-- Existing client source observation agrees exactly with the local quotient projection.
client-observation : ∀ actions →
  mapMaybe clientDecode (mapMaybe Projection.clientWire actions) ≡ ClientObservation.wire actions
client-observation [] = refl
client-observation (C.sendRequest ∷ actions) rewrite client-observation actions = refl
client-observation (C.sendQuit ∷ actions) rewrite client-observation actions = refl
client-observation (C.recvReply _ ∷ actions) rewrite client-observation actions = refl
client-observation (C.recvDone ∷ actions) rewrite client-observation actions = refl
client-observation (C.continue _ ∷ actions) = client-observation actions
client-observation (C.terminate _ ∷ actions) = client-observation actions
client-observation (C.handled _ ∷ actions) = client-observation actions

-- Existing server source observation deletes only callback selections, preserving each exact wire reply.
server-observation : ∀ actions →
  mapMaybe serverDecode (mapMaybe Projection.serverWire actions) ≡ SW.wire actions
server-observation [] = refl
server-observation (S.recvRequest ∷ actions) rewrite server-observation actions = refl
server-observation (S.recvQuit ∷ actions) rewrite server-observation actions = refl
server-observation (S.sendReply _ ∷ actions) rewrite server-observation actions = refl
server-observation (S.sendDone ∷ actions) rewrite server-observation actions = refl
server-observation (S.nextReply _ ∷ actions) = server-observation actions

-- A merged product trace yields exactly the supplied client order, including receive-before-send hooks.
client-merged : ∀ {client server events} → Rows.Merge client server events →
  mapMaybe clientDecode (Projection.clientRows events) ≡ map clientWire client
client-merged Rows.empty = refl
client-merged (Rows.client {row = Rows.sendCommand D.request} merged) rewrite client-merged merged = refl
client-merged (Rows.client {row = Rows.sendCommand D.quit} merged) rewrite client-merged merged = refl
client-merged (Rows.client {row = Rows.receiveResponse D.done} merged) rewrite client-merged merged = refl
client-merged (Rows.client {row = Rows.receiveResponse (D.reply _)} merged) rewrite client-merged merged = refl
client-merged (Rows.server {row = Rows.receiveCommand _} merged) = client-merged merged
client-merged (Rows.server {row = Rows.sendResponse _} merged) = client-merged merged

-- The corresponding server projection preserves every supplied server occurrence and exact reply.
server-merged : ∀ {client server events} → Rows.Merge client server events →
  mapMaybe serverDecode (Projection.serverRows events) ≡ map serverWire server
server-merged Rows.empty = refl
server-merged (Rows.server {row = Rows.receiveCommand D.request} merged) rewrite server-merged merged = refl
server-merged (Rows.server {row = Rows.receiveCommand D.quit} merged) rewrite server-merged merged = refl
server-merged (Rows.server {row = Rows.sendResponse D.done} merged) rewrite server-merged merged = refl
server-merged (Rows.server {row = Rows.sendResponse (D.reply _)} merged) rewrite server-merged merged = refl
server-merged (Rows.client {row = Rows.sendCommand _} merged) = server-merged merged
server-merged (Rows.client {row = Rows.receiveResponse _} merged) = server-merged merged

-- Local success is only a necessary conjunction and never asserts a shared paired execution exists.
Pass : S.Contract → List Rows.ClientRow → List Rows.ServerRow → Set
Pass contract client server =
  CW.HasTrace CW.initial (map clientWire client) × SW.HasTrace contract SW.initial (map serverWire server)

-- Both local quotient decisions are total and require neither Notification equality nor an inhabited Return.
decide : (contract : S.Contract) (client : List Rows.ClientRow) (server : List Rows.ServerRow) →
  Dec (Pass contract client server)
decide contract client server with CW.decide CW.initial (map clientWire client)
... | no absent = no λ { (accepted , _) → absent accepted }
... | yes accepted with SW.decide contract SW.initial (map serverWire server)
...   | no absent = no λ { (_ , accepted) → absent accepted }
...   | yes serverAccepted = yes (accepted , serverAccepted)

-- Every actual paired fresh prefix passes both exact local languages under the same server contract.
necessary : ∀ {contract client server events target} → Rows.Merge client server events →
  D.Run contract D.initial events target → Pass contract client server
necessary {contract} {target = target} merged source
  with Projection.For.client contract source | Projection.For.server contract source
... | clientActions , clientSource , clientSame | serverActions , serverSource , serverSame =
  Client.source→quotient (clientActions , D.clientState target , clientSource ,
    trans (sym (client-observation clientActions))
      (trans (cong (mapMaybe clientDecode) clientSame) (client-merged merged))) ,
  Server.source→quotient (serverActions , D.serverState target , serverSource ,
    trans (sym (server-observation serverActions))
      (trans (cong (mapMaybe serverDecode) serverSame) (server-merged merged)))

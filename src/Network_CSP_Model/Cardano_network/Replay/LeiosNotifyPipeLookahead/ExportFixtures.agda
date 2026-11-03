{-# OPTIONS --guardedness #-}

-- Pure wire-row export for Agda normalization of checked node witnesses; not a log decider.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ExportFixtures where

open import Data.List using (List; []; _∷_; map)
open import Data.Maybe using (just; nothing)
open import Data.Nat.Show using (show)
open import Data.Product using (_,_)
open import Data.String using (String; _++_; intersperse)
open import Data.Unit using (⊤)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams using (header)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverTests as Tests

-- The renderer retains every exact normalized field of the witness payload.
notification : Notification → String
notification (announcement (header nothing)) = "Announcement:none"
notification (announcement (header (just (hash , slot , size)))) =
  "Announcement:" ++ show hash ++ ":" ++ show slot ++ ":" ++ show size
notification (offer (hash , slot) size) = "Offer:" ++ show hash ++ ":" ++ show slot ++ ":" ++ show size
notification (txsOffer (hash , slot)) = "TxsOffer:" ++ show hash ++ ":" ++ show slot
notification (votes xs) = "Votes:" ++ intersperse "," (map (λ (h , v) → show h ++ ":" ++ show v) xs)

-- A reply retains the distinction between normal data and cancellation.
reply : S.Reply → String
reply (S.normal msg) = notification msg
reply S.canceled = "Canceled"

-- Client agency admits exactly RequestNext and Quit.
clientMessage : D.ClientMessage → String
clientMessage D.request = "RequestNext"
clientMessage D.quit = "Quit"

-- Done remains distinct from every reply kind.
serverMessage : D.ServerMessage → String
serverMessage (D.reply msg) = reply msg
serverMessage D.done = "Done"

-- Endpoint tags and driver directions are serialized without sorting or merging.
row : D.Event → String
row (D.clientSend msg) = "client\tSend\t" ++ clientMessage msg
row (D.serverRecv msg) = "server\tRecv\t" ++ clientMessage msg
row (D.serverSend msg) = "server\tSend\t" ++ serverMessage msg
row (D.clientRecv msg) = "client\tRecv\t" ++ serverMessage msg

-- Each exported list is computed from the same actions inhabited by its source theorem.
fixture : String → List Node.Action → String
fixture name actions = intersperse "\n" (map (λ e → name ++ "\t" ++ row e) (Node.wireRows actions))

-- Normalize only the four concrete histories already certified by NodeDriverTests.
rendered : String
rendered = intersperse "\n"
  (fixture "idle-quit" Tests.idle-actions ∷
   fixture "cancel-blocked-next" Tests.shutdown-actions ∷
   fixture "delayed-send-prefix" Tests.delayed-actions ∷
   fixture "selected-normal" Tests.late-normal-actions ∷ [])

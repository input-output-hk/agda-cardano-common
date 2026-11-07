{-# OPTIONS --guardedness #-}

-- Actual full-node source/native observations and nondeleting validation controls.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodePolicyObservationTests where

open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_; map; length)
open import Data.Maybe using (just)
open import Data.Nat using (ℕ)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitnessFalse)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (Notification; votes)
import Cardano_network.Replay.LeiosNotifySession as Log
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverPayloadMap Notification as PayloadMap
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverTests as Source
import Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeDriverDecideTests as Decisions
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ClientAdapter as Client
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.ServerAdapter as Server
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodePairedAdapter as Policy
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.LoggerObservation as Typed
import Cardano_network.Replay.LeiosNotifyPipeLookahead.Wire.NodePolicyObservation as Observation
module Native = Observation.At fzero fzero hi hi

-- Each endpoint retains its independent graceful cancellation order.
client-close : List Log.E
client-close = (Log.Send , Log.RequestNext) ∷ (Log.Send , Log.Quit) ∷
  (Log.Recv , Log.Canceled) ∷ (Log.Recv , Log.Done) ∷ []

-- Server receives and sends are opposite observations of the same commands and replies.
server-close : List Log.E
server-close = (Log.Recv , Log.RequestNext) ∷ (Log.Recv , Log.Quit) ∷
  (Log.Send , Log.Canceled) ∷ (Log.Send , Log.Done) ∷ []

-- Independent exact row encodings validate all eight positions without invoking a protocol search.
close-valid : Policy.Valid Log.client (Policy.present client-close)
  Log.server (Policy.present server-close) Decisions.cancel-client Decisions.cancel-server
close-valid =
  (refl , Client.linked refl (Client.linked refl (Client.linked refl (Client.linked refl Client.empty)))) ,
  (refl , Server.linked refl (Server.linked refl (Server.linked refl (Server.linked refl Server.empty))))

-- This accepted prefix carries the previously constructed actual fresh full node-policy cancellation run.
close-source : Policy.Accepted Log.client (Policy.present client-close) Log.server (Policy.present server-close)
close-source = Decisions.cancel-client , Decisions.cancel-server , close-valid , Decisions.cancel-source

-- Canonical typed hooks are an independently inhabited instance of the same reusable mapping theorem.
typed-close : Observation.Logger.Accepted Log.client (map Typed.representative client-close)
  Log.server (map Typed.representative server-close)
typed-close = client-close , server-close , Typed.representative-list client-close ,
  Typed.representative-list server-close , close-source

-- Typed logger observation also realizes the actual full policy rather than the generic driver language.
typed-native-close : Native.LoggerNative.Observed Log.client (map Typed.representative client-close)
  Log.server (map Typed.representative server-close)
typed-native-close = Native.LoggerNative.observed-realize typed-close

-- A real notification value retains the order and duplicate position inside its vote payload.
duplicate-votes : Notification
duplicate-votes = votes ((170 , 3) ∷ (187 , 4) ∷ (170 , 3) ∷ [])

module VotesMap = PayloadMap (λ _ → duplicate-votes)

-- The delayed client Send remains after the received vote reply in its own endpoint list.
vote-client : List Rows.ClientRow
vote-client = Rows.receiveResponse (D.reply (S.normal duplicate-votes)) ∷ Rows.sendCommand D.request ∷ []

-- The other endpoint retains its actual Request Receive before the delayed Send hook.
vote-server : List Rows.ServerRow
vote-server = Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply (S.normal duplicate-votes)) ∷ []

-- Both endpoint observations include every original duplicate vote rather than an unordered set.
vote-client-events : List Log.E
vote-client-events = (Log.Recv , Log.Votes ((170 , 3) ∷ (187 , 4) ∷ (170 , 3) ∷ [])) ∷
  (Log.Send , Log.RequestNext) ∷ []

-- The server sees precisely the same concrete payload in its independent log order.
vote-server-events : List Log.E
vote-server-events = (Log.Recv , Log.RequestNext) ∷
  (Log.Send , Log.Votes ((170 , 3) ∷ (187 , 4) ∷ (170 , 3) ∷ [])) ∷ []

-- Mapping the already inhabited full source run supplies genuine queue/handler evidence for this payload.
vote-source : Policy.Accepted Log.client (Policy.present vote-client-events) Log.server (Policy.present vote-server-events)
vote-source = vote-client , vote-server ,
  ((refl , Client.linked refl (Client.linked refl Client.empty)) ,
   (refl , Server.linked refl (Server.linked refl Server.empty))) ,
  _ , Rows.server (Rows.client (Rows.client (Rows.server Rows.empty))) ,
  VotesMap.nodeState Source.delayedState , map VotesMap.nodeAction Source.delayed-actions ,
  VotesMap.nodeRun Source.delayed-source , refl

-- Ordered repeated votes also retain an actual typed native-policy path.
votes-typed : Observation.Logger.Accepted Log.client (map Typed.representative vote-client-events)
  Log.server (map Typed.representative vote-server-events)
votes-typed = vote-client-events , vote-server-events , Typed.representative-list vote-client-events ,
  Typed.representative-list vote-server-events , vote-source

-- Native realization preserves the same ordered duplicate payloads.
votes-native : Native.LoggerNative.Observed Log.client (map Typed.representative vote-client-events)
  Log.server (map Typed.representative vote-server-events)
votes-native = Native.LoggerNative.observed-realize votes-typed

-- Endpoint declarations remain checked for empty observations.
wrong-role-empty : Observation.Logger.Accepted Log.server [] Log.server [] → ⊥
wrong-role-empty = toWitnessFalse {a? = Observation.Logger.decide Log.server [] Log.server []} tt

-- Both original endpoint shutdown sequences retain every row.
close-row-counts : length client-close ≡ 4 × length server-close ≡ 4
close-row-counts = refl , refl

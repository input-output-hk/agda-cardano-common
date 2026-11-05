{-# OPTIONS --guardedness #-}

-- Native paired decisions retain exact payloads while allowing both delayed Send records.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideNativeTests where

open import Data.Bool using (false)
open import Data.Empty using (⊥)
open import Data.Fin using () renaming (zero to fzero)
open import Data.Integer using (+_)
open import Data.List using (List; []; _∷_)
open import Data.Maybe using (nothing)
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Function using (_$_)
open import Relation.Binary.PropositionalEquality using (refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Cardano_network.Base using (hi)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Notification ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecide Notification notificationEq (votes []) as Check
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverDecideNative exactParams as Bridge
module B = Bridge.At S.nodeNext fzero fzero hi hi

-- Empty inputs are a real native prefix without a successful-return claim.
empty-native : B.NativeTrace [] []
empty-native = toWitness {a? = B.decide [] []} tt

-- Final Done cannot appear at the initial server without a matching observed Quit.
unmatched-done : B.NativeTrace [] (Rows.sendResponse D.done ∷ []) → ⊥
unmatched-done = toWitnessFalse {a? = B.decide [] (Rows.sendResponse D.done ∷ [])} tt

-- Vote ordering and duplicate occurrences are part of the exact native notification value.
sample : Notification
sample = votes ((17 , 23) ∷ (31 , 37) ∷ (17 , 23) ∷ [])

-- Each endpoint supplies its own order, with its Receive preceding the delayed Send.
clientRows : List Rows.ClientRow
clientRows = Rows.receiveResponse (D.reply (S.normal sample)) ∷ Rows.sendCommand D.request ∷ []

-- The server's Request receive precedes its exact selected reply's Send hook.
serverRows : List Rows.ServerRow
serverRows = Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply (S.normal sample)) ∷ []

-- One valid merge contains both Receive rows before either corresponding Send row.
events : List D.Event
events = D.serverRecv D.request ∷ D.clientRecv (D.reply (S.normal sample)) ∷
  D.clientSend D.request ∷ D.serverSend (D.reply (S.normal sample)) ∷ []

-- The product still has the exact selected value under client inspection at this prefix.
target : D.State
target = D.pair
  (C.client C.poll (C.inspect (S.normal sample)) [] [] 1 (+ 0) false nothing)
  (S.state S.awaitNext 0 S.sent 0 false) [] [] nothing nothing nothing nothing

-- This inhabited source schedule uses actual commits and decodes, without rearranging trace hooks.
source : D.Run S.nodeNext D.initial events target
source =
  D.internal (D.clientCallback (D.continue {k = + 1}) C.continueZero) $
  D.internal (D.clientInternal C.registerResponse) $
  D.internal (D.clientInternal (C.startResponse refl)) $
  D.internal (D.commitClient C.sentRequest) $
  D.internal (D.decodeServer (S.receiveRequest S.atFirst)) $
  D.visible (D.serverReceived (S.receiveRequest S.atFirst)) $
  D.internal (D.serverInternal S.admitted) $
  D.internal (D.serverInternal S.registered) $
  D.internal (D.serverInternal (S.claim refl)) $
  D.internal (D.serverCallback (S.choose refl refl)) $
  D.internal (D.commitServer (S.send refl)) $
  D.internal (D.decodeClient (C.receivedReply refl)) $
  D.visible (D.clientReceived (C.receivedReply refl)) $
  D.visible (D.clientSent C.sentRequest) $
  D.visible (D.serverSent (S.send refl)) D.stop

-- The merge certifies exactly both endpoint inputs, retaining all repeated vote pairs.
paired-source : Check.SourceTrace S.nodeNext clientRows serverRows
paired-source = events , Rows.server (Rows.client (Rows.client (Rows.server Rows.empty))) , target , source

-- Actual native paired PTree execution is constructed from the unrestricted accepted source witness.
delayed-native : B.NativeTrace clientRows serverRows
delayed-native = B.realize paired-source

-- Native inversion recovers a matching unrestricted source trace rather than just a canonical encoding.
native-roundtrip : Check.SourceTrace S.nodeNext clientRows serverRows
native-roundtrip = B.sound delayed-native

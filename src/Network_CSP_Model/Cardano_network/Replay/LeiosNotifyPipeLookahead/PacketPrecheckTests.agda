{-# OPTIONS --safe #-}

-- Exact mismatches fail while unfinished Send hooks and unequal recorded lengths remain possible.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketPrecheckTests where

open import Data.Bool using (Bool; false; true)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
import Data.List.Properties as List
open import Data.Product using (_,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Bool ⊤ (false ∷ []) as Basis
import Cardano_network.LeiosNotifyPipeLookahead.DriverConservation Bool ⊤ as Conservation
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketPrecheck Bool ⊤ as Packet
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverBasisExecutionTests as Fixture

-- No records impose no packet-prefix restriction, irrespective of future work.
empty-prefix : Packet.Pass [] []
empty-prefix = toWitness {a? = Packet.decide Bool._≟_ [] []} tt

-- One Request Send may be the last observation before the entire server input's EOF.
send-before-receive : Packet.Pass (Rows.sendCommand D.request ∷ []) []
send-before-receive = toWitness {a? = Packet.decide Bool._≟_ (Rows.sendCommand D.request ∷ []) []} tt

-- The same physical Request may instead be received before its delayed Send record.
receive-before-send : Packet.Pass [] (Rows.receiveCommand D.request ∷ [])
receive-before-send = toWitness {a? = Packet.decide Bool._≟_ [] (Rows.receiveCommand D.request ∷ [])} tt

-- Both Receive hooks can appear while both Send hooks remain pending at EOF.
both-receives : Packet.Pass (Rows.receiveResponse (D.reply (S.normal false)) ∷ [])
  (Rows.receiveCommand D.request ∷ [])
both-receives = toWitness {a? = Packet.decide Bool._≟_
  (Rows.receiveResponse (D.reply (S.normal false)) ∷ []) (Rows.receiveCommand D.request ∷ [])} tt

-- This positive also follows from an inhabited fresh source run and the general necessary theorem.
necessary-both-receives : Packet.Pass (Rows.receiveResponse (D.reply (S.normal false)) ∷ [])
  (Rows.receiveCommand D.request ∷ [])
necessary-both-receives = Packet.necessary (Rows.server (Rows.client Rows.empty)) (Basis.sound Fixture.both-delayed)

-- An endpoint's recorded command kind cannot be changed by hidden packet suffixes.
wrong-command : Packet.Pass (Rows.sendCommand D.request ∷ []) (Rows.receiveCommand D.quit ∷ []) → ⊥
wrong-command = toWitnessFalse {a? = Packet.decide Bool._≟_
  (Rows.sendCommand D.request ∷ []) (Rows.receiveCommand D.quit ∷ [])} tt

-- Late command mismatches are checked after an initially matching Request.
wrong-late-command : Packet.Pass
  (Rows.sendCommand D.request ∷ Rows.sendCommand D.quit ∷ [])
  (Rows.receiveCommand D.request ∷ Rows.receiveCommand D.request ∷ []) → ⊥
wrong-late-command = toWitnessFalse {a? = Packet.decide Bool._≟_
  (Rows.sendCommand D.request ∷ Rows.sendCommand D.quit ∷ [])
  (Rows.receiveCommand D.request ∷ Rows.receiveCommand D.request ∷ [])} tt

-- Exact normal reply values must agree at the first common recorded position.
wrong-reply : Packet.Pass (Rows.receiveResponse (D.reply (S.normal true)) ∷ [])
  (Rows.sendResponse (D.reply (S.normal false)) ∷ []) → ⊥
wrong-reply = toWitnessFalse {a? = Packet.decide Bool._≟_
  (Rows.receiveResponse (D.reply (S.normal true)) ∷ [])
  (Rows.sendResponse (D.reply (S.normal false)) ∷ [])} tt

-- Matching the first response does not excuse a different later payload.
wrong-late-reply : Packet.Pass
  (Rows.receiveResponse (D.reply (S.normal false)) ∷ Rows.receiveResponse (D.reply (S.normal true)) ∷ [])
  (Rows.sendResponse (D.reply (S.normal false)) ∷ Rows.sendResponse (D.reply (S.normal false)) ∷ []) → ⊥
wrong-late-reply = toWitnessFalse {a? = Packet.decide Bool._≟_
  (Rows.receiveResponse (D.reply (S.normal false)) ∷ Rows.receiveResponse (D.reply (S.normal true)) ∷ [])
  (Rows.sendResponse (D.reply (S.normal false)) ∷ Rows.sendResponse (D.reply (S.normal false)) ∷ [])} tt

-- Canceled is a response constructor; it cannot match final Done.
canceled-is-not-done : Packet.Pass (Rows.receiveResponse D.done ∷ [])
  (Rows.sendResponse (D.reply S.canceled) ∷ []) → ⊥
canceled-is-not-done = toWitnessFalse {a? = Packet.decide Bool._≟_
  (Rows.receiveResponse D.done ∷ []) (Rows.sendResponse (D.reply S.canceled) ∷ [])} tt

-- An extra final Receive may correspond to one pending Send; equality of recorded lengths is unnecessary.
receive-lead : Packet.Pass
  (Rows.receiveResponse (D.reply (S.normal false)) ∷ Rows.receiveResponse (D.reply (S.normal true)) ∷ [])
  (Rows.sendResponse (D.reply (S.normal false)) ∷ [])
receive-lead = toWitness {a? = Packet.decide Bool._≟_
  (Rows.receiveResponse (D.reply (S.normal false)) ∷ Rows.receiveResponse (D.reply (S.normal true)) ∷ [])
  (Rows.sendResponse (D.reply (S.normal false)) ∷ [])} tt

-- This necessary-only guard also permits the opposite unequal recorded lengths.
send-lead : Packet.Pass
  (Rows.receiveResponse (D.reply (S.normal false)) ∷ [])
  (Rows.sendResponse (D.reply (S.normal false)) ∷ Rows.sendResponse (D.reply (S.normal true)) ∷ [])
send-lead = toWitness {a? = Packet.decide Bool._≟_
  (Rows.receiveResponse (D.reply (S.normal false)) ∷ [])
  (Rows.sendResponse (D.reply (S.normal false)) ∷ Rows.sendResponse (D.reply (S.normal true)) ∷ [])} tt

-- This necessary-only guard deliberately omits pending-slot count and local-control sufficiency.
not-a-count-check : Packet.Pass [] (Rows.receiveCommand D.request ∷ Rows.receiveCommand D.request ∷ [])
not-a-count-check = toWitness {a? = Packet.decide Bool._≟_ []
  (Rows.receiveCommand D.request ∷ Rows.receiveCommand D.request ∷ [])} tt

-- Repeated packet values remain repeated positions in the exact history projection.
repeated-positions : Packet.serverSends
  (Rows.sendResponse (D.reply (S.normal false)) ∷ Rows.sendResponse (D.reply (S.normal false)) ∷ []) ≡
  D.reply (S.normal false) ∷ D.reply (S.normal false) ∷ []
repeated-positions = refl

-- This normal source inventory allows multiple endpoint merges with identical packet histories.
client : List Rows.ClientRow
client = Rows.sendCommand D.request ∷ Rows.receiveResponse (D.reply (S.normal false)) ∷ []

-- Its complementary records preserve the exact responder payload independently of interleaving.
server : List Rows.ServerRow
server = Rows.receiveCommand D.request ∷ Rows.sendResponse (D.reply (S.normal false)) ∷ []

-- The history lemma covers the server Receive preceding the delayed client Send.
merge-independent-history : Conservation.observe
  (D.serverRecv D.request ∷ D.clientSend D.request ∷
   D.serverSend (D.reply (S.normal false)) ∷ D.clientRecv (D.reply (S.normal false)) ∷ []) Conservation.empty ≡
  Packet.extend Conservation.empty client server
merge-independent-history = Packet.merge-history {client = client} {server = server}
  (Rows.server (Rows.client (Rows.server (Rows.client Rows.empty)))) Conservation.empty

import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketPrecheck (List Bool) ⊤ as Nested
import Cardano_network.LeiosNotifyPipeLookahead.Model (List Bool) as ListsS
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel (List Bool) ⊤ as ListsD
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows (List Bool) ⊤ as ListsRows

-- Notification equality retains an internal list's final duplicate rather than treating it as a set.
inner-duplicate-preserved : Nested.Pass
  (ListsRows.receiveResponse (ListsD.reply (ListsS.normal (true ∷ false ∷ []))) ∷ [])
  (ListsRows.sendResponse (ListsD.reply (ListsS.normal (true ∷ false ∷ true ∷ []))) ∷ []) → ⊥
inner-duplicate-preserved = toWitnessFalse {a? = Nested.decide (List.≡-dec Bool._≟_)
  (ListsRows.receiveResponse (ListsD.reply (ListsS.normal (true ∷ false ∷ []))) ∷ [])
  (ListsRows.sendResponse (ListsD.reply (ListsS.normal (true ∷ false ∷ true ∷ []))) ∷ [])} tt

-- Internal reordering is also an exact payload mismatch despite an unchanged multiset.
inner-order-preserved : Nested.Pass
  (ListsRows.receiveResponse (ListsD.reply (ListsS.normal (false ∷ true ∷ true ∷ []))) ∷ [])
  (ListsRows.sendResponse (ListsD.reply (ListsS.normal (true ∷ false ∷ true ∷ []))) ∷ []) → ⊥
inner-order-preserved = toWitnessFalse {a? = Nested.decide (List.≡-dec Bool._≟_)
  (ListsRows.receiveResponse (ListsD.reply (ListsS.normal (false ∷ true ∷ true ∷ []))) ∷ [])
  (ListsRows.sendResponse (ListsD.reply (ListsS.normal (true ∷ false ∷ true ∷ []))) ∷ [])} tt

import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊥ as EmptyDriver
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊥ as EmptyRows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketPrecheck Bool ⊥ as EmptyPacket

-- Packet necessity does not assume an inhabited Return type or a successful terminating execution.
empty-return : EmptyPacket.Pass [] []
empty-return = EmptyPacket.necessary {contract = S.nodeNext} EmptyRows.empty EmptyDriver.stop

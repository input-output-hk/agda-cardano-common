{-# OPTIONS --safe #-}

-- Reply credit is recorded server Request credit, without confusing Send hooks, Quit or Done.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.CreditPrecheckTests where

open import Data.Bool using (Bool; false)
import Data.Bool.Properties as Bool
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_)
open import Data.Nat using (z≤n)
open import Data.Product using (_×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊥ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊥ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CreditPrecheck Bool ⊥ as Credit
import Cardano_network.Replay.LeiosNotifyPipeLookahead.LocalPrecheck Bool ⊥ as Local
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketPrecheck Bool ⊥ as Packet
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketCountPrecheck Bool ⊥ as Count

-- A normal reply Receive without any server Request record is unsolicited, even if its Send is pending.
unsolicited : List Rows.ClientRow
unsolicited = Rows.receiveResponse (D.reply (S.normal false)) ∷ []

-- The generic successful callback contract cannot manufacture a reply obligation either.
no-unsolicited-normal : Credit.Pass unsolicited [] → ⊥
no-unsolicited-normal = toWitnessFalse {a? = Credit.decide unsolicited []} tt

-- Canceled consumes the same actual request credit as a normal reply.
no-unsolicited-canceled : Credit.Pass (Rows.receiveResponse (D.reply S.canceled) ∷ []) [] → ⊥
no-unsolicited-canceled = toWitnessFalse {a? = Credit.decide (Rows.receiveResponse (D.reply S.canceled) ∷ []) []} tt

-- A recorded client Request Send alone cannot license a server callback before its Request Receive record.
client-send-is-not-credit : Credit.Pass
  (Rows.sendCommand D.request ∷ unsolicited) [] → ⊥
client-send-is-not-credit = toWitnessFalse {a? = Credit.decide (Rows.sendCommand D.request ∷ unsolicited) []} tt

-- Recorded Quit never adds a reply obligation.
quit-is-not-credit : Credit.Pass unsolicited (Rows.receiveCommand D.quit ∷ []) → ⊥
quit-is-not-credit = toWitnessFalse {a? = Credit.decide unsolicited (Rows.receiveCommand D.quit ∷ [])} tt

-- One server Request Receive is sufficient for this numerical necessary condition, even with no Send records.
one-recorded-request : Credit.Pass unsolicited (Rows.receiveCommand D.request ∷ [])
one-recorded-request = toWitness {a? = Credit.decide unsolicited (Rows.receiveCommand D.request ∷ [])} tt

-- Repeated equal payloads still consume two distinct request credits.
no-second-reply : Credit.Pass (Rows.receiveResponse (D.reply (S.normal false)) ∷ unsolicited)
  (Rows.receiveCommand D.request ∷ []) → ⊥
no-second-reply = toWitnessFalse {a? = Credit.decide
  (Rows.receiveResponse (D.reply (S.normal false)) ∷ unsolicited) (Rows.receiveCommand D.request ∷ [])} tt

-- Normal and Canceled remain separate reply occurrences in the count.
two-kinds-two-credits : Credit.Pass
  (Rows.receiveResponse (D.reply S.canceled) ∷ unsolicited)
  (Rows.receiveCommand D.request ∷ Rows.receiveCommand D.request ∷ [])
two-kinds-two-credits = toWitness {a? = Credit.decide
  (Rows.receiveResponse (D.reply S.canceled) ∷ unsolicited)
  (Rows.receiveCommand D.request ∷ Rows.receiveCommand D.request ∷ [])} tt

-- Unused request credit is not an error at finite-prefix EOF.
request-excess : Credit.Pass unsolicited
  (Rows.receiveCommand D.request ∷ Rows.receiveCommand D.request ∷ [])
request-excess = toWitness {a? = Credit.decide unsolicited
  (Rows.receiveCommand D.request ∷ Rows.receiveCommand D.request ∷ [])} tt

-- Done is excluded: a legitimate zero-request idle shutdown must not consume reply credit.
idle-close : Credit.Pass (Rows.sendCommand D.quit ∷ Rows.receiveResponse D.done ∷ [])
  (Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ [])
idle-close = toWitness {a? = Credit.decide
  (Rows.sendCommand D.quit ∷ Rows.receiveResponse D.done ∷ [])
  (Rows.receiveCommand D.quit ∷ Rows.sendResponse D.done ∷ [])} tt

-- Credit alone intentionally leaves orphan Done for the complete backend or another necessary condition.
done-is-outside-credit : Credit.Pass (Rows.sendCommand D.quit ∷ Rows.receiveResponse D.done ∷ []) []
done-is-outside-credit = toWitness {a? = Credit.decide
  (Rows.sendCommand D.quit ∷ Rows.receiveResponse D.done ∷ []) []} tt

-- Earlier necessary guards all pass this example; the cross-endpoint credit check supplies new information.
prior-guards-pass : Local.Pass S.genericNext unsolicited [] × Packet.Pass unsolicited [] × Count.Pass unsolicited []
prior-guards-pass =
  toWitness {a? = Local.decide S.genericNext unsolicited []} tt ,
  toWitness {a? = Packet.decide Bool._≟_ unsolicited []} tt ,
  toWitness {a? = Count.decide unsolicited []} tt

-- The new rejection applies to every source schedule and every merge, without observing a failed search.
no-original-source : ∀ {contract events target} → Rows.Merge unsolicited [] events →
  D.Run contract D.initial events target → ⊥
no-original-source merged source = no-unsolicited-normal (Credit.necessary merged source)

-- With no reply receives, every unused server request inventory passes this credit-only condition.
no-replies : ∀ server → Credit.Pass [] server
no-replies server = z≤n

-- Generic Return may be empty; a fresh zero-operation source already witnesses necessity.
empty-return : Credit.Pass [] []
empty-return = Credit.necessary {contract = S.nodeNext} Rows.empty D.stop

import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as Actual
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as ActualRows
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Bool ⊤ (false ∷ []) as Basis
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CreditPrecheck Bool ⊤ as ActualCredit
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverBasisExecutionTests as Fixture

-- A real source prefix has both Sends pending but its recorded Request Receive already licenses the reply.
actual-delayed-send : ActualCredit.Pass
  (ActualRows.receiveResponse (Actual.reply (S.normal false)) ∷ []) (ActualRows.receiveCommand Actual.request ∷ [])
actual-delayed-send = ActualCredit.necessary
  (ActualRows.server (ActualRows.client ActualRows.empty)) (Basis.sound Fixture.both-delayed)

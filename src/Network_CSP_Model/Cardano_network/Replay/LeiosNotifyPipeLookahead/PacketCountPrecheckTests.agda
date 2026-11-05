{-# OPTIONS --safe #-}

-- Boundary controls retain a one-record Lead but reject two, without bounding queued sends.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketCountPrecheckTests where

open import Data.Bool using (Bool; false)
open import Data.Empty using (⊥)
open import Data.List using (List; []; _∷_; replicate)
open import Data.Nat using (ℕ; zero; suc; z≤n)
open import Data.Product using (_,_; proj₁; proj₂)
open import Data.Unit using (⊤)
open import Relation.Nullary.Decidable using (toWitness; toWitnessFalse)
open import Data.Unit using (tt)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊥ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊥ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketCountPrecheck Bool ⊥ as Count

-- These exact endpoint rows preserve command occurrences rather than counting a set of values.
commands-sent : ℕ → List Rows.ClientRow
commands-sent n = replicate n (Rows.sendCommand D.request)

-- Recorded Request receives may lead their Send records only through one pending client Send.
commands-received : ℕ → List Rows.ServerRow
commands-received n = replicate n (Rows.receiveCommand D.request)

-- Response receives use a concrete normal value; no Return value or callback termination is needed.
responses-received : ℕ → List Rows.ClientRow
responses-received n = replicate n (Rows.receiveResponse (D.reply (S.normal false)))

-- Every identical response Send remains an individual recorded occurrence.
responses-sent : ℕ → List Rows.ServerRow
responses-sent n = replicate n (Rows.sendResponse (D.reply (S.normal false)))

-- With no recorded Send, one server Receive remains a permitted delayed-hook boundary.
command-zero-one : Count.Pass (commands-sent 0) (commands-received 1)
command-zero-one = toWitness {a? = Count.decide (commands-sent 0) (commands-received 1)} tt

-- Two server receives cannot be backed by a single pending client Send.
command-zero-two : Count.Pass (commands-sent 0) (commands-received 2) → ⊥
command-zero-two = toWitnessFalse {a? = Count.decide (commands-sent 0) (commands-received 2)} tt

-- One recorded Send plus one pending Send may back two recorded server receives.
command-one-two : Count.Pass (commands-sent 1) (commands-received 2)
command-one-two = toWitness {a? = Count.decide (commands-sent 1) (commands-received 2)} tt

-- A second extra receive is rejected even when some ordinary progress was recorded.
command-one-three : Count.Pass (commands-sent 1) (commands-received 3) → ⊥
command-one-three = toWitnessFalse {a? = Count.decide (commands-sent 1) (commands-received 3)} tt

-- The response direction independently permits its one pending server Send.
response-zero-one : Count.Pass (responses-received 1) (responses-sent 0)
response-zero-one = toWitness {a? = Count.decide (responses-received 1) (responses-sent 0)} tt

-- It independently excludes two client receives with no recorded server Sends.
response-zero-two : Count.Pass (responses-received 2) (responses-sent 0) → ⊥
response-zero-two = toWitnessFalse {a? = Count.decide (responses-received 2) (responses-sent 0)} tt

-- One recorded server response Send permits a second received response at EOF.
response-one-two : Count.Pass (responses-received 2) (responses-sent 1)
response-one-two = toWitness {a? = Count.decide (responses-received 2) (responses-sent 1)} tt

-- Three receives cannot be explained by one recorded Send and its one pending successor.
response-one-three : Count.Pass (responses-received 3) (responses-sent 1) → ⊥
response-one-three = toWitnessFalse {a? = Count.decide (responses-received 3) (responses-sent 1)} tt

-- Both pending Send slots may be occupied at once; each receiver can lead by one independently.
simultaneous-lead : Count.Pass
  (Rows.sendCommand D.request ∷ responses-received 2)
  (Rows.sendResponse (D.reply (S.normal false)) ∷ commands-received 2)
simultaneous-lead = toWitness {a? = Count.decide
  (Rows.sendCommand D.request ∷ responses-received 2)
  (Rows.sendResponse (D.reply (S.normal false)) ∷ commands-received 2)} tt

-- Arbitrarily many Sends may await their Receive records in a FIFO; there is no reverse count cap.
arbitrary-command-send-excess : ∀ n → Count.Pass (commands-sent n) []
arbitrary-command-send-excess zero = z≤n , z≤n
arbitrary-command-send-excess (suc n) = z≤n , proj₂ (arbitrary-command-send-excess n)

-- The response FIFO has the same unbounded excess-Send allowance.
arbitrary-response-send-excess : ∀ n → Count.Pass [] (responses-sent n)
arbitrary-response-send-excess zero = z≤n , z≤n
arbitrary-response-send-excess (suc n) = proj₁ (arbitrary-response-send-excess n) , z≤n

-- Generic Return may be empty: the fresh no-operation run already inhabits count necessity.
empty-return : Count.Pass [] []
empty-return = Count.necessary {contract = S.nodeNext} Rows.empty D.stop

import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as Actual
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as ActualRows
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Bool ⊤ (false ∷ []) as Basis
import Cardano_network.Replay.LeiosNotifyPipeLookahead.PacketCountPrecheck Bool ⊤ as ActualCount
import Cardano_network.Replay.LeiosNotifyPipeLookahead.DriverBasisExecutionTests as Fixture

-- Actual source realization protects both Receive-before-Send EOF races, not just arithmetic predicates.
actual-both-pending : ActualCount.Pass
  (ActualRows.receiveResponse (Actual.reply (S.normal false)) ∷ [])
  (ActualRows.receiveCommand Actual.request ∷ [])
actual-both-pending = ActualCount.necessary
  (ActualRows.server (ActualRows.client ActualRows.empty)) (Basis.sound Fixture.both-delayed)

{-# OPTIONS --safe #-}

-- Guarding readiness preserves enabled candidates, duplicate positions and other hidden operation families.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.ReadyGateOrderTests where

open import Data.Bool using (Bool; true; false)
import Data.Bool.Properties as Bool
open import Data.List using ([]; _∷_; map; length)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (just; nothing)
open import Data.Product using (proj₁)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Bool as S
import Cardano_network.LeiosNotifyPipeLookahead.ClientModel Bool ⊤ as C
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Bool ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Bool ⊤ as Rows
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Bool ⊤ (false ∷ true ∷ false ∷ []) as Basis
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Bool ⊤ [] as EmptyBasis
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasisExecution Bool Bool._≟_ (false ∷ true ∷ false ∷ []) as Menu
import Cardano_network.LeiosNotifyPipeLookahead.DriverSearchOrder Bool Bool._≟_ (false ∷ true ∷ false ∷ []) as Old
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ReadyGateOrder Bool Bool._≟_ (false ∷ true ∷ false ∷ []) as Gate
import Cardano_network.Replay.LeiosNotifyPipeLookahead.ReadyGateOrder Bool Bool._≟_ [] as Empty

-- These arbitrary snapshots deliberately require no reachability or paired-node policy hypothesis.
snapshot : S.State → D.State
snapshot server = D.pair C.initial server [] [] nothing nothing nothing nothing

-- Claimed/false is the only delegated sender/flag combination; the original guard still checks active reader.
claimed : D.State
claimed = snapshot (S.state S.first 0 S.claimed 0 false)

-- Generic cancellation remains last, and both occurrences of the repeated normal candidate remain present.
generic-duplicate-targets : map proj₁ (Gate.readyMoves S.genericNext claimed) ≡
  snapshot (S.state S.first 0 (S.selected (S.normal false)) 0 false) ∷
  snapshot (S.state S.first 0 (S.selected (S.normal true)) 0 false) ∷
  snapshot (S.state S.first 0 (S.selected (S.normal false)) 0 false) ∷
  snapshot (S.state S.first 0 (S.selected S.canceled) 0 false) ∷ []
generic-duplicate-targets = refl

-- Node next keeps the same three normal candidate positions while its existing guard excludes generic cancellation.
node-duplicate-targets : map proj₁ (Gate.readyMoves S.nodeNext claimed) ≡
  snapshot (S.state S.first 0 (S.selected (S.normal false)) 0 false) ∷
  snapshot (S.state S.first 0 (S.selected (S.normal true)) 0 false) ∷
  snapshot (S.state S.first 0 (S.selected (S.normal false)) 0 false) ∷ []
node-duplicate-targets = refl

-- The enabled proof-bearing list is reused verbatim, rather than reconstructed with replacement evidence.
enabled-certificates : Gate.readyMoves S.genericNext claimed ≡ Menu.readyMoves S.genericNext claimed
enabled-certificates = refl

-- Initial idle sender state does not need to enumerate any candidate payload.
idle-ready-empty : Gate.readyMoves S.nodeNext D.initial ≡ []
idle-ready-empty = refl

-- Flag publication blocks the readiness callback even when the sender remains claimed.
flagged-ready-empty : Gate.readyMoves S.genericNext (snapshot (S.state S.first 0 S.claimed 0 true)) ≡ []
flagged-ready-empty = refl

-- An inactive reader with claimed/false still delegates; this optimization introduces no reader-active gate.
inactive-reader-delegates : Gate.readyMoves S.genericNext (snapshot (S.state S.closed 0 S.claimed 0 false)) ≡
  Menu.readyMoves S.genericNext (snapshot (S.state S.closed 0 S.claimed 0 false))
inactive-reader-delegates = refl

-- Empty bases still allow the original generic callback cancellation candidate when enabled.
empty-generic : length (Empty.readyMoves S.genericNext claimed) ≡ 1
empty-generic = refl

-- Empty bases have no normal node-next callback result; the existing contract guard decides this.
empty-node : Empty.readyMoves S.nodeNext claimed ≡ []
empty-node = refl

-- Replacing one family neither inserts nor removes an independent operation family.
eight-families : length (Gate.menus S.nodeNext D.initial) ≡ 8
eight-families = refl

-- A selected normal may have been chosen before Quit and remains physically committable afterward.
selected-after-quit : D.State
selected-after-quit = snapshot (S.state S.flushing 0 (S.selected (S.normal true)) 0 true)

-- Readiness is gated off for an already selected sender, independently of its normal packet value.
selected-ready-empty : Empty.readyMoves S.nodeNext selected-after-quit ≡ []
selected-ready-empty = refl

-- The distinct server commit family retains that exact selected packet even outside an empty callback basis.
committed : D.State
committed = D.pair C.initial (S.state S.flushing 0 (S.selected (S.normal true)) 0 true)
  [] (D.reply (S.normal true) ∷ []) nothing (just (D.reply (S.normal true))) nothing nothing

-- Completeness applies to the unchanged commit certificate, not to a new readiness selection.
selected-commit-retained : committed ∈ Empty.orderedTargets S.nodeNext selected-after-quit []
  (Rows.sendResponse (D.reply (S.normal true)) ∷ [])
selected-commit-retained = Empty.target-complete
  {p = S.nodeNext} {s = selected-after-quit} {client = []}
  {server = Rows.sendResponse (D.reply (S.normal true)) ∷ []} (EmptyBasis.commitServer (S.send refl))

-- A true-flag cancellation is an independent scheduling operation and survives the readiness gate too.
flag-cancel-retained : snapshot (S.state S.first 0 (S.selected S.canceled) 0 true) ∈
  Gate.orderedTargets S.nodeNext (snapshot (S.state S.first 0 S.claimed 0 true)) [] []
flag-cancel-retained = Gate.target-complete
  {p = S.nodeNext} {s = snapshot (S.state S.first 0 S.claimed 0 true)} {client = []} {server = []}
  (Basis.serverInternal (S.cancel refl))

-- Full sorted certificate equality retains score ties, duplicates and targets at every input suffix.
exact-order : ∀ p state client server →
  Gate.orderedMoves p state client server ≡ Old.orderedMoves p state client server
exact-order = Gate.orderedMoves-exact

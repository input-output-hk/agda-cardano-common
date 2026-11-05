{-# OPTIONS --guardedness #-}

-- Small actual-menu gates and anchor witnesses, with no paired-source search normalization.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.MenuProbeTests where

open import Data.List using ([]; _∷_; length)
open import Data.Maybe using (just; nothing)
open import Data.Nat using (suc)
open import Data.Product using (_,_)
open import Data.Unit using (⊤)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)
open import Cardano_network.Replay.LeiosNotifyExactParams using (exactParams)
open import Cardano_network.Data exactParams using (header)
open import Cardano_network.LeiosNotifyPipeLookahead.Notifications exactParams using (Notification; announcement)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverRows Notification ⊤ as Rows
import Cardano_network.Replay.LeiosNotifyPipeLookahead.CostProbe as Cost
import Cardano_network.Replay.LeiosNotifyPipeLookahead.MenuProbe as Probe

-- Empty input still has the actual one-element unobserved normal representative basis.
emptyPrepared : Probe.Prepared
emptyPrepared = Probe.prepare (Cost.typed [] [])

-- This computes the real production basis construction, not a hand-supplied list length.
empty-basis-count : length (Probe.normalBasis emptyPrepared) ≡ 1
empty-basis-count = refl

-- One distinct observed normal appears in addition to the unobserved votes[] representative.
onePrepared : Probe.Prepared
onePrepared = Probe.prepare (Cost.typed
  (Rows.receiveResponse (D.reply (S.normal (announcement (header nothing)))) ∷ []) [])

-- The actual unique basis has two elements after retaining the exact observed notification.
one-basis-count : length (Probe.normalBasis onePrepared) ≡ 2
one-basis-count = refl

-- Initial idle sender cannot select callback results, even with a nonempty normal basis.
initial-ready-empty : Probe.targets Probe.rawReady S.nodeNext (Probe.anchor Probe.initial) onePrepared ≡ []
initial-ready-empty = refl

-- The gate agrees by returning no readiness target without scanning candidate values.
initial-gated-empty : Probe.targets Probe.gatedReady S.nodeNext (Probe.anchor Probe.initial) onePrepared ≡ []
initial-gated-empty = refl

-- At claimed/false, the node callback accepts both actual normal basis values.
claimed-node-count : length (Probe.targets Probe.rawReady S.nodeNext Probe.claimedState onePrepared) ≡ 2
claimed-node-count = refl

-- Generic callbacks additionally expose Canceled through the unchanged old menu.
claimed-generic-count : length (Probe.targets Probe.rawReady S.genericNext Probe.claimedState onePrepared) ≡ 3
claimed-generic-count = refl

-- Claimed/false remains an exact delegation control for the candidate gate.
claimed-gated-count : length (Probe.targets Probe.gatedReady S.nodeNext Probe.claimedState onePrepared) ≡ 2
claimed-gated-count = refl

-- A selected payload cannot be replaced by another next callback before its Send.
selected-ready-empty : Probe.targets Probe.rawReady S.nodeNext Probe.selectedState onePrepared ≡ []
selected-ready-empty = refl

-- Flagged claimed control permits cancellation scheduling, but no callback selection.
flagged-ready-empty : Probe.targets Probe.rawReady S.nodeNext Probe.afterQuitState onePrepared ≡ []
flagged-ready-empty = refl

-- Fully closed control has no hidden target in any of the eight actual raw families.
closed-menu-empty : Probe.targets Probe.rawMenu S.nodeNext Probe.closedState onePrepared ≡ []
closed-menu-empty = refl

-- Inactive reader/claimed/false is explicitly a no-win control: the gate still delegates lookup.
inactive-reader-ready-empty : Probe.targets Probe.gatedReady S.nodeNext Probe.inactiveReaderState onePrepared ≡ []
inactive-reader-ready-empty = refl

-- A nonempty target's full-state forcing observes the varied scalar; empty targets need separate compiler qualification.
nonce-state-touched : Probe.touchState (Probe.withNonce 1 Probe.claimedState) ≡
  suc (Probe.touchState (Probe.withNonce 0 Probe.claimedState))
nonce-state-touched = refl

-- Exact gate-list equality transports through the complete common target-state fold.
same-forced-ready : ∀ contract state preparedInput →
  Probe.forceTargets (Probe.targets Probe.gatedReady contract state preparedInput) ≡
  Probe.forceTargets (Probe.targets Probe.rawReady contract state preparedInput)
same-forced-ready contract state preparedInput = cong Probe.forceTargets (Probe.ready-targets-exact contract state preparedInput)

-- The complete raw-menu projection is likewise identical at arbitrary perturbed states.
same-forced-menu : ∀ contract state preparedInput →
  Probe.forceTargets (Probe.targets Probe.gatedMenu contract state preparedInput) ≡
  Probe.forceTargets (Probe.targets Probe.rawMenu contract state preparedInput)
same-forced-menu contract state preparedInput = cong Probe.forceTargets (Probe.menu-targets-exact contract state preparedInput)

-- Old and candidate ordered iteration totals coincide for all iteration counts and nonce starts.
same-ordered-iterations : ∀ contract snapshot preparedInput repetitions nonce →
  Probe.iterations Probe.orderedGated contract snapshot preparedInput repetitions nonce ≡
  Probe.iterations Probe.orderedOld contract snapshot preparedInput repetitions nonce
same-ordered-iterations = Probe.iterations-exact

-- The zero-nonce first callback anchor has an actual fresh original source execution.
real-claimed-anchor : ∀ contract → D.Run contract D.initial (D.serverRecv D.request ∷ []) Probe.claimedState
real-claimed-anchor = Probe.claimed-reachable

-- The selected anchor is reached by the same source with one successful normal callback.
real-selected-anchor : ∀ contract → D.Run contract D.initial (D.serverRecv D.request ∷ []) Probe.selectedState
real-selected-anchor = Probe.selected-reachable

-- The source witness records Request then Quit before the published flag at a claimed sender.
real-after-quit-anchor : ∀ contract → D.Run contract D.initial
  (D.serverRecv D.request ∷ D.clientSend D.request ∷ D.clientSend D.quit ∷ D.serverRecv D.quit ∷ []) Probe.afterQuitState
real-after-quit-anchor = Probe.afterQuit-reachable

-- Idle shutdown reaches genuine closed control without assuming a benchmark trace suffix matches it.
real-closed-anchor : ∀ contract → D.Run contract D.initial
  (D.clientSend D.quit ∷ D.serverRecv D.quit ∷ D.serverSend D.done ∷ D.clientRecv D.done ∷ []) Probe.closedState
real-closed-anchor = Probe.closed-reachable

-- The arbitrary inactive-reader anchor is visibly labeled separately from the witnessed anchors.
unwitnessed-snapshot-label : Probe.nonceScope Probe.inactiveReaderClaimed ≡ "all-nonces-arbitrary-raw"
unwitnessed-snapshot-label = refl

-- Unsupported measurement modes remain explicit errors instead of another selected function.
unsupported-mode : Probe.parseMode "accepted-prefix" ≡ nothing
unsupported-mode = refl

-- Basis-only records zero menu iterations while still forcing the unique basis once through basisReady.
basis-only-no-menu : Probe.executed Probe.basisOnly 1000 ≡ 0
basis-only-no-menu = refl

-- The renderer consumes the three fields of one already supplied aggregate without rerunning a menu.
one-aggregate-render : Probe.renderTotals Probe.rawReady Probe.closed 1 (Probe.totals 2 3 4) ≡
  "menu-probe-complete\nstage=raw-ready;snapshot=closed;requested-iterations=1;executed-iterations=1;targets=2;state-sum=3;position-sum=4\ncontext=whole-input-ranking-only\nnonce-scope=anchor-0-source-witnessed;positive-nonces-arbitrary-raw"
one-aggregate-render = refl

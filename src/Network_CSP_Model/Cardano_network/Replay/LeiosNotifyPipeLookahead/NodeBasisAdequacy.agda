{-# OPTIONS --safe #-}

-- Finite input-relative eligible-offer bases preserve the full fresh node wire language.
-- Initial stores outside the fresh state need an explicit fixed-state premise.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.NodeBasisAdequacy
  (Notification : Set) where

open import Data.List using (List; map)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Data.Unit using (⊤; tt)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification ⊤ as D
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverModel Notification as Node
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCore Notification as Core
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBridge Notification as Reduction
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverWireCoreBasis Notification as Basis
import Cardano_network.LeiosNotifyPipeLookahead.NodeDriverPayloadMap Notification as PayloadMap
import Cardano_network.Replay.LeiosNotifyPipeLookahead.BasisAdequacy Notification ⊤ as Existing
import Cardano_network.Replay.LeiosNotifyPipeLookahead.UniqueBasisAdequacy Notification ⊤ as ExistingUnique

-- Arbitrary total maps into a declared basis restrict only newly supplied offers.
module IntoBasis (basis : List Notification) (rename : Notification → Notification)
  (lands : ∀ value → rename value ∈ basis) where
  module B = Basis basis
  module M = PayloadMap rename

  -- Existing guards remain source evidence; only offered values receive membership.
  tau : ∀ {s t} → Core.Tau s t → B.Tau (M.coreState s) (M.coreState t)
  tau proof@(Core.operational _) = M.coreTau proof , tt
  tau proof@(Core.offered {msg = value} _ _) = M.coreTau proof , lands value
  tau proof@(Core.handled _) = M.coreTau proof , tt
  tau proof@(Core.rejected _) = M.coreTau proof , tt

  -- All-state mapped runs retain wire order and the mapped queue/pending payloads exactly.
  run : ∀ {s rows t} → Core.Run s rows t →
    B.Run (M.coreState s) (map M.Driver.event rows) (M.coreState t)
  run Core.stop = B.stop
  run (Core.internal proof rest) = B.internal (tau proof) (run rest)
  run (Core.visible proof rest) = B.visible (M.coreVisible proof) (run rest)

-- The complete supplied inventory fixes observed values; a separate actual merge may use any order.
module ForInput (notificationEq : DecidableEquality Notification)
  (representative : Notification) (inventory : List D.Event) where
  module Reused = ExistingUnique.ForInput notificationEq representative inventory

  -- Candidate enumeration is deduplicated; original wire lists and inner vote lists are not.
  basis : List Notification
  basis = Reused.basis

  -- Reuse the original proved finite retraction, including its established computation gates.
  retract : Notification → Notification
  retract = Reused.Original.retract

  -- Every normal choice maps to the exact declared unique candidate alphabet.
  lands : ∀ value → retract value ∈ basis
  lands value = Reused.original→unique (Reused.Original.lands value)

  -- Recorded values are fixed even when repeated many times or equal to the fallback.
  fixes : ∀ {value} → value ∈ basis → retract value ≡ value
  fixes present = Reused.Original.fixes (Reused.unique→original present)

  -- Existing standard-library deduplication supplies the unique enumeration certificate.
  duplicate-free : Unique basis
  duplicate-free = Reused.duplicate-free

  module B = Basis basis
  module M = PayloadMap retract
  module Restricted = IntoBasis basis retract lands

  -- Payload-only coverage fixes complete events without constraining their endpoint merge order.
  event-fixed-payloads : ∀ {row} →
    (∀ {value} → value ∈ Existing.payloads row → value ∈ basis) → M.Driver.event row ≡ row
  event-fixed-payloads covered = Reused.Original.event-fixed-payloads
    (λ present → Reused.unique→original (covered present))

  -- Exact source-row membership in the supplied inventory implies observed-payload coverage.
  event-fixed : ∀ {row} → row ∈ inventory → M.Driver.event row ≡ row
  event-fixed = Reused.Original.event-fixed

  -- Every covered visible occurrence remains exact, including duplicate messages.
  rows-fixed-payloads : (rows : List D.Event) →
    (∀ {row value} → row ∈ rows → value ∈ Existing.payloads row → value ∈ basis) →
    map M.Driver.event rows ≡ rows
  rows-fixed-payloads rows covered = Reused.Original.rows-fixed-payloads rows
    (λ present payload → Reused.unique→original (covered present payload))

  -- The complete inventory supports every ordered merge drawn from either supplied endpoint.
  rows-fixed : (rows : List D.Event) → (∀ {row} → row ∈ rows → row ∈ inventory) →
    map M.Driver.event rows ≡ rows
  rows-fixed = Reused.Original.rows-fixed

  -- Nonfresh starts require the actual mapped initial state to remain unchanged.
  adequate-from : ∀ {s rows t} → M.coreState s ≡ s →
    (∀ {row value} → row ∈ rows → value ∈ Existing.payloads row → value ∈ basis) →
    Core.Run s rows t → B.Run s rows (M.coreState t)
  adequate-from {s} {rows} {t} fixed covered source =
    subst (λ initial → B.Run initial rows (M.coreState t)) fixed
      (subst (λ events → B.Run (M.coreState s) events (M.coreState t))
        (rows-fixed-payloads rows covered) (Restricted.run source))

  -- Fresh source runs contain no initial payload, so no extra inventory premise is needed.
  adequate-payloads : ∀ {rows t} →
    (∀ {row value} → row ∈ rows → value ∈ Existing.payloads row → value ∈ basis) →
    Core.Run Core.initial rows t → B.Run Core.initial rows (M.coreState t)
  adequate-payloads = adequate-from M.core-initial

  -- Complete input coverage preserves every possible endpoint merge and EOF prefix.
  adequate-covered : ∀ {rows t} → (∀ {row} → row ∈ rows → row ∈ inventory) →
    Core.Run Core.initial rows t → B.Run Core.initial rows (M.coreState t)
  adequate-covered {rows} {t} covered source =
    subst (λ initial → B.Run initial rows (M.coreState t)) M.core-initial
      (subst (λ events → B.Run (M.coreState Core.initial) events (M.coreState t))
        (rows-fixed rows covered) (Restricted.run source))

  -- In particular, the complete supplied ordered word has a genuine restricted source run.
  adequate : ∀ {t} → Core.Run Core.initial inventory t → B.Run Core.initial inventory (M.coreState t)
  adequate = adequate-covered (λ present → present)

  -- Source acceptance is the original fresh reduced wire-prefix language, with an actual endpoint.
  SourceTrace : List D.Event → Set
  SourceTrace rows = Σ[ target ∈ Core.State ] Core.Run Core.initial rows target

  -- Restricted acceptance keeps the same observed word and permits a mapped hidden endpoint.
  BasisTrace : List D.Event → Set
  BasisTrace rows = Σ[ target ∈ Core.State ] B.Run Core.initial rows target

  -- Mapping unobserved eligible offers supplies a basis witness for every covered source word.
  source→basis-covered : ∀ {rows} → (∀ {row} → row ∈ rows → row ∈ inventory) →
    SourceTrace rows → BasisTrace rows
  source→basis-covered covered (target , source) = M.coreState target , adequate-covered covered source

  -- Erasing membership evidence recovers a genuine unrestricted run at exactly the same states.
  basis→source : ∀ {rows} → BasisTrace rows → SourceTrace rows
  basis→source (target , source) = target , B.sound source

  -- Every covered merge has exactly the same unrestricted and basis-restricted wire language.
  equivalence-covered : ∀ rows → (∀ {row} → row ∈ rows → row ∈ inventory) →
    (SourceTrace rows → BasisTrace rows) × (BasisTrace rows → SourceTrace rows)
  equivalence-covered rows covered = source→basis-covered covered , basis→source

  -- The complete supplied word is a direct instance, not a different smaller profile.
  equivalence : (SourceTrace inventory → BasisTrace inventory) × (BasisTrace inventory → SourceTrace inventory)
  equivalence = equivalence-covered inventory (λ present → present)

  -- The full original node language keeps every erased environment/handler witness existentially.
  NodeSourceTrace : List D.Event → Set
  NodeSourceTrace rows = Σ[ target ∈ Node.State ] Reduction.SourceRun Node.initial rows target

  -- Original node runs normalize without losing one observed wire occurrence.
  node-to-core : ∀ {rows} → NodeSourceTrace rows → SourceTrace rows
  node-to-core (target , source) = Core.erase target , Reduction.source-to-core source

  -- A reduced source witness rehydrates to an actual original node run from its fresh state.
  core-to-node : ∀ {rows} → SourceTrace rows → NodeSourceTrace rows
  core-to-node (target , source) with Reduction.canonical source
  ... | actions , original , observed = Core.canonical target , actions , original , observed

  -- Every covered full-policy wire word has a finite-offer-basis witness.
  node→basis-covered : ∀ {rows} → (∀ {row} → row ∈ rows → row ∈ inventory) →
    NodeSourceTrace rows → BasisTrace rows
  node→basis-covered covered source = source→basis-covered covered (node-to-core source)

  -- Every basis witness is admitted by the unchanged full original node policy.
  basis→node : ∀ {rows} → BasisTrace rows → NodeSourceTrace rows
  basis→node source = core-to-node (basis→source source)

  -- Full fresh node acceptance coincides with basis acceptance for every covered endpoint merge.
  node-equivalence-covered : ∀ rows → (∀ {row} → row ∈ rows → row ∈ inventory) →
    (NodeSourceTrace rows → BasisTrace rows) × (BasisTrace rows → NodeSourceTrace rows)
  node-equivalence-covered rows covered = node→basis-covered covered , basis→node

  -- The full supplied word needs no additional source assumptions beyond the explicit fallback value.
  node-equivalence : (NodeSourceTrace inventory → BasisTrace inventory) × (BasisTrace inventory → NodeSourceTrace inventory)
  node-equivalence = node-equivalence-covered inventory (λ present → present)

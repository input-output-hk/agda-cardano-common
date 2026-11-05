{-# OPTIONS --safe #-}

-- Duplicate-free callback enumeration preserves exact source runs and all original retraction behavior.
module Cardano_network.Replay.LeiosNotifyPipeLookahead.UniqueBasisAdequacy
  (Notification Return : Set) where

open import Data.List using (List; deduplicate)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Membership.Propositional.Properties using (∈-deduplicate⁺; ∈-deduplicate⁻)
open import Data.List.Relation.Unary.Any using (here)
open import Data.List.Relation.Unary.Unique.Propositional using (Unique)
import Data.List.Relation.Unary.Unique.DecPropositional.Properties as Unique
open import Data.Product using (Σ-syntax; _×_; _,_)
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality using (refl)
import Cardano_network.LeiosNotifyPipeLookahead.Model Notification as S
import Cardano_network.LeiosNotifyPipeLookahead.DriverModel Notification Return as D
import Cardano_network.LeiosNotifyPipeLookahead.DriverBasis Notification Return as Basis
import Cardano_network.Replay.LeiosNotifyPipeLookahead.BasisAdequacy Notification Return as Old

-- Membership inclusion changes only callback membership evidence, never any source state or label.
module Inclusion (source target : List Notification)
  (include : ∀ {value} → value ∈ source → value ∈ target) where
  module From = Basis source
  module To = Basis target

  -- Cancellation remains unchanged; exact normal values retain their original membership witness value.
  allowed : ∀ {reply} → From.AllowedReply reply → To.AllowedReply reply
  allowed (From.allowNormal present) = To.allowNormal (include present)
  allowed From.allowCanceled = To.allowCanceled

  -- Every hidden transition is transported at the same arbitrary source and target states.
  tau : ∀ {p s t} → From.Tau p s t → To.Tau p s t
  tau (From.clientInternal pr) = To.clientInternal pr
  tau (From.serverInternal pr) = To.serverInternal pr
  tau (From.clientCallback classification pr) = To.clientCallback classification pr
  tau (From.serverCallback admitted pr) = To.serverCallback (allowed admitted) pr
  tau (From.commitClient pr) = To.commitClient pr
  tau (From.commitServer pr) = To.commitServer pr
  tau (From.decodeClient pr) = To.decodeClient pr
  tau (From.decodeServer pr) = To.decodeServer pr

  -- Complete finite runs preserve every visible occurrence and the entire original scheduling structure.
  run : ∀ {p s rows t} → From.Run p s rows t → To.Run p s rows t
  run From.stop = To.stop
  run (From.internal pr rest) = To.internal (tau pr) (run rest)
  run (From.visible pr rest) = To.visible pr (run rest)

-- Keep the old exact retraction and its computation gates while deduplicating enumeration only.
module ForInput (notificationEq : DecidableEquality Notification)
  (representative : Notification) (input : List D.Event) where
  module Original = Old.ForInput notificationEq representative input

  -- A payload value appears at most once in the hidden normal callback candidate alphabet.
  basis : List Notification
  basis = deduplicate notificationEq Original.basis

  module B = Basis basis
  module M = Original.M

  -- Every original normal choice is retained as exactly the same value after enumeration deduplication.
  original→unique : ∀ {value} → value ∈ Original.basis → value ∈ basis
  original→unique = ∈-deduplicate⁺ notificationEq

  -- No new normal value can be introduced by the unique callback candidate alphabet.
  unique→original : ∀ {value} → value ∈ basis → value ∈ Original.basis
  unique→original = ∈-deduplicate⁻ notificationEq Original.basis

  -- The two basis lists define precisely the same allowed normal payload membership predicate.
  membership-equivalence : ∀ {value} →
    (value ∈ Original.basis → value ∈ basis) × (value ∈ basis → value ∈ Original.basis)
  membership-equivalence = original→unique , unique→original

  -- The explicit unobserved-choice representative remains present even when observed values equal it.
  representative-present : representative ∈ basis
  representative-present = original→unique (here refl)

  -- The standard-library equality-based deduplication theorem certifies the entire candidate list.
  duplicate-free : Unique basis
  duplicate-free = Unique.deduplicate-! notificationEq Original.basis

  module Forward = Inclusion Original.basis basis original→unique
  module Backward = Inclusion basis Original.basis unique→original

  -- All-state source relation transport has no fresh-state, reachability or input-validity premise.
  tau-forward : ∀ {p s t} → Original.B.Tau p s t → B.Tau p s t
  tau-forward = Forward.tau

  -- Unique enumeration cannot create a hidden transition absent from the original basis relation.
  tau-backward : ∀ {p s t} → B.Tau p s t → Original.B.Tau p s t
  tau-backward = Backward.tau

  -- Visible rules are independent of basis membership and remain definitionally identical.
  step-forward : ∀ {p s row t} → Original.B.Step p s row t → B.Step p s row t
  step-forward pr = pr

  -- The inverse visible transport preserves exactly the same source Step certificate.
  step-backward : ∀ {p s row t} → B.Step p s row t → Original.B.Step p s row t
  step-backward pr = pr

  -- Whole original basis runs retain every exact row, source/target state and internal schedule.
  run-forward : ∀ {p s rows t} → Original.B.Run p s rows t → B.Run p s rows t
  run-forward = Forward.run

  -- The reverse whole-run transport excludes any language enlargement through deduplication.
  run-backward : ∀ {p s rows t} → B.Run p s rows t → Original.B.Run p s rows t
  run-backward = Backward.run

  -- Fresh source adequacy keeps the old retraction and exact covered input order unchanged.
  adequate-covered : ∀ {p rows t} → (∀ {row} → row ∈ rows → row ∈ input) →
    D.Run p D.initial rows t → B.Run p D.initial rows (M.state t)
  adequate-covered covered source = run-forward (Original.adequate-covered covered source)

  -- Payload-only coverage remains sufficient when reference and actual merge orders differ.
  adequate-payloads : ∀ {p rows t} →
    (∀ {row value} → row ∈ rows → value ∈ Old.payloads row → value ∈ basis) →
    D.Run p D.initial rows t → B.Run p D.initial rows (M.state t)
  adequate-payloads covered source = run-forward
    (Original.adequate-payloads (λ present payload → unique→original (covered present payload)) source)

  -- In particular, the supplied exact fresh input has a genuine run in the unique-basis model.
  adequate : ∀ {p t} → D.Run p D.initial input t → B.Run p D.initial input (M.state t)
  adequate source = run-forward (Original.adequate source)

  -- The public source language is exactly the unchanged unrestricted initial paired source language.
  SourceTrace : S.Contract → Set
  SourceTrace = Original.SourceTrace

  -- A unique-basis language witness retains an actual finite run and its exact endpoint.
  BasisTrace : S.Contract → Set
  BasisTrace p = Σ[ target ∈ D.State ] B.Run p D.initial input target

  -- Mapping hidden unobserved choices preserves the complete fresh visible input exactly.
  source→basis : ∀ {p} → SourceTrace p → BasisTrace p
  source→basis (target , source) = M.state target , adequate source

  -- Every unique-basis witness remains an original unrestricted source execution.
  basis→source : ∀ {p} → BasisTrace p → SourceTrace p
  basis→source (target , source) = target , B.sound source

  -- Deduplicated enumeration preserves both initial source-language inclusions without new premises.
  equivalence : ∀ {p} → (SourceTrace p → BasisTrace p) × (BasisTrace p → SourceTrace p)
  equivalence = source→basis , basis→source

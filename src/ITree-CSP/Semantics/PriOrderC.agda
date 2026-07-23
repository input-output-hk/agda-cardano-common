{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- CHANNEL-level order presentation for the priority operator `Priᶜ`
-- (companion of `Semantics.PriOrder`, but at CHANNEL granularity — see
-- `docs/specs/priority-implementation-plan.md`).
--
-- The value-level order (`Semantics.PriOrder`) domination test walks
-- `above : Ev → List Ev`, a FINITE list of dominating EVENTS.  That breaks
-- when a channel with an INFINITE carrier is a dominator: the up-set of a
-- dominated event then contains one entry per carried value — an infinite
-- list that cannot be enumerated.
--
-- Here domination is declared between CHANNELS (`AnyTypes E`) only; values are
-- never mentioned.  `aboveᶜ c` lists the dominating CHANNELS (one entry per
-- dominating channel, regardless of how many values each carries), so it stays
-- finite even over infinite carriers.  This is what `Priᶜ` uses (via
-- `FinBr.chan-supp`, which is also channel-level) to prioritise value-free.
--
-- Order LIFT to the Ev level (Phase 2): a `PriOrderC` induces a `PriOrderProp`
-- by `e₁ <ᵖ e₂ = chan e₁ <ᶜ chan e₂` (domination ignores values) — this is the
-- bridge from `PriOrderC` to the existing `Semantics.PriOrder.PriOrderProp`
-- used by the relational spec `Semantics.PriLTS`.
--
-- Depends only on `Process_Trees`; `--safe` (only `--guardedness`, no Classical).
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Bool using (Bool)
open import Data.List using (List; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Product using (proj₁)
open import Relation.Nullary using (¬_)

open import Process_Trees using (AnyTypes)

module Semantics.PriOrderC {ℓ ℓe} {E : Set ℓ → Set ℓe} where

------------------------------------------------------------------------
-- Propositional channel order
------------------------------------------------------------------------

-- a strict partial order on CHANNELS (`ℓo` = the order's own level); no values
record PriOrderCProp (ℓo : Level) : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓo) where
  field
    _<ᶜ_      : AnyTypes E → AnyTypes E → Set ℓo
    <ᶜ-irrefl : ∀ {a}     → ¬ (a <ᶜ a)
    <ᶜ-trans  : ∀ {a b c} → a <ᶜ b → b <ᶜ c → a <ᶜ c

-- channel `c` is ≤-maximal: no channel strictly dominates it
Maximalᶜ : ∀ {ℓo} → PriOrderCProp ℓo → AnyTypes E → Set (lsuc ℓ ⊔ ℓe ⊔ ℓo)
Maximalᶜ O c = ∀ c′ → ¬ (O .PriOrderCProp._<ᶜ_ c c′)

------------------------------------------------------------------------
-- Finitary channel order — `aboveᶜ` enumerates dominating CHANNELS
------------------------------------------------------------------------

-- a `PriOrderCProp` whose up-sets are finitely enumerable via `aboveᶜ`;
-- crucially `aboveᶜ` lists CHANNELS, so it is finite even for infinite carriers
record PriOrderC (ℓo : Level) : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓo) where
  field
    prop   : PriOrderCProp ℓo
    aboveᶜ : AnyTypes E → List (AnyTypes E)   -- dominating channels; [] ⇒ maximal

  open PriOrderCProp prop public

  field
    -- `aboveᶜ` is sound and complete for `_<ᶜ_`
    aboveᶜ-sound    : ∀ {c c′} → c′ ∈ aboveᶜ c → c <ᶜ c′
    aboveᶜ-complete : ∀ {c c′} → c <ᶜ c′ → c′ ∈ aboveᶜ c
    -- every dominating channel is inhabited: uninhabited dominators are degenerate
    -- (they can never be offered), so a well-formed priority order excludes them
    above-inhabited : ∀ {c c′} → c′ ∈ aboveᶜ c → proj₁ c′

-- `c` is ≤-maximal iff it has no dominating channels (empty `aboveᶜ` list)
isMaxᶜ? : ∀ {ℓo} → PriOrderC ℓo → AnyTypes E → Bool
isMaxᶜ? O c = null (PriOrderC.aboveᶜ O c)

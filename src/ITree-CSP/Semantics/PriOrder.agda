{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Order presentation for Roscoe's priority operator `Pri` (shared by all
-- layers of the `Pri_≤` implementation — see
-- `docs/specs/priority-implementation-plan.md`).
--
--   * `Ev`            — an event = a channel `at : AnyTypes E` together with
--                       a value `val : proj₁ at` of its carried type.
--                       (Isomorphic to `Semantics.LTS.Event`, repackaged.)
--   * `PriOrderProp`  — the PROPOSITIONAL strict partial order used by the
--                       Layer-1 relational spec (`Semantics.PriLTS`). Negative
--                       premises stay propositional; no decidability.
--   * `PriOrder`      — the FINITARY order used by the Layer-2 executable
--                       operator: `above e` lists the strict dominators of `e`
--                       (`[]` ⇒ `e` is ≤-maximal), with well-formedness lemmas
--                       linking it to a `PriOrderProp`.
--   * `dominated?`    — total boolean "some dominator of `e` is offered", the
--                       firing test the operator uses. No classical content.
--
-- Convention: τ and ✓ are ≤-maximal and never appear in any `above e`.
--
-- Placement: this order presentation depends only on `Process_Trees`, so it
-- lives in `Semantics/` — the Layer-1 spec `Semantics.PriLTS` imports it without
-- any `Semantics/ → CSP/` back-edge, and the Layer-2 operator (`CSP.Priority`)
-- imports it in the allowed `CSP/ → Semantics/` direction.
--
-- `--safe`: this module uses only `--guardedness` (safe) and imports nothing
-- from `Classical`.
------------------------------------------------------------------------

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Bool using (Bool; false; _∨_)
open import Data.List using (List; foldr)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; is-just)
open import Data.Product using (Σ; _,_; proj₁; proj₂; Σ-syntax)
open import Relation.Nullary using (¬_)

open import Process_Trees using (AnyTypes; ContinueType)

module Semantics.PriOrder {ℓ ℓe} {E : Set ℓ → Set ℓe} where

------------------------------------------------------------------------
-- Events
------------------------------------------------------------------------

-- an event: a channel `at` and a value `val` of its carried type `proj₁ at`
record Ev : Set (lsuc ℓ ⊔ ℓe) where
  constructor _∙_
  field
    at  : AnyTypes E
    val : proj₁ at
open Ev public

------------------------------------------------------------------------
-- Propositional order (Layer 1)
------------------------------------------------------------------------

-- a strict partial order on events (`ℓo` = the order's own level)
record PriOrderProp (ℓo : Level) : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓo) where
  field
    _<ᵖ_      : Ev → Ev → Set ℓo
    <ᵖ-irrefl : ∀ {a}     → ¬ (a <ᵖ a)
    <ᵖ-trans  : ∀ {a b c} → a <ᵖ b → b <ᵖ c → a <ᵖ c

-- `e` is ≤-maximal: nothing strictly dominates it (so `Pri` never blocks it)
Maximal : ∀ {ℓo} → PriOrderProp ℓo → Ev → Set (lsuc ℓ ⊔ ℓe ⊔ ℓo)
Maximal O a = ∀ b → ¬ (O .PriOrderProp._<ᵖ_ a b)

------------------------------------------------------------------------
-- Finitary order (Layer 2) — `above` enumerates strict dominators
------------------------------------------------------------------------

-- a `PriOrderProp` whose up-sets are finitely enumerable via `above`
record PriOrder (ℓo : Level) : Set (lsuc ℓ ⊔ ℓe ⊔ lsuc ℓo) where
  field
    prop  : PriOrderProp ℓo
    above : Ev → List Ev        -- strict dominators of the argument; [] ⇒ maximal

  open PriOrderProp prop public

  field
    -- `above` is sound and complete for `_<ᵖ_`
    above-sound    : ∀ {a b} → b ∈ above a → a <ᵖ b
    above-complete : ∀ {a b} → a <ᵖ b → b ∈ above a

-- total firing test: is some strict dominator of `e` offered by the visible
-- map `v`?  `is-just ∘ v` is decidable pointwise; only the ∃ over dominators
-- needs the finite presentation `above`.  No classical content.
dominated? : ∀ {ℓo ℓx} {X : Set ℓx}
           → PriOrder ℓo
           → ((at : AnyTypes E) → ContinueType at (Maybe X))
           → Ev → Bool
dominated? O v e =
  foldr (λ b acc → is-just (v (b .at) (b .val)) ∨ acc) false (PriOrder.above O e)

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- FinBr — a certificate carrying (i) a DECISION of stability, (ii) a finite
-- CHANNEL-level offer support, at each reachable state, closed under transitions.
--
-- This is a GENERAL process-tree notion (it mentions only `Process_Trees` and
-- `Semantics.LTS`), so it lives in the generic semantics layer rather than in
-- the priority layer that first needed it; it is parametric in the τ-index type
-- `I` exactly like `Semantics.LTS`.  The CSP layer instantiates `I = ExtI E`.
--
-- The τ-support cannot be enumerated as a finite list: at the CSP instantiation
-- τ-indices are keyed on `ExtI.fin`, and `fin : ∀ {n} → ExtI I (Lift ℓ (Fin n))`
-- is ℕ-polymorphic, so e.g. `br2 P Q (Lift ℓ (Fin n) , fin) (lift fzero) ≡ just P`
-- for EVERY `n ≥ 1`.  Hence stability is carried as a DECISION (`no` is witnessed
-- by ONE enabled τ at, say, `fin {1}`), never by an enumeration.
--
-- Visible offers, by contrast, are indexed by `AnyTypes E` (E DIRECTLY — no
-- `ExtI`/`fin`/ℕ-polymorphism), and each node offers finitely many CHANNELS
-- (prefix 1, □/∥ a union, ⊓/Stop/div none, rename a relabel).  Value carriers
-- may be infinite, but we track CHANNELS, so `chan-supp` stays a finite list.
-- This is what makes hide (`∖`) decidable: "P offers an A-channel" is a finite
-- fold of A-membership over `chan-supp`.
--
-- NOTE (scope): `FinBr` bounds the VISIBLE branching only.  It does NOT bound
-- τ-fan-out, so it is not a finite-branching certificate in the König sense —
-- see `CSP.Laws.FD.HideMonoFinBrFail`.
--
-- `--safe`: no `postulate`, no `NON_TERMINATING`, no `--sized-types`.
------------------------------------------------------------------------

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.List using (List)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; Is-just)
open import Data.Product using (proj₁)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module Semantics.FinBr {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open PTree

open import Semantics.LTS {ℓ} {ℓe} {ℓi} {E} {I}

-- stability decision + finite visible-channel support, propagated along steps
record FinBr {ℓr} {R : Set ℓr} (t : PTree E I R)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    -- a decision of `t`'s stability (drives `Pri`'s stable/unstable split)
    stable?    : Dec (isStable t)
    -- the finite list of channels this node visibly offers
    chan-supp  : List (AnyTypes E)
    -- every actually-offered channel at a react node is listed (finite completeness)
    chan-compl : ∀ {v τc} → PTree.force t ≡ react v τc
               → ∀ at a → Is-just (v at a) → at ∈ chan-supp
    -- the certificate propagates along every transition
    next       : ∀ {l t′} → t ─[ l ]─► t′ → FinBr t′

-- `Dec (isStable t)` is now read straight off the certificate.
stab? : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → FinBr t → Dec (isStable t)
stab? t fb = FinBr.stable? fb

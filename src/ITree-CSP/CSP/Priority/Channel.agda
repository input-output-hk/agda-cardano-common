{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- CHANNEL-level priority operator `Priᶜ` (Phase 1 — see
-- `docs/specs/priority-implementation-plan.md`).
--
-- `Priᶜ` is the value-free sibling of `CSP.Priority.Pri`: it decides
-- domination between CHANNELS (via a `PriOrderC` + the certificate's finite
-- `FinBr.chan-supp`) rather than between events.  This is exactly what supports
-- INFINITE carriers — the value-level `Pri` needs `above : Ev → List Ev`, which
-- cannot enumerate an infinite-carrier dominating channel; `Priᶜ` only ever
-- touches channels, so its domination test stays a finite `List`-membership.
--
--   * `dominatedᶜ?` — "some higher-priority CHANNEL is offered", decided as a
--                     finite membership of `aboveᶜ` in `FinBr.chan-supp`.
--                     Totally value-free ⇒ infinite carriers are fine.
--   * `Priᶜ O t fb` — mirrors `Pri`'s INVERTIBLE node-view (priForceᶜ + the
--                     value-view helpers), so `Priᶜ` is invertible too (needed
--                     for the Phase-2 adequacy bridge).
--
-- Order lift (Phase 2): a `PriOrderC` induces the Ev-level `PriOrderProp` via
-- `e₁ <ᵖ e₂ = chan e₁ <ᶜ chan e₂`, connecting this operator to the relational
-- spec `Semantics.PriLTS`.
--
-- `--safe`: no `postulate`, no `NON_TERMINATING`, no `--sized-types`, nothing
-- from `Classical`.  Corecursion in `Priᶜ` is guarded exactly like `Pri`: every
-- recursive call sits under `just`/`sil`/`react`.
------------------------------------------------------------------------

open import Level using (_⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List; [])
open import Data.Bool.ListAction using (any)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; proj₁)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Priority.Channel {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open PTree

-- channel-level order + value-free FinBr certificate + LTS steps
open import Semantics.PriOrderC {ℓ} {ℓe} {E}
open import Semantics.LTS       {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import CSP.Priority.Base        {ℓ} {ℓe} {E} using (FinBr; stab?; finBr-deadlock)
open import Data.List.Membership.DecPropositional E-≟ using (_∈?_)

------------------------------------------------------------------------
-- Channel domination test — value-free (works for infinite carriers).
------------------------------------------------------------------------

-- decide "some higher-priority CHANNEL of `chan` is in `FinBr.chan-supp fb`",
-- a finite `List`-membership over `aboveᶜ`; no value of any carrier is touched
dominatedᶜ? : ∀ {ℓo ℓr} {R : Set ℓr} {t : PTree E (ExtI E) R}
            → PriOrderC ℓo → FinBr t → AnyTypes E → Bool
dominatedᶜ? O fb chan =
  any (λ c → ⌊ c ∈? FinBr.chan-supp fb ⌋) (PriOrderC.aboveᶜ O chan)

------------------------------------------------------------------------
-- The priority operator `Priᶜ` (mirrors `CSP.Priority.Pri`, channel-level).
--
--   * stable react   : drop channel-dominated offers, keep the rest (no τ);
--   * unstable react : keep ONLY ≤-maximal channels + ALL τ-branches;
-- and every surviving residual is prioritised RECURSIVELY.
------------------------------------------------------------------------

-- forward declarations (house style — no old-style `mutual`)
priVisᶜ : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrderC ℓo)
        → (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
        → {t : PTree E (ExtI E) R}
          {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
        → PTree.force t ≡ react v τc → FinBr t
        → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
priMaxᶜ : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrderC ℓo)
        → (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
        → {t : PTree E (ExtI E) R}
          {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
        → PTree.force t ≡ react v τc → FinBr t
        → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
priTauᶜ : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrderC ℓo)
        → (τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
        → {t : PTree E (ExtI E) R}
          {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
        → PTree.force t ≡ react v τc → FinBr t
        → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
-- value-view helpers: dispatch on the ALREADY-COMPUTED channel flag + offer
-- value (passed explicitly with their equations) ⇒ the maps are INVERTIBLE by
-- casing those values (mirrors `priForceᶜ` for the node).
priVisAtᶜ : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrderC ℓo)
          → (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
          → {t : PTree E (ExtI E) R}
            {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
          → (eqf : PTree.force t ≡ react v τc) (fb : FinBr t)
            (at : AnyTypes E) (a : proj₁ at)
          → (dm : Bool) → dominatedᶜ? O fb at ≡ dm
          → (m : Maybe (PTree E (ExtI E) R)) → v at a ≡ m
          → Maybe (PTree E (ExtI E) R)
priMaxAtᶜ : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrderC ℓo)
          → (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
          → {t : PTree E (ExtI E) R}
            {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
          → (eqf : PTree.force t ≡ react v τc) (fb : FinBr t)
            (at : AnyTypes E) (a : proj₁ at)
          → (mx : Bool) → isMaxᶜ? O at ≡ mx
          → (m : Maybe (PTree E (ExtI E) R)) → v at a ≡ m
          → Maybe (PTree E (ExtI E) R)
priTauAtᶜ : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrderC ℓo)
          → (τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
          → {t : PTree E (ExtI E) R}
            {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
          → (eqf : PTree.force t ≡ react v τc) (fb : FinBr t)
            (i : AnyTypes (ExtI E)) (a : proj₁ i)
          → (m : Maybe (PTree E (ExtI E) R)) → τc i a ≡ m
          → Maybe (PTree E (ExtI E) R)
-- node-view of `Priᶜ`'s head: dispatches on the ALREADY-FORCED node `nP` (passed
-- with its force-equation) ⇒ `force (Priᶜ O t fb)` is INVERTIBLE by casing `force t`.
priForceᶜ : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrderC ℓo) {t : PTree E (ExtI E) R}
          → (nP : NodeKind E (ExtI E) R) → PTree.force t ≡ nP → FinBr t → Dec (isStable t)
          → NodeKind E (ExtI E) R
Priᶜ : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrderC ℓo)
     → (t : PTree E (ExtI E) R) → FinBr t → PTree E (ExtI E) R

-- node-view dispatch (matches the passed node `nP` + its force-eq `eqf`)
priForceᶜ O (ret r)      eqf fb _       = ret r
priForceᶜ O (sil c)      eqf fb _       = sil (Priᶜ O c (FinBr.next fb (sSil eqf)))
priForceᶜ O (react v τc) eqf fb (yes _) = react (priVisᶜ O v eqf fb) (λ _ _ → nothing)
priForceᶜ O (react v τc) eqf fb (no  _) = react (priMaxᶜ O v eqf fb) (priTauᶜ O τc eqf fb)

-- head node: route through `priForceᶜ` on `force t` (⇒ invertible), like `Pri`
force (Priᶜ O t fb) = priForceᶜ O (PTree.force t) refl fb (stab? t fb)

-- stable case: prune channel-dominated offers, prioritise each surviving residual
priVisᶜ O v eqf fb at a = priVisAtᶜ O v eqf fb at a (dominatedᶜ? O fb at) refl (v at a) refl
priVisAtᶜ O v eqf fb at a _     _ nothing   _   = nothing
priVisAtᶜ O v eqf fb at a true  _ (just t′) _   = nothing
priVisAtᶜ O v eqf fb at a false _ (just t′) eva = just (Priᶜ O t′ (FinBr.next fb (sVis eqf eva)))

-- unstable case (offers): keep ONLY ≤-maximal channels, prioritise each residual
priMaxᶜ O v eqf fb at a = priMaxAtᶜ O v eqf fb at a (isMaxᶜ? O at) refl (v at a) refl
priMaxAtᶜ O v eqf fb at a _     _ nothing   _   = nothing
priMaxAtᶜ O v eqf fb at a false _ (just t′) _   = nothing
priMaxAtᶜ O v eqf fb at a true  _ (just t′) eva = just (Priᶜ O t′ (FinBr.next fb (sVis eqf eva)))

-- unstable case (τ): keep ALL τ-branches, prioritise each residual
priTauᶜ O τc eqf fb i a = priTauAtᶜ O τc eqf fb i a (τc i a) refl
priTauAtᶜ O τc eqf fb i a nothing   _   = nothing
priTauAtᶜ O τc eqf fb i a (just t′) eia = just (Priᶜ O t′ (FinBr.next fb (sTau eqf eia)))

------------------------------------------------------------------------
-- Smoke test (a): `deadlock` — a stable react node with no transitions.
------------------------------------------------------------------------

-- the trivial (empty) channel order: nothing dominates anything
emptyPOC : PriOrderC lzero
emptyPOC = record
  { prop = record
      { _<ᶜ_      = λ _ _ → ⊥
      ; <ᶜ-irrefl = λ z → z
      ; <ᶜ-trans  = λ p _ → p
      }
  ; aboveᶜ          = λ _ → []
  ; aboveᶜ-sound    = λ ()
  ; aboveᶜ-complete = λ ()
  ; above-inhabited = λ ()
  }

-- `Priᶜ` on `deadlock` — exercises the operator end-to-end
pri-c-deadlock-smoke : ∀ {ℓr} {R : Set ℓr} → PTree E (ExtI E) R
pri-c-deadlock-smoke = Priᶜ emptyPOC deadlock finBr-deadlock

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Layer 2 (core) — the EXECUTABLE priority operator `Pri`
-- (see `docs/specs/priority-implementation-plan.md`).
--
-- The relational spec `Semantics.PriLTS._─[_]─►ᵖ_` is ground truth; here we
-- give a productive operator on process trees that realises it.  The obstacle
-- is that firing a non-maximal visible event needs the source node to be
-- STABLE, and `isStable` is a Π-type (`∀ i a → τc i a ≡ nothing`), undecidable
-- in general.  We do NOT decide the raw Π; instead every tree carries a
-- `FinBr` certificate — a coinductive record carrying a `Dec (isStable t)`
-- decision at each reachable state — and `stab?` just reads it off.  No classical
-- axiom (`dne`/`Classical`) is used anywhere.
--
--   * `FinBr t`   — stability-decision certificate for `t`, closed under steps.
--   * `stab? t fb`— `Dec (isStable t)` from the certificate.
--   * `Pri O t fb`— prioritise `t` under the finitary order `O`, RECURSING into
--                   every residual (a real operator prioritises continuations,
--                   not just the head node — unlike the plan's raw sketch).
--   * `finBr-deadlock` / `pri-deadlock-smoke` — inhabitation + smoke test.
--
-- Adequacy (`Pri` vs the relational `─►ᵖ`, up to strong bisim) is PROVED in the
-- SEPARATE module `CSP.Priority.Adequacy`, as the cross-simulation pair
-- `pri-adequacy-fwd` / `pri-adequacy-bwd`: every `Pri`-step is matched by a
-- `─►ᵖ`-step whose residual, once RE-prioritised, is strongly bisimilar to the
-- `Pri`-successor, and conversely.  It is kept apart purely for layering — it
-- needs `Semantics.PriLTS`/`Semantics.Bisim`, which THIS module does not — and
-- BOTH modules are genuinely `--safe`-green with zero postulates.
--
-- `--safe`: no `postulate`, no `NON_TERMINATING`, no `--sized-types`, and nothing
-- imported from `Classical`.  Corecursion in `Pri` is guarded exactly like `_∖_`
-- (hide): every recursive call sits under `just`/`sil`/`react`.
------------------------------------------------------------------------

open import Level using (_⊔_) renaming (suc to lsuc; zero to lzero)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; []; null)
open import Data.List.Membership.Propositional using (_∈_)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; _×_; proj₁; Σ-syntax)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Priority.Base {ℓ ℓe} {E : Set ℓ → Set ℓe} where

open PTree

-- the τ-index type is `ExtI E` throughout (binary/product/finite τ-branches)
open import Semantics.PriOrder {ℓ} {ℓe} {E}
open import Semantics.LTS      {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}

------------------------------------------------------------------------
-- FinBr — the stability-decision + finite-visible-support certificate.
--
-- It is a GENERAL process-tree notion, so it now lives in `Semantics.FinBr`
-- (parametric in the τ-index type `I`); here we merely instantiate it at the
-- CSP τ-index type `I = ExtI E` and re-export it, so that the ~22 modules that
-- get `FinBr` from `CSP.Priority.Base` need no change.  See `Semantics.FinBr`
-- for the explanation of why the τ-support is a DECISION and only the VISIBLE
-- channel support is a finite list.
------------------------------------------------------------------------

open import Semantics.FinBr {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E} public

------------------------------------------------------------------------
-- The priority operator `Pri`.
--
-- Guarded like `_∖_` (hide): every corecursive `Pri` call sits under
-- `just`/`sil`/`react`, so NO `NON_TERMINATING`.  Forward declarations (house
-- style) instead of an old-style `mutual` block.
--
--   * stable react   : drop dominated offers, keep the rest (no τ);
--   * unstable react : keep ONLY ≤-maximal offers + ALL τ-branches;
-- and in every case the surviving residual is prioritised RECURSIVELY.
------------------------------------------------------------------------

-- `e` is ≤-maximal iff it has no strict dominators (empty `above` list)
isMax? : ∀ {ℓo} → PriOrder ℓo → Ev → Bool
isMax? O e = null (PriOrder.above O e)

-- forward declarations
priVis : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
       → (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
       → {t : PTree E (ExtI E) R}
         {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
       → PTree.force t ≡ react v τc → FinBr t
       → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
priMax : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
       → (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
       → {t : PTree E (ExtI E) R}
         {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
       → PTree.force t ≡ react v τc → FinBr t
       → (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))
priTau : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
       → (τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
       → {t : PTree E (ExtI E) R}
         {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
       → PTree.force t ≡ react v τc → FinBr t
       → (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))
-- value-view helpers: dispatch on the ALREADY-COMPUTED dominance/maximality flag
-- and offer/τ value (passed explicitly with their equations), so the offer maps
-- are INVERTIBLE by casing those values (mirrors `priForce` for the node).
priVisAt : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
         → (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         → {t : PTree E (ExtI E) R}
           {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
         → PTree.force t ≡ react v τc → FinBr t → (at : AnyTypes E) (a : proj₁ at)
         → (dm : Bool) → dominated? O v (at ∙ a) ≡ dm
         → (m : Maybe (PTree E (ExtI E) R)) → v at a ≡ m
         → Maybe (PTree E (ExtI E) R)
priMaxAt : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
         → (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         → {t : PTree E (ExtI E) R}
           {τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
         → PTree.force t ≡ react v τc → FinBr t → (at : AnyTypes E) (a : proj₁ at)
         → (mx : Bool) → isMax? O (at ∙ a) ≡ mx
         → (m : Maybe (PTree E (ExtI E) R)) → v at a ≡ m
         → Maybe (PTree E (ExtI E) R)
priTauAt : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
         → (τc : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
         → {t : PTree E (ExtI E) R}
           {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
         → PTree.force t ≡ react v τc → FinBr t → (i : AnyTypes (ExtI E)) (a : proj₁ i)
         → (m : Maybe (PTree E (ExtI E) R)) → τc i a ≡ m
         → Maybe (PTree E (ExtI E) R)
-- node-view of `Pri`'s head: dispatches on the ALREADY-FORCED node `nP` (passed
-- explicitly, with its force-equation), so `force (Pri O t fb)` is INVERTIBLE by
-- casing `force t` (mirrors `hide-hVis`/`□-mt` etc.).
priForce : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo) {t : PTree E (ExtI E) R}
         → (nP : NodeKind E (ExtI E) R) → PTree.force t ≡ nP → FinBr t → Dec (isStable t)
         → NodeKind E (ExtI E) R
Pri : ∀ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
    → (t : PTree E (ExtI E) R) → FinBr t → PTree E (ExtI E) R

-- node-view dispatch (matches the passed node `nP` + its force-eq `eqf`)
priForce O (ret r)      eqf fb _       = ret r
priForce O (sil c)      eqf fb _       = sil (Pri O c (FinBr.next fb (sSil eqf)))
priForce O (react v τc) eqf fb (yes _) = react (priVis O v eqf fb) (λ _ _ → nothing)
priForce O (react v τc) eqf fb (no  _) = react (priMax O v eqf fb) (priTau O τc eqf fb)

-- head node: route through `priForce` on `force t` (⇒ invertible).  The force-eq
-- is `refl : force t ≡ force t`; when `force t` is later cased it becomes the
-- canonical proof and `priForce` reduces to the corresponding clause.
force (Pri O t fb) = priForce O (PTree.force t) refl fb (stab? t fb)

-- stable case: prune dominated offers, prioritise each surviving residual
priVis O v eqf fb at a = priVisAt O v eqf fb at a (dominated? O v (at ∙ a)) refl (v at a) refl
priVisAt O v eqf fb at a _     _ nothing   _   = nothing
priVisAt O v eqf fb at a true  _ (just t′) _   = nothing
priVisAt O v eqf fb at a false _ (just t′) eva = just (Pri O t′ (FinBr.next fb (sVis eqf eva)))

-- unstable case (offers): keep ONLY ≤-maximal offers, prioritise each residual
priMax O v eqf fb at a = priMaxAt O v eqf fb at a (isMax? O (at ∙ a)) refl (v at a) refl
priMaxAt O v eqf fb at a _     _ nothing   _   = nothing
priMaxAt O v eqf fb at a false _ (just t′) _   = nothing
priMaxAt O v eqf fb at a true  _ (just t′) eva = just (Pri O t′ (FinBr.next fb (sVis eqf eva)))

-- unstable case (τ): keep ALL τ-branches, prioritise each residual
priTau O τc eqf fb i a = priTauAt O τc eqf fb i a (τc i a) refl
priTauAt O τc eqf fb i a nothing  _   = nothing
priTauAt O τc eqf fb i a (just t′) eia = just (Pri O t′ (FinBr.next fb (sTau eqf eia)))

------------------------------------------------------------------------
-- Smoke test: `deadlock` is a stable react node with no transitions, so its
-- `FinBr` is trivial, and `Pri` applied to it typechecks (exercising the
-- operator end-to-end).
------------------------------------------------------------------------

-- `deadlock = react ∅v ∅t`: stable (τc everywhere `nothing`), offers no channel.
finBr-deadlock : ∀ {ℓr} {R : Set ℓr} → FinBr {R = R} deadlock
FinBr.stable?    finBr-deadlock          = yes (λ i a → refl)  -- τc = ∅t ⇒ stable
FinBr.chan-supp  finBr-deadlock          = []                  -- ∅v offers nothing
FinBr.chan-compl finBr-deadlock refl c x ()                    -- ∅v c x = nothing ⇒ absurd
FinBr.next       finBr-deadlock (sRet ())
FinBr.next       finBr-deadlock (sSil ())
FinBr.next       finBr-deadlock (sVis refl ())    -- v  = ∅v ⇒ `nothing ≡ just` absurd
FinBr.next       finBr-deadlock (sTau refl ())    -- τc = ∅t ⇒ `nothing ≡ just` absurd

-- the trivial (empty) priority order: nothing dominates anything
emptyPO : PriOrder lzero
emptyPO = record
  { prop = record
      { _<ᵖ_      = λ _ _ → ⊥
      ; <ᵖ-irrefl = λ z → z
      ; <ᵖ-trans  = λ p _ → p
      }
  ; above          = λ _ → []
  ; above-sound    = λ ()
  ; above-complete = λ ()
  }

-- `Pri` on `deadlock` — exercises the operator on a concrete order
pri-deadlock-smoke : ∀ {ℓr} {R : Set ℓr} → PTree E (ExtI E) R
pri-deadlock-smoke = Pri emptyPO deadlock finBr-deadlock

------------------------------------------------------------------------
-- Adequacy (ties `Pri` to the relational spec `─►ᵖ` up to strong bisim) is
-- PROVED in the SEPARATE module `CSP.Priority.Adequacy` (`pri-adequacy-fwd` /
-- `pri-adequacy-bwd`).  It lives there, not here, only for layering: it imports
-- `Semantics.PriLTS` and `Semantics.Bisim`, which this module has no need of.
-- That module is `--safe`-green and postulate-free as well.
------------------------------------------------------------------------

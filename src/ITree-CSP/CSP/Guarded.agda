{-# OPTIONS --guardedness #-}

-- The two RHS constructs of the full (menu) hide-step law, expressed over an
-- arbitrary visible offer map `v` (the menu `?x:A→P`, A = whatever v offers):
--
--   • RPrefix v X  =  ?x:(A∖X) → (P x∖X)        — the SURVIVING menu: a prefix-choice
--     (`pchoice`) over `v` with the X-hidden events dropped and the kept continuations
--     hidden on.  This is exactly the visible part of `(pchoice v) ∖ X`, namely
--     `pchoice (hide-hVis X (react v ∅t))`.
--
--   • GChoice v X  =  ⨅{ P a∖X | a∈A, a∈X }     — the guarded internal choice over the
--     HIDDEN events: the pure-τ node `react ∅v (hide-hTau X (react v ∅t))`, i.e. exactly
--     the τ-part of `(pchoice v) ∖ X`.
--
-- Defining them from the hide maps (rather than fresh maps) is what lets the full
-- hide-step proof avoid any connecting bisimulation: `(pchoice v) ∖ X` and the fused
-- node `react V τc` then share their force DEFINITIONALLY (see CSP.Laws.FD.HideStepFull).

open import Level using (Level)
open import Data.Maybe using (Maybe; just; nothing)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Guarded {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS {E = E} {I = ExtI E}

private
  variable
    ℓr : Level
    R  : Set ℓr

-- the surviving menu  ?x:(A∖X)→(P∖X)  =  visible part of (pchoice v) ∖ X
RPrefix : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
          (X : EventSet) → PTree E (ExtI E) R
RPrefix v X = pchoice (hide-hVis X (react v ∅t))

-- the hidden internal choice  ⨅{ P a∖X | a∈A∩X }  =  τ part of (pchoice v) ∖ X
GChoice : (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
          (X : EventSet) → PTree E (ExtI E) R
GChoice v X = ptree (react ∅v (hide-hTau X (react v ∅t)))

-- `(pchoice v) ∖ X` and `GChoice v X` carry the SAME τ-map (hide-hTau X (react v ∅t)),
-- differing only in their visible part — so a τ of the former is a τ of the latter.
hide-τ→gchoice-τ : {v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
                   {X : EventSet} {M : PTree E (ExtI E) R}
                 → ((pchoice v) ∖ X) ─[ τ ]─► M → (GChoice v X) ─[ τ ]─► M
hide-τ→gchoice-τ (sSil ())
hide-τ→gchoice-τ (sTau {i = i} {a = a} refl br) = sTau {i = i} {a = a} refl br

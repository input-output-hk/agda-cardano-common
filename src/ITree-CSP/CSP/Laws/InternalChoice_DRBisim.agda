{-
  Internal-choice laws for ITree-CSP, validated w.r.t. divergence-respecting
  weak bisimulation (DRWbisim) with propositional equality on return values.

  We work with the abbreviation
      _≈_  =  DRWbisim _≡_
  introduced in ITree_Relations.DRWeakBisim.

  Laws proved here:

    ⊓-comm   :  P ⊓ Q  ≈ Q ⊓ P
    ⊓-idem   :  P ⊓ P  ≈ P

  Stated but commented out (does NOT hold under DRWbisim — see end of file):

    ⊓-assoc  :  (P ⊓ Q) ⊓ R  ≈  P ⊓ (Q ⊓ R)
-}

{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_; Lift; lift; lower)
                 renaming (zero to lzero; suc to lsuc)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax; ∃-syntax)
open import Data.Maybe   using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)
open import Data.Unit.Base renaming (tt to tt₀)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality
     using (_≡_; refl)

open import Class.DecEq using (DecEq; _≟_)

open import Prelude
open import Interaction_Trees
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences using (Divergent; divergent-prefix)
open import ITree_Relations.DRWeakBisim

module CSP.Laws.InternalChoice_DRBisim
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

import CSP.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

open ITree
open Label
open DRWSimF
open DRWbisim

-- Reusable equivalence-closure helpers for `≈ = DRWbisim _≡_`.
private
  open module EQ {ℓ' ℓe' ℓi' ℓr'} {E' : Set ℓ' → Set ℓe'}
                 {I' : Set ℓ' → Set ℓi'} {R' : Set ℓr'} =
        DRWbisimEquiv {E = E'} {I = I'} {R = R'} {RetRel = _≡_} ≡-equiv
        using (drwbisim-refl)

-----------------------------------------------------------------------------
-- Commutativity of internal choice.
--
-- `force (P ⊓ Q) = ndbr (br2 P Q) (Lift _ (Fin 2) , fin) (lift fzero) ...`,
-- so any τ step out of `(P ⊓ Q)` is `sNdbr` choosing branch `lift fzero`
-- (yielding P) or `lift (fsuc fzero)` (yielding Q).  In `(Q ⊓ P)` the
-- two branches are swapped, so the matching step picks the *opposite*
-- index — successor is identical, bisim is reflexive.
⊓-comm :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (P Q : ITree E (ExtI I) R)
  → (P ⊓ Q) ≈ (Q ⊓ P)
-- on-ret: force (P ⊓ Q) is ndbr, not ret.
⊓-comm P Q .fwd .on-ret ()
-- on-vis: force (P ⊓ Q) is ndbr, not vis.  The step's force-eq is
-- `force (P ⊓ Q) ≡ vis _`, which is absurd.
⊓-comm P Q .fwd .on-vis (sVis () _)
-- on-tau: case on the τ step; only sNdbr possible.
⊓-comm P Q .fwd .on-tau (sSil ())
⊓-comm P Q .fwd .on-tau (sNdbr {i = (_ , base _)}   refl ())
⊓-comm P Q .fwd .on-tau (sNdbr {i = (_ , pair _ _)} refl ())
⊓-comm P Q .fwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl) =
    P ,
    weak-τ (τ*-step
              (sNdbr {p = Q ⊓ P} {f = br2 Q P}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                     refl refl)
              τ*-zero) ,
    drwbisim-refl P
⊓-comm P Q .fwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl) =
    Q ,
    weak-τ (τ*-step
              (sNdbr {p = Q ⊓ P} {f = br2 Q P}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                     refl refl)
              τ*-zero) ,
    drwbisim-refl Q
⊓-comm P Q .fwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))} refl ())
-- on-div: divergence flows through one of the two branches.  Reuse the
-- on-tau result via `divergent-prefix`.
⊓-comm P Q .fwd .on-div d
  with ⊓-comm P Q .fwd .on-tau (d .Divergent.step)
... | t' , weak-τ chain , bisim =
        divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))
-- bwd: by symmetry — same proof with P, Q swapped.
⊓-comm P Q .bwd .on-ret ()
⊓-comm P Q .bwd .on-vis (sVis () _)
⊓-comm P Q .bwd .on-tau (sSil ())
⊓-comm P Q .bwd .on-tau (sNdbr {i = (_ , base _)}   refl ())
⊓-comm P Q .bwd .on-tau (sNdbr {i = (_ , pair _ _)} refl ())
⊓-comm P Q .bwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl) =
    Q ,
    weak-τ (τ*-step
              (sNdbr {p = P ⊓ Q} {f = br2 P Q}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                     refl refl)
              τ*-zero) ,
    drwbisim-refl Q
⊓-comm P Q .bwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl) =
    P ,
    weak-τ (τ*-step
              (sNdbr {p = P ⊓ Q} {f = br2 P Q}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                     refl refl)
              τ*-zero) ,
    drwbisim-refl P
⊓-comm P Q .bwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))} refl ())
⊓-comm P Q .bwd .on-div d
  with ⊓-comm P Q .bwd .on-tau (d .Divergent.step)
... | t' , weak-τ chain , bisim =
        divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))

-----------------------------------------------------------------------------
-- Idempotence of internal choice.
--
-- `force (P ⊓ P) = ndbr (br2 P P) (Lift _ (Fin 2) , fin) (lift fzero) ...`
-- with both `br2`-branches yielding `P`, so any τ step out of `(P ⊓ P)`
-- has successor `P` — bisim is reflexive.  In the bwd direction, every
-- step of `P` is matched by `(P ⊓ P)` doing one τ to `P` (via `br2`'s
-- first branch) and then the same step.
⊓-idem :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (P : ITree E (ExtI I) R)
  → (P ⊓ P) ≈ P
-- fwd: every step of `(P ⊓ P)` is matched by `P` doing nothing.
-- on-ret/on-vis: force is ndbr, not ret or vis.
⊓-idem P .fwd .on-ret ()
⊓-idem P .fwd .on-vis (sVis () _)
-- on-tau: force is ndbr, not sil.  For sNdbr the index must be `fin`
-- (base/pair give `nothing`); both productive `fin` branches yield P.
⊓-idem P .fwd .on-tau (sSil ())
⊓-idem P .fwd .on-tau (sNdbr {i = (_ , base _)}   refl ())
⊓-idem P .fwd .on-tau (sNdbr {i = (_ , pair _ _)} refl ())
⊓-idem P .fwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl) =
    P , weak-τ τ*-zero , drwbisim-refl P
⊓-idem P .fwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl) =
    P , weak-τ τ*-zero , drwbisim-refl P
⊓-idem P .fwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))} refl ())
-- on-div: divergence flows through one of the two `P`-branches.  Reuse
-- the on-tau result via `divergent-prefix` (as in `⊓-comm`).
⊓-idem P .fwd .on-div d
  with ⊓-idem P .fwd .on-tau (d .Divergent.step)
... | t' , weak-τ chain , bisim =
        divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))
-- bwd: every step of `P` is matched by `(P ⊓ P)` first τ-stepping to P
-- (via `br2`'s `lift fzero` branch) and then performing the same step.
⊓-idem P .bwd .on-ret {r = r} eq =
    P , r ,
    weak-τ (τ*-step
              (sNdbr {p = P ⊓ P} {f = br2 P P}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                     refl refl)
              τ*-zero) ,
    eq , refl
⊓-idem P .bwd .on-vis {t₁' = t'} step =
    t' ,
    weak-ev (τ*-step
               (sNdbr {p = P ⊓ P} {f = br2 P P}
                      {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                      refl refl)
               τ*-zero)
            step τ*-zero ,
    drwbisim-refl t'
⊓-idem P .bwd .on-tau {t₁' = t'} step =
    t' ,
    weak-τ (τ*-step
              (sNdbr {p = P ⊓ P} {f = br2 P P}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                     refl refl)
              (τ*-step step τ*-zero)) ,
    drwbisim-refl t'
-- on-div: lift `Divergent P` to `Divergent (P ⊓ P)` by prepending the
-- τ step `(P ⊓ P) ─[τ]─► P` and reusing the original divergence (since
-- the chosen branch IS `P`).
⊓-idem P .bwd .on-div d = aux
  where
    aux : Divergent (P ⊓ P)
    aux .Divergent.next    = P
    aux .Divergent.step    =
        sNdbr {p = P ⊓ P} {f = br2 P P}
              {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
              refl refl
    aux .Divergent.diverge = d

-----------------------------------------------------------------------------
-- ⊓-assoc :  (P ⊓ Q) ⊓ R  ≈  P ⊓ (Q ⊓ R)
--
-- This law holds in classical CSP under trace, failures, and
-- failures-divergences semantics, but it does NOT hold under
-- `DRWbisim _≡_` as defined in this development.  We state it here
-- (commented out) so the gap is visible, and document the failure.
--
-- Why it fails:
--   `_⊓_` is encoded as `ndbr (br2 _ _) (Lift _ (Fin 2) , fin) ...`,
--   so each internal choice emits a real τ-transition with observable
--   branching.  DRWbisim is the standard delay-/weak-bisim:
--     on-tau : t₁ ─[τ]─► t₁'  ⇒  ∃ t₂'. t₂ ═[τ]═► t₂' × t₁' ≈ t₂'
--   Re-bracketing internal choice changes the branching tree at depth 1
--   in a way that no τ*-saturation can recover.
--
-- Concrete counterexample.  Let P = ret 0, Q = ret 1, R = ret 2.
--   LHS = (P ⊓ Q) ⊓ R  has τ-successors  { P ⊓ Q , R } .
--   RHS = P ⊓ (Q ⊓ R)  has τ-successors  { P , Q ⊓ R } .
--
--   The fwd τ-step  LHS ─[τ]─► (P ⊓ Q)  must be matched by some
--   t₂' weakly τ*-reachable from RHS with `P ⊓ Q ≈ t₂'`.  The τ*-
--   reachable states from RHS are:
--       P ⊓ (Q ⊓ R) ,  P ,  Q ⊓ R ,  Q ,  R   (= ret 0, 1, 2 for stable ones)
--   None is DRWbisim-equivalent to `P ⊓ Q`:
--     - `P` and `Q` and `R` are stable rets; `P ⊓ Q` has two τ-successors.
--     - `Q ⊓ R` has τ-successors {ret 1, ret 2}; `P ⊓ Q` has {ret 0, ret 1};
--       the τ-step `P ⊓ Q ─[τ]─► ret 0` cannot be matched by any τ*-
--       derivative of `Q ⊓ R` (no ret-0 successor exists), so they are
--       not bisim.
--     - `P ⊓ (Q ⊓ R)` itself fails for the symmetric reason: its
--       τ-step to `Q ⊓ R` has no match in `P ⊓ Q`.
--
-- Strong bisim is even worse: `SSimF.on-tau` requires a *single* τ-step
-- match (no τ*), so any failure under DRWbisim is a fortiori a failure
-- under strong bisim.
--
-- What does hold:
--   • Trace equivalence — see `InternalChoice-trace` in CSP/Traces.agda.
--   • Stable-failures and failures-divergences equivalence (when those
--     models are added).
--   • A coarser bisimulation that saturates τ-steps from `_⊓_` (treating
--     all `ndbr`-successors as one equivalence class).
--
-- {-
-- ⊓-assoc :
--   ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
--   → (P Q R : ITree E (ExtI I) R)
--   → ((P ⊓ Q) ⊓ R) ≈ (P ⊓ (Q ⊓ R))
-- ⊓-assoc P Q R = {!  -- does NOT hold under DRWbisim _≡_; see comment above !}
-- -}

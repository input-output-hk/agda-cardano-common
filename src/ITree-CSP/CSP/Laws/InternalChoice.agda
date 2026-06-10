{-
  Trace, failures/divergences, and DR-weak-bisimulation laws for
  internal choice _⊓_.
-}

{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_; Lift; lift; lower)
                 renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing; Is-just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Maybe.Relation.Unary.Any using (Any) renaming (just to any-just)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Base using () renaming (tt to tt₀)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; Σ-syntax; ∃-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (List; []; _∷_; _++_)
open import Function using (case_of_)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Relation.Binary.PropositionalEquality
     using (_≡_; refl; sym; trans; subst; cong)

open import Class.DecEq using (DecEq; _≟_)

open import Prelude
open import Interaction_Trees
open import CSP.Definitions.Basic_Processes
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences
open import ITree_Relations.DRWeakBisim
open import ITree_Relations.FailuresDivergencesEquiv

module CSP.Laws.InternalChoice
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where

open ITree
open Label
open Event√
open Traces
open Failures
open IsDivergence
open DRWSimF
open DRWbisim

import CSP.Definitions.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

open import CSP.Laws.BasicProcesses {ℓ} {ℓe} {E} E-≟

-- Reusable equivalence-closure helpers for `≈ = DRWbisim _≡_`.
private
  open module EQ {ℓ' ℓe' ℓi' ℓr'} {E' : Set ℓ' → Set ℓe'}
                 {I' : Set ℓ' → Set ℓi'} {R' : Set ℓr'} =
        DRWbisimEquiv {E = E'} {I = I'} {R = R'} {RetRel = _≡_} ≡-equiv
        using (drwbisim-refl; drwbisim-sym)

-----------------------------------------------------------------------------
-- Step lemmas: P ⊓ Q always τ-reaches its two operands directly.
-----------------------------------------------------------------------------

⊓-step-L : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         → (P Q : ITree E (ExtI I) R) → (P ⊓ Q) ─[ τ ]─► P
⊓-step-L P Q = sNdbr {p = P ⊓ Q} {f = br2 P Q}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                     refl refl

⊓-step-R : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         → (P Q : ITree E (ExtI I) R) → (P ⊓ Q) ─[ τ ]─► Q
⊓-step-R P Q = sNdbr {p = P ⊓ Q} {f = br2 P Q}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                     refl refl

-----------------------------------------------------------------------------
-- Trace lemmas
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------------------
-- Internal choice ⊓
-- traces [P ⊓ Q] = traces [P] ∪ traces [Q]

InternalChoice-trace : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (P Q : ITree E (ExtI I) R) {s : List (Event√ E R)}
  → traces {I = ExtI I} {R = R} (_⊓_ {I = I} {R = R} P Q) s
  → traces P s ⊎ traces Q s

InternalChoice-trace P Q (_ , bNil) = inj₁ (_ , bNil)

-- Internal choice cannot take visible or return steps directly
InternalChoice-trace P Q (_ , bStep (sVis () _) _)
InternalChoice-trace P Q (_ , bStep (sRet ()) _)

InternalChoice-trace P Q (._ , bTau (sNdbr {i = i} {a = a} eq-f eq-j) big-step)
  with i | a | eq-f
-- Case: Branch fzero (P)
-- By matching eq-f as refl, Agda now knows f is br2.
-- br2 (_ , fin) (lift fzero) simplifies definitionally to (just P).
... | (_ , fin) | (lift fzero) | refl =
    -- Now eq-j has type: just P ≡ just t'
    let t'-is-P = just-injective eq-j
    in inj₁ (_ , subst (λ t → t ═⟨ _ ⟩═► _) (sym t'-is-P) big-step)

-- Case: Branch fsuc fzero (Q)
... | (_ , fin) | (lift (fsuc fzero)) | refl =
    -- Now eq-j has type: just Q ≡ just t'
    let t'-is-Q = just-injective eq-j
    in inj₂ (_ , subst (λ t → t ═⟨ _ ⟩═► _) (sym t'-is-Q) big-step)

------------------------------------------------------------------------
-- Introduction direction for `InternalChoice-trace`.
-- Lift a trace of P (resp. Q) into a trace of (P ⊓ Q) via the τ-step.
------------------------------------------------------------------------
IntChoice-trace-introL : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → traces P s → traces (P ⊓ Q) s
IntChoice-trace-introL {P = P} {Q} (P′ , bs) = P′ , bTau (⊓-step-L P Q) bs

IntChoice-trace-introR : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → traces Q s → traces (P ⊓ Q) s
IntChoice-trace-introR {P = P} {Q} (Q′ , bs) = Q′ , bTau (⊓-step-R P Q) bs

------------------------------------------------------------------------
-- Refinement-order corollaries:  (P ⊓ Q) ⊑ᵀ P   and   (P ⊓ Q) ⊑ᵀ Q.
------------------------------------------------------------------------
⊑ᵀ-⊓-L : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {P Q : ITree E (ExtI I) R}
         → (P ⊓ Q) ⊑ᵀ P
⊑ᵀ-⊓-L = IntChoice-trace-introL

⊑ᵀ-⊓-R : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {P Q : ITree E (ExtI I) R}
         → (P ⊓ Q) ⊑ᵀ Q
⊑ᵀ-⊓-R = IntChoice-trace-introR

------------------------------------------------------------------------
-- Monotonicity of _⊓_ under _⊑ᵀ_.
------------------------------------------------------------------------
⊓-mono-⊑ᵀ : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              {P P′ Q Q′ : ITree E (ExtI I) R}
            → P ⊑ᵀ P′ → Q ⊑ᵀ Q′
            → (P ⊓ Q) ⊑ᵀ (P′ ⊓ Q′)
⊓-mono-⊑ᵀ {P = P} {P′ = P′} {Q = Q} {Q′ = Q′} P⊑P′ Q⊑Q′ tr-rhs
  with InternalChoice-trace P′ Q′ tr-rhs
... | inj₁ tr-P′ = IntChoice-trace-introL (P⊑P′ tr-P′)
... | inj₂ tr-Q′ = IntChoice-trace-introR (Q⊑Q′ tr-Q′)

-----------------------------------------------------------------------------
-- DRBisim lemmas
-----------------------------------------------------------------------------

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
-- Congruence of internal choice.
--
-- `force (P ⊓ Q) = ndbr (br2 P Q) ...`, and the only τ-successors are
-- `P` (via `lift fzero`) and `Q` (via `lift (fsuc fzero)`).  For
-- `(P₁ ⊓ Q₁) ≈ (P₂ ⊓ Q₂)` we match each branch with the same branch
-- on the RHS, using the supplied bisims `bP : P₁ ≈ P₂` and `bQ : Q₁ ≈ Q₂`.
⊓-cong :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → {P₁ P₂ Q₁ Q₂ : ITree E (ExtI I) R}
  → P₁ ≈ P₂ → Q₁ ≈ Q₂
  → (P₁ ⊓ Q₁) ≈ (P₂ ⊓ Q₂)
-- fwd: τ steps of (P₁ ⊓ Q₁) matched by same-index step of (P₂ ⊓ Q₂).
⊓-cong bP bQ .fwd .on-ret ()
⊓-cong bP bQ .fwd .on-vis (sVis () _)
⊓-cong bP bQ .fwd .on-tau (sSil ())
⊓-cong bP bQ .fwd .on-tau (sNdbr {i = (_ , base _)}   refl ())
⊓-cong bP bQ .fwd .on-tau (sNdbr {i = (_ , pair _ _)} refl ())
⊓-cong {P₂ = P₂} {Q₂ = Q₂} bP bQ .fwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl) =
    P₂ ,
    weak-τ (τ*-step
              (sNdbr {p = P₂ ⊓ Q₂} {f = br2 P₂ Q₂}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                     refl refl)
              τ*-zero) ,
    bP
⊓-cong {P₂ = P₂} {Q₂ = Q₂} bP bQ .fwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl) =
    Q₂ ,
    weak-τ (τ*-step
              (sNdbr {p = P₂ ⊓ Q₂} {f = br2 P₂ Q₂}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                     refl refl)
              τ*-zero) ,
    bQ
⊓-cong bP bQ .fwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))} refl ())
⊓-cong bP bQ .fwd .on-div d
  with ⊓-cong bP bQ .fwd .on-tau (d .Divergent.step)
... | t' , weak-τ chain , bisim =
        divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))
-- bwd: symmetric — match same-index steps using `drwbisim-sym` of the
-- supplied bisims.
⊓-cong bP bQ .bwd .on-ret ()
⊓-cong bP bQ .bwd .on-vis (sVis () _)
⊓-cong bP bQ .bwd .on-tau (sSil ())
⊓-cong bP bQ .bwd .on-tau (sNdbr {i = (_ , base _)}   refl ())
⊓-cong bP bQ .bwd .on-tau (sNdbr {i = (_ , pair _ _)} refl ())
⊓-cong {P₁ = P₁} {Q₁ = Q₁} bP bQ .bwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift fzero} refl refl) =
    P₁ ,
    weak-τ (τ*-step
              (sNdbr {p = P₁ ⊓ Q₁} {f = br2 P₁ Q₁}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift fzero}
                     refl refl)
              τ*-zero) ,
    drwbisim-sym bP
⊓-cong {P₁ = P₁} {Q₁ = Q₁} bP bQ .bwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl) =
    Q₁ ,
    weak-τ (τ*-step
              (sNdbr {p = P₁ ⊓ Q₁} {f = br2 P₁ Q₁}
                     {i = (Lift ℓ (Fin 2) , fin)} {a = lift (fsuc fzero)}
                     refl refl)
              τ*-zero) ,
    drwbisim-sym bQ
⊓-cong bP bQ .bwd .on-tau
  (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))} refl ())
⊓-cong bP bQ .bwd .on-div d
  with ⊓-cong bP bQ .bwd .on-tau (d .Divergent.step)
... | t' , weak-τ chain , bisim =
        divergent-prefix chain (bisim .fwd .on-div (d .Divergent.diverge))

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
--   • Trace equivalence — see `InternalChoice-trace` above.
--   • Stable-failures and failures-divergences equivalence — see
--     `⊓-assoc-FD` below.
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

-----------------------------------------------------------------------------
-- FD lemmas
-----------------------------------------------------------------------------

-----------------------------------------------------------------------------
-- failures decomposes as a sum: failures (P ⊓ Q) = failures P ⊎ failures Q.
-----------------------------------------------------------------------------

-- Intro-L: prepend a τ-step from `P ⊓ Q` to `P` in front of any failure
-- of P; the visible-label list `s` is unchanged because the prepended
-- step is `bTau`.
⊓-failures-introL :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures P s B → failures (P ⊓ Q) s B
⊓-failures-introL {P = P} {Q = Q} (T , bigstep , refusal) =
  T , bTau (⊓-step-L P Q) bigstep , refusal

⊓-failures-introR :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures Q s B → failures (P ⊓ Q) s B
⊓-failures-introR {P = P} {Q = Q} (T , bigstep , refusal) =
  T , bTau (⊓-step-R P Q) bigstep , refusal

-- Elim: invert a failure of P ⊓ Q.  The trace must take a τ-step out of
-- P ⊓ Q first (force = ndbr admits no `bNil` witness for refusal and no
-- `bStep`/sVis/sRet step).  The τ-step picks a `br2`-branch leading to
-- P (lift fzero) or Q (lift (fsuc fzero)); other branches yield
-- `nothing` and are absurd.
⊓-failures-elim :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures (P ⊓ Q) s B
  → failures P s B ⊎ failures Q s B
⊓-failures-elim {P = P} {Q = Q} {B = B} (T , bigstep , refusal) =
    go bigstep refusal
  where
    go : ∀ {s} → (P ⊓ Q) ═⟨ s ⟩═► T → T ref B
       → failures P s B ⊎ failures Q s B
    -- bNil : T = P ⊓ Q.  Refusal of an ndbr-shaped tree is impossible:
    -- ref-stable needs `isStable (P ⊓ Q)` (= ⊥), ref-tick needs
    -- `force (P ⊓ Q) ≡ ret _` (it is `ndbr _`).
    go bNil (ref-stable () _)
    go bNil (ref-tick (sRet ()) _)
    -- bTau: τ from P ⊓ Q is sNdbr (force is ndbr, sSil absurd).
    go (bTau (sSil ()) _) _
    go (bTau (sNdbr {i = (_ , base _)}   refl ()) _) _
    go (bTau (sNdbr {i = (_ , pair _ _)} refl ()) _) _
    go (bTau (sNdbr {i = (_ , fin)} {a = lift fzero}        refl refl) rest) ref =
        inj₁ (T , rest , ref)
    go (bTau (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)} refl refl) rest) ref =
        inj₂ (T , rest , ref)
    go (bTau (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))} refl ()) _) _
    -- bStep: ev from P ⊓ Q is impossible (force is ndbr).
    go (bStep (sRet ())   _) _
    go (bStep (sVis () _) _) _

-----------------------------------------------------------------------------
-- divergences decomposes as a sum:
--   divergences (P ⊓ Q) = divergences P ⊎ divergences Q.
-----------------------------------------------------------------------------

⊓-divergences-introL :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → divergences P s → divergences (P ⊓ Q) s
⊓-divergences-introL {P = P} {Q = Q} d = record
  { prefix  = d .prefix
  ; suffix  = d .suffix
  ; split   = d .split
  ; witness = d .witness
  ; reach   = bTau (⊓-step-L P Q) (d .reach)
  ; divwit  = d .divwit
  }

⊓-divergences-introR :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → divergences Q s → divergences (P ⊓ Q) s
⊓-divergences-introR {P = P} {Q = Q} d = record
  { prefix  = d .prefix
  ; suffix  = d .suffix
  ; split   = d .split
  ; witness = d .witness
  ; reach   = bTau (⊓-step-R P Q) (d .reach)
  ; divwit  = d .divwit
  }

-- Elim for divergences.  The reach `(P ⊓ Q) ═⟨ pre ⟩═► witness` either
-- starts with a τ-step into P/Q (bTau) — re-anchor the trace at P or Q —
-- or is `bNil` with `witness = P ⊓ Q`, in which case the divergent
-- witness's first τ-step lands at P or Q and we re-anchor on that.
⊓-divergences-elim :
  ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
  → divergences (P ⊓ Q) s
  → divergences P s ⊎ divergences Q s
⊓-divergences-elim {I = I} {R = R} {P = P} {Q = Q} {s = s}
  record { prefix = pre ; suffix = suf ; split = sp
         ; witness = w  ; reach = r ; divwit = dw } =
    go suf sp r dw
  where
    -- Inner helper for the `bNil`-prefix case: in that branch the trace
    -- itself is empty, so the divergent witness's first τ-step is the
    -- only thing that picks a br2 branch.  Records produced here use
    -- `prefix = []` and `suffix = s` (forced by `reach = bNil`).
    -- Splitting out into `aux` lets the `refl` in `sNdbr … refl refl`
    -- unify `next` with `P`/`Q` — impossible if `next` were a record
    -- projection like `dpq .Divergent.next`.
    aux : (next : ITree E (ExtI I) R)
        → (P ⊓ Q) ─[ τ ]─► next
        → Divergent next
        → divergences P s ⊎ divergences Q s
    aux next (sSil ()) _
    aux next (sNdbr {i = (_ , base _)}   refl ()) _
    aux next (sNdbr {i = (_ , pair _ _)} refl ()) _
    aux next (sNdbr {i = (_ , fin)} {a = lift fzero}
                    refl refl) dnext =
        inj₁ (record
          { prefix = [] ; suffix = s ; split = refl
          ; witness = next ; reach = bNil ; divwit = dnext
          })
    aux next (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)}
                    refl refl) dnext =
        inj₂ (record
          { prefix = [] ; suffix = s ; split = refl
          ; witness = next ; reach = bNil ; divwit = dnext
          })
    aux next (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))}
                    refl ()) _

    -- Walk the trace `(P ⊓ Q) ═⟨ pre' ⟩═► w'`.  We thread `suf'`/`sp'`
    -- through but make `pre'` implicit so that the `bNil` pattern can
    -- refine it to `[]` automatically (otherwise `pre'` would be a
    -- pattern variable and Agda couldn't unify it with `[]`).
    go : (suf' : List (Event√ E R))
       → ∀ {pre'} → s ≡ pre' ++ suf'
       → ∀ {w'}
       → (P ⊓ Q) ═⟨ pre' ⟩═► w'
       → Divergent w'
       → divergences P s ⊎ divergences Q s
    -- bNil : pre' = [], w' = P ⊓ Q.  Delegate to `aux`.
    go suf' sp' bNil dpq =
      aux (dpq .Divergent.next) (dpq .Divergent.step)
          (dpq .Divergent.diverge)
    -- bTau : the τ-step is sNdbr (force = ndbr).  Re-anchor on P or Q.
    go _ _ (bTau (sSil ())                              _) _
    go _ _ (bTau (sNdbr {i = (_ , base _)}   refl ())   _) _
    go _ _ (bTau (sNdbr {i = (_ , pair _ _)} refl ())   _) _
    go suf' sp' (bTau (sNdbr {i = (_ , fin)} {a = lift fzero}
                              refl refl) rest) dw' =
        inj₁ (record
          { prefix = _ ; suffix = suf' ; split = sp'
          ; witness = _ ; reach = rest ; divwit = dw'
          })
    go suf' sp' (bTau (sNdbr {i = (_ , fin)} {a = lift (fsuc fzero)}
                              refl refl) rest) dw' =
        inj₂ (record
          { prefix = _ ; suffix = suf' ; split = sp'
          ; witness = _ ; reach = rest ; divwit = dw'
          })
    go _ _ (bTau (sNdbr {i = (_ , fin)} {a = lift (fsuc (fsuc _))}
                        refl ()) _) _
    -- bStep: ev from P ⊓ Q impossible.
    go _ _ (bStep (sRet ())   _) _
    go _ _ (bStep (sVis () _) _) _

-----------------------------------------------------------------------------
-- failures⊥ inherits the sum decomposition via case-split on the
-- `failures ⊎ divergences` representation.
-----------------------------------------------------------------------------

⊓-failures⊥-introL :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures⊥ P s B → failures⊥ (P ⊓ Q) s B
⊓-failures⊥-introL (inj₁ f) = inj₁ (⊓-failures-introL f)
⊓-failures⊥-introL (inj₂ d) = inj₂ (⊓-divergences-introL d)

⊓-failures⊥-introR :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures⊥ Q s B → failures⊥ (P ⊓ Q) s B
⊓-failures⊥-introR (inj₁ f) = inj₁ (⊓-failures-introR f)
⊓-failures⊥-introR (inj₂ d) = inj₂ (⊓-divergences-introR d)

⊓-failures⊥-elim :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {P Q : ITree E (ExtI I) R} {s : List (Event√ E R)}
    {B : Event√ E R → Set ℓB}
  → failures⊥ (P ⊓ Q) s B
  → failures⊥ P s B ⊎ failures⊥ Q s B
⊓-failures⊥-elim (inj₁ f) with ⊓-failures-elim f
... | inj₁ fP = inj₁ (inj₁ fP)
... | inj₂ fQ = inj₂ (inj₁ fQ)
⊓-failures⊥-elim (inj₂ d) with ⊓-divergences-elim d
... | inj₁ dP = inj₁ (inj₂ dP)
... | inj₂ dQ = inj₂ (inj₂ dQ)

-----------------------------------------------------------------------------
-- Associativity of internal choice in the FD model.
--
-- Given the sum decomposition lemmas, the proof is just associativity
-- of `_⊎_`: a failure⊥ of `P ⊓ (Q ⊓ R)` decomposes as
--     failures⊥ P ⊎ (failures⊥ Q ⊎ failures⊥ R)
-- which by re-bracketing is
--     (failures⊥ P ⊎ failures⊥ Q) ⊎ failures⊥ R
-- and re-introduces as a failure⊥ of `(P ⊓ Q) ⊓ R`.  Same shape for
-- divergences.  The two refinements pair into `≃FD`.
-----------------------------------------------------------------------------

⊓-assoc-FD :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr} ⦃ _ : DecEq R ⦄
  → (P Q R' : ITree E (ExtI I) R)
  → _≃FD_ {ℓB = ℓB} ((P ⊓ Q) ⊓ R') (P ⊓ (Q ⊓ R'))
⊓-assoc-FD P Q R' = (fwd-F⊥ , fwd-D) , (bwd-F⊥ , bwd-D)
  where
    -- ((P ⊓ Q) ⊓ R')  ⊑FD  (P ⊓ (Q ⊓ R')):
    --   inputs are failures⊥/divergences of the right side; we
    --   produce failures⊥/divergences of the left side.
    fwd-F⊥ : ((P ⊓ Q) ⊓ R') ⊑F⊥ (P ⊓ (Q ⊓ R'))
    fwd-F⊥ f-RHS with ⊓-failures⊥-elim f-RHS
    ... | inj₁ f-P  = ⊓-failures⊥-introL (⊓-failures⊥-introL f-P)
    ... | inj₂ f-QR with ⊓-failures⊥-elim f-QR
    ... | inj₁ f-Q  = ⊓-failures⊥-introL (⊓-failures⊥-introR f-Q)
    ... | inj₂ f-R' = ⊓-failures⊥-introR f-R'

    fwd-D : ((P ⊓ Q) ⊓ R') ⊑D (P ⊓ (Q ⊓ R'))
    fwd-D d-RHS with ⊓-divergences-elim d-RHS
    ... | inj₁ d-P  = ⊓-divergences-introL (⊓-divergences-introL d-P)
    ... | inj₂ d-QR with ⊓-divergences-elim d-QR
    ... | inj₁ d-Q  = ⊓-divergences-introL (⊓-divergences-introR d-Q)
    ... | inj₂ d-R' = ⊓-divergences-introR d-R'

    -- The reverse direction is the mirror image: re-bracket via the
    -- sum decompositions in the opposite associativity.
    bwd-F⊥ : (P ⊓ (Q ⊓ R')) ⊑F⊥ ((P ⊓ Q) ⊓ R')
    bwd-F⊥ f-LHS with ⊓-failures⊥-elim f-LHS
    ... | inj₂ f-R' = ⊓-failures⊥-introR (⊓-failures⊥-introR f-R')
    ... | inj₁ f-PQ with ⊓-failures⊥-elim f-PQ
    ... | inj₁ f-P  = ⊓-failures⊥-introL f-P
    ... | inj₂ f-Q  = ⊓-failures⊥-introR (⊓-failures⊥-introL f-Q)

    bwd-D : (P ⊓ (Q ⊓ R')) ⊑D ((P ⊓ Q) ⊓ R')
    bwd-D d-LHS with ⊓-divergences-elim d-LHS
    ... | inj₂ d-R' = ⊓-divergences-introR (⊓-divergences-introR d-R')
    ... | inj₁ d-PQ with ⊓-divergences-elim d-PQ
    ... | inj₁ d-P  = ⊓-divergences-introL d-P
    ... | inj₂ d-Q  = ⊓-divergences-introR (⊓-divergences-introL d-Q)

-----------------------------------------------------------------------------
-- Laws lifted from DRWbisim via `≈⇒≃FD`.
--
-- `_⊓_` commutativity and idempotence already hold under DRWbisim
-- (`⊓-comm` and `⊓-idem` above), so they lift to `_≃FD_` for free via
-- the preservation theorem
--   `≈⇒≃FD : ∀ {P Q} → P ≈ Q → P ≃FD Q`
-- defined in `ITree_Relations.FailuresDivergencesEquiv`.
-----------------------------------------------------------------------------

⊓-comm-FD :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (P Q : ITree E (ExtI I) R)
  → _≃FD_ {ℓB = ℓB} (P ⊓ Q) (Q ⊓ P)
⊓-comm-FD P Q = ≈⇒≃FD (⊓-comm P Q)

⊓-idem-FD :
  ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (P : ITree E (ExtI I) R)
  → _≃FD_ {ℓB = ℓB} (P ⊓ P) P
⊓-idem-FD P = ≈⇒≃FD (⊓-idem P)

------------------------------------------------------------------------
-- Monotonicity of _⊓_ under _⊑F⊥_, _⊑D_, _⊑FD_.
------------------------------------------------------------------------
⊓-mono-⊑F⊥ : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {P P′ Q Q′ : ITree E (ExtI I) R}
             → _⊑F⊥_ {ℓB = ℓB} P P′ → _⊑F⊥_ {ℓB = ℓB} Q Q′
             → _⊑F⊥_ {ℓB = ℓB} (P ⊓ Q) (P′ ⊓ Q′)
⊓-mono-⊑F⊥ P⊑P′ Q⊑Q′ f
  with ⊓-failures⊥-elim f
... | inj₁ fP′ = ⊓-failures⊥-introL (P⊑P′ fP′)
... | inj₂ fQ′ = ⊓-failures⊥-introR (Q⊑Q′ fQ′)

⊓-mono-⊑D : ∀ {ℓi ℓr} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              {P P′ Q Q′ : ITree E (ExtI I) R}
            → P ⊑D P′ → Q ⊑D Q′
            → (P ⊓ Q) ⊑D (P′ ⊓ Q′)
⊓-mono-⊑D P⊑P′ Q⊑Q′ d
  with ⊓-divergences-elim d
... | inj₁ dP′ = ⊓-divergences-introL (P⊑P′ dP′)
... | inj₂ dQ′ = ⊓-divergences-introR (Q⊑Q′ dQ′)

⊓-mono-⊑FD : ∀ {ℓi ℓr ℓB} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {P P′ Q Q′ : ITree E (ExtI I) R}
             → _⊑FD_ {ℓB = ℓB} P P′ → _⊑FD_ {ℓB = ℓB} Q Q′
             → _⊑FD_ {ℓB = ℓB} (P ⊓ Q) (P′ ⊓ Q′)
⊓-mono-⊑FD (pF , pD) (qF , qD) = ⊓-mono-⊑F⊥ pF qF , ⊓-mono-⊑D pD qD

{-# OPTIONS --guardedness #-}

-- FAILURE-SIMULATION congruences for the EXTENSIONAL choice operators: internal
-- choice `⊓`, prefix `⟶₀`, and the one-way refinement `P ⊓ Q ⊑FD P`.
--
-- CONGRUENCES (`FSim → FSim`) plus that ONE strict refinement.  The `⊑FD`-MONOTONICITY
-- laws for these operators are fact-shaped and live in the FD layer
-- (`CSP.Laws.FD.IChoiceMonoFD.⊓-mono-⊑FD`, `CSP.Laws.FD.ChoiceRefine.⟶₀-mono-⊑FD`); see
-- the note above `⊓-refine-⊑FD` below for why the `FSim → ⊑FD` wrappers were retired.
--
-- ORIENTATION: in `FSim R t₁ t₂` the FIRST argument is the IMPLEMENTATION and the
-- SECOND the SPECIFICATION (`fsim→⊑FD : FSim R Q P → P ⊑FD Q`).
--
-- These are DIRECT builds, deliberately NOT routed through
-- `Semantics.DRImpliesFD.drbisim→fsim ∘ CSP.Laws.FD.FDCong.⊓-cong-DR`, which would
-- drag in that module's classical postulate `¬-divergent→normal`.  `⊓` and prefix are
-- the two cheapest possible FSim constructions, so the direct route costs little and
-- keeps the whole `CSP.Laws.FSim` layer postulate-free, matching
-- `Semantics.FailureSim`'s own stated discipline.
--
-- POSTULATES: none, local or inherited.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_)
open import Data.Empty using (⊥; ⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Process_Trees

module CSP.Laws.FSim.IChoiceCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS       {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim {E = E} {I = ExtI E}
open import Semantics.DRBisim   {E = E} {I = ExtI E} using (Diverges)
open import Semantics.Refusals  {E = E} {I = ExtI E} using (Offers)
open import Semantics.Stability {E = E} {I = ExtI E} using (stable-no-τ)
open import Semantics.FailureSim {E = E} {I = ExtI E}
  using (FSim; fsim-refl; fsim→⊑FD)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_⊑FD_)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-τ-inv; ⊓-stepL; ⊓-stepR)
open import CSP.Laws.Bisim.Congruence E-≟ using (pc-just)

-------------------------------------------------------------------------------------
-- INTERNAL CHOICE.  `P ⊓ Q` forces to `react ∅v (br2 P Q)`: it offers no visible
-- event and has exactly two τ-branches, so `fwd`'s `on-ev` cases are all absurd and
-- `stab`'s hypothesis is absurd too (a `⊓` root is never stable).
-------------------------------------------------------------------------------------

-- the forward-simulation half: a τ of the impl choice lands on one operand, matched
-- by the spec choice committing to the corresponding operand
f-sim-⊓ : ∀ {ℓr} {R : Set ℓr} {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
        → FSim R P₁ P₂ → FSim R Q₁ Q₂
        → WSimF (FSim R) (P₁ ⊓ Q₁) (P₂ ⊓ Q₂)

-- a divergence of the impl choice runs through one operand, so it transports through
-- that operand's `div→` after the spec commits to the same side
⊓-fsim-div→ : ∀ {ℓr} {R : Set ℓr} {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
            → FSim R P₁ P₂ → FSim R Q₁ Q₂
            → Diverges (P₁ ⊓ Q₁) → Diverges (P₂ ⊓ Q₂)

-- ⊓ is an FSim congruence (spec operands failure-simulate impl operands)
⊓-fsim : ∀ {ℓr} {R : Set ℓr} {P₁ P₂ Q₁ Q₂ : PTree E (ExtI E) R}
       → FSim R P₁ P₂ → FSim R Q₁ Q₂
       → FSim R (P₁ ⊓ Q₁) (P₂ ⊓ Q₂)

-- `⊓` offers no visible event: both `on-ev` shapes are refuted outright
f-sim-⊓ pp qq .WSimF.on-ev (sRet ())
f-sim-⊓ pp qq .WSimF.on-ev (sVis refl ())
f-sim-⊓ {P₁ = P₁} {P₂ = P₂} {Q₁ = Q₁} {Q₂ = Q₂} pp qq .WSimF.on-tau step
  with ⊓-τ-inv P₁ Q₁ step
... | inj₁ refl = P₂ , wτ (τ*-step (⊓-stepL P₂ Q₂) τ*-refl) , pp
... | inj₂ refl = Q₂ , wτ (τ*-step (⊓-stepR P₂ Q₂) τ*-refl) , qq

⊓-fsim-div→ {P₁ = P₁} {P₂ = P₂} {Q₁ = Q₁} {Q₂ = Q₂} pp qq d
  with ⊓-τ-inv P₁ Q₁ (d .Diverges.step)
... | inj₁ eq = record { step = ⊓-stepL P₂ Q₂
                       ; rest = pp .FSim.div→ (subst Diverges eq (d .Diverges.rest)) }
... | inj₂ eq = record { step = ⊓-stepR P₂ Q₂
                       ; rest = qq .FSim.div→ (subst Diverges eq (d .Diverges.rest)) }

⊓-fsim pp qq .FSim.fwd = f-sim-⊓ pp qq
-- `isStable (P₁ ⊓ Q₁)` is absurd: the left τ-branch always fires
⊓-fsim {P₁ = P₁} {Q₁ = Q₁} pp qq .FSim.stab st =
  ⊥-elim (stable-no-τ st (⊓-stepL P₁ Q₁))
⊓-fsim pp qq .FSim.div→ d = ⊓-fsim-div→ pp qq d

-------------------------------------------------------------------------------------
-- PREFIX.  `e ⟶₀ P` forces to `react (Prefix-cont e P) ∅t`: it IS stable, so `stab`
-- is discharged with `τ*-refl` and an offer reflection, and `div→` is vacuous.
-------------------------------------------------------------------------------------

-- prefix is an FSim congruence
prefix-fsim : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} (e : E A) {P Q : PTree E (ExtI E) R}
            → FSim R P Q → FSim R (e ⟶₀ P) (e ⟶₀ Q)

-- `e ⟶₀ P` is stable: its τ-map is `∅t`, everywhere `nothing`
prefix-stable-f : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} {e : E A} {P : PTree E (ExtI E) R}
                → isStable (e ⟶₀ P)
prefix-stable-f _ _ = refl

-- both sides offer exactly `e` on every carried value, so an offer of the spec
-- prefix reflects to an offer of the impl prefix
prefix-offer-reflect : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} (e : E A)
                       {P Q : PTree E (ExtI E) R} (x : Event√ R)
                     → Offers (e ⟶₀ Q) x → Offers (e ⟶₀ P) x
prefix-offer-reflect e x (_ , sRet ())
prefix-offer-reflect {A = A} e {P} {Q} x (_ , sVis {at = at} {a = y} refl br)
  with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with br
...               | refl = P , sVis {at = A , e} {a = y} refl (pc-just e P y)

-- the forward-simulation half: the only impl step is the prefix event itself
f-sim-prefix : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} (e : E A) {P Q : PTree E (ExtI E) R}
             → FSim R P Q → WSimF (FSim R) (e ⟶₀ P) (e ⟶₀ Q)
f-sim-prefix e sim .WSimF.on-ev (sRet ())
f-sim-prefix {A = A} e {P} {Q} sim .WSimF.on-ev (sVis {at = at} {a = x} refl br)
  with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with br
...               | refl = Q , wev τ*-refl (sVis {at = A , e} {a = x} refl (pc-just e Q x)) τ*-refl , sim
f-sim-prefix e sim .WSimF.on-tau (sSil ())
f-sim-prefix e sim .WSimF.on-tau (sTau refl ())

prefix-fsim e sim .FSim.fwd = f-sim-prefix e sim
-- the spec prefix is already stable, so it settles in zero steps
prefix-fsim e {P} {Q} sim .FSim.stab st =
  (e ⟶₀ Q) , τ*-refl , prefix-stable-f {e = e} {P = Q}
            , λ x off → prefix-offer-reflect e {P = P} {Q = Q} x off
-- a stable state cannot diverge
prefix-fsim e {P} {Q} sim .FSim.div→ d =
  ⊥-elim (stable-no-τ (prefix-stable-f {e = e} {P = P}) (d .Diverges.step))

-------------------------------------------------------------------------------------
-- THE ONE-WAY REFINEMENT `P ⊓ Q ⊑FD P`.  The spec resolves its internal choice by a
-- τ and thereafter IS the impl, so `fsim-refl` closes every residual.  This is the
-- strict-refinement witness the FSim tower smoke test needs for its leaves.
-------------------------------------------------------------------------------------

-- the impl `P` is failure-simulated by the more nondeterministic spec `P ⊓ Q`
⊓-refine-fsim : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) → FSim R P (P ⊓ Q)

-- every impl step is matched by the spec first committing left (one τ) and then
-- performing the very same step
f-sim-⊓-refine : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R)
               → WSimF (FSim R) P (P ⊓ Q)
f-sim-⊓-refine P Q .WSimF.on-ev {t₁′ = P′} step =
  P′ , wev (τ*-step (⊓-stepL P Q) τ*-refl) step τ*-refl , fsim-refl P′
f-sim-⊓-refine P Q .WSimF.on-tau {t₁′ = P′} step =
  P′ , wτ (τ*-step (⊓-stepL P Q) (τ*-step step τ*-refl)) , fsim-refl P′

⊓-refine-fsim P Q .FSim.fwd = f-sim-⊓-refine P Q
-- the spec settles by committing left, landing exactly on the stable impl
⊓-refine-fsim P Q .FSim.stab st =
  P , τ*-step (⊓-stepL P Q) τ*-refl , st , λ _ off → off
-- an impl divergence is a spec divergence prefixed by the left commitment
⊓-refine-fsim P Q .FSim.div→ d = record { step = ⊓-stepL P Q ; rest = d }

-------------------------------------------------------------------------------------
-- `⊑FD` COROLLARY.  ⚠ This CASHES OUT the simulation witness and it is NOT
-- recoverable: `⊑FD → FSim` completeness is out of scope (`Laws_status.md:1104`).
-- Use it for leaf-level statements only.  Inside a composite refinement, keep the
-- `FSim` and compose with `Par-fsim` / `Hide-fsim` / `⦀Fin-fsim` instead.
--
-- ⚠ EXACTLY ONE corollary lives here, and it is NOT a monotonicity law: it is the
-- strict one-way refinement `(P ⊓ Q) ⊑FD P`, which has no `FSim`-free counterpart.
--
-- The two `FSim → ⊑FD` MONOTONICITY wrappers this section used to carry —
-- `⊓-mono-⊑FD` and `prefix-mono-⊑FD` — were RETIRED.  Each was literally
-- `fsim→⊑FD (⊓-fsim …)` / `fsim→⊑FD (prefix-fsim …)`: a name, not power.  Because
-- `⊑FD → FSim` completeness is out of scope, such a wrapper can never consume a `⊑FD`
-- FACT (from a hand-built bisimulation, a denotational argument, or an earlier
-- refinement step), so it cannot appear in a `⊑FD`-only chain.  The FACT-SHAPED
-- (`⊑FD → ⊑FD`) laws that can are:
--
--   * `⊓-mono-⊑FD`  — `CSP.Laws.FD.IChoiceMonoFD` (also carries the three-shape
--                      taxonomy note in its header)
--   * `⟶₀-mono-⊑FD` — `CSP.Laws.FD.ChoiceRefine`
--
-- Both are strictly stronger than the deleted wrappers: feed them
-- `fsim→⊑FD (⊓-fsim …)` / `fsim→⊑FD (prefix-fsim …)` to recover the old uses.  The
-- congruences `⊓-fsim` / `prefix-fsim` remain exported and are what a composite FSim
-- tower should use.  Please do not re-add the wrappers.
-------------------------------------------------------------------------------------

-- internal choice is refined by either branch
⊓-refine-⊑FD : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) → (P ⊓ Q) ⊑FD P
⊓-refine-⊑FD P Q = fsim→⊑FD (⊓-refine-fsim P Q)

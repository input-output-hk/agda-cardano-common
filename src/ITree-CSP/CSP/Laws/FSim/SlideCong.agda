{-# OPTIONS --guardedness #-}

-- FAILURE-SIMULATION congruence for SLIDING CHOICE `_▷_`, in its RIGHT operand only.
--
--   ▷-fsim-R : (P : PTree E (ExtI E) R) → FSim R Q₁ Q₂ → FSim R (P ▷ Q₁) (P ▷ Q₂)
--
-- ORIENTATION: in `FSim R t₁ t₂` the FIRST argument is the IMPLEMENTATION and the SECOND
-- the SPECIFICATION (`fsim→⊑FD : FSim R Q P → P ⊑FD Q`), so this reads: if the spec
-- timeout continuation failure-simulates the impl one, the spec slide failure-simulates
-- the impl slide.  ⚠ NO side condition — in particular NO `NonRet` hypothesis on `P`:
-- the LEFT operand is literally the SAME tree on both sides, so whichever of the two
-- clauses of `force (P ▷ ·)` applies, it applies to both composites simultaneously.
--
-- WHY ONE-SIDED.  The two-sided law
--     ▷-fsim : FSim R P₁ P₂ → FSim R Q₁ Q₂ → FSim R (P₁ ▷ Q₁) (P₂ ▷ Q₂)
-- is FALSE, and this is FORMALISED (not argued in prose) in
--
--     CSP.Laws.FSim.SlideCounterexample.¬▷-fsim
--
-- (`--safe`, zero postulates).  `force (P ▷ Q)` resolves EAGERLY on termination
-- (`… | ret r = ret r`: Roscoe's R3, a terminated left operand DISCARDS the timeout),
-- so the predicate deciding whether the timeout exists at all is `NonRet (force P)` —
-- and that predicate is NOT preserved by `FSim`, which may erase a leading τ and so turn
-- a `sil` node (timeout LIVE) into a `ret` node (timeout ABSENT).  The counterexample is
-- `FSim R (Tau (Ret tt)) (Ret tt)` on the left with `Q₁ = Q₂ = ea ⟶₀ Stop`: a live impl
-- timeout faces an absent spec timeout.  Sharing `P` is exactly the dodge that the
-- trace-level `CSP.Laws.Traces.TraceLawsExtChoiceMono.▷-mono-R` already uses, and this
-- module is its `FSim` transcription.
--
-- The three fields (all of them cheap — `▷` is the least expensive congruence here):
--
--   fwd  : NO case analysis on `force P` is needed.  A visible impl step is inverted by
--          the reused `▷-ev-elim` (which drops the `▷` entirely and lands on the SAME
--          successor, `ret`/√ case included) and re-lifted on the spec side by the reused
--          `▷-ev-L`, so the residual is `fsim-refl`.  A τ impl step is split by the reused
--          `▷-τ-elim` into (a) the TIMEOUT, matched by the spec's own timeout — available
--          because `▷-τ-nonret` recovers `NonRet (force P)` from the impl step itself —
--          and discharged by the operand hypothesis; and (b) a τ OF `P`, matched by
--          `▷-τ-L`, whose residual `P′ ▷ Q₁` vs `P′ ▷ Q₂` carries the SAME `P′` (both
--          sides read the same `viewT (force P)`) and is the corecursive case.
--
--   stab : VACUOUS, and free.  `▷-unstable` (reused, unconditional and total) says a
--          `▷`-node always has its timeout τ, so `isStable (P ▷ Q₁)` is absurd.  No
--          `Offers`-inclusion reasoning whatsoever.
--
--   div→ : the only place a classical ingredient enters, and it is a PRE-EXISTING one.
--          `▷-Diverges→` (`CSP.Laws.FD.ExtChoiceDivergence`, a repo postulate certified
--          from the single `dne` of `CSP.Laws.ClassicalFromLEM`, and `DecEq`-free) decides
--          which operand carries the impl livelock.  A guilty `P` re-lifts by the reused
--          constructive `▷-Diverges-L`; a guilty `Q₁` transfers through the operand's own
--          `FSim.div→` and re-lifts by the new `▷-Diverges-R`, whose `NonRet` side
--          condition is recovered from the impl divergence's FIRST step by `▷-τ-nonret`
--          (the trick `▷-mono-R-aux` uses).  No guarded builder is required: both
--          re-lifters are standalone productive functions.
--
-- POSTULATES: none declared locally.  Exactly ONE is inherited — `▷-Diverges→` — used
-- for `div→` only; `fwd` and `stab` are fully constructive.  No NON_TERMINATING, no
-- sized types, no holes.
--
-- The τ*/weak lifts (`▷-τ*-L`, `▷-wτ-L`, `▷-wev-L`) and `▷-Diverges-R` are stated
-- GENERALLY rather than inlined: the external-choice `□` congruence needs them for the
-- `▷`-slide states that appear when one of its operands terminates.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FSim.SlideCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS        {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim  {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step; τ*-trans; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.DRBisim    {E = E} {I = ExtI E} using (Diverges)
open import Semantics.FailureSim {E = E} {I = ExtI E} using (FSim; fsim-refl; fsim→⊑FD)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_⊑FD_)
open import CSP.Laws.Traces.TraceLaws E-≟ using (▷-τ-L; ▷-ev-L)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (▷-τ-elim; ▷-ev-elim; ▷-τ-nonret; ▷-timeout)
open import CSP.Laws.FD.ExtChoiceFD E-≟ using (▷-unstable; ▷-Diverges-L)
open import CSP.Laws.FD.ExtChoiceDivergence E-≟ using (▷-Diverges→)

-------------------------------------------------------------------------------------
-- τ* AND WEAK LIFTING through the slide's LEFT operand.  These are the `▷` analogues of
-- `DRCongruence`'s `Hide-τ*` / `Hide-wτ` / `Hide-wev-keep`; a later `□` module consumes
-- them for the slide states that arise when one `□` operand terminates.
-------------------------------------------------------------------------------------

-- a silent run of the left operand lifts to a silent run of the slide (map `▷-τ-L`)
▷-τ*-L : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) {P′ : PTree E (ExtI E) R}
       → P ─[τ*]─► P′ → (P ▷ Q) ─[τ*]─► (P′ ▷ Q)
▷-τ*-L P Q τ*-refl           = τ*-refl
▷-τ*-L P Q (τ*-step Pτ rest) = τ*-step (▷-τ-L {Q = Q} Pτ) (▷-τ*-L _ Q rest)

-- a WEAK silent step of the left operand lifts to a weak silent step of the slide
▷-wτ-L : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) {P′ : PTree E (ExtI E) R}
       → P ═[ τ ]═► P′ → (P ▷ Q) ═[ τ ]═► (P′ ▷ Q)
▷-wτ-L P Q (wτ run) = wτ (▷-τ*-L P Q run)

-- a WEAK visible step of the left operand lifts to one of the slide — and DISCARDS the
-- timeout continuation, because `▷-ev-L` resolves the slide (the trailing τ*-run of the
-- weak step therefore already sits OUTSIDE the slide, so `Q` does not occur on the right)
▷-wev-L : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) {P′ : PTree E (ExtI E) R}
          {e : Event√ R}
        → P ═[ ev e ]═► P′ → (P ▷ Q) ═[ ev e ]═► P′
▷-wev-L P Q (wev pre step post) =
  wev (▷-τ*-L P Q pre) (▷-ev-L {Q = Q} step) post

-------------------------------------------------------------------------------------
-- DIVERGENCE INTRODUCTION on the RIGHT.  The dual `▷-Diverges-L` (reused) is
-- unconditional, but this one is NECESSARILY `NonRet`-gated: a terminated left operand
-- makes `P ▷ Q` a `ret` node, which has no τ at all and therefore converges.
-------------------------------------------------------------------------------------

-- a divergence of the timeout continuation is reached by the always-available timeout,
-- provided the left operand has not terminated
▷-Diverges-R : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R)
               {nP : NodeKind E (ExtI E) R}
             → PTree.force P ≡ nP → NonRet nP → Diverges Q → Diverges (P ▷ Q)
▷-Diverges-R P Q eqP ntP d =
  record { step = ▷-timeout P Q eqP ntP ; rest = d }

-------------------------------------------------------------------------------------
-- THE `div→` FIELD.  Split the impl livelock with the certified König step, then
-- re-lift on the guilty side.  Not corecursive: it only dispatches to the two
-- standalone productive re-lifters.
-------------------------------------------------------------------------------------

-- an impl slide divergence transfers to the spec slide (same left operand)
▷-fsim-R-div→ : ∀ {ℓr} {R : Set ℓr} (P : PTree E (ExtI E) R)
                {Q₁ Q₂ : PTree E (ExtI E) R}
              → FSim R Q₁ Q₂ → Diverges (P ▷ Q₁) → Diverges (P ▷ Q₂)
▷-fsim-R-div→ P {Q₁} {Q₂} sim d with ▷-Diverges→ {P = P} {Q = Q₁} d
-- the left operand is guilty: it is shared, so the same divergence re-lifts verbatim
... | inj₁ dP = ▷-Diverges-L {P = P} {Q = Q₂} dP
-- the timeout continuation is guilty: transfer it, and reach it by the spec's timeout,
-- whose `NonRet` witness comes from the impl divergence's own first step
... | inj₂ dQ with ▷-τ-nonret P Q₁ (d .Diverges.step)
...   | nP , eqP , ntP = ▷-Diverges-R P Q₂ eqP ntP (sim .FSim.div→ dQ)

-------------------------------------------------------------------------------------
-- THE CONGRUENCE.  Forward declarations (no old-style mutual block): the corecursive
-- `▷-fsim-R` residual sits under the `WSimF` Σ-result of `f-sim-▷-R`, the discipline
-- `HideCong.f-sim-∖` uses.  Operands are passed as ARGUMENTS to every lift lemma and no
-- composite is ever `with`-forced at a call site, so guardedness is preserved.
-------------------------------------------------------------------------------------

-- HEADLINE: sliding choice is an FSim congruence in its RIGHT operand, with NO side
-- condition (the left operand must be shared — see `SlideCounterexample` above)
▷-fsim-R : ∀ {ℓr} {R : Set ℓr} (P : PTree E (ExtI E) R) {Q₁ Q₂ : PTree E (ExtI E) R}
         → FSim R Q₁ Q₂ → FSim R (P ▷ Q₁) (P ▷ Q₂)

-- the forward-simulation half: invert the impl slide step, re-lift the matching spec step
f-sim-▷-R : ∀ {ℓr} {R : Set ℓr} (P : PTree E (ExtI E) R) {Q₁ Q₂ : PTree E (ExtI E) R}
          → FSim R Q₁ Q₂ → WSimF (FSim R) (P ▷ Q₁) (P ▷ Q₂)
-- a visible impl step is a step of `P` to the SAME successor (√ from a `ret` included),
-- so the spec slide performs literally the same step and the residual is reflexive
f-sim-▷-R P {Q₁} {Q₂} sim .WSimF.on-ev {t₁′ = M} step =
  M , wev τ*-refl (▷-ev-L {Q = Q₂} (▷-ev-elim P Q₁ step)) τ*-refl , fsim-refl M
f-sim-▷-R P {Q₁} {Q₂} sim .WSimF.on-tau {t₁′ = M} step with ▷-τ-elim P Q₁ step
-- the TIMEOUT: the spec times out too (`▷-τ-nonret` re-derives that `P` is live) and the
-- operand hypothesis discharges the residual
... | inj₁ refl with ▷-τ-nonret P Q₁ step
...   | nP , eqP , ntP =
        Q₂ , wτ (τ*-step (▷-timeout P Q₂ eqP ntP) τ*-refl) , sim
-- a τ OF `P`: the spec slides along the very same τ, keeping the SAME `P′` — corecursion
f-sim-▷-R P {Q₁} {Q₂} sim .WSimF.on-tau {t₁′ = M} step | inj₂ (P′ , Pτ , refl) =
  (P′ ▷ Q₂) , wτ (τ*-step (▷-τ-L {Q = Q₂} Pτ) τ*-refl) , ▷-fsim-R P′ sim

▷-fsim-R P sim .FSim.fwd = f-sim-▷-R P sim
-- `isStable (P ▷ Q₁)` is absurd: the `▷`-node always has its timeout τ
▷-fsim-R P {Q₁} {Q₂} sim .FSim.stab st = ⊥-elim (▷-unstable P Q₁ st)
▷-fsim-R P sim .FSim.div→ d = ▷-fsim-R-div→ P sim d

-------------------------------------------------------------------------------------
-- `⊑FD` COROLLARY.  ⚠ This CASHES OUT the simulation witness and it is NOT recoverable
-- (`⊑FD → FSim` completeness is out of scope).  Inside a composite refinement keep the
-- `FSim` and compose with `▷-fsim-R` / `Hide-fsim` / `Par-fsim` instead.
-------------------------------------------------------------------------------------

-- sliding choice is `⊑FD`-monotone in its right operand, from an `FSim` WITNESS premise
-- (not a bare `⊑FD` fact — hence the `-fsim` suffix, per the naming convention in
-- `CSP.Laws.FD.Congruences`'s header)
▷-mono-R-⊑FD-fsim : ∀ {ℓr} {R : Set ℓr} (P : PTree E (ExtI E) R)
               {Q₁ Q₂ : PTree E (ExtI E) R}
             → FSim R Q₂ Q₁ → (P ▷ Q₁) ⊑FD (P ▷ Q₂)
▷-mono-R-⊑FD-fsim P sim = fsim→⊑FD (▷-fsim-R P sim)

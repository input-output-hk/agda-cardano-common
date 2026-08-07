{-# OPTIONS --guardedness #-}

-- ALPHABETISED PARALLEL `_⟦_∥_⟧_` HAS NO UNCONDITIONAL TWO-SIDED `FSim` CONGRUENCE.
--
-- The proposition refuted here is
--
--     αpar-fsim : FSim R P₁ P₂ → FSim R Q₁ Q₂
--               → FSim R (P₁ ⟦ A ∥ B ⟧ Q₁) (P₂ ⟦ A ∥ B ⟧ Q₂)
--
-- (`FSim R impl spec`, matching `fsim→⊑FD : FSim R Q P → P ⊑FD Q`, so `P₁`/`Q₁` are the
-- IMPLEMENTATION operands and `P₂`/`Q₂` the SPECIFICATION ones).  It is FALSE, for ALL
-- alphabets `A`/`B` that make one event solo (the witness below fixes `A = everything`,
-- `B = ∅`), and the witness needs only ONE event and the `⊓`/`div` vocabulary:
--
--     P₁ = P₂ = ea ⟶₀ Stop      (`FSim`-related by `fsim-refl`)
--     Q₁ = div ⊓ div            Q₂ = div        (`FSim`-related: `fsim-divR-div`)
--
-- WHY IT BREAKS — `αpar`'s SIL-HEADED-OPERAND PRIORITY.  `force (αpar P Q)`
-- (CSP.Operators) inspects both heads, and a `sil` on EITHER side pre-empts everything:
--
--     sil P′ | _        = sil (αpar P′ Q)
--     ret _  | sil Q′   = sil (αpar P Q′)
--     react _ _ | sil Q′ = sil (αpar P Q′)
--
-- A `sil`-headed operand therefore MASKS the other operand's visible offers entirely:
-- the composite is a `sil` node, which offers nothing.  Only when both heads are
-- `ret`/`react` does `αpar-pVis` route a visible event.  So the predicate deciding
-- whether the composite can offer anything at all is `NonSil (force ·)` on BOTH
-- operands — and `NonSil (force ·)` is NOT preserved by `FSim`.
--
-- Normally that masking is a mere DELAY (nothing is discarded, unlike `_▷_`'s eager
-- `ret` clause), and both `WSimF`'s weak matching and `FSim.stab`'s τ*-settling absorb
-- finitely many τ's.  The masking becomes PERMANENT exactly when the spec operand's
-- leading `sil` chain is infinite, i.e. when the spec operand is `div`.  And `FSim`
-- does relate a `react`-headed divergence to `div`:  `div ⊓ div` is a `react` node
-- (`react ∅v (br2 div div)`) with no visible offers, no stable descendant and a τ to
-- `div`, so `FSim R (div ⊓ div) div` holds — `fwd.on-ev` is vacuous, `fwd.on-tau` is
-- matched by the empty spec run, `stab` is refuted by the enabled τ, and `div→` is
-- discharged by `Diverges div`.
--
-- Consequently:
--   * IMPL  `(ea ⟶₀ Stop) ⟦ A ∥ B ⟧ (div ⊓ div)` is `react`-headed (both operands are
--     `react`), so `αpar-pVis` routes `ea` as an A-solo event: it CAN perform `ea`.
--   * SPEC  `(ea ⟶₀ Stop) ⟦ A ∥ B ⟧ div` forces to `sil` of ITSELF — the unique
--     τ-successor is the same term — so it can NEVER perform a visible event.
-- `WSimF.on-ev` is then unsatisfiable.  See `¬fsim-αpar` (concrete pair) and
-- `¬αpar-fsim` (the law itself, universally quantified over the alphabets).
--
-- SCOPE OF THE NEGATIVE RESULT.  This refutes the `FSim` CONGRUENCE, not the FD law:
-- both composites diverge immediately here (`impl-div`, `spec-div`), so both are ⊥ in
-- the failures-divergences model and `⊑FD` holds trivially between them.  What fails is
-- `FSim`'s step-wise `fwd` obligation, which — unlike `⊑FD` — is not weakened by a
-- diverging specification.  Since a PERMANENTLY `sil`-headed operand is precisely a
-- divergent one, the fix is a divergence-freedom (reachability-closed `τ-Acc`) side
-- condition on the two SPEC operands; a bare `NoSil` hypothesis (as in
-- `CSP.Laws.AlphaParallelLift`) is not closed under stepping and so cannot be carried
-- coinductively.  Note also that SHARING one operand does NOT help: here `P₁ = P₂`
-- literally, so the one-sided variant `FSim R Q₁ Q₂ → FSim R (P ⟦ A ∥ B ⟧ Q₁)
-- (P ⟦ A ∥ B ⟧ Q₂)` is refuted by the very same witness, and the mirror image (swap the
-- roles of the two operands, put the shared one on the right) refutes the other
-- orientation — `αpar` inspects BOTH heads, so `▷-fsim-R`'s dodge is unavailable.
--
-- ZERO postulates, no NON_TERMINATING, no sized types, no holes.

open import Level using (Lift; lift) renaming (zero to 0ℓ)
open import Data.Unit using (⊤; tt)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module CSP.Laws.FSim.AlphaParCounterexample where
open PTree

-------------------------------------------------------------------------------------
-- A concrete alphabet: ONE event, carrying `⊤` (a visible offer can only ever FIRE
-- when its carried type is inhabited, so `⊥`-carried events would be invisible).
-------------------------------------------------------------------------------------

-- the single event of the counterexample
data Ev : Set → Set where
  ea : Ev ⊤

-- decidable equality on the alphabet, as `CSP.Operators` requires
Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ (_ , ea) (_ , ea) = yes refl

open import CSP.Operators Ev-≟
  using (Stop; Prefix; Prefix₀; _⊓_; _⟦_∥_⟧_; EventSet; chanSet; ∅ES; ∅v)
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
  using ( _─[_]─►_; Label; ev; τ; Event; evLabel; Event√; evl; √
        ; sRet; sSil; sVis; sTau; ev-inv; Diverges)
open import Semantics.WeakBisim {E = Ev} {I = ExtI Ev}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.FailureSim {E = Ev} {I = ExtI Ev} using (FSim; fsim-refl)

-- the return type of the operands; the composite returns `Rt × Rt` (`merge = _,_`)
Rt : Set
Rt = ⊤

-- the single visible label used throughout: the event `ea` carrying its only value
evA : Event√ (Rt × Rt)
evA = evl (evLabel ⊤ ea tt)

-------------------------------------------------------------------------------------
-- The alphabets: everything on the left, nothing on the right, so `ea` is A-SOLO
-- (`αpar-pVis`'s `yes _ | no _` clause: the left operand moves alone and the right
-- operand is carried along unchanged).
-------------------------------------------------------------------------------------

-- the full alphabet (a channel-level set that always decides `yes`)
allES : EventSet
allES = chanSet (λ _ → ⊤) (λ _ → yes tt)

-------------------------------------------------------------------------------------
-- `div` facts.  `force div ≡ sil div`, so `div` is a permanently `sil`-headed process.
-------------------------------------------------------------------------------------

-- `div` diverges: its τ is the `sil`, and its τ-successor is `div` again
div-div : Diverges (div {E = Ev} {I = ExtI Ev} {R = Rt})
div-div .Diverges.next = div
div-div .Diverges.step = sSil refl
div-div .Diverges.rest = div-div

-------------------------------------------------------------------------------------
-- The IMPL right operand: a `react`-headed divergence.  `div ⊓ div` forces to
-- `react ∅v (br2 div div)` — no visible offers, a τ-branch to `div`, never stable.
-------------------------------------------------------------------------------------

-- the `react`-headed divergence (FD-equal to `div`, but NOT `sil`-headed)
divR : PTree Ev (ExtI Ev) Rt
divR = div ⊓ div

-- every τ-move of `divR` lands in `div` (both `br2` branches point there)
divR-τ-inv : {t : PTree Ev (ExtI Ev) Rt} → divR ─[ τ ]─► t → t ≡ div
divR-τ-inv (sSil ())
divR-τ-inv (sTau {i = _ , base _}   refl ())
divR-τ-inv (sTau {i = _ , pair _ _} refl ())
divR-τ-inv (sTau {i = _ , fin} {a = lift fzero}               refl refl) = refl
divR-τ-inv (sTau {i = _ , fin} {a = lift (fsuc fzero)}        refl refl) = refl
divR-τ-inv (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))}     refl ())

-- `divR` is unstable: the `br2` τ-branch at tag `fzero` is enabled
divR-unstable : ¬ isStable divR
divR-unstable st with st (Lift 0ℓ (Fin 2) , fin) (lift fzero)
... | ()

-------------------------------------------------------------------------------------
-- HYPOTHESIS 1 (right operands): the `sil`-headed `div` failure-simulates the
-- `react`-headed `divR`.
-------------------------------------------------------------------------------------

-- forward half: `divR` has NO visible move (it is `react` with the empty offer map
-- `∅v`, so neither `sRet` nor `sVis` can fire), and its only τ goes to `div`, matched
-- by the EMPTY spec run with residual `FSim Rt div div`
f-divR-div : WSimF (FSim Rt) divR div
f-divR-div .WSimF.on-ev  (sRet ())
f-divR-div .WSimF.on-ev  (sVis refl ())
f-divR-div .WSimF.on-tau s with divR-τ-inv s
... | refl = div , wτ τ*-refl , fsim-refl div

-- HYPOTHESIS 1, assembled.  `stab` is vacuous by `divR-unstable`, and `div→` is
-- discharged outright by `div-div`.
fsim-divR-div : FSim Rt divR div
fsim-divR-div .FSim.fwd     = f-divR-div
fsim-divR-div .FSim.stab st = ⊥-elim (divR-unstable st)
fsim-divR-div .FSim.div→ _  = div-div

-------------------------------------------------------------------------------------
-- The shared left operand (HYPOTHESIS 2 is then `fsim-refl`).
-------------------------------------------------------------------------------------

-- offer `ea`, then deadlock — identical on impl and spec side
Pℓ : PTree Ev (ExtI Ev) Rt
Pℓ = ea ⟶₀ Stop

-- HYPOTHESIS 2, assembled: the left operands are the same tree
fsim-Pℓ-Pℓ : FSim Rt Pℓ Pℓ
fsim-Pℓ-Pℓ = fsim-refl Pℓ

-------------------------------------------------------------------------------------
-- The two composites.
-------------------------------------------------------------------------------------

-- IMPL: both operands are `react`-headed, so the composite is a `react` node
impl : PTree Ev (ExtI Ev) (Rt × Rt)
impl = Pℓ ⟦ allES ∥ ∅ES ⟧ divR

-- SPEC: the right operand is `sil`-headed, so the composite is a `sil` node
spec : PTree Ev (ExtI Ev) (Rt × Rt)
spec = Pℓ ⟦ allES ∥ ∅ES ⟧ div

-------------------------------------------------------------------------------------
-- The impl side: `ea` is routed as an A-solo event, `divR` carried along unchanged.
-------------------------------------------------------------------------------------

-- THE VISIBLE MOVE the spec cannot match: `allES .dec` says yes, `∅ES .dec` says no,
-- and `Pℓ`'s offer map yields `Stop`, so `αpar-pVis` offers `ea`
impl-ea : impl ─[ ev evA ]─► (Stop ⟦ allES ∥ ∅ES ⟧ divR)
impl-ea = sVis {at = ⊤ , ea} {a = tt} refl refl

-------------------------------------------------------------------------------------
-- The spec side: a `sil` node whose unique τ-successor is ITSELF.
-------------------------------------------------------------------------------------

-- `force Pℓ` is `react` and `force div` is `sil div`, so the third `force` clause of
-- `αpar` fires and reproduces the very same composite under a `sil`
force-spec : PTree.force spec ≡ sil spec
force-spec = refl

-- hence every τ-move of the spec is a self-loop …
spec-τ-inv : {t : PTree Ev (ExtI Ev) (Rt × Rt)} → spec ─[ τ ]─► t → t ≡ spec
spec-τ-inv (sSil eq)   = sym (sil-injective (trans (sym force-spec) eq))
spec-τ-inv (sTau eq _) with trans (sym eq) force-spec
... | ()

-- … so every τ*-run out of the spec stays at the spec (nothing is ever unmasked)
spec-τ*-inv : {t : PTree Ev (ExtI Ev) (Rt × Rt)} → spec ─[τ*]─► t → t ≡ spec
spec-τ*-inv τ*-refl        = refl
spec-τ*-inv (τ*-step s rest) with spec-τ-inv s
... | refl = spec-τ*-inv rest

-- … and a `sil` node has no visible move at all (neither `sRet` nor `sVis` applies)
spec-noEv : {t : PTree Ev (ExtI Ev) (Rt × Rt)} → spec ─[ ev evA ]─► t → ⊥
spec-noEv step with ev-inv step
... | v , τc , eq , _ with trans (sym eq) force-spec
...   | ()

-------------------------------------------------------------------------------------
-- THE REFUTATION.
-------------------------------------------------------------------------------------

-- HEADLINE: the two hypotheses hold but the conclusion fails for this pair.  The
-- impl's `ea` must be matched by a weak spec run `τ* · ea · τ*`; every spec τ*-run is
-- a self-loop, and the spec is a `sil` node, so the `ea` step is unavailable.
¬fsim-αpar : ¬ (FSim (Rt × Rt) impl spec)
¬fsim-αpar sim with sim .FSim.fwd .WSimF.on-ev impl-ea
... | _ , wev pre step post , _ with spec-τ*-inv pre
...   | refl = spec-noEv step

-- the proposition itself, monomorphised at `Rt` but UNIVERSALLY QUANTIFIED over both
-- alphabets (refuting this instance a fortiori refutes any polymorphic phrasing)
αpar-fsim-claim : Set₁
αpar-fsim-claim = (X Y : EventSet) (A₁ A₂ B₁ B₂ : PTree Ev (ExtI Ev) Rt)
                → FSim Rt A₁ A₂ → FSim Rt B₁ B₂
                → FSim (Rt × Rt) (A₁ ⟦ X ∥ Y ⟧ B₁) (A₂ ⟦ X ∥ Y ⟧ B₂)

-- THE VERDICT: there is no unconditional two-sided `FSim` congruence for `_⟦_∥_⟧_`
¬αpar-fsim : ¬ αpar-fsim-claim
¬αpar-fsim law =
  ¬fsim-αpar (law allES ∅ES Pℓ Pℓ divR div fsim-Pℓ-Pℓ fsim-divR-div)

-- … and, since `A₁ = A₂` above, not even the ONE-SIDED variant that fixes the left
-- operand (the `▷-fsim-R` dodge) survives: `αpar` inspects BOTH heads
αpar-fsim-R-claim : Set₁
αpar-fsim-R-claim = (X Y : EventSet) (P B₁ B₂ : PTree Ev (ExtI Ev) Rt)
                  → FSim Rt B₁ B₂
                  → FSim (Rt × Rt) (P ⟦ X ∥ Y ⟧ B₁) (P ⟦ X ∥ Y ⟧ B₂)

-- the one-sided law is refuted by the very same witness
¬αpar-fsim-R : ¬ αpar-fsim-R-claim
¬αpar-fsim-R law = ¬fsim-αpar (law allES ∅ES Pℓ divR div fsim-divR-div)

-------------------------------------------------------------------------------------
-- NON-VACUITY / SCOPE.  The separation is about a REAL behaviour of the impl (it
-- weakly performs `ea`), and BOTH composites diverge — so the FD-level law is NOT
-- refuted, only the step-wise `FSim` congruence.
-------------------------------------------------------------------------------------

-- the impl really performs `ea` (no padding τ's needed)
impl-weak-ea : impl ═[ ev evA ]═► (Stop ⟦ allES ∥ ∅ES ⟧ divR)
impl-weak-ea = wev τ*-refl impl-ea τ*-refl

-- the spec diverges: its `sil` self-loop is an infinite τ-run
spec-div : Diverges spec
spec-div .Diverges.next = spec
spec-div .Diverges.step = sSil force-spec
spec-div .Diverges.rest = spec-div

-- the impl diverges too — its `divR` τ-branch leads straight into the spec composite,
-- so both sides are ⊥ in the failures-divergences model
impl-div : Diverges impl
impl-div .Diverges.next = spec
impl-div .Diverges.step =
  sTau {i = (Lift 0ℓ (Fin 2) × Lift 0ℓ (Fin 2)) , pair fin fin}
       {a = lift (fsuc fzero) , lift fzero} refl refl
impl-div .Diverges.rest = spec-div

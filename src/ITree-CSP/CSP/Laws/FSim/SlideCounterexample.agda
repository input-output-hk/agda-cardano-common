{-# OPTIONS --guardedness #-}

-- SLIDING CHOICE `_▷_` HAS NO UNCONDITIONAL TWO-SIDED `FSim` CONGRUENCE.
--
-- The proposition refuted here is
--
--     ▷-fsim : FSim R P₁ P₂ → FSim R Q₁ Q₂ → FSim R (P₁ ▷ Q₁) (P₂ ▷ Q₂)
--
-- (`FSim R impl spec`, matching `fsim→⊑FD : FSim R Q P → P ⊑FD Q`, so `P₁`/`Q₁` are the
-- IMPLEMENTATION operands and `P₂`/`Q₂` the SPECIFICATION ones).  It is FALSE, and the
-- witness is as small as it can be:
--
--     P₁ = Tau (Ret tt)      P₂ = Ret tt            (`FSim`-related: `fsim-P₁-P₂`)
--     Q₁ = Q₂ = ea ⟶₀ Stop                          (`FSim`-related: `fsim-refl`)
--
-- WHY IT BREAKS — the eager `ret` clause of `_▷_`.  `force (P ▷ Q)` (CSP.Operators)
-- inspects `force P` and resolves IMMEDIATELY on termination (`… | ret r = ret r`,
-- Roscoe's R3: a terminating left operand DISCARDS the timeout).  Every other node
-- shape yields `react (viewV nP) (▷-slide nP Q)`, whose τ-branch at tag `fzero` is the
-- ALWAYS-available timeout `just Q`.  So the predicate that decides which of the two
-- happens is `NonRet (force P)` — and `NonRet (force ·)` is NOT preserved by `FSim`:
-- an `FSim` may erase a leading τ, turning a `sil` node (non-ret, timeout LIVE) into a
-- `ret` node (timeout ABSENT).  Here `P₁` is `sil`, so `P₁ ▷ Q₁` can time out to `Q₁`
-- and then offer `ea`; `P₂` is `ret`, so `P₂ ▷ Q₂` forces to `ret tt`, has no τ at all,
-- and its ONLY transition is `√ tt`.  `WSimF.on-tau` therefore has to match the impl's
-- timeout by a τ*-run of a `ret` node, i.e. by the empty run, leaving the obligation
-- `FSim Rt Q₁ (P₂ ▷ Q₂)` — refuted, because the impl offers `ea` and the spec offers
-- nothing but `√`.  See `¬fsim-slide` (concrete pair) and `¬▷-fsim` (the law itself).
--
-- This is a fact about THIS encoding of `▷`, not about CSP's `▷`: it says a `ret` node
-- is not τ-insensitive under `▷`, i.e. `_▷_` is not compatible with the τ-abstraction
-- that `FSim` performs on its LEFT operand.  The RIGHT operand is untouched by the
-- argument — the same `P` on both sides keeps `NonRet` in step — which is exactly the
-- dodge that `CSP.Laws.Traces.TraceLawsExtChoiceMono.▷-mono-R` uses at trace level.
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

module CSP.Laws.FSim.SlideCounterexample where
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

open import CSP.Operators Ev-≟ using (Stop; Prefix; Prefix₀; Ret; Tau; _▷_; ▷-slide; ∅v)
open import Semantics.LTS {E = Ev} {I = ExtI Ev}
  using ( _─[_]─►_; Label; ev; τ; Event; evLabel; Event√; evl; √
        ; sRet; sSil; sVis; sTau; ev-inv; Diverges)
open import Semantics.WeakBisim {E = Ev} {I = ExtI Ev}
  using (_─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wτ; wev; WSimF)
open import Semantics.FailureSim {E = Ev} {I = ExtI Ev} using (FSim; fsim-refl)

-- the (irrelevant) return type; `tt` is the value both `Ret`s return
Rt : Set
Rt = ⊤

-- the single visible label used throughout: the event `ea` carrying its only value
evA : Event√ Rt
evA = evl (evLabel ⊤ ea tt)

-------------------------------------------------------------------------------------
-- A generic inversion, reused throughout: a `ret` node has no τ-move.
-------------------------------------------------------------------------------------

-- nothing silent can leave a terminated state (neither `sSil` nor `sTau` can fire)
ret-noτ : {t M : PTree Ev (ExtI Ev) Rt} {r : Rt}
        → PTree.force t ≡ ret r → t ─[ τ ]─► M → ⊥
ret-noτ eqf (sSil sileq)  with trans (sym sileq) eqf
... | ()
ret-noτ eqf (sTau eqc _)  with trans (sym eqc) eqf
... | ()

-------------------------------------------------------------------------------------
-- The four operands.
-------------------------------------------------------------------------------------

-- IMPL left operand: one silent step, then terminate (`force` is `sil`, i.e. NonRet)
P₁ : PTree Ev (ExtI Ev) Rt
P₁ = Tau (Ret tt)

-- SPEC left operand: terminate immediately (`force` is `ret`, i.e. NOT NonRet)
P₂ : PTree Ev (ExtI Ev) Rt
P₂ = Ret tt

-- BOTH right operands: offer `ea`, then deadlock (identical on impl and spec side)
Q₁ Q₂ : PTree Ev (ExtI Ev) Rt
Q₁ = ea ⟶₀ Stop
Q₂ = ea ⟶₀ Stop

-------------------------------------------------------------------------------------
-- HYPOTHESIS 1: the spec `Ret tt` failure-simulates the impl `Tau (Ret tt)`.
-------------------------------------------------------------------------------------

-- the impl's τ-successor is a terminated state (its only τ is the `sil` itself)
P₁-τ-inv : {t : PTree Ev (ExtI Ev) Rt} → P₁ ─[ τ ]─► t → PTree.force t ≡ ret tt
P₁-τ-inv (sSil refl) = refl
P₁-τ-inv (sTau () _)

-- the impl cannot diverge: its single τ lands in `Ret tt`, which has no τ at all
¬div-P₁ : ¬ Diverges P₁
¬div-P₁ d =
  ret-noτ (P₁-τ-inv (d .Diverges.step)) (d .Diverges.rest .Diverges.step)

-- forward half: the impl's only move is the leading τ, matched by the EMPTY spec
-- τ*-run (`wτ τ*-refl`) with residual `Ret tt` on both sides; visible moves are
-- vacuous because a `sil` node is neither `ret` (for `sRet`) nor `react` (for `sVis`)
f-P₁-P₂ : WSimF (FSim Rt) P₁ P₂
f-P₁-P₂ .WSimF.on-ev  (sRet ())
f-P₁-P₂ .WSimF.on-ev  (sVis () _)
f-P₁-P₂ .WSimF.on-tau (sSil refl) = P₂ , wτ τ*-refl , fsim-refl P₂
f-P₁-P₂ .WSimF.on-tau (sTau () _)

-- HYPOTHESIS 1, assembled.  `stab` is vacuous (`isStable` of a `sil` node unfolds to
-- `Lift ⊥`) and `div→` is vacuous by `¬div-P₁`.
fsim-P₁-P₂ : FSim Rt P₁ P₂
fsim-P₁-P₂ .FSim.fwd            = f-P₁-P₂
fsim-P₁-P₂ .FSim.stab (lift ())
fsim-P₁-P₂ .FSim.div→ d         = ⊥-elim (¬div-P₁ d)

-------------------------------------------------------------------------------------
-- HYPOTHESIS 2: the right operands are identical, so reflexivity suffices.
-------------------------------------------------------------------------------------

-- HYPOTHESIS 2, assembled
fsim-Q₁-Q₂ : FSim Rt Q₁ Q₂
fsim-Q₁-Q₂ = fsim-refl Q₁

-------------------------------------------------------------------------------------
-- The impl side: `P₁ ▷ Q₁` is a `react` node whose τ-branch `fzero` is the timeout.
-------------------------------------------------------------------------------------

-- `force P₁` is `sil`, so the slide does NOT resolve: no visible offers (`viewV` of a
-- `sil` node is `∅v`) and the full `▷-slide` τ-map
force-slide₁ : PTree.force (P₁ ▷ Q₁) ≡ react ∅v (▷-slide (sil (Ret tt)) Q₁)
force-slide₁ = refl

-- THE LIVE TIMEOUT: the impl can silently abandon `P₁` in favour of `Q₁`.  The τ-index
-- is `pair fin fin` (an inhabited index — `▷-slide`'s timeout clause needs the `fzero`
-- tag together with SOME value of the paired index), cf. `▷-timeout` in
-- `CSP.Laws.Traces.TraceLawsExtChoiceMono`.
slide-timeout : (P₁ ▷ Q₁) ─[ τ ]─► Q₁
slide-timeout = sTau {i = (Lift 0ℓ (Fin 2) × Lift 0ℓ (Fin 1)) , pair fin fin}
                     {a = lift fzero , lift fzero} refl refl

-- …and `Q₁` then offers `ea`
Q₁-ea : Q₁ ─[ ev evA ]─► Stop
Q₁-ea = sVis {at = ⊤ , ea} {a = tt} refl refl

-------------------------------------------------------------------------------------
-- The spec side: `P₂ ▷ Q₂` is a bare `ret` node — no τ, no visible offer but `√`.
-------------------------------------------------------------------------------------

-- the eager `ret` clause of `_▷_` fires, discarding `Q₂` entirely
force-slide₂ : PTree.force (P₂ ▷ Q₂) ≡ ret tt
force-slide₂ = refl

-- hence the spec has no τ-move whatsoever …
slide₂-noτ : {t : PTree Ev (ExtI Ev) Rt} → (P₂ ▷ Q₂) ─[ τ ]─► t → ⊥
slide₂-noτ = ret-noτ force-slide₂

-- … so every τ*-run out of the spec is the empty one (nothing to match a timeout with)
slide₂-τ*-inv : {t : PTree Ev (ExtI Ev) Rt} → (P₂ ▷ Q₂) ─[τ*]─► t → t ≡ (P₂ ▷ Q₂)
slide₂-τ*-inv τ*-refl       = refl
slide₂-τ*-inv (τ*-step s _) = ⊥-elim (slide₂-noτ s)

-- … and the spec cannot perform `ea` either: a `ret` node has an empty offer map
slide₂-noEvA : {t : PTree Ev (ExtI Ev) Rt} → (P₂ ▷ Q₂) ─[ ev evA ]─► t → ⊥
slide₂-noEvA step with ev-inv step
... | v , τc , () , _

-------------------------------------------------------------------------------------
-- THE REFUTATION.
-------------------------------------------------------------------------------------

-- KEY LEMMA: the residual obligation left by the timeout is unsatisfiable — the impl
-- residual `Q₁` offers `ea`, and any weak `ea`-match by the spec would have to fire a
-- visible `ea` from the (τ-free, offer-free) `ret` node `P₂ ▷ Q₂`
¬fsim-Q₁-slide₂ : ¬ (FSim Rt Q₁ (P₂ ▷ Q₂))
¬fsim-Q₁-slide₂ sim with sim .FSim.fwd .WSimF.on-ev Q₁-ea
... | _ , wev pre step post , _ with slide₂-τ*-inv pre
...   | refl = slide₂-noEvA step

-- HEADLINE: the two hypotheses hold but the conclusion fails for this pair.  The
-- impl's timeout must be matched by a weak spec τ-run; the spec is a `ret` node, so
-- the only such run is empty and the residual pair is refuted by `¬fsim-Q₁-slide₂`.
¬fsim-slide : ¬ (FSim Rt (P₁ ▷ Q₁) (P₂ ▷ Q₂))
¬fsim-slide sim with sim .FSim.fwd .WSimF.on-tau slide-timeout
... | _ , wτ run , sim′ with slide₂-τ*-inv run
...   | refl = ¬fsim-Q₁-slide₂ sim′

-- the proposition itself, monomorphised at `Rt` (refuting this instance a fortiori
-- refutes any universe-polymorphic phrasing of the same law)
▷-fsim-claim : Set₁
▷-fsim-claim = (A₁ A₂ B₁ B₂ : PTree Ev (ExtI Ev) Rt)
             → FSim Rt A₁ A₂ → FSim Rt B₁ B₂ → FSim Rt (A₁ ▷ B₁) (A₂ ▷ B₂)

-- THE VERDICT: there is no unconditional two-sided `FSim` congruence for `_▷_`
¬▷-fsim : ¬ ▷-fsim-claim
¬▷-fsim law = ¬fsim-slide (law P₁ P₂ Q₁ Q₂ fsim-P₁-P₂ fsim-Q₁-Q₂)

-------------------------------------------------------------------------------------
-- NON-VACUITY: the impl really does reach `Stop` by `τ · ea`, so the separation is
-- about a REAL behaviour of `P₁ ▷ Q₁` that `P₂ ▷ Q₂` lacks — not an artefact of a
-- degenerate process.  (`P₂ ▷ Q₂`'s only transition is `√ tt`, exhibited below.)
-------------------------------------------------------------------------------------

-- the impl weakly performs `ea` (time out, then fire the prefix)
slide₁-weak-ea : (P₁ ▷ Q₁) ═[ ev evA ]═► Stop
slide₁-weak-ea = wev (τ*-step slide-timeout τ*-refl) Q₁-ea τ*-refl

-- the spec's sole move: immediate successful termination
slide₂-√ : (P₂ ▷ Q₂) ─[ ev (√ tt) ]─► deadlock
slide₂-√ = sRet force-slide₂

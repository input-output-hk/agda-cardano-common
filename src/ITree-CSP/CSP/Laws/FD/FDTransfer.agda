{-# OPTIONS --guardedness #-}

-- The classical refinement-transfer toolkit for the FD layer.
--
-- Central export is `FD→trace⊥`: a divergence-strict refinement `P ⊑FD Q` lets a
-- bare Q-run be transported to either a P-run on the SAME trace or a P-divergence.
-- This is the bridge the parallel FD-monotonicity law (Par-mono-⊑FD) relies on.
--
-- The ONLY new postulate here is `Diverges-LEM` (a plain LEM instance, like
-- `offer-LEM`); it is certified derivable from `dne` as Derivation 10 in
-- CSP.Laws.ClassicalFromLEM.  The two "local copies" (`⟹-then-τ*`, `term→√failure`)
-- are verbatim from CSP.Laws.FD.IterateMonoFD, kept here to avoid importing that heavy
-- module (mirrors the ParallelFailures "local copy" precedent).

open import Level using (Level; _⊔_; Lift; lift; lower) renaming (suc to lsuc)
open import Data.List using (List; []; _∷_; _++_)
open import Data.List.Properties using (++-identityʳ; ++-conicalˡ; ++-conicalʳ; ∷-injective)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Nullary using (¬_; Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)

open import Process_Trees

module CSP.Laws.FD.FDTransfer {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open PTree
open import CSP.Operators E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.WeakBisim           {E = E} {I = ExtI E}
  using (_─[τ*]─►_; τ*-refl; τ*-step)
open import Semantics.Failures            {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; failures)
open import Semantics.Refusals            {E = E} {I = ExtI E}
  using (Refuses; Offers; deadlock-refuses; deadlock-no-offer)
open import Semantics.DRBisim             {E = E} {I = ExtI E}
  using (Diverges; deadlock-no-τ; deadlock-converges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_⊇F⊥_; _⊇D_; failures⊥; divergences; IsDivergence)
open import Semantics.DRImpliesFD         {E = E} {I = ExtI E}
  using (¬-divergent→normal)
open IsDivergence

-------------------------------------------------------------------------------------
-- Item 1: the one new postulate — a plain LEM instance (mirrors `offer-LEM`),
-- certified from `dne` as Derivation 10 in CSP.Laws.ClassicalFromLEM.
-------------------------------------------------------------------------------------

postulate
  -- divergence of a state is classically decidable
  Diverges-LEM : ∀ {ℓr} {R : Set ℓr} (t : PTree E (ExtI E) R)
               → Diverges t ⊎ ¬ Diverges t

-------------------------------------------------------------------------------------
-- Item 2: split a visible run along a trace concatenation `s₁ ++ s₂`.
-------------------------------------------------------------------------------------

-- a run over `s₁ ++ s₂` factors through an intermediate state after the `s₁` prefix
⟹-split : ∀ {ℓr} {R : Set ℓr} {p q : PTree E (ExtI E) R}
          (s₁ : List (Event√ R)) {s₂ : List (Event√ R)}
        → p ⟹⟨ s₁ ++ s₂ ⟩ q
        → Σ[ m ∈ PTree E (ExtI E) R ] ((p ⟹⟨ s₁ ⟩ m) × (m ⟹⟨ s₂ ⟩ q))
⟹-split []        run                = _ , ⟹-refl , run
⟹-split (x ∷ s₁) (⟹-τ step rest) with ⟹-split (x ∷ s₁) rest
... | m , r1 , r2 = m , ⟹-τ step r1 , r2
⟹-split (x ∷ s₁) (⟹-ev step rest) with ⟹-split s₁ rest
... | m , r1 , r2 = m , ⟹-ev step r1 , r2

-------------------------------------------------------------------------------------
-- Item 3: local copies from CSP.Laws.FD.IterateMonoFD (verbatim; avoids importing it).
-------------------------------------------------------------------------------------

-- compose a visible big-step run with a trailing silent τ*-run (trace unchanged).
-- (local copy of IterateMonoFD's `⟹-then-τ*`)
⟹-then-τ* : ∀ {ℓr} {R : Set ℓr} {P Q Q′ : PTree E (ExtI E) R} {s}
           → P ⟹⟨ s ⟩ Q → Q ─[τ*]─► Q′ → P ⟹⟨ s ⟩ Q′
⟹-then-τ* ⟹-refl            τ*-refl           = ⟹-refl
⟹-then-τ* ⟹-refl            (τ*-step st rest) = ⟹-τ st (⟹-then-τ* ⟹-refl rest)
⟹-then-τ* (⟹-τ step run)    tt*               = ⟹-τ step (⟹-then-τ* run tt*)
⟹-then-τ* (⟹-ev step run)   tt*               = ⟹-ev step (⟹-then-τ* run tt*)

-- a terminating run (`P` reaches `ret x` on `s₁`) gives a √-extended FAILURE for ANY
-- ban set `B`: append the `√ x` tick to `deadlock`, which refuses everything.
-- (local copy of IterateMonoFD's `term→√failure`)
term→√failure : ∀ {ℓr} {R : Set ℓr} {P Pᵣ : PTree E (ExtI E) R} {x : R}
   {s₁ : List (Event√ R)} {B : Event√ R → Set ℓr}
   → P ⟹⟨ s₁ ⟩ Pᵣ → force Pᵣ ≡ ret x → failures P (s₁ ++ √ x ∷ []) B
term→√failure {x = x} ⟹-refl          fe =
  deadlock , ⟹-ev (sRet fe) ⟹-refl , deadlock-refuses
term→√failure {x = x} (⟹-τ step rest)  fe with term→√failure rest fe
... | (T , run , ref) = T , ⟹-τ step run , ref
term→√failure {x = x} (⟹-ev step rest) fe with term→√failure rest fe
... | (T , run , ref) = T , ⟹-ev step run , ref

-------------------------------------------------------------------------------------
-- Local list / deadlock helpers used by the √-truncation machinery.
-------------------------------------------------------------------------------------

-- a snoc list is never empty
snoc≢[] : ∀ {ℓa} {A : Set ℓa} (xs : List A) {y : A} → ¬ (xs ++ y ∷ [] ≡ [])
snoc≢[] []       ()
snoc≢[] (x ∷ xs) ()

-- deadlock performs no step, so any run out of it is `⟹-refl` (empty trace, same state)
deadlock-run-inv : ∀ {ℓr} {R : Set ℓr} {s : List (Event√ R)} {T : PTree E (ExtI E) R}
                 → deadlock ⟹⟨ s ⟩ T → (s ≡ []) × (T ≡ deadlock)
deadlock-run-inv ⟹-refl        = refl , refl
deadlock-run-inv (⟹-τ step _)  = ⊥-elim (deadlock-no-τ step)
deadlock-run-inv (⟹-ev step _) = ⊥-elim (deadlock-no-offer step)

-------------------------------------------------------------------------------------
-- Item 4: split a √-terminated run at a GENERAL trace `s` (no `map evl` needed).
-------------------------------------------------------------------------------------

-- `P ⟹⟨ s ++ √ x ∷ [] ⟩ T` means `P` visibly reaches a `ret x` state on `s`.  A
-- mid-trace `√` step would land in `deadlock`, whose non-empty remainder is absurd.
√-run-split-gen : ∀ {ℓr} {R : Set ℓr} {P T : PTree E (ExtI E) R} {x : R}
   (s : List (Event√ R))
   → P ⟹⟨ s ++ √ x ∷ [] ⟩ T
   → Σ[ Pᵣ ∈ PTree E (ExtI E) R ] ((P ⟹⟨ s ⟩ Pᵣ) × force Pᵣ ≡ ret x)
-- empty s: trace is `√ x ∷ []`; a τ keeps it, the `√` tick fires from `ret x`.
√-run-split-gen []        (⟹-τ step rest) with √-run-split-gen [] rest
... | Pᵣ , run , fe = Pᵣ , ⟹-τ step run , fe
√-run-split-gen []        (⟹-ev (sRet fe) rest) = _ , ⟹-refl , fe
-- non-empty s: a τ keeps it; a visible (sVis) event peels it; a mid `√` (sRet) is absurd.
√-run-split-gen (e ∷ es) (⟹-τ step rest) with √-run-split-gen (e ∷ es) rest
... | Pᵣ , run , fe = Pᵣ , ⟹-τ step run , fe
√-run-split-gen (e ∷ es) (⟹-ev (sVis eqf br) rest) with √-run-split-gen es rest
... | Pᵣ , run , fe = Pᵣ , ⟹-ev (sVis eqf br) run , fe
√-run-split-gen (e ∷ es) (⟹-ev (sRet fe) rest) =
  ⊥-elim (snoc≢[] es (proj₁ (deadlock-run-inv rest)))

-------------------------------------------------------------------------------------
-- Item 5: plain list surgery — split `s ++ x ∷ []` against a concatenation `p ++ q`.
-------------------------------------------------------------------------------------

-- either the trailing `x` lands inside `q` (so `q = q′ ++ x ∷ []`) or `q` is empty
-- and the whole `s ++ x ∷ []` is `p`.
snoc-split : ∀ {ℓx} {X : Set ℓx} (p : List X) {q s : List X} {x : X}
   → s ++ x ∷ [] ≡ p ++ q
   → (Σ[ q′ ∈ List X ] ((q ≡ q′ ++ x ∷ []) × (s ≡ p ++ q′))) ⊎ ((q ≡ []) × (p ≡ s ++ x ∷ []))
snoc-split []        {q} {s}      eq = inj₁ (s , sym eq , refl)
snoc-split (a ∷ p') {q} {[]} {x} eq with ∷-injective eq
... | refl , rest = inj₂ ( ++-conicalʳ p' q (sym rest)
                          , cong (a ∷_) (++-conicalˡ p' q (sym rest)) )
snoc-split (a ∷ p') {q} {b ∷ s'} eq with ∷-injective eq
... | refl , tl with snoc-split p' {q} {s'} tl
...   | inj₁ (q′ , qeq , seq) = inj₁ (q′ , qeq , cong (a ∷_) seq)
...   | inj₂ (qeq , peq)      = inj₂ (qeq , cong (a ∷_) peq)

-------------------------------------------------------------------------------------
-- Divergence half: a run passing a `√` tick lands in deadlock, which cannot diverge.
-------------------------------------------------------------------------------------

-- a `Diverges`-reaching run cannot cross a `√` tick (it would strand at deadlock).
no-div-through-√ : ∀ {ℓr} {R : Set ℓr} {P W : PTree E (ExtI E) R} {r : R}
   (s′ rest : List (Event√ R))
   → P ⟹⟨ s′ ++ √ r ∷ rest ⟩ W → Diverges W → ⊥
no-div-through-√ []        rest (⟹-τ step run)      dv = no-div-through-√ [] rest run dv
no-div-through-√ []        rest (⟹-ev (sRet _) run) dv with deadlock-run-inv run
... | refl , refl = deadlock-converges dv
no-div-through-√ (e ∷ es) rest (⟹-τ step run) dv = no-div-through-√ (e ∷ es) rest run dv
no-div-through-√ (e ∷ es) rest (⟹-ev step run) dv = no-div-through-√ es rest run dv

-------------------------------------------------------------------------------------
-- Item 6: truncate a √-terminated divergence back to its `√`-free prefix trace.
-------------------------------------------------------------------------------------

-- `divergences P (s ++ √ r ∷ [])` implies `divergences P s`: the `√` cannot sit in the
-- divergence prefix (that would strand the witness at deadlock), so it lives in the
-- suffix and shortening the suffix rebuilds the divergence on `s`.
div-√-truncate : ∀ {ℓr} {R : Set ℓr} {P : PTree E (ExtI E) R} {r : R}
   {s : List (Event√ R)}
   → divergences P (s ++ √ r ∷ []) → divergences P s
div-√-truncate {P = P} {r = r} {s = s} d
  with snoc-split (d .prefix) {d .suffix} {s} {√ r} (d .split)
-- √ lives in the suffix: keep the prefix reach, shorten the suffix to `q′`.
... | inj₁ (q′ , _ , seq) = record
        { prefix  = d .prefix
        ; suffix  = q′
        ; split   = seq
        ; witness = d .witness
        ; reach   = d .reach
        ; divwit  = d .divwit
        }
-- √ ends the prefix: the reach crosses the tick, stranding the witness — absurd.
... | inj₂ (_ , peq) =
        ⊥-elim (no-div-through-√ s []
                  (subst (λ z → P ⟹⟨ z ⟩ (d .witness)) peq (d .reach))
                  (d .divwit))

-------------------------------------------------------------------------------------
-- Item 7: THE BRIDGE — ⊑FD transports a bare Q-run to a P-run (same trace) or a
-- P-divergence.  Classical via `Diverges-LEM` + `¬-divergent→normal`.
-------------------------------------------------------------------------------------

-- ⊑FD gives traces⊥-containment: a Q-run maps to a P-run on the same trace or a P-divergence.
FD→trace⊥ : ∀ {ℓr} {R : Set ℓr} {P Q Q* : PTree E (ExtI E) R} {s : List (Event√ R)}
          → P ⊇F⊥ Q → P ⊇D Q → Q ⟹⟨ s ⟩ Q*
          → (Σ[ P* ∈ PTree E (ExtI E) R ] (P ⟹⟨ s ⟩ P*)) ⊎ divergences P s
FD→trace⊥ {ℓr = ℓr} {R = R} {P} {Q} {Q*} {s} fF fD run with Diverges-LEM Q*
-- Q* diverges: `s` is a Q-divergence (prefix `s`, empty suffix); transfer via ⊇D.
... | inj₁ dvg =
      inj₂ (fD (record { prefix  = s ; suffix = []
                       ; split   = sym (++-identityʳ s)
                       ; witness = Q* ; reach = run ; divwit = dvg }))
-- Q* converges: reach a τ-normal-form Q′ (stable or a ret) and feed ⊇F⊥ a witness.
... | inj₂ ndvg with ¬-divergent→normal ndvg
-- stable Q′: an empty ban failure on `s` transfers to a P-failure (P-run) or P-divergence.
...   | Q′ , τ*run , inj₁ st
        with fF {s} {λ _ → Lift ℓr ⊥}
               (inj₁ (Q′ , ⟹-then-τ* run τ*run , (st , λ e b → ⊥-elim (lower b))))
...       | inj₁ (P* , P-run , _) = inj₁ (P* , P-run)
...       | inj₂ dv               = inj₂ dv
-- ret Q′: a √-extended empty-ban failure on `s ++ √ r ∷ []` transfers, then split/truncate.
FD→trace⊥ {ℓr = ℓr} {R = R} {P} {Q} {Q*} {s} fF fD run | inj₂ ndvg
  | Q′ , τ*run , inj₂ (r , eqret)
    with fF {s ++ √ r ∷ []} {λ _ → Lift ℓr ⊥}
           (inj₁ (term→√failure (⟹-then-τ* run τ*run) eqret))
... | inj₁ (P* , P-run√ , _) with √-run-split-gen s P-run√
...   | Pᵣ , P-run , _ = inj₁ (Pᵣ , P-run)
FD→trace⊥ {ℓr = ℓr} {R = R} {P} {Q} {Q*} {s} fF fD run | inj₂ ndvg
  | Q′ , τ*run , inj₂ (r , eqret) | inj₂ dv√ = inj₂ (div-√-truncate dv√)

{-# OPTIONS --guardedness #-}

-- UCS chapter 7 §7.1: semantics of termination (section7-1.csp, A.W. Roscoe).
--   TE = (up -> STOP) [] SKIP
--   assert TE [FD= TE;SKIP   and   TE;SKIP [FD= TE      -- ⇒ TE ≈FD TE;SKIP
-- Roscoe: these are equal under TICK-AS-SIGNAL (FDR) but NOT under Hoare's
-- TICK-AS-REFUSABLE.  In THIS model √ under □ is realised as an UNSTABLE τ-slide
-- (the `□-slide-PR` tag0 branch to SKIP): the √-offering node has an enabled τ, so
-- √ is never in a stable refusal ⇒ the model is tick-as-signal ⇒ TE ≈FD TE;SKIP.
--
-- Concretely `force TE` hits the `□` clause `react vP τcP | ret r`, i.e.
--   force TE = react vP (□-slide-PR (react vP ∅t) Skip),
-- so TE's root OFFERS `up` visibly (via vP = Prefix-cont up …) AND has an enabled τ
-- (the tag0 slide to SKIP) — an unstable node, hence √ non-refusable.
--
-- The equivalence TE ≈FD TE;SKIP is exactly the certified RIGHT-UNIT law of
-- sequential composition, `;-unit-r` (T6.5 / U7.1): `P ; SKIP ∼ P`, instantiated at
-- P := TE.  That law is a strong bisimulation whose step-matching is precisely the
-- tick-as-signal correspondence flagged in the Background:
--   * the `up`-branch relates  STOP  ↔  STOP ; SKIP   (both force to `react ∅v ∅t`);
--   * the √-slide relates       SKIP  ↔  SKIP >>= _    (both force to `ret tt`).
-- We reuse the proven law (Semantics: ∼ ⇒ ≈DR ⇒ ≈FD) rather than re-deriving the
-- coinductive bind bisimulation by hand.

module CSP.Examples.UCS.Ch7.Termination where

open import Level using (0ℓ) renaming (zero to lzero)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees
open PTree

data TEv : Set → Set where
  up : TEv ⊤            -- nullary channel `up` (Roscoe: `channel up, down`; only `up` used by TE)

TEv-≟ : (x y : AnyTypes TEv) → Dec (x ≡ y)
TEv-≟ (_ , up) (_ , up) = yes refl

open import CSP.Operators TEv-≟

instance
  DecEq-⊤ : ∀ {ℓr} → DecEq (⊤ {ℓr})
  DecEq-⊤ = record { _≟_ = λ _ _ → yes refl }   -- cf. Laws/FD/SlideZero.agda:96

open import Semantics.Bisim               {E = TEv} {I = ExtI TEv} using (_∼_; sbisim-sym)
open import Semantics.StrongImpliesDR     {E = TEv} {I = ExtI TEv} using (sbisim→drbisim)
open import Semantics.DRImpliesFD         {E = TEv} {I = ExtI TEv} using (drbisim→≈FD)
open import Semantics.FailuresDivergences {E = TEv} {I = ExtI TEv} using (_≈FD_)
open import CSP.Laws.FD.SeqLaws           TEv-≟ using (seq-unit-r-∼)

TProc : Set₁
TProc = PTree TEv (ExtI TEv) (⊤ {lzero})

-------------------------------------------------------------------------------------
-- The processes
-------------------------------------------------------------------------------------

TE  : TProc
TE  = (up ⟶₀ Stop) □ Skip        -- (up -> STOP) [] SKIP  ; □ picks up the DecEq-⊤ instance

TE′ : TProc
TE′ = TE >> Skip                  -- TE ; SKIP

-------------------------------------------------------------------------------------
-- TE ≈FD TE;SKIP  (tick-as-signal)
-------------------------------------------------------------------------------------

-- TE ∼ TE;SKIP is the right-unit law `TE ; SKIP ∼ TE` read backwards.  The strong
-- bisimulation it packages IS the tick-as-signal step-matching: the `up`-offer relates
-- STOP ↔ STOP;SKIP and the √-slide relates SKIP ↔ SKIP >>= _.
te∼ : TE ∼ TE′
te∼ = sbisim-sym (seq-unit-r-∼ TE)

te-≈FD : TE ≈FD TE′
te-≈FD = drbisim→≈FD (sbisim→drbisim te∼)

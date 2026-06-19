{-# OPTIONS --guardedness #-}

-- SPIKE: monotonicity of the guarded process  b ＆ P = guard b >> P  (Roscoe UCS),
-- at trace refinement ⊑T.  The key tool is `force-≡→traces-⊆`: trees with equal
-- `force` have equal traces (the LTS only inspects `force`).  Then:
--   true  ＆ P = Skip >> P, and force (Skip >> P) ≡ force P        (so ≈T P);
--   false ＆ P = Stop >> P, and force (Stop >> P) ≡ force (Stop>>P′)(both deadlock).
-- No postulates, no NON_TERMINATING.

open import Level using (Level)
open import Data.Bool using (Bool; true; false)
open import Data.List using (List)
open import Data.Product using (Σ; _,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsGuard {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators  E-≟
open import Semantics.LTS       {E = E} {I = ExtI E}
open import Semantics.Failures  {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_)

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- force-equal trees have ⊆ traces (every transition only inspects `force`, so each
-- step is rebuilt at the new source by retargeting its force-equation through `eq`)
-------------------------------------------------------------------------------------

force-≡→traces-⊆ : {t₁ t₂ : PTree E (ExtI E) R} {s : List (Event√ R)}
                 → PTree.force t₁ ≡ PTree.force t₂ → traces t₁ s → traces t₂ s
force-≡→traces-⊆ {t₂ = t₂} eq (_ , ⟹-refl)              = t₂ , ⟹-refl
force-≡→traces-⊆ eq (Q , ⟹-τ  (sSil eqf)    rest)       = Q , ⟹-τ  (sSil (trans (sym eq) eqf))    rest
force-≡→traces-⊆ eq (Q , ⟹-τ  (sTau eqf br)  rest)      = Q , ⟹-τ  (sTau (trans (sym eq) eqf) br)  rest
force-≡→traces-⊆ eq (Q , ⟹-ev (sRet eqf)    rest)       = Q , ⟹-ev (sRet (trans (sym eq) eqf))    rest
force-≡→traces-⊆ eq (Q , ⟹-ev (sVis eqf br)  rest)      = Q , ⟹-ev (sVis (trans (sym eq) eqf) br)  rest

-------------------------------------------------------------------------------------
-- guard is ⊑ᵀ-monotone in its process argument
-------------------------------------------------------------------------------------

＆-mono-⊑ᵀ : (b : Bool) {P P′ : PTree E (ExtI E) R}
           → P ⊑T P′ → (b ＆ P) ⊑T (b ＆ P′)
-- true  ＆ P = Skip >> P  and  force (Skip >> P) ≡ force P,  so route through P
＆-mono-⊑ᵀ true {P} {P′} p⊑ s tp′ =
  force-≡→traces-⊆ {t₁ = P} {t₂ = Skip >> P} refl
    (p⊑ s (force-≡→traces-⊆ {t₁ = Skip >> P′} {t₂ = P′} refl tp′))
-- false ＆ P = Stop >> P  is a deadlock independent of P, so the two sides are force-equal
＆-mono-⊑ᵀ false {P} {P′} p⊑ s tp′ =
  force-≡→traces-⊆ {t₁ = Stop >> P′} {t₂ = Stop >> P} refl tp′

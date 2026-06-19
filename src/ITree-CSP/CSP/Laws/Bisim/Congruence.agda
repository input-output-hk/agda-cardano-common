{-# OPTIONS --guardedness #-}

-- SPIKE: congruence of CSP operators w.r.t. weak bisimulation — the property that
-- makes equational reasoning usable (rewrite under a context).  Starts with the two
-- cleanest cases: internal choice ⊓ and prefix ⟶₀.

open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.Bisim.Congruence {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators  E-≟
open import Semantics.LTS       {E = E} {I = ExtI E}
open import Semantics.WeakBisim {E = E} {I = ExtI E}
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-τ-inv; ⊓-stepL; ⊓-stepR)

-- internal choice is a congruence
⊓-cong : ∀ {ℓr} {R : Set ℓr} {P P′ Q Q′ : PTree E (ExtI E) R}
       → P ≈ P′ → Q ≈ Q′ → (P ⊓ Q) ≈ (P′ ⊓ Q′)
⊓-cong p≈p′ q≈q′ .Wbisim.fwd .WSimF.on-ev (sRet ())
⊓-cong p≈p′ q≈q′ .Wbisim.fwd .WSimF.on-ev (sVis refl ())
⊓-cong {P = P} {P′ = P′} {Q = Q} {Q′ = Q′} p≈p′ q≈q′ .Wbisim.fwd .WSimF.on-tau step
  with ⊓-τ-inv P Q step
... | inj₁ refl = P′ , wτ (τ*-step (⊓-stepL P′ Q′) τ*-refl) , p≈p′
... | inj₂ refl = Q′ , wτ (τ*-step (⊓-stepR P′ Q′) τ*-refl) , q≈q′
⊓-cong p≈p′ q≈q′ .Wbisim.bwd .WSimF.on-ev (sRet ())
⊓-cong p≈p′ q≈q′ .Wbisim.bwd .WSimF.on-ev (sVis refl ())
⊓-cong {P = P} {P′ = P′} {Q = Q} {Q′ = Q′} p≈p′ q≈q′ .Wbisim.bwd .WSimF.on-tau step
  with ⊓-τ-inv P′ Q′ step
... | inj₁ refl = P , wτ (τ*-step (⊓-stepL P Q) τ*-refl) , wbisim-sym p≈p′
... | inj₂ refl = Q , wτ (τ*-step (⊓-stepR P Q) τ*-refl) , wbisim-sym q≈q′

-- the matching prefix branch fires (discharging the no-case via neq refl) — needed
-- because a freshly-built Prefix-cont's E-≟ (A,e)(A,e) does not reduce abstractly.
pc-just : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} (e : E A) (P : PTree E (ExtI E) R) (x : A)
        → Prefix-cont e (λ _ → P) (A , e) x ≡ just P
pc-just {A = A} e P x with E-≟ (A , e) (A , e)
... | yes refl = refl
... | no neq   = ⊥-elim (neq refl)

-- prefix is a congruence (reasons through the abstract decision E-≟)
prefix-cong : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} (e : E A)
              {P Q : PTree E (ExtI E) R}
            → P ≈ Q → (e ⟶₀ P) ≈ (e ⟶₀ Q)
prefix-cong e p≈q .Wbisim.fwd .WSimF.on-ev (sRet ())
prefix-cong {A = A} e {P} {Q} p≈q .Wbisim.fwd .WSimF.on-ev (sVis {at = at} {a = x} refl br)
  with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with br
...               | refl = Q , wev τ*-refl (sVis {at = A , e} {a = x} refl (pc-just e Q x)) τ*-refl , p≈q
prefix-cong e p≈q .Wbisim.fwd .WSimF.on-tau (sSil ())
prefix-cong e p≈q .Wbisim.fwd .WSimF.on-tau (sTau refl ())
prefix-cong e p≈q .Wbisim.bwd .WSimF.on-ev (sRet ())
prefix-cong {A = A} e {P} {Q} p≈q .Wbisim.bwd .WSimF.on-ev (sVis {at = at} {a = x} refl br)
  with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with br
...               | refl = P , wev τ*-refl (sVis {at = A , e} {a = x} refl (pc-just e P x)) τ*-refl , wbisim-sym p≈q
prefix-cong e p≈q .Wbisim.bwd .WSimF.on-tau (sSil ())
prefix-cong e p≈q .Wbisim.bwd .WSimF.on-tau (sTau refl ())

-------------------------------------------------------------------------------------
-- BOUNDARY: why only ⊓ and prefix are here.
--
-- ⊓ and prefix are EXTENSIONAL: their `force` wraps the operands as opaque
-- sub-trees (`react ∅ (br2 P Q)`, `react (Prefix-cont …) ∅`) regardless of what the
-- operands reduce to.  So a congruence proof only relates the operands as black
-- boxes — exactly what `P ≈ Q` provides.
--
-- □, ▷, Par and >>= are INTENSIONAL: `force (P □ Q) with force P | force Q` branches
-- on whether each operand is ret / sil / react, producing structurally different
-- nodes per case.  Weak bisimulation, however, is transition-based, not shape-based:
-- `P ≈ P′` says nothing about whether `force P` and `force P′` share a constructor
-- (e.g. `Tau (a ⟶ Stop) ≈ (a ⟶ Stop)` but their forces are `sil …` vs `react …`).
-- A direct case-on-force proof therefore cannot bridge `force P` to `force P′`, so
-- congruence for these operators needs a bisimulation-UP-TO-CONTEXT technique — a
-- separate piece of metatheory, not an instance of the pattern above.
--
-- (The laws THEMSELVES hold — CSP's □ keeps the choice alive across τ, avoiding the
--  CCS counterexample τ.a + b ≉ a + b — it is only the proof that is hard.)
-------------------------------------------------------------------------------------

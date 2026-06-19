{-# OPTIONS --guardedness #-}

-- FD-equivalence congruences for the EXTENSIONAL CSP operators (prefix ⟶₀ and
-- internal choice ⊓), following the strategy: prove the congruence on DRbisim
-- (≈DR) — where it is constructive — then transport to ≈FD via the bridge
-- `drbisim→≈FD` (Semantics.DRImpliesFD).
--
-- These two operators are extensional (their `force` wraps the operands as opaque
-- sub-trees), so the DRbisim proof is the Wbisim congruence (Laws.Bisim.Congruence)
-- plus the two divergence-correspondence fields:
--   • prefix is stable ⇒ never diverges ⇒ div→/div← are vacuous;
--   • P ⊓ Q diverges iff one operand does ⇒ transport via the operand's div→.

open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (_,_)
open import Data.Maybe using (just)
open import Data.Empty using (⊥-elim)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; subst)

open import Process_Trees

module CSP.Laws.FD.FDCong {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators            E-≟
open import Semantics.LTS                 {E = E} {I = ExtI E}
open import Semantics.WeakBisim           {E = E} {I = ExtI E}
open import Semantics.DRBisim             {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.DRImpliesFD {E = E} {I = ExtI E} using (stable-no-τ; drbisim→≈FD)
open import CSP.Laws.Bisim.Laws       E-≟ using (⊓-τ-inv; ⊓-stepL; ⊓-stepR)
open import CSP.Laws.Bisim.Congruence E-≟ using (pc-just)

-------------------------------------------------------------------------------------
-- Prefix:  e ⟶₀ · is a congruence.  It is stable, so it never diverges.
-------------------------------------------------------------------------------------

prefix-stable : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} {e : E A} {P : PTree E (ExtI E) R}
              → isStable (Prefix e (λ _ → P))
prefix-stable _ _ = refl

prefix-cong-DR : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} (e : E A)
                 {P Q : PTree E (ExtI E) R}
               → DRbisim R P Q → DRbisim R (e ⟶₀ P) (e ⟶₀ Q)
prefix-cong-DR e p≈q .DRbisim.fwd .WSimF.on-ev (sRet ())
prefix-cong-DR {A = A} e {P} {Q} p≈q .DRbisim.fwd .WSimF.on-ev (sVis {at = at} {a = x} refl br)
  with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with br
...               | refl = Q , wev τ*-refl (sVis {at = A , e} {a = x} refl (pc-just e Q x)) τ*-refl , p≈q
prefix-cong-DR e p≈q .DRbisim.fwd .WSimF.on-tau (sSil ())
prefix-cong-DR e p≈q .DRbisim.fwd .WSimF.on-tau (sTau refl ())
prefix-cong-DR e p≈q .DRbisim.bwd .WSimF.on-ev (sRet ())
prefix-cong-DR {A = A} e {P} {Q} p≈q .DRbisim.bwd .WSimF.on-ev (sVis {at = at} {a = x} refl br)
  with E-≟ (A , e) at
... | no _     = case br of λ ()
... | yes refl with br
...               | refl = P , wev τ*-refl (sVis {at = A , e} {a = x} refl (pc-just e P x)) τ*-refl , drbisim-sym p≈q
prefix-cong-DR e p≈q .DRbisim.bwd .WSimF.on-tau (sSil ())
prefix-cong-DR e p≈q .DRbisim.bwd .WSimF.on-tau (sTau refl ())
prefix-cong-DR e {P} {Q} p≈q .DRbisim.div→ d =
  ⊥-elim (stable-no-τ (prefix-stable {e = e} {P = P}) (d .Diverges.step))
prefix-cong-DR e {P} {Q} p≈q .DRbisim.div← d =
  ⊥-elim (stable-no-τ (prefix-stable {e = e} {P = Q}) (d .Diverges.step))

prefix-cong-FD : ∀ {ℓr} {A : Set ℓ} {R : Set ℓr} (e : E A)
                 {P Q : PTree E (ExtI E) R}
               → DRbisim R P Q → (e ⟶₀ P) ≈FD (e ⟶₀ Q)
prefix-cong-FD e p≈q = drbisim→≈FD (prefix-cong-DR e p≈q)

-------------------------------------------------------------------------------------
-- Internal choice ⊓ is a congruence.  P ⊓ Q diverges iff a chosen operand diverges,
-- so a divergence transports through that operand's div→.
-------------------------------------------------------------------------------------

⊓-div→ : ∀ {ℓr} {R : Set ℓr} {P Q P′ Q′ : PTree E (ExtI E) R}
       → DRbisim R P P′ → DRbisim R Q Q′
       → Diverges (P ⊓ Q) → Diverges (P′ ⊓ Q′)
⊓-div→ {P = P} {Q = Q} {P′ = P′} {Q′ = Q′} pp qq d with ⊓-τ-inv P Q (d .Diverges.step)
... | inj₁ eq = record { step = ⊓-stepL P′ Q′
                       ; rest = pp .DRbisim.div→ (subst Diverges eq (d .Diverges.rest)) }
... | inj₂ eq = record { step = ⊓-stepR P′ Q′
                       ; rest = qq .DRbisim.div→ (subst Diverges eq (d .Diverges.rest)) }

⊓-cong-DR : ∀ {ℓr} {R : Set ℓr} {P P′ Q Q′ : PTree E (ExtI E) R}
          → DRbisim R P P′ → DRbisim R Q Q′ → DRbisim R (P ⊓ Q) (P′ ⊓ Q′)
⊓-cong-DR pp qq .DRbisim.fwd .WSimF.on-ev (sRet ())
⊓-cong-DR pp qq .DRbisim.fwd .WSimF.on-ev (sVis refl ())
⊓-cong-DR {P = P} {P′ = P′} {Q = Q} {Q′ = Q′} pp qq .DRbisim.fwd .WSimF.on-tau step
  with ⊓-τ-inv P Q step
... | inj₁ refl = P′ , wτ (τ*-step (⊓-stepL P′ Q′) τ*-refl) , pp
... | inj₂ refl = Q′ , wτ (τ*-step (⊓-stepR P′ Q′) τ*-refl) , qq
⊓-cong-DR pp qq .DRbisim.bwd .WSimF.on-ev (sRet ())
⊓-cong-DR pp qq .DRbisim.bwd .WSimF.on-ev (sVis refl ())
⊓-cong-DR {P = P} {P′ = P′} {Q = Q} {Q′ = Q′} pp qq .DRbisim.bwd .WSimF.on-tau step
  with ⊓-τ-inv P′ Q′ step
... | inj₁ refl = P , wτ (τ*-step (⊓-stepL P Q) τ*-refl) , drbisim-sym pp
... | inj₂ refl = Q , wτ (τ*-step (⊓-stepR P Q) τ*-refl) , drbisim-sym qq
⊓-cong-DR pp qq .DRbisim.div→ d = ⊓-div→ pp qq d
⊓-cong-DR pp qq .DRbisim.div← d = ⊓-div→ (drbisim-sym pp) (drbisim-sym qq) d

⊓-cong-FD : ∀ {ℓr} {R : Set ℓr} {P P′ Q Q′ : PTree E (ExtI E) R}
          → DRbisim R P P′ → DRbisim R Q Q′ → (P ⊓ Q) ≈FD (P′ ⊓ Q′)
⊓-cong-FD pp qq = drbisim→≈FD (⊓-cong-DR pp qq)

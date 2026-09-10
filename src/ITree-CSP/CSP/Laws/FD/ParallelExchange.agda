{-# OPTIONS --guardedness #-}

-- Interleaving EXCHANGE at ≈FD:  P ⦀ (Q ⦀ R) ≈FD Q ⦀ (P ⦀ R), with NO side
-- condition (no `Sep`, no `SepDR`, no `OffersOnly`, no disjointness).
--
-- Why it is unconditional.  The two reassociations are `⦀-assoc-FD`
-- (`CSP.Laws.FD.ParallelAssoc`), which is itself unconditional; the inner swap's
-- premise is COMMUTATIVITY, and commutativity of `⦀` holds already at STRONG
-- bisimulation (`Par-comm`), so it rides the UNCONDITIONAL `∼`-congruence
-- `cong-⦀-∼` and is then lifted.  Nothing here ever needs an `≈FD`-premised
-- congruence with a separation obligation.
--
-- The module also names the plain `≈FD`-congruence of `⦀` (`⦀-cong-FD`), which is
-- just the FACT-SHAPED `⦀-mono-⊑FD` (`CSP.Laws.FD.ParallelMonoFD`) read in both
-- refinement directions — that law carries no `Sep` either, so a rewrite may be
-- performed at ANY depth of a `⦀` spine.  (Contrast the FSim-shaped parallel
-- congruences of `CSP.Laws.FSim.*`, which do demand `Sep`.)
--
-- Exchange is genuinely FALSE at `∼`: when P, Q and R all offer the same event the
-- two bracketings commit their overlaps in a different order, which is also why
-- associativity is proved only at `≈FD` (see `ParallelAssoc`'s header).

open import Level using (Level)
open import Data.Unit.Polymorphic using (⊤)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.FD.ParallelExchange {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟
open import Semantics.Bisim {E = E} {I = ExtI E} using (_∼_; sbisim-refl)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_≈FD_; ≈FD-refl; ≈FD-sym; ≈FD-trans)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Bisim.ParallelCong E-≟ using (cong-⦀-∼)
open import CSP.Laws.FD.ParallelAssoc   E-≟ using (⦀-assoc-FD)
open import CSP.Laws.FD.ParallelComm    E-≟ using (Par-comm)
open import CSP.Laws.FD.ParallelMonoFD  E-≟ using (⦀-mono-⊑FD)

private
  variable
    ℓr : Level

-- lift a strong bisimulation all the way down to ≈FD (the two library bridges)
∼→≈FD : {P Q : PTree E (ExtI E) (⊤ {ℓr})} → P ∼ Q → P ≈FD Q
∼→≈FD p∼q = drbisim→≈FD (sbisim→drbisim p∼q)

-- interleaving is an ≈FD-congruence in BOTH operands, unconditionally: the
-- fact-shaped `⦀-mono-⊑FD` applied in each refinement direction
⦀-cong-FD : {P P′ Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
          → P ≈FD P′ → Q ≈FD Q′ → (P ⦀ Q) ≈FD (P′ ⦀ Q′)
⦀-cong-FD (p⊑ , ⊑p) (q⊑ , ⊑q) = ⦀-mono-⊑FD p⊑ q⊑ , ⦀-mono-⊑FD ⊑p ⊑q

-- rewrite only the TAIL of one `⦀` level, leaving the head alone
⦀-tail-FD : (P : PTree E (ExtI E) (⊤ {ℓr})) {Q Q′ : PTree E (ExtI E) (⊤ {ℓr})}
          → Q ≈FD Q′ → (P ⦀ Q) ≈FD (P ⦀ Q′)
⦀-tail-FD P q≈ = ⦀-cong-FD (≈FD-refl P) q≈

-- commutativity of `⦀`, transported to ≈FD (it holds already at `∼`)
⦀-comm-FD : (P Q : PTree E (ExtI E) (⊤ {ℓr})) → (P ⦀ Q) ≈FD (Q ⦀ P)
⦀-comm-FD P Q = ∼→≈FD (Par-comm ∅ES P Q)

-- HEADLINE: adjacent-pair EXCHANGE in a right-nested `⦀` spine, unconditional.
-- Both reassociations are `⦀-assoc-FD`; the middle swap is the unconditional
-- `∼`-congruence applied to commutativity, then lifted — no `Sep` anywhere.
⦀-exchange-FD : (P Q R₀ : PTree E (ExtI E) (⊤ {ℓr}))
              → (P ⦀ (Q ⦀ R₀)) ≈FD (Q ⦀ (P ⦀ R₀))
⦀-exchange-FD P Q R₀ =
  ≈FD-trans (≈FD-sym (⦀-assoc-FD P Q R₀))
  (≈FD-trans (∼→≈FD (cong-⦀-∼ (Par-comm ∅ES P Q) (sbisim-refl R₀)))
             (⦀-assoc-FD Q P R₀))

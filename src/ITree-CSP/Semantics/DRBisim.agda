{-# OPTIONS --guardedness #-}

-- SPIKE: divergence-respecting weak bisimulation (DRbisim) on the pure-react LTS.
-- It is weak bisimulation PLUS a divergence-correspondence, so it rules out the
-- div ≈ deadlock pathology that made failures-respects-≈ fail for plain weak bisim.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary using (IsEquivalence; Setoid)
open import Relation.Binary.PropositionalEquality using (refl)

open import Process_Trees

module Semantics.DRBisim {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I}

-- divergence: an infinite τ-path
record Diverges {ℓr} {R : Set ℓr} (t : PTree E I R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    {next} : PTree E I R
    step   : t ─[ τ ]─► next
    rest   : Diverges next

-- div diverges; deadlock converges
div-diverges : ∀ {ℓr} {R : Set ℓr} → Diverges (div {E = E} {I = I} {R = R})
div-diverges .Diverges.next = div
div-diverges .Diverges.step = sSil refl
div-diverges .Diverges.rest = div-diverges

deadlock-no-τ : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} → ¬ (deadlock ─[ τ ]─► t)
deadlock-no-τ (sSil ())
deadlock-no-τ (sTau refl ())

deadlock-converges : ∀ {ℓr} {R : Set ℓr} → ¬ Diverges (deadlock {E = E} {I = I} {R = R})
deadlock-converges d = deadlock-no-τ (d .Diverges.step)

-- divergence-respecting weak bisimulation: weak simulation both ways + divergence match
record DRbisim {ℓr} (R : Set ℓr) (t₁ t₂ : PTree E I R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    fwd  : WSimF (DRbisim R) t₁ t₂
    bwd  : WSimF (DRbisim R) t₂ t₁
    div→ : Diverges t₁ → Diverges t₂
    div← : Diverges t₂ → Diverges t₁

_≈DR_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
_≈DR_ {R = R} = DRbisim R

-- reflexivity, symmetry
dr-sim-refl  : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → WSimF (DRbisim R) t t
drbisim-refl : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → DRbisim R t t
dr-sim-refl t .WSimF.on-ev  step = _ , wev τ*-refl step τ*-refl , drbisim-refl _
dr-sim-refl t .WSimF.on-tau step = _ , wτ (τ*-step step τ*-refl) , drbisim-refl _
drbisim-refl t .DRbisim.fwd  = dr-sim-refl t
drbisim-refl t .DRbisim.bwd  = dr-sim-refl t
drbisim-refl t .DRbisim.div→ d = d
drbisim-refl t .DRbisim.div← d = d

drbisim-sym : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R} → DRbisim R t₁ t₂ → DRbisim R t₂ t₁
drbisim-sym p .DRbisim.fwd  = p .DRbisim.bwd
drbisim-sym p .DRbisim.bwd  = p .DRbisim.fwd
drbisim-sym p .DRbisim.div→ = p .DRbisim.div←
drbisim-sym p .DRbisim.div← = p .DRbisim.div→

-- DRbisim is finer than weak bisim: drop the divergence fields
drbisim→wbisim : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R} → DRbisim R t₁ t₂ → Wbisim R t₁ t₂
drbisim→wbisim p .Wbisim.fwd .WSimF.on-ev  s with p .DRbisim.fwd .WSimF.on-ev  s
... | _ , w , rel = _ , w , drbisim→wbisim rel
drbisim→wbisim p .Wbisim.fwd .WSimF.on-tau s with p .DRbisim.fwd .WSimF.on-tau s
... | _ , w , rel = _ , w , drbisim→wbisim rel
drbisim→wbisim p .Wbisim.bwd .WSimF.on-ev  s with p .DRbisim.bwd .WSimF.on-ev  s
... | _ , w , rel = _ , w , drbisim→wbisim rel
drbisim→wbisim p .Wbisim.bwd .WSimF.on-tau s with p .DRbisim.bwd .WSimF.on-tau s
... | _ , w , rel = _ , w , drbisim→wbisim rel

-- THE PAYOFF: unlike weak bisim (div ≈ deadlock), DRbisim distinguishes them,
-- because div diverges and deadlock does not.
div≉DR-deadlock : ∀ {ℓr} {R : Set ℓr} → ¬ DRbisim R (div {E = E} {I = I} {R = R}) deadlock
div≉DR-deadlock dr = deadlock-converges (dr .DRbisim.div→ div-diverges)

-------------------------------------------------------------------------------------
-- Transitivity.  The genuine difficulty of weak bisimulation: a single step on the
-- left is matched by a WEAK (τ*-padded) step in the middle; that WEAK step must in
-- turn be matched by a weak step on the right.  So we first lift the single-step
-- simulation `WSimF (DRbisim R)` to a simulation of *weak* steps (`dr-τ*-sim` for τ*,
-- `dr-wev-sim` for a weak visible run), then compose.  Divergence composes directly
-- through `div→` / `div←`.
--
-- These weak-step lemmas are stated generically over a single-step simulation
-- `WSimF (DRbisim R) Q S` (the `.fwd` of a DRbisim), reusing `τ*-trans` from
-- `WeakBisim`.
-------------------------------------------------------------------------------------

-- a τ* run of Q is matched by a τ* run of S, given a single-step DR-simulation Q→S.
-- The residual relation each step is the DRbisim carried by the simulation; we only
-- need the τ* on S and the FINAL DRbisim, so we thread the simulation forward.
dr-τ*-sim : ∀ {ℓr} {R : Set ℓr} {Q Q′ S : PTree E I R}
          → Q ─[τ*]─► Q′ → DRbisim R Q S
          → Σ[ S′ ∈ PTree E I R ] (S ─[τ*]─► S′ × DRbisim R Q′ S′)
dr-τ*-sim τ*-refl          q≈s = _ , τ*-refl , q≈s
dr-τ*-sim (τ*-step qτ rest) q≈s with q≈s .DRbisim.fwd .WSimF.on-tau qτ
... | _ , wτ s→s₁ , q₁≈s₁ with dr-τ*-sim rest q₁≈s₁
...   | S′ , s₁→s′ , q′≈s′ = S′ , τ*-trans s→s₁ s₁→s′ , q′≈s′

-- a weak visible run of Q is matched by a weak visible run of S.
dr-wev-sim : ∀ {ℓr} {R : Set ℓr} {Q Q′ S : PTree E I R} {l : Event√ R}
           → Q ═[ ev l ]═► Q′ → DRbisim R Q S
           → Σ[ S′ ∈ PTree E I R ] (S ═[ ev l ]═► S′ × DRbisim R Q′ S′)
dr-wev-sim (wev q→q₁ q₁ev q₂→q′) q≈s with dr-τ*-sim q→q₁ q≈s
... | _ , s→s₁ , q₁≈s₁ with q₁≈s₁ .DRbisim.fwd .WSimF.on-ev q₁ev
...   | _ , wev s₁→m mev n→s₂ , q₂≈s₂ with dr-τ*-sim q₂→q′ q₂≈s₂
...     | S′ , s₂→s′ , q′≈s′ =
          S′ , wev (τ*-trans s→s₁ s₁→m) mev (τ*-trans n→s₂ s₂→s′) , q′≈s′

-- composing a single-step DR-simulation P→Q with a DRbisim Q≈S: a single step of P
-- is matched by a weak step of S, residuals related by composition.  Stated as a
-- transformation on `WSimF`s so that `drbisim-trans` can use it for both directions
-- without invoking symmetry (which would break the productivity check).
dr-sim-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R}
             → WSimF (DRbisim R) P Q → DRbisim R Q S → WSimF (DRbisim R) P S
drbisim-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R}
              → DRbisim R P Q → DRbisim R Q S → DRbisim R P S

dr-sim-trans p→q q≈s .WSimF.on-ev pev with p→q .WSimF.on-ev pev
... | _ , q-weak , p′≈q′ with dr-wev-sim q-weak q≈s
...   | S′ , s-weak , q′≈s′ = S′ , s-weak , drbisim-trans p′≈q′ q′≈s′
dr-sim-trans p→q q≈s .WSimF.on-tau pτ with p→q .WSimF.on-tau pτ
... | _ , wτ q→q′ , p′≈q′ with dr-τ*-sim q→q′ q≈s
...   | S′ , s→s′ , q′≈s′ = S′ , wτ s→s′ , drbisim-trans p′≈q′ q′≈s′

drbisim-trans p≈q q≈s .DRbisim.fwd  = dr-sim-trans (p≈q .DRbisim.fwd) q≈s
drbisim-trans p≈q q≈s .DRbisim.bwd  =
  dr-sim-trans (q≈s .DRbisim.bwd) (drbisim-sym p≈q)
drbisim-trans p≈q q≈s .DRbisim.div→ d = q≈s .DRbisim.div→ (p≈q .DRbisim.div→ d)
drbisim-trans p≈q q≈s .DRbisim.div← d = p≈q .DRbisim.div← (q≈s .DRbisim.div← d)

-- divergence-respecting weak bisim is an equivalence relation:
≈DR-isEquivalence : ∀ {ℓr} {R : Set ℓr} → IsEquivalence (_≈DR_ {R = R})
≈DR-isEquivalence = record
  { refl  = λ {x} → drbisim-refl x
  ; sym   = drbisim-sym
  ; trans = drbisim-trans
  }

≈DR-setoid : ∀ {ℓr} (R : Set ℓr) → Setoid _ _
≈DR-setoid R = record
  { Carrier       = PTree E I R
  ; _≈_           = _≈DR_
  ; isEquivalence = ≈DR-isEquivalence
  }

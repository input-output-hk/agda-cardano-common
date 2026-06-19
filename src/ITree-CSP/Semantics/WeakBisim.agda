{-# OPTIONS --guardedness #-}

-- SPIKE: weak (τ-abstracting) bisimulation over the pure-react LTS.
-- A strong step on one side is matched by a WEAK step (τ*-padded) on the other,
-- so laws that change the number of τ's (⊓-idempotence, …) become provable.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Process_Trees

module Semantics.WeakBisim {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS {ℓ} {ℓe} {ℓi} {E} {I}

-- reflexive-transitive closure of τ
data _─[τ*]─►_ {ℓr} {R : Set ℓr}
    : PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  τ*-refl : ∀ {t} → t ─[τ*]─► t
  τ*-step : ∀ {t t′ t″} → t ─[ τ ]─► t′ → t′ ─[τ*]─► t″ → t ─[τ*]─► t″

-- weak transitions:  τ̂ = τ*  ;  weak visible = τ* · a · τ*
data _═[_]═►_ {ℓr} {R : Set ℓr}
    : PTree E I R → Label R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  wτ  : ∀ {p q} → p ─[τ*]─► q → p ═[ τ ]═► q
  wev : ∀ {p p′ q′ q} {l : Event√ R}
      → p ─[τ*]─► p′ → p′ ─[ ev l ]─► q′ → q′ ─[τ*]─► q
      → p ═[ ev l ]═► q

record WSimF {ℓr ℓ≈} {R : Set ℓr}
             (TreeRel : Rel (PTree E I R) ℓ≈)
             (t₁ t₂ : PTree E I R)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓ≈) where
  field
    on-ev  : ∀ {l : Event√ R} {t₁′}
           → t₁ ─[ ev l ]─► t₁′
           → Σ[ t₂′ ∈ PTree E I R ] (t₂ ═[ ev l ]═► t₂′ × TreeRel t₁′ t₂′)
    on-tau : ∀ {t₁′}
           → t₁ ─[ τ ]─► t₁′
           → Σ[ t₂′ ∈ PTree E I R ] (t₂ ═[ τ ]═► t₂′ × TreeRel t₁′ t₂′)

record Wbisim {ℓr} (R : Set ℓr) (t₁ t₂ : PTree E I R)
            : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    fwd : WSimF (Wbisim R) t₁ t₂
    bwd : WSimF (Wbisim R) t₂ t₁

_≈_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
_≈_ {R = R} = Wbisim R

-- reflexivity: a step is matched by itself padded with zero τ's
wsim-refl   : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → WSimF (Wbisim R) t t
wbisim-refl : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → Wbisim R t t
wsim-refl t .WSimF.on-ev  step = _ , wev τ*-refl step τ*-refl , wbisim-refl _
wsim-refl t .WSimF.on-tau step = _ , wτ (τ*-step step τ*-refl) , wbisim-refl _
wbisim-refl t .Wbisim.fwd = wsim-refl t
wbisim-refl t .Wbisim.bwd = wsim-refl t

-- symmetry
wbisim-sym : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R} → Wbisim R t₁ t₂ → Wbisim R t₂ t₁
wbisim-sym p .Wbisim.fwd = p .Wbisim.bwd
wbisim-sym p .Wbisim.bwd = p .Wbisim.fwd

-------------------------------------------------------------------------------------
-- Transitivity.  Needs to lift the single-step simulation (.fwd) to WEAK steps:
-- if Q can weakly do l and Q ≈ S, then S can weakly do l to a related state.
-------------------------------------------------------------------------------------

τ*-trans : ∀ {ℓr} {R : Set ℓr} {t t′ t″ : PTree E I R}
         → t ─[τ*]─► t′ → t′ ─[τ*]─► t″ → t ─[τ*]─► t″
τ*-trans τ*-refl        q = q
τ*-trans (τ*-step s rs) q = τ*-step s (τ*-trans rs q)

-- a τ* run of Q is matched by a τ* run of any S with Q ≈ S
τ*-sim : ∀ {ℓr} {R : Set ℓr} {Q Q′ S : PTree E I R}
       → Q ─[τ*]─► Q′ → Wbisim R Q S
       → Σ[ S′ ∈ PTree E I R ] (S ─[τ*]─► S′ × Wbisim R Q′ S′)
τ*-sim τ*-refl          q≈s = _ , τ*-refl , q≈s
τ*-sim (τ*-step qτ rest) q≈s with q≈s .Wbisim.fwd .WSimF.on-tau qτ
... | _ , wτ s→s₁ , q₁≈s₁ with τ*-sim rest q₁≈s₁
...   | S′ , s₁→s′ , q′≈s′ = S′ , τ*-trans s→s₁ s₁→s′ , q′≈s′

-- a weak visible run of Q is matched by a weak visible run of S
wev-sim : ∀ {ℓr} {R : Set ℓr} {Q Q′ S : PTree E I R} {l : Event√ R}
        → Q ═[ ev l ]═► Q′ → Wbisim R Q S
        → Σ[ S′ ∈ PTree E I R ] (S ═[ ev l ]═► S′ × Wbisim R Q′ S′)
wev-sim (wev q→q₁ q₁ev q₂→q′) q≈s with τ*-sim q→q₁ q≈s
... | _ , s→s₁ , q₁≈s₁ with q₁≈s₁ .Wbisim.fwd .WSimF.on-ev q₁ev
...   | _ , wev s₁→m mev n→s₂ , q₂≈s₂ with τ*-sim q₂→q′ q₂≈s₂
...     | S′ , s₂→s′ , q′≈s′ =
          S′ , wev (τ*-trans s→s₁ s₁→m) mev (τ*-trans n→s₂ s₂→s′) , q′≈s′

-- composing a single-step simulation P→Q with a weak bisim Q≈S: a single step of P
-- is matched by a WEAK step of S, residuals related by composition.  Stated as a
-- transformation on `WSimF`s (mirroring `dr-sim-trans`) so that `wbisim-trans` can use
-- it for BOTH directions without taking `.fwd` of a symmetric reversed composition —
-- that detour is what previously forced the `NON_TERMINATING` pragma.  Here the
-- corecursive `wbisim-trans` sits under the Σ-result of the simulation and is guarded.
w-sim-trans  : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R}
             → WSimF (Wbisim R) P Q → Wbisim R Q S → WSimF (Wbisim R) P S
wbisim-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R}
             → Wbisim R P Q → Wbisim R Q S → Wbisim R P S

w-sim-trans p→q q≈s .WSimF.on-ev pev with p→q .WSimF.on-ev pev
... | _ , q-weak , p′≈q′ with wev-sim q-weak q≈s
...   | S′ , s-weak , q′≈s′ = S′ , s-weak , wbisim-trans p′≈q′ q′≈s′
w-sim-trans p→q q≈s .WSimF.on-tau pτ with p→q .WSimF.on-tau pτ
... | _ , wτ q→q′ , p′≈q′ with τ*-sim q→q′ q≈s
...   | S′ , s→s′ , q′≈s′ = S′ , wτ s→s′ , wbisim-trans p′≈q′ q′≈s′

wbisim-trans p≈q q≈s .Wbisim.fwd = w-sim-trans (p≈q .Wbisim.fwd) q≈s
wbisim-trans p≈q q≈s .Wbisim.bwd =
  w-sim-trans (q≈s .Wbisim.bwd) (wbisim-sym p≈q)

-- weak bisim is an equivalence relation:
≈-isEquivalence : ∀ {ℓr} {R : Set ℓr} → IsEquivalence (_≈_ {R = R})
≈-isEquivalence = record
  { refl  = λ {x} → wbisim-refl x
  ; sym   = wbisim-sym
  ; trans = wbisim-trans
  }

≈-setoid : ∀ {ℓr} (R : Set ℓr) → Setoid _ _
≈-setoid R = record
  { Carrier       = PTree E I R
  ; _≈_           = _≈_
  ; isEquivalence = ≈-isEquivalence
  }

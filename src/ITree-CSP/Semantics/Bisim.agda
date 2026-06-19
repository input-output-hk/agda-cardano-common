{-# OPTIONS --guardedness #-}

-- SPIKE: label-based strong bisimulation over the pure-react LTS.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Relation.Binary using (Rel; IsEquivalence; Setoid)

open import Process_Trees

module Semantics.Bisim {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS {ℓ} {ℓe} {ℓi} {E} {I}

-- one unfolding of bisimulation, phrased entirely on LTS labels
record SSimF {ℓr ℓ≈} {R : Set ℓr}
             (TreeRel : Rel (PTree E I R) ℓ≈)
             (t₁ t₂ : PTree E I R)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓ≈) where
  field
    on-ev  : ∀ {l : Event√ R} {t₁′}
           → t₁ ─[ ev l ]─► t₁′
           → Σ[ t₂′ ∈ PTree E I R ] (t₂ ─[ ev l ]─► t₂′ × TreeRel t₁′ t₂′)
    on-tau : ∀ {t₁′}
           → t₁ ─[ τ ]─► t₁′
           → Σ[ t₂′ ∈ PTree E I R ] (t₂ ─[ τ ]─► t₂′ × TreeRel t₁′ t₂′)

record Sbisim {ℓr} (R : Set ℓr) (t₁ t₂ : PTree E I R)
            : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    fwd : SSimF (Sbisim R) t₁ t₂
    bwd : SSimF (Sbisim R) t₂ t₁

_∼_ : ∀ {ℓr} {R : Set ℓr} → PTree E I R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
_∼_ {R = R} = Sbisim R

-- reflexivity
ssim-refl   : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → SSimF (Sbisim R) t t
sbisim-refl : ∀ {ℓr} {R : Set ℓr} (t : PTree E I R) → Sbisim R t t
ssim-refl t .SSimF.on-ev  step = _ , step , sbisim-refl _
ssim-refl t .SSimF.on-tau step = _ , step , sbisim-refl _
sbisim-refl t .Sbisim.fwd = ssim-refl t
sbisim-refl t .Sbisim.bwd = ssim-refl t

-- symmetry (just swap fwd/bwd)
sbisim-sym : ∀ {ℓr} {R : Set ℓr} {t₁ t₂ : PTree E I R} → Sbisim R t₁ t₂ → Sbisim R t₂ t₁
sbisim-sym p .Sbisim.fwd = p .Sbisim.bwd
sbisim-sym p .Sbisim.bwd = p .Sbisim.fwd

-------------------------------------------------------------------------------------
-- Transitivity.  Strong bisimulation matches SINGLE steps (no τ* padding), so the
-- composition is structurally productive: a step of P matched by a single step of Q,
-- that in turn matched by a single step of S; the residual is closed corecursively.
-- `bwd` routes through the reversed composition (mirroring `drbisim-trans`), but with
-- single steps the simulation transformer `ssim-trans` is itself enough.
-------------------------------------------------------------------------------------

-- composing a single-step simulation P→Q with a strong bisim Q∼S: a single step of P
-- is matched by a single step of S, residuals related by composition.
ssim-trans   : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R}
             → SSimF (Sbisim R) P Q → Sbisim R Q S → SSimF (Sbisim R) P S
sbisim-trans : ∀ {ℓr} {R : Set ℓr} {P Q S : PTree E I R}
             → Sbisim R P Q → Sbisim R Q S → Sbisim R P S

ssim-trans p→q q∼s .SSimF.on-ev pev with p→q .SSimF.on-ev pev
... | _ , q-step , p′∼q′ with q∼s .Sbisim.fwd .SSimF.on-ev q-step
...   | S′ , s-step , q′∼s′ = S′ , s-step , sbisim-trans p′∼q′ q′∼s′
ssim-trans p→q q∼s .SSimF.on-tau pτ with p→q .SSimF.on-tau pτ
... | _ , q-step , p′∼q′ with q∼s .Sbisim.fwd .SSimF.on-tau q-step
...   | S′ , s-step , q′∼s′ = S′ , s-step , sbisim-trans p′∼q′ q′∼s′

sbisim-trans p∼q q∼s .Sbisim.fwd = ssim-trans (p∼q .Sbisim.fwd) q∼s
sbisim-trans p∼q q∼s .Sbisim.bwd =
  ssim-trans (q∼s .Sbisim.bwd) (sbisim-sym p∼q)

-- the four behavioural equivalences are equivalence relations; strong bisim:
∼-isEquivalence : ∀ {ℓr} {R : Set ℓr} → IsEquivalence (_∼_ {R = R})
∼-isEquivalence = record
  { refl  = λ {x} → sbisim-refl x
  ; sym   = sbisim-sym
  ; trans = sbisim-trans
  }

∼-setoid : ∀ {ℓr} (R : Set ℓr) → Setoid _ _
∼-setoid R = record
  { Carrier       = PTree E I R
  ; _≈_           = _∼_
  ; isEquivalence = ∼-isEquivalence
  }

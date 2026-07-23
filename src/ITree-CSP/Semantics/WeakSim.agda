{-# OPTIONS --guardedness #-}

-- One-way weak simulation and its trace-inclusion theorem.
-- WSim is the fwd half of Wbisim; wsim-traces is traces-≈→ with the
-- bwd cases deleted.  Used by CSP.Examples.TPC.* to discharge the
-- one-directional FDR trace-refinement asserts.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)

open import Process_Trees

module Semantics.WeakSim {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Failures  {ℓ} {ℓe} {ℓi} {E} {I}

record WSim {ℓr} (R : Set ℓr) (t₁ t₂ : PTree E I R)
          : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    fwd : WSimF (WSim R) t₁ t₂
open WSim public

-- a simulated process's big-step trace is replayed move-by-move (cf. trace-sim)
wsim-trace-sim : ∀ {ℓr} {R : Set ℓr} {P Q P′ : PTree E I R} {s}
               → WSim R P Q → P ⟹⟨ s ⟩ P′
               → Σ[ Q′ ∈ PTree E I R ] (Q ⟹⟨ s ⟩ Q′ × WSim R P′ Q′)
wsim-trace-sim p≲q ⟹-refl = _ , ⟹-refl , p≲q
wsim-trace-sim p≲q (⟹-τ pτ rest)  with p≲q .fwd .WSimF.on-tau pτ
... | _ , qτ , p₁≲q₁ with wsim-trace-sim p₁≲q₁ rest
...   | Q′ , q⟹ , p′≲q′ = Q′ , weaken-τ qτ q⟹ , p′≲q′
wsim-trace-sim p≲q (⟹-ev pev rest) with p≲q .fwd .WSimF.on-ev pev
... | _ , qev , p₁≲q₁ with wsim-trace-sim p₁≲q₁ rest
...   | Q′ , q⟹ , p′≲q′ = Q′ , weaken-ev qev q⟹ , p′≲q′

wsim-traces : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R} {s}
            → WSim R P Q → traces P s → traces Q s
wsim-traces p≲q (_ , tr) with wsim-trace-sim p≲q tr
... | Q′ , q⟹ , _ = Q′ , q⟹

wsim→⊑T : ∀ {ℓr} {R : Set ℓr} {P Q : PTree E I R}
        → WSim R Q P → P ⊑T Q
wsim→⊑T sim s t = wsim-traces sim t

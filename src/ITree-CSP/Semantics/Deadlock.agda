{-# OPTIONS --guardedness #-}

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; Σ-syntax; _×_)
open import Data.List using (List; [])
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Process_Trees

module Semantics.Deadlock {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS      {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.Failures {ℓ} {ℓe} {ℓi} {E} {I}

-- A state is stuck (real deadlock) when no LTS label is enabled.
IsStuck : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
IsStuck {R = R} t = ∀ {l : Label R} {t′ : PTree E I R} → t ─[ l ]─► t′ → ⊥

-- Deadlock-free: no state reachable via the τ-absorbing big-step ⟹⟨_⟩ is stuck.
-- Successful termination (ret) is NOT a deadlock — ret has the sRet √-step enabled.
DeadlockFree : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
DeadlockFree {R = R} t =
  ∀ {s : List (Event√ R)} {t′ : PTree E I R}
  → t ⟹⟨ s ⟩ t′ → IsStuck t′ → ⊥

-- Dual: a witnessing trace reaching a stuck state.
HasDeadlock : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
HasDeadlock {R = R} t =
  Σ[ s ∈ List (Event√ R) ] Σ[ t′ ∈ PTree E I R ] (t ⟹⟨ s ⟩ t′ × IsStuck t′)

hasDeadlock⇒¬deadlockFree :
  ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
  → HasDeadlock t → ¬ DeadlockFree t
hasDeadlock⇒¬deadlockFree (s , t′ , reach , stuck) df = df reach stuck

private
  module Sanity where
    -- `deadlock` (CSP Stop) is stuck.
    deadlock-IsStuck : ∀ {ℓr} {R : Set ℓr} → IsStuck (deadlock {E = E} {I = I} {R = R})
    deadlock-IsStuck (sRet eq)      = case eq of λ ()
    deadlock-IsStuck (sSil eq)      = case eq of λ ()
    deadlock-IsStuck (sVis refl br) = case br of λ ()
    deadlock-IsStuck (sTau refl br) = case br of λ ()

    has-deadlock-deadlock : ∀ {ℓr} {R : Set ℓr} → HasDeadlock (deadlock {E = E} {I = I} {R = R})
    has-deadlock-deadlock = [] , deadlock , ⟹-refl , deadlock-IsStuck

    -- `div` (pure τ-loop) is deadlock-free: every reachable state is `div`.
    div-reaches-div : ∀ {ℓr} {R : Set ℓr} {s : List (Event√ R)} {t′ : PTree E I R}
                    → div ⟹⟨ s ⟩ t′ → t′ ≡ div
    div-reaches-div ⟹-refl = refl
    div-reaches-div (⟹-τ (sSil eq) rest) rewrite sym (sil-injective eq) = div-reaches-div rest
    div-reaches-div (⟹-τ (sTau eq _) _)  = case eq of λ ()
    div-reaches-div (⟹-ev (sVis eq _) _) = case eq of λ ()
    div-reaches-div (⟹-ev (sRet eq) _)   = case eq of λ ()

    deadlock-free-div : ∀ {ℓr} {R : Set ℓr} → DeadlockFree (div {E = E} {I = I} {R = R})
    deadlock-free-div reach stuck rewrite div-reaches-div reach = stuck (sSil refl)

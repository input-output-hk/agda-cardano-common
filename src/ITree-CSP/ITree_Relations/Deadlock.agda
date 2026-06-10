{-# OPTIONS --guardedness #-}

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; Σ-syntax; _×_)
open import Data.List using (List; [])
open import Function using (case_of_)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)

open import Interaction_Trees
open import ITree_Relations.LTS

module ITree_Relations.Deadlock where

open ITree

-- A process is deadlock-free when no state reachable from it (via the
-- τ-absorbing bigstep ═⟨_⟩═►, which folds silent steps into the trace) is
-- stuck (IsStuck: no LTS label enabled).  Successful termination is not a
-- deadlock — only `deadlock`/Stop-like states are stuck.
DeadlockFree : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
DeadlockFree {E = E} {I = I} {R = R} t =
  ∀ {s : List (Event√ E R)} {t′ : ITree E I R}
  → t ═⟨ s ⟩═► t′ → IsStuck t′ → ⊥

-- Dual of DeadlockFree: a witnessing trace `s` that reaches a stuck state `t′`.
HasDeadlock : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
HasDeadlock {E = E} {I = I} {R = R} t =
  Σ[ s ∈ List (Event√ E R) ] Σ[ t′ ∈ ITree E I R ] (t ═⟨ s ⟩═► t′ × IsStuck t′)

hasDeadlock⇒¬deadlockFree :
  ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t : ITree E I R}
  → HasDeadlock t → ¬ DeadlockFree t
hasDeadlock⇒¬deadlockFree (s , t′ , reach , stuck) df = df reach stuck

private
  module Sanity where
    -- `deadlock` (CSP Stop) is stuck.
    deadlock-IsStuck :
      ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → IsStuck (deadlock {E = E} {I = I} {R = R})
    deadlock-IsStuck (sVis refl br-eq) = case br-eq of λ ()
    deadlock-IsStuck (sMixVis eq-mix _) = case eq-mix of λ ()
    deadlock-IsStuck (sRet eq)          = case eq of λ ()
    deadlock-IsStuck (sSil eq)          = case eq of λ ()
    deadlock-IsStuck (sNdbr eq _)       = case eq of λ ()
    deadlock-IsStuck (sMixSlide eq)     = case eq of λ ()

    has-deadlock-deadlock :
      ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → HasDeadlock (deadlock {E = E} {I = I} {R = R})
    has-deadlock-deadlock = [] , deadlock , bNil , deadlock-IsStuck

    -- `div` (pure τ-loop) is deadlock-free: every reachable state is `div`.
    div-reaches-div :
      ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {s : List (Event√ E R)} {t′ : ITree E I R}
      → div ═⟨ s ⟩═► t′ → t′ ≡ div
    div-reaches-div bNil = refl
    div-reaches-div (bTau (sSil eq) rest)
      rewrite sym (sil-injective eq) = div-reaches-div rest
    div-reaches-div (bTau (sNdbr eq _) _)  = case eq of λ ()
    div-reaches-div (bTau (sMixSlide eq) _) = case eq of λ ()
    div-reaches-div (bStep (sVis eq _) _)    = case eq of λ ()
    div-reaches-div (bStep (sMixVis eq _) _) = case eq of λ ()
    div-reaches-div (bStep (sRet eq) _)      = case eq of λ ()

    deadlock-free-div :
      ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → DeadlockFree (div {E = E} {I = I} {R = R})
    deadlock-free-div reach stuck
      rewrite div-reaches-div reach = stuck (sSil refl)

{-# OPTIONS --guardedness #-}

open import Level using (_⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥)
open import Data.Product using (_,_; Σ-syntax; _×_)
open import Data.List using (List; []; _∷_; map)
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

-- Reachability via τ and visible (evl) events only — never traversing the √
-- termination step into Ω.  This is what deadlock-freedom must quantify over:
-- successful termination (√) is NOT a deadlock.
data _⟹∖√⟨_⟩_ {ℓr} {R : Set ℓr}
    : PTree E I R → List Event → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  ∖√-refl : ∀ {p}                                       → p ⟹∖√⟨ [] ⟩ p
  ∖√-τ    : ∀ {p q r s}                 → p ─[ τ ]─► q          → q ⟹∖√⟨ s ⟩ r → p ⟹∖√⟨ s ⟩ r
  ∖√-ev   : ∀ {p q r s} {e : Event}     → p ─[ ev (evl e) ]─► q → q ⟹∖√⟨ s ⟩ r → p ⟹∖√⟨ e ∷ s ⟩ r

-- Deadlock-free: no state reachable via √-free big-step is stuck.  Successful
-- termination (√ → Ω) is exempt because `⟹∖√` never fires √.
DeadlockFree : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
DeadlockFree {R = R} t =
  ∀ {s : List Event} {t′ : PTree E I R} → t ⟹∖√⟨ s ⟩ t′ → IsStuck t′ → ⊥

-- Dual: a √-free trace reaching a stuck state.
HasDeadlock : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
HasDeadlock {R = R} t =
  Σ[ s ∈ List Event ] Σ[ t′ ∈ PTree E I R ] (t ⟹∖√⟨ s ⟩ t′ × IsStuck t′)

hasDeadlock⇒¬deadlockFree :
  ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
  → HasDeadlock t → ¬ DeadlockFree t
hasDeadlock⇒¬deadlockFree (s , t′ , reach , stuck) df = df reach stuck

-- A √-free run embeds into the general big-step run (tag each event with `evl`).
embed∖√ : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R} {s : List Event}
        → t ⟹∖√⟨ s ⟩ t′ → t ⟹⟨ map evl s ⟩ t′
embed∖√ ∖√-refl         = ⟹-refl
embed∖√ (∖√-τ  st rest) = ⟹-τ  st (embed∖√ rest)
embed∖√ (∖√-ev st rest) = ⟹-ev st (embed∖√ rest)

-- Strip `evl` tags from a general big-step run over `map evl s` to get a √-free run.
-- Sound because `map evl s` contains no `√` labels, so every visible step is `evl`-tagged.
strip∖√ : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R} {s : List Event}
        → t ⟹⟨ map evl s ⟩ t′ → t ⟹∖√⟨ s ⟩ t′
strip∖√ {s = []}    ⟹-refl         = ∖√-refl
strip∖√ {s = []}    (⟹-τ  st rest) = ∖√-τ st (strip∖√ rest)
strip∖√ {s = _ ∷ _} (⟹-ev st rest) = ∖√-ev st (strip∖√ rest)
strip∖√ {s = _ ∷ _} (⟹-τ  st rest) = ∖√-τ st (strip∖√ rest)

private
  module Sanity where
    -- `deadlock` (CSP Stop) is stuck.
    deadlock-IsStuck : ∀ {ℓr} {R : Set ℓr} → IsStuck (deadlock {E = E} {I = I} {R = R})
    deadlock-IsStuck (sRet eq)      = case eq of λ ()
    deadlock-IsStuck (sSil eq)      = case eq of λ ()
    deadlock-IsStuck (sVis refl br) = case br of λ ()
    deadlock-IsStuck (sTau refl br) = case br of λ ()

    has-deadlock-deadlock : ∀ {ℓr} {R : Set ℓr} → HasDeadlock (deadlock {E = E} {I = I} {R = R})
    has-deadlock-deadlock = [] , deadlock , ∖√-refl , deadlock-IsStuck

    -- `div` (pure τ-loop) is deadlock-free: every reachable state is `div`.
    div-reaches-div : ∀ {ℓr} {R : Set ℓr} {s : List Event} {t′ : PTree E I R}
                    → div ⟹∖√⟨ s ⟩ t′ → t′ ≡ div
    div-reaches-div ∖√-refl = refl
    div-reaches-div (∖√-τ (sSil eq) rest) rewrite sym (sil-injective eq) = div-reaches-div rest
    div-reaches-div (∖√-τ (sTau eq _) _)  = case eq of λ ()
    div-reaches-div (∖√-ev (sVis eq _) _) = case eq of λ ()

    deadlock-free-div : ∀ {ℓr} {R : Set ℓr} → DeadlockFree (div {E = E} {I = I} {R = R})
    deadlock-free-div reach stuck rewrite div-reaches-div reach = stuck (sSil refl)

{-# OPTIONS --guardedness #-}
-- {-# OPTIONS --cubical-compatible --no-import-sorts #-}

-- open import Agda.Buildin.Maybe
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)
open import Relation.Unary
open import Function using (case_of_)
open import Interaction_Trees

module ITree_Relations.Equivalence where

mutual
  -- ≈ is coinductive: "forever agreeing on all transitions"
  record _≈_ {ℓ ℓe ℓi ℓr}
             {E : Set ℓ → Set ℓe}
             {I : Set ℓ → Set ℓi}
             {R : Set ℓr}
             (t₁ t₂ : ITree E I R)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
    coinductive
    field
      force≈ : NodeKind≈ (ITree.force t₁) (ITree.force t₂)

  -- Structural agreement on the head NodeKind, one layer at a time
  data NodeKind≈ {ℓ ℓe ℓi ℓr}
                 {E : Set ℓ → Set ℓe}
                 {I : Set ℓ → Set ℓi}
                 {R : Set ℓr}
               : NodeKind E I R → NodeKind E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

    -- Both terminate with the same return value
    ret≈ : ∀ {r}
         → NodeKind≈ (ret r) (ret r)

    -- Both take the same silent step, with bisimilar continuations
    sil≈ : ∀ {t₁ t₂}
         → t₁ ≈ t₂
         → NodeKind≈ (sil t₁) (sil t₂)

    -- For every visible event (A , e) and every payload a : A,
    -- both offer the same branch (nothing/just) with bisimilar subtrees
    vis≈ : ∀ {f₁ f₂}
         → (∀ (at : AnyTypes E) (a : proj₁ at)
            → MaybeITree≈ (f₁ at a) (f₂ at a))
         → NodeKind≈ (vis f₁) (vis f₂)

    -- Same idea for indexed (internal/nondeterministic) branches
    inv≈ : ∀ {f₁ f₂}
         → (∀ (i : AnyTypes I) (a : proj₁ i)
            → MaybeITree≈ (f₁ i a) (f₂ i a))
         → NodeKind≈ (inv f₁) (inv f₂)

  -- Lifted ≈ through Maybe: both absent, or both present with bisimilar trees
  data MaybeITree≈ {ℓ ℓe ℓi ℓr}
                   {E : Set ℓ → Set ℓe}
                   {I : Set ℓ → Set ℓi}
                   {R : Set ℓr}
                 : Maybe (ITree E I R) → Maybe (ITree E I R)
                 → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
    nothing≈ : MaybeITree≈ nothing nothing
    just≈    : ∀ {t₁ t₂} → t₁ ≈ t₂ → MaybeITree≈ (just t₁) (just t₂)


-- Reflexivity: corecursive, case-split on force t
≈-refl : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         (t : ITree E I R) → t ≈ t
≈-refl t ._≈_.force≈ with ITree.force t
... | ret r   = ret≈
... | sil t'  = sil≈ (≈-refl t')
... | vis f   = vis≈ (λ at a → go-maybe (f at a))
  where
    go-maybe : ∀ m → MaybeITree≈ m m
    go-maybe nothing   = nothing≈
    go-maybe (just t') = just≈ (≈-refl t')
... | inv f   = inv≈ (λ i a → go-maybe (f i a))
  where
    go-maybe : ∀ m → MaybeITree≈ m m
    go-maybe nothing   = nothing≈
    go-maybe (just t') = just≈ (≈-refl t')

≈-sym : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          {t₁ t₂ : ITree E I R}
        → t₁ ≈ t₂ → t₂ ≈ t₁
≈-sym {t₁ = t₁} {t₂ = t₂} p ._≈_.force≈
  -- Reveal both forces so indices become concrete, THEN match the proof
  with ITree.force t₁ | ITree.force t₂ | p ._≈_.force≈
... | ret r   | ret .r   | ret≈     = ret≈
... | sil s₁  | sil s₂   | sil≈ q   = sil≈ (≈-sym q)
... | vis f₁  | vis f₂   | vis≈ h   = vis≈ (λ at a → sym-maybe (h at a))
  where
    sym-maybe : ∀ {m₁ m₂} → MaybeITree≈ m₁ m₂ → MaybeITree≈ m₂ m₁
    sym-maybe nothing≈  = nothing≈
    sym-maybe (just≈ q) = just≈ (≈-sym q)
... | inv f₁  | inv f₂   | inv≈ h   = inv≈ (λ i a → sym-maybe (h i a))
  where
    sym-maybe : ∀ {m₁ m₂} → MaybeITree≈ m₁ m₂ → MaybeITree≈ m₂ m₁
    sym-maybe nothing≈  = nothing≈
    sym-maybe (just≈ q) = just≈ (≈-sym q)

≈-trans : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {t₁ t₂ t₃ : ITree E I R}
          → t₁ ≈ t₂ → t₂ ≈ t₃ → t₁ ≈ t₃
≈-trans {t₁ = t₁} {t₂ = t₂} {t₃ = t₃} p q ._≈_.force≈
  with ITree.force t₁ | ITree.force t₂ | ITree.force t₃
     | p ._≈_.force≈  | q ._≈_.force≈
... | ret r   | ret .r   | ret .r   | ret≈     | ret≈     = ret≈
... | sil s₁  | sil s₂   | sil s₃   | sil≈ p'  | sil≈ q'  = sil≈ (≈-trans p' q')
... | vis f₁  | vis f₂   | vis f₃   | vis≈ hp  | vis≈ hq  =
      vis≈ (λ at a → trans-maybe (hp at a) (hq at a))
  where
    trans-maybe : ∀ {m₁ m₂ m₃} → MaybeITree≈ m₁ m₂ → MaybeITree≈ m₂ m₃ → MaybeITree≈ m₁ m₃
    trans-maybe nothing≈   nothing≈   = nothing≈
    trans-maybe (just≈ p') (just≈ q') = just≈ (≈-trans p' q')
... | inv f₁  | inv f₂   | inv f₃   | inv≈ hp  | inv≈ hq  =
      inv≈ (λ i a → trans-maybe (hp i a) (hq i a))
  where
    trans-maybe : ∀ {m₁ m₂ m₃} → MaybeITree≈ m₁ m₂ → MaybeITree≈ m₂ m₃ → MaybeITree≈ m₁ m₃
    trans-maybe nothing≈   nothing≈   = nothing≈
    trans-maybe (just≈ p') (just≈ q') = just≈ (≈-trans p' q')
    

{-# OPTIONS --guardedness #-}

-- SPIKE: labelled transition system for the pure-react PTree.
-- Only THREE node kinds (ret/sil/react) ⇒ FOUR rules (vs six for vis/ndbr/mix).

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)

open import Process_Trees

module Semantics.LTS {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree

record Event : Set (lsuc ℓ ⊔ ℓe) where
  constructor evLabel
  field
    A : Set ℓ
    e : E A
    a : A

data Event√ {ℓr} (R : Set ℓr) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  evl : Event → Event√ R
  √   : R → Event√ R

data Label {ℓr} (R : Set ℓr) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  ev : Event√ R → Label R
  τ  : Label R

-- small-step semantics
data _─[_]─►_ {ℓr} {R : Set ℓr}
    : PTree E I R → Label R → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  sRet : ∀ {p : PTree E I R} {x : R}
       → PTree.force p ≡ ret x
       → p ─[ ev (√ x) ]─► deadlock

  sSil : ∀ {p t : PTree E I R}
       → PTree.force p ≡ sil t
       → p ─[ τ ]─► t

  -- a visible offer from the react node's vis-part
  sVis : ∀ {p : PTree E I R}
         {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E I R))}
         {τc : (i  : AnyTypes I) → ContinueType i  (Maybe (PTree E I R))}
         {at : AnyTypes E} {a : proj₁ at} {t′ : PTree E I R}
       → PTree.force p ≡ react v τc
       → v at a ≡ just t′
       → p ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t′

  -- a τ-move from the react node's τ-part
  sTau : ∀ {p : PTree E I R}
         {v  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E I R))}
         {τc : (i  : AnyTypes I) → ContinueType i  (Maybe (PTree E I R))}
         {i  : AnyTypes I} {a : proj₁ i} {t′ : PTree E I R}
       → PTree.force p ≡ react v τc
       → τc i a ≡ just t′
       → p ─[ τ ]─► t′

-- inversion: a τ-step comes from `sil` or from an react τ-branch
τ-inv : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R}
      → t ─[ τ ]─► t′
      → (PTree.force t ≡ sil t′)
      ⊎ (Σ[ v ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E I R))) ]
         Σ[ τc ∈ ((i : AnyTypes I) → ContinueType i (Maybe (PTree E I R))) ]
         Σ[ i ∈ AnyTypes I ] Σ[ a ∈ proj₁ i ]
           (PTree.force t ≡ react v τc × τc i a ≡ just t′))
τ-inv (sSil eq)        = inj₁ eq
τ-inv (sTau {v = v} {τc = τc} {i = i} {a = a} eq br) = inj₂ (v , τc , i , a , eq , br)

-- a visible (non-√) step comes from an react vis-branch
ev-inv : ∀ {ℓr} {R : Set ℓr} {t t′ : PTree E I R} {A : Set ℓ} {e : E A} {a : A}
       → t ─[ ev (evl (evLabel A e a)) ]─► t′
       → Σ[ v ∈ ((at : AnyTypes E) → ContinueType at (Maybe (PTree E I R))) ]
         Σ[ τc ∈ ((i : AnyTypes I) → ContinueType i (Maybe (PTree E I R))) ]
           (PTree.force t ≡ react v τc × v (A , e) a ≡ just t′)
ev-inv (sVis {v = v} {τc = τc} eq br) = v , τc , eq , br

-- divergence: an infinite τ-path (single home for DRBisim + TauAcc to reuse)
record Diverges {ℓr} {R : Set ℓr} (t : PTree E I R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    {next} : PTree E I R
    step   : t ─[ τ ]─► next
    rest   : Diverges next

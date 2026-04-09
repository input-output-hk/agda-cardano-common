{-
  This module defines the traces semantics for CSP.
-}

{-# OPTIONS --guardedness #-}

open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)
open import Relation.Unary using (∅)
open import Function using (case_of_)
-- open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary using (¬_)
-- open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _++_; _∷_; []; length; reverse; map; foldr; downFrom)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym; trans; refl; inspect; [_]; cong)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)

open import Interaction_Trees
open import CSP.Basic_Processes
open import ITree_Relations.LTS

module CSP.Traces where
open ITree
open Traces

-----------------------------------------------------------------
-- Stop makes no τ step
Stop-no-τ :
  ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t′ : ITree E I R}
  → Stop' ─[ τ ]─► t′
  → ⊥
Stop-no-τ tr = τ-from-force-vis-impossible refl tr
  
-- Stop makes no ev step
-- If nothing ≡ just t', then we can produce ⊥
Stop-no-ev :
  ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t′ : ITree E I R}
    {A : Set ℓ} {e : E A} {a : A}        
  → Stop' ─[ ev (evLabel A e a) ]─► t′
  → ⊥
Stop-no-ev {t′ = t′} {A = A} {e = e} {a = a} tr with ev-ndbr tr
... | f , (force≡vis , f-eq) =
  nothing≢just
    (subst (λ g → g (A , e) a ≡ just _)
           (vis-injective (sym force≡vis))   -- f ≡ λ _ _ → nothing
           f-eq)                        -- f (A , e) a ≡ just t′
  where
    nothing≢just : nothing ≡ just _ → ⊥
    nothing≢just ()

-- Stop makes no visible transition
Stop-no-steps : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {s : List (EvLabel E)} {t′ : ITree E I R}
  → Stop' ═⟨ s ⟩═► t′
  → s ≡ []
Stop-no-steps bNil          = refl
Stop-no-steps (bTau τ-step _)  = ⊥-elim (Stop-no-τ τ-step)
Stop-no-steps (bStep ev-step _) = ⊥-elim (Stop-no-ev ev-step)

-- The traces of Stop is empty
Stop-traces-empty : ∀ {ℓ ℓe} {E : Set ℓ → Set ℓe}
    {s : List (EvLabel E)}
  → traces Stop' s
  → s ≡ []
Stop-traces-empty (_ , der) = Stop-no-steps {ℓi = lzero} {ℓr = lzero} {I = λ _ → ⊥} {R = ⊤} der

-- Any ITree refines Stop
⊑ᵀ-Stop : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    (t : ITree E I R)
  → t ⊑ᵀ Stop'
⊑ᵀ-Stop t (_ , der) with Stop-no-steps der
... | refl = t , bNil

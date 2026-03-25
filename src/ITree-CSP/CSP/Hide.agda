{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Fin using (Fin; remQuot) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_)
-- open import Relation.Unary
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
-- open import Class.DecEq
open import Level using (Level)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Class.DecEq

open import Interaction_Trees
open import CSP.Basic_Processes

module CSP.Hide  {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where
open ITree

import CSP.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

-------------------------------------------------------------------------------------
-- Hide
{-# NON_TERMINATING #-}
_∖_¿_ :
  ∀ {ℓr} {R : Set ℓr}
  → {{ DecEq R }}  
  → ITree E (ExtI E) R
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → ITree E (ExtI E) R

force (P ∖ cs ¿ dec) with P .force
... | sil P' = sil (P ∖ cs ¿ dec)
... | ret r  = ret r

-- See hide-step on page 96 of UCS
-- For all events that are not in cs,
--   (?x : A → P(x)) ∖ cs = (?x : (A - cs) → P(x) ∖ cs) ▷ ⨅ a : A ∩ cs @ (P[a/x] ∖ cs)

... | vis fP = (hide-not-in-cs ▷ hide-in-cs) .force
  where
    hide-not-in-cs = itree (vis (λ at a →           -- (?x : A - cs → P(x) ∖ cs)
      case dec at of λ where
        (no  _) → case fP at a of λ where
           nothing  → nothing
           (just P') → just (P' ∖ cs ¿ dec)
        (yes _) → nothing))               -- hidden: removed from vis

    -- ⨅ a : A ∩ cs @ (P[a/x] ∖ cs)
    -- The index of I is cs
    hide-in-cs = itree (inv (λ (A , i) a →
      case i of λ where
        (base e) → case dec (A , e) of λ where
          (no  _) → nothing     -- no this branch
          (yes _) → case fP (A , e) a of λ where
            nothing → nothing   -- no this branch
            (just P') → just (P' ∖ cs ¿ dec)
        (pair _ _) → nothing
        fin → nothing))

... | inv fP = inv (λ ai a →
  case fP ai a of λ where
    nothing → nothing
    (just P') → just (P ∖ cs ¿ dec))

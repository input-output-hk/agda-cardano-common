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

module CSP.Parallel {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where
open ITree

import CSP.Operators {ℓ} {ℓe} {E} as CSPOps
open CSPOps E-≟

-------------------------------------------------------------------------------------
-- Parallel composition
{-# NON_TERMINATING #-}
_∥⇘_¿_⇙_ :
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs} -- → {{ DecEq R }}
  → ITree E (ExtI I) R
  → (cs : AnyTypes E → Set)
  → (dec : (at : AnyTypes E) → Dec (cs at))
  → ITree E (ExtI I) S
  → ITree E (ExtI I) (R × S)

-- force (P ∥⇘ cs ¿ dec ⇙ Q) with P .force | Q .force
force (_∥⇘_¿_⇙_ {I = I} {R = R} {S = S} P cs dec Q) with P .force | Q .force
... | sil P' | _  = sil (P' ∥⇘ cs ¿ dec ⇙ Q)
... | _ | sil Q'  = sil (P ∥⇘ cs ¿ dec ⇙ Q')
... | √ r | √ s = √ (r , s)

... | √ r | vis fQ = vis (λ at x →
  case fQ at x of λ where
    nothing → nothing         -- If P can terminate, but Q cannot, it is finally like a Stop.
                              -- So nothing here, it is called distributed termination.
                              -- See P136 of UCS
    (just Q') → just (P ∥⇘ cs ¿ dec ⇙ Q')
  )
  
... | ret r | inv fQ = inv (λ ai a →   -- ∥-dist 
    case fQ ai a of λ where
      nothing  → nothing
      (just Q') → just (P ∥⇘ cs ¿ dec ⇙ Q'))

... | vis fP | ret s = vis (λ at x →
    case fP at x of λ where
      nothing → nothing         -- If P can terminate, but Q cannot, it is finally like a Stop.
                              -- So nothing here, it is called distributed termination.
                              -- See P136 of UCS
      (just P') → just (P' ∥⇘ cs ¿ dec ⇙ Q)
  )

... | vis fP | vis fQ = vis (λ at x →
  case dec at of λ where
    -- Event IN cs: both must synchronize
    (yes _) → case (fP at x , fQ at x) of λ where
        (just P' , just Q') → just (P' ∥⇘ cs ¿ dec ⇙ Q')  -- both accept
        (_     ,    _)      → nothing                      -- either refuses → refuse

    -- Event NOT in cs: interleave (nondeterministic choice of who moves)
    (no _) → case (fP at x , fQ at x) of λ where
        (nothing  ,  nothing)    → nothing
        (just P' , nothing)    → just (P' ∥⇘ cs ¿ dec ⇙ Q)   -- only P moves
        (nothing , just Q')  → just (P  ∥⇘ cs ¿ dec ⇙ Q')  -- only Q moves
        (just P' , just Q')  → just ((P' ∥⇘ cs ¿ dec ⇙ Q) ⊓ (P ∥⇘ cs ¿ dec ⇙ Q'))
   )

... | vis fP | inv fQ = inv (λ ai a → -- ∥-dist
    case fQ ai a of λ where
      nothing  → nothing
      (just Q') → just (P ∥⇘ cs ¿ dec ⇙ Q'))

... | inv fP | ret s = inv (λ ai a → -- ∥-dist 
    case fP ai a of λ where
      nothing  → nothing
      (just P') → just (P' ∥⇘ cs ¿ dec ⇙ Q))
    
... | inv fP | vis fQ = inv (λ ai a → -- ∥-dist
    case fP ai a of λ where
      nothing  → nothing
      (just P') → just (P' ∥⇘ cs ¿ dec ⇙ Q))

... | inv fP | inv fQ = inv mergeInv
  where
    mergeInv : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) (R × S)))
    mergeInv (.(AP × AQ) , pair {AP} {AQ} iP iQ) (aP , aQ) =
      case fP (AP , iP) aP , fQ (AQ , iQ) aQ of λ where
        (just P' , just Q') → just (P' ∥⇘ cs ¿ dec ⇙ Q')
        (just P' , nothing) → just (P'  ∥⇘ cs ¿ dec ⇙ Q)  -- Q done, P steps
        (nothing , just Q') → just (P  ∥⇘ cs ¿ dec ⇙ Q')  -- P done, Q steps
        (nothing , nothing) → nothing
    mergeInv (A , base i) a = nothing            -- non-pair index: blocked
    mergeInv (_ , fin) a = nothing            -- non-pair index: blocked
    
-------------------------------------------------------------------------------------
-- Interleave
{-# NON_TERMINATING #-}
_⦀_ :              -- C-x 8 RET and then 2980 to type ⦀
  ∀ {ℓi ℓr ℓs} {I : Set ℓ → Set ℓi} {R : Set ℓr} {S : Set ℓs} -- → {{ DecEq R }}
  → ITree E (ExtI I) R
  → ITree E (ExtI I) S
  → ITree E (ExtI I) (R × S)
force (_⦀_ {I = I} {R = R} {S = S} P Q) with P .force | Q .force

... | sil P' | _  = sil (P' ⦀ Q)

... | _ | sil Q'  = sil (P ⦀ Q')

... | √ r | √ s = √ (r , s)

... | √ r | vis fQ = vis (λ at x →
  case fQ at x of λ where
    nothing → nothing         
    (just Q') → just (P ⦀ Q')
  )

... | ret r | inv fQ = inv (λ ai a →
  case fQ ai a of λ where
    nothing → nothing         
    (just Q') → just (P ⦀ Q')
  ) 

... | vis fP | √ s = vis (λ at x →
    case fP at x of λ where
    nothing → nothing
    (just P') → just (P' ⦀ Q)
  )
  
... | vis fP | vis fQ = vis (λ at x →
    case (fP at x , fQ at x) of λ where
        (nothing  ,  nothing)    → nothing
        (just P' , nothing)    → just (P' ⦀ Q)   -- only P moves
        (nothing , just Q')  → just (P  ⦀ Q')  -- only Q moves
        (just P' , just Q')  → just ((P' ⦀ Q) ⊓ (P ⦀ Q'))
   )

... | vis fP | inv fQ = inv (λ ai a →
  case fQ ai a of λ where
    nothing → nothing         
    (just Q') → just (P ⦀ Q')
  ) 

... | inv fP | ret s = inv (λ ai a →
  case fP ai a of λ where
    nothing → nothing         
    (just P') → just (P' ⦀ Q)
  ) 

... | inv fP | vis fQ = inv (λ ai a →
  case fP ai a of λ where
    nothing → nothing         
    (just P') → just (P' ⦀ Q)
  ) 

... | inv fP | inv fQ = inv mergeInv
  where
    mergeInv : (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) (R × S)))
    mergeInv (.(AP × AQ) , pair {AP} {AQ} iP iQ) (aP , aQ) =
      case fP (AP , iP) aP , fQ (AQ , iQ) aQ of λ where
        (just P' , just Q') → just (P' ⦀ Q')
        (just P' , nothing) → just (P' ⦀ Q)  -- Q done, P steps
        (nothing , just Q') → just (P ⦀ Q')  -- P done, Q steps
        (nothing , nothing) → nothing
    mergeInv (A , base i) a = nothing            -- non-pair index: blocked
    mergeInv (_ , fin) a = nothing            -- non-pair index: blocked

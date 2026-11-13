{-# OPTIONS --guardedness #-}

-- Alphabet-polymorphic output inversion and firing shared by replay bridges.
-- Checked with command-line --safe, like the PTree-importing bridge modules.
module Cardano_network.Replay.LeiosFetchOutParts where

open import Data.Empty using (⊥-elim)
open import Data.Maybe using (just)
open import Data.Maybe.Properties using (just-injective)
open import Data.Product using (_×_; _,_)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym)
open import Class.DecEq using (DecEq; _≟_)
open import Process_Trees using (PTree; ExtI; AnyTypes)

-- a single output fires only its own value and continues with its tree (any alphabet)
module OutInv {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
  open import CSP.Operators E-≟ using (Output)
  import Semantics.LTS {E = E} {I = ExtI E} as L

  -- the output inversion
  out-ev : ∀ {ℓr} {R : Set ℓr} {B : Set ℓ} ⦃ _ : DecEq B ⦄ {ce : E B} {v : B} {P : PTree E (ExtI E) R}
             {x : L.Event} {t′ : PTree E (ExtI E) R}
         → Output ce v P L.─[ L.ev (L.evl x) ]─► t′ → x ≡ L.evLabel B ce v × t′ ≡ P
  out-ev {B = B} {ce = ce} {v = v} (L.sVis {at = A , e} {a = a} refl br) with E-≟ (B , ce) (A , e)
  ... | no _ = case br of λ ()
  ... | yes refl with a ≟ v
  ...   | yes refl = refl , sym (just-injective br)
  ...   | no _     = case br of λ ()

-- a channel or value compared with itself is equal, in any alphabet
module Fire {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
  open import CSP.Operators E-≟ using (Prefix; Prefix-cont; Output; Output-cont)
  import Semantics.LTS {E = E} {I = ExtI E} as L

  -- a prefix's offer map accepts every value on its own channel
  pfx-br : ∀ {ℓr} {R : Set ℓr} {B : Set ℓ} (ce : E B) (P : B → PTree E (ExtI E) R) (a : B)
         → Prefix-cont ce P (B , ce) a ≡ just (P a)
  pfx-br {B = B} ce P a with E-≟ (B , ce) (B , ce)
  ... | yes refl = refl
  ... | no ¬p    = ⊥-elim (¬p refl)

  -- an output's offer map accepts its own value (the DecEq is fixed by the tree)
  out-br : ∀ {ℓr} {R : Set ℓr} {B : Set ℓ} {d : DecEq B} (ce : E B) (v : B) (P : PTree E (ExtI E) R)
         → Output-cont ⦃ d ⦄ ce v P (B , ce) v ≡ just P
  out-br {B = B} {d} ce v P with E-≟ (B , ce) (B , ce)
  ... | no ¬p    = ⊥-elim (¬p refl)
  ... | yes refl with DecEq._≟_ d v v
  ...   | yes _  = refl
  ...   | no ¬p  = ⊥-elim (¬p refl)

  -- a prefix fires any value
  pfx-fire : ∀ {ℓr} {R : Set ℓr} {B : Set ℓ} {ce : E B} {P : B → PTree E (ExtI E) R} {a : B}
           → Prefix ce P L.─[ L.ev (L.evl (L.evLabel B ce a)) ]─► P a
  pfx-fire {ce = ce} {P} {a} = L.sVis refl (pfx-br ce P a)

  -- an output fires its own value
  out-fire : ∀ {ℓr} {R : Set ℓr} {B : Set ℓ} {d : DecEq B} {ce : E B} {v : B} {P : PTree E (ExtI E) R}
           → Output ⦃ d ⦄ ce v P L.─[ L.ev (L.evl (L.evLabel B ce v)) ]─► P
  out-fire {d = d} {ce} {v} {P} = L.sVis refl (out-br {d = d} ce v P)

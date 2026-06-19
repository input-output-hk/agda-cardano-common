{-# OPTIONS --guardedness #-}

-- Sanity checks (reduction / refl-style) for the pure-react renaming operator.
-- Mirrors CSP.Examples.RenameSanity (old vis/ndbr/mix) on the react layer; the
-- operator is productive, so we observe `force (P ⟦…⟧)` directly and read the
-- offered continuation out of the `react` node's visible part.

open import Level using (Lift) renaming (zero to lzero; suc to lsuc)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Data.List using (List; []; _∷_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Examples.RenameSanity where
open PTree

-- Four simple events, each carrying ⊤ (so a visible step can fire them).
data Ev : Set → Set where
  evA evA′ evB evC : Ev ⊤

Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ (_ , evA)  (_ , evA)  = yes refl
Ev-≟ (_ , evA′) (_ , evA′) = yes refl
Ev-≟ (_ , evB)  (_ , evB)  = yes refl
Ev-≟ (_ , evC)  (_ , evC)  = yes refl
Ev-≟ (_ , evA)  (_ , evA′) = no λ ()
Ev-≟ (_ , evA)  (_ , evB)  = no λ ()
Ev-≟ (_ , evA)  (_ , evC)  = no λ ()
Ev-≟ (_ , evA′) (_ , evA)  = no λ ()
Ev-≟ (_ , evA′) (_ , evB)  = no λ ()
Ev-≟ (_ , evA′) (_ , evC)  = no λ ()
Ev-≟ (_ , evB)  (_ , evA)  = no λ ()
Ev-≟ (_ , evB)  (_ , evA′) = no λ ()
Ev-≟ (_ , evB)  (_ , evC)  = no λ ()
Ev-≟ (_ , evC)  (_ , evA)  = no λ ()
Ev-≟ (_ , evC)  (_ , evA′) = no λ ()
Ev-≟ (_ , evC)  (_ , evB)  = no λ ()

open import CSP.Operators Ev-≟
open import CSP.Rename {E₁ = Ev} {E₂ = Ev} (λ e → e) (λ e → just e) (λ _ → refl)

Rr : Set
Rr = Poly.⊤ {lzero}

instance
  DecEq-Rr : DecEq Rr
  DecEq-Rr = record { _≟_ = λ _ _ → yes refl }

⊥₁ : Set₁
⊥₁ = Lift (lsuc lzero) ⊥

Stop⊤ : PTree Ev (ExtI Ev) Rr
Stop⊤ = Stop

Skip⊤ : PTree Ev (ExtI Ev) Rr
Skip⊤ = Skip

-- read the visible continuation out of a node (the react vis-part)
visCont : NodeKind Ev (ExtI Ev) Rr
        → (bt : AnyTypes Ev) → proj₁ bt → Maybe (PTree Ev (ExtI Ev) Rr)
visCont (react v _) = v
visCont _          = λ _ _ → nothing

ceA : ConcEvent₁
ceA = ((⊤ , evA) , tt)

------------------------------------------------------------------------
-- Check 1: (evA → Stop) renamed by evA ↦ evB offers evB and drops evA.
------------------------------------------------------------------------

R₁ : ConcEvent₁ → ConcEvent₂ → Set₁
R₁ ce ((_ , evB) , _) = ce ≡ ceA
R₁ _  _               = ⊥₁

preimg₁ : (bt : AnyTypes Ev) (b : proj₁ bt)
        → List (Σ[ at ∈ AnyTypes Ev ] Σ[ a ∈ proj₁ at ] R₁ (at , a) (bt , b))
preimg₁ (_ , evB)  _ = ((⊤ , evA) , tt , refl) ∷ []
preimg₁ (_ , evA)  _ = []
preimg₁ (_ , evA′) _ = []
preimg₁ (_ , evC)  _ = []

P₁R : PTree Ev (ExtI Ev) Rr
P₁R = (evA ⟶₀ Stop⊤) ⟦ R₁ ¿ preimg₁ ⟧

check₁-B : visCont (force P₁R) (⊤ , evB) tt ≡ just (Stop⊤ ⟦ R₁ ¿ preimg₁ ⟧)
check₁-B = refl

check₁-A : visCont (force P₁R) (⊤ , evA) tt ≡ nothing
check₁-A = refl

------------------------------------------------------------------------
-- Check 2: fan-in.  (evA → Stop) □ (evA′ → Skip) under evA,evA′ ↦ evB
-- offers evB as the internal choice (fan-in) of the two renamed sources.
------------------------------------------------------------------------

R₂ : ConcEvent₁ → ConcEvent₂ → Set₁
R₂ ce ((_ , evB) , _) = (ce ≡ ((⊤ , evA) , tt)) ⊎ (ce ≡ ((⊤ , evA′) , tt))
R₂ _  _               = ⊥₁

preimg₂ : (bt : AnyTypes Ev) (b : proj₁ bt)
        → List (Σ[ at ∈ AnyTypes Ev ] Σ[ a ∈ proj₁ at ] R₂ (at , a) (bt , b))
preimg₂ (_ , evB)  _ = ((⊤ , evA)  , tt , inj₁ refl)
                     ∷ ((⊤ , evA′) , tt , inj₂ refl)
                     ∷ []
preimg₂ (_ , evA)  _ = []
preimg₂ (_ , evA′) _ = []
preimg₂ (_ , evC)  _ = []

P₂R : PTree Ev (ExtI Ev) Rr
P₂R = ((evA ⟶₀ Stop⊤) □ (evA′ ⟶₀ Skip⊤)) ⟦ R₂ ¿ preimg₂ ⟧

check₂-fan-in : visCont (force P₂R) (⊤ , evB) tt
              ≡ rnFan R₂ preimg₂ (Stop⊤ ∷ Skip⊤ ∷ [])
check₂-fan-in = refl

check₂-A-gone : visCont (force P₂R) (⊤ , evA) tt ≡ nothing
check₂-A-gone = refl

------------------------------------------------------------------------
-- Check 3: fan-out.  (evA → Stop) under evA ↦ evB and evA ↦ evC offers both.
------------------------------------------------------------------------

R₃ : ConcEvent₁ → ConcEvent₂ → Set₁
R₃ ce ((_ , evB) , _) = ce ≡ ((⊤ , evA) , tt)
R₃ ce ((_ , evC) , _) = ce ≡ ((⊤ , evA) , tt)
R₃ _  _               = ⊥₁

preimg₃ : (bt : AnyTypes Ev) (b : proj₁ bt)
        → List (Σ[ at ∈ AnyTypes Ev ] Σ[ a ∈ proj₁ at ] R₃ (at , a) (bt , b))
preimg₃ (_ , evB)  _ = ((⊤ , evA) , tt , refl) ∷ []
preimg₃ (_ , evC)  _ = ((⊤ , evA) , tt , refl) ∷ []
preimg₃ (_ , evA)  _ = []
preimg₃ (_ , evA′) _ = []

P₃R : PTree Ev (ExtI Ev) Rr
P₃R = (evA ⟶₀ Stop⊤) ⟦ R₃ ¿ preimg₃ ⟧

check₃-B : visCont (force P₃R) (⊤ , evB) tt ≡ just (Stop⊤ ⟦ R₃ ¿ preimg₃ ⟧)
check₃-B = refl

check₃-C : visCont (force P₃R) (⊤ , evC) tt ≡ just (Stop⊤ ⟦ R₃ ¿ preimg₃ ⟧)
check₃-C = refl

check₃-A-gone : visCont (force P₃R) (⊤ , evA) tt ≡ nothing
check₃-A-gone = refl

------------------------------------------------------------------------
-- Check 4: renameInv exercises invRel / invPreimg (the inverse-based wrapper).
------------------------------------------------------------------------

inv₁ : (bt : AnyTypes Ev) → proj₁ bt → Maybe ConcEvent₁
inv₁ (_ , evB) _ = just ceA
inv₁ _         _ = nothing

P-invR : PTree Ev (ExtI Ev) Rr
P-invR = renameInv (evA ⟶₀ Stop⊤) inv₁

check-inv-B : visCont (force P-invR) (⊤ , evB) tt
            ≡ just (Stop⊤ ⟦ invRel inv₁ ¿ invPreimg inv₁ ⟧)
check-inv-B = refl

check-inv-A : visCont (force P-invR) (⊤ , evA) tt ≡ nothing
check-inv-A = refl

------------------------------------------------------------------------
-- Check 5: genuine E₁ ≠ E₂ via distinct alphabets Ev₁, Ev₂ and injective ι₁₂.
------------------------------------------------------------------------

data Ev₁ : Set → Set where  a₁ b₁ : Ev₁ ⊤
data Ev₂ : Set → Set where  a₂ b₂ : Ev₂ ⊤

ι₁₂ : ∀ {A} → Ev₁ A → Ev₂ A
ι₁₂ a₁ = a₂
ι₁₂ b₁ = b₂

ι₁₂⁻¹ : ∀ {A} → Ev₂ A → Maybe (Ev₁ A)
ι₁₂⁻¹ a₂ = just a₁
ι₁₂⁻¹ b₂ = just b₁

ι₁₂-linv : ∀ {A} (e : Ev₁ A) → ι₁₂⁻¹ (ι₁₂ e) ≡ just e
ι₁₂-linv a₁ = refl
ι₁₂-linv b₁ = refl

Ev₁-≟ : (x y : AnyTypes Ev₁) → Dec (x ≡ y)
Ev₁-≟ (_ , a₁) (_ , a₁) = yes refl
Ev₁-≟ (_ , b₁) (_ , b₁) = yes refl
Ev₁-≟ (_ , a₁) (_ , b₁) = no λ ()
Ev₁-≟ (_ , b₁) (_ , a₁) = no λ ()

import CSP.Operators {E = Ev₁} as Ops₁
module Ops₁′ = Ops₁ Ev₁-≟
import CSP.Rename {E₁ = Ev₁} {E₂ = Ev₂} ι₁₂ ι₁₂⁻¹ ι₁₂-linv as Ren₁₂

Stop₁ : PTree Ev₁ (ExtI Ev₁) Rr
Stop₁ = Ops₁′.Stop

visCont₂ : NodeKind Ev₂ (ExtI Ev₂) Rr
         → (bt : AnyTypes Ev₂) → proj₁ bt → Maybe (PTree Ev₂ (ExtI Ev₂) Rr)
visCont₂ (react v _) = v
visCont₂ _          = λ _ _ → nothing

R₁₂ : Ren₁₂.ConcEvent₁ → Ren₁₂.ConcEvent₂ → Set₁
R₁₂ ce ((_ , a₂) , _) = ce ≡ ((⊤ , a₁) , tt)
R₁₂ _  _              = ⊥₁

preimg₁₂ : (bt : AnyTypes Ev₂) (b : proj₁ bt)
         → List (Σ[ at ∈ AnyTypes Ev₁ ] Σ[ a ∈ proj₁ at ] R₁₂ (at , a) (bt , b))
preimg₁₂ (_ , a₂) _ = ((⊤ , a₁) , tt , refl) ∷ []
preimg₁₂ (_ , b₂) _ = []

P₁₂R : PTree Ev₂ (ExtI Ev₂) Rr
P₁₂R = (Ops₁′.Prefix₀ a₁ Stop₁) Ren₁₂.⟦ R₁₂ ¿ preimg₁₂ ⟧

check-E₁₂-a : visCont₂ (force P₁₂R) (⊤ , a₂) tt
            ≡ just (Stop₁ Ren₁₂.⟦ R₁₂ ¿ preimg₁₂ ⟧)
check-E₁₂-a = refl

check-E₁₂-b : visCont₂ (force P₁₂R) (⊤ , b₂) tt ≡ nothing
check-E₁₂-b = refl

-- ext-linv round-trip on a sample internal `base` index (post-hide path wired)
check-ext-linv : Ren₁₂.extBwd (Ren₁₂.extFwd (base a₁)) ≡ just (base a₁)
check-ext-linv = refl

-- renameMap: functional injective relabel via ι (a₁ ↦ a₂)
PmapR : PTree Ev₂ (ExtI Ev₂) Rr
PmapR = Ren₁₂.renameMap (Ops₁′.Prefix₀ a₁ Stop₁)

check-renameMap : visCont₂ (force PmapR) (⊤ , a₂) tt
                ≡ just (Ren₁₂.renameMap Stop₁)
check-renameMap = refl

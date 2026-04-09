{-
  This module defines the relations between various different equivalence relations
-}

{-# OPTIONS --guardedness #-}

-- open import Agda.Builtin.Nat
-- open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
-- open import Data.Fin using (Fin; remQuot) renaming (zero to fzero; suc to fsuc)
-- open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Maybe.Properties using (just-injective)
open import Data.Empty using (⊥; ⊥-elim)
-- open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; Σ-syntax; ∃-syntax; ∃₂)
-- -- open import Relation.Unary
open import Function using (case_of_)
-- import Relation.Binary.PropositionalEquality as Eq
-- open Eq using (_≡_; refl)
open import Relation.Binary                using (Rel)
-- -- open import Relation.Binary.Definitions using (DecidableEquality)
-- open import Class.DecEq
open import Level using (Level; 0ℓ)
-- open import Relation.Nullary using (Dec; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
-- open import Data.Bool using (Bool; true; false; if_then_else_)

-- open import Data.List using (List; _++_; _∷_; []; length; reverse; map; foldr; downFrom)
-- open import Data.List.Relation.Unary.All using (All; []; _∷_)
-- import  Data.List.Relation.Unary.Any using (Any; here;there)
-- import Data.List.Membership.Propositional using (_∈_)
-- import Data.List.Properties using (reverse-++-commute; map-compose; map-++-commute; foldr-++; map-is-foldr)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym; trans; refl; inspect; [_]; cong)
open import Data.Maybe.Relation.Binary.Pointwise using (Pointwise) renaming (just to pw-just; nothing to pw-nothing)

open import Interaction_Trees
open import ITree_Relations.LTS using (Label; ev; τ; _─[_]─►_; sSil; sNdbr; τ^-ndbr;
  _─[τ^_]─►_; τ^-zero; τ^-suc; _─[τ*]─►_; τ*-zero; τ*-step)
open import ITree_Relations.Equivalence_Rel renaming (_≈_ to _≈ᵉ_)
open import ITree_Relations.StrongBisim renaming (_≈_ to _≈ˢ_)
open import ITree_Relations.WeakBisim renaming (_≈_ to _≈ʷ_)
open import ITree_Relations.DRWeakBisim renaming (_≈_ to _≈ᵈ_)
open import ITree_Relations.Divergence

module ITree_Relations.Relations 
  where
open ITree

variable
  ℓ ℓe ℓi ℓr ℓ≡ ℓ≈ : Level
  E : Set ℓ → Set ℓe
  I : Set ℓ → Set ℓi
  R : Set ℓr
  RetRel : Rel R ℓ≡

pw-map : ∀ {ℓ₁ ℓ₂} {R1 : Rel (ITree E I R) ℓ₁} {R2 : Rel (ITree E I R) ℓ₂}
       → (∀ {t t'} → R1 t t' → R2 t t')
       → ∀ {m m'} → Pointwise R1 m m' → Pointwise R2 m m'
pw-map f (Pointwise.just r)  = Pointwise.just (f r)
pw-map f Pointwise.nothing   = Pointwise.nothing

{-# NON_TERMINATING #-}
equiv→sbisim : ∀ {t t' : ITree E I R}
                → t ≈ᵉ t'
                → t ≈ˢ t'
equiv→sbisim eq .Sbisim.step = go (eq .SEquiv.step)
  where
    go : ∀ {n₁ n₂}
       → EqNodeKindF _≡_ (SEquiv _≡_) n₁ n₂
       → SNodeKindF _≡_ (Sbisim _≡_) n₁ n₂
    go (EqNodeKindF.retF r)   = SNodeKindF.retF r
    go (EqNodeKindF.silF t)   = SNodeKindF.silF (equiv→sbisim t)
    go (EqNodeKindF.visF h)   = SNodeKindF.visF (λ at a → pw-map equiv→sbisim (h at a))
    go (EqNodeKindF.ndbrF {f₁} {f₂} eq-inx eq-a h) = SNodeKindF.ndbrF fwd bwd
      where
        fwd : ∀ {t₁} → Image f₁ t₁ → Σ _ (λ t₂ → Image f₂ t₂ × Sbisim _≡_ t₁ t₂)
        -- Add inspect (f₂ i) a to the with-clause
        fwd {t₁} (i , a , eq) with f₁ i a | f₂ i a | inspect (f₂ i) a | h i a
        ... | nothing  | nothing  | _       | pw-nothing  = ⊥-elim (case eq of λ ())
        ... | just t₁' | just t₂' | [ eq₂ ] | pw-just rel = 
              t₂' , (i , a , eq₂) , -- <-- Use eq₂ instead of refl!
              equiv→sbisim (subst (λ t → SEquiv _≡_ t t₂') (just-injective eq) rel)

        bwd : ∀ {t₂} → Image f₂ t₂ → Σ _ (λ t₁ → Image f₁ t₁ × Sbisim _≡_ t₁ t₂)
        -- Add inspect (f₁ i) a to the with-clause for the backward direction
        bwd {t₂} (i , a , eq) with f₁ i a | inspect (f₁ i) a | f₂ i a | h i a
        ... | nothing  | _       | nothing  | pw-nothing  = ⊥-elim (case eq of λ ())
        ... | just t₁' | [ eq₁ ] | just t₂' | pw-just rel = 
              t₁' , (i , a , eq₁) , -- <-- Use eq₁ instead of refl!
              equiv→sbisim (subst (SEquiv _≡_ t₁') (just-injective eq) rel)

{-
private
  -- Extract the continuation from a silF proof
  silF-ndbr : ∀ {t₁} {n₂}
           → SNodeKindF _≡_ (Sbisim _≡_) (sil t₁) n₂
           → Σ[ t₂ ∈ ITree E I R ] (n₂ ≡ sil t₂ × Sbisim _≡_ t₁ t₂)
  silF-ndbr (SNodeKindF.silF rel) = _ , refl , rel

  -- Extract the ndbrF forward direction when left side is ndbr
  ndbrF-fwd : ∀ {f₁ f₂}
           → SNodeKindF _≡_ (Sbisim _≡_) (ndbr f₁) (ndbr f₂)
           → ∀ {t₁} → Image f₁ t₁
           → Σ[ t₂ ∈ ITree E I R ] (Image f₂ t₂ × Sbisim _≡_ t₁ t₂)
  ndbrF-fwd (SNodeKindF.ndbrF fwd _) = fwd
{-  
{-# NON_TERMINATING #-}
sbisim→divergent : ∀ {t₁ t₂ : ITree E I R}
                 → Sbisim _≡_ t₁ t₂ → Divergent t₁ → Divergent t₂
sbisim→divergent p d with d .Divergent.step
... | sSil eq =
      let step'             = subst (λ n → SNodeKindF _≡_ (Sbisim _≡_) n (ITree.force _))
                                    eq (p .Sbisim.step)
          (t₂' , eq₂ , rel) = silF-ndbr step'
      in  record { next    = t₂'
                 ; step    = sSil eq₂       -- ← eq₂ : ITree.force t₂ ≡ sil t₂'
                 ; diverge = sbisim→divergent rel (d .Divergent.diverge) }
... | sNdbr {a = a} eq =
      let step'              = subst (λ n → SNodeKindF _≡_ (Sbisim _≡_) n (ITree.force _))
                                     eq (p .Sbisim.step)
          (t₂' , img , rel)  = ndbrF-fwd step' (_ , a , eq)
      in  record { next    = t₂'
                 ; step    = sNdbr (proj₂ (proj₂ img))
                 ; diverge = sbisim→divergent rel (d .Divergent.diverge) }
-}
{-# NON_TERMINATING #-}
sbisim→divergent : ∀ {t₁ t₂ : ITree E I R}
                 → Sbisim _≡_ t₁ t₂ → Divergent t₁ → Divergent t₂
sbisim→divergent {t₁ = t₁} {t₂ = t₂} p d with d .Divergent.step
-- sil case: eq : ITree.force t₁ ≡ sil t'  — a NodeKind equality, use it in subst
... | sSil eq =
      let step'              = subst (λ n → SNodeKindF _≡_ (Sbisim _≡_) n (ITree.force _))
                                     eq (p .Sbisim.step)
          (t₂' , eq₂ , rel)  = silF-ndbr step'
      in  record { next    = t₂'
                 ; step    = sSil eq₂
                 ; diverge = sbisim→divergent rel (d .Divergent.diverge) }

... | sNdbr {f = f₁} {A = A} {i = i} {a = a} ndbrEq
    with ITree.force t₁
... | ndbr f₁
    with ITree.force t₂ in eq₂
... | ndbr f₂ =
  let
    step₀ = p .Sbisim.step

    -- 🔑 rewrite RHS index
    step₁ : SNodeKindF _≡_ (Sbisim _≡_) (ndbr f₁) (ndbr f₂)
    step₁ = subst (λ n → SNodeKindF _≡_ (Sbisim _≡_) (ndbr f₁) n) eq₂ step₀
  in
    case step₁ of λ where
      ndbrF _ _ fwd bwd →
        let
          (t₂' , (img₂ , rel)) =
            fwd ((A , i) , a , ndbrEq)
        in
        record
          { next    = t₂'
          ; step    = sNdbr (proj₂ (proj₂ img₂))
          ; diverge = sbisim→divergent rel (d .Divergent.diverge)
          }
-}

{-
... | sNdbr {f = f₁} {A = A} {i = i} {a = a} ndbrEq
    with ITree.force t₁
... | ndbr f₁ =
  let
    step' : SNodeKindF _≡_ (Sbisim _≡_) (ndbr f₁) (ITree.force t₂)
    step' = p .Sbisim.step

    -- 🔑 FIRST: ndbrert the RHS shape
    (f₂ , eq₂ , step'') = ndbrF-ndbr step'

    -- now eq₂ : force t₂ ≡ ndbr f₂
    -- and step'' : the refined structure

    -- 🔑 THEN: use forward rule
    (t₂' , img , rel) =
      ndbrF-fwd
        (subst
          (λ n → SNodeKindF _≡_ (Sbisim _≡_) (ndbr f₁) n)
          eq₂
          step')
        ((A , i) , a , ndbrEq)

  in
  record
    { next    = t₂'
    ; step    = sNdbr (proj₂ (proj₂ img))
    ; diverge = sbisim→divergent rel (d .Divergent.diverge)
    }                 
-}
{-
{-# NON_TERMINATING #-}
sbisim<drwbisim : ∀ {t t' : ITree E I R}
                → t ≈ˢ t'
                → t ≈ᵈ t'
sbisim<drwbisim p .DRWbisim.divL = sbisim→divergent p
sbisim<drwbisim p .DRWbisim.divR = sbisim→divergent (SbisimEquiv.sbisim-sym p)
sbisim<drwbisim p .DRWbisim.step = go (p .Sbisim.step)
  where
    go : ∀ {n₁ n₂}
       → SNodeKindF _≡_ (Sbisim _≡_) n₁ n₂
       → Divergent _ ⊎ Divergent _ ⊎ ∃₂ λ t₁' t₂'
           → (_ ─[τ*]─► t₁') × (_ ─[τ*]─► t₂')
           × DRWNodeKindF _≡_ (DRWbisim _≡_) (ITree.force t₁') (ITree.force t₂')
    go (SNodeKindF.retF r) =
      inj₂ (inj₂ (_ , _ , τ*-zero , τ*-zero , DRWNodeKindF.retF r))
    -- sil: take one τ step on each side then recurse
    go (SNodeKindF.silF rel) with (sbisim<drwbisim rel) .DRWbisim.step
    ... | inj₁ d =
          inj₁ (step-diverges refl d)
    ... | inj₂ (inj₁ d) =
          inj₂ (inj₁ (step-diverges refl d))
    ... | inj₂ (inj₂ (t₁' , t₂' , red₁ , red₂ , obs)) =
          inj₂ (inj₂ (t₁' , t₂' , refl τ*-step red₁ , refl τ*-step red₂ , obs))
    go (SNodeKindF.visF h) =
      inj₂ (inj₂ (_ , _ , τ*-zero , τ*-zero ,
        DRWNodeKindF.visF (λ at a → pw-map sbisim<drwbisim (h at a))))
    go (SNodeKindF.ndbrF fwd bwd) =
      inj₂ (inj₂ (_ , _ , τ*-zero , τ*-zero ,
        DRWNodeKindF.ndbrF
          (λ img → let (t₂ , img₂ , rel) = fwd img in t₂ , img₂ , sbisim<drwbisim rel)
          (λ img → let (t₁ , img₁ , rel) = bwd img in t₁ , img₁ , sbisim<drwbisim rel)))
-}

{-
mutual
  sbisim<drwbisim : ∀ {t t' : ITree E I R}
                  → t ≈ˢ t'
                  → t ≈ᵈ t'
  DRWbisim.step (sbisim<drwbisim {t} {t'} s) = 
    -- Inject into the observable agreement branch (inj₂ ∘ inj₂).
    -- We use zero-step τ transitions for both sides.
    -- Note: Replace `τ*-refl` with your library's actual zero-step constructor (e.g., `nil`, `ε`, or `refl`).
    inj₂ (inj₂ (t , t' , τ*-zero , τ*-zero , go-node (Sbisim.step s)))

  -- Map the divergence fields using divergence preservation lemmas
  DRWbisim.divL (sbisim<drwbisim s) div-t  = sbisim-divL s div-t
  DRWbisim.divR (sbisim<drwbisim s) div-t' = sbisim-divR s div-t'

  go-node : ∀ {n₁ n₂}
          → SNodeKindF RetRel (_≈ˢ_) n₁ n₂
          → DRWNodeKindF RetRel (_≈ᵈ_) n₁ n₂
  go-node (SNodeKindF.retF r) = DRWNodeKindF.retF r
  go-node (SNodeKindF.silF s) = DRWNodeKindF.silF (sbisim<drwbisim s)
  go-node (SNodeKindF.visF h) = DRWNodeKindF.visF (λ at a → pw-map sbisim<drwbisim (h at a))
  
  -- For ndbrF, we unpack the Sigma types returned by the strong bisimulation's fwd/bwd 
  -- and wrap the resulting strong equivalence in our mutual `sbisim<drwbisim`.
  go-node (SNodeKindF.ndbrF fwd bwd) = DRWNodeKindF.ndbrF fwd' bwd'
    where
      fwd' : ∀ {t₁} → Image _ t₁ → Σ _ (λ t₂ → Image _ t₂ × t₁ ≈ᵈ t₂)
      fwd' img₁ with fwd img₁
      ... | t₂ , img₂ , s-eq = t₂ , img₂ , sbisim<drwbisim s-eq

      bwd' : ∀ {t₂} → Image _ t₂ → Σ _ (λ t₁ → Image _ t₁ × t₁ ≈ᵈ t₂)
      bwd' img₂ with bwd img₂
      ... | t₁ , img₁ , s-eq = t₁ , img₁ , sbisim<drwbisim s-eq

  sbisim-divL : ∀ {t t' : ITree E I R}
              → t ≈ˢ t'
              → Divergent t
              → Divergent t'
  sbisim-divL {t} {t'} s d = helper s d (Divergent.step d)
    where
      -- We extract the transition to unify the node shapes
      helper : ∀ {t₁ t₂} → t₁ ≈ˢ t₂ → (d₁ : Divergent t₁) → t₁ ─[ τ ]─► (Divergent.next d₁) → Divergent t₂
      helper {t₁} {t₂} s₁ d₁ (sSil eq) with ITree.force t₁ | eq | Sbisim.step s₁
      ... | .(sil (Divergent.next d₁)) | refl | SNodeKindF.silF s-next = 
        -- Because the strong bisimulation requires t₂ to also be a `sil` node,
        -- we can simply use your `step-diverges` lemma with `refl` for the right tree.
        step-diverges refl (sbisim-divL s-next (Divergent.diverge d₁))

  sbisim-divR : ∀ {t t' : ITree E I R}
              → t ≈ˢ t'
              → Divergent t'
              → Divergent t
  sbisim-divR {t} {t'} s d' = helper s d' (Divergent.step d')
    where
      -- The right-to-left direction is completely symmetric
      helper : ∀ {t₁ t₂} → t₁ ≈ˢ t₂ → (d₂ : Divergent t₂) → t₂ ─[ τ ]─► (Divergent.next d₂) → Divergent t₁
      helper {t₁} {t₂} s₂ d₂ (sSil eq) with ITree.force t₂ | eq | Sbisim.step s₂
      ... | .(sil (Divergent.next d₂)) | refl | SNodeKindF.silF s-next = 
        step-diverges refl (sbisim-divR s-next (Divergent.diverge d₂))
-}

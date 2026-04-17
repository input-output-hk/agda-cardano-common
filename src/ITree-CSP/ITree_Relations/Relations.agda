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
open import Relation.Binary                using (Rel; IsEquivalence)
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
open import Relation.Binary.PropositionalEquality.Properties using (isEquivalence)
open import Data.Maybe.Relation.Binary.Pointwise using (Pointwise) renaming (just to pw-just; nothing to pw-nothing)
 
open import Interaction_Trees
open import ITree_Relations.LTS using (Event; Event√; Label; ev; τ;
  _─[_]─►_; sRet; sSil; sNdbr; sVis; τ^-ndbr; √-is-ret;
  _─[τ^_]─►_; τ^-zero; τ^-suc; _─[τ*]─►_; τ*-zero; τ*-step;
    _═[_]═►_; weak-τ; weak-ev)
open import ITree_Relations.Equivalence_Rel using (EqNodeKindF; SEquiv; module SEquivEquiv) renaming (_≈_ to _≈ᵉ_)
open import ITree_Relations.StrongBisim renaming (_∼_ to _≈ˢ_)
open import ITree_Relations.StrongBisim using (Sbisim; SSimF)
open import ITree_Relations.WeakBisim renaming (_≈_ to _≈ʷ_)
open import ITree_Relations.DRWeakBisim renaming (_≈_ to _≈ᵈ_)
open import ITree_Relations.Divergence

module ITree_Relations.Relations 
  where
open ITree

-- IsEquivalence for propositional equality (used in SEquivEquiv calls)
≡-equiv : ∀ {a} {A : Set a} → IsEquivalence (_≡_ {A = A})
≡-equiv = isEquivalence

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

-- Helper: wrap a single strong τ step into a weak-τ transition
τ-to-weak-τ : ∀ {t t' : ITree E I R}
            → t ─[ τ ]─► t'
            → t ═[ τ ]═► t'
τ-to-weak-τ step = weak-τ (τ*-step step τ*-zero)

-- Helper: wrap a single strong visible step into a weak-ev transition  
ev-to-weak-ev : ∀ {t t' : ITree E I R} {e : Event√ E R}
             → t ─[ ev e ]─► t'
             → t ═[ ev e ]═► t'
ev-to-weak-ev step = weak-ev τ*-zero step τ*-zero

{-# NON_TERMINATING #-}
-- Lifting: a strong simulation implies a weak simulation (one side)
ssim→drwsim : ∀ (t₁ t₂ : ITree E I R)
            → SSimF _≡_ (DRWbisim _≡_) t₁ t₂
            → DRWSimF _≡_ (DRWbisim _≡_) t₁ t₂
ssim→drwsim t₁ t₂ ssim .DRWSimF.on-ret eq =
    let t₂' , step₂ , _bisim = ssim .SSimF.on-ret (sRet eq)
        eq₂ , _             = √-is-ret step₂
        -- t₂ itself is the stable witness: reach it via zero τ steps
    in  t₂ , _ , weak-τ τ*-zero , eq₂ , refl

ssim→drwsim t₁ t₂ ssim .DRWSimF.on-vis step =
    let t₂' , step' , bisim = ssim .SSimF.on-vis step
    in  t₂' , ev-to-weak-ev step' , bisim

ssim→drwsim t₁ t₂ ssim .DRWSimF.on-tau step =
    let t₂' , step' , bisim = ssim .SSimF.on-tau step
    in  t₂' , τ-to-weak-τ step' , bisim

ssim→drwsim t₁ t₂ ssim .DRWSimF.on-div d =
    divergent-ssim-closed t₁ t₂ ssim d
  where
    divergent-ssim-closed : ∀ (t₁ t₂ : ITree E I R)
                          → SSimF _≡_ (DRWbisim _≡_) t₁ t₂
                          → Divergent t₁ → Divergent t₂
    divergent-ssim-closed t₁ t₂ ssim d =
        let step₁           = d .Divergent.step
            t₂' , step₂ , bisim' = ssim .SSimF.on-tau step₁
        in record
             { step    = step₂
             ; diverge = DRWSimF.on-div (DRWbisim.fwd bisim') (d .Divergent.diverge)
             }

{-# NON_TERMINATING #-}
-- Main theorem: strong bisimulation implies DRW weak bisimulation
sbisim→drwbisim : ∀ {t t' : ITree E I R}
                → t ≈ˢ t'
                → t ≈ᵈ t'
sbisim→drwbisim {t} {t'} bisim = go bisim
  where
    -- Lift SSimF with (Sbisim _≡_) as TreeRel to SSimF with (DRWbisim _≡_) as TreeRel
    lift-ssim : ∀ {t₁ t₂ : ITree E I R}
              → SSimF _≡_ (Sbisim _≡_) t₁ t₂
              → SSimF _≡_ (DRWbisim _≡_) t₁ t₂
    go : ∀ {t t' : ITree E I R} → t ≈ˢ t' → t ≈ᵈ t'
    
    lift-ssim ssim .SSimF.on-ret step =
        let t₂' , step' , sub = ssim .SSimF.on-ret step
        in  t₂' , step' , go sub
    lift-ssim ssim .SSimF.on-vis step =
        let t₂' , step' , sub = ssim .SSimF.on-vis step
        in  t₂' , step' , go sub
    lift-ssim ssim .SSimF.on-tau step =
        let t₂' , step' , sub = ssim .SSimF.on-tau step
        in  t₂' , step' , go sub

    go {t = t} {t' = t'} bisim .DRWbisim.fwd = ssim→drwsim t t' (lift-ssim (bisim .Sbisim.fwd))
    go {t = t} {t' = t'} bisim .DRWbisim.bwd = ssim→drwsim t' t (lift-ssim (bisim .Sbisim.bwd))


{-
mutual

  {-# NON_TERMINATING #-}
  equiv→sbisim : ∀ {t t' : ITree E I R}
                  → t ≈ᵉ t'
                  → t ≈ˢ t'
  equiv→sbisim eq .Sbisim.fwd = mkSim eq
  equiv→sbisim eq .Sbisim.bwd = mkSim (SEquivEquiv.sequiv-sym ≡-equiv eq)
 
  -- mkSim builds a one-sided SSimF from a SEquiv proof.
  mkSim : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          {t₁ t₂ : ITree E I R}
        → t₁ ≈ᵉ t₂
        → SSimF _≡_ (Sbisim _≡_) t₁ t₂
 
  mkSim {t₁ = t₁} {t₂ = t₂} eq .SSimF.on-ret (sRet {x = r} force≡ret)
    with ITree.force t₁ | inspect ITree.force t₁
       | ITree.force t₂ | inspect ITree.force t₂
       | eq .SEquiv.step | force≡ret
  ... | ret r₁ | [ eq₁ ] | ret r₂ | [ eq₂ ] | EqNodeKindF.retF r-rel | refl =
       deadlock
       , sRet (trans eq₂ (cong ret (sym r-rel)))
       , SbisimEquiv.sbisim-refl ≡-equiv deadlock

  -- on-tau/sSil: force≡sil collapses force t₁ to sil t₁'';
  -- force t₂ is matched to sil t₂', giving the right-side τ step as sSil refl.
  mkSim {t₁ = t₁} {t₂ = t₂} eq .SSimF.on-tau (sSil {t = t₁'} force≡sil)
    with ITree.force t₁ | ITree.force t₂ | eq .SEquiv.step | force≡sil
  ... | sil t₁'' | sil t₂' | EqNodeKindF.silF rel | refl = ?
--        t₂' , sSil refl , equiv→sbisim rel
 
  -- on-tau/sNdbr: force≡ndbr collapses force t₁ to ndbr f₁ ...; force t₂ gives f₂.
  -- pw-just rel means Pointwise matched just/just, so we also inspect f₂ i a
  -- to get the equation f₂ i a ≡ just t₂' needed for the right-side sNdbr step.
  mkSim {t₁ = t₁} {t₂ = t₂} eq .SSimF.on-tau
      (sNdbr {f = f₁} {wi = wi} {wa = wa} {prf = prf} {i = i} {a = a} force≡ndbr branch-eq)
    with ITree.force t₁ | ITree.force t₂ | eq .SEquiv.step | force≡ndbr
  ... | ndbr f₁' wi' wa' prf' | ndbr f₂ wi₂ wa₂ prf₂ | EqNodeKindF.ndbrF eq-idx eq-val h | refl
      with h i a | inspect (f₁ i) a | inspect (f₂ i) a
  ... | pw-just rel | [ f₁-eq ] | [ f₂-eq ] =
        _ , sNdbr refl f₂-eq
          , equiv→sbisim (subst (λ t → SEquiv _≡_ t _)
                                 (just-injective (trans (sym f₁-eq) branch-eq))
                                 rel)
  ... | pw-nothing | [ f₁-eq ] | _ =
        ⊥-elim (case trans (sym branch-eq) f₁-eq of λ ())

  -- on-vis/sVis: force≡vis collapses force t₁ to vis f₁; force t₂ gives f₂.
  -- Similarly inspect f₂ at a for the right-side sVis step equation.
  mkSim {t₁ = t₁} {t₂ = t₂} eq .SSimF.on-vis
      (sVis {f = f₁} {at = at} {a = a} force≡vis f-eq)
    with ITree.force t₁ | ITree.force t₂ | eq .SEquiv.step | force≡vis
  ... | vis f₁' | vis f₂ | EqNodeKindF.visF h | refl
      with h at a | inspect (f₁ at) a | inspect (f₂ at) a
  ... | pw-just rel | [ f₁-eq ] | [ f₂-eq ] =
        _ , sVis refl f₂-eq
          , equiv→sbisim (subst (λ t → SEquiv _≡_ t _)
                                 (just-injective (trans (sym f₁-eq) f-eq))
                                 rel)
  ... | pw-nothing | [ f₁-eq ] | _ =
        ⊥-elim (case trans (sym f-eq) f₁-eq of λ ())
        
-}

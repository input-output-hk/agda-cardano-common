{-# OPTIONS --guardedness #-}

-- slide-fuse (FD-direct):  (react V ∅t) ▷ (react ∅v τc)  ≈FD  react V τc,
-- provided the τ-only operand is UNSTABLE (has at least one internal branch).
--
-- "Sliding a stable visible-offer node over an unstable internal-choice node fuses
-- them into one react node."  The left makes ONE extra internal τ (the timeout/slide)
-- to `Q = react ∅v τc`, which then resolves via τc exactly as the fused node does;
-- that leading τ is UNOBSERVABLE, so the two agree on failures and divergences —
-- but NOT on bisimulation (the slide-τ to Q discards V's offers, and no state of the
-- fused node matches Q).  Hence this is proved FD-directly, not via a bisimulation.
--
-- The unstable hypothesis is essential: if τc were everywhere-nothing then Q = STOP,
-- the slide could time out to a stable deadlock, and the left would gain the failure
-- of refusing everything — which the fused (stable, offering V) node does not have.

open import Level using (Level; Lift; lift)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.List using (List; []; _++_)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees

module CSP.Laws.FD.SlideFuse {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Refusals {E = E} {I = ExtI E} using (Refuses)
open import Semantics.Failures  {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; failures)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (failures⊥; divergences; IsDivergence; _≈FD_; _⊑F⊥_; _⊑D_; _⊑FD_)
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges)
open import Semantics.DRImpliesFD {E = E} {I = ExtI E} using (stable-no-τ)

module _ {ℓr} {R : Set ℓr}
         (V  : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         (τc : (i  : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R)))
         (qτ : Σ[ M ∈ PTree E (ExtI E) R ] (ptree (react ∅v τc) ─[ τ ]─► M)) where

  P0 : PTree E (ExtI E) R
  P0 = ptree (react V ∅t)

  Q : PTree E (ExtI E) R
  Q = ptree (react ∅v τc)

  LHSf : PTree E (ExtI E) R
  LHSf = P0 ▷ Q

  RHSf : PTree E (ExtI E) R
  RHSf = ptree (react V τc)

  -----------------------------------------------------------------------------------
  -- step intro / elim and cross-tree conversions
  -----------------------------------------------------------------------------------

  -- the slide always offers the timeout-τ to Q
  LHSf-τ-intro : LHSf ─[ τ ]─► Q
  LHSf-τ-intro = sTau {i = (Lift ℓ (Fin 2) × Lift ℓ (Fin 1)) , pair fin fin}
                      {a = lift fzero , lift fzero} refl refl

  -- the ONLY τ of LHSf is that timeout-τ
  LHSf-τ-elim : {M : PTree E (ExtI E) R} → LHSf ─[ τ ]─► M → M ≡ Q
  LHSf-τ-elim (sSil ())
  LHSf-τ-elim (sTau {i = _ , base _}            refl br) = case br of λ ()
  LHSf-τ-elim (sTau {i = _ , fin}               refl br) = case br of λ ()
  LHSf-τ-elim (sTau {i = _ , pair (base _) _}   refl br) = case br of λ ()
  LHSf-τ-elim (sTau {i = _ , pair (pair _ _) _} refl br) = case br of λ ()
  LHSf-τ-elim (sTau {i = _ , pair fin _} {a = lift fzero           , a} refl br) = sym (just-injective br)
  LHSf-τ-elim (sTau {i = _ , pair fin _} {a = lift (fsuc fzero)    , a} refl br) = case br of λ ()
  LHSf-τ-elim (sTau {i = _ , pair fin _} {a = lift (fsuc (fsuc _)) , a} refl br) = case br of λ ()

  -- Q and RHSf have identical τ-behaviour (same τc)
  cvt-τ-QR : {M : PTree E (ExtI E) R} → Q ─[ τ ]─► M → RHSf ─[ τ ]─► M
  cvt-τ-QR (sSil ())
  cvt-τ-QR (sTau {i = i} {a = a} refl br) = sTau {i = i} {a = a} refl br

  cvt-τ-RQ : {M : PTree E (ExtI E) R} → RHSf ─[ τ ]─► M → Q ─[ τ ]─► M
  cvt-τ-RQ (sSil ())
  cvt-τ-RQ (sTau {i = i} {a = a} refl br) = sTau {i = i} {a = a} refl br

  -- LHSf and RHSf share the visible map V
  cvt-ev-RL : {l : Event√ R} {M : PTree E (ExtI E) R} → RHSf ─[ ev l ]─► M → LHSf ─[ ev l ]─► M
  cvt-ev-RL (sRet ())
  cvt-ev-RL (sVis {at = at} {a = a} refl br) = sVis {at = at} {a = a} refl br

  cvt-ev-LR : {l : Event√ R} {M : PTree E (ExtI E) R} → LHSf ─[ ev l ]─► M → RHSf ─[ ev l ]─► M
  cvt-ev-LR (sRet ())
  cvt-ev-LR (sVis {at = at} {a = a} refl br) = sVis {at = at} {a = a} refl br

  Q-no-ev : {l : Event√ R} {M : PTree E (ExtI E) R} → Q ─[ ev l ]─► M → ⊥
  Q-no-ev (sRet ())
  Q-no-ev (sVis refl ())

  -----------------------------------------------------------------------------------
  -- instability of the three unstable nodes
  -----------------------------------------------------------------------------------

  LHSf-unstable : isStable LHSf → ⊥
  LHSf-unstable st = stable-no-τ st LHSf-τ-intro

  Q-unstable : isStable Q → ⊥
  Q-unstable st = stable-no-τ st (proj₂ qτ)

  RHSf-unstable : isStable RHSf → ⊥
  RHSf-unstable st = stable-no-τ st (cvt-τ-QR (proj₂ qτ))

  -----------------------------------------------------------------------------------
  -- weak-reach correspondences
  -----------------------------------------------------------------------------------

  -- a run of Q is the matching run of RHSf (or the trivial 0-step run staying at Q)
  Q-reach : {s : List (Event√ R)} {W : PTree E (ExtI E) R}
          → Q ⟹⟨ s ⟩ W → (W ≡ Q × s ≡ []) ⊎ (RHSf ⟹⟨ s ⟩ W)
  Q-reach ⟹-refl            = inj₁ (refl , refl)
  Q-reach (⟹-τ step rest)   = inj₂ (⟹-τ (cvt-τ-QR step) rest)
  Q-reach (⟹-ev step rest)  = ⊥-elim (Q-no-ev step)

  -- a run of RHSf is the matching run of LHSf (or the trivial 0-step run at RHSf)
  reach-RL : {s : List (Event√ R)} {W : PTree E (ExtI E) R}
           → RHSf ⟹⟨ s ⟩ W → (W ≡ RHSf × s ≡ []) ⊎ (LHSf ⟹⟨ s ⟩ W)
  reach-RL ⟹-refl           = inj₁ (refl , refl)
  reach-RL (⟹-τ step rest)  = inj₂ (⟹-τ LHSf-τ-intro (⟹-τ (cvt-τ-RQ step) rest))
  reach-RL (⟹-ev step rest) = inj₂ (⟹-ev (cvt-ev-RL step) rest)

  -- a run of LHSf is the matching run of RHSf (or a trivial 0-step run at LHSf / Q)
  reach-LR : {s : List (Event√ R)} {W : PTree E (ExtI E) R}
           → LHSf ⟹⟨ s ⟩ W
           → (W ≡ LHSf × s ≡ []) ⊎ (W ≡ Q × s ≡ []) ⊎ (RHSf ⟹⟨ s ⟩ W)
  reach-LR ⟹-refl           = inj₁ (refl , refl)
  reach-LR (⟹-τ step rest)  with LHSf-τ-elim step
  ... | refl = case Q-reach rest of λ
        { (inj₁ (refl , refl)) → inj₂ (inj₁ (refl , refl))
        ; (inj₂ rr)            → inj₂ (inj₂ rr) }
  reach-LR (⟹-ev step rest) = inj₂ (inj₂ (⟹-ev (cvt-ev-LR step) rest))

  -----------------------------------------------------------------------------------
  -- divergence correspondences
  -----------------------------------------------------------------------------------

  divQ→divR : Diverges Q → Diverges RHSf
  divQ→divR d = record { step = cvt-τ-QR (d .Diverges.step) ; rest = d .Diverges.rest }

  divR→divQ : Diverges RHSf → Diverges Q
  divR→divQ d = record { step = cvt-τ-RQ (d .Diverges.step) ; rest = d .Diverges.rest }

  divQ→divL : Diverges Q → Diverges LHSf
  divQ→divL d = record { step = LHSf-τ-intro ; rest = d }

  divL→divQ : Diverges LHSf → Diverges Q
  divL→divQ d = subst Diverges (LHSf-τ-elim (d .Diverges.step)) (d .Diverges.rest)

  -----------------------------------------------------------------------------------
  -- failures⊥ and divergences refinements (both directions) ⇒ ≈FD
  -----------------------------------------------------------------------------------

  fail-R→L : {s : List (Event√ R)} {B : Event√ R → Set ℓr}
           → failures⊥ RHSf s B → failures⊥ LHSf s B
  fail-R→L (inj₁ (W , reach , ref)) with reach-RL reach
  ... | inj₁ (refl , refl) = ⊥-elim (RHSf-unstable (proj₁ ref))
  ... | inj₂ lreach        = inj₁ (W , lreach , ref)
  fail-R→L (inj₂ record { prefix = pre ; suffix = suf ; split = sp
                        ; witness = w ; reach = rc ; divwit = dw }) with reach-RL rc
  ... | inj₁ (refl , refl) =
        inj₂ (record { prefix = [] ; suffix = suf ; split = sp ; witness = LHSf
                     ; reach = ⟹-refl ; divwit = divQ→divL (divR→divQ dw) })
  ... | inj₂ lreach =
        inj₂ (record { prefix = pre ; suffix = suf ; split = sp ; witness = w
                     ; reach = lreach ; divwit = dw })

  fail-L→R : {s : List (Event√ R)} {B : Event√ R → Set ℓr}
           → failures⊥ LHSf s B → failures⊥ RHSf s B
  fail-L→R (inj₁ (W , reach , ref)) with reach-LR reach
  ... | inj₁ (refl , refl)        = ⊥-elim (LHSf-unstable (proj₁ ref))
  ... | inj₂ (inj₁ (refl , refl)) = ⊥-elim (Q-unstable (proj₁ ref))
  ... | inj₂ (inj₂ rreach)        = inj₁ (W , rreach , ref)
  fail-L→R (inj₂ record { prefix = pre ; suffix = suf ; split = sp
                        ; witness = w ; reach = rc ; divwit = dw }) with reach-LR rc
  ... | inj₁ (refl , refl) =
        inj₂ (record { prefix = [] ; suffix = suf ; split = sp ; witness = RHSf
                     ; reach = ⟹-refl ; divwit = divQ→divR (divL→divQ dw) })
  ... | inj₂ (inj₁ (refl , refl)) =
        inj₂ (record { prefix = [] ; suffix = suf ; split = sp ; witness = RHSf
                     ; reach = ⟹-refl ; divwit = divQ→divR dw })
  ... | inj₂ (inj₂ rreach) =
        inj₂ (record { prefix = pre ; suffix = suf ; split = sp ; witness = w
                     ; reach = rreach ; divwit = dw })

  div-R→L : {s : List (Event√ R)} → divergences RHSf s → divergences LHSf s
  div-R→L record { prefix = pre ; suffix = suf ; split = sp
                 ; witness = w ; reach = rc ; divwit = dw } with reach-RL rc
  ... | inj₁ (refl , refl) =
        record { prefix = [] ; suffix = suf ; split = sp ; witness = LHSf
               ; reach = ⟹-refl ; divwit = divQ→divL (divR→divQ dw) }
  ... | inj₂ lreach =
        record { prefix = pre ; suffix = suf ; split = sp ; witness = w
               ; reach = lreach ; divwit = dw }

  div-L→R : {s : List (Event√ R)} → divergences LHSf s → divergences RHSf s
  div-L→R record { prefix = pre ; suffix = suf ; split = sp
                 ; witness = w ; reach = rc ; divwit = dw } with reach-LR rc
  ... | inj₁ (refl , refl) =
        record { prefix = [] ; suffix = suf ; split = sp ; witness = RHSf
               ; reach = ⟹-refl ; divwit = divQ→divR (divL→divQ dw) }
  ... | inj₂ (inj₁ (refl , refl)) =
        record { prefix = [] ; suffix = suf ; split = sp ; witness = RHSf
               ; reach = ⟹-refl ; divwit = divQ→divR dw }
  ... | inj₂ (inj₂ rreach) =
        record { prefix = pre ; suffix = suf ; split = sp ; witness = w
               ; reach = rreach ; divwit = dw }

  -- (react V ∅t) ▷ (react ∅v τc)  ≈FD  react V τc          (τc unstable)
  slide-fuse-FD : LHSf ≈FD RHSf
  slide-fuse-FD = (fail-R→L , div-R→L) , (fail-L→R , div-L→R)

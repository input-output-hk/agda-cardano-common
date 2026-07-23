{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Priority Law: `Pri` distributes over internal choice (⊓), up to STRONG
-- bisimulation.
--
--   Pri O (P ⊓ Q) (finBr-⊓ fbP fbQ)  ∼  (Pri O P fbP) ⊓ (Pri O Q fbQ)
--
-- `P ⊓ Q = react ∅v (br2 P Q)` is a pure-τ react node (unstable), so `Pri`
-- keeps BOTH τ-branches (priMax prunes the empty vis to nothing; priTau keeps
-- every τc-branch) and re-prioritises each residual.  Because τ is ≤-maximal,
-- NO `Or`-collapse / dominance reasoning is needed here — the two τ-branches
-- pass through untouched.  In fact `FinBr.next (finBr-⊓ fbP fbQ) (sTau refl refl)
-- ≡ fbP` (resp. `fbQ`) DEFINITIONALLY, so the prioritised residuals are already
-- `Pri O P fbP` / `Pri O Q fbQ` — the two τc-maps agree pointwise and the
-- residuals are EQUAL (closed by `sbisim-refl`; no `PriCong` needed).  Hence `∼`.
--
-- `--safe`, 0 postulates, no dne/Classical.
------------------------------------------------------------------------

open import Level using (_⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_; _×_; Σ-syntax; proj₁; proj₂)
open import Data.Empty using (⊥)
open import Data.Fin using (zero; suc)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)
open import Function using (case_of_)

open import Process_Trees

module CSP.Priority.Laws.IChoiceDist {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open PTree

open import Semantics.PriOrder {ℓ} {ℓe} {E}
open import Semantics.LTS      {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import Semantics.Bisim    {ℓ} {ℓe} {lsuc ℓ ⊔ ℓe} {E} {ExtI E}
open import CSP.Priority.Base       {ℓ} {ℓe} {E}
open import CSP.Operators      E-≟
open import CSP.Priority.Closure E-≟

------------------------------------------------------------------------
-- Residual relation for the τ-branches (both dead, or both alive & ∼).
------------------------------------------------------------------------

data MaybeRel {ℓr} {R : Set ℓr}
            : Maybe (PTree E (ExtI E) R) → Maybe (PTree E (ExtI E) R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  mnothing : MaybeRel nothing nothing
  mjust    : ∀ {p q} → p ∼ q → MaybeRel (just p) (just q)

mrel-sym : ∀ {ℓr} {R : Set ℓr} {mp mq : Maybe (PTree E (ExtI E) R)}
         → MaybeRel mp mq → MaybeRel mq mp
mrel-sym mnothing    = mnothing
mrel-sym (mjust p∼q) = mjust (sbisim-sym p∼q)

mrel-just : ∀ {ℓr} {R : Set ℓr} {mp mq : Maybe (PTree E (ExtI E) R)} {u}
          → MaybeRel mp mq → mp ≡ just u
          → Σ[ q ∈ PTree E (ExtI E) R ] (mq ≡ just q) × (u ∼ q)
mrel-just mnothing ()
mrel-just (mjust {p} {q} p∼q) eq = q , refl , subst (λ z → z ∼ q) (just-injective eq) p∼q

------------------------------------------------------------------------
-- Two nodes with EMPTY visible menus and ∼-agreeing τ-branches are ∼.
------------------------------------------------------------------------

-- one direction (P₁'s empty vis ⇒ no visible step; τ-steps matched via MaybeRel)
τmenu-sim : ∀ {ℓr} {R : Set ℓr} {P₁ P₂ : PTree E (ExtI E) R}
              {v₁ v₂ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
              {τc₁ τc₂ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
          → PTree.force P₁ ≡ react v₁ τc₁ → PTree.force P₂ ≡ react v₂ τc₂
          → (∀ at a → v₁ at a ≡ nothing)
          → (∀ i a → MaybeRel (τc₁ i a) (τc₂ i a))
          → SSimF (Sbisim R) P₁ P₂
τmenu-sim fP₁ fP₂ v₁∅ τm .SSimF.on-ev (sVis {at = at} {a = a} eqP brP) =
  case trans (sym (v₁∅ at a))
             (subst (λ w → w at a ≡ just _)
                    (sym (proj₁ (react-injective (trans (sym fP₁) eqP)))) brP) of λ ()
τmenu-sim fP₁ fP₂ v₁∅ τm .SSimF.on-ev  (sRet eqP)                     = case trans (sym fP₁) eqP of λ ()
τmenu-sim fP₁ fP₂ v₁∅ τm .SSimF.on-tau (sSil eqP)                     = case trans (sym fP₁) eqP of λ ()
τmenu-sim fP₁ fP₂ v₁∅ τm .SSimF.on-tau (sTau {i = i} {a = a} eqP brP)
  with mrel-just (τm i a)
         (subst (λ w → w i a ≡ just _) (sym (proj₂ (react-injective (trans (sym fP₁) eqP)))) brP)
... | u′ , eq₂ , u∼u′ = u′ , sTau fP₂ eq₂ , u∼u′

-- both empty-vis, τ-branches MaybeRel-agreeing ⇒ strong bisim
react-τ-∼ : ∀ {ℓr} {R : Set ℓr} {P₁ P₂ : PTree E (ExtI E) R}
              {v₁ v₂ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R))}
              {τc₁ τc₂ : (i : AnyTypes (ExtI E)) → ContinueType i (Maybe (PTree E (ExtI E) R))}
          → PTree.force P₁ ≡ react v₁ τc₁ → PTree.force P₂ ≡ react v₂ τc₂
          → (∀ at a → v₁ at a ≡ nothing) → (∀ at a → v₂ at a ≡ nothing)
          → (∀ i a → MaybeRel (τc₁ i a) (τc₂ i a))
          → P₁ ∼ P₂
react-τ-∼ fP₁ fP₂ v₁∅ v₂∅ τm .Sbisim.fwd = τmenu-sim fP₁ fP₂ v₁∅ τm
react-τ-∼ fP₁ fP₂ v₁∅ v₂∅ τm .Sbisim.bwd = τmenu-sim fP₂ fP₁ v₂∅ (λ i a → mrel-sym (τm i a))

------------------------------------------------------------------------
-- The distribution law.
------------------------------------------------------------------------

module _ {ℓo ℓr} {R : Set ℓr} (O : PriOrder ℓo)
         (P Q : PTree E (ExtI E) R) (fbP : FinBr P) (fbQ : FinBr Q) where

  private fb = finBr-⊓ fbP fbQ

  -- LHS' pruned vis (priMax over the empty ∅v) is everywhere nothing
  vis∅-L : ∀ at a → priMax O ∅v refl fb at a ≡ nothing
  vis∅-L at a = refl

  -- the two τc-maps agree pointwise (identical residuals ⇒ `sbisim-refl`)
  τagree : ∀ i a → MaybeRel (priTau O (br2 P Q) refl fb i a)
                            (br2 (Pri O P fbP) (Pri O Q fbQ) i a)
  τagree (_ , fin) (lift zero)            = mjust (sbisim-refl _)
  τagree (_ , fin) (lift (suc zero))      = mjust (sbisim-refl _)
  τagree (_ , fin) (lift (suc (suc _)))   = mnothing
  τagree (_ , base _)   _                 = mnothing
  τagree (_ , pair _ _) _                 = mnothing

  -- Pri distributes over ⊓ (strong bisimulation)
  pri-⊓-dist : Pri O (P ⊓ Q) fb ∼ ((Pri O P fbP) ⊓ (Pri O Q fbQ))
  pri-⊓-dist = react-τ-∼ refl refl vis∅-L (λ _ _ → refl) τagree

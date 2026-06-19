{-# OPTIONS --guardedness #-}

-- rename-step (T3.15):  (?x:A → P) ⟦R⟧  =  ?y:R(A) → ⨅{ P[a/x]⟦R⟧ | a∈A ∧ a R y }.
--
-- For the INJECTIVE single-alphabet renaming `_⟦_⟧ⁱ` (= renameInv with ι = id,
-- ι⁻¹ = just) each target event has AT MOST ONE preimage (invPreimg is a singleton
-- or empty), so the `⨅` collapses: renaming a prefix-choice node is the prefix-choice
-- node over the explicitly-renamed menu `renMenu`.
--
-- `pchoice v` is the bare visible-offer node `react v ∅t` (no τ).  Renaming it
-- produces (force-ren-react) `react (λ bt b → rnFan … (rnCollect v (invPreimg inv bt b)))
-- (extBranch … ∅t)`.  The visible map is NOT definitionally `renMenu inv v` and the
-- τ-map is NOT definitionally `∅t`, but they are POINTWISE-equal — so we lift a
-- generalised pointwise-both-maps strong bisim `node-pw2` to ≈FD.

open import Level using (Level)
open import Data.Maybe using (Maybe; just; nothing)
import Data.Maybe
open import Data.Product using (Σ; _,_; Σ-syntax; proj₁; proj₂)
open import Data.List using (List; []; _∷_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.RenameStep {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (pchoice; ∅t)
open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)
  using (ConcEvent₁; invRel; invPreimg; rnFan; rnCollect; rnMc; extBranch; extBwd)
open import CSP.Laws.Traces.TraceLawsRename {E = E}
  using (_⟦_⟧ⁱ; force-ren-react)
open import CSP.Laws.FD.SeqSlide E-≟ using (node-pw2)
open import Semantics.Bisim   {E = E} {I = ExtI E}
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)

-------------------------------------------------------------------------------------
-- The explicit renamed menu (the "spec" form, NOT the operator's internal rnFan):
-- a target event `b : bt` offers — if it has a (unique, injective) source preimage
-- `(at , a)` that the source menu enables (`v at a = just M`) — the renamed `M ⟦inv⟧ⁱ`.
-------------------------------------------------------------------------------------

renMenu : ∀ {ℓr} {R : Set ℓr}
          (inv : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
          (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
        → (bt : AnyTypes E) → ContinueType bt (Maybe (PTree E (ExtI E) R))
renMenu inv v bt b with inv bt b
... | nothing       = nothing
... | just (at , a) = Data.Maybe.map (_⟦ inv ⟧ⁱ) (v at a)

-------------------------------------------------------------------------------------
-- The law.
-------------------------------------------------------------------------------------

module _ {ℓr} {R : Set ℓr}
         (inv : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
         (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         where

  -- visible-map pointwise: the operator's rnFan∘rnCollect∘invPreimg collapses (the
  -- preimage list is empty or a singleton) to the explicit `renMenu`.
  vis-pw : ∀ bt b
         → rnFan (invRel inv) (invPreimg inv) (rnCollect v (invPreimg inv bt b))
           ≡ renMenu inv v bt b
  vis-pw bt b with inv bt b
  ... | nothing       = refl
  ... | just (at , a) with v at a
  ...   | nothing = refl
  ...   | just M  = refl

  -- τ-map pointwise: the renamed empty τ-map is still empty.
  tau-pw : ∀ i a → extBranch (invRel inv) (invPreimg inv) (∅t {R = R}) i a ≡ ∅t {R = R} i a
  tau-pw (A , eι₂) a with extBwd eι₂
  ... | just eι₁ = refl
  ... | nothing  = refl

  rename-step-∼ : ((pchoice v) ⟦ inv ⟧ⁱ) ∼ (pchoice (renMenu inv v))
  rename-step-∼ =
    node-pw2
      ((pchoice v) ⟦ inv ⟧ⁱ) (pchoice (renMenu inv v))
      (λ bt b → rnFan (invRel inv) (invPreimg inv) (rnCollect v (invPreimg inv bt b)))
      (renMenu inv v)
      (extBranch (invRel inv) (invPreimg inv) ∅t) ∅t
      (force-ren-react {inv = inv} {P = pchoice v} refl)
      refl
      vis-pw
      tau-pw

  -- rename-step (T3.15):  (pchoice v) ⟦ inv ⟧ⁱ  ≈FD  pchoice (renMenu inv v)
  rename-step-FD : ((pchoice v) ⟦ inv ⟧ⁱ) ≈FD (pchoice (renMenu inv v))
  rename-step-FD = drbisim→≈FD (sbisim→drbisim rename-step-∼)

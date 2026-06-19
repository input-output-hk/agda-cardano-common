{-# OPTIONS --guardedness #-}

-- Renaming composes (rename-combine), for injective single-E renamings:
--   ((P ⟦ inv₁ ⟧ⁱ) ⟦ inv₂ ⟧ⁱ) ≈FD (P ⟦ invComp inv₁ inv₂ ⟧ⁱ)
-- where `invComp inv₁ inv₂` is the Kleisli composition through `Maybe`:
--   invComp inv₁ inv₂ bt b = inv₂ bt b >>= λ (yt , ya) → inv₁ yt ya.
--
-- Proved as a STRONG bisimulation lifted to ≈FD via drbisim→≈FD ∘ sbisim→drbisim
-- (the RenameEChoiceDist lift).  It is a FAMILY over P, genuinely coinductive, so it
-- is defined MUTUALLY with its REVERSE (rename-combine-∼ / rename-combine-∼R), the
-- residuals referring to the reverse WITHOUT sbisim-sym (which would unguard).

open import Level using (Level)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; subst)

open import Process_Trees

module CSP.Laws.FD.RenameCombine {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)

open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)
  using (ConcEvent₁)
open import CSP.Laws.Traces.TraceLawsRename {E = E}
  using (_⟦_⟧ⁱ; ren-τ-fwd; ren-ev-fwd; ren-τ-inv; ren-ev-inv;
         force-ren-ret; force-ren-ret-inv)

private
  variable
    ℓr : Level
    R  : Set ℓr

-------------------------------------------------------------------------------------
-- The Kleisli composition of two injective single-E renamings.
-------------------------------------------------------------------------------------

invComp : (inv₁ inv₂ : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
        → (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁
invComp inv₁ inv₂ bt b with inv₂ bt b
... | nothing        = nothing
... | just (yt , ya) = inv₁ yt ya

-- composing two `just` witnesses gives a composite `just` witness (orientation pin).
invComp-just : (inv₁ inv₂ : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
             → ∀ {zt z yt ya xt xa}
             → inv₂ zt z ≡ just (yt , ya) → inv₁ yt ya ≡ just (xt , xa)
             → invComp inv₁ inv₂ zt z ≡ just (xt , xa)
invComp-just inv₁ inv₂ {zt = zt} {z = z} eq₂ eq₁ with inv₂ zt z | eq₂
... | just (yt , ya) | refl = eq₁

-- decomposing a composite `just` witness back into the two layers.
invComp-split : (inv₁ inv₂ : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
              → ∀ {bt b xt xa}
              → invComp inv₁ inv₂ bt b ≡ just (xt , xa)
              → Σ[ yt ∈ AnyTypes E ] Σ[ ya ∈ proj₁ yt ]
                  (inv₂ bt b ≡ just (yt , ya)) × (inv₁ yt ya ≡ just (xt , xa))
invComp-split inv₁ inv₂ {bt = bt} {b = b} eq with inv₂ bt b
... | nothing        = case eq of λ ()
... | just (yt , ya) = yt , ya , refl , eq

-------------------------------------------------------------------------------------
-- MAIN: rename composes (mutual/reversed strong bisimulation).
-------------------------------------------------------------------------------------

rename-combine-∼  : (inv₁ inv₂ : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
                    (P : PTree E (ExtI E) R)
                  → ((P ⟦ inv₁ ⟧ⁱ) ⟦ inv₂ ⟧ⁱ) ∼ (P ⟦ invComp inv₁ inv₂ ⟧ⁱ)
rename-combine-∼R : (inv₁ inv₂ : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
                    (P : PTree E (ExtI E) R)
                  → (P ⟦ invComp inv₁ inv₂ ⟧ⁱ) ∼ ((P ⟦ inv₁ ⟧ⁱ) ⟦ inv₂ ⟧ⁱ)

-- forward visible/√ : ((P⟦inv₁⟧ⁱ)⟦inv₂⟧ⁱ)  ⟶  (P⟦invComp⟧ⁱ)
comb-fwd-ev : (inv₁ inv₂ : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
              (P : PTree E (ExtI E) R) {l : Event√ R} {M : PTree E (ExtI E) R}
            → ((P ⟦ inv₁ ⟧ⁱ) ⟦ inv₂ ⟧ⁱ) ─[ ev l ]─► M
            → Σ[ M′ ∈ PTree E (ExtI E) R ]
                ((P ⟦ invComp inv₁ inv₂ ⟧ⁱ) ─[ ev l ]─► M′) × (M ∼ M′)

-- forward τ
comb-fwd-tau : (inv₁ inv₂ : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
               (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
             → ((P ⟦ inv₁ ⟧ⁱ) ⟦ inv₂ ⟧ⁱ) ─[ τ ]─► M
             → Σ[ M′ ∈ PTree E (ExtI E) R ]
                 ((P ⟦ invComp inv₁ inv₂ ⟧ⁱ) ─[ τ ]─► M′) × (M ∼ M′)

-- backward visible/√ : (P⟦invComp⟧ⁱ)  ⟶  ((P⟦inv₁⟧ⁱ)⟦inv₂⟧ⁱ)
comb-bwd-ev : (inv₁ inv₂ : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
              (P : PTree E (ExtI E) R) {l : Event√ R} {M : PTree E (ExtI E) R}
            → (P ⟦ invComp inv₁ inv₂ ⟧ⁱ) ─[ ev l ]─► M
            → Σ[ M′ ∈ PTree E (ExtI E) R ]
                (((P ⟦ inv₁ ⟧ⁱ) ⟦ inv₂ ⟧ⁱ) ─[ ev l ]─► M′) × (M ∼ M′)

-- backward τ
comb-bwd-tau : (inv₁ inv₂ : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
               (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
             → (P ⟦ invComp inv₁ inv₂ ⟧ⁱ) ─[ τ ]─► M
             → Σ[ M′ ∈ PTree E (ExtI E) R ]
                 (((P ⟦ inv₁ ⟧ⁱ) ⟦ inv₂ ⟧ⁱ) ─[ τ ]─► M′) × (M ∼ M′)

-- forward visible/√ body.  Invert OUTER (inv₂), then INNER (inv₁).
comb-fwd-ev inv₁ inv₂ P step with ren-ev-inv step
... | inj₂ (r , refl , eqret , refl) =
      -- OUTER √: force (P⟦inv₁⟧ⁱ) ≡ ret r ⇒ force P ≡ ret r.
      deadlock
    , sRet (force-ren-ret {P = P} (force-ren-ret-inv {P = P} eqret))
    , sbisim-refl deadlock
... | inj₁ (yt , ya , zt , z , M₁ , innerEv , inv₂eq , refl , refl) with ren-ev-inv innerEv
...   | inj₁ (xt , xa , yt′ , ya′ , P₁ , Pev , inv₁eq , refl , refl) =
        (P₁ ⟦ invComp inv₁ inv₂ ⟧ⁱ)
      , ren-ev-fwd {P = P} Pev (invComp-just inv₁ inv₂ inv₂eq inv₁eq)
      , rename-combine-∼ inv₁ inv₂ P₁
...   | inj₂ (r , () , eqret , refl)

-- forward τ body.  Invert OUTER then INNER τ.
comb-fwd-tau inv₁ inv₂ P step with ren-τ-inv step
... | M₁ , innerτ , refl with ren-τ-inv innerτ
...   | P₁ , Pτ , refl =
        (P₁ ⟦ invComp inv₁ inv₂ ⟧ⁱ)
      , ren-τ-fwd {P = P} Pτ
      , rename-combine-∼ inv₁ inv₂ P₁

-- backward visible/√ body.  Invert the composite, decompose invComp, rebuild two layers.
comb-bwd-ev inv₁ inv₂ P step with ren-ev-inv step
... | inj₂ (r , refl , eqret , refl) =
      deadlock
    , sRet (force-ren-ret {P = P ⟦ inv₁ ⟧ⁱ} (force-ren-ret {P = P} eqret))
    , sbisim-refl deadlock
... | inj₁ (xt , xa , zt , z , P₁ , Pev , invCeq , refl , refl)
      with invComp-split inv₁ inv₂ invCeq
...   | yt , ya , inv₂eq , inv₁eq =
        (P₁ ⟦ inv₁ ⟧ⁱ ⟦ inv₂ ⟧ⁱ)
      , ren-ev-fwd {P = P ⟦ inv₁ ⟧ⁱ} (ren-ev-fwd {P = P} Pev inv₁eq) inv₂eq
      , rename-combine-∼R inv₁ inv₂ P₁

-- backward τ body.
comb-bwd-tau inv₁ inv₂ P step with ren-τ-inv step
... | P₁ , Pτ , refl =
      (P₁ ⟦ inv₁ ⟧ⁱ ⟦ inv₂ ⟧ⁱ)
    , ren-τ-fwd {P = P ⟦ inv₁ ⟧ⁱ} (ren-τ-fwd {P = P} Pτ)
    , rename-combine-∼R inv₁ inv₂ P₁

rename-combine-∼  inv₁ inv₂ P .Sbisim.fwd .SSimF.on-ev  = comb-fwd-ev  inv₁ inv₂ P
rename-combine-∼  inv₁ inv₂ P .Sbisim.fwd .SSimF.on-tau = comb-fwd-tau inv₁ inv₂ P
rename-combine-∼  inv₁ inv₂ P .Sbisim.bwd .SSimF.on-ev  = comb-bwd-ev  inv₁ inv₂ P
rename-combine-∼  inv₁ inv₂ P .Sbisim.bwd .SSimF.on-tau = comb-bwd-tau inv₁ inv₂ P

rename-combine-∼R inv₁ inv₂ P .Sbisim.fwd .SSimF.on-ev  = comb-bwd-ev  inv₁ inv₂ P
rename-combine-∼R inv₁ inv₂ P .Sbisim.fwd .SSimF.on-tau = comb-bwd-tau inv₁ inv₂ P
rename-combine-∼R inv₁ inv₂ P .Sbisim.bwd .SSimF.on-ev  = comb-fwd-ev  inv₁ inv₂ P
rename-combine-∼R inv₁ inv₂ P .Sbisim.bwd .SSimF.on-tau = comb-fwd-tau inv₁ inv₂ P

-------------------------------------------------------------------------------------
-- FD lift.
-------------------------------------------------------------------------------------

rename-combine-FD : (inv₁ inv₂ : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
                    (P : PTree E (ExtI E) R)
                  → ((P ⟦ inv₁ ⟧ⁱ) ⟦ inv₂ ⟧ⁱ) ≈FD (P ⟦ invComp inv₁ inv₂ ⟧ⁱ)
rename-combine-FD inv₁ inv₂ P =
  drbisim→≈FD (sbisim→drbisim (rename-combine-∼ inv₁ inv₂ P))

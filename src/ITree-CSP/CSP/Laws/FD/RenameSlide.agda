{-# OPTIONS --guardedness #-}

-- Renaming distributes over sliding for an INJECTIVE prefix head (U13.6):
--   (((pchoice v) ▷ Q) ⟦ inv ⟧ⁱ) ≈FD (((pchoice v) ⟦ inv ⟧ⁱ) ▷ (Q ⟦ inv ⟧ⁱ)).
--
-- Faithful spike rendering of Roscoe's
--   ((?x:A→P) ▷ Q)⟦R⟧ = (?y:R(A)→⨅{P[a/x]⟦R⟧ | a R y}) ▷ (Q⟦R⟧).
-- For an INJECTIVE `inv` each target event `y` has ≤1 preimage, so the inner ⨅
-- collapses and the surviving menu `?y:R(A)→…` is exactly the renamed prefix
-- `(pchoice v)⟦inv⟧ⁱ`.
--
-- Renaming does NOT turn events into τ's (unlike hiding): it relabels visible
-- events and re-indexes τ's 1-1.  The prefix `pchoice v` is τ-FREE
-- (`force (pchoice v) = react v ∅t`), so there is NO coinductive recursion: every
-- matched successor is the literally-same tree, discharged by `sbisim-refl`.  Hence
-- a (finite, non-recursive) STRONG bisimulation, lifted to ≈FD via
-- `drbisim→≈FD ∘ sbisim→drbisim`.  Mirrors `CSP.Laws.FD.RenameIChoiceDist`.

open import Level using (Level)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.RenameSlide {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (pchoice; _▷_; ∅t)
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Traces.TraceLaws E-≟ using (▷-ev-L)
open import CSP.Laws.Traces.TraceLawsExtChoice E-≟ using (NonRet)
open import CSP.Laws.Traces.TraceLawsExtChoiceMono E-≟
  using (▷-τ-elim; ▷-ev-elim; ▷-timeout)
open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)
  using (ConcEvent₁)
open import CSP.Laws.Traces.TraceLawsRename {E = E}
  using (_⟦_⟧ⁱ; ren-τ-fwd; ren-ev-fwd; ren-τ-inv; ren-ev-inv;
         force-ren-react)

private
  variable
    ℓr : Level
    R  : Set ℓr

module _ (inv : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
         (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
         (Q : PTree E (ExtI E) R) where

  -- the bare prefix has no τ (force is `react v ∅t`, whose τ-map is everywhere
  -- `nothing`): `sSil` needs `force ≡ sil _` (it is `react`), `sTau` needs the
  -- τ-branch `∅t i a ≡ just _` (it is `nothing`).
  pchoice-no-τ : {M : PTree E (ExtI E) R} → (pchoice v) ─[ τ ]─► M → ⊥
  pchoice-no-τ (sSil eq)     = case eq of λ ()
  pchoice-no-τ (sTau eq br) with react-injective eq
  ... | _ , refl = case br of λ ()

  -- `force ((pchoice v)⟦inv⟧ⁱ)` is a `react` node (renaming a `react v ∅t`),
  -- so its head is non-ret.
  ren-pchoice-react :
      Σ[ v′ ∈ _ ] Σ[ τc′ ∈ _ ] PTree.force ((pchoice v) ⟦ inv ⟧ⁱ) ≡ react v′ τc′
  ren-pchoice-react = _ , _ , force-ren-react {inv = inv} {P = pchoice v} refl

  -- the renamed prefix has no τ either: invert (ren-τ-inv) to a τ of `pchoice v`.
  ren-pchoice-no-τ : {M : PTree E (ExtI E) R} → ((pchoice v) ⟦ inv ⟧ⁱ) ─[ τ ]─► M → ⊥
  ren-pchoice-no-τ step with ren-τ-inv step
  ... | P₁ , Pτ , refl = pchoice-no-τ Pτ

  -----------------------------------------------------------------------------------
  -- four bisimulation handlers
  -----------------------------------------------------------------------------------

  -- fwd on-tau: a τ of LHS = timeout (→ Q⟦inv⟧ⁱ) or P's own τ (impossible).
  fwd-tau : {M : PTree E (ExtI E) R}
          → ((((pchoice v) ▷ Q) ⟦ inv ⟧ⁱ)) ─[ τ ]─► M
          → Σ[ M′ ∈ PTree E (ExtI E) R ]
              ((((pchoice v) ⟦ inv ⟧ⁱ) ▷ (Q ⟦ inv ⟧ⁱ)) ─[ τ ]─► M′) × (M ∼ M′)
  fwd-tau step with ren-τ-inv step
  ... | P₁ , Pτ , refl with ▷-τ-elim (pchoice v) Q Pτ
  ...   | inj₁ refl =
            (Q ⟦ inv ⟧ⁱ)
          , (case ren-pchoice-react of λ where
               (v′ , τc′ , eqf) → ▷-timeout ((pchoice v) ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ) eqf tt)
          , sbisim-refl (Q ⟦ inv ⟧ⁱ)
    where open import Data.Unit using (tt)
  ...   | inj₂ (P' , Pτ' , _) = ⊥-elim (pchoice-no-τ Pτ')

  -- fwd on-ev: a visible event of LHS = a P-event (through the slide), relabelled.
  fwd-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
         → ((((pchoice v) ▷ Q) ⟦ inv ⟧ⁱ)) ─[ ev l ]─► M
         → Σ[ M′ ∈ PTree E (ExtI E) R ]
             ((((pchoice v) ⟦ inv ⟧ⁱ) ▷ (Q ⟦ inv ⟧ⁱ)) ─[ ev l ]─► M′) × (M ∼ M′)
  fwd-ev step with ren-ev-inv step
  ... | inj₁ (at , a , bt , b , P₁ , Pev , inv-eq , refl , refl) =
          (P₁ ⟦ inv ⟧ⁱ)
        , ▷-ev-L {Q = Q ⟦ inv ⟧ⁱ} (ren-ev-fwd (▷-ev-elim (pchoice v) Q Pev) inv-eq)
        , sbisim-refl (P₁ ⟦ inv ⟧ⁱ)
  -- `force ((pchoice v) ▷ Q) ≡ ret r` is impossible: it forces to a `react` node.
  ... | inj₂ (r , refl , eqret , refl) = case eqret of λ ()

  -- bwd on-tau: a τ of RHS = timeout (→ Q⟦inv⟧ⁱ) or renamed-prefix's τ (impossible).
  bwd-tau : {M : PTree E (ExtI E) R}
          → ((((pchoice v) ⟦ inv ⟧ⁱ) ▷ (Q ⟦ inv ⟧ⁱ))) ─[ τ ]─► M
          → Σ[ M′ ∈ PTree E (ExtI E) R ]
              (((((pchoice v) ▷ Q) ⟦ inv ⟧ⁱ)) ─[ τ ]─► M′) × (M ∼ M′)
  bwd-tau step with ▷-τ-elim ((pchoice v) ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ) step
  ... | inj₁ refl =
          (Q ⟦ inv ⟧ⁱ)
        , ren-τ-fwd (▷-timeout (pchoice v) Q {nP = react v ∅t} refl tt)
        , sbisim-refl (Q ⟦ inv ⟧ⁱ)
    where open import Data.Unit using (tt)
  ... | inj₂ (P' , Pτ' , _) = ⊥-elim (ren-pchoice-no-τ Pτ')

  -- bwd on-ev: a visible event of RHS = renamed-prefix's event; invert to source.
  bwd-ev : {l : Event√ R} {M : PTree E (ExtI E) R}
         → ((((pchoice v) ⟦ inv ⟧ⁱ) ▷ (Q ⟦ inv ⟧ⁱ))) ─[ ev l ]─► M
         → Σ[ M′ ∈ PTree E (ExtI E) R ]
             (((((pchoice v) ▷ Q) ⟦ inv ⟧ⁱ)) ─[ ev l ]─► M′) × (M ∼ M′)
  bwd-ev step with ▷-ev-elim ((pchoice v) ⟦ inv ⟧ⁱ) (Q ⟦ inv ⟧ⁱ) step
  ... | renPev with ren-ev-inv renPev
  ...   | inj₁ (at , a , bt , b , P₁ , Pev , inv-eq , refl , refl) =
            (P₁ ⟦ inv ⟧ⁱ)
          , ren-ev-fwd (▷-ev-L {Q = Q} Pev) inv-eq
          , sbisim-refl (P₁ ⟦ inv ⟧ⁱ)
  ...   | inj₂ (r , refl , eqret , refl) = case eqret of λ ()

  -----------------------------------------------------------------------------------
  -- the strong bisimulation, and the FD law
  -----------------------------------------------------------------------------------

  rename-slide-∼ :
      ((((pchoice v) ▷ Q) ⟦ inv ⟧ⁱ)) ∼ (((pchoice v) ⟦ inv ⟧ⁱ) ▷ (Q ⟦ inv ⟧ⁱ))
  rename-slide-∼ .Sbisim.fwd .SSimF.on-ev  = fwd-ev
  rename-slide-∼ .Sbisim.fwd .SSimF.on-tau = fwd-tau
  rename-slide-∼ .Sbisim.bwd .SSimF.on-ev  = bwd-ev
  rename-slide-∼ .Sbisim.bwd .SSimF.on-tau = bwd-tau

-- rename-slide (U13.6):
--   (((pchoice v) ▷ Q) ⟦ inv ⟧ⁱ) ≈FD (((pchoice v) ⟦ inv ⟧ⁱ) ▷ (Q ⟦ inv ⟧ⁱ))
rename-slide-FD : ∀ {ℓr} {R : Set ℓr}
                  (inv : (bt : AnyTypes E) → proj₁ bt → Maybe ConcEvent₁)
                  (v : (at : AnyTypes E) → ContinueType at (Maybe (PTree E (ExtI E) R)))
                  (Q : PTree E (ExtI E) R)
                → ((((pchoice v) ▷ Q) ⟦ inv ⟧ⁱ)) ≈FD (((pchoice v) ⟦ inv ⟧ⁱ) ▷ (Q ⟦ inv ⟧ⁱ))
rename-slide-FD inv v Q = drbisim→≈FD (sbisim→drbisim (rename-slide-∼ inv v Q))

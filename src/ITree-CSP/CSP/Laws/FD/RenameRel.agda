{-# OPTIONS --guardedness #-}

-- Failures-divergences laws for the GENERAL RELATIONAL renaming `_⟦ R ¿ preimg ⟧`
-- (same-alphabet instantiation E₁ = E₂ = E), generalizing the injective versions in
-- `CSP.Laws.FD.RenameZero` (rename-zero) and `CSP.Laws.FD.RenameIChoiceDist`
-- (rename-⊓-dist).  `R`/`preimg` are threaded as explicit lemma parameters.
--
--   LAW 1 (T11.8):  (div ⟦ R ¿ preimg ⟧) ≈FD div
--   LAW 2 (T3.13):  ((P ⊓ Q) ⟦ R ¿ preimg ⟧) ≈FD ((P ⟦ R ¿ preimg ⟧) ⊓ (Q ⟦ R ¿ preimg ⟧))

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Sum using (inj₁; inj₂)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)

open import Process_Trees

module CSP.Laws.FD.RenameRel {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (_⊓_; ∅v)
open import CSP.Rename {E₁ = E} {E₂ = E} (λ e → e) (λ e → just e) (λ _ → refl)
  using (_⟦_¿_⟧; ConcEvent₁; ConcEvent₂; rnCollect; rnFan)
open import Semantics.LTS     {E = E} {I = ExtI E} hiding (Diverges)
open import Semantics.Bisim   {E = E} {I = ExtI E}
open import Semantics.DRBisim {E = E} {I = ExtI E} using (Diverges)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (divergences; _≈FD_; empty-div; div-extension-closed; div-divergence)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Bisim.Laws E-≟ using (⊓-stepL; ⊓-stepR; ⊓-τ-inv)
open import CSP.Laws.Traces.TraceLawsRenameGen {E = E}
  using (ren-τ-fwd; ren-τ-inv; force-renG-react-inv; force-renG-ret-inv)

private
  variable
    ℓr ℓR : Level
    Rr : Set ℓr
    R : ConcEvent₁ → ConcEvent₂ → Set ℓR
    preimg : (bt : AnyTypes E) (b : proj₁ bt)
           → List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] R (at , a) (bt , b))

-------------------------------------------------------------------------------------
-- LAW 1 — rename-zero relational (T11.8):  (div ⟦ R ¿ preimg ⟧) ≈FD div
--
-- force(div) = sil div ⇒ force(div ⟦ R ¿ preimg ⟧) = sil (div ⟦ R ¿ preimg ⟧):
-- an infinite silent loop, hence diverges at []. By extension-closure both sides
-- are ⊥ at every trace, so all four refinements emit that divergence.
-------------------------------------------------------------------------------------

rename-div-diverges : (R : ConcEvent₁ → ConcEvent₂ → Set ℓR) (preimg : _)
                    → Diverges ((div {E = E} {I = ExtI E} {R = Rr}) ⟦ R ¿ preimg ⟧)
rename-div-diverges R preimg .Diverges.next = div ⟦ R ¿ preimg ⟧
rename-div-diverges R preimg .Diverges.step = sSil refl
rename-div-diverges R preimg .Diverges.rest = rename-div-diverges R preimg

rename-div-all : {R : ConcEvent₁ → ConcEvent₂ → Set ℓR} {preimg : _} {s : _}
               → divergences ((div {E = E} {I = ExtI E} {R = Rr}) ⟦ R ¿ preimg ⟧) s
rename-div-all {R = R} {preimg = preimg} =
  div-extension-closed (empty-div (rename-div-diverges R preimg))

div-all : {s : _} → divergences (div {E = E} {I = ExtI E} {R = Rr}) s
div-all = div-extension-closed div-divergence

-- rename-zero (T11.8):  (div ⟦ R ¿ preimg ⟧) ≈FD div
rename-zero-FD : (R : ConcEvent₁ → ConcEvent₂ → Set ℓR) (preimg : _)
              → ((div {E = E} {I = ExtI E} {R = Rr}) ⟦ R ¿ preimg ⟧) ≈FD div
rename-zero-FD R preimg =
    ( (λ _ → inj₂ rename-div-all) , (λ _ → rename-div-all) )
  , ( (λ _ → inj₂ div-all)        , (λ _ → div-all)        )

-------------------------------------------------------------------------------------
-- LAW 2 — rename-⊓-dist relational (T3.13):
--   ((P ⊓ Q) ⟦ R ¿ preimg ⟧) ≈FD ((P ⟦ R ¿ preimg ⟧) ⊓ (Q ⟦ R ¿ preimg ⟧))
--
-- Both sides are ⊓-shaped: they offer NO visible event (⊓ = react ∅v (br2 P Q),
-- and renaming a ∅v offer map yields no offers), and a single internal τ on either
-- side resolves to exactly the SAME state — P ⟦…⟧ or Q ⟦…⟧.  So it is a
-- (non-recursive) STRONG bisimulation with sbisim-refl continuations, lifted to ≈FD.
-------------------------------------------------------------------------------------

-- an internal choice offers no visible event (force is `react ∅v …`).
⊓-no-ev : {P Q M : PTree E (ExtI E) Rr} {e : Event√ Rr} → (P ⊓ Q) ─[ ev e ]─► M → ⊥
⊓-no-ev (sRet eq)    = case eq of λ ()
⊓-no-ev (sVis eq br) with react-injective eq
... | refl , _ = case br of λ ()

-- collecting from the empty visible offer map gives the empty source list
-- (∅v at a = nothing for every entry).
rnCollect-∅v : ∀ {ℓP} {Pr : (at : AnyTypes E) → proj₁ at → Set ℓP}
                 (xs : List (Σ[ at ∈ AnyTypes E ] Σ[ a ∈ proj₁ at ] Pr at a))
             → rnCollect (∅v {R = Rr}) xs ≡ []
rnCollect-∅v []                  = refl
rnCollect-∅v ((at , a , _) ∷ xs) = rnCollect-∅v xs

-- the renamed internal choice offers no visible event either.  Invert the sVis:
-- force ((P⊓Q)⟦R¿preimg⟧) is the renamed react node whose source is
-- force(P⊓Q) = react ∅v (br2 P Q); since rnCollect ∅v _ = [], the offered fan is
-- rnFan R preimg [] = nothing, contradicting the `br : (offer) ≡ just M`.
rename-⊓-no-ev : {P Q M : PTree E (ExtI E) Rr} {e : Event√ Rr}
               → ((P ⊓ Q) ⟦ R ¿ preimg ⟧) ─[ ev e ]─► M → ⊥
rename-⊓-no-ev {P = P} {Q = Q} (sRet eq)
  with force-renG-ret-inv {P = P ⊓ Q} eq
... | ()
rename-⊓-no-ev {R = R} {preimg = preimg} {P = P} {Q = Q}
               (sVis {at = bt} {a = b} eq br)
  with force-renG-react-inv {P = P ⊓ Q} eq
... | vP , τcP , eqPQ , refl , _ with react-injective eqPQ
...   | refl , _ =
        case trans (sym (cong (rnFan R preimg)
                              (rnCollect-∅v {Pr = λ at a → R (at , a) (bt , b)} (preimg bt b))))
                   br of λ ()

module _ (R : ConcEvent₁ → ConcEvent₂ → Set ℓR) (preimg : _)
         (P Q : PTree E (ExtI E) Rr) where

  dist-fwd-ev : {l : Event√ Rr} {M : PTree E (ExtI E) Rr}
              → ((P ⊓ Q) ⟦ R ¿ preimg ⟧) ─[ ev l ]─► M
              → Σ[ M′ ∈ PTree E (ExtI E) Rr ]
                  (((P ⟦ R ¿ preimg ⟧) ⊓ (Q ⟦ R ¿ preimg ⟧)) ─[ ev l ]─► M′) × (M ∼ M′)
  dist-fwd-ev step = ⊥-elim (rename-⊓-no-ev {P = P} {Q = Q} step)

  dist-fwd-tau : {M : PTree E (ExtI E) Rr}
               → ((P ⊓ Q) ⟦ R ¿ preimg ⟧) ─[ τ ]─► M
               → Σ[ M′ ∈ PTree E (ExtI E) Rr ]
                   (((P ⟦ R ¿ preimg ⟧) ⊓ (Q ⟦ R ¿ preimg ⟧)) ─[ τ ]─► M′) × (M ∼ M′)
  dist-fwd-tau step with ren-τ-inv step
  ... | P₁ , Pτ , refl with ⊓-τ-inv P Q Pτ
  ...   | inj₁ refl = (P ⟦ R ¿ preimg ⟧) , ⊓-stepL (P ⟦ R ¿ preimg ⟧) (Q ⟦ R ¿ preimg ⟧)
                    , sbisim-refl (P ⟦ R ¿ preimg ⟧)
  ...   | inj₂ refl = (Q ⟦ R ¿ preimg ⟧) , ⊓-stepR (P ⟦ R ¿ preimg ⟧) (Q ⟦ R ¿ preimg ⟧)
                    , sbisim-refl (Q ⟦ R ¿ preimg ⟧)

  dist-bwd-ev : {l : Event√ Rr} {M : PTree E (ExtI E) Rr}
              → ((P ⟦ R ¿ preimg ⟧) ⊓ (Q ⟦ R ¿ preimg ⟧)) ─[ ev l ]─► M
              → Σ[ M′ ∈ PTree E (ExtI E) Rr ]
                  (((P ⊓ Q) ⟦ R ¿ preimg ⟧) ─[ ev l ]─► M′) × (M ∼ M′)
  dist-bwd-ev step = ⊥-elim (⊓-no-ev step)

  dist-bwd-tau : {M : PTree E (ExtI E) Rr}
               → ((P ⟦ R ¿ preimg ⟧) ⊓ (Q ⟦ R ¿ preimg ⟧)) ─[ τ ]─► M
               → Σ[ M′ ∈ PTree E (ExtI E) Rr ]
                   (((P ⊓ Q) ⟦ R ¿ preimg ⟧) ─[ τ ]─► M′) × (M ∼ M′)
  dist-bwd-tau step with ⊓-τ-inv (P ⟦ R ¿ preimg ⟧) (Q ⟦ R ¿ preimg ⟧) step
  ... | inj₁ refl = (P ⟦ R ¿ preimg ⟧) , ren-τ-fwd (⊓-stepL P Q) , sbisim-refl (P ⟦ R ¿ preimg ⟧)
  ... | inj₂ refl = (Q ⟦ R ¿ preimg ⟧) , ren-τ-fwd (⊓-stepR P Q) , sbisim-refl (Q ⟦ R ¿ preimg ⟧)

  rename-⊓-dist-∼ : ((P ⊓ Q) ⟦ R ¿ preimg ⟧) ∼ ((P ⟦ R ¿ preimg ⟧) ⊓ (Q ⟦ R ¿ preimg ⟧))
  rename-⊓-dist-∼ .Sbisim.fwd .SSimF.on-ev  = dist-fwd-ev
  rename-⊓-dist-∼ .Sbisim.fwd .SSimF.on-tau = dist-fwd-tau
  rename-⊓-dist-∼ .Sbisim.bwd .SSimF.on-ev  = dist-bwd-ev
  rename-⊓-dist-∼ .Sbisim.bwd .SSimF.on-tau = dist-bwd-tau

  -- rename-⊓-dist (T3.13)
  rename-⊓-dist-FD : ((P ⊓ Q) ⟦ R ¿ preimg ⟧) ≈FD ((P ⟦ R ¿ preimg ⟧) ⊓ (Q ⟦ R ¿ preimg ⟧))
  rename-⊓-dist-FD = drbisim→≈FD (sbisim→drbisim rename-⊓-dist-∼)

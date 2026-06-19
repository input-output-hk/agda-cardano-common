{-# OPTIONS --guardedness #-}

-- Hide-combine (T3.3 / U5.3):  (P ∖ A) ∖ B ≈FD P ∖ (A ∪ B).
--
-- Hiding A then B = hiding A ∪ B.  The visible maps already AGREE — an event survives both
-- nested hides iff it is in neither A nor B, i.e. iff it is outside `A ∪es B`.  The τ's also
-- correspond: P's own τ's propagate through both; a hidden event becomes a τ at whichever
-- level hides it (inner ∖A if it is in A, outer ∖B if in B-not-A) on the left, and via the
-- single `A ∪es B` hide on the right, related by `(A ∪es B).mem ≡ A.mem ⊎ B.mem`.  A coinductive
-- STRONG bisimulation, lifted to ≈FD.  Mutual `combine`/`combineR` (reversed, for bwd).

open import Level using (Level)
open import Data.Empty using (⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.HideCombine {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_)
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (Hide-τ; Hide-keep; Hide-hidden; Hide-√; Hide-τ-elim; HideτR; hτP; hτH
        ; hide-hVis-inv; HideevR; heV; he√; fHide-ret; fHide-ret-inv)
open import CSP.Laws.Traces.TraceLawsHideAlg E-≟ using (_∪es_)

private
  variable
    ℓr : Level
    R  : Set ℓr

combine  : (A B : EventSet) (P : PTree E (ExtI E) R) → ((P ∖ A) ∖ B) ∼ (P ∖ (A ∪es B))
combineR : (A B : EventSet) (P : PTree E (ExtI E) R) → (P ∖ (A ∪es B)) ∼ ((P ∖ A) ∖ B)

-- forward: a move of (P∖A)∖B is matched by P∖(A∪B).
fwd-ev : (A B : EventSet) (P : PTree E (ExtI E) R) {l : Event√ R} {M : PTree E (ExtI E) R}
       → ((P ∖ A) ∖ B) ─[ ev l ]─► M
       → Σ[ M′ ∈ PTree E (ExtI E) R ] ((P ∖ (A ∪es B)) ─[ ev l ]─► M′) × (M ∼ M′)
fwd-ev A B P (sVis eqf br) with hide-hVis-inv B (P ∖ A) eqf br
... | heV M' ¬cB (sVis eqf' br') with hide-hVis-inv A P eqf' br'
...   | heV M'' ¬cA Pev =
        M'' ∖ (A ∪es B)
        , Hide-keep (A ∪es B) P (λ { (inj₁ x) → ¬cA x ; (inj₂ x) → ¬cB x }) Pev
        , combine A B M''
fwd-ev A B P (sRet eqf) =
  deadlock , Hide-√ (A ∪es B) P (fHide-ret-inv A P (fHide-ret-inv B (P ∖ A) eqf)) , sbisim-refl deadlock

fwd-tau : (A B : EventSet) (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
        → ((P ∖ A) ∖ B) ─[ τ ]─► M
        → Σ[ M′ ∈ PTree E (ExtI E) R ] ((P ∖ (A ∪es B)) ─[ τ ]─► M′) × (M ∼ M′)
fwd-tau A B P step with Hide-τ-elim B (P ∖ A) step
... | hτP M' Pτ refl with Hide-τ-elim A P Pτ
...   | hτP M'' Pτ′ refl     = M'' ∖ (A ∪es B) , Hide-τ (A ∪es B) P Pτ′ , combine A B M''
...   | hτH M'' cA Pev refl  = M'' ∖ (A ∪es B) , Hide-hidden (A ∪es B) P (inj₁ cA) Pev , combine A B M''
fwd-tau A B P step | hτH M' cB (sVis eqf' br') refl with hide-hVis-inv A P eqf' br'
...   | heV M'' ¬cA Pev      = M'' ∖ (A ∪es B) , Hide-hidden (A ∪es B) P (inj₂ cB) Pev , combine A B M''

-- backward: a move of P∖(A∪B) is matched by (P∖A)∖B.
bwd-ev : (A B : EventSet) (P : PTree E (ExtI E) R) {l : Event√ R} {M : PTree E (ExtI E) R}
       → (P ∖ (A ∪es B)) ─[ ev l ]─► M
       → Σ[ M′ ∈ PTree E (ExtI E) R ] (((P ∖ A) ∖ B) ─[ ev l ]─► M′) × (M ∼ M′)
bwd-ev A B P (sVis eqf br) with hide-hVis-inv (A ∪es B) P eqf br
... | heV M'' ¬cAB Pev =
      (M'' ∖ A) ∖ B
      , Hide-keep B (P ∖ A) (λ x → ¬cAB (inj₂ x)) (Hide-keep A P (λ x → ¬cAB (inj₁ x)) Pev)
      , combineR A B M''
bwd-ev A B P (sRet eqf) =
  deadlock , Hide-√ B (P ∖ A) (fHide-ret A P (fHide-ret-inv (A ∪es B) P eqf)) , sbisim-refl deadlock

bwd-tau : (A B : EventSet) (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
        → (P ∖ (A ∪es B)) ─[ τ ]─► M
        → Σ[ M′ ∈ PTree E (ExtI E) R ] (((P ∖ A) ∖ B) ─[ τ ]─► M′) × (M ∼ M′)
bwd-tau A B P step with Hide-τ-elim (A ∪es B) P step
... | hτP M'' Pτ refl = (M'' ∖ A) ∖ B , Hide-τ B (P ∖ A) (Hide-τ A P Pτ) , combineR A B M''
... | hτH {B = C} {e = e} {a = a} M'' cAB Pev refl with cAB
...   | inj₁ cA = (M'' ∖ A) ∖ B , Hide-τ B (P ∖ A) (Hide-hidden A P cA Pev) , combineR A B M''
...   | inj₂ cB with EventSet.dec A (C , e) a
...     | yes cA  = (M'' ∖ A) ∖ B , Hide-τ B (P ∖ A) (Hide-hidden A P cA Pev) , combineR A B M''
...     | no  ¬cA = (M'' ∖ A) ∖ B , Hide-hidden B (P ∖ A) cB (Hide-keep A P ¬cA Pev) , combineR A B M''

combine  A B P .Sbisim.fwd .SSimF.on-ev  = fwd-ev  A B P
combine  A B P .Sbisim.fwd .SSimF.on-tau = fwd-tau A B P
combine  A B P .Sbisim.bwd .SSimF.on-ev  = bwd-ev  A B P
combine  A B P .Sbisim.bwd .SSimF.on-tau = bwd-tau A B P
combineR A B P .Sbisim.fwd .SSimF.on-ev  = bwd-ev  A B P
combineR A B P .Sbisim.fwd .SSimF.on-tau = bwd-tau A B P
combineR A B P .Sbisim.bwd .SSimF.on-ev  = fwd-ev  A B P
combineR A B P .Sbisim.bwd .SSimF.on-tau = fwd-tau A B P

-- hide-combine (T3.3):  (P ∖ A) ∖ B ≈FD P ∖ (A ∪ B)
hide-combine-FD : (A B : EventSet) (P : PTree E (ExtI E) R) → ((P ∖ A) ∖ B) ≈FD (P ∖ (A ∪es B))
hide-combine-FD A B P = drbisim→≈FD (sbisim→drbisim (combine A B P))

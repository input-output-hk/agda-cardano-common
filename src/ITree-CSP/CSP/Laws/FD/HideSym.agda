{-# OPTIONS --guardedness #-}

-- Hide-sym (T3.2 / U5.2):  (P ∖ Y) ∖ X ≈FD (P ∖ X) ∖ Y.
--
-- Derived from hide-combine + the fact that `X ∪ Y` and `Y ∪ X` hide the same events:
--   (P∖A)∖B ≈FD P∖(A∪B) ≈FD P∖(B∪A) ≈FD (P∖B)∖A.
-- The middle step is `hide-mem-cong`: hiding respects membership-equivalence of EventSets
-- (a strong bisimulation — an event is kept/hidden by A iff by A′).  `hide-mem-cong` is
-- self-dual (bwd = fwd with the sets swapped and the equivalence flipped) and reusable.

open import Level using (Level; suc; _⊔_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.FD.HideSym {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS   {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}
open import Semantics.FailuresDivergences {E = E} {I = ExtI E} using (_≈FD_; ≈FD-trans; ≈FD-sym; ≈FD-setoid)
import Relation.Binary.Reasoning.Setoid as SetoidReasoning
open import Semantics.StrongImpliesDR {E = E} {I = ExtI E} using (sbisim→drbisim)
open import Semantics.DRImpliesFD     {E = E} {I = ExtI E} using (drbisim→≈FD)
open import CSP.Laws.Traces.TraceLawsHide E-≟
  using (Hide-τ; Hide-keep; Hide-hidden; Hide-√; Hide-τ-elim; HideτR; hτP; hτH
        ; hide-hVis-inv; HideevR; heV; he√; fHide-ret-inv)
open import CSP.Laws.Traces.TraceLawsHideAlg E-≟ using (_∪es_)
open import CSP.Laws.FD.HideCombine E-≟ using (hide-combine-FD)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- membership-equivalence of two EventSets
MemEq : EventSet → EventSet → Set (suc ℓ ⊔ ℓe)
MemEq A A' = (at : AnyTypes E) (a : proj₁ at)
           → (EventSet.mem A at a → EventSet.mem A' at a) × (EventSet.mem A' at a → EventSet.mem A at a)

flip-eq : {A A' : EventSet} → MemEq A A' → MemEq A' A
flip-eq eqv at a = proj₂ (eqv at a) , proj₁ (eqv at a)

-- the bisimulation: hiding equivalent sets gives bisimilar trees.
hide-mem-cong : (A A' : EventSet) → MemEq A A' → (P : PTree E (ExtI E) R) → (P ∖ A) ∼ (P ∖ A')

-- one-directional simulation (P∖A simulated by P∖A′); bwd reuses it with sets swapped.
cong-ev : (A A' : EventSet) (eqv : MemEq A A') (P : PTree E (ExtI E) R)
          {l : Event√ R} {M : PTree E (ExtI E) R}
        → (P ∖ A) ─[ ev l ]─► M
        → Σ[ M′ ∈ PTree E (ExtI E) R ] ((P ∖ A') ─[ ev l ]─► M′) × (M ∼ M′)
cong-ev A A' eqv P (sVis eqf br) with hide-hVis-inv A P eqf br
... | heV {B} {e} {a} M'' ¬cA Pev =
      M'' ∖ A' , Hide-keep A' P (λ x → ¬cA (proj₂ (eqv (B , e) a) x)) Pev , hide-mem-cong A A' eqv M''
cong-ev A A' eqv P (sRet eqf) = deadlock , Hide-√ A' P (fHide-ret-inv A P eqf) , sbisim-refl deadlock

cong-tau : (A A' : EventSet) (eqv : MemEq A A') (P : PTree E (ExtI E) R) {M : PTree E (ExtI E) R}
         → (P ∖ A) ─[ τ ]─► M
         → Σ[ M′ ∈ PTree E (ExtI E) R ] ((P ∖ A') ─[ τ ]─► M′) × (M ∼ M′)
cong-tau A A' eqv P step with Hide-τ-elim A P step
... | hτP M'' Pτ refl            = M'' ∖ A' , Hide-τ A' P Pτ , hide-mem-cong A A' eqv M''
... | hτH {B} {e} {a} M'' cA Pev refl =
      M'' ∖ A' , Hide-hidden A' P (proj₁ (eqv (B , e) a) cA) Pev , hide-mem-cong A A' eqv M''

hide-mem-cong A A' eqv P .Sbisim.fwd .SSimF.on-ev  = cong-ev  A A' eqv P
hide-mem-cong A A' eqv P .Sbisim.fwd .SSimF.on-tau = cong-tau A A' eqv P
hide-mem-cong A A' eqv P .Sbisim.bwd .SSimF.on-ev  = cong-ev  A' A (flip-eq {A = A} {A' = A'} eqv) P
hide-mem-cong A A' eqv P .Sbisim.bwd .SSimF.on-tau = cong-tau A' A (flip-eq {A = A} {A' = A'} eqv) P

hide-mem-cong-FD : (A A' : EventSet) → MemEq A A' → (P : PTree E (ExtI E) R) → (P ∖ A) ≈FD (P ∖ A')
hide-mem-cong-FD A A' eqv P = drbisim→≈FD (sbisim→drbisim (hide-mem-cong A A' eqv P))

-- (A ∪ B) and (B ∪ A) have the same membership (⊎-swap).
∪es-comm-eq : (A B : EventSet) → MemEq (A ∪es B) (B ∪es A)
∪es-comm-eq A B at a = swap , swap
  where swap : {X Y : Set} → X ⊎ Y → Y ⊎ X
        swap (inj₁ x) = inj₂ x
        swap (inj₂ y) = inj₁ y

-- hide-sym (T3.2):  (P ∖ A) ∖ B ≈FD (P ∖ B) ∖ A
hide-sym-FD : (A B : EventSet) (P : PTree E (ExtI E) R) → ((P ∖ A) ∖ B) ≈FD ((P ∖ B) ∖ A)
hide-sym-FD {R = R} A B P = begin
  (P ∖ A) ∖ B       ≈⟨ hide-combine-FD A B P ⟩
  P ∖ (A ∪es B)     ≈⟨ hide-mem-cong-FD (A ∪es B) (B ∪es A) (∪es-comm-eq A B) P ⟩
  P ∖ (B ∪es A)     ≈⟨ hide-combine-FD B A P ⟨
  (P ∖ B) ∖ A       ∎
  where open SetoidReasoning (≈FD-setoid R)

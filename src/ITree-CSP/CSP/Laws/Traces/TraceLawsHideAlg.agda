{-# OPTIONS --guardedness #-}

-- SPIKE: algebraic trace laws for hiding (Roscoe UCS), at trace equivalence ≈T (a pair
-- of ⊑T inclusions).  Built on the HideTr de-hiding relation + Hide-trace-elim/intro.
--   Hide-∅-≈T      : P ∖ ∅ ≈T P                       (hiding nothing is identity)
--   Hide-∪-≈T      : (P ∖ cs) ∖ ds ≈T P ∖ (cs ∪ ds)   (hiding combines — exercises the
--                    nested-hiding τ-namespace fix end to end)
-- No postulates, no NON_TERMINATING.

open import Level using (Level)
open import Data.List using (List; []; _∷_)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax; proj₁; proj₂)
open import Function using (case_of_)
open import Relation.Nullary using (Dec; ¬_; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsHideAlg {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators               E-≟
open EventSet
open import Semantics.LTS                    {E = E} {I = ExtI E}
open import Semantics.Failures               {E = E} {I = ExtI E}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟ using (deadlock-no-τ; deadlock-no-ev)
open import CSP.Laws.Traces.TraceLawsHide          E-≟
  using (HideTr; hnil; hkeep; hdrop; h√; Hide-trace-elim; Hide-trace-intro;
         Hide-τ; Hide-keep; Hide-√)

private
  variable
    ℓr : Level
    R  : Set ℓr
    A B : EventSet

-------------------------------------------------------------------------------------
-- a little set algebra on the hidden EventSets (event-level)
-------------------------------------------------------------------------------------

∅es : EventSet
∅es .mem _ _ = ⊥
∅es .dec _ _ = no (λ z → z)

_∪es_ : EventSet → EventSet → EventSet
(A ∪es B) .mem at a = A .mem at a ⊎ B .mem at a
(A ∪es B) .dec at a with A .dec at a | B .dec at a
... | yes p | _      = yes (inj₁ p)
... | no _  | yes q  = yes (inj₂ q)
... | no ¬p | no ¬q  = no λ { (inj₁ p) → ¬p p ; (inj₂ q) → ¬q q }

-------------------------------------------------------------------------------------
-- Hide-∅ : hiding the empty set is the identity (at ≈T)
-------------------------------------------------------------------------------------

-- with A = ∅ nothing is ever dropped, so the de-hiding relation is the identity
HideTr-∅-≡ : {s' s : List (Event√ R)} → HideTr ∅es s' s → s' ≡ s
HideTr-∅-≡ hnil          = refl
HideTr-∅-≡ (hkeep _ h)   = cong (_ ∷_) (HideTr-∅-≡ h)
HideTr-∅-≡ (hdrop () _)
HideTr-∅-≡ h√            = refl

-- (P ∖ ∅) ⊑T P : re-hide a P-trace with nothing hidden (every event kept)
hide-∅-intro : (P : PTree E (ExtI E) R) {s : List (Event√ R)} {P' : PTree E (ExtI E) R}
             → P ⟹⟨ s ⟩ P' → traces (P ∖ ∅es) s
hide-∅-intro P ⟹-refl = (P ∖ ∅es) , ⟹-refl
hide-∅-intro P (⟹-τ Pτ rest) =
  case hide-∅-intro _ rest of λ where
    (Rt , bs) → Rt , ⟹-τ (Hide-τ ∅es P Pτ) bs
hide-∅-intro P (⟹-ev (sVis eqf veq) rest) =
  case hide-∅-intro _ rest of λ where
    (Rt , bs) → Rt , ⟹-ev (Hide-keep ∅es P (λ ()) (sVis eqf veq)) bs
hide-∅-intro P (⟹-ev (sRet eqf) rest) =
  case rest of λ where
    ⟹-refl      → deadlock , ⟹-ev (Hide-√ ∅es P eqf) ⟹-refl
    (⟹-τ st _)  → ⊥-elim (deadlock-no-τ st)
    (⟹-ev st _) → ⊥-elim (deadlock-no-ev st)

Hide-∅-⊑ : (P : PTree E (ExtI E) R) → (P ∖ ∅es) ⊑T P
Hide-∅-⊑ P s (_ , bs) = hide-∅-intro P bs

Hide-∅-⊒ : (P : PTree E (ExtI E) R) → P ⊑T (P ∖ ∅es)
Hide-∅-⊒ P s (_ , bs) with Hide-trace-elim ∅es P bs
... | s' , P' , rP , h with HideTr-∅-≡ h
...   | refl = P' , rP

Hide-∅-≈T : (P : PTree E (ExtI E) R)
          → ((P ∖ ∅es) ⊑T P) × (P ⊑T (P ∖ ∅es))
Hide-∅-≈T P = Hide-∅-⊑ P , Hide-∅-⊒ P

-------------------------------------------------------------------------------------
-- Hide-combine : (P ∖ A) ∖ B ≈T P ∖ (A ∪ B)
-------------------------------------------------------------------------------------

-- composing two de-hidings = de-hiding the union (deletes A-events then B-events)
HideTr-compose : {a b c : List (Event√ R)}
               → HideTr A a b → HideTr B b c → HideTr (A ∪es B) a c
HideTr-compose hnil          hnil           = hnil
HideTr-compose (hkeep ¬cs h1) (hkeep ¬ds h2) =
  hkeep (λ { (inj₁ p) → ¬cs p ; (inj₂ q) → ¬ds q }) (HideTr-compose h1 h2)
HideTr-compose (hkeep ¬cs h1) (hdrop dse h2) = hdrop (inj₂ dse) (HideTr-compose h1 h2)
HideTr-compose (hdrop cse h1) h2             = hdrop (inj₁ cse) (HideTr-compose h1 h2)
HideTr-compose h√            h√             = h√

-- splitting a union de-hiding (decide A-membership to attribute each dropped event)
HideTr-split : (A : EventSet) {a c : List (Event√ R)}
             → HideTr (A ∪es B) a c
             → Σ[ b ∈ List (Event√ R) ] HideTr A a b × HideTr B b c
HideTr-split A hnil = [] , hnil , hnil
HideTr-split A (hkeep ¬cd h) with HideTr-split A h
... | b , h1 , h2 = _ ∷ b , hkeep (λ p → ¬cd (inj₁ p)) h1 , hkeep (λ q → ¬cd (inj₂ q)) h2
HideTr-split A (hdrop {B = B} {e = e} {a = a} cd h) with A .dec (B , e) a
... | yes cse with HideTr-split A h
...   | b , h1 , h2 = b , hdrop cse h1 , h2
HideTr-split A (hdrop {B = B} {e = e} {a = a} cd h) | no ¬cse with HideTr-split A h
...   | b , h1 , h2 = _ ∷ b , hkeep ¬cse h1 ,
                      hdrop (case cd of λ { (inj₁ p) → ⊥-elim (¬cse p) ; (inj₂ q) → q }) h2
HideTr-split A h√ = _ ∷ [] , h√ , h√

Hide-∪-⊑ : (P : PTree E (ExtI E) R) (A B : EventSet)
         → (P ∖ (A ∪es B)) ⊑T ((P ∖ A) ∖ B)
Hide-∪-⊑ P A B s (_ , bs)
  with Hide-trace-elim B (P ∖ A) bs
... | s' , Q' , rQ , hds with Hide-trace-elim A P rQ
...   | s'' , P'' , rP , hcs =
        Hide-trace-intro (A ∪es B) P rP (HideTr-compose hcs hds)

Hide-∪-⊒ : (P : PTree E (ExtI E) R) (A B : EventSet)
         → ((P ∖ A) ∖ B) ⊑T (P ∖ (A ∪es B))
Hide-∪-⊒ P A B s (_ , bs)
  with Hide-trace-elim (A ∪es B) P bs
... | s'' , P'' , rP , hcd with HideTr-split A hcd
...   | s' , hcs , hds with Hide-trace-intro A P rP hcs
...     | Q' , rQ = Hide-trace-intro B (P ∖ A) rQ hds

Hide-∪-≈T : (P : PTree E (ExtI E) R) (A B : EventSet)
          → (((P ∖ A) ∖ B) ⊑T (P ∖ (A ∪es B)))
          × ((P ∖ (A ∪es B)) ⊑T ((P ∖ A) ∖ B))
Hide-∪-≈T P A B = Hide-∪-⊒ P A B , Hide-∪-⊑ P A B

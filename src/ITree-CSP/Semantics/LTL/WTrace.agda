{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_; Lift) renaming (suc to lsuc)
open import Data.Product using (Σ; _×_; _,_)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; subst)

open import Process_Trees hiding (div)

module Semantics.LTL.WTrace
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open PTree

open import Semantics.LTS              {ℓ} {ℓe} {ℓi} {E} {I} hiding (Diverges)
open import Semantics.WeakBisim        {ℓ} {ℓe} {ℓi} {E} {I} using (_═[_]═►_; _─[τ*]─►_)
open import Semantics.DRBisim          {ℓ} {ℓe} {ℓi} {E} {I} using (Diverges)
open import Semantics.Deadlock         {ℓ} {ℓe} {ℓi} {E} {I} using (IsStuck)
open import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I}
  using (Frame; LTLᵗ; ⊤'; atom; ¬_; _∧_; X_; _U_)

mutual
  data WTrace {ℓr : Level} (R : Set ℓr) : PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
    step  : ∀ {t : PTree E I R} {e : Event√ R} {t′ : PTree E I R}
          → t ═[ ev e ]═► t′ → ∞WTrace R t′ → WTrace R t
    done  : ∀ {t u : PTree E I R} {r : R}
          → t ─[τ*]─► u → PTree.force u ≡ ret r → WTrace R t
    stuck : ∀ {t u : PTree E I R}
          → t ─[τ*]─► u → IsStuck u → WTrace R t
    div   : ∀ {t : PTree E I R}
          → Diverges t → WTrace R t

  record ∞WTrace {ℓr : Level} (R : Set ℓr) (t : PTree E I R)
               : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
    coinductive
    field force : WTrace R t

open ∞WTrace public

frameOf : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} → WTrace R t → Frame R
frameOf (step {t} {e} _ _)        = Frame.step  t e
frameOf (done {u = u} {r = r} _ _) = Frame.done  u r
frameOf (stuck {u = u} _ _)        = Frame.stuck u
frameOf (div {t} _)                = Frame.div   t

IsTermᵂ : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} → WTrace R t → Set
IsTermᵂ (step  _ _) = ⊥
IsTermᵂ (done  _ _) = ⊤
IsTermᵂ (stuck _ _) = ⊤
IsTermᵂ (div   _)   = ⊤

tailIdx : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} → WTrace R t → PTree E I R
tailIdx (step {t′ = t′} _ _) = t′
tailIdx {t = t} (done _ _)   = t
tailIdx {t = t} (stuck _ _)  = t
tailIdx {t = t} (div _)      = t

tail : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
       → (tr : WTrace R t) → WTrace R (tailIdx tr)
tail (step _ tr)     = ∞WTrace.force tr
tail tr@(done _ _)   = tr
tail tr@(stuck _ _)  = tr
tail tr@(div _)      = tr

dropIdx : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R} → ℕ → WTrace R t → PTree E I R
dropIdx {t = t} zero   tr = t
dropIdx        (suc n) tr = dropIdx n (tail tr)

drop : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
       → (n : ℕ) (tr : WTrace R t) → WTrace R (dropIdx n tr)
drop zero    tr = tr
drop (suc n) tr = drop n (tail tr)

tailIdx-stutter : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                    (tr : WTrace R t) → IsTermᵂ tr → tailIdx tr ≡ t
tailIdx-stutter (step _ _)  ()
tailIdx-stutter (done _ _)  _ = refl
tailIdx-stutter (stuck _ _) _ = refl
tailIdx-stutter (div _)     _ = refl

tail-stutter : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                 (tr : WTrace R t) (term : IsTermᵂ tr)
               → tail tr ≡ subst (WTrace R) (sym (tailIdx-stutter tr term)) tr
tail-stutter (done _ _)  _ = refl
tail-stutter (stuck _ _) _ = refl
tail-stutter (div _)     _ = refl

dropIdx-stutter : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                    (n : ℕ) (tr : WTrace R t) → IsTermᵂ tr → dropIdx n tr ≡ t
dropIdx-stutter zero    tr          term = refl
dropIdx-stutter (suc n) (done p eq)  term = dropIdx-stutter n (done p eq)  term
dropIdx-stutter (suc n) (stuck p st) term = dropIdx-stutter n (stuck p st) term
dropIdx-stutter (suc n) (div dv)     term = dropIdx-stutter n (div dv)     term

drop-stutter : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                 (n : ℕ) (tr : WTrace R t) (term : IsTermᵂ tr)
               → drop n tr ≡ subst (WTrace R) (sym (dropIdx-stutter n tr term)) tr
drop-stutter zero    tr          term = refl
drop-stutter (suc n) (done p eq)  term = drop-stutter n (done p eq)  term
drop-stutter (suc n) (stuck p st) term = drop-stutter n (stuck p st) term
drop-stutter (suc n) (div dv)     term = drop-stutter n (div dv)     term

⟦_⟧ᵂ : ∀ {ℓr ℓa} {R : Set ℓr} {t : PTree E I R}
      → LTLᵗ ℓa R → WTrace R t → Set ℓa
⟦_⟧ᵂ {ℓa = ℓa} ⊤'      tr = Lift ℓa ⊤
⟦ atom P  ⟧ᵂ tr = P (frameOf tr)
⟦_⟧ᵂ {ℓa = ℓa} (¬ φ)   tr = ⟦ φ ⟧ᵂ tr → Lift ℓa ⊥
⟦ φ ∧ ψ   ⟧ᵂ tr = ⟦ φ ⟧ᵂ tr × ⟦ ψ ⟧ᵂ tr
⟦ X φ     ⟧ᵂ tr = ⟦ φ ⟧ᵂ (tail tr)
⟦ φ U ψ   ⟧ᵂ tr = Σ ℕ (λ n → ⟦ ψ ⟧ᵂ (drop n tr)
                           × (∀ m → m < n → ⟦ φ ⟧ᵂ (drop m tr)))

_⊨ᵂ_ : ∀ {ℓr ℓa} {R : Set ℓr}
       → (t : PTree E I R) → LTLᵗ ℓa R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓa)
t ⊨ᵂ φ = ∀ (tr : WTrace _ t) → ⟦ φ ⟧ᵂ tr

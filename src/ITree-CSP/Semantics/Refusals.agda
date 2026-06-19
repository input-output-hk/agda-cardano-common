{-# OPTIONS --guardedness #-}

-- SPIKE: a refusals layer on the pure-react LTS — now possible because `isStable`
-- is a real predicate.  A STABLE state refuses an event set it offers nothing from;
-- the canonical fact proved here is that `deadlock` (= Stop) refuses everything.

open import Level using (Level; _⊔_) renaming (suc to lsuc)
open import Data.Product using (Σ; _,_; _×_; Σ-syntax)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module Semantics.Refusals {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where
open PTree
open import Semantics.LTS {ℓ} {ℓe} {ℓi} {E} {I}

-- t offers (can immediately perform) the visible event e
Offers : ∀ {ℓr} {R : Set ℓr} → PTree E I R → Event√ R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Offers {R = R} t e = Σ[ t′ ∈ PTree E I R ] (t ─[ ev e ]─► t′)

-- a STABLE t refuses the event-set X: it is stable and offers nothing in X
Refuses : ∀ {ℓr ℓx} {R : Set ℓr}
        → PTree E I R → (Event√ R → Set ℓx) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓx)
Refuses t X = isStable t × (∀ e → X e → ¬ Offers t e)

-- deadlock is stable (its τc is everywhere nothing)…
deadlock-stable : ∀ {ℓr} {R : Set ℓr} → isStable {E = E} {I = I} {R = R} deadlock
deadlock-stable _ _ = refl

-- …and offers no event…
deadlock-no-offer : ∀ {ℓr} {R : Set ℓr} {e} {t′ : PTree E I R}
                  → ¬ (deadlock ─[ ev e ]─► t′)
deadlock-no-offer (sRet ())
deadlock-no-offer (sVis refl ())

-- …so it refuses EVERY set (the maximally-refusing process).
deadlock-refuses : ∀ {ℓr ℓx} {R : Set ℓr} {X : Event√ R → Set ℓx} → Refuses deadlock X
deadlock-refuses = deadlock-stable , λ e _ (_ , step) → deadlock-no-offer step

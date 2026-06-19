{-# OPTIONS --guardedness #-}

-- SPIKE: a CSP law proved against the pure-react definitions, via the LTS-based
-- strong bisimulation.  Demonstrator: internal-choice commutativity  P ⊓ Q ∼ Q ⊓ P.

open import Level using (Level; Lift; lift; _⊔_) renaming (suc to lsuc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (_,_)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees

module CSP.Laws.Bisim.Laws {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟
open import Semantics.LTS  {E = E} {I = ExtI E}
open import Semantics.Bisim {E = E} {I = ExtI E}

-- the two τ-successors of an internal choice (the fin-indexed br2 branches)
⊓-stepL : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) → (P ⊓ Q) ─[ τ ]─► P
⊓-stepL P Q = sTau {i = Lift ℓ (Fin 2) , fin} {a = lift fzero} refl refl

⊓-stepR : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) → (P ⊓ Q) ─[ τ ]─► Q
⊓-stepR P Q = sTau {i = Lift ℓ (Fin 2) , fin} {a = lift (fsuc fzero)} refl refl

-- every τ-move out of P ⊓ Q lands on P or on Q
⊓-τ-inv : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) {t : PTree E (ExtI E) R}
        → (P ⊓ Q) ─[ τ ]─► t → (t ≡ P) ⊎ (t ≡ Q)
⊓-τ-inv P Q (sSil ())
⊓-τ-inv P Q (sTau {i = _ , base _}   refl ())
⊓-τ-inv P Q (sTau {i = _ , pair _ _} refl ())
⊓-τ-inv P Q (sTau {i = _ , fin} {a = lift fzero}           refl refl) = inj₁ refl
⊓-τ-inv P Q (sTau {i = _ , fin} {a = lift (fsuc fzero)}    refl refl) = inj₂ refl
⊓-τ-inv P Q (sTau {i = _ , fin} {a = lift (fsuc (fsuc _))} refl ())

-- internal choice is commutative (up to strong bisimulation)
⊓-comm : ∀ {ℓr} {R : Set ℓr} (P Q : PTree E (ExtI E) R) → (P ⊓ Q) ∼ (Q ⊓ P)
⊓-comm P Q .Sbisim.fwd .SSimF.on-ev (sVis refl ())
⊓-comm P Q .Sbisim.fwd .SSimF.on-tau step with ⊓-τ-inv P Q step
... | inj₁ refl = P , ⊓-stepR Q P , sbisim-refl P
... | inj₂ refl = Q , ⊓-stepL Q P , sbisim-refl Q
⊓-comm P Q .Sbisim.bwd .SSimF.on-ev (sVis refl ())
⊓-comm P Q .Sbisim.bwd .SSimF.on-tau step with ⊓-τ-inv Q P step
... | inj₁ refl = Q , ⊓-stepR P Q , sbisim-refl Q
... | inj₂ refl = P , ⊓-stepL P Q , sbisim-refl P

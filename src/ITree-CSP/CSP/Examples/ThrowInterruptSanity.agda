{-# OPTIONS --guardedness #-}

-- Sanity checks (reduction / refl-style) for throw (_⟦_▷_) and interrupt (_△_)
-- operators, plus a chanSet round-trip check.  Every check is proved by refl.

open import Level using (Lift; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Empty using (⊥)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ-syntax; _,_; proj₁)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Examples.ThrowInterruptSanity where
open PTree

-- Two channels: evA and evB, each carrying ⊤.
data Ev : Set → Set where
  evA evB : Ev ⊤

Ev-≟ : (x y : AnyTypes Ev) → Dec (x ≡ y)
Ev-≟ (_ , evA) (_ , evA) = yes refl
Ev-≟ (_ , evB) (_ , evB) = yes refl
Ev-≟ (_ , evA) (_ , evB) = no λ ()
Ev-≟ (_ , evB) (_ , evA) = no λ ()

open import CSP.Operators Ev-≟

Rr : Set
Rr = Poly.⊤ {lzero}

instance
  DecEq-Rr : DecEq Rr
  DecEq-Rr = record { _≟_ = λ _ _ → yes refl }

-- Helper to read the visible continuation out of an react node.
visCont : NodeKind Ev (ExtI Ev) Rr
        → (bt : AnyTypes Ev) → proj₁ bt → Maybe (PTree Ev (ExtI Ev) Rr)
visCont (react v _) = v
visCont _          = λ _ _ → nothing

------------------------------------------------------------------------
-- Concrete processes used in the checks.
-- R₀ = evB ⟶₀ Stop,  S₀ = Stop,  Q = Skip
------------------------------------------------------------------------

R₀ : PTree Ev (ExtI Ev) Rr
R₀ = evB ⟶₀ Stop

S₀ : PTree Ev (ExtI Ev) Rr
S₀ = Stop

Q : PTree Ev (ExtI Ev) Rr
Q = Skip

------------------------------------------------------------------------
-- EventSets: Aset = {evA}, Aset' = {evB}
------------------------------------------------------------------------

-- Aset: channel evA only
isA : AnyTypes Ev → Set
isA (_ , evA) = ⊤
isA (_ , evB) = ⊥

isA-dec : (at : AnyTypes Ev) → Dec (isA at)
isA-dec (_ , evA) = yes tt
isA-dec (_ , evB) = no (λ ())

Aset : EventSet
Aset = chanSet isA isA-dec

-- Aset': channel evB only
isB : AnyTypes Ev → Set
isB (_ , evA) = ⊥
isB (_ , evB) = ⊤

isB-dec : (at : AnyTypes Ev) → Dec (isB at)
isB-dec (_ , evA) = no (λ ())
isB-dec (_ , evB) = yes tt

Aset' : EventSet
Aset' = chanSet isB isB-dec

------------------------------------------------------------------------
-- Check 1: Throw fires on an A-event.
-- a ∈ Aset  ⇒  the evA-offer of  force ((evA ⟶₀ R₀) ⟦ Aset ▷ Q)
--                                 is  just Q  (control transferred).
------------------------------------------------------------------------

check-throw-fires : visCont (force ((evA ⟶₀ R₀) ⟦ Aset ▷ Q)) (⊤ , evA) tt ≡ just Q
check-throw-fires = refl

------------------------------------------------------------------------
-- Check 2: Throw passes a non-A event.
-- a ∉ Aset'  ⇒  the evA-offer of  force ((evA ⟶₀ R₀) ⟦ Aset' ▷ Q)
--                                  is  just (R₀ ⟦ Aset' ▷ Q)  (continue).
------------------------------------------------------------------------

check-throw-passes : visCont (force ((evA ⟶₀ R₀) ⟦ Aset' ▷ Q)) (⊤ , evA) tt
                   ≡ just (R₀ ⟦ Aset' ▷ Q)
check-throw-passes = refl

------------------------------------------------------------------------
-- Check 3: Throw and P-√.
-- Skip = Ret tt, so force Skip = ret tt,
-- ⇒  force (Skip ⟦ Aset ▷ Q)  ≡  ret tt  (no throw on termination).
------------------------------------------------------------------------

check-throw-skip : force (Skip ⟦ Aset ▷ Q) ≡ ret Poly.tt
check-throw-skip = refl

------------------------------------------------------------------------
-- Check 4: Interrupt continues on P-event.
-- The evA-offer of  force ((evA ⟶₀ R₀) △ (evB ⟶₀ S₀))
-- is  just (R₀ △ (evB ⟶₀ S₀))  (P-event, P′ wrapped).
------------------------------------------------------------------------

check-interrupt-P : visCont (force ((evA ⟶₀ R₀) △ (evB ⟶₀ S₀))) (⊤ , evA) tt
                  ≡ just (R₀ △ (evB ⟶₀ S₀))
check-interrupt-P = refl

------------------------------------------------------------------------
-- Check 5: Interrupt fires on Q-event.
-- The evB-offer of  force ((evA ⟶₀ R₀) △ (evB ⟶₀ S₀))
-- is  just S₀  (interrupt fires, P discarded).
------------------------------------------------------------------------

check-interrupt-Q : visCont (force ((evA ⟶₀ R₀) △ (evB ⟶₀ S₀))) (⊤ , evB) tt
                  ≡ just S₀
check-interrupt-Q = refl

------------------------------------------------------------------------
-- Check 6: Interrupt and P-√.
-- Skip = Ret tt, so force Skip = ret tt  ⇒
--   force (Skip △ Q)  ≡  react ∅v (br2 Skip Q)   (= Skip ⊓ Q: nondeterministic
--   terminate-or-interrupt, NOT simply ret tt).
-- Sub-checks 6a/6b confirm the two τ-branches of br2:
--   tag fzero  → just Skip   (terminate: P-√ wins)
--   tag (fsuc fzero) → just Q   (interrupt: Q wins)
------------------------------------------------------------------------

check-interrupt-skip : force (Skip △ Q) ≡ react ∅v (br2 Skip Q)
check-interrupt-skip = refl

check-interrupt-skip-tau0 : br2 Skip Q (Lift lzero (Fin 2) , fin) (lift fzero) ≡ just Skip
check-interrupt-skip-tau0 = refl

check-interrupt-skip-tau1 : br2 Skip Q (Lift lzero (Fin 2) , fin) (lift (fsuc fzero)) ≡ just Q
check-interrupt-skip-tau1 = refl

------------------------------------------------------------------------
-- Check 7: chanSet round-trip.
-- For any EventSet built via chanSet cs d, the dec field at (at , x)
-- agrees with d at (up to definitional equality).
------------------------------------------------------------------------

check-chanSet : ∀ (cs : AnyTypes Ev → Set) (d : (at : AnyTypes Ev) → Dec (cs at))
                  (at : AnyTypes Ev) (x : proj₁ at)
              → (chanSet cs d) .EventSet.dec at x ≡ d at
check-chanSet cs d at x = refl

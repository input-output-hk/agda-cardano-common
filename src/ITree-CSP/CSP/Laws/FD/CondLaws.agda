{-# OPTIONS --guardedness #-}

-- Conditional choice  P ◁ b ▷ Q = if b then P else Q  (TPC/UCS §1.17–1.22).
-- All laws hold by casing the boolean condition + reflexivity; the two distributive
-- laws collapse one branch to a duplicated ⊓, discharged by ⊓-idem.

open import Level using (Level)
open import Data.Bool using (Bool; true; false)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_)
open import Class.DecEq using (DecEq)

open import Process_Trees

module CSP.Laws.FD.CondLaws {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators E-≟ using (_◁_▷_; _⊓_; _□_)
open import Semantics.FailuresDivergences {E = E} {I = ExtI E}
  using (_≈FD_; ≈FD-refl; ≈FD-sym)
open import CSP.Laws.FD.FDLawsIChoice E-≟ using (⊓-idem-FD)

private
  variable
    ℓr : Level
    R  : Set ℓr

-- ◁true-id (T1.20):  P ◁ true ▷ Q = P
◁true-id : (P Q : PTree E (ExtI E) R) → (P ◁ true ▷ Q) ≈FD P
◁true-id P Q = ≈FD-refl P

-- ◁false-id (T1.21):  P ◁ false ▷ Q = Q
◁false-id : (P Q : PTree E (ExtI E) R) → (P ◁ false ▷ Q) ≈FD Q
◁false-id P Q = ≈FD-refl Q

-- ◁-idem (T1.17):  P ◁ b ▷ P = P
◁-idem : (b : Bool) (P : PTree E (ExtI E) R) → (P ◁ b ▷ P) ≈FD P
◁-idem true  P = ≈FD-refl P
◁-idem false P = ≈FD-refl P

-- ◁-dist-l (T1.18):  (P ⊓ Q) ◁ b ▷ S = (P ◁ b ▷ S) ⊓ (Q ◁ b ▷ S)
◁-dist-l : (b : Bool) (P Q S : PTree E (ExtI E) R)
         → ((P ⊓ Q) ◁ b ▷ S) ≈FD ((P ◁ b ▷ S) ⊓ (Q ◁ b ▷ S))
◁-dist-l true  P Q S = ≈FD-refl (P ⊓ Q)
◁-dist-l false P Q S = ≈FD-sym (⊓-idem-FD S)

-- ◁-dist-r (T1.19):  S ◁ b ▷ (P ⊓ Q) = (S ◁ b ▷ P) ⊓ (S ◁ b ▷ Q)
◁-dist-r : (b : Bool) (S P Q : PTree E (ExtI E) R)
         → (S ◁ b ▷ (P ⊓ Q)) ≈FD ((S ◁ b ▷ P) ⊓ (S ◁ b ▷ Q))
◁-dist-r true  S P Q = ≈FD-sym (⊓-idem-FD S)
◁-dist-r false S P Q = ≈FD-refl (P ⊓ Q)

-- ◁-□-dist (T1.22):  P □ (Q ◁ b ▷ S) = (P □ Q) ◁ b ▷ (P □ S)
◁-□-dist : ⦃ _ : DecEq R ⦄ (b : Bool) (P Q S : PTree E (ExtI E) R)
         → (P □ (Q ◁ b ▷ S)) ≈FD ((P □ Q) ◁ b ▷ (P □ S))
◁-□-dist true  P Q S = ≈FD-refl (P □ Q)
◁-□-dist false P Q S = ≈FD-refl (P □ S)

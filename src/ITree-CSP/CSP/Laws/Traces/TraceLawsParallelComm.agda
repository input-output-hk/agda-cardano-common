{-# OPTIONS --guardedness #-}

-- SPIKE: parallel commutativity AT THE TRACE LEVEL, up to flipping the merge.
-- The generalised Par is not literally commutative (ret|ret ⇒ merge r₁ r₂ is asymmetric),
-- but Par A merge P Q and Par A (flip merge) Q P have the SAME traces:
-- de-interleaving (ParInter) is symmetric — psoloL ↔ psoloR, and p√ matches because
-- flip merge r₂ r₁ = merge r₁ r₂.  So no operational symmetry (bisimulation) is needed;
-- the trace equivalence falls straight out of Par-trace-elim + ParInter-sym + Par-trace-intro.
--
-- The CSP instance Par⊤ (merge = λ _ _ → tt) has flip merge = merge definitionally, so
-- Par⊤ A P Q ≈T Par⊤ A Q P is the immediate specialisation.

open import Level using (Level)
open import Data.List using (List)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_; _×_; proj₁; proj₂)
open import Relation.Nullary using (Dec; ¬_; no)
open import Relation.Binary.PropositionalEquality using (_≡_)

open import Process_Trees

module CSP.Laws.Traces.TraceLawsParallelComm {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where
open PTree

open import CSP.Operators               E-≟
open EventSet
open import Semantics.LTS                    {E = E} {I = ExtI E}
open import Semantics.Failures               {E = E} {I = ExtI E} using (traces; _⊑T_)
open import CSP.Laws.Traces.TraceLawsParallel      E-≟ using (Mg)
open import CSP.Laws.Traces.TraceLawsParallelTrace E-≟
  using (ParInter; pnil; psync; psoloL; psoloR; p√; Par-trace-elim)
open import CSP.Laws.Traces.TraceLawsParallelMono  E-≟ using (Par-trace-intro)

private
  variable
    ℓ₁ ℓ₂ ℓs : Level
    R₁ : Set ℓ₁
    R₂ : Set ℓ₂
    R  : Set ℓs

-------------------------------------------------------------------------------------
-- the interleaving relation is symmetric (swap operands, flip the merge)
-------------------------------------------------------------------------------------

ParInter-sym : (A : EventSet) (merge : Mg R₁ R₂ R)
                 {sP : List (Event√ R₁)} {sQ : List (Event√ R₂)} {s : List (Event√ R)}
             → ParInter A merge sP sQ s
             → ParInter A (λ r₂ r₁ → merge r₁ r₂) sQ sP s
ParInter-sym A merge pnil           = pnil
ParInter-sym A merge (psync csat r) = psync csat (ParInter-sym A merge r)
ParInter-sym A merge (psoloL ¬cs r) = psoloR ¬cs (ParInter-sym A merge r)
ParInter-sym A merge (psoloR ¬cs r) = psoloL ¬cs (ParInter-sym A merge r)
ParInter-sym A merge p√             = p√

-------------------------------------------------------------------------------------
-- trace commutativity: traces (Par merge P Q) ⊆ traces (Par (flip merge) Q P)
-- (i.e. (Par (flip merge) Q P) ⊑T (Par merge P Q), since ⊑T is ⊇ on traces)
-------------------------------------------------------------------------------------

Par-comm-⊑ : (A : EventSet) (merge : Mg R₁ R₂ R)
               (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
           → (Par A (λ r₂ r₁ → merge r₁ r₂) Q P) ⊑T (Par A merge P Q)
Par-comm-⊑ A merge P Q s (_ , bs) with Par-trace-elim A merge P Q bs
... | sP , sQ , P' , Q' , rP , rQ , inter =
      Par-trace-intro A (λ r₂ r₁ → merge r₁ r₂) Q P rQ rP (ParInter-sym A merge inter)

-- trace equivalence (both inclusions); the reverse reuses Par-comm-⊑ at the flipped merge
Par-comm-≈T : (A : EventSet) (merge : Mg R₁ R₂ R)
                (P : PTree E (ExtI E) R₁) (Q : PTree E (ExtI E) R₂)
            → ((Par A (λ r₂ r₁ → merge r₁ r₂) Q P) ⊑T (Par A merge P Q))
            × ((Par A merge P Q) ⊑T (Par A (λ r₂ r₁ → merge r₁ r₂) Q P))
Par-comm-≈T A merge P Q =
  Par-comm-⊑ A merge P Q , Par-comm-⊑ A (λ r₂ r₁ → merge r₁ r₂) Q P

-------------------------------------------------------------------------------------
-- CSP specialisations: here flip merge = merge definitionally (merge = λ _ _ → tt),
-- so these are genuine (self-)commutativities of synchronised parallel / interleaving.
-------------------------------------------------------------------------------------

-- synchronised parallel on the EventSet A (R₁ = R₂ = R = ⊤)
Par⊤-comm : ∀ {ℓr} (A : EventSet)
              (P Q : PTree E (ExtI E) (⊤ {ℓr}))
          → ((Q ∥⇘ A ⇙ P) ⊑T (P ∥⇘ A ⇙ Q))
          × ((P ∥⇘ A ⇙ Q) ⊑T (Q ∥⇘ A ⇙ P))
Par⊤-comm A P Q = Par-comm-≈T A (λ _ _ → tt) P Q

-- interleaving (empty synchronisation set)
⦀-comm : ∀ {ℓr} (P Q : PTree E (ExtI E) (⊤ {ℓr}))
       → ((Q ⦀ P) ⊑T (P ⦀ Q)) × ((P ⦀ Q) ⊑T (Q ⦀ P))
⦀-comm P Q = Par-comm-≈T ∅ES (λ _ _ → tt) P Q

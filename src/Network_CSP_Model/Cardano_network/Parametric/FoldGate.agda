{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — the fold-gate regression module.
--
-- Task 4's system fold over an arbitrary topology dispatches on `⦀Fin⁺`
-- reducing to the right-nested `⦀` term "on the nose" (by `refl`, no
-- proof needed). This module pins the three definitional facts the
-- campaign's four-node instantiation already relies on, as a permanent
-- regression test: a later refactor of `⦀Fin⁺`/`⦀⁺` in `CSP.Operators`
-- that silently breaks these `refl`s would otherwise only be discovered
-- deep inside Task 4's proof, far from the actual cause.
------------------------------------------------------------------------

open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.List using (_∷_; [])
open import Data.Unit.Polymorphic using (⊤)
open import Relation.Nullary using (Dec)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees using (PTree; AnyTypes; ExtI)

module CSP.Examples.Cardano_network.Parametric.FoldGate
  {ℓ ℓe} {E : Set ℓ → Set ℓe}
  (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y)) where

open import CSP.Operators E-≟ using (_⦀_; ⦀Fin; ⦀Fin⁺; ⦀⁺; Skip)

-- THE GATE: the non-empty fold over four components is the right-nested term on the nose
gate : ∀ {ℓr} (f : Fin 4 → PTree E (ExtI E) (⊤ {ℓr}))
     → ⦀Fin⁺ 3 f ≡ (f fzero ⦀ (f (fsuc fzero) ⦀ (f (fsuc (fsuc fzero)) ⦀ f (fsuc (fsuc (fsuc fzero))))))
gate f = refl

-- CONTRAST: the original `⦀Fin` does NOT have that property — it carries a trailing `Skip`,
-- which is precisely why `⦀Fin⁺` had to be introduced rather than reusing `⦀Fin`
contrast : ∀ {ℓr} (f : Fin 4 → PTree E (ExtI E) (⊤ {ℓr}))
         → ⦀Fin 4 f ≡ (f fzero ⦀ (f (fsuc fzero) ⦀ (f (fsuc (fsuc fzero)) ⦀ (f (fsuc (fsuc (fsuc fzero))) ⦀ Skip))))
contrast f = refl

-- the list fold at two elements is exactly `P ⦀ Q` — what a degree-2 node's `linkBundles` needs
gate⁺ : ∀ {ℓr} (P Q : PTree E (ExtI E) (⊤ {ℓr}))
      → ⦀⁺ P (Q ∷ []) ≡ (P ⦀ Q)
gate⁺ P Q = refl

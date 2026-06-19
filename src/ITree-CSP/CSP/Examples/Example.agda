{-# OPTIONS --guardedness #-}

-- SPIKE: smoke test — the react-only CSP operators compose for a concrete alphabet.

open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (_,_)
open import Data.Empty using (⊥)
open import Data.Bool using (Bool; true; false)
open import Level using (0ℓ)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq; DecEq-⊥)

open import Process_Trees
import CSP.Operators as Extc

module CSP.Examples.Example where

  data Ch : Set → Set where
    a : Ch ⊤
    b : Ch ⊤

  Ch-≟ : (x y : AnyTypes Ch) → Dec (x ≡ y)
  Ch-≟ (_ , a) (_ , a) = yes refl
  Ch-≟ (_ , b) (_ , b) = yes refl
  Ch-≟ (_ , a) (_ , b) = no λ ()
  Ch-≟ (_ , b) (_ , a) = no λ ()

  open Extc Ch-≟

  -- prefix + external choice (□ needs DecEq on the return type)
  P : PTree Ch (ExtI Ch) ⊥
  P = _□_ {{DecEq-⊥}} (a ⟶₀ Stop) (b ⟶₀ Stop)

  -- prefix + internal choice (witness-free)
  Q : PTree Ch (ExtI Ch) (⊤ {0ℓ})
  Q = (a ⟶₀ Skip) ⊓ (b ⟶₀ Skip)

  -- sliding / timeout
  S : PTree Ch (ExtI Ch) (⊤ {0ℓ})
  S = (a ⟶₀ Skip) ▷ Skip

  -- sequential composition  (first operand's return type is discarded ⇒ pin it)
  T : PTree Ch (ExtI Ch) (⊤ {0ℓ})
  T = (a ⟶₀ Skip {0ℓ}) >> (b ⟶₀ Skip)

  -- nested: prefix into a choice, then bind
  U : PTree Ch (ExtI Ch) (⊤ {0ℓ})
  U = (a ⟶₀ (Skip {0ℓ} ⊓ (b ⟶₀ Skip {0ℓ}))) >> Skip

  -- a concrete sync set: hide / sync on channel `a`
  csa : AnyTypes Ch → Set
  csa (_ , a) = ⊤ {0ℓ}
  csa (_ , b) = ⊥
  deca : (at : AnyTypes Ch) → Dec (csa at)
  deca (_ , a) = yes tt
  deca (_ , b) = no (λ z → z)

  -- hiding `a` turns it into an internal τ
  H : PTree Ch (ExtI Ch) (⊤ {0ℓ})
  H = (a ⟶₀ (b ⟶₀ Skip)) ∖ chanSet csa deca

  -- interleaving (no synchronisation)
  V : PTree Ch (ExtI Ch) (⊤ {0ℓ})
  V = (a ⟶₀ Skip) ⦀ (b ⟶₀ Skip)

  -- parallel synchronising on `a` (both must offer `a` together)
  W : PTree Ch (ExtI Ch) (⊤ {0ℓ})
  W = Par⊤ (chanSet csa deca) (a ⟶₀ Skip) (a ⟶₀ Skip)

  -- iteration: non-stateful forever loop
  L : PTree Ch (ExtI Ch) (⊤ {0ℓ})
  L = loop0 (a ⟶₀ Skip)

  -- stateful forever loop (Bool state, flipped each pass)
  Lstate : PTree Ch (ExtI Ch) (⊤ {0ℓ})
  Lstate = loop (λ b → a ⟶₀ Ret b) true

  -- while loop: do `a` once, then stop (body returns false, cond is identity)
  Lwhile : PTree Ch (ExtI Ch) Bool
  Lwhile = while (λ b → b) (λ _ → a ⟶₀ Ret false) true

  -- the stability predicate is now real (not a ⊤/⊥ placeholder):
  -- Stop = react ∅ ∅ has an everywhere-`nothing` τc, hence is provably stable.
  Stop-stable : isStable (Stop {R = ⊤ {0ℓ}})
  Stop-stable _ _ = refl

{-# OPTIONS --guardedness #-}

-- Regression test for the Hide τ-namespace fix (CSP.Operators hide-hTau tag0/tag1 split).
-- BEFORE the fix the base index was overloaded, so re-hiding a channel DROPPED the
-- inner hidden-event τ (Hide-τ was false; (R ∖ a) ∖ a lost traces).  AFTER the fix
-- hiding propagates P's τ's UNCONDITIONALLY (tag0), so the doubly-hidden process still
-- makes the inner τ-move — witnessed here through the proven Hide-hidden / Hide-τ.

open import Data.Unit.Polymorphic using (⊤; tt)
open import Level using (0ℓ)
open import Relation.Nullary using (Dec; yes)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Data.Product using (_,_)

open import Process_Trees
import CSP.Operators as Extc

module CSP.Laws.Traces.HideRegression where
  open PTree

  data Ch : Set → Set where
    a : Ch (⊤ {0ℓ})

  Ch-≟ : (x y : AnyTypes Ch) → Dec (x ≡ y)
  Ch-≟ (_ , a) (_ , a) = yes refl

  open Extc Ch-≟
  open import Semantics.LTS {E = Ch} {I = ExtI Ch}
  open import CSP.Laws.Traces.TraceLawsHide Ch-≟ using (Hide-hidden; Hide-τ)

  csa : AnyTypes Ch → Set
  csa (_ , a) = ⊤ {0ℓ}
  deca : (at : AnyTypes Ch) → Dec (csa at)
  deca (_ , a) = yes tt

  -- recover the channel-level set as an event-level EventSet via chanSet
  Aa : EventSet
  Aa = chanSet csa deca

  R : PTree Ch (ExtI Ch) (⊤ {0ℓ})
  R = a ⟶₀ Skip

  -- R offers `a`, stepping to Skip
  R-does-a : R ─[ ev (evl (evLabel (⊤ {0ℓ}) a tt)) ]─► Skip
  R-does-a = sVis refl refl

  -- hiding `a` turns R's visible `a` into a τ:  (R ∖ a) ─[ τ ]─► (Skip ∖ a)
  P-step : (R ∖ Aa) ─[ τ ]─► (Skip ∖ Aa)
  P-step = Hide-hidden Aa R tt R-does-a

  -- THE FIX: re-hiding `a` PRESERVES that τ (the old operator dropped it entirely).
  re-hidden : ((R ∖ Aa) ∖ Aa) ─[ τ ]─► ((Skip ∖ Aa) ∖ Aa)
  re-hidden = Hide-τ Aa (R ∖ Aa) P-step

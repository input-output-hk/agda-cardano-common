{-# OPTIONS --guardedness #-}

open import Level using (Level; _⊔_; Lift; lift) renaming (suc to lsuc)
open import Data.Product using (_×_; _,_)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; sym)

open import Process_Trees hiding (div)

module Semantics.LTL.FrameSim
  {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open PTree

open import Semantics.LTS              {ℓ} {ℓe} {ℓi} {E} {I}
open import Semantics.DRBisim          {ℓ} {ℓe} {ℓi} {E} {I} using (_≈DR_; drbisim-sym)
open import Semantics.LTL.Traces_Based {ℓ} {ℓe} {ℓi} {E} {I}

FrameSim : ∀ {ℓr} {R : Set ℓr} → Frame R → Frame R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
FrameSim {ℓr} {R} (Frame.step  t₁ e₁) (Frame.step  t₂ e₂) = (e₁ ≡ e₂) × (t₁ ≈DR t₂)
FrameSim {ℓr} {R} (Frame.done  t₁ r₁) (Frame.done  t₂ r₂) = (r₁ ≡ r₂) × (t₁ ≈DR t₂)
FrameSim {ℓr} {R} (Frame.stuck t₁)    (Frame.stuck t₂)    = t₁ ≈DR t₂
FrameSim {ℓr} {R} (Frame.div   t₁)    (Frame.div   t₂)    = t₁ ≈DR t₂
FrameSim {ℓr} {R} (Frame.step  _ _) (Frame.done  _ _) = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
FrameSim {ℓr} {R} (Frame.step  _ _) (Frame.stuck _)   = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
FrameSim {ℓr} {R} (Frame.step  _ _) (Frame.div   _)   = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
FrameSim {ℓr} {R} (Frame.done  _ _) (Frame.step  _ _) = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
FrameSim {ℓr} {R} (Frame.done  _ _) (Frame.stuck _)   = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
FrameSim {ℓr} {R} (Frame.done  _ _) (Frame.div   _)   = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
FrameSim {ℓr} {R} (Frame.stuck _)   (Frame.step  _ _) = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
FrameSim {ℓr} {R} (Frame.stuck _)   (Frame.done  _ _) = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
FrameSim {ℓr} {R} (Frame.stuck _)   (Frame.div   _)   = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
FrameSim {ℓr} {R} (Frame.div   _)   (Frame.step  _ _) = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
FrameSim {ℓr} {R} (Frame.div   _)   (Frame.done  _ _) = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
FrameSim {ℓr} {R} (Frame.div   _)   (Frame.stuck _)   = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥

FrameSim-sym : ∀ {ℓr} {R : Set ℓr} {fr₁ fr₂ : Frame R}
             → FrameSim fr₁ fr₂ → FrameSim fr₂ fr₁
FrameSim-sym {fr₁ = Frame.step  _ _} {Frame.step  _ _} (e , b) = sym e , drbisim-sym b
FrameSim-sym {fr₁ = Frame.done  _ _} {Frame.done  _ _} (r , b) = sym r , drbisim-sym b
FrameSim-sym {fr₁ = Frame.stuck _}   {Frame.stuck _}   b       = drbisim-sym b
FrameSim-sym {fr₁ = Frame.div   _}   {Frame.div   _}   b       = drbisim-sym b
FrameSim-sym {fr₁ = Frame.step  _ _} {Frame.done  _ _} (lift ())
FrameSim-sym {fr₁ = Frame.step  _ _} {Frame.stuck _}   (lift ())
FrameSim-sym {fr₁ = Frame.step  _ _} {Frame.div   _}   (lift ())
FrameSim-sym {fr₁ = Frame.done  _ _} {Frame.step  _ _} (lift ())
FrameSim-sym {fr₁ = Frame.done  _ _} {Frame.stuck _}   (lift ())
FrameSim-sym {fr₁ = Frame.done  _ _} {Frame.div   _}   (lift ())
FrameSim-sym {fr₁ = Frame.stuck _}   {Frame.step  _ _} (lift ())
FrameSim-sym {fr₁ = Frame.stuck _}   {Frame.done  _ _} (lift ())
FrameSim-sym {fr₁ = Frame.stuck _}   {Frame.div   _}   (lift ())
FrameSim-sym {fr₁ = Frame.div   _}   {Frame.step  _ _} (lift ())
FrameSim-sym {fr₁ = Frame.div   _}   {Frame.done  _ _} (lift ())
FrameSim-sym {fr₁ = Frame.div   _}   {Frame.stuck _}   (lift ())

data BisimStable {ℓr ℓa} {R : Set ℓr} : LTLᵗ ℓa R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓa) where
  bs-⊤    : BisimStable ⊤'
  bs-atom : ∀ {P : FramePred ℓa R}
          → (∀ {fr₁ fr₂ : Frame R} → FrameSim fr₁ fr₂ → P fr₁ → P fr₂)
          → BisimStable (atom P)
  bs-¬    : ∀ {φ}   → BisimStable φ                → BisimStable (¬ φ)
  bs-∧    : ∀ {φ ψ} → BisimStable φ → BisimStable ψ → BisimStable (φ ∧ ψ)
  bs-X    : ∀ {φ}   → BisimStable φ                → BisimStable (X φ)
  bs-U    : ∀ {φ ψ} → BisimStable φ → BisimStable ψ → BisimStable (φ U ψ)

{-
  This module defines a labelled transition system (LTS) for ITree with various transition relations.
-}

{-# OPTIONS --guardedness #-}

-- open import Agda.Builtin.Nat
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Fin using (Fin; remQuot) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing) renaming (map to mapMaybe)
open import Data.Empty using (⊥)
-- open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_; ∃; Σ-syntax; ∃-syntax)
-- open import Relation.Unary
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)
open import Relation.Binary                using (Rel)
-- open import Relation.Binary.Definitions using (DecidableEquality)
open import Class.DecEq
open import Level using (Level; 0ℓ)
open import Relation.Nullary using (Dec; yes; no)
open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Bool using (Bool; true; false; if_then_else_)


open import Data.List using (List; _++_; _∷_; []; length; reverse; map; foldr; downFrom)
-- open import Data.List.Relation.Unary.All using (All; []; _∷_)
-- import  Data.List.Relation.Unary.Any using (Any; here;there)
-- import Data.List.Membership.Propositional using (_∈_)
-- import Data.List.Properties using (reverse-++-commute; map-compose; map-++-commute; foldr-++; map-is-foldr)

open import Interaction_Trees
open import ITree_Relations.LTS using (Label; ev; τ; _─[_]─►_; sSil;
  _─[τ^_]─►_; τ^-zero; τ^-suc)

module ITree_Relations.Divergence
  {ℓ ℓe ℓi ℓr : Level}
  {E : Set ℓ → Set ℓe}
  {I : Set ℓ → Set ℓi}
  {R : Set ℓr}
  where
  
open ITree

-- P stabilises if there exists some P' reachable by finitely many taus,
-- where P' is stable (no further tau transitions possible)
Stabilises : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           → ITree E I R → Set _
Stabilises P = ∃[ P' ] ∃[ n ] P ─[τ^ n ]─► P' × isStable P'
{-
stabilises P = Σ (ITree _ _ _) λ P' →
               Σ ℕ             λ n  →
               P ─[τ^ n ]─► P' × isStable P'
-}

-- Smart constructor: package up the evidence
stabilises : ∀ {ℓ ℓe ℓi ℓr}
               {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {P : ITree E I R}
               (P'   : ITree E I R)
               (n    : ℕ)
             → P ─[τ^ n ]─► P'
             → isStable P'
             → Stabilises P
stabilises P' n steps stable = P' , n , steps , stable

-- Already-stable trees trivially stabilise in 0 steps
stabilises-now : ∀ {ℓ ℓe ℓi ℓr}
                   {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                   {P : ITree E I R}
               → isStable P → Stabilises P
stabilises-now {P = P} st = stabilises P 0 τ^-zero st

-- If P -[τ]→ P' and P' stabilises, then so does P
stabilises-step : ∀ {ℓ ℓe ℓi ℓr}
                    {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                    {P P' : ITree E I R}
                → force P ≡ sil P'
                → Stabilises P'
                → Stabilises P
stabilises-step eq (P'' , n , steps , stable) =
  stabilises P'' (suc n) (τ^-suc eq steps) stable

-- (ret v) always stabiliese
stabilises-ret : ∀ {ℓ ℓe ℓi ℓr}
                   {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                   (v : R) → Stabilises {E = E} {I = I} (itree (ret v))
stabilises-ret v = itree (ret v) , 0 , τ^-zero , tt


record Divergent (P : ITree E I R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    next    : ITree E I R
    step    : P ─[ τ ]─► next
    diverge : Divergent next

open Divergent

div-diverges : Divergent div
div-diverges .next    = div
div-diverges .step    = sSil refl
div-diverges .diverge = div-diverges

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
open import Data.Unit.Polymorphic using (⊤; tt)
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

module ITree_Relations.LTS -- {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where
open ITree

-- Event labels are visible.
record EvLabel {ℓ ℓe : Level} (E : Set ℓ → Set ℓe) : Set (lsuc ℓ ⊔ ℓe) where
  constructor evLabel
  field
    A : Set ℓ
    e : E A
    a : A

data Label {ℓ ℓe : Level} (E : Set ℓ → Set ℓe) : Set (lsuc ℓ ⊔ ℓe) where
  ev   : EvLabel E → Label E   -- visible event with response
  τ  : Label E                  -- silent step from inv
--  √  : Label E                -- successful termination at ret

-- Small-step semantics
data _─[_]─►_ {ℓ ℓe ℓi ℓr : Level}
              {E : Set ℓ → Set ℓe}
              {I : Set ℓ → Set ℓi}
              {R : Set ℓr}
    : ITree E I R → Label E → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  sSil : ∀ {p t : ITree E I R}
       → ITree.force p ≡ sil t
       ---------------------------------------------
       → p ─[ τ ]─► t
    
  sVis : ∀ {A  : Set ℓ}
         {f  : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
         {e  : E A}
         {a  : A}
         {t′ : ITree E I R}
       → f (A , e) a ≡ just t′
       ---------------------------------------------
       → itree (vis f) ─[ ev (evLabel A e a) ]─► t′

  sInv : ∀ {f  : (at : AnyTypes I) → ContinueType at (Maybe (ITree E I R))}
         {A  : Set ℓ}
         {i  : I A}
         {a  : A}
         {t′ : ITree E I R}
       → f (A , i) a ≡ just t′
       ---------------------------------------------
       → itree (inv f) ─[ τ ]─► t′

-- This relation denotes a ITree t' is reachable from t via n transitions, including τ
data _─[^_]─►_ {ℓ ℓe ℓi ℓr : Level}
               {E : Set ℓ → Set ℓe}
               {I : Set ℓ → Set ℓi}
               {R : Set ℓr}
             : ITree E I R → ℕ → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  ^-zero : {t : ITree E I R}
         → t ─[^ zero ]─► t

  ^-suc  : {t t′ t″ : ITree E I R}
           {l : Label E}
           {n : ℕ}
         → t  ─[ l  ]─► t′
         → t′ ─[^ n ]─► t″
         → t  ─[^ suc n ]─► t″

-- This relation denotes a ITree t' is reachable from t via n τs.
data _─[τ^_]─►_ {ℓ ℓe ℓi ℓr : Level}
               {E : Set ℓ → Set ℓe}
               {I : Set ℓ → Set ℓi}
               {R : Set ℓr}
             : ITree E I R → ℕ → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  τ^-zero : {t : ITree E I R}
         ------------------------
         → t ─[τ^ zero ]─► t

  τ^-suc  : {t t′ t″ : ITree E I R}
            {n : ℕ}
         → ITree.force t ≡ sil t′ -- t steps silently to t'
         → t′ ─[τ^ n ]─► t″
         ------------------------
         → t  ─[τ^ suc n ]─► t″

-- This relation denotes a ITree t' is reachable from t via any number of τs.
data _─[τ*]─►_ {ℓ ℓe ℓi ℓr : Level}
               {E : Set ℓ → Set ℓe}
               {I : Set ℓ → Set ℓi}
               {R : Set ℓr}
             : ITree E I R → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  τ*-zero : {t : ITree E I R}
         ------------------------
         → t ─[τ*]─► t

  _τ*-step_  : {t t′ t″ : ITree E I R}
         → ITree.force t ≡ sil t′ -- t steps silently to t'
         → t′ ─[τ*]─► t″
         ------------------------
         → t  ─[τ*]─► t″

-- Finite sequence of silent steps: t reduces to t' via taus
{-
data _⇒*_ {ℓ ℓe ℓi ℓr}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        : Rel (ITree E I R) (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  ε    : ∀ {t}           → t ⇒* t
  _◅τ_ : ∀ {t t' t''}
       → ITree.force t ≡ sil t'   -- t steps silently to t'
       → t' ⇒* t''
       → t  ⇒* t''
-}

-- A set of reachable ITrees from P after n steps.
Reachₙ : ∀ {ℓ ℓe ℓi ℓr : Level}
          {E : Set ℓ → Set ℓe}
          {I : Set ℓ → Set ℓi}
          {R : Set ℓr}
        → ITree E I R → ℕ → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Reachₙ t n = Σ[ t′ ∈ ITree _ _ _ ] (t ─[^ n ]─► t′)

-- Big-step semantics: transitions through a sequence of events, including τ in traces
data _─⟨_⟩─►_ {ℓ ℓe ℓi ℓr : Level}
              {E : Set ℓ → Set ℓe}
              {I : Set ℓ → Set ℓi}
              {R : Set ℓr}
    : ITree E I R → List (Label E) → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  bNil : ∀{t : ITree E I R} → t ─⟨ [] ⟩─► t
  
  -- bRet  : ∀{r : R}
  --      → itree (ret r) ─⟨ √ ∷ [] ⟩─► r

  bStep : {l  : Label E}
          {ls : List (Label E)}
          {r  : R}
          {t  : ITree E I R}
          {t′ : ITree E I R}
          {t′′ : ITree E I R}
        → t  ─[ l ]─► t′
        → t′ ─⟨ ls ⟩─► t′′
       ---------------------------------------------        
        → t  ─⟨ l ∷ ls ⟩─► t′′

-- Big-step semantics: transitions through a sequence of events, excluding τ in traces
data _═⟨_⟩═►_ {ℓ ℓe ℓi ℓr : Level}
              {E : Set ℓ → Set ℓe}
              {I : Set ℓ → Set ℓi}
              {R : Set ℓr}
    : ITree E I R
    → List (EvLabel E)
    → ITree E I R
    → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  bNil : ∀{t : ITree E I R} → t ═⟨ [] ⟩═► t
  
--  bRet  : {r : R}
--        → itree (ret r) ═⟨ √ ∷ [] ⟩═► r
  bTau :  {els : List (EvLabel E)}
          {t  : ITree E I R}
          {t′ : ITree E I R}
          {t′′ : ITree E I R}
        → t  ─[ τ ]─► t′
        → t′ ═⟨ els ⟩═► t′′
       ---------------------------------------------        
        → t  ═⟨ els ⟩═► t′′
        
  bStep : {el  : EvLabel E}
          {els : List (EvLabel E)}
          {t  : ITree E I R}
          {t′ : ITree E I R}
          {t′′ : ITree E I R}
        → t  ─[ ev el ]─► t′
        → t′ ═⟨ els ⟩═► t′′
       ---------------------------------------------        
        → t  ═⟨ el ∷ els ⟩═► t′′

module Traces where
  -- Traces can be extracted from the big-step semantics
  traces : ∀ {ℓ ℓe ℓi ℓr : Level} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → ITree E I R → List (EvLabel E) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
  traces t s = Σ[ t′ ∈ ITree _ _ _ ] (t ═⟨ s ⟩═► t′)

  _⊑ᵀ_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → ITree E I R → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
  P ⊑ᵀ Q = ∀ {s} → traces Q s → traces P s


{-
  This module defines a labelled transition system (LTS) for ITree with various transition relations.
-}

{-# OPTIONS --guardedness #-}

-- open import Agda.Builtin.Nat
open import Data.Nat using (ℕ; zero; suc; _+_; _*_; _^_; _∸_)
open import Data.Fin using (Fin; remQuot) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing; Is-just) renaming (map to mapMaybe)
open import Data.Empty using (⊥)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; ∃; Σ-syntax; ∃-syntax)
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
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym; trans; refl; inspect; [_]; cong)

open import Interaction_Trees

module ITree_Relations.LTS -- {ℓ ℓe} {E : Set ℓ → Set ℓe} (E-≟ : (x y : AnyTypes E) → Dec (x ≡ y))
  where
open ITree

-----------------------------------------------------------------
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

-----------------------------------------------------------------
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

{-
  sVis : ∀ {A  : Set ℓ}
         {f  : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
         {e  : E A}
         {a  : A}
         {t′ : ITree E I R}
       → f (A , e) a ≡ just t′
       -- → ITree.force t ≡ vis f
       ---------------------------------------------
       → itree (vis f) ─[ ev (evLabel A e a) ]─► t′
-}       

{-
  sInv : ∀ {f  : (at : AnyTypes I) → ContinueType at (Maybe (ITree E I R))}
         {A  : Set ℓ}
         {i  : I A}
         {a  : A}
         {t′ : ITree E I R}
         {p : Is-just {lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr} (f (A , i) a)}
       → f (A , i) a ≡ just t′
       ---------------------------------------------
       → itree (inv f (A , i) a p) ─[ τ ]─► t′
-}
  sVis : ∀ {p : ITree E I R}
         {f  : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
         {at  : AnyTypes E}
         {a  : proj₁ at}
         {t′ : ITree E I R}
       → ITree.force p ≡ vis f
       → f at a ≡ just t′       
       ---------------------------------------------
       → p ─[ ev (evLabel (proj₁ at) (proj₂ at) a) ]─► t′

{-
  sInv : ∀ {p : ITree E I R}
         {f  : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
         {i  : AnyTypes I}
         {a  : proj₁ i}
         {prf : Is-just {lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr} (f i a)}
         {t′ : ITree E I R}         
       → ITree.force p ≡ inv f i a prf
       → f i a ≡ just t′
       ---------------------------------------------
       → p ─[ τ ]─► t′
-}

  sInv : ∀ {p : ITree E I R}
       {f   : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
       {wi  : AnyTypes I} {wa  : proj₁ wi} {prf : Is-just (f wi wa)}  -- stored witness (non-emptiness)
       {i   : AnyTypes I} {a   : proj₁ i}                              -- branch actually taken
       {t′  : ITree E I R}
     → ITree.force p ≡ inv f wi wa prf   -- p is an inv node
     → f i a ≡ just t′                   -- ANY branch (i, a) can be taken
     → p ─[ τ ]─► t′

-----------------------------------------------------------------------
-- A τ inversion
--   if a τ transition, it could be a sil transition, or a inv transition
{-
τ-inv :
  ∀ {ℓ ℓe ℓi ℓr}
    {E : Set ℓ → Set ℓe}
    {I : Set ℓ → Set ℓi}
    {R : Set ℓr}
    {t t′ : ITree E I R}
  → t ─[ τ ]─► t′
  → (Σ[ u ∈ ITree E I R ] (ITree.force t ≡ sil u × t′ ≡ u))
  ⊎ (Σ[ f ∈ ((i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))) ]
     Σ[ i ∈ AnyTypes I ]
     Σ[ a ∈ proj₁ i ]
       Σ[ p ∈ Is-just {lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr} (f i a) ]
       (ITree.force t ≡ inv f i a p × f i a ≡ just t′))
τ-inv (sSil eq) =
  inj₁ (_ , (eq , refl))

τ-inv (sInv {f = f} {i = i} {a = a} {prf = prf} eq1 eq2 ) =
  inj₂ (f , i , a , prf , (eq1 , eq2))
-}

-- An ev inversion
--   if an ev transition, it must be vis
ev-inv : ∀ {ℓ ℓe ℓi ℓr}
    {E : Set ℓ → Set ℓe}
    {I : Set ℓ → Set ℓi}
    {R : Set ℓr}
    {t t′ : ITree E I R}
    {A : Set ℓ} {e : E A} {a : A}
  → t ─[ ev (evLabel A e a) ]─► t′
  → Σ[ f ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R)))]
      (ITree.force t ≡ vis f × f (A , e) a ≡ just t′)
ev-inv (sVis eq1 eq2) = _ , (eq1 , eq2)

{-
τ-from-force-vis-impossible :
  ∀ {ℓ ℓe ℓi ℓr}
    {E : Set ℓ → Set ℓe}
    {I : Set ℓ → Set ℓi}
    {R : Set ℓr}
    {t t′ : ITree E I R}
    {f : ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R)))}
  → ITree.force t ≡ vis f
  → t ─[ τ ]─► t′
  → ⊥
τ-from-force-vis-impossible force≡vis tr with τ-inv tr
... | inj₁ (u , (force≡sil , _)) =
      vis≢sil (trans (sym force≡vis) force≡sil)

... | inj₂ (f′ , A , i , a , (force≡inv , _)) =
      vis≢inv (trans (sym force≡vis) force≡inv)
-}
{-
ev-from-force-vis-impossible :
  ∀ {ℓ ℓe ℓi ℓr}
    {E : Set ℓ → Set ℓe}
    {I : Set ℓ → Set ℓi}
    {R : Set ℓr}
    {t t′ : ITree E I R}
    {A : Set ℓ} {e : E A} {a : A}    
  → ITree.force t ≡ vis (λ _ _ → nothing)
  → t ─[ ev (evLabel A e a) ]─► t′
  → ⊥
ev-from-force-vis-impossible {A} {e} {a} force≡vis tr with ev-inv tr
... | f′ , (force≡vis′ , step≡just) =
      -- vis-injective gives f ≡ f′
      -- But f = λ _ _ → nothing cannot produce just t′
      let f-eq : (λ _ _ → nothing) ≡ f′
          f-eq = vis-injective (trans (sym force≡vis) force≡vis′)
      in
        -- Apply f′ to the label (A , e) and a: it must be nothing, not just t′
        let contradiction : step≡just ≡ nothing
            contradiction = cong (\g → g (A , e) a) f-eq
        in
        -- now impossible
        ()
-}      
--------------------------------------------------------------------------------------
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

-----------------------------------------------------------------
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

  τ^-inv : {t t′ t″ : ITree E I R}
           {n : ℕ}
         → {f : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
         → {wi : AnyTypes I} {wa : proj₁ wi} {wprf : Is-just (f wi wa)}
         → {i : AnyTypes I} {a : proj₁ i}
         → ITree.force t ≡ inv f wi wa wprf
         → f i a ≡ just t′ 
         → t′ ─[τ^ n ]─► t″
         ------------------------
         → t  ─[τ^ suc n ]─► t″
   
-----------------------------------------------------------------------------
-- This relation denotes a ITree t' is reachable from t via any number of τs.

data _─[τ*]─►_ {ℓ ℓe ℓi ℓr : Level}
               {E : Set ℓ → Set ℓe}
               {I : Set ℓ → Set ℓi}
               {R : Set ℓr}
             : ITree E I R → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  τ*-zero : {t : ITree E I R}
         ------------------------
         → t ─[τ*]─► t

  τ*-step : ∀ {t t' t''}
          → t  ─[ τ ]─► t'
          → t' ─[τ*]─►  t''
          → t  ─[τ*]─►  t''
{-          
  τ*-sil  : {t t′ t″ : ITree E I R}
         → ITree.force t ≡ sil t′ -- t steps silently to t'
         → t′ ─[τ*]─► t″
         ------------------------
         → t  ─[τ*]─► t″

  -- Step via 'inv' constructor (The invisible choice)
  τ*-inv : {t t′ t″ : ITree E I R}
    → {f : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
    → {i : AnyTypes I} {a : proj₁ i} {prf : Is-just (f i a)}
    → ITree.force t ≡ inv f i a prf
    → f i a ≡ just t′
    → t′ ─[τ*]─► t″
    ----------------
    → t ─[τ*]─► t″
-}
-----------------------------------------------------------------
-- A set of reachable ITrees from P after n steps.
Reachₙ : ∀ {ℓ ℓe ℓi ℓr : Level}
          {E : Set ℓ → Set ℓe}
          {I : Set ℓ → Set ℓi}
          {R : Set ℓr}
        → ITree E I R → ℕ → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Reachₙ t n = Σ[ t′ ∈ ITree _ _ _ ] (t ─[^ n ]─► t′)

--------------------------------------------------------------------------------------
-- a weak transition relation
data _═[_]═►_ {ℓ ℓe ℓi ℓr : Level} 
                {E : Set ℓ → Set ℓe} 
                {I : Set ℓ → Set ℓi} 
                {R : Set ℓr}
     : ITree E I R → Label E → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  -- Weak Tau Transition (just the reflexive-transitive closure)
  weak-τ : ∀ {p q}
    → p ─[τ*]─► q 
    -----------------
    → p ═[ τ ]═► q

  -- Weak Visible Transition
  -- p --τ*--> p' --e--> q' --τ*--> q
  weak-ev : ∀ {p q p' q' at a}
    → (p ─[τ*]─► p')
    → (p' ─[ ev (evLabel (proj₁ at) (proj₂ at) a) ]─► q')
    → (q' ─[τ*]─► q)
      -----------------------------------------------
    → p ═[ ev (evLabel (proj₁ at) (proj₂ at) a) ]═► q
    
--------------------------------------------------------------------------------------
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

--------------------------------------------------------------------------------------
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

-----------------------------------------------------------------
module Traces where
  traces′ : ∀ {ℓ ℓe ℓi ℓr : Level} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → ITree E I R → List (Label E) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
  traces′ t s = Σ[ t′ ∈ ITree _ _ _ ] (t ─⟨ s ⟩─► t′)

  -- Traces can be extracted from the big-step semantics
  traces : ∀ {ℓ ℓe ℓi ℓr : Level} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → ITree E I R → List (EvLabel E) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
  traces t s = Σ[ t′ ∈ ITree _ _ _ ] (t ═⟨ s ⟩═► t′)

  _⊑ᵀ_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → ITree E I R → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
  P ⊑ᵀ Q = ∀ {s} → traces Q s → traces P s


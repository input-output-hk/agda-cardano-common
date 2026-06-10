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
open import Relation.Nullary using (Dec; yes; no; ¬_)
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
record Event {ℓ ℓe : Level} (E : Set ℓ → Set ℓe) : Set (lsuc ℓ ⊔ ℓe) where
  constructor evLabel
  field
    A : Set ℓ
    e : E A
    a : A

-- Event includes an extra tick event for termination
data Event√ {ℓ ℓe ℓr : Level} (E : Set ℓ → Set ℓe) (R : Set ℓr) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  evl   : Event E → Event√ E R   -- visible event with response
  √  : R → Event√ E R            -- successful termination at ret
  
data Label {ℓ ℓe ℓr : Level} (E : Set ℓ → Set ℓe) (R : Set ℓr) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓr) where
  ev   : Event√ E R → Label E R   -- visible event with response
  τ  : Label E R                -- silent step from ndbr

-----------------------------------------------------------------
-- Small-step semantics
data _─[_]─►_ {ℓ ℓe ℓi ℓr : Level}
              {E : Set ℓ → Set ℓe}
              {I : Set ℓ → Set ℓi}
              {R : Set ℓr}
    : ITree E I R → Label E R → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  -- we choose deadlock to represent Ω in the Bill Roscoe's UCS book as a terminated process
  sRet : ∀ {p : ITree E I R} {x : R}
       → ITree.force p ≡ ret x
       ---------------------------------------------
       → p ─[ ev (√ x) ]─► deadlock
       
  sSil : ∀ {p t : ITree E I R}
       → ITree.force p ≡ sil t
       ---------------------------------------------
       → p ─[ τ ]─► t

  sVis : ∀ {p : ITree E I R}
         {f  : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
         {at  : AnyTypes E}
         {a  : proj₁ at}
         {t′ : ITree E I R}
       → ITree.force p ≡ vis f
       → f at a ≡ just t′       
       ---------------------------------------------
       → p ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t′

  sNdbr : ∀ {p : ITree E I R}
       {f   : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
       {wi  : AnyTypes I} {wa  : proj₁ wi} {prf : Is-just (f wi wa)}  -- stored witness (non-emptiness)
       {i   : AnyTypes I} {a   : proj₁ i}                              -- branch actually taken
       {t′  : ITree E I R}
     → ITree.force p ≡ ndbr f wi wa prf   -- p is an ndbr node
     → f i a ≡ just t′                   -- ANY branch (i, a) can be taken
     → p ─[ τ ]─► t′

  -- mix: visible offers from its vis-side function
  sMixVis : ∀ {p : ITree E I R}
            {f  : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
            {Qt : ITree E I R}
            {at : AnyTypes E} {a : proj₁ at} {t′ : ITree E I R}
          → ITree.force p ≡ mix f Qt
          → f at a ≡ just t′
          ---------------------------------------------
          → p ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► t′

  -- mix: silent timeout / slide to the fallback subtree
  sMixSlide : ∀ {p : ITree E I R}
              {f  : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
              {Qt : ITree E I R}
            → ITree.force p ≡ mix f Qt
            ---------------------------------------------
            → p ─[ τ ]─► Qt

√-is-ret : ∀ {ℓ ℓe ℓi ℓr : Level}
              {E : Set ℓ → Set ℓe}
              {I : Set ℓ → Set ℓi}
              {R : Set ℓr}
              {t t' : ITree E I R} {x : R}
         → t ─[ ev (√ x) ]─► t'
         → (ITree.force t ≡ ret x) × t' ≡ deadlock
√-is-ret (sRet eq) = eq , refl

-----------------------------------------------------------------------
-- A τ inversion
--   if a τ transition, it could be a sil transition, or a ndbr transition

τ-ndbr :
  ∀ {ℓ ℓe ℓi ℓr}
    {E : Set ℓ → Set ℓe}
    {I : Set ℓ → Set ℓi}
    {R : Set ℓr}
    {t t′ : ITree E I R}
  → t ─[ τ ]─► t′
  → (Σ[ u ∈ ITree E I R ] (ITree.force t ≡ sil u × t′ ≡ u))
  ⊎ (Σ[ f ∈ ((i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))) ]
     Σ[ wi ∈ AnyTypes I ] Σ[ wa ∈ proj₁ wi ] Σ[ prf ∈ Is-just {lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr} (f wi wa) ]
     Σ[ i ∈ AnyTypes I ] Σ[ a ∈ proj₁ i ]
       (ITree.force t ≡ ndbr f wi wa prf × f i a ≡ just t′))
  ⊎ (Σ[ f ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))) ]
     Σ[ Qt ∈ ITree E I R ]
       (ITree.force t ≡ mix f Qt × t′ ≡ Qt))
τ-ndbr (sSil eq) =
  inj₁ (_ , (eq , refl))

τ-ndbr (sNdbr {f = f} {wi = wi} {wa = wa} {prf = prf} {i = i} {a = a} {t′ = t′} eq1 eq2 ) =
  inj₂ (inj₁ (f , wi , wa , prf , i , a , (eq1 , eq2)))

τ-ndbr (sMixSlide {f = f} {Qt = Qt} eq) =
  inj₂ (inj₂ (f , Qt , (eq , refl)))


-- An ev inversion
--   if an ev transition, it must come from either a vis node or a mix node
ev-ndbr : ∀ {ℓ ℓe ℓi ℓr}
    {E : Set ℓ → Set ℓe}
    {I : Set ℓ → Set ℓi}
    {R : Set ℓr}
    {t t′ : ITree E I R}
    {A : Set ℓ} {e : E A} {a : A}
  → t ─[ (ev (evl (evLabel A e a))) ]─► t′
  → (Σ[ f ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R)))]
        (ITree.force t ≡ vis f × f (A , e) a ≡ just t′))
  ⊎ (Σ[ f ∈ ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R)))]
     Σ[ Qt ∈ ITree E I R ]
        (ITree.force t ≡ mix f Qt × f (A , e) a ≡ just t′))
ev-ndbr (sVis eq1 eq2) = inj₁ (_ , (eq1 , eq2))
ev-ndbr (sMixVis eq1 eq2) = inj₂ (_ , _ , (eq1 , eq2))

-- A τ transition is not possible from vis
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
τ-from-force-vis-impossible force≡vis tr with tr
... | sSil force≡sil =
      vis≢sil (trans (sym force≡vis) force≡sil)

... | sNdbr force≡ndbr _ =
      vis≢ndbr (trans (sym force≡vis) force≡ndbr)

... | sMixSlide force≡mix =
      vis≢mix (trans (sym force≡vis) force≡mix)

-- Stop or stuck has no transition
ev-from-force-vis-impossible :
  ∀ {ℓ ℓe ℓi ℓr}
    {E : Set ℓ → Set ℓe}
    {I : Set ℓ → Set ℓi}
    {R : Set ℓr}
    {t t′ : ITree E I R}
    {A : Set ℓ} {e : E A} {a : A}    
  → ITree.force t ≡ vis (λ _ _ → nothing)
  → t ─[ (ev (evl (evLabel A e a))) ]─► t′
  → ⊥
ev-from-force-vis-impossible forceEq (sVis forceEq′ branch-eq)
  with trans (sym forceEq′) forceEq
... | refl = case branch-eq of λ ()
ev-from-force-vis-impossible forceEq (sMixVis force≡mix _) =
  vis≢mix (trans (sym forceEq) force≡mix)

-- No τ transition is possible when force P = ret r
no-τ-from-ret :
  ∀ {ℓ ℓe ℓi ℓr}
    {E : Set ℓ → Set ℓe}
    {I : Set ℓ → Set ℓi}
    {R : Set ℓr}
    {P Q : ITree E I R} {r : R}
  → ITree.force P ≡ ret r
  → P ─[ τ ]─► Q → ⊥
no-τ-from-ret force-ret (sSil eq)      = case trans (sym force-ret) eq of λ ()
no-τ-from-ret force-ret (sNdbr eq _)   = case trans (sym force-ret) eq of λ ()
no-τ-from-ret force-ret (sMixSlide eq) = case trans (sym force-ret) eq of λ ()

-- A state is stuck (real deadlock) when no LTS label is enabled.
IsStuck : ∀ {ℓ ℓe ℓi ℓr}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
IsStuck {E = E} {I = I} {R = R} t =
  ∀ {l : Label E R} {t' : ITree E I R} → t ─[ l ]─► t' → ⊥
  -- ⊥ here is non-polymorphic Data.Empty.⊥ at level 0, which embeds
  -- into the codomain level lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr via _⊔_.

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
           {l : Label E R}
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

  τ^-ndbr : {t t′ t″ : ITree E I R}
           {n : ℕ}
         → {f : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R))}
         → {wi : AnyTypes I} {wa : proj₁ wi} {wprf : Is-just (f wi wa)}
         → {i : AnyTypes I} {a : proj₁ i}
         → ITree.force t ≡ ndbr f wi wa wprf
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
     : ITree E I R → Label E R → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  -- Weak Tau Transition (just the reflexive-transitive closure)
  weak-τ : ∀ {p q}
    → p ─[τ*]─► q 
    -----------------
    → p ═[ τ ]═► q

  -- Weak Visible Transition
  -- p --τ*--> p' --e--> q' --τ*--> q
  {-
  weak-ev : ∀ {p q p' q' at a}
    → (p ─[τ*]─► p')
    → (p' ─[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]─► q')
    → (q' ─[τ*]─► q)
      -----------------------------------------------
    → p ═[ ev (evl (evLabel (proj₁ at) (proj₂ at) a)) ]═► q
  -}

  weak-ev : ∀ {p q p' q'} {e : Event√ E R}
    → (p ─[τ*]─► p')
    → (p' ─[ ev e ]─► q')
    → (q' ─[τ*]─► q)
      -----------------------------------------------
    → p ═[ ev e ]═► q

--------------------------------------------------------------------------------------
-- Big-step semantics: transitions through a sequence of events, including τ in traces
data _─⟨_⟩─►_ {ℓ ℓe ℓi ℓr : Level}
              {E : Set ℓ → Set ℓe}
              {I : Set ℓ → Set ℓi}
              {R : Set ℓr}
    : ITree E I R → List (Label E R) → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  bNil : ∀{t : ITree E I R} → t ─⟨ [] ⟩─► t
  
  bRet  : ∀{t  : ITree E I R} {x : R}
        → t ─[ ev (√ x) ]─► deadlock
        → t ─⟨ ev (√ x) ∷ [] ⟩─► deadlock

  bStep : {l  : Label E R}
          {ls : List (Label E R)}
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
    → List (Event√ E R)
    → ITree E I R
    → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  bNil : ∀{t : ITree E I R} → t ═⟨ [] ⟩═► t

{-
  bRet  : ∀{t  : ITree E I R} {x : R}
        → t ─[ ev (√ x) ]─► deadlock
        → t ═⟨ (√ x) ∷ [] ⟩═► deadlock
-}

  bTau :  {els : List (Event√ E R)}
          {t  : ITree E I R}
          {t′ : ITree E I R}
          {t′′ : ITree E I R}
        → t  ─[ τ ]─► t′
        → t′ ═⟨ els ⟩═► t′′
       ---------------------------------------------        
        → t  ═⟨ els ⟩═► t′′
        
  bStep : {el  : Event√ E R}
          {els : List (Event√ E R)}
          {t  : ITree E I R}
          {t′ : ITree E I R}
          {t′′ : ITree E I R}
        → t  ─[ ev el ]─► t′
        → t′ ═⟨ els ⟩═► t′′
       ---------------------------------------------
        → t  ═⟨ el ∷ els ⟩═► t′′

-- No τ transition is possible from a state reachable from deadlock via bigstep
no-τ-from-deadlock-bigstep :
  ∀ {ℓ ℓe ℓi ℓr}
    {E : Set ℓ → Set ℓe}
    {I : Set ℓ → Set ℓi}
    {R : Set ℓr}
    {s : List (Event√ E R)}
    {P′ Q : ITree E I R}
  → deadlock ═⟨ s ⟩═► P′
  → P′ ─[ τ ]─► Q → ⊥
no-τ-from-deadlock-bigstep bNil τ-step =
  τ-from-force-vis-impossible refl τ-step
no-τ-from-deadlock-bigstep (bTau τ-step _) _ =
  τ-from-force-vis-impossible refl τ-step
no-τ-from-deadlock-bigstep (bStep (sVis refl eq') _) _ =
  case eq' of λ ()
no-τ-from-deadlock-bigstep (bStep (sRet eq') _) _ =
  case eq' of λ ()
no-τ-from-deadlock-bigstep (bStep (sMixVis force≡mix _) _) _ =
  case force≡mix of λ ()

-----------------------------------------------------------------
module Traces where
  traces′ : ∀ {ℓ ℓe ℓi ℓr : Level} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → ITree E I R → List (Label E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
  traces′ t s = Σ[ t′ ∈ ITree _ _ _ ] (t ─⟨ s ⟩─► t′)

  -- Traces can be extracted from the big-step semantics
  traces : ∀ {ℓ ℓe ℓi ℓr : Level} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → ITree E I R → List (Event√ E R) → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
  traces t s = Σ[ t′ ∈ ITree _ _ _ ] (t ═⟨ s ⟩═► t′)

  _⊑ᵀ_ : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → ITree E I R → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
  P ⊑ᵀ Q = ∀ {s} → traces Q s → traces P s

-- The Failures module (refusals, failures, _⊑F_) lives in
-- `ITree_Relations.FailuresDivergences`, alongside `Divergent`, `IsDivergence`,
-- `failures⊥`, `_⊑F⊥_`, and `_⊑FD_`.  The whole denotational-model
-- bestiary is collected there since `failures⊥` couples failures with
-- divergences.


{-
  This module defines Interaction Trees (ITree), including basic definitions and proofs related to ITree

ITree E I R (Coinductive Record)
  |
  +-- force: NodeKind E I R (Data Type)
              |
              +-- ret r: R
              |   (Terminal node returning value r)
              |
              +-- sil t: ITree E I R
              |   (Silent transition τ to next tree t)
              |
              +-- vis choices: (at : AnyTypes E) -> ContinueType at (Maybe (ITree E I R))
              |   (Visible event choices)
              |   |
              |   +-- (at : (A, _)) -> (a : A) -> Just t: ITree E I R
              |   |   (Event (at, a) leads to next tree t)
              |   |
              |   +-- (at : (A, _)) -> (a : A) -> Nothing
              |   |   (Event (at, a) is not enabled in this choice)
              |   .
              |   .
              |   .              
              |
              +-- ndbr branches: (it : AnyTypes I) -> ContinueType it (Maybe (ITree E I R))
                  witness: (i : AnyTypes I) -> (a : proj1 i) -> Is-just (branches i a)
                  (Nondeterministic internal branches)
                  |
                  +-- (it : (A, _)) -> (a : A) -> Just t: ITree E I R
                  |   (Branch indexed by (it, a) leads to next tree t)
                  |
                  +-- (it : (A, _)) -> (a : A) -> Nothing
                  |   (Branch indexed by (it, a) does not exist)
                  |
                  .
                  ,                  

Or similarly represented as below.

[ ITree E I R ]  (Coinductive Record)
              |
           .force
              |
      _______/ \___________________________________________
     |                |                 |                  |
 [ ret ]           [ sil ]           [ vis ]            [ ndbr ]
    |                 |                 |                  |
 (Value R)      (Next ITree)     (Visible Events)   (Internal Choice)
    |                 |                 |                  |
 [Term]            [ τ ]          (AnyTypes E)       (AnyTypes I)
                                        |                  |
                                 (ContinueType)     (ContinueType)
                                        |                  |
                                 +------+------+    +------+------+
                                 |             |    |             |
                              [Just]       [Nothing] [Just]    [Nothing]
                                 |             |    |             |
                            (Next ITree)    (Dead) (Next ITree) (Dead)
                            
-}

{-# OPTIONS --guardedness #-}

open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Level using (Level; _⊔_; Lift; lift; lower) renaming (zero to lzero; suc to lsuc)
open import Data.Maybe using (Maybe; just; nothing; is-just; Is-just) renaming (map to mapMaybe)
open import Data.Empty using (⊥)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_; ∃; Σ-syntax; ∃-syntax)
open import Relation.Unary
open import Function using (case_of_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
-- open import Data.Maybe.Relation.Unary.Any

module Interaction_Trees where

-- This is the "Sort" for all by the type constructor E
-- It reads: "There exists some type A, such that we have an E A"
-- Elements of this type are like {(ℕ , input), (⊥ , output _)}
AnyTypes : ∀ {ℓ ℓ'} → (Set ℓ → Set ℓ') → Set (lsuc ℓ ⊔ ℓ')
AnyTypes {ℓ} {ℓ'} E = Σ (Set ℓ) E

-- The continuation data type for a channel from (AnyTypes E) of type A with its next process
ContinueType : ∀ {ℓ ℓ' ℓ''} {E : Set ℓ → Set ℓ'}
             → AnyTypes E
             → Set ℓ''
             → Set (ℓ ⊔ ℓ'')
ContinueType (A , _) next = A → next

mutual
  {-
    E is a type constructor for visible events, and
    I is a type constructor for indexed branches (could be any finite or infinite set)
      - Fin n can be used for finite branching
      - in CSP, three operators are able to introduce infinite branching or unbounded nondeterministic choice
        - ⨅ S where S is a set of processes
        - P ∖ CS where CS could be an infinite set of events
        - r[P] if r is a non-injective renaming function or renaming relations
     For CSP, I could be the same as E
  -}
  -- ITree is not able to model something like (a → P □ (τ → Q)) because visible choices only allow visible events, not tau
  data NodeKind {ℓ ℓe ℓi ℓr : Level}
               (E : Set ℓ → Set ℓe)
               (I : Set ℓ → Set ℓi) -- maybe too general? type a as cardinality a → Set (you may not need to deal with levels)
               -- (I : a → Set ℓi) -- maybe too general? type a as cardinality a → Set (you may not need to deal with levels)               
               (R : Set ℓr)
             : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
    ret : R
        → NodeKind E I R -- terminate immediately and return a value of type R
    sil : ITree E I R -- a silent transition tau
        → NodeKind E I R
    -- input → (λ {x → child (x)}) [] output.1 → (λ ⊥ → child2) [] input →
    -- See Chapter 9.2 firing rules for CSP in UCS for a similar idea
    -- nothing mean an event is not appeared in this choice
    vis : ((at : AnyTypes E) → ContinueType at (Maybe (ITree E I R)))
        → NodeKind E I R
    -- nondeterministic branches or internal or invisible
    -- (A , i) → (A → child)
    -- What does nothing mean? It is different from vis. Here, I is just an index set
    --  like (Fin n) for index. I doesn't mean events in vis. So nothing means no this branch.
    ndbr : (branches : (i  : AnyTypes I) → ContinueType i  (Maybe (ITree E I R)))
        → (i : AnyTypes I) → (a : proj₁ i) → Is-just {lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr} (branches i a) -- This ensures the non-empty of ndbr
        -- where i a are witnesses of at least one just branch
        → NodeKind E I R

  record ITree {ℓ ℓe ℓi ℓr : Level}
               (E : Set ℓ → Set ℓe)
               (I : Set ℓ → Set ℓi)
               (R : Set ℓr)
             : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where -- _ for undecided levels, ?
    coinductive
    constructor itree
    field
      force : NodeKind E I R

-- Kleiski trees
KTree : ∀ {ℓ ℓe ℓi ℓr ℓs}
      → (E : Set ℓ → Set ℓe)
      → (I : Set ℓ → Set ℓi)
      → Set ℓr
      → Set ℓs
      → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs)
KTree E I R S = R → ITree E I S

-- Homogeneous Kleiski trees
HKTree : ∀ {ℓ ℓe ℓi ℓr}
       → (E : Set ℓ → Set ℓe)
       → (I : Set ℓ → Set ℓi)
       → Set ℓr
       → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
HKTree E I A = KTree E I A A

data ExtI {ℓ ℓi} (I : Set ℓ → Set ℓi) : Set ℓ → Set (lsuc ℓ ⊔ ℓi) where
  base : ∀ {A}         → I A          → ExtI I A
  pair : ∀ {AP AQ}     → ExtI I AP → ExtI I AQ  → ExtI I (AP × AQ)
  fin  : ∀ {n : ℕ}       → ExtI I (Lift ℓ (Fin n))

--  A ITree is stable, useful to define refusals
isStable : ∀ {ℓ ℓe ℓi ℓr : Level}
             {E : Set ℓ → Set ℓe}
             {I : Set ℓ → Set ℓi}
             {R : Set ℓr}
           → ITree E I R → Set
isStable t with ITree.force t
... | ret _ = ⊤
... | sil _ = ⊥
... | vis _ = ⊤
... | ndbr _ _ _ _ = ⊥

isUnstable : ∀ {ℓ ℓe ℓi ℓr : Level}
               {E : Set ℓ → Set ℓe}
               {I : Set ℓ → Set ℓi}
               {R : Set ℓr}
             → ITree E I R → Set
isUnstable t with ITree.force t
... | ret _ = ⊥
... | sil _ = ⊤
... | vis _ = ⊥
... | ndbr _ _ _ _ = ⊤

-- The image of f: the set of ITrees reachable via f
Image : ∀ {ℓ ℓe ℓi ℓr : Level}
          {E : Set ℓ → Set ℓe}
          {I : Set ℓ → Set ℓi}
          {R : Set ℓr}
        → ((i : AnyTypes I) → proj₁ i → Maybe (ITree E I R))
        → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Image {I = I} f t = Σ[ i ∈ AnyTypes I ] Σ[ a ∈ proj₁ i ] f i a ≡ just t

-- Divergent process: spins silently forever
div : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → ITree E I R
ITree.force div = sil div

deadlock : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → ITree E I R
ITree.force deadlock = vis (λ _ _ → nothing)

vis≢sil : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
    {t : ITree E I R}
  → vis f ≡ sil t → ⊥
vis≢sil ()

vis≢ndbr : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {f : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}    
    {g : (at : AnyTypes I) → ContinueType at (Maybe (ITree E I R))}
    {i : AnyTypes I} {a : proj₁ i} {p : Is-just (g i a)}
  → vis f ≡ ndbr g i a p  → ⊥
vis≢ndbr ()

sil≢ndbr : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t : ITree E I R}
    {f : (at : AnyTypes I) → ContinueType at (Maybe (ITree E I R))}    
    {i : AnyTypes I} {a : proj₁ i} {p : Is-just (f i a)}
  → sil t ≡ ndbr f i a p  → ⊥
sil≢ndbr ()

-- vis is injective in its continuation argument
vis-injective : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {f g : (at : AnyTypes E) → ContinueType at (Maybe (ITree E I R))}
  → vis f ≡ vis g → f ≡ g
vis-injective refl = refl

-- vis is injective in its continuation argument
sil-injective : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {f g : (ITree E I R)}
  → sil f ≡ sil g → f ≡ g
sil-injective refl = refl


br2 : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (P : ITree E (ExtI I) R) → (Q : ITree E (ExtI I) R) →
  (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (ITree E (ExtI I) R))
br2 P Q (_ , fin) x = case x of λ where
  (lift fzero)        → just P
  (lift (fsuc fzero)) → just Q
  _                   → nothing   -- covers Fin n for n > 2
br2 P Q (_ , base _)   _ = nothing
br2 P Q (_ , pair _ _) _ = nothing

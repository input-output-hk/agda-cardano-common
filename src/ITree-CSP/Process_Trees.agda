{-
  This module defines Process Trees (PTree), including basic definitions and proofs related to PTree

PTree E I R (Coinductive Record)
  |
  +-- force: NodeKind E I R (Data Type)
              |
              +-- ret r: R
              |   (Terminal node returning value r)
              |
              +-- sil t: PTree E I R
              |   (Silent transition τ to next tree t)
              |
              +-- vis choices: (at : AnyTypes E) -> ContinueType at (Maybe (PTree E I R))
              |   (Visible event choices)
              |   |
              |   +-- (at : (A, _)) -> (a : A) -> Just t: PTree E I R
              |   |   (Event (at, a) leads to next tree t)
              |   |
              |   +-- (at : (A, _)) -> (a : A) -> Nothing
              |   |   (Event (at, a) is not enabled in this choice)
              |   .
              |   .
              |   .              
              |
              +-- ndbr branches: (it : AnyTypes I) -> ContinueType it (Maybe (PTree E I R))
                  witness: (i : AnyTypes I) -> (a : proj1 i) -> Is-just (branches i a)
                  (Nondeterministic internal branches)
                  |
                  +-- (it : (A, _)) -> (a : A) -> Just t: PTree E I R
                  |   (Branch indexed by (it, a) leads to next tree t)
                  |
                  +-- (it : (A, _)) -> (a : A) -> Nothing
                  |   (Branch indexed by (it, a) does not exist)
                  |
                  .
                  ,                  

Or similarly represented as below.

[ PTree E I R ]  (Coinductive Record)
              |
           .force
              |
      _______/ \___________________________________________
     |                |                 |                  |
 [ ret ]           [ sil ]           [ vis ]            [ ndbr ]
    |                 |                 |                  |
 (Value R)      (Next PTree)     (Visible Events)   (Internal Choice)
    |                 |                 |                  |
 [Term]            [ τ ]          (AnyTypes E)       (AnyTypes I)
                                        |                  |
                                 (ContinueType)     (ContinueType)
                                        |                  |
                                 +------+------+    +------+------+
                                 |             |    |             |
                              [Just]       [Nothing] [Just]    [Nothing]
                                 |             |    |             |
                            (Next PTree)    (Dead) (Next PTree) (Dead)
                            
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

module Process_Trees where

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
  -- PTree is not able to model something like (a → P □ (τ → Q)) because visible choices only allow visible events, not tau
  data NodeKind {ℓ ℓe ℓi ℓr : Level}
               (E : Set ℓ → Set ℓe)
               (I : Set ℓ → Set ℓi) -- maybe too general? type a as cardinality a → Set (you may not need to deal with levels)
               -- (I : a → Set ℓi) -- maybe too general? type a as cardinality a → Set (you may not need to deal with levels)               
               (R : Set ℓr)
             : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
    ret : R
        → NodeKind E I R -- terminate immediately and return a value of type R
    sil : PTree E I R -- a silent transition tau
        → NodeKind E I R

    -- PURE EXTC: the only branching node.  Fuses `vis` and `ndbr` with NO
    -- non-emptiness witness: a visible-offer continuation together with a
    -- (possibly everywhere-`nothing`) τ-branch continuation.  τ-moves exist
    -- only where `τc` is `just`, so an empty τc means the node is stable
    -- (behaves as a pure `vis`) — emptiness is benign, needs no decision.
    react : ((at : AnyTypes E) → ContinueType at (Maybe (PTree E I R)))  -- visible offers
         → ((i  : AnyTypes I) → ContinueType i  (Maybe (PTree E I R)))  -- τ-branches, no witness
         → NodeKind E I R

  record PTree {ℓ ℓe ℓi ℓr : Level}
               (E : Set ℓ → Set ℓe)
               (I : Set ℓ → Set ℓi)
               (R : Set ℓr)
             : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where -- _ for undecided levels, ?
    coinductive
    constructor ptree
    field
      force : NodeKind E I R

-- Kleiski trees
KTree : ∀ {ℓ ℓe ℓi ℓr ℓs}
      → (E : Set ℓ → Set ℓe)
      → (I : Set ℓ → Set ℓi)
      → Set ℓr
      → Set ℓs
      → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓs)
KTree E I R S = R → PTree E I S

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

--  A PTree is stable iff it offers no τ-move: an `react` node is stable exactly when
--  its τ-branch continuation is everywhere `nothing`.  Since `react` fuses vis and
--  ndbr, stability is no longer a per-constructor fact (as it was for vis/ndbr/mix)
--  but a PREDICATE on `τc` — so the result type is lifted out of `Set₀`.
isStable : ∀ {ℓ ℓe ℓi ℓr : Level}
             {E : Set ℓ → Set ℓe}
             {I : Set ℓ → Set ℓi}
             {R : Set ℓr}
           → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
isStable {ℓ} {ℓe} {ℓi} {ℓr} t with PTree.force t
... | ret _     = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥   -- termination is not env-controlled ⇒ not stable
... | sil _     = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊥
... | react _ τc = ∀ (i : AnyTypes _) (a : proj₁ i) → τc i a ≡ nothing

isUnstable : ∀ {ℓ ℓe ℓi ℓr : Level}
               {E : Set ℓ → Set ℓe}
               {I : Set ℓ → Set ℓi}
               {R : Set ℓr}
             → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
isUnstable {ℓ} {ℓe} {ℓi} {ℓr} t with PTree.force t
... | ret _     = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊤
... | sil _     = Lift (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) ⊤
... | react _ τc = Σ[ i ∈ AnyTypes _ ] Σ[ a ∈ proj₁ i ] Is-just (τc i a)   -- some τ-move enabled

-- The image of f: the set of ITrees reachable via f
Image : ∀ {ℓ ℓe ℓi ℓr : Level}
          {E : Set ℓ → Set ℓe}
          {I : Set ℓ → Set ℓi}
          {R : Set ℓr}
        → ((i : AnyTypes I) → proj₁ i → Maybe (PTree E I R))
        → PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
Image {I = I} f t = Σ[ i ∈ AnyTypes I ] Σ[ a ∈ proj₁ i ] f i a ≡ just t

-- Divergent process: spins silently forever
div : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    → PTree E I R
PTree.force div = sil div

deadlock : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → PTree E I R
PTree.force deadlock = react (λ _ _ → nothing) (λ _ _ → nothing)

sil-injective : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {f g : (PTree E I R)}
  → sil f ≡ sil g → f ≡ g
sil-injective refl = refl

sil≢react : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {t : PTree E I R}
    {g : (at : AnyTypes E) → ContinueType at (Maybe (PTree E I R))}
    {h : (i : AnyTypes I) → ContinueType i (Maybe (PTree E I R))}
  → sil t ≡ react g h → ⊥
sil≢react ()

react-injective : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
    {v₁ v₂ : (at : AnyTypes E) → ContinueType at (Maybe (PTree E I R))}
    {τc₁ τc₂ : (i : AnyTypes I) → ContinueType i (Maybe (PTree E I R))}
  → react v₁ τc₁ ≡ react v₂ τc₂ → (v₁ ≡ v₂) × (τc₁ ≡ τc₂)
react-injective refl = refl , refl


br2 : ∀ {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (P : PTree E (ExtI I) R) → (Q : PTree E (ExtI I) R) →
  (i : AnyTypes (ExtI I)) → ContinueType i (Maybe (PTree E (ExtI I) R))
br2 P Q (_ , fin) x = case x of λ where
  (lift fzero)        → just P
  (lift (fsuc fzero)) → just Q
  _                   → nothing   -- covers Fin n for n > 2
br2 P Q (_ , base _)   _ = nothing
br2 P Q (_ , pair _ _) _ = nothing

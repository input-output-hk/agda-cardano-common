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
-- open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using (⊤; tt)
open import Data.Product using (Σ; _,_; proj₁; _×_; ∃; Σ-syntax; ∃-syntax)

open import Class.DecEq
open import Level using (Level; 0ℓ)

open import Relation.Binary                using (Rel)
-- open import Relation.Unary
open import Function using (case_of_)
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_; refl)

open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; subst; sym; trans; refl; inspect; [_]; cong)
-- open import Relation.Binary.Definitions using (DecidableEquality)

open import Data.Sum using (_⊎_; inj₁; inj₂) renaming ([_,_] to case-⊎)
open import Data.Bool using (Bool; true; false; if_then_else_)
open import Data.List using (List; _++_; _∷_; []; length; reverse; map; foldr; downFrom)
-- open import Data.List.Relation.Unary.All using (All; []; _∷_)
-- import  Data.List.Relation.Unary.Any using (Any; here;there)
-- import Data.List.Membership.Propositional using (_∈_)

-- import Data.List.Properties using (reverse-++-commute; map-compose; map-++-commute; foldr-++; map-is-foldr)

open import Interaction_Trees
open import Relation.Nullary using (¬_)

open import ITree_Relations.LTS using (Event; evLabel; Event√; Label;
  ev; τ; evl; √;
  _─[_]─►_; sSil; sVis; sNdbr;
  _─[τ*]─►_; τ*-zero; τ*-step; -- τ*-sil; τ*-inv;
  _═[_]═►_; weak-τ; weak-ev;
  _─[τ^_]─►_; τ^-zero; τ^-suc;
  _═⟨_⟩═►_; bNil; bTau; bStep;
  module Traces
  )

module ITree_Relations.FailuresDivergences
  {ℓ ℓe ℓi ℓr : Level}
  {E : Set ℓ → Set ℓe}
  {I : Set ℓ → Set ℓi}
  {R : Set ℓr}
  where
  
open ITree
open Traces

-----------------------------------------------------------------
-- Failures, derived from `_ref_`.
--   (s , B) is a failure of P iff P can perform trace s to some P′
--   that refuses B.
--
-- Originally defined in `ITree_Relations.LTS`; moved here so it sits
-- alongside `divergences` and `failures⊥` (the divergence-strict
-- closure used by the FD model couples failures with divergences).
module Failures where
  -----------------------------------------------------------------
  -- Refusal relation P ref B
  --   B is a subset (predicate) over Event√ E R, i.e. visible events ∪ {√ x}.
  --   Two CSP-style cases:
  --     ref-stable : P is stable (vis-shaped) and refuses every event in B
  --     ref-tick   : P can fire √ x to some Q, and √ x is not in B
  data _ref_ {ℓB : Level}
           : ITree E I R → (Event√ E R → Set ℓB)
           → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓB) where

    ref-stable : ∀ {P : ITree E I R} {B : Event√ E R → Set ℓB}
               → isStable P
               → (∀ e → B e → ∀ {Q : ITree E I R} → ¬ (P ─[ ev e ]─► Q))
               → P ref B

    ref-tick   : ∀ {P : ITree E I R} {B : Event√ E R → Set ℓB}
                   {x : R} {Q : ITree E I R}
               → P ─[ ev (√ x) ]─► Q
               → ¬ B (√ x)
               → P ref B

  failures : ∀ {ℓB : Level}
           → ITree E I R
           → List (Event√ E R)
           → (Event√ E R → Set ℓB)
           → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓB)
  failures P s B = Σ[ P′ ∈ ITree _ _ _ ] (P ═⟨ s ⟩═► P′) × (P′ ref B)

  -- Failures refinement: every failure of Q is a failure of P
  _⊑F_ : ITree E I R → ITree E I R → Set (lsuc (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr))
  _⊑F_ P Q =
        ∀ {s} {B : Event√ E R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)}
      → failures Q s B → failures P s B

{-
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

--------------------------------------------------------------------------------------
stabilises-ret v = itree (ret v) , 0 , τ^-zero , tt

-}

-- Definition of a divergent ITree
-- UCS 9.5.1: We say P can diverge, written P ⇑, if there exist P0 = P , P1 , P2 , . . .
-- such that, for all n ∈ N, Pn −τ→ Pn+1 .
record Divergent (P : ITree E I R) : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    next    : ITree E I R
    step    : P ─[ Label.τ ]─► next
    diverge : Divergent next

open Divergent

-- div is divergent
div-diverges : Divergent div
div-diverges .next    = div
div-diverges .step    = sSil refl
div-diverges .diverge = div-diverges

-- Lift divergence up through a sil node
step-sil-diverges : ∀ {t t' : ITree E I R}
              → ITree.force t ≡ sil t'
              → Divergent t'
              → Divergent t
step-sil-diverges {t} {t'} eq d .Divergent.next    = t'
step-sil-diverges eq d .Divergent.step    = sSil eq
step-sil-diverges eq d .Divergent.diverge = d

-- If a branch of nondeterministic branches (ndbr) is divergent, then this ndbr is divergent
step-ndbr-diverges : ∀ -- {ℓ ℓe ℓi ℓr} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                (branches : (i : AnyTypes I) → ContinueType i (Maybe (ITree E I R)))
                (wi : AnyTypes I) (wa : proj₁ wi) (p : Is-just {lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr} (branches wi wa))
                (i : AnyTypes I) (a : proj₁ i) (P : ITree E I R)
              → branches i a ≡ just P
              → Divergent (P) -- The chosen branch must be divergent
              → Divergent (itree (ndbr branches wi wa p))

-- 1. The 'next' state is the result of the branch we picked
step-ndbr-diverges branches wi wa p i a P eq dP .next = P

-- 2. The 'step' proof uses the sNdbr constructor (matching your transition system)
-- It proves: ndbr branches i a p ─[ τ ]─► next
step-ndbr-diverges branches wi wa p i a P eq dP .step = sNdbr refl eq

-- 3. The continuation is the divergence of the chosen branch
step-ndbr-diverges branches wi wa p i a P eq dP .diverge = dP

divergent-prefix : ∀ {t t' : ITree E I R}
                 → t ─[τ*]─► t'
                 → Divergent t'
                 → Divergent t
divergent-prefix τ*-zero       d = d
divergent-prefix (τ*-step s p) d .next    = _
divergent-prefix (τ*-step s p) d .step    = s
divergent-prefix (τ*-step s p) d .diverge = divergent-prefix p d

--------------------------------------------------------------------------------------
-- Extract divergences from LTS
--------------------------------------------------------------------------------------

-----------------------------------------------------------
-- Definition of divergences based on divergence strictness
--   
-- P ⇒s Q : P weakly reaches Q via visible trace s
-- This is exactly _═⟨_⟩═► in LTS
record IsDivergence {- {ℓ ℓe ℓi ℓr}
                    {E : Set ℓ → Set ℓe}
                    {I : Set ℓ → Set ℓi}
                    {R : Set ℓr} -}
                    (P : ITree E I R)
                    (s : List (Event√ E R))
                  : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  field
    prefix  : List (Event√ E R)              -- s₀
    suffix  : List (Event√ E R)              -- t
    split   : s ≡ prefix ++ suffix          -- s = s₀ ^ t
    witness : ITree E I R                   -- Q
    reach   : P ═⟨ prefix ⟩═► witness      -- P ⇒s₀ Q
    divwit  : Divergent witness             -- Q⇑

divergences : ∀ {-
                {ℓ ℓe ℓi ℓr}
                {E : Set ℓ → Set ℓe}
                {I : Set ℓ → Set ℓi}
                {R : Set ℓr} -}
            (P : ITree E I R)
            → List (Event√ E R)
            → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
divergences P s = IsDivergence P s

-----------------------------------------------------------------------------------------
-- Key properties of divergences

-- Divergences are extension-closed: if s ∈ div(P) then s^t ∈ div(P)
div-extension-closed : ∀ {-{ℓ ℓe ℓi ℓr}
                         {E : Set ℓ → Set ℓe}
                         {I : Set ℓ → Set ℓi}
                         {R : Set ℓr} -}
                         {P : ITree E I R} {s t : List (Event√ E R)}
                       → IsDivergence P s
                       → IsDivergence P (s ++ t)
div-extension-closed {t = t} d = record
  { prefix  = d .IsDivergence.prefix
  ; suffix  = d .IsDivergence.suffix ++ t
  ; split   = trans (cong (_++ t) (d .IsDivergence.split)) (++-assoc (d .IsDivergence.prefix) (d .IsDivergence.suffix) t)
  ; witness = d .IsDivergence.witness
  ; reach   = d .IsDivergence.reach
  ; divwit  = d .IsDivergence.divwit
  }
  where open import Data.List.Properties using (++-assoc)

-- Every prefix of a divergence is a trace
div-prefix-is-trace : ∀ {- {ℓ ℓe ℓi ℓr}
                        {E : Set ℓ → Set ℓe}
                        {I : Set ℓ → Set ℓi}
                        {R : Set ℓr} -}
                        {P : ITree E I R} {s : List (Event√ E R)}
                      → (d : IsDivergence P s)
                      → traces P (d .IsDivergence.prefix)
div-prefix-is-trace d =
    d .IsDivergence.witness , d .IsDivergence.reach

-- The empty trace is a divergence iff P itself diverges
empty-div-iff : ∀ {- {ℓ ℓe ℓi ℓr}
                  {E : Set ℓ → Set ℓe}
                  {I : Set ℓ → Set ℓi}
                  {R : Set ℓr} -}
                  {P : ITree E I R}
                → Divergent P
                → IsDivergence P []
empty-div-iff dP = record
  { prefix  = []
  ; suffix  = []
  ; split   = refl
  ; witness = _
  ; reach   = bNil
  ; divwit  = dP
  }

-----------------------------------------------------------------------------------------
-- Failures-divergences (FD) model
--
-- LTS-derived denotational refinement orderings used by the standard
-- CSP-FD model (Roscoe, UCS §9.5).  Builds on `failures` (above) and
-- `divergences` (above).

open Failures using (failures; _ref_)

-- Divergence-strict failures: once `s` is a divergence trace of `P`,
-- every refusal set `B` is a failure of `P` after `s` ("chaos after
-- divergence").  This is the closure that distinguishes the FD model
-- from the plain failures model.
failures⊥ : ∀ {ℓB : Level}
          → ITree E I R
          → List (Event√ E R)
          → (Event√ E R → Set ℓB)
          → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓB)
failures⊥ P s B = failures P s B ⊎ divergences P s

-- failures⊥ refinement:  P ⊑F⊥ Q  iff every divergence-strict failure
-- of Q is also one of P (i.e. `failures⊥ Q ⊆ failures⊥ P`).
_⊑F⊥_ : ITree E I R → ITree E I R → Set (lsuc (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr))
_⊑F⊥_ P Q =
      ∀ {s} {B : Event√ E R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)}
    → failures⊥ Q s B → failures⊥ P s B

-- Divergence refinement:  P ⊑D Q  iff every divergence of Q is a
-- divergence of P.
_⊑D_ : ITree E I R → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
_⊑D_ P Q = ∀ {s} → divergences Q s → divergences P s

-- Failures-divergences refinement:  the conjunction.  In CSP-FD, this
-- is the standard refinement order (`⊑FD`).
_⊑FD_ : ITree E I R → ITree E I R → Set (lsuc (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr))
_⊑FD_ P Q = (P ⊑F⊥ Q) × (P ⊑D Q)

{-# OPTIONS --guardedness #-}

------------------------------------------------------------
-- Imports
------------------------------------------------------------

open import Level using (Level; _⊔_; Lift; lift) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as UnitPoly
open import Data.Empty using (⊥; ⊥-elim)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; subst)
-- Note: we deliberately do NOT import Relation.Nullary.¬_; LTLᵗ has its
-- own `¬_` constructor and we encode semantic negation as `… → ⊥`.

open import Process_Trees hiding (div)
  -- `Process_Trees.div` is the divergent PTree itself; we hide it
  -- so we can use `div` as a Frame constructor name.

module Semantics.LTL.Traces_Based {ℓ ℓe ℓi} {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} where

open PTree

open import Semantics.LTS       {ℓ} {ℓe} {ℓi} {E} {I} hiding (Diverges)
open import Semantics.WeakBisim {ℓ} {ℓe} {ℓi} {E} {I} using (_═[_]═►_)
open import Semantics.DRBisim   {ℓ} {ℓe} {ℓi} {E} {I} using (Diverges)
open import Semantics.Deadlock  {ℓ} {ℓe} {ℓi} {E} {I} using (IsStuck)

------------------------------------------------------------
-- §1 Frame
--
-- A Frame is the unit of observation that a Trace exposes at each
-- point and that atoms consume. Four frame kinds match the four
-- DR-weak observations: visible step, √-termination, deadlock, and
-- τ-divergence.
------------------------------------------------------------

data Frame {ℓr : Level}
           (R : Set ℓr)
         : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  step  : PTree E I R → Event√ R → Frame R
  done  : PTree E I R → R        → Frame R
  stuck : PTree E I R            → Frame R
  div   : PTree E I R            → Frame R

frameState : ∀ {ℓr} {R : Set ℓr}
             → Frame R → PTree E I R
frameState (step  t _) = t
frameState (done  t _) = t
frameState (stuck t  ) = t
frameState (div   t  ) = t

IsTerminator : ∀ {ℓr} {R : Set ℓr}
               → Frame R → Set
IsTerminator (step  _ _) = ⊥
IsTerminator (done  _ _) = ⊤
IsTerminator (stuck _  ) = ⊤
IsTerminator (div   _  ) = ⊤

------------------------------------------------------------
-- §2 Trace
------------------------------------------------------------

-- Intrinsic, finite-or-infinite, valid-by-construction execution trace.
-- `step` is the only coinductive carrier (its tail is thunked); the
-- three terminator constructors are leaves.

mutual
  data Trace {ℓr : Level}
             (R : Set ℓr)
           : PTree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
    step  : ∀ {t : PTree E I R} {e : Event√ R} {t' : PTree E I R}
          → t ═[ ev e ]═► t' → ∞Trace R t' → (Trace R) t
    done  : ∀ {t : PTree E I R} {r : R}
          → PTree.force t ≡ ret r → (Trace R) t
    stuck : ∀ {t : PTree E I R}
          → IsStuck t → (Trace R) t
    div   : ∀ {t : PTree E I R}
          → Diverges t → (Trace R) t

  record ∞Trace {ℓr : Level}
                (R : Set ℓr)
                (t : PTree E I R)
              : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
    coinductive
    field
      force : (Trace R) t

open ∞Trace public

-- The frame currently observed by the trace.
frameOf : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
          → (Trace R) t → Frame R
frameOf (step {t} {e} _ _) = step t e
frameOf (done {t} {r} _)   = done t r
frameOf (stuck {t} _)      = stuck t
frameOf (div {t} _)        = div t

-- Index of the tail trace (the successor state, or the same state at a leaf).
tailIdx : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
          → (Trace R) t → PTree E I R
tailIdx (step {t' = t'} _ _) = t'
tailIdx {t = t} (done _)     = t
tailIdx {t = t} (stuck _)    = t
tailIdx {t = t} (div _)      = t

-- Total tail. At terminator frames, `tail` self-loops (stuttering convention).
tail : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
       → (tr : (Trace R) t) → Trace R (tailIdx tr)
tail (step _ tr)        = ∞Trace.force tr
tail tr@(done _)        = tr
tail tr@(stuck _)       = tr
tail tr@(div _)         = tr

dropIdx : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
          → ℕ → (Trace R) t → PTree E I R
dropIdx {t = t} zero    tr = t
dropIdx        (suc n)  tr = dropIdx n (tail tr)

drop : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
       → (n : ℕ) (tr : (Trace R) t) → Trace R (dropIdx n tr)
drop zero    tr = tr
drop (suc n) tr = drop n (tail tr)

-- At a terminator frame the tail self-loops, so its index is unchanged.
tailIdx-stutter : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                    (tr : (Trace R) t)
                  → IsTerminator (frameOf tr) → tailIdx tr ≡ t
tailIdx-stutter (step _ _) ()
tailIdx-stutter (done _)   _ = refl
tailIdx-stutter (stuck _)  _ = refl
tailIdx-stutter (div _)    _ = refl

-- Stutter law for tail at terminator frames. `tail tr` lives at index
-- `tailIdx tr`; we transport `tr` (at index `t`) along `tailIdx-stutter`
-- so both sides inhabit `(Trace R) (tailIdx tr)` and the equation is
-- homogeneous. At each terminator constructor `tailIdx-stutter … = refl`,
-- so the transport is the identity and the witness is `refl`.
tail-stutter : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                 (tr : (Trace R) t) (term : IsTerminator (frameOf tr))
               → tail tr ≡ subst (Trace R) (sym (tailIdx-stutter tr term)) tr
tail-stutter (done _)   _ = refl
tail-stutter (stuck _)  _ = refl
tail-stutter (div _)    _ = refl

-- The index after `drop n` at a terminator is unchanged.
dropIdx-stutter : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                    (n : ℕ) (tr : (Trace R) t)
                  → IsTerminator (frameOf tr) → dropIdx n tr ≡ t
dropIdx-stutter zero    tr        term = refl
dropIdx-stutter (suc n) (done eq)  term = dropIdx-stutter n (done eq)  term
dropIdx-stutter (suc n) (stuck st) term = dropIdx-stutter n (stuck st) term
dropIdx-stutter (suc n) (div dv)   term = dropIdx-stutter n (div dv)   term

-- Stutter law for drop at terminator frames. As with `tail-stutter`, both
-- sides are placed at index `dropIdx n tr` via `dropIdx-stutter`; at a
-- terminator that transport is the identity, so the witness is `refl`/IH.
drop-stutter : ∀ {ℓr} {R : Set ℓr} {t : PTree E I R}
                 (n : ℕ) (tr : (Trace R) t) (term : IsTerminator (frameOf tr))
               → drop n tr ≡ subst (Trace R) (sym (dropIdx-stutter n tr term)) tr
drop-stutter zero    tr        term = refl
drop-stutter (suc n) (done eq)  term = drop-stutter n (done eq)  term
drop-stutter (suc n) (stuck st) term = drop-stutter n (stuck st) term
drop-stutter (suc n) (div dv)   term = drop-stutter n (div dv)   term

------------------------------------------------------------
-- §4 Syntax
------------------------------------------------------------

FramePred : ∀ {ℓr} (ℓa : Level)
              (R : Set ℓr)
            → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓa)
FramePred ℓa R = Frame R → Set ℓa

-- Six-constructor primitive syntax. Everything else is a definition.
data LTLᵗ {ℓr : Level} (ℓa : Level)
          (R : Set ℓr)
        : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓa) where
  ⊤'    : LTLᵗ ℓa R
  atom  : FramePred ℓa R              → LTLᵗ ℓa R
  ¬_    : LTLᵗ ℓa R                   → LTLᵗ ℓa R
  _∧_   : LTLᵗ ℓa R → LTLᵗ ℓa R       → LTLᵗ ℓa R
  X_    : LTLᵗ ℓa R                   → LTLᵗ ℓa R
  _U_   : LTLᵗ ℓa R → LTLᵗ ℓa R       → LTLᵗ ℓa R

infix  4 _U_
infixr 6 _∧_
infix  7 X_
infix  8 ¬_

------------------------------------------------------------
-- §5 Semantics
------------------------------------------------------------

-- ⊤'/¬ in ⟦_⟧ use Lift to land in Set ℓa from level-0 ⊤/⊥. The other
-- cases (atom, ∧, X, U) are level-ℓa naturally because their building
-- blocks (FramePred, ×, Σ) all preserve / are at ℓa.
⟦_⟧ : ∀ {ℓr ℓa}
        {R : Set ℓr} {t : PTree E I R}
      → LTLᵗ ℓa R → (Trace R) t → Set ℓa
⟦_⟧ {ℓa = ℓa} ⊤'      tr = Lift ℓa ⊤
⟦ atom P  ⟧ tr = P (frameOf tr)
⟦_⟧ {ℓa = ℓa} (¬ φ)   tr = ⟦ φ ⟧ tr → Lift ℓa ⊥
⟦ φ ∧ ψ   ⟧ tr = ⟦ φ ⟧ tr × ⟦ ψ ⟧ tr
⟦ X φ     ⟧ tr = ⟦ φ ⟧ (tail tr)
⟦ φ U ψ   ⟧ tr = Σ ℕ (λ n → ⟦ ψ ⟧ (drop n tr)
                          × (∀ m → m < n → ⟦ φ ⟧ (drop m tr)))

-- Satisfaction. Coherence (the trace is rooted at `t`) is now in the type
-- of `(Trace R) t`, so the old `frameState (frameOf tr) ≡ t` premise is gone.
_⊨_ : ∀ {ℓr ℓa}
        {R : Set ℓr}
      → (t : PTree E I R) → LTLᵗ ℓa R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓa)
t ⊨ φ = ∀ (tr : Trace _ t) → ⟦ φ ⟧ tr

------------------------------------------------------------
-- §4.4 Derived operators (definitions, not constructors)
------------------------------------------------------------

⊥' : ∀ {ℓr ℓa}
       {R : Set ℓr}
     → LTLᵗ ℓa R
⊥' = ¬ ⊤'

_∨_ : ∀ {ℓr ℓa}
        {R : Set ℓr}
      → LTLᵗ ℓa R → LTLᵗ ℓa R → LTLᵗ ℓa R
φ ∨ ψ = ¬ ((¬ φ) ∧ (¬ ψ))

_⇒_ : ∀ {ℓr ℓa}
        {R : Set ℓr}
      → LTLᵗ ℓa R → LTLᵗ ℓa R → LTLᵗ ℓa R
φ ⇒ ψ = (¬ φ) ∨ ψ

F_ : ∀ {ℓr ℓa}
       {R : Set ℓr}
     → LTLᵗ ℓa R → LTLᵗ ℓa R
F_ φ = ⊤' U φ

G_ : ∀ {ℓr ℓa}
       {R : Set ℓr}
     → LTLᵗ ℓa R → LTLᵗ ℓa R
G_ φ = ¬ (F_ (¬ φ))

_W_ : ∀ {ℓr ℓa}
        {R : Set ℓr}
      → LTLᵗ ℓa R → LTLᵗ ℓa R → LTLᵗ ℓa R
φ W ψ = (φ U ψ) ∨ (G_ φ)

-- Release. Named `_Rel_` (not `_R_`) so the operator letter does not
-- collide with the result-type variable `R` in `Trace R t` applications.
_Rel_ : ∀ {ℓr ℓa}
        {R : Set ℓr}
      → LTLᵗ ℓa R → LTLᵗ ℓa R → LTLᵗ ℓa R
φ Rel ψ = ¬ ((¬ φ) U (¬ ψ))

infixr 5 _∨_
infixr 4 _⇒_
infix  4 _W_
infix  4 _Rel_
infix  7 F_
infix  7 G_

------------------------------------------------------------
-- §3 Convenience atoms (LTLᵗ values)
------------------------------------------------------------

-- Frame is `step` whose event is a `√ r` for some r.
atTick : ∀ {ℓr} {R : Set ℓr}
         → LTLᵗ lzero R
atTick = atom λ
  { (step _ (√ _))   → ⊤
  ; (step _ (evl _)) → ⊥
  ; (done  _ _)      → ⊥
  ; (stuck _)        → ⊥
  ; (div   _)        → ⊥
  }

-- Frame is `done` with value satisfying P.
atDone : ∀ {ℓr ℓa} {R : Set ℓr}
         → (R → Set ℓa) → LTLᵗ ℓa R
atDone {ℓa = ℓa} P = atom λ
  { (step  _ _) → Lift ℓa ⊥
  ; (done  _ r) → P r
  ; (stuck _)   → Lift ℓa ⊥
  ; (div   _)   → Lift ℓa ⊥
  }

-- Frame is `stuck`.
atStuck : ∀ {ℓr} {R : Set ℓr}
          → LTLᵗ lzero R
atStuck = atom λ
  { (step  _ _) → ⊥
  ; (done  _ _) → ⊥
  ; (stuck _)   → ⊤
  ; (div   _)   → ⊥
  }

-- Frame is `div`.
atDiv : ∀ {ℓr} {R : Set ℓr}
        → LTLᵗ lzero R
atDiv = atom λ
  { (step  _ _) → ⊥
  ; (done  _ _) → ⊥
  ; (stuck _)   → ⊥
  ; (div   _)   → ⊤
  }

-- Frame is `step` with a visible (non-tick) event.
atVis : ∀ {ℓr} {R : Set ℓr}
        → LTLᵗ lzero R
atVis = atom λ
  { (step _ (evl _))   → ⊤
  ; (step _ (√ _))     → ⊥
  ; (done  _ _)        → ⊥
  ; (stuck _)          → ⊥
  ; (div   _)          → ⊥
  }

-- The state in the current frame is at a `ret r` node with P r.
atRet : ∀ {ℓr ℓa} {R : Set ℓr}
        → (R → Set ℓa) → LTLᵗ ℓa R
atRet {ℓa = ℓa} P = atom λ fr → returnsWith′ P (frameState fr)
  where
    returnsWith′ : ∀ {ℓr} {R : Set ℓr}
                   → (R → Set ℓa) → PTree E I R → Set ℓa
    returnsWith′ P t with PTree.force t
    ... | ret r = P r
    ... | _     = Lift ℓa ⊥

-- Alias matching the old file's name.
returnsWith : ∀ {ℓr ℓa} {R : Set ℓr}
              → (R → Set ℓa) → LTLᵗ ℓa R
returnsWith = atRet

-- The state in the current frame is stable in the LTS sense.
-- In the react model `isStable` lands in `Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)`
-- (it quantifies over the τ-branch index), so this atom is at that level
-- rather than `lzero` as in the old vis/ndbr/mix model.
isStableᵗ : ∀ {ℓr} {R : Set ℓr}
            → LTLᵗ (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) R
isStableᵗ = atom λ fr → isStable (frameState fr)

------------------------------------------------------------
-- §6 Coinductive / inductive presentations
------------------------------------------------------------

record □ᵗ {ℓr ℓa}
          {R : Set ℓr} {t : PTree E I R}
          (φ : LTLᵗ ℓa R) (tr : (Trace R) t)
        : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓa) where
  coinductive
  field
    □ᵗ-now  : ⟦ φ ⟧ tr
    □ᵗ-tail : □ᵗ φ (tail tr)

open □ᵗ public

data ◇ᵗ {ℓr ℓa}
        {R : Set ℓr}
        (φ : LTLᵗ ℓa R)
      : {t : PTree E I R} → (Trace R) t → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓa) where
  ◇ᵗ-now   : ∀ {t} {tr : (Trace R) t} → ⟦ φ ⟧ tr        → ◇ᵗ φ tr
  ◇ᵗ-later : ∀ {t} {tr : (Trace R) t} → ◇ᵗ φ (tail tr) → ◇ᵗ φ tr

data _Uᵗ_ {ℓr ℓa}
          {R : Set ℓr}
          (φ ψ : LTLᵗ ℓa R)
        : {t : PTree E I R} → (Trace R) t → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓa) where
  Uᵗ-now  : ∀ {t} {tr : (Trace R) t} → ⟦ ψ ⟧ tr                          → (φ Uᵗ ψ) tr
  Uᵗ-step : ∀ {t} {tr : (Trace R) t} → ⟦ φ ⟧ tr → (φ Uᵗ ψ) (tail tr)     → (φ Uᵗ ψ) tr

------------------------------------------------------------
-- §6.1 Equivalences ⟦ F ⟧ ↔ ◇ᵗ, ⟦G⟧⁺ ↔ □ᵗ, ⟦ U ⟧ ↔ Uᵗ
------------------------------------------------------------

-- Helper for F⇒◇ᵗ: recurses structurally on n (no NON_TERMINATING needed).
F⇒◇ᵗ-helper : ∀ {ℓr ℓa}
                {R : Set ℓr} {t : PTree E I R}
                {φ : LTLᵗ ℓa R}
                (n : ℕ) (tr : (Trace R) t)
              → ⟦ φ ⟧ (drop n tr) → ◇ᵗ φ tr
F⇒◇ᵗ-helper zero    tr h = ◇ᵗ-now h
F⇒◇ᵗ-helper (suc n) tr h = ◇ᵗ-later (F⇒◇ᵗ-helper n (tail tr) h)

F⇒◇ᵗ : ∀ {ℓr ℓa}
         {R : Set ℓr} {t : PTree E I R}
         {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
       → ⟦ F_ φ ⟧ tr → ◇ᵗ φ tr
F⇒◇ᵗ {tr = tr} (n , h , _) = F⇒◇ᵗ-helper n tr h

◇ᵗ⇒F : ∀ {ℓr ℓa}
         {R : Set ℓr} {t : PTree E I R}
         {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
       → ◇ᵗ φ tr → ⟦ F_ φ ⟧ tr
◇ᵗ⇒F (◇ᵗ-now h)   = zero , h , (λ _ ())
◇ᵗ⇒F (◇ᵗ-later e) with ◇ᵗ⇒F e
... | n , h , bef = suc n , h , λ where
                                  zero    _              → lift tt
                                  (suc m) (s≤s m<sn)     → bef m m<sn
  where open import Data.Nat using (s≤s)

-- Σ-form of G semantics (positive). Constructively equivalent to □ᵗ;
-- classically equivalent to ⟦ G_ φ ⟧.
⟦G⟧⁺ : ∀ {ℓr ℓa}
         {R : Set ℓr} {t : PTree E I R}
       → LTLᵗ ℓa R → (Trace R) t → Set ℓa
⟦G⟧⁺ φ tr = ∀ n → ⟦ φ ⟧ (drop n tr)

⟦G⟧⁺⇒□ᵗ : ∀ {ℓr ℓa}
            {R : Set ℓr} {t : PTree E I R}
            {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
          → ⟦G⟧⁺ φ tr → □ᵗ φ tr
□ᵗ-now  (⟦G⟧⁺⇒□ᵗ g)            = g zero
□ᵗ-tail (⟦G⟧⁺⇒□ᵗ {tr = tr} g) = ⟦G⟧⁺⇒□ᵗ (λ n → g (suc n))

□ᵗ⇒⟦G⟧⁺ : ∀ {ℓr ℓa}
            {R : Set ℓr} {t : PTree E I R}
            {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
          → □ᵗ φ tr → ⟦G⟧⁺ φ tr
□ᵗ⇒⟦G⟧⁺ b zero    = □ᵗ-now b
□ᵗ⇒⟦G⟧⁺ b (suc n) = □ᵗ⇒⟦G⟧⁺ (□ᵗ-tail b) n

-- Constructive direction: ⟦G⟧⁺ ⇒ ⟦ G_ ⟧
⟦G⟧⁺⇒⟦G⟧ : ∀ {ℓr ℓa}
             {R : Set ℓr} {t : PTree E I R}
             {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
           → ⟦G⟧⁺ φ tr → ⟦ G_ φ ⟧ tr
⟦G⟧⁺⇒⟦G⟧ {φ = φ} {tr = tr} g (n , notφ , _) = notφ (g n)

-- Classical direction. The only classical axiom in the file; users who
-- want to avoid it should phrase global properties using □ᵗ or ⟦G⟧⁺.
postulate
-- This can be derived from LEM and see ClassicalFromLEM.agda where this lemma is proved from a single dne
  ⟦G⟧⇒⟦G⟧⁺ : ∀ {ℓr ℓa}
               {R : Set ℓr} {t : PTree E I R}
               {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
             → ⟦ G_ φ ⟧ tr → ⟦G⟧⁺ φ tr

-- Helper for U⇒Uᵗ: recurses structurally on n.
U⇒Uᵗ-helper : ∀ {ℓr ℓa}
                {R : Set ℓr} {t : PTree E I R}
                {φ ψ : LTLᵗ ℓa R}
                (n : ℕ) (tr : (Trace R) t)
              → ⟦ ψ ⟧ (drop n tr)
              → (∀ m → m < n → ⟦ φ ⟧ (drop m tr))
              → (φ Uᵗ ψ) tr
U⇒Uᵗ-helper zero    tr q _   = Uᵗ-now q
U⇒Uᵗ-helper (suc n) tr q bef =
  Uᵗ-step (bef zero (s≤s z≤n))
          (U⇒Uᵗ-helper n (tail tr) q (λ m m<n → bef (suc m) (s≤s m<n)))
  where open import Data.Nat using (s≤s; z≤n)

U⇒Uᵗ : ∀ {ℓr ℓa}
         {R : Set ℓr} {t : PTree E I R}
         {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
       → ⟦ φ U ψ ⟧ tr → (φ Uᵗ ψ) tr
U⇒Uᵗ {tr = tr} (n , q , bef) = U⇒Uᵗ-helper n tr q bef

Uᵗ⇒U : ∀ {ℓr ℓa}
         {R : Set ℓr} {t : PTree E I R}
         {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
       → (φ Uᵗ ψ) tr → ⟦ φ U ψ ⟧ tr
Uᵗ⇒U (Uᵗ-now q)        = zero , q , (λ _ ())
Uᵗ⇒U (Uᵗ-step p u) with Uᵗ⇒U u
... | n , q , bef = suc n , q , λ where
                                  zero    _              → p
                                  (suc m) (s≤s m<n)      → bef m m<n
  where open import Data.Nat using (s≤s)

------------------------------------------------------------
-- §7 Laws (Tier 1.C)
------------------------------------------------------------

-- §7.1 Monotonicity for □ᵗ, ◇ᵗ, Uᵗ.

□ᵗ-mono : ∀ {ℓr ℓa ℓb}
            {R : Set ℓr} {t : PTree E I R}
            {φ : LTLᵗ ℓa R} {ψ : LTLᵗ ℓb R}
            {tr : (Trace R) t}
          → (∀ {t'} {tr' : (Trace R) t'} → ⟦ φ ⟧ tr' → ⟦ ψ ⟧ tr')
          → □ᵗ φ tr → □ᵗ ψ tr
□ᵗ-now  (□ᵗ-mono imp b) = imp (□ᵗ-now b)
□ᵗ-tail (□ᵗ-mono imp b) = □ᵗ-mono imp (□ᵗ-tail b)

◇ᵗ-mono : ∀ {ℓr ℓa ℓb}
            {R : Set ℓr} {t : PTree E I R}
            {φ : LTLᵗ ℓa R} {ψ : LTLᵗ ℓb R}
            {tr : (Trace R) t}
          → (∀ {t'} {tr' : (Trace R) t'} → ⟦ φ ⟧ tr' → ⟦ ψ ⟧ tr')
          → ◇ᵗ φ tr → ◇ᵗ ψ tr
◇ᵗ-mono imp (◇ᵗ-now h)   = ◇ᵗ-now (imp h)
◇ᵗ-mono imp (◇ᵗ-later d) = ◇ᵗ-later (◇ᵗ-mono imp d)

Uᵗ-mono : ∀ {ℓr ℓa}
            {R : Set ℓr} {t : PTree E I R}
            {φ ψ φ' ψ' : LTLᵗ ℓa R}
            {tr : (Trace R) t}
          → (∀ {t'} {tr' : (Trace R) t'} → ⟦ φ ⟧ tr' → ⟦ φ' ⟧ tr')
          → (∀ {t'} {tr' : (Trace R) t'} → ⟦ ψ ⟧ tr' → ⟦ ψ' ⟧ tr')
          → (φ Uᵗ ψ) tr → (φ' Uᵗ ψ') tr
Uᵗ-mono impφ impψ (Uᵗ-now q)        = Uᵗ-now (impψ q)
Uᵗ-mono impφ impψ (Uᵗ-step p u)     = Uᵗ-step (impφ p) (Uᵗ-mono impφ impψ u)

-- §7.2 Surface-form monotonicities derivable via the equivalences.

F-mono : ∀ {ℓr ℓa}
           {R : Set ℓr} {t : PTree E I R}
           {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
         → (∀ {t'} {tr' : (Trace R) t'} → ⟦ φ ⟧ tr' → ⟦ ψ ⟧ tr')
         → ⟦ F_ φ ⟧ tr → ⟦ F_ ψ ⟧ tr
F-mono {tr = tr} imp (n , h , bef) = n , imp h , bef

U-mono : ∀ {ℓr ℓa}
           {R : Set ℓr} {t : PTree E I R}
           {φ ψ φ' ψ' : LTLᵗ ℓa R} {tr : (Trace R) t}
         → (∀ {t'} {tr' : (Trace R) t'} → ⟦ φ ⟧ tr' → ⟦ φ' ⟧ tr')
         → (∀ {t'} {tr' : (Trace R) t'} → ⟦ ψ ⟧ tr' → ⟦ ψ' ⟧ tr')
         → ⟦ φ U ψ ⟧ tr → ⟦ φ' U ψ' ⟧ tr
U-mono {tr = tr} impφ impψ (n , q , bef) = n , impψ q , (λ m m<n → impφ (bef m m<n))

G⁺-mono : ∀ {ℓr ℓa}
            {R : Set ℓr} {t : PTree E I R}
            {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
          → (∀ {t'} {tr' : (Trace R) t'} → ⟦ φ ⟧ tr' → ⟦ ψ ⟧ tr')
          → ⟦G⟧⁺ φ tr → ⟦G⟧⁺ ψ tr
G⁺-mono imp g n = imp (g n)

------------------------------------------------------------
-- §7.3 Closure
------------------------------------------------------------

□ᵗ-∧ : ∀ {ℓr ℓa}
         {R : Set ℓr} {t : PTree E I R}
         {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
       → □ᵗ φ tr → □ᵗ ψ tr → □ᵗ (φ ∧ ψ) tr
□ᵗ-now  (□ᵗ-∧ bP bQ) = □ᵗ-now bP , □ᵗ-now bQ
□ᵗ-tail (□ᵗ-∧ bP bQ) = □ᵗ-∧ (□ᵗ-tail bP) (□ᵗ-tail bQ)

-- For ◇ᵗ-∨ direction lemmas, ⟦ φ ∨ ψ ⟧ unfolds to a double-negation
-- form, so injecting ⟦ φ ⟧ requires applying the negation pair.
◇ᵗ-∨ᴸ : ∀ {ℓr ℓa}
          {R : Set ℓr} {t : PTree E I R}
          {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
        → ◇ᵗ φ tr → ◇ᵗ (φ ∨ ψ) tr
◇ᵗ-∨ᴸ {φ = φ} {ψ = ψ} = ◇ᵗ-mono inj
  where
    inj : ∀ {t'} {tr : Trace _ t'} → ⟦ φ ⟧ tr → ⟦ φ ∨ ψ ⟧ tr
    inj h (notφ , _) = notφ h

◇ᵗ-∨ᴿ : ∀ {ℓr ℓa}
          {R : Set ℓr} {t : PTree E I R}
          {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
        → ◇ᵗ ψ tr → ◇ᵗ (φ ∨ ψ) tr
◇ᵗ-∨ᴿ {φ = φ} {ψ = ψ} = ◇ᵗ-mono inj
  where
    inj : ∀ {t'} {tr : Trace _ t'} → ⟦ ψ ⟧ tr → ⟦ φ ∨ ψ ⟧ tr
    inj h (_ , notψ) = notψ h

------------------------------------------------------------
-- §7.4 Implications between operators
------------------------------------------------------------

□ᵗ⇒◇ᵗ : ∀ {ℓr ℓa}
          {R : Set ℓr} {t : PTree E I R}
          {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
        → □ᵗ φ tr → ◇ᵗ φ tr
□ᵗ⇒◇ᵗ b = ◇ᵗ-now (□ᵗ-now b)

Uᵗ⇒◇ᵗ : ∀ {ℓr ℓa}
          {R : Set ℓr} {t : PTree E I R}
          {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
        → (φ Uᵗ ψ) tr → ◇ᵗ ψ tr
Uᵗ⇒◇ᵗ (Uᵗ-now q)    = ◇ᵗ-now q
Uᵗ⇒◇ᵗ (Uᵗ-step _ u) = ◇ᵗ-later (Uᵗ⇒◇ᵗ u)

------------------------------------------------------------
-- §7.5 Idempotence
------------------------------------------------------------

-- Helper: drop addition law.
open import Data.Nat using (_+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)

-- Index-level addition law: dropping n then m lands at the same node as
-- dropping (n + m).
dropIdx-+ : ∀ {ℓr}
              {R : Set ℓr} {t : PTree E I R}
              (n m : ℕ) (tr : (Trace R) t)
            → dropIdx n (drop m tr) ≡ dropIdx (n + m) tr
dropIdx-+ n zero    tr rewrite +-identityʳ n = refl
dropIdx-+ n (suc m) tr rewrite +-suc n m     = dropIdx-+ n m (tail tr)

-- Trace-level addition law. The two traces sit at the (propositionally
-- equal) indices related by `dropIdx-+`, so we equate them after transport.
drop-+ : ∀ {ℓr}
           {R : Set ℓr} {t : PTree E I R}
           (n m : ℕ) (tr : (Trace R) t)
         → drop n (drop m tr) ≡ subst (Trace R) (sym (dropIdx-+ n m tr)) (drop (n + m) tr)
drop-+ n zero    tr rewrite +-identityʳ n = refl
drop-+ n (suc m) tr rewrite +-suc n m     = drop-+ n m (tail tr)

-- F idempotence at the semantics level.
FF⇒F : ∀ {ℓr ℓa}
         {R : Set ℓr} {t : PTree E I R}
         {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
       → ⟦ F_ (F_ φ) ⟧ tr → ⟦ F_ φ ⟧ tr
FF⇒F {φ = φ} ff = ◇ᵗ⇒F (collapse (F⇒◇ᵗ ff))
  where
    collapse : ∀ {t'} {tr' : Trace _ t'} → ◇ᵗ (F_ φ) tr' → ◇ᵗ φ tr'
    collapse (◇ᵗ-now h)   = F⇒◇ᵗ h
    collapse (◇ᵗ-later d) = ◇ᵗ-later (collapse d)

F⇒FF : ∀ {ℓr ℓa}
         {R : Set ℓr} {t : PTree E I R}
         {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
       → ⟦ F_ φ ⟧ tr → ⟦ F_ (F_ φ) ⟧ tr
F⇒FF f = zero , f , (λ _ ())

-- ⟦G⟧⁺ idempotence via drop-+.
open import Relation.Binary.PropositionalEquality using (subst)

-- Transporting a trace along an index equality does not change which
-- LTL formulas it satisfies.
⟦⟧-subst : ∀ {ℓr ℓa}
             {R : Set ℓr} {t₁ t₂ : PTree E I R}
             {φ : LTLᵗ ℓa R} (e : t₁ ≡ t₂) (w : (Trace R) t₁)
           → ⟦ φ ⟧ w → ⟦ φ ⟧ (subst (Trace R) e w)
⟦⟧-subst refl w h = h

⟦G⟧⁺-drop : ∀ {ℓr ℓa}
              {R : Set ℓr} {t : PTree E I R}
              {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
            → ⟦G⟧⁺ φ tr → ∀ k → ⟦G⟧⁺ φ (drop k tr)
⟦G⟧⁺-drop {φ = φ} {tr = tr} g k n =
  subst (λ tr' → ⟦ φ ⟧ tr') (sym (drop-+ n k tr))
        (⟦⟧-subst {φ = φ} (sym (dropIdx-+ n k tr)) (drop (n + k) tr) (g (n + k)))

⟦G⟧⁺-idem-fwd : ∀ {ℓr ℓa}
                  {R : Set ℓr} {t : PTree E I R}
                  {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
                → (∀ k → ⟦G⟧⁺ φ (drop k tr)) → ⟦G⟧⁺ φ tr
⟦G⟧⁺-idem-fwd g = g zero

⟦G⟧⁺-idem-bwd : ∀ {ℓr ℓa}
                  {R : Set ℓr} {t : PTree E I R}
                  {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
                → ⟦G⟧⁺ φ tr → (∀ k → ⟦G⟧⁺ φ (drop k tr))
⟦G⟧⁺-idem-bwd {φ = φ} {tr = tr} g k = ⟦G⟧⁺-drop {φ = φ} {tr = tr} g k

------------------------------------------------------------
-- §7.6 Fixpoint unfolds (unconditional via stuttering)
------------------------------------------------------------

F-unfold-fwd : ∀ {ℓr ℓa}
                 {R : Set ℓr} {t : PTree E I R}
                 {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
               → ⟦ F_ φ ⟧ tr → ⟦ φ ⟧ tr ⊎ ⟦ X_ (F_ φ) ⟧ tr
F-unfold-fwd (zero  , h , _) = inj₁ h
F-unfold-fwd {φ = φ} {tr = tr} (suc n , h , bef) =
  inj₂ (n , h , (λ m m<n → bef (suc m) (s≤s m<n)))
  where open import Data.Nat using (s≤s)

F-unfold-bwd : ∀ {ℓr ℓa}
                 {R : Set ℓr} {t : PTree E I R}
                 {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
               → ⟦ φ ⟧ tr ⊎ ⟦ X_ (F_ φ) ⟧ tr → ⟦ F_ φ ⟧ tr
F-unfold-bwd (inj₁ h)               = zero , h , (λ _ ())
F-unfold-bwd (inj₂ (n , h , bef))   = suc n , h , (λ m m<sn → go m m<sn)
  where
    open import Data.Nat using (s≤s)
    go : ∀ m → m < suc n → Lift _ ⊤
    go zero    _              = lift tt
    go (suc m) (s≤s m<n)      = bef m m<n

⟦G⟧⁺-unfold-fwd : ∀ {ℓr ℓa}
                    {R : Set ℓr} {t : PTree E I R}
                    {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
                  → ⟦G⟧⁺ φ tr → ⟦ φ ⟧ tr × ⟦G⟧⁺ φ (tail tr)
⟦G⟧⁺-unfold-fwd g = g zero , (λ n → g (suc n))

⟦G⟧⁺-unfold-bwd : ∀ {ℓr ℓa}
                    {R : Set ℓr} {t : PTree E I R}
                    {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
                  → ⟦ φ ⟧ tr × ⟦G⟧⁺ φ (tail tr) → ⟦G⟧⁺ φ tr
⟦G⟧⁺-unfold-bwd (h , g) zero    = h
⟦G⟧⁺-unfold-bwd (h , g) (suc n) = g n

U-unfold-fwd : ∀ {ℓr ℓa}
                 {R : Set ℓr} {t : PTree E I R}
                 {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
               → ⟦ φ U ψ ⟧ tr → ⟦ ψ ⟧ tr ⊎ (⟦ φ ⟧ tr × ⟦ X_ (φ U ψ) ⟧ tr)
U-unfold-fwd (zero  , q , _) = inj₁ q
U-unfold-fwd {φ = φ} {ψ} {tr} (suc n , q , bef) =
  inj₂ (bef zero (s≤s z≤n)
       , (n , q , (λ m m<n → bef (suc m) (s≤s m<n))))
  where open import Data.Nat using (s≤s; z≤n)

U-unfold-bwd : ∀ {ℓr ℓa}
                 {R : Set ℓr} {t : PTree E I R}
                 {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
               → ⟦ ψ ⟧ tr ⊎ (⟦ φ ⟧ tr × ⟦ X_ (φ U ψ) ⟧ tr) → ⟦ φ U ψ ⟧ tr
U-unfold-bwd (inj₁ q)                          = zero , q , (λ _ ())
U-unfold-bwd (inj₂ (p , (n , q , bef)))        = suc n , q , (λ m m<sn → go m m<sn)
  where
    open import Data.Nat using (s≤s)
    go : ∀ m → m < suc n → _
    go zero    _              = p
    go (suc m) (s≤s m<n)      = bef m m<n

------------------------------------------------------------
-- §7.7 De Morgan
------------------------------------------------------------

-- Constructive directions.
F¬⇒¬G : ∀ {ℓr ℓa}
          {R : Set ℓr} {t : PTree E I R}
          {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
        → ⟦ F_ (¬ φ) ⟧ tr → ⟦ ¬ (G_ φ) ⟧ tr
F¬⇒¬G f notG = notG f

G¬⇒¬F : ∀ {ℓr ℓa}
          {R : Set ℓr} {t : PTree E I R}
          {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
        → ⟦ G_ (¬ φ) ⟧ tr → ⟦ ¬ (F_ φ) ⟧ tr
G¬⇒¬F gn (n , h , bef) = gn (n , (λ k → k h) , bef)

-- Classical direction (postulated; same axiomatic basis as ⟦G⟧⇒⟦G⟧⁺).
postulate
-- This can be derived from LEM and see ClassicalFromLEM.agda where this lemma is proved from a single dne
  ¬G⇒F¬ : ∀ {ℓr ℓa}
            {R : Set ℓr} {t : PTree E I R}
            {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
          → ⟦ ¬ (G_ φ) ⟧ tr → ⟦ F_ (¬ φ) ⟧ tr

-- Constructive direction (NOT classical): ⟦ G_ (¬ φ) ⟧ tr reduces to
-- ⟦ F_ (¬ ¬ φ) ⟧ tr → Lift ⊥; given (n , nnφ , bef), feed the negation
-- (λ p → notF (n , p , bef)) into the double-negated point nnφ.
¬F⇒G¬ : ∀ {ℓr ℓa}
          {R : Set ℓr} {t : PTree E I R}
          {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
        → ⟦ ¬ (F_ φ) ⟧ tr → ⟦ G_ (¬ φ) ⟧ tr
¬F⇒G¬ notF (n , nnφ , bef) = nnφ (λ p → notF (n , p , bef))

------------------------------------------------------------
-- §7.8 Surface implications
------------------------------------------------------------

⟦G⟧⁺⇒F : ∀ {ℓr ℓa}
           {R : Set ℓr} {t : PTree E I R}
           {φ : LTLᵗ ℓa R} {tr : (Trace R) t}
         → ⟦G⟧⁺ φ tr → ⟦ F_ φ ⟧ tr
⟦G⟧⁺⇒F g = zero , g zero , (λ _ ())

U⇒F : ∀ {ℓr ℓa}
        {R : Set ℓr} {t : PTree E I R}
        {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
      → ⟦ φ U ψ ⟧ tr → ⟦ F_ ψ ⟧ tr
U⇒F (n , q , _) = n , q , (λ _ _ → lift tt)

⟦G⟧⁺⇒W : ∀ {ℓr ℓa}
           {R : Set ℓr} {t : PTree E I R}
           {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
         → ⟦G⟧⁺ φ tr → ⟦ φ W ψ ⟧ tr
⟦G⟧⁺⇒W {φ = φ} {tr = tr} g = λ p → (proj₂ p) (⟦G⟧⁺⇒⟦G⟧ {φ = φ} {tr = tr} g)

U⇒W : ∀ {ℓr ℓa}
        {R : Set ℓr} {t : PTree E I R}
        {φ ψ : LTLᵗ ℓa R} {tr : (Trace R) t}
      → ⟦ φ U ψ ⟧ tr → ⟦ φ W ψ ⟧ tr
U⇒W {φ = φ} {tr = tr} u = λ p → (proj₁ p) u

------------------------------------------------------------
-- §8 Sanity examples (trace witnesses only — v1 stops short of ⊨ proofs)
------------------------------------------------------------

private
  open import Function using (case_of_)

  -- Stop: the empty-offer, empty-τ react node (= `deadlock` from
  -- Process_Trees, the CSP Stop). Kept model-agnostic in `I`.
  Stop : ∀ {ℓr} {R : Set ℓr} → PTree E I R
  Stop = deadlock

  -- Stop is stuck: no LTS transition is enabled.
  Stop-IsStuck : ∀ {ℓr} {R : Set ℓr} → IsStuck (Stop {R = R})
  Stop-IsStuck (sRet eq)    = case eq of λ ()
  Stop-IsStuck (sSil eq)    = case eq of λ ()
  Stop-IsStuck (sVis refl br) = case br of λ ()
  Stop-IsStuck (sTau refl br) = case br of λ ()

  -- Canonical trace from Stop.
  StopTrace : ∀ {ℓr} {R : Set ℓr} → (Trace R) Stop
  StopTrace = stuck Stop-IsStuck

  -- TODO v2: Stop ⊨ atStuck — needs a "every trace rooted at Stop is `stuck _`"
  -- uniqueness lemma. Deferred.

  -- Loop: τ-self-looping divergent PTree.
  loop : ∀ {ℓr} {R : Set ℓr} → PTree E I R
  PTree.force loop = sil loop

  loop-Div : ∀ {ℓr} {R : Set ℓr} → Diverges (loop {R = R})
  Diverges.next loop-Div = loop
  Diverges.step loop-Div = sSil refl
  Diverges.rest loop-Div = loop-Div

  -- Canonical trace from loop.
  loopTrace : ∀ {ℓr} {R : Set ℓr} → (Trace R) loop
  loopTrace = div loop-Div

  -- TODO v2: loop ⊨ atDiv — needs uniqueness lemma. Deferred.

  -- Skip: explicit version to match the Trace type.
  Skip' : ∀ {ℓr} {R : Set ℓr} (r : R) → PTree E I R
  PTree.force (Skip' r) = ret r

  -- Skip's done-rooted trace.
  SkipTraceDone : ∀ {ℓr} {R : Set ℓr} (r : R) → (Trace R) (Skip' r)
  SkipTraceDone r = done {t = Skip' r} refl

  -- TODO v2: Skip-rooted traces include a step shape too (Skip ─[ ev (√ tt) ]─►
  -- deadlock). Showing `Skip ⊨ atDone _ ∨ X_ atStuck` requires both shapes plus
  -- a case-split — deferred.

------------------------------------------------------------
-- v2 TODO: DR-weak bisim invariance
--
-- The headline meta-theorem is:
--
--   ⊨-DRWB-invariant : ∀ {t₁ t₂} (φ : LTLᵗ ℓa R)
--                    → BisimStable φ
--                    → t₁ ≈ᴰᴿ t₂
--                    → t₁ ⊨ φ ↔ t₂ ⊨ φ
--
-- where BisimStable is an inductive Set-valued predicate whose
-- substantive case is `atom P` and demands DR-weak-bisim-stability
-- of the frame predicate P.
--
-- Proving it requires a frame-by-frame trace transport lemma
-- relating traces from t₁ and t₂ via the bisim.
------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module ITree_Relations.LTL.Traces_Based where

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
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
-- Note: we deliberately do NOT import Relation.Nullary.¬_; LTLᵗ has its
-- own `¬_` constructor and we encode semantic negation as `… → ⊥`.

open import Interaction_Trees hiding (div)
  -- `Interaction_Trees.div` is the divergent ITree itself; we hide it
  -- so we can use `div` as a Frame constructor name.
open import ITree_Relations.LTS
open import ITree_Relations.FailuresDivergences using (Divergent)

open ITree

------------------------------------------------------------
-- §1 Frame
--
-- A Frame is the unit of observation that a Trace exposes at each
-- point and that atoms consume. Four frame kinds match the four
-- DR-weak observations: visible step, √-termination, deadlock, and
-- τ-divergence.
------------------------------------------------------------

data Frame {ℓ ℓe ℓi ℓr : Level}
           (E : Set ℓ → Set ℓe)
           (I : Set ℓ → Set ℓi)
           (R : Set ℓr)
         : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  step  : ITree E I R → Event√ E R → Frame E I R
  done  : ITree E I R → R          → Frame E I R
  stuck : ITree E I R              → Frame E I R
  div   : ITree E I R              → Frame E I R

frameState : ∀ {ℓ ℓe ℓi ℓr}
               {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             → Frame E I R → ITree E I R
frameState (step  t _) = t
frameState (done  t _) = t
frameState (stuck t  ) = t
frameState (div   t  ) = t

IsTerminator : ∀ {ℓ ℓe ℓi ℓr}
                 {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               → Frame E I R → Set
IsTerminator (step  _ _) = ⊥
IsTerminator (done  _ _) = ⊤
IsTerminator (stuck _  ) = ⊤
IsTerminator (div   _  ) = ⊤

------------------------------------------------------------
-- §2 Trace
------------------------------------------------------------

-- A state is stuck (real deadlock) when no LTS label is enabled.
IsStuck : ∀ {ℓ ℓe ℓi ℓr}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          → ITree E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr)
IsStuck {E = E} {I = I} {R = R} t =
  ∀ {l : Label E R} {t' : ITree E I R} → t ─[ l ]─► t' → ⊥
  -- ⊥ here is non-polymorphic Data.Empty.⊥ at level 0, which embeds
  -- into the codomain level lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr via _⊔_.

-- Intrinsic, finite-or-infinite, valid-by-construction execution trace.
-- `step` is the only coinductive carrier (its tail is thunked); the
-- three terminator constructors are leaves.

mutual
  data Trace {ℓ ℓe ℓi ℓr : Level}
             (E : Set ℓ → Set ℓe)
             (I : Set ℓ → Set ℓi)
             (R : Set ℓr)
           : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
    step  : ∀ {t : ITree E I R} {e : Event√ E R} {t' : ITree E I R}
          → t ═[ ev e ]═► t' → ∞Trace E I R → Trace E I R
    done  : ∀ {t : ITree E I R} {r : R}
          → ITree.force t ≡ ret r → Trace E I R
    stuck : ∀ {t : ITree E I R}
          → IsStuck t → Trace E I R
    div   : ∀ {t : ITree E I R}
          → Divergent t → Trace E I R

  record ∞Trace {ℓ ℓe ℓi ℓr : Level}
                (E : Set ℓ → Set ℓe)
                (I : Set ℓ → Set ℓi)
                (R : Set ℓr)
              : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
    coinductive
    field
      force : Trace E I R

open ∞Trace public

-- The frame currently observed by the trace.
frameOf : ∀ {ℓ ℓe ℓi ℓr}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          → Trace E I R → Frame E I R
frameOf (step {t} {e} _ _) = step t e
frameOf (done {t} {r} _)   = done t r
frameOf (stuck {t} _)      = stuck t
frameOf (div {t} _)        = div t

-- Total tail. At terminator frames, `tail` self-loops (stuttering convention).
tail : ∀ {ℓ ℓe ℓi ℓr}
         {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
       → Trace E I R → Trace E I R
tail (step _ tr)        = ∞Trace.force tr
tail tr@(done _)        = tr
tail tr@(stuck _)       = tr
tail tr@(div _)         = tr

drop : ∀ {ℓ ℓe ℓi ℓr}
         {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
       → ℕ → Trace E I R → Trace E I R
drop zero    tr = tr
drop (suc n) tr = drop n (tail tr)

-- Stutter law for tail at terminator frames.
tail-stutter : ∀ {ℓ ℓe ℓi ℓr}
                 {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                 (tr : Trace E I R)
               → IsTerminator (frameOf tr) → tail tr ≡ tr
tail-stutter (step _ _) ()
tail-stutter (done _)   _ = refl
tail-stutter (stuck _)  _ = refl
tail-stutter (div _)    _ = refl

drop-stutter : ∀ {ℓ ℓe ℓi ℓr}
                 {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                 (n : ℕ) (tr : Trace E I R)
               → IsTerminator (frameOf tr) → drop n tr ≡ tr
drop-stutter zero    tr term = refl
drop-stutter (suc n) tr term
  rewrite tail-stutter tr term = drop-stutter n tr term

------------------------------------------------------------
-- §4 Syntax
------------------------------------------------------------

FramePred : ∀ {ℓ ℓe ℓi ℓr} (ℓa : Level)
              (E : Set ℓ → Set ℓe) (I : Set ℓ → Set ℓi) (R : Set ℓr)
            → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓa)
FramePred ℓa E I R = Frame E I R → Set ℓa

-- Six-constructor primitive syntax. Everything else is a definition.
data LTLᵗ {ℓ ℓe ℓi ℓr : Level} (ℓa : Level)
          (E : Set ℓ → Set ℓe)
          (I : Set ℓ → Set ℓi)
          (R : Set ℓr)
        : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ lsuc ℓa) where
  ⊤'    : LTLᵗ ℓa E I R
  atom  : FramePred ℓa E I R                   → LTLᵗ ℓa E I R
  ¬_    : LTLᵗ ℓa E I R                        → LTLᵗ ℓa E I R
  _∧_   : LTLᵗ ℓa E I R → LTLᵗ ℓa E I R       → LTLᵗ ℓa E I R
  X_    : LTLᵗ ℓa E I R                        → LTLᵗ ℓa E I R
  _U_   : LTLᵗ ℓa E I R → LTLᵗ ℓa E I R       → LTLᵗ ℓa E I R

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
⟦_⟧ : ∀ {ℓ ℓe ℓi ℓr ℓa}
        {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → LTLᵗ ℓa E I R → Trace E I R → Set ℓa
⟦_⟧ {ℓa = ℓa} ⊤'      tr = Lift ℓa ⊤
⟦ atom P  ⟧ tr = P (frameOf tr)
⟦_⟧ {ℓa = ℓa} (¬ φ)   tr = ⟦ φ ⟧ tr → Lift ℓa ⊥
⟦ φ ∧ ψ   ⟧ tr = ⟦ φ ⟧ tr × ⟦ ψ ⟧ tr
⟦ X φ     ⟧ tr = ⟦ φ ⟧ (tail tr)
⟦ φ U ψ   ⟧ tr = Σ ℕ (λ n → ⟦ ψ ⟧ (drop n tr)
                          × (∀ m → m < n → ⟦ φ ⟧ (drop m tr)))

-- Satisfaction (≡-rooted).
_⊨_ : ∀ {ℓ ℓe ℓi ℓr ℓa}
        {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → ITree E I R → LTLᵗ ℓa E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓa)
t ⊨ φ = ∀ tr → frameState (frameOf tr) ≡ t → ⟦ φ ⟧ tr

------------------------------------------------------------
-- §4.4 Derived operators (definitions, not constructors)
------------------------------------------------------------

⊥' : ∀ {ℓ ℓe ℓi ℓr ℓa}
       {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
     → LTLᵗ ℓa E I R
⊥' = ¬ ⊤'

_∨_ : ∀ {ℓ ℓe ℓi ℓr ℓa}
        {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → LTLᵗ ℓa E I R → LTLᵗ ℓa E I R → LTLᵗ ℓa E I R
φ ∨ ψ = ¬ ((¬ φ) ∧ (¬ ψ))

_⇒_ : ∀ {ℓ ℓe ℓi ℓr ℓa}
        {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → LTLᵗ ℓa E I R → LTLᵗ ℓa E I R → LTLᵗ ℓa E I R
φ ⇒ ψ = (¬ φ) ∨ ψ

F_ : ∀ {ℓ ℓe ℓi ℓr ℓa}
       {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
     → LTLᵗ ℓa E I R → LTLᵗ ℓa E I R
F_ φ = ⊤' U φ

G_ : ∀ {ℓ ℓe ℓi ℓr ℓa}
       {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
     → LTLᵗ ℓa E I R → LTLᵗ ℓa E I R
G_ φ = ¬ (F_ (¬ φ))

_W_ : ∀ {ℓ ℓe ℓi ℓr ℓa}
        {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → LTLᵗ ℓa E I R → LTLᵗ ℓa E I R → LTLᵗ ℓa E I R
φ W ψ = (φ U ψ) ∨ (G_ φ)

_R_ : ∀ {ℓ ℓe ℓi ℓr ℓa}
        {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
      → LTLᵗ ℓa E I R → LTLᵗ ℓa E I R → LTLᵗ ℓa E I R
φ R ψ = ¬ ((¬ φ) U (¬ ψ))

infixr 5 _∨_
infixr 4 _⇒_
infix  4 _W_
infix  4 _R_
infix  7 F_
infix  7 G_

------------------------------------------------------------
-- §3 Convenience atoms (LTLᵗ values)
------------------------------------------------------------

-- Frame is `step` whose event is a `√ r` for some r.
atTick : ∀ {ℓ ℓe ℓi ℓr}
           {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         → LTLᵗ lzero E I R
atTick = atom λ
  { (step _ (√ _))   → ⊤
  ; (step _ (evl _)) → ⊥
  ; (done  _ _)      → ⊥
  ; (stuck _)        → ⊥
  ; (div   _)        → ⊥
  }

-- Frame is `done` with value satisfying P.
atDone : ∀ {ℓ ℓe ℓi ℓr ℓa}
           {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         → (R → Set ℓa) → LTLᵗ ℓa E I R
atDone {ℓa = ℓa} P = atom λ
  { (step  _ _) → Lift ℓa ⊥
  ; (done  _ r) → P r
  ; (stuck _)   → Lift ℓa ⊥
  ; (div   _)   → Lift ℓa ⊥
  }

-- Frame is `stuck`.
atStuck : ∀ {ℓ ℓe ℓi ℓr}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          → LTLᵗ lzero E I R
atStuck = atom λ
  { (step  _ _) → ⊥
  ; (done  _ _) → ⊥
  ; (stuck _)   → ⊤
  ; (div   _)   → ⊥
  }

-- Frame is `div`.
atDiv : ∀ {ℓ ℓe ℓi ℓr}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        → LTLᵗ lzero E I R
atDiv = atom λ
  { (step  _ _) → ⊥
  ; (done  _ _) → ⊥
  ; (stuck _)   → ⊥
  ; (div   _)   → ⊤
  }

-- Frame is `step` with a visible (non-tick) event.
atVis : ∀ {ℓ ℓe ℓi ℓr}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        → LTLᵗ lzero E I R
atVis = atom λ
  { (step _ (evl _))   → ⊤
  ; (step _ (√ _))     → ⊥
  ; (done  _ _)        → ⊥
  ; (stuck _)          → ⊥
  ; (div   _)          → ⊥
  }

-- The state in the current frame is at a `ret r` node with P r.
atRet : ∀ {ℓ ℓe ℓi ℓr ℓa}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        → (R → Set ℓa) → LTLᵗ ℓa E I R
atRet {ℓa = ℓa} P = atom λ fr → returnsWith′ P (frameState fr)
  where
    returnsWith′ : ∀ {ℓ ℓe ℓi ℓr}
                     {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                   → (R → Set ℓa) → ITree E I R → Set ℓa
    returnsWith′ P t with ITree.force t
    ... | ret r = P r
    ... | _     = Lift ℓa ⊥

-- Alias matching the old file's name.
returnsWith : ∀ {ℓ ℓe ℓi ℓr ℓa}
                {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              → (R → Set ℓa) → LTLᵗ ℓa E I R
returnsWith = atRet

-- The state in the current frame is stable in the LTS sense.
isStableᵗ : ∀ {ℓ ℓe ℓi ℓr}
              {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            → LTLᵗ lzero E I R
isStableᵗ = atom λ fr → isStable (frameState fr)

------------------------------------------------------------
-- §6 Coinductive / inductive presentations
------------------------------------------------------------

record □ᵗ {ℓ ℓe ℓi ℓr ℓa}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          (φ : LTLᵗ ℓa E I R) (tr : Trace E I R)
        : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓa) where
  coinductive
  field
    □ᵗ-now  : ⟦ φ ⟧ tr
    □ᵗ-tail : □ᵗ φ (tail tr)

open □ᵗ public

data ◇ᵗ {ℓ ℓe ℓi ℓr ℓa}
        {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        (φ : LTLᵗ ℓa E I R)
      : Trace E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓa) where
  ◇ᵗ-now   : ∀ {tr : Trace E I R} → ⟦ φ ⟧ tr        → ◇ᵗ φ tr
  ◇ᵗ-later : ∀ {tr : Trace E I R} → ◇ᵗ φ (tail tr) → ◇ᵗ φ tr

data _Uᵗ_ {ℓ ℓe ℓi ℓr ℓa}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          (φ ψ : LTLᵗ ℓa E I R)
        : Trace E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr ⊔ ℓa) where
  Uᵗ-now  : ∀ {tr} → ⟦ ψ ⟧ tr                                → (φ Uᵗ ψ) tr
  Uᵗ-step : ∀ {tr} → ⟦ φ ⟧ tr → (φ Uᵗ ψ) (tail tr)          → (φ Uᵗ ψ) tr

------------------------------------------------------------
-- §6.1 Equivalences ⟦ F ⟧ ↔ ◇ᵗ, ⟦G⟧⁺ ↔ □ᵗ, ⟦ U ⟧ ↔ Uᵗ
------------------------------------------------------------

-- Helper for F⇒◇ᵗ: recurses structurally on n (no NON_TERMINATING needed).
F⇒◇ᵗ-helper : ∀ {ℓ ℓe ℓi ℓr ℓa}
                {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                {φ : LTLᵗ ℓa E I R}
                (n : ℕ) (tr : Trace E I R)
              → ⟦ φ ⟧ (drop n tr) → ◇ᵗ φ tr
F⇒◇ᵗ-helper zero    tr h = ◇ᵗ-now h
F⇒◇ᵗ-helper (suc n) tr h = ◇ᵗ-later (F⇒◇ᵗ-helper n (tail tr) h)

F⇒◇ᵗ : ∀ {ℓ ℓe ℓi ℓr ℓa}
         {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
       → ⟦ F_ φ ⟧ tr → ◇ᵗ φ tr
F⇒◇ᵗ {tr = tr} (n , h , _) = F⇒◇ᵗ-helper n tr h

◇ᵗ⇒F : ∀ {ℓ ℓe ℓi ℓr ℓa}
         {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
       → ◇ᵗ φ tr → ⟦ F_ φ ⟧ tr
◇ᵗ⇒F (◇ᵗ-now h)   = zero , h , (λ _ ())
◇ᵗ⇒F (◇ᵗ-later e) with ◇ᵗ⇒F e
... | n , h , bef = suc n , h , λ where
                                  zero    _              → lift tt
                                  (suc m) (s≤s m<sn)     → bef m m<sn
  where open import Data.Nat using (s≤s)

-- Σ-form of G semantics (positive). Constructively equivalent to □ᵗ;
-- classically equivalent to ⟦ G_ φ ⟧.
⟦G⟧⁺ : ∀ {ℓ ℓe ℓi ℓr ℓa}
         {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
       → LTLᵗ ℓa E I R → Trace E I R → Set ℓa
⟦G⟧⁺ φ tr = ∀ n → ⟦ φ ⟧ (drop n tr)

⟦G⟧⁺⇒□ᵗ : ∀ {ℓ ℓe ℓi ℓr ℓa}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
          → ⟦G⟧⁺ φ tr → □ᵗ φ tr
□ᵗ-now  (⟦G⟧⁺⇒□ᵗ g)            = g zero
□ᵗ-tail (⟦G⟧⁺⇒□ᵗ {tr = tr} g) = ⟦G⟧⁺⇒□ᵗ (λ n → g (suc n))

□ᵗ⇒⟦G⟧⁺ : ∀ {ℓ ℓe ℓi ℓr ℓa}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
          → □ᵗ φ tr → ⟦G⟧⁺ φ tr
□ᵗ⇒⟦G⟧⁺ b zero    = □ᵗ-now b
□ᵗ⇒⟦G⟧⁺ b (suc n) = □ᵗ⇒⟦G⟧⁺ (□ᵗ-tail b) n

-- Constructive direction: ⟦G⟧⁺ ⇒ ⟦ G_ ⟧
⟦G⟧⁺⇒⟦G⟧ : ∀ {ℓ ℓe ℓi ℓr ℓa}
             {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
             {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
           → ⟦G⟧⁺ φ tr → ⟦ G_ φ ⟧ tr
⟦G⟧⁺⇒⟦G⟧ {φ = φ} {tr = tr} g (n , notφ , _) = notφ (g n)

-- Classical direction. The only classical axiom in the file; users who
-- want to avoid it should phrase global properties using □ᵗ or ⟦G⟧⁺.
postulate
  ⟦G⟧⇒⟦G⟧⁺ : ∀ {ℓ ℓe ℓi ℓr ℓa}
               {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
               {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
             → ⟦ G_ φ ⟧ tr → ⟦G⟧⁺ φ tr

-- Helper for U⇒Uᵗ: recurses structurally on n.
U⇒Uᵗ-helper : ∀ {ℓ ℓe ℓi ℓr ℓa}
                {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                {φ ψ : LTLᵗ ℓa E I R}
                (n : ℕ) (tr : Trace E I R)
              → ⟦ ψ ⟧ (drop n tr)
              → (∀ m → m < n → ⟦ φ ⟧ (drop m tr))
              → (φ Uᵗ ψ) tr
U⇒Uᵗ-helper zero    tr q _   = Uᵗ-now q
U⇒Uᵗ-helper (suc n) tr q bef =
  Uᵗ-step (bef zero (s≤s z≤n))
          (U⇒Uᵗ-helper n (tail tr) q (λ m m<n → bef (suc m) (s≤s m<n)))
  where open import Data.Nat using (s≤s; z≤n)

U⇒Uᵗ : ∀ {ℓ ℓe ℓi ℓr ℓa}
         {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
       → ⟦ φ U ψ ⟧ tr → (φ Uᵗ ψ) tr
U⇒Uᵗ {tr = tr} (n , q , bef) = U⇒Uᵗ-helper n tr q bef

Uᵗ⇒U : ∀ {ℓ ℓe ℓi ℓr ℓa}
         {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
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

□ᵗ-mono : ∀ {ℓ ℓe ℓi ℓr ℓa ℓb}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {φ : LTLᵗ ℓa E I R} {ψ : LTLᵗ ℓb E I R}
            {tr : Trace E I R}
          → (∀ {tr'} → ⟦ φ ⟧ tr' → ⟦ ψ ⟧ tr')
          → □ᵗ φ tr → □ᵗ ψ tr
□ᵗ-now  (□ᵗ-mono imp b) = imp (□ᵗ-now b)
□ᵗ-tail (□ᵗ-mono imp b) = □ᵗ-mono imp (□ᵗ-tail b)

◇ᵗ-mono : ∀ {ℓ ℓe ℓi ℓr ℓa ℓb}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {φ : LTLᵗ ℓa E I R} {ψ : LTLᵗ ℓb E I R}
            {tr : Trace E I R}
          → (∀ {tr'} → ⟦ φ ⟧ tr' → ⟦ ψ ⟧ tr')
          → ◇ᵗ φ tr → ◇ᵗ ψ tr
◇ᵗ-mono imp (◇ᵗ-now h)   = ◇ᵗ-now (imp h)
◇ᵗ-mono imp (◇ᵗ-later d) = ◇ᵗ-later (◇ᵗ-mono imp d)

Uᵗ-mono : ∀ {ℓ ℓe ℓi ℓr ℓa}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {φ ψ φ' ψ' : LTLᵗ ℓa E I R}
            {tr : Trace E I R}
          → (∀ {tr'} → ⟦ φ ⟧ tr' → ⟦ φ' ⟧ tr')
          → (∀ {tr'} → ⟦ ψ ⟧ tr' → ⟦ ψ' ⟧ tr')
          → (φ Uᵗ ψ) tr → (φ' Uᵗ ψ') tr
Uᵗ-mono impφ impψ (Uᵗ-now q)        = Uᵗ-now (impψ q)
Uᵗ-mono impφ impψ (Uᵗ-step p u)     = Uᵗ-step (impφ p) (Uᵗ-mono impφ impψ u)

-- §7.2 Surface-form monotonicities derivable via the equivalences.

F-mono : ∀ {ℓ ℓe ℓi ℓr ℓa}
           {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
         → (∀ {tr'} → ⟦ φ ⟧ tr' → ⟦ ψ ⟧ tr')
         → ⟦ F_ φ ⟧ tr → ⟦ F_ ψ ⟧ tr
F-mono {tr = tr} imp (n , h , bef) = n , imp h , bef

U-mono : ∀ {ℓ ℓe ℓi ℓr ℓa}
           {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {φ ψ φ' ψ' : LTLᵗ ℓa E I R} {tr : Trace E I R}
         → (∀ {tr'} → ⟦ φ ⟧ tr' → ⟦ φ' ⟧ tr')
         → (∀ {tr'} → ⟦ ψ ⟧ tr' → ⟦ ψ' ⟧ tr')
         → ⟦ φ U ψ ⟧ tr → ⟦ φ' U ψ' ⟧ tr
U-mono {tr = tr} impφ impψ (n , q , bef) = n , impψ q , (λ m m<n → impφ (bef m m<n))

G⁺-mono : ∀ {ℓ ℓe ℓi ℓr ℓa}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
          → (∀ {tr'} → ⟦ φ ⟧ tr' → ⟦ ψ ⟧ tr')
          → ⟦G⟧⁺ φ tr → ⟦G⟧⁺ ψ tr
G⁺-mono imp g n = imp (g n)

------------------------------------------------------------
-- §7.3 Closure
------------------------------------------------------------

□ᵗ-∧ : ∀ {ℓ ℓe ℓi ℓr ℓa}
         {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
       → □ᵗ φ tr → □ᵗ ψ tr → □ᵗ (φ ∧ ψ) tr
□ᵗ-now  (□ᵗ-∧ bP bQ) = □ᵗ-now bP , □ᵗ-now bQ
□ᵗ-tail (□ᵗ-∧ bP bQ) = □ᵗ-∧ (□ᵗ-tail bP) (□ᵗ-tail bQ)

-- For ◇ᵗ-∨ direction lemmas, ⟦ φ ∨ ψ ⟧ unfolds to a double-negation
-- form, so injecting ⟦ φ ⟧ requires applying the negation pair.
◇ᵗ-∨ᴸ : ∀ {ℓ ℓe ℓi ℓr ℓa}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
        → ◇ᵗ φ tr → ◇ᵗ (φ ∨ ψ) tr
◇ᵗ-∨ᴸ {φ = φ} {ψ = ψ} = ◇ᵗ-mono inj
  where
    inj : ∀ {tr} → ⟦ φ ⟧ tr → ⟦ φ ∨ ψ ⟧ tr
    inj h (notφ , _) = notφ h

◇ᵗ-∨ᴿ : ∀ {ℓ ℓe ℓi ℓr ℓa}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
        → ◇ᵗ ψ tr → ◇ᵗ (φ ∨ ψ) tr
◇ᵗ-∨ᴿ {φ = φ} {ψ = ψ} = ◇ᵗ-mono inj
  where
    inj : ∀ {tr} → ⟦ ψ ⟧ tr → ⟦ φ ∨ ψ ⟧ tr
    inj h (_ , notψ) = notψ h

------------------------------------------------------------
-- §7.4 Implications between operators
------------------------------------------------------------

□ᵗ⇒◇ᵗ : ∀ {ℓ ℓe ℓi ℓr ℓa}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
        → □ᵗ φ tr → ◇ᵗ φ tr
□ᵗ⇒◇ᵗ b = ◇ᵗ-now (□ᵗ-now b)

Uᵗ⇒◇ᵗ : ∀ {ℓ ℓe ℓi ℓr ℓa}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
        → (φ Uᵗ ψ) tr → ◇ᵗ ψ tr
Uᵗ⇒◇ᵗ (Uᵗ-now q)    = ◇ᵗ-now q
Uᵗ⇒◇ᵗ (Uᵗ-step _ u) = ◇ᵗ-later (Uᵗ⇒◇ᵗ u)

------------------------------------------------------------
-- §7.5 Idempotence
------------------------------------------------------------

-- Helper: drop addition law.
open import Data.Nat using (_+_)
open import Data.Nat.Properties using (+-identityʳ; +-suc)

drop-+ : ∀ {ℓ ℓe ℓi ℓr}
           {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           (n m : ℕ) (tr : Trace E I R)
         → drop n (drop m tr) ≡ drop (n + m) tr
drop-+ n zero    tr rewrite +-identityʳ n = refl
drop-+ n (suc m) tr rewrite +-suc n m     = drop-+ n m (tail tr)

-- F idempotence at the semantics level.
FF⇒F : ∀ {ℓ ℓe ℓi ℓr ℓa}
         {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
       → ⟦ F_ (F_ φ) ⟧ tr → ⟦ F_ φ ⟧ tr
FF⇒F {φ = φ} ff = ◇ᵗ⇒F (collapse (F⇒◇ᵗ ff))
  where
    collapse : ∀ {tr'} → ◇ᵗ (F_ φ) tr' → ◇ᵗ φ tr'
    collapse (◇ᵗ-now h)   = F⇒◇ᵗ h
    collapse (◇ᵗ-later d) = ◇ᵗ-later (collapse d)

F⇒FF : ∀ {ℓ ℓe ℓi ℓr ℓa}
         {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
         {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
       → ⟦ F_ φ ⟧ tr → ⟦ F_ (F_ φ) ⟧ tr
F⇒FF f = zero , f , (λ _ ())

-- ⟦G⟧⁺ idempotence via drop-+.
open import Relation.Binary.PropositionalEquality using (subst)

⟦G⟧⁺-drop : ∀ {ℓ ℓe ℓi ℓr ℓa}
              {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
              {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
            → ⟦G⟧⁺ φ tr → ∀ k → ⟦G⟧⁺ φ (drop k tr)
⟦G⟧⁺-drop {φ = φ} {tr = tr} g k n =
  subst (λ tr' → ⟦ φ ⟧ tr') (sym (drop-+ n k tr)) (g (n + k))

⟦G⟧⁺-idem-fwd : ∀ {ℓ ℓe ℓi ℓr ℓa}
                  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                  {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
                → (∀ k → ⟦G⟧⁺ φ (drop k tr)) → ⟦G⟧⁺ φ tr
⟦G⟧⁺-idem-fwd g = g zero

⟦G⟧⁺-idem-bwd : ∀ {ℓ ℓe ℓi ℓr ℓa}
                  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                  {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
                → ⟦G⟧⁺ φ tr → (∀ k → ⟦G⟧⁺ φ (drop k tr))
⟦G⟧⁺-idem-bwd {φ = φ} {tr = tr} g k = ⟦G⟧⁺-drop {φ = φ} {tr = tr} g k

------------------------------------------------------------
-- §7.6 Fixpoint unfolds (unconditional via stuttering)
------------------------------------------------------------

F-unfold-fwd : ∀ {ℓ ℓe ℓi ℓr ℓa}
                 {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                 {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
               → ⟦ F_ φ ⟧ tr → ⟦ φ ⟧ tr ⊎ ⟦ X_ (F_ φ) ⟧ tr
F-unfold-fwd (zero  , h , _) = inj₁ h
F-unfold-fwd {φ = φ} {tr = tr} (suc n , h , bef) =
  inj₂ (n , h , (λ m m<n → bef (suc m) (s≤s m<n)))
  where open import Data.Nat using (s≤s)

F-unfold-bwd : ∀ {ℓ ℓe ℓi ℓr ℓa}
                 {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                 {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
               → ⟦ φ ⟧ tr ⊎ ⟦ X_ (F_ φ) ⟧ tr → ⟦ F_ φ ⟧ tr
F-unfold-bwd (inj₁ h)               = zero , h , (λ _ ())
F-unfold-bwd (inj₂ (n , h , bef))   = suc n , h , (λ m m<sn → go m m<sn)
  where
    open import Data.Nat using (s≤s)
    go : ∀ m → m < suc n → Lift _ ⊤
    go zero    _              = lift tt
    go (suc m) (s≤s m<n)      = bef m m<n

⟦G⟧⁺-unfold-fwd : ∀ {ℓ ℓe ℓi ℓr ℓa}
                    {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                    {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
                  → ⟦G⟧⁺ φ tr → ⟦ φ ⟧ tr × ⟦G⟧⁺ φ (tail tr)
⟦G⟧⁺-unfold-fwd g = g zero , (λ n → g (suc n))

⟦G⟧⁺-unfold-bwd : ∀ {ℓ ℓe ℓi ℓr ℓa}
                    {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                    {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
                  → ⟦ φ ⟧ tr × ⟦G⟧⁺ φ (tail tr) → ⟦G⟧⁺ φ tr
⟦G⟧⁺-unfold-bwd (h , g) zero    = h
⟦G⟧⁺-unfold-bwd (h , g) (suc n) = g n

U-unfold-fwd : ∀ {ℓ ℓe ℓi ℓr ℓa}
                 {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                 {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
               → ⟦ φ U ψ ⟧ tr → ⟦ ψ ⟧ tr ⊎ (⟦ φ ⟧ tr × ⟦ X_ (φ U ψ) ⟧ tr)
U-unfold-fwd (zero  , q , _) = inj₁ q
U-unfold-fwd {φ = φ} {ψ} {tr} (suc n , q , bef) =
  inj₂ (bef zero (s≤s z≤n)
       , (n , q , (λ m m<n → bef (suc m) (s≤s m<n))))
  where open import Data.Nat using (s≤s; z≤n)

U-unfold-bwd : ∀ {ℓ ℓe ℓi ℓr ℓa}
                 {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
                 {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
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
F¬⇒¬G : ∀ {ℓ ℓe ℓi ℓr ℓa}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
        → ⟦ F_ (¬ φ) ⟧ tr → ⟦ ¬ (G_ φ) ⟧ tr
F¬⇒¬G f notG = notG f

G¬⇒¬F : ∀ {ℓ ℓe ℓi ℓr ℓa}
          {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
          {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
        → ⟦ G_ (¬ φ) ⟧ tr → ⟦ ¬ (F_ φ) ⟧ tr
G¬⇒¬F gn (n , h , bef) = gn (n , (λ k → k h) , bef)

-- Classical directions (postulated; same axiomatic basis as ⟦G⟧⇒⟦G⟧⁺).
postulate
  ¬G⇒F¬ : ∀ {ℓ ℓe ℓi ℓr ℓa}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
          → ⟦ ¬ (G_ φ) ⟧ tr → ⟦ F_ (¬ φ) ⟧ tr
  ¬F⇒G¬ : ∀ {ℓ ℓe ℓi ℓr ℓa}
            {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
            {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
          → ⟦ ¬ (F_ φ) ⟧ tr → ⟦ G_ (¬ φ) ⟧ tr

------------------------------------------------------------
-- §7.8 Surface implications
------------------------------------------------------------

⟦G⟧⁺⇒F : ∀ {ℓ ℓe ℓi ℓr ℓa}
           {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {φ : LTLᵗ ℓa E I R} {tr : Trace E I R}
         → ⟦G⟧⁺ φ tr → ⟦ F_ φ ⟧ tr
⟦G⟧⁺⇒F g = zero , g zero , (λ _ ())

U⇒F : ∀ {ℓ ℓe ℓi ℓr ℓa}
        {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
      → ⟦ φ U ψ ⟧ tr → ⟦ F_ ψ ⟧ tr
U⇒F (n , q , _) = n , q , (λ _ _ → lift tt)

⟦G⟧⁺⇒W : ∀ {ℓ ℓe ℓi ℓr ℓa}
           {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
           {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
         → ⟦G⟧⁺ φ tr → ⟦ φ W ψ ⟧ tr
⟦G⟧⁺⇒W {φ = φ} {tr = tr} g = λ p → (proj₂ p) (⟦G⟧⁺⇒⟦G⟧ {φ = φ} {tr = tr} g)

U⇒W : ∀ {ℓ ℓe ℓi ℓr ℓa}
        {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
        {φ ψ : LTLᵗ ℓa E I R} {tr : Trace E I R}
      → ⟦ φ U ψ ⟧ tr → ⟦ φ W ψ ⟧ tr
U⇒W {φ = φ} {tr = tr} u = λ p → (proj₁ p) u

------------------------------------------------------------
-- §8 Sanity examples (trace witnesses only — v1 stops short of ⊨ proofs)
------------------------------------------------------------

private
  -- Simplest universe: no events, no internal branches, unit returns.
  EmptyE : Set → Set
  EmptyE _ = ⊥

  EmptyI : Set → Set
  EmptyI _ = ⊥

  open import CSP.Definitions.Basic_Processes using (Stop; Skip; Tau)
  open import Function using (case_of_)

  -- Stop is stuck: no LTS transition is enabled.
  Stop-IsStuck : IsStuck (Stop {E = EmptyE} {I = EmptyI} {R = ⊤})
  Stop-IsStuck (sRet eq) with eq
  ... | ()
  Stop-IsStuck (sSil eq) with eq
  ... | ()
  Stop-IsStuck (sVis {f = f} {at = at} {a = a} eq br-eq) with eq
  ... | refl = case br-eq of λ ()
    -- At this point, br-eq : f at a ≡ just t'
    -- Since f = λ _ _ → nothing, we have nothing ≡ just t', contradiction
  Stop-IsStuck (sNdbr eq _) with eq
  ... | ()

  -- Canonical trace from Stop.
  StopTrace : Trace EmptyE EmptyI ⊤
  StopTrace = stuck Stop-IsStuck

  -- TODO v2: Stop ⊨ atStuck — needs a "every trace rooted at Stop is `stuck _`"
  -- uniqueness lemma. Deferred.

  -- Loop: τ-self-looping divergent ITree.
  loop : ITree EmptyE EmptyI ⊤
  ITree.force loop = sil loop

  loop-Div : Divergent loop
  Divergent.next    loop-Div = loop
  Divergent.step    loop-Div = sSil refl
  Divergent.diverge loop-Div = loop-Div

  -- Canonical trace from loop.
  loopTrace : Trace EmptyE EmptyI ⊤
  loopTrace = div loop-Div

  -- TODO v2: loop ⊨ atDiv — needs uniqueness lemma. Deferred.

  -- Skip: explicit monomorphic version to match the Trace type.
  Skip' : ITree EmptyE EmptyI ⊤
  ITree.force Skip' = ret tt

  -- Skip's done-rooted trace.
  SkipTraceDone : Trace EmptyE EmptyI ⊤
  SkipTraceDone = done {t = Skip'} refl

  -- TODO v2: Skip-rooted traces include a step shape too (Skip ─[ ev (√ tt) ]─►
  -- deadlock). Showing `Skip ⊨ atDone _ ∨ X_ atStuck` requires both shapes plus
  -- a case-split — deferred.

------------------------------------------------------------
-- v2 TODO: DR-weak bisim invariance
--
-- The headline meta-theorem is:
--
--   ⊨-DRWB-invariant : ∀ {t₁ t₂} (φ : LTLᵗ ℓa E I R)
--                    → BisimStable φ
--                    → t₁ ≈ᴰᴿ t₂
--                    → t₁ ⊨ φ ↔ t₂ ⊨ φ
--
-- where BisimStable is an inductive Set-valued predicate whose
-- substantive case is `atom P` and demands DR-weak-bisim-stability
-- of the frame predicate P.
--
-- Proving it requires a frame-by-frame trace transport lemma
-- relating traces from t₁ and t₂ via the bisim. See
-- docs/superpowers/specs/2026-05-05-traces-based-ltl-design.md §2.11.
------------------------------------------------------------

{-# OPTIONS --guardedness #-}

module ITree_Relations.LTL.Traces_Based where

open import Level using (Level; _⊔_) renaming (zero to lzero; suc to lsuc)
open import Data.Nat using (ℕ; zero; suc; _<_)
open import Data.Product using (Σ; _,_; proj₁; proj₂; _×_; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Unit using (⊤; tt)
open import Data.Empty using (⊥)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Interaction_Trees
open import ITree_Relations.LTS

open ITree

---

-- State-aware infinite trace.
-- Each frame records:
--   state : the current ITree configuration
--   head  : the observable event labelling the step out of state
--   tail  : the continuation
--   step  : witness that the weak transition is valid

record Trace∞ {ℓ ℓe ℓi ℓr}
  (E : Set ℓ → Set ℓe)
  (I : Set ℓ → Set ℓi)
  (R : Set ℓr)
  : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    state : ITree E I R
    head  : Event√ E R
    tail  : Trace∞ E I R

open Trace∞

-- A trace is valid when every frame's state weakly steps via head into the
-- next frame's state.  Kept as a separate coinductive predicate because
-- referencing Trace∞.state inside the record definition itself would be
-- a forward reference.
record Valid {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (tr : Trace∞ E I R)
  : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    step : state tr ═[ ev (head tr) ]═► state (tail tr)
    cont : Valid (tail tr)

open Valid

---

-- Drop (iterate tail)

drop : ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ℕ → Trace∞ E I R → Trace∞ E I R
drop zero    tr = tr
drop (suc n) tr = drop n (Trace∞.tail tr)

---

-- Syntax of trace-based LTL with three atom flavours:
--   evAtom : predicate on the current event
--   stAtom : predicate on the current ITree state
--   esAtom : predicate on both (state × event)

data LTLᵗ {ℓ ℓe ℓi ℓr}
  (E : Set ℓ → Set ℓe)
  (I : Set ℓ → Set ℓi)
  (R : Set ℓr)
  : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where

  ⊤'   : LTLᵗ E I R
  ⊥'   : LTLᵗ E I R

  evAtom : (Event√ E R                      → Set) → LTLᵗ E I R
  stAtom : (ITree E I R                     → Set) → LTLᵗ E I R
  esAtom : (ITree E I R → Event√ E R        → Set) → LTLᵗ E I R

  ¬_  : LTLᵗ E I R → LTLᵗ E I R
  _∧_ : LTLᵗ E I R → LTLᵗ E I R → LTLᵗ E I R
  _∨_ : LTLᵗ E I R → LTLᵗ E I R → LTLᵗ E I R
  _⇒_ : LTLᵗ E I R → LTLᵗ E I R → LTLᵗ E I R

  X_  : LTLᵗ E I R → LTLᵗ E I R
  _U_ : LTLᵗ E I R → LTLᵗ E I R → LTLᵗ E I R

  F_  : LTLᵗ E I R → LTLᵗ E I R
  G_  : LTLᵗ E I R → LTLᵗ E I R

---

-- Semantics

⟦_⟧ :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe}
  {I : Set ℓ → Set ℓi}
  {R : Set ℓr}
  → LTLᵗ E I R → Trace∞ E I R → Set

⟦ ⊤' ⟧ tr = ⊤
⟦ ⊥' ⟧ tr = ⊥

⟦ evAtom P ⟧ tr = P (Trace∞.head tr)
⟦ stAtom P ⟧ tr = P (Trace∞.state tr)
⟦ esAtom P ⟧ tr = P (Trace∞.state tr) (Trace∞.head tr)

⟦ ¬ φ ⟧ tr = ⟦ φ ⟧ tr → ⊥

⟦ φ ∧ ψ ⟧ tr = ⟦ φ ⟧ tr × ⟦ ψ ⟧ tr
⟦ φ ∨ ψ ⟧ tr = ⟦ φ ⟧ tr ⊎ ⟦ ψ ⟧ tr
⟦ φ ⇒ ψ ⟧ tr = ⟦ φ ⟧ tr → ⟦ ψ ⟧ tr

⟦ X φ ⟧ tr = ⟦ φ ⟧ (Trace∞.tail tr)

⟦ φ U ψ ⟧ tr = Σ ℕ (λ n → ⟦ ψ ⟧ (drop n tr) ×
  (∀ m → m < n → ⟦ φ ⟧ (drop m tr)))

⟦ F φ ⟧ tr = Σ ℕ (λ n → ⟦ φ ⟧ (drop n tr))

⟦ G φ ⟧ tr = ∀ n → ⟦ φ ⟧ (drop n tr)

---

-- Satisfaction for ITrees: every trace starting at t satisfies φ

_⊨_ :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe}
  {I : Set ℓ → Set ℓi}
  {R : Set ℓr}
  → ITree E I R → LTLᵗ E I R → Set _
t ⊨ φ = ∀ tr → Valid tr → Trace∞.state tr ≡ t → ⟦ φ ⟧ tr

---

-- Optional fairness (placeholder)

Fair :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → Trace∞ E I R → Set
Fair tr = ⊤

_⊨fair_ :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ITree E I R → LTLᵗ E I R → Set _
t ⊨fair φ = ∀ tr → Valid tr → Trace∞.state tr ≡ t → Fair tr → ⟦ φ ⟧ tr

---

-- Derived operators: W (weak until), R (release)

_W_ :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → LTLᵗ E I R → LTLᵗ E I R → LTLᵗ E I R
φ W ψ = (φ U ψ) ∨ (G φ)

_R_ :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → LTLᵗ E I R → LTLᵗ E I R → LTLᵗ E I R
φ R ψ = ¬ ((¬ φ) U (¬ ψ))

---

-- Inductive/coinductive presentations of F, G, U

data ◇ᵗ
  {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (φ : LTLᵗ E I R)
  : Trace∞ E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  ◇ᵗ-now   : ∀ {tr} → ⟦ φ ⟧ tr                  → ◇ᵗ φ tr
  ◇ᵗ-later : ∀ {tr} → ◇ᵗ φ (Trace∞.tail tr)     → ◇ᵗ φ tr

record □ᵗ
  {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (φ : LTLᵗ E I R) (tr : Trace∞ E I R)
  : Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  coinductive
  field
    □ᵗ-now  : ⟦ φ ⟧ tr
    □ᵗ-tail : □ᵗ φ (Trace∞.tail tr)

open □ᵗ public

data _Uᵗ_
  {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  (φ ψ : LTLᵗ E I R)
  : Trace∞ E I R → Set (lsuc ℓ ⊔ ℓe ⊔ ℓi ⊔ ℓr) where
  Uᵗ-now  : ∀ {tr} → ⟦ ψ ⟧ tr                                → (φ Uᵗ ψ) tr
  Uᵗ-step : ∀ {tr} → ⟦ φ ⟧ tr → (φ Uᵗ ψ) (Trace∞.tail tr)    → (φ Uᵗ ψ) tr

---

-- Equivalences between the inductive/coinductive forms and ⟦_⟧ forms

F⇒◇ᵗ :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → ⟦ F φ ⟧ tr → ◇ᵗ φ tr
F⇒◇ᵗ φ (zero  , h) = ◇ᵗ-now   h
F⇒◇ᵗ φ (suc n , h) = ◇ᵗ-later (F⇒◇ᵗ φ (n , h))

◇ᵗ⇒F :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → ◇ᵗ φ tr → ⟦ F φ ⟧ tr
◇ᵗ⇒F φ (◇ᵗ-now   h) = zero , h
◇ᵗ⇒F φ (◇ᵗ-later e) with ◇ᵗ⇒F φ e
... | n , h = suc n , h

G⇒□ᵗ :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → ⟦ G φ ⟧ tr → □ᵗ φ tr
□ᵗ-now  (G⇒□ᵗ φ g) = g zero
□ᵗ-tail (G⇒□ᵗ φ g) = G⇒□ᵗ φ (λ n → g (suc n))

□ᵗ⇒G :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → □ᵗ φ tr → ⟦ G φ ⟧ tr
□ᵗ⇒G φ b zero    = □ᵗ-now b
□ᵗ⇒G φ b (suc n) = □ᵗ⇒G φ (□ᵗ-tail b) n

---

-- Basic laws

G⇒F :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → ⟦ G φ ⟧ tr → ⟦ F φ ⟧ tr
G⇒F φ g = zero , g zero

□ᵗ⇒◇ᵗ :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → □ᵗ φ tr → ◇ᵗ φ tr
□ᵗ⇒◇ᵗ φ b = ◇ᵗ-now (□ᵗ-now b)

◇◇⇒◇ :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → ◇ᵗ (F φ) tr → ◇ᵗ φ tr
◇◇⇒◇ φ (◇ᵗ-now   h) = F⇒◇ᵗ φ h
◇◇⇒◇ φ (◇ᵗ-later d) = ◇ᵗ-later (◇◇⇒◇ φ d)

{-# NON_TERMINATING #-}
□ᵗ⇒□ᵗG :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → □ᵗ φ tr → □ᵗ (G φ) tr
□ᵗ-now  (□ᵗ⇒□ᵗG φ b) = □ᵗ⇒G φ b
□ᵗ-tail (□ᵗ⇒□ᵗG φ b) = □ᵗ⇒□ᵗG φ (□ᵗ-tail b)

◇ᵗ-mono :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ ψ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → (∀ {tr'} → ⟦ φ ⟧ tr' → ⟦ ψ ⟧ tr')
  → ◇ᵗ φ tr → ◇ᵗ ψ tr
◇ᵗ-mono φ ψ imp (◇ᵗ-now   h) = ◇ᵗ-now   (imp h)
◇ᵗ-mono φ ψ imp (◇ᵗ-later e) = ◇ᵗ-later (◇ᵗ-mono φ ψ imp e)

□ᵗ-mono :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ ψ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → (∀ {tr'} → ⟦ φ ⟧ tr' → ⟦ ψ ⟧ tr')
  → □ᵗ φ tr → □ᵗ ψ tr
□ᵗ-now  (□ᵗ-mono φ ψ imp b) = imp (□ᵗ-now b)
□ᵗ-tail (□ᵗ-mono φ ψ imp b) = □ᵗ-mono φ ψ imp (□ᵗ-tail b)

□ᵗ-unfold-fwd :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → □ᵗ φ tr → ⟦ φ ⟧ tr × □ᵗ φ (Trace∞.tail tr)
□ᵗ-unfold-fwd φ b = □ᵗ-now b , □ᵗ-tail b

□ᵗ-unfold-bwd :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (φ : LTLᵗ E I R) → {tr : Trace∞ E I R}
  → ⟦ φ ⟧ tr × □ᵗ φ (Trace∞.tail tr) → □ᵗ φ tr
□ᵗ-now  (□ᵗ-unfold-bwd φ (h , _))  = h
□ᵗ-tail (□ᵗ-unfold-bwd φ (_ , t))  = t

---

-- Example event predicates

isTick :
  ∀ {ℓ ℓe ℓr} {E : Set ℓ → Set ℓe} {R : Set ℓr}
  → Event√ E R → Set
isTick (evl _) = ⊥
isTick (√ _)   = ⊤

isVisible :
  ∀ {ℓ ℓe ℓr} {E : Set ℓ → Set ℓe} {R : Set ℓr}
  → Event√ E R → Set
isVisible (evl _) = ⊤
isVisible (√ _)   = ⊥

---

-- Example state predicates (using state in ret nodes and node kinds)

-- "current state is at a ret node whose value satisfies P"
returnsWith :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (R → Set) → ITree E I R → Set
returnsWith P t with ITree.force t
... | ret r = P r
... | _     = ⊥

-- "current state is at some ret node"
atRetNode :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ITree E I R → Set
atRetNode t with ITree.force t
... | ret _ = ⊤
... | _     = ⊥

-- "current state is at a vis node"
atVisNode :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ITree E I R → Set
atVisNode t with ITree.force t
... | vis _ = ⊤
... | _     = ⊥

-- "current state is a stable node (no silent τ available)" — reuses isStable
atStable :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → ITree E I R → Set
atStable = isStable

---

-- Ready-made atomic formulas

𝕧 :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → LTLᵗ E I R
𝕧 = evAtom isVisible

𝕥 :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → LTLᵗ E I R
𝕥 = evAtom isTick

-- "currently at a ret node returning a value satisfying P"
atRet :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (R → Set) → LTLᵗ E I R
atRet P = stAtom (returnsWith P)

-- "currently at any ret node"
isRet :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → LTLᵗ E I R
isRet = stAtom atRetNode

-- "currently at any vis node"
isVis :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → LTLᵗ E I R
isVis = stAtom atVisNode

-- "currently at a stable node"
stable :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → LTLᵗ E I R
stable = stAtom atStable

---

-- Common patterns

eventuallyTerminates :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → LTLᵗ E I R
eventuallyTerminates = F 𝕥

-- "eventually reach a ret node with value satisfying P"
eventuallyReturns :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → (R → Set) → LTLᵗ E I R
eventuallyReturns P = F (atRet P)

neverTerminates :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → LTLᵗ E I R
neverTerminates = G (¬ 𝕥)

-- "every visible event is eventually followed by termination"
responsive :
  ∀ {ℓ ℓe ℓi ℓr}
  {E : Set ℓ → Set ℓe} {I : Set ℓ → Set ℓi} {R : Set ℓr}
  → LTLᵗ E I R
responsive = G (𝕧 ⇒ (F 𝕥))

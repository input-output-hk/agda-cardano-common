{-# OPTIONS --guardedness #-}

-- UCS chapter 7 §7.1: the ZERO/POS up-down counter (counter.csp, A.W. Roscoe).
--   channel up, down
--   ZERO = up -> POS;ZERO
--   POS  = up -> POS;POS  []  down -> SKIP
-- No FDR `assert` appears against this model in the book at this point (§7.1 uses
-- COUNTER purely to illustrate infinite-state processes and the `;` (sequential
-- composition) trick for encoding a stack-like unbounded counter) ⇒ MODEL-ONLY: we
-- only certify that `ZERO`/`POS` are well-defined (productive) process trees and
-- exhibit transition sanity checks, with NO FD/refinement theorem.
--
-- INFINITE-STATE, NO FDR ASSERTION ⇒ MODEL-ONLY (per the task brief).
--
-- On productivity — a genuine Agda guardedness limitation, confirmed by direct
-- experiment (not a matter of style): the literal
--   ZERO = up ⟶₀ (POS >> ZERO)
--   POS  = (up ⟶₀ (POS >> POS)) □ (down ⟶₀ Skip)
-- CANNOT be accepted by Agda's `--guardedness` productivity checker in this
-- codebase, in ANY of the forms tried (a plain function clause; a `force`
-- copattern delegating via `force (up ⟶₀ …)`; a `force` copattern with the
-- `react`/`mergeVis`/`□-mt` node spelled out by hand).  The obstruction is NOT
-- "recursion through `;`" per se — a self-recursive `react` node whose offer map
-- refers to ITSELF directly (`just (COPYout x)`, the `COPY`/`COPYout` style used
-- throughout this codebase, e.g. `Ch6/Buffers.agda`) is accepted — but is
-- SPECIFICALLY that the recursive occurrence of `ZERO`/`POS` is passed as an
-- ARGUMENT to a further (already fully-elaborated, non-clique) function call —
-- `_>>_`, `_□_`, or any hand-rolled stand-in (`f x` for a plain helper `f`) —
-- before it reaches a `just`; Agda's guardedness checker only recognises a
-- corecursive occurrence as guarded when it is a DIRECT argument of a
-- constructor (`react`/`just`/…) in the SAME equation, and does not "see through"
-- an intervening ordinary function call, no matter how transparently that call
-- behaves.  (`Semantics`'s own `iter`/`iter-bind`/`iterV`/`iterT` — see
-- `CSP/Operators.agda` — hand-roll a dedicated bind-shaped clique for exactly this
-- reason, rather than self-applying the generic `_>>=_`.)
--
-- The fix used below: `ZERO`/`POS`'s UNBOUNDED nesting ("`POS` composed with
-- itself `n` times, then a fixed tail") is realised directly as two ℕ-indexed,
-- SELF-CONTAINED families — `Zn n` = `POS^n ; ZERO` and `Pn n` = `POS^n ; SKIP` —
-- each defined by its OWN direct recursion (no external `_>>_`/`_□_` call, no
-- self-reference threaded through another function), which Agda accepts as
-- productive exactly like `COPY`/`BUFN`.  `ZERO := Zn 0` and `POS := Pn 1` are then
-- plain (non-recursive) aliases.  `Zn`/`Pn`'s transition structure reproduces the
-- book's `;`-recursion up to the `SKIP;·` termination-handoff τ: a literal
-- `POS;ZERO`/`POS;POS` term steps `down` via `SKIP;rest ─τ─► rest`, whereas
-- `Zn (suc n)`/`Pn (suc n)` step `down` DIRECTLY to `Zn n`/`Pn n`, collapsing that
-- handoff τ — i.e. `Zn`/`Pn` is the τ-COLLAPSED (weak/observational) image of the
-- literal counter, equal to it up to weak bisimulation (traces/failures/
-- divergences), which is all that matters for this model-only illustration
-- (verified by the `zero-up`/`pos-up`/`pos-down` sanity steps below): `Zn 0` offers only `up`,
-- stepping to `Zn 1` (`POS;ZERO`); `Pn (suc n)` offers `up` (stepping to
-- `Pn (suc (suc n))`, i.e. one more `POS` layer) and `down` (stepping to `Pn n`,
-- i.e. peeling one `POS` layer off — `Pn 0` reduces to `ret tt`, i.e. `SKIP`).

module CSP.Examples.UCS.Ch7.Counter where

open import Level using (0ℓ) renaming (zero to lzero)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Product using (_,_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Class.DecEq using (DecEq)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §1. Event type + decidable equality (two nullary channels `up`, `down`).
data CEv : Set → Set where
  up down : CEv ⊤

CEv-≟ : (x y : AnyTypes CEv) → Dec (x ≡ y)
CEv-≟ (_ , up)   (_ , up)   = yes refl
CEv-≟ (_ , down) (_ , down) = yes refl
CEv-≟ (_ , up)   (_ , down) = no (λ ())
CEv-≟ (_ , down) (_ , up)   = no (λ ())

open import CSP.Operators CEv-≟

instance
  DecEq-⊤ : ∀ {ℓr} → DecEq (⊤ {ℓr})
  DecEq-⊤ = record { _≟_ = λ _ _ → yes refl }   -- cf. Ch7/Termination.agda, Laws/FD/SlideZero.agda:96

open import Semantics.LTS {E = CEv} {I = ExtI CEv}

CProc : Set₁
CProc = PTree CEv (ExtI CEv) (⊤ {lzero})

-------------------------------------------------------------------------------------
-- §2. The processes ZERO / POS, via the self-contained ℕ-indexed unrollings `Zn`/
-- `Pn` (see the header note for why this shape — not the literal `>>`/`□` pseudocode
-- — is what Agda's guardedness checker accepts).  No `mutual` block: `Zn`/`Pn` are
-- each a single, directly self-recursive `PTree`-valued function (own clique), and
-- `ZERO`/`POS` are plain non-recursive aliases into them.
-------------------------------------------------------------------------------------

-- Zn n = POS^n ; ZERO  (n pending `POS` layers before the counter re-reads as ZERO).
Zn : ℕ → CProc
force (Zn zero)    = react                              -- ZERO itself: offers only `up`
  (λ where (_ , up)   _ → just (Zn 1)
           (_ , down) _ → nothing)
  ∅t
force (Zn (suc n)) = react                               -- a live `POS` layer atop `Zn n`
  (λ where (_ , up)   _ → just (Zn (suc (suc n)))        -- POS;POS;(POS^n;ZERO) = POS^(n+2);ZERO
           (_ , down) _ → just (Zn n))                   -- SKIP;(POS^n;ZERO)    = POS^n;ZERO
  ∅t

ZERO : CProc
ZERO = Zn 0                                              -- ZERO = up -> POS;ZERO

-- Pn n = POS^n ; SKIP  (n pending `POS` layers before termination).
Pn : ℕ → CProc
force (Pn zero)    = force Skip                          -- POS^0;SKIP = SKIP
force (Pn (suc n)) = react
  (λ where (_ , up)   _ → just (Pn (suc (suc n)))         -- POS;POS;(POS^n;SKIP) = POS^(n+2);SKIP
           (_ , down) _ → just (Pn n))                    -- SKIP;(POS^n;SKIP)    = POS^n;SKIP
  ∅t

POS : CProc
POS = Pn 1                                               -- POS = up -> POS;POS [] down -> SKIP

-------------------------------------------------------------------------------------
-- §3. Transition sanity checks (model-only — no FD/refinement claim).
-------------------------------------------------------------------------------------

-- ZERO offers `up`, stepping to POS;ZERO (= Zn 1, one pending POS layer).
zero-up : ZERO ─[ ev (evl (evLabel ⊤ up tt)) ]─► Zn 1
zero-up = sVis refl refl

-- POS offers `up`, stepping to POS;POS (= Pn 2, two pending POS layers).
pos-up : POS ─[ ev (evl (evLabel ⊤ up tt)) ]─► Pn 2
pos-up = sVis refl refl

-- POS offers `down`, stepping to SKIP (= Pn 0, which reduces definitionally to
-- `ret tt`, i.e. exactly `Skip`'s own force value — `Pn 0` names the same
-- transition target as `Skip` would).
pos-down : POS ─[ ev (evl (evLabel ⊤ down tt)) ]─► Pn 0
pos-down = sVis refl refl

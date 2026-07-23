{-# OPTIONS --guardedness #-}

-- UCS chapter 4: SUDOKU as a CSP constraint network (sudoku.csp, Bill Roscoe),
-- reduced to 4×4 shidoku (rows, columns, 2×2 boxes; values Fin 4).
--
-- sudoku.csp models the board as cell processes emitting a value-commitment
-- `select.r.c.v`, with row/column/box ALL-DIFFERENT constraint processes
-- synchronising on those events; a SOLUTION is a trace to a full consistent
-- assignment, an UNSOLVABLE (over-constrained) puzzle DEADLOCKS.
--
-- MODELLING NOTE (fused product).  A literal parallel network (4 row + 4 column
-- + 4 box all-different processes, each `sel` a 3-way sync) is faithful but makes
-- a 16-step full-solve witness a volume wall.  Since the deliverables are
-- trace-level existentials, this module models the board as a SINGLE process
-- `Board g` whose `sel.r.c.v` offer is guarded by the CONJUNCTION of the row,
-- column and box all-different constraints — the PRODUCT of the region-constraint
-- processes, trace-equivalent to their literal `∥`.  The literal 12-fold parallel
-- network is a documented NON-GOAL (deferred).
--
-- Deliverables (both EXISTENTIAL, postulate-free):
--   sudoku-solvable  : the empty board reaches a full valid grid (16-`sel` trace)
--   sudoku-deadlocks : HasDeadlock of an over-constrained board (a blocked cell)

module CSP.Examples.UCS.Ch4.Sudoku where

open import Level using (lift) renaming (zero to lzero)
open import Data.Bool using (Bool; true; false; _∧_; _∨_; not)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Fin.Properties using () renaming (_≟_ to _F≟_)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using (tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no)
open import Relation.Nullary.Decidable using (⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

-- single event: sel.(row,col,value)
data SEv : Set → Set where
  sel : SEv (Fin 4 × Fin 4 × Fin 4)

SEv-≟ : (x y : AnyTypes SEv) → Dec (x ≡ y)
SEv-≟ (_ , sel) (_ , sel) = yes refl

open import CSP.Operators SEv-≟
open EventSet

open import Data.Product using (Σ; Σ-syntax)
open import Semantics.LTS      {E = SEv} {I = ExtI SEv}
open import Semantics.Failures {E = SEv} {I = ExtI SEv}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-ev; traces)

SProc : Set₁
SProc = PTree SEv (ExtI SEv) (⊤poly {lzero})

Cell : Set
Cell = Fin 4 × Fin 4 × Fin 4        -- (row , col , value)

Grid : Set
Grid = List Cell                    -- the placed cells (partial assignment)

_==F_ : Fin 4 → Fin 4 → Bool
x ==F y = ⌊ x F≟ y ⌋

-- 2×2 box band: rows/cols 0,1 → low half; 2,3 → high half.
band : Fin 4 → Bool
band fz                = false
band (fs fz)           = false
band (fs (fs fz))      = true
band (fs (fs (fs _)))  = true

-- same 2×2 box: same row-band and same col-band.
sameBox : Fin 4 → Fin 4 → Fin 4 → Fin 4 → Bool
sameBox r c r′ c′ = (bandEq (band r) (band r′)) ∧ (bandEq (band c) (band c′))
  where
    bandEq : Bool → Bool → Bool
    bandEq true  true  = true
    bandEq false false = true
    bandEq _     _     = false

anyL : {A : Set} → (A → Bool) → List A → Bool
anyL p []       = false
anyL p (x ∷ xs) = p x ∨ anyL p xs

-- is cell (r,c) already placed?
cellFilled : Grid → Fin 4 → Fin 4 → Bool
cellFilled g r c = anyL (λ where (r′ , c′ , _) → (r′ ==F r) ∧ (c′ ==F c)) g

-- is value v already used in row r / col c / the box of (r,c)?
rowHas : Grid → Fin 4 → Fin 4 → Bool
rowHas g r v = anyL (λ where (r′ , _ , v′) → (r′ ==F r) ∧ (v′ ==F v)) g

colHas : Grid → Fin 4 → Fin 4 → Bool
colHas g c v = anyL (λ where (_ , c′ , v′) → (c′ ==F c) ∧ (v′ ==F v)) g

boxHas : Grid → Fin 4 → Fin 4 → Fin 4 → Bool
boxHas g r c v = anyL (λ where (r′ , c′ , v′) → sameBox r c r′ c′ ∧ (v′ ==F v)) g

-- the fused all-different guard: cell empty AND value unused in row, col, box.
legal : Grid → Fin 4 → Fin 4 → Fin 4 → Bool
legal g r c v =
  not (cellFilled g r c) ∧ not (rowHas g r v) ∧ not (colHas g c v) ∧ not (boxHas g r c v)

-- Board g: offers sel.(r,c,v) → Board ((r,c,v) ∷ g)  iff  legal g r c v.  PINNED.
Board : Grid → SProc
force (Board g) = react
  (λ where
     (_ , sel) (r , c , v) → case legal g r c v of λ where
         true  → just (Board ((r , c , v) ∷ g))
         false → nothing)
  ∅t

emptyBoard : Grid
emptyBoard = []

Puzzle : SProc
Puzzle = Board emptyBoard

-- completeness: every one of the 16 cells is filled.
Full : Grid → Set
Full g = ∀ (r c : Fin 4) → cellFilled g r c ≡ true

------------------------------------------------------------------------------------
-- §B. SOLVING THE EMPTY BOARD: the trace witness `sudoku-solvable`.
--
-- The chosen valid shidoku solution (rows top→bottom):
--   row0: 0 1 2 3
--   row1: 2 3 0 1
--   row2: 1 0 3 2
--   row3: 3 2 1 0
-- Rows, columns, and all four 2×2 boxes are permutations of {0,1,2,3}.  Because
-- every prefix of a valid solution is region-consistent, each `sel.(r,c,v)` is
-- `legal` at its step (the guard reduces to `true`), so the whole solve is ONE
-- finite forward ⟹ derivation of 16 visible `sel` steps (no τ).
------------------------------------------------------------------------------------

-- Fin 4 literals (fz/fs, as used throughout the model).
0F 1F 2F 3F : Fin 4
0F = fz
1F = fs fz
2F = fs (fs fz)
3F = fs (fs (fs fz))

-- one `sel.(r,c,v)` visible event.
selev : Fin 4 → Fin 4 → Fin 4 → Event√ (⊤poly {lzero})
selev r c v = evl (evLabel (Fin 4 × Fin 4 × Fin 4) sel (r , c , v))

-- the 16-event solve trace, in reading order (row0 left→right, then row1, …).
solveTrace : List (Event√ (⊤poly {lzero}))
solveTrace =
    selev 0F 0F 0F ∷ selev 0F 1F 1F ∷ selev 0F 2F 2F ∷ selev 0F 3F 3F
  ∷ selev 1F 0F 2F ∷ selev 1F 1F 3F ∷ selev 1F 2F 0F ∷ selev 1F 3F 1F
  ∷ selev 2F 0F 1F ∷ selev 2F 1F 0F ∷ selev 2F 2F 3F ∷ selev 2F 3F 2F
  ∷ selev 3F 0F 3F ∷ selev 3F 1F 2F ∷ selev 3F 2F 1F ∷ selev 3F 3F 0F ∷ []

-- the full grid the solve trace reaches: the 16 placed cells in the accumulation
-- order (each step conses at the front, so this is the trace in reverse).
solvedGrid : Grid
solvedGrid =
    (3F , 3F , 0F) ∷ (3F , 2F , 1F) ∷ (3F , 1F , 2F) ∷ (3F , 0F , 3F)
  ∷ (2F , 3F , 2F) ∷ (2F , 2F , 3F) ∷ (2F , 1F , 0F) ∷ (2F , 0F , 1F)
  ∷ (1F , 3F , 1F) ∷ (1F , 2F , 0F) ∷ (1F , 1F , 3F) ∷ (1F , 0F , 2F)
  ∷ (0F , 3F , 3F) ∷ (0F , 2F , 2F) ∷ (0F , 1F , 1F) ∷ (0F , 0F , 0F) ∷ []

-- the empty board reaches a full valid grid via the 16-`sel` solve trace.
sudoku-solvable : Σ[ end ∈ Grid ] (Puzzle ⟹⟨ solveTrace ⟩ Board end × Full end)
sudoku-solvable = solvedGrid , derivation , full
  where
    derivation : Puzzle ⟹⟨ solveTrace ⟩ Board solvedGrid
    derivation =
      ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
      (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
      (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
      (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
      (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
      (⟹-ev (sVis refl refl) ⟹-refl)))))))))))))))
    full : Full solvedGrid
    full fz               fz               = refl
    full fz               (fs fz)          = refl
    full fz               (fs (fs fz))     = refl
    full fz               (fs (fs (fs fz))) = refl
    full (fs fz)          fz               = refl
    full (fs fz)          (fs fz)          = refl
    full (fs fz)          (fs (fs fz))     = refl
    full (fs fz)          (fs (fs (fs fz))) = refl
    full (fs (fs fz))     fz               = refl
    full (fs (fs fz))     (fs fz)          = refl
    full (fs (fs fz))     (fs (fs fz))     = refl
    full (fs (fs fz))     (fs (fs (fs fz))) = refl
    full (fs (fs (fs fz))) fz              = refl
    full (fs (fs (fs fz))) (fs fz)         = refl
    full (fs (fs (fs fz))) (fs (fs fz))    = refl
    full (fs (fs (fs fz))) (fs (fs (fs fz))) = refl

------------------------------------------------------------------------------------
-- §C. DEADLOCK: an over-constrained board is stuck (`sudoku-deadlocks`).
--
-- `badGrid` fills 15 cells and leaves ONE cell empty — (3,3) — but blocked for
-- ALL four values, so no `sel.(3,3,v)` is `legal` and the board can take no step:
--   * row 3 holds {1,2,3} at (3,0),(3,1),(3,2)  → forbids v ∈ {1,2,3} at (3,3);
--   * column 3 holds 0 at (0,3)                 → forbids v = 0        at (3,3).
-- Thus all four values are illegal at (3,3).  Every OTHER cell is already filled,
-- so `sel.(r,c,v)` at a filled cell is illegal too (cellFilled ⇒ guard false).
-- Hence `Board badGrid` refuses every visible offer, has no τ-branch (τc = ∅t),
-- and is not a ret/sil node — it is stuck: a genuine (over-constrained) deadlock.
------------------------------------------------------------------------------------

open import Data.Empty using (⊥)
open import Semantics.Deadlock {E = SEv} {I = ExtI SEv}
  using (IsStuck; HasDeadlock; _⟹∖√⟨_⟩_; ∖√-refl)

badGrid : Grid
badGrid =
    (0F , 0F , 0F) ∷ (0F , 1F , 0F) ∷ (0F , 2F , 0F) ∷ (0F , 3F , 0F)   -- (0,3)=0 : column-3 blocker
  ∷ (1F , 0F , 0F) ∷ (1F , 1F , 0F) ∷ (1F , 2F , 0F) ∷ (1F , 3F , 1F)
  ∷ (2F , 0F , 0F) ∷ (2F , 1F , 0F) ∷ (2F , 2F , 0F) ∷ (2F , 3F , 2F)
  ∷ (3F , 0F , 1F) ∷ (3F , 1F , 2F) ∷ (3F , 2F , 3F) ∷ []               -- row 3 = {1,2,3}; (3,3) empty & blocked

BadPuzzle : SProc
BadPuzzle = Board badGrid

-- No `sel.(r,c,v)` is legal on `badGrid`: the 15 filled cells fail `cellFilled`
-- (value free), and at the empty (3,3) every value is blocked by row/column.
stuck-sel : ∀ (r c v : Fin 4) → legal badGrid r c v ≡ false
-- row 0 (all filled)
stuck-sel fz               fz               v = refl
stuck-sel fz               (fs fz)          v = refl
stuck-sel fz               (fs (fs fz))     v = refl
stuck-sel fz               (fs (fs (fs fz))) v = refl
-- row 1 (all filled)
stuck-sel (fs fz)          fz               v = refl
stuck-sel (fs fz)          (fs fz)          v = refl
stuck-sel (fs fz)          (fs (fs fz))     v = refl
stuck-sel (fs fz)          (fs (fs (fs fz))) v = refl
-- row 2 (all filled)
stuck-sel (fs (fs fz))     fz               v = refl
stuck-sel (fs (fs fz))     (fs fz)          v = refl
stuck-sel (fs (fs fz))     (fs (fs fz))     v = refl
stuck-sel (fs (fs fz))     (fs (fs (fs fz))) v = refl
-- row 3: (3,0),(3,1),(3,2) filled; (3,3) empty but blocked for every value.
stuck-sel (fs (fs (fs fz))) fz              v = refl
stuck-sel (fs (fs (fs fz))) (fs fz)         v = refl
stuck-sel (fs (fs (fs fz))) (fs (fs fz))    v = refl
stuck-sel (fs (fs (fs fz))) (fs (fs (fs fz))) fz               = refl  -- v=0 : column 3 has 0
stuck-sel (fs (fs (fs fz))) (fs (fs (fs fz))) (fs fz)          = refl  -- v=1 : row 3 has 1
stuck-sel (fs (fs (fs fz))) (fs (fs (fs fz))) (fs (fs fz))     = refl  -- v=2 : row 3 has 2
stuck-sel (fs (fs (fs fz))) (fs (fs (fs fz))) (fs (fs (fs fz))) = refl  -- v=3 : row 3 has 3

-- `Board badGrid` can take no LTS step: it is a stable `react` node whose visible
-- offers are all `nothing` (stuck-sel) and whose τ-branch is empty (∅t).
is-stuck : IsStuck BadPuzzle
is-stuck (sRet eq)                               = case eq of λ ()
is-stuck (sSil eq)                               = case eq of λ ()
is-stuck (sTau refl br)                          = case br of λ ()
is-stuck (sVis {at = _ , sel} {a = r , c , v} refl br)
  rewrite stuck-sel r c v                        = case br of λ ()

-- The over-constrained board deadlocks: reachable (via the empty √-free trace) and stuck.
sudoku-deadlocks : HasDeadlock BadPuzzle
sudoku-deadlocks = [] , BadPuzzle , ∖√-refl , is-stuck

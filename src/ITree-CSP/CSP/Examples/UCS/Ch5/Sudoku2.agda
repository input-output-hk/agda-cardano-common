{-# OPTIONS --guardedness #-}

-- UCS chapter 5: SUDOKU by renaming (sudoku2.csp, Bill Roscoe, Sept 2009; source
-- fdr-examples/ucs/chapter05/sudoku2.csp), reduced to the 4×4 shidoku board that
-- `CSP.Examples.UCS.Ch4.Sudoku` uses (rows, columns, 2×2 boxes; symbols `Fin 4`).
--
-- WHAT IS NEW HERE (the chapter-5 lesson, sudoku2.csp:202).  The script announces
-- "In this file we define generic square processes using events that can later be
-- renamed".  ONE generic square process — over the private events `selhere` (this
-- square is being filled) and `seladj` (a neighbour is being filled) — is renamed
-- per co-ordinate onto the global `select.p.v` channel:
--
--   Cell(p) = (if init(p)==0 then GVar else GFixed(init(p)))
--             [[selhere.v <- select.p.v | v <- Symbol]]
--             [[seladj.v  <- select.q.v | q <- adj(p), v <- Symbol]]
--
-- That is `Cell` below: `renameInv (genCell (pz p)) (cellInv p)` — a SINGLE pair of
-- generic processes `genCell blank` / `genCell (fixed v)`, plus a per-square inverse
-- `cellInv p`.  The renaming is non-injective (fan-OUT: the one source event
-- `seladj.v` becomes `select.q.v` for every neighbour q) but functional per TARGET
-- (each `select.q.v` has at most one source), so `CSP.Rename.renameInv` applies and
-- NO fan-in τ is introduced.  The source's own point of comparison — the direct
-- per-square family `Var(p)`/`Fixed(p,v)` of sudoku2.csp:213-218 — is ported too, as
-- `dirCell`, so that BOTH of the script's assertions can be stated (they are the same
-- assertion about `System` and about `System'`).
--
-- REUSED FROM Ch4/Sudoku.agda: the 4×4 reduction itself, the `_==F_` value test and
-- the `sameBox` 2×2-box predicate (imported, not copied), and the solved grid
-- (rows 0123 / 2301 / 1032 / 3210) that `goodP` blanks one square of.  Everything
-- else here is new: Ch4 models the board as ONE fused `Board g` process whose guard
-- is the conjunction of the region constraints, whereas this module builds the real
-- 16-component alphabetised-parallel network of the script.
--
-- SCOPED OMISSION (deliberate, not a gap).  sudoku2.csp:261-300 — `count`,
-- `greatest`, `inc`, `orderl`, `rank`, `statorder` — computes a smarter square
-- ordering from a blocked-count / adjacency weighting.  It exists purely to shrink
-- FDR's state-space search and has NO CSP-semantic content: nothing in the algebra
-- depends on the order squares are filled, and the script itself offers `order` as a
-- free choice.  It is NOT ported.  `Reg`, by contrast, IS part of the model whose
-- traces the assertions are about, so it is ported, instantiated at the script's
-- DEFAULT `order = scanorder` (the blank squares in scan order, `order` below).
--
-- THE ASSERTIONS (sudoku2.csp:258-259)
--   assert STOP [T= RegSys \{|select|}          assert STOP [T= RegSys'\{|select|}
-- `STOP [T= P` says P performs no visible event.  Hiding `select` leaves only `done`,
-- and `done` is in every square's alphabet while only `GFixed`/`Fixed` offers it, so
-- `done` happens exactly when every square has been filled.  The assertion therefore
-- FAILS exactly when the puzzle is solvable — the solver-by-counterexample idiom.
--
-- Both truth values are re-derived here and proved, on two deliberately chosen boards.
-- §B covers both of the script's assertions, §C the renamed one, §D checks non-vacuity:
--   goodP  15 givens, one blank at (3,3) with the unique completion 0
--          ⇒ ⟨done⟩ IS a trace  ⇒  BOTH assertions are FALSE   (`stop⋢hidden`, `stop⋢hidden′`)
--   badP   15 givens whose blank at (3,3) is blocked for all four symbols
--          ⇒ the network cannot move at all ⇒ the assertion is TRUE (`stop⊑hidden-bad`,
--            and `bad-deadlocks` reads the same fact as Ch4's `sudoku-deadlocks` does)
-- An all-blank board would also make the assertion FALSE, but its witness is the
-- 16-select solve that Ch4 already delivers against the trace-equivalent fused board;
-- re-running it through the 16-fold renamed network adds volume, not content, so the
-- solvable witness here is taken on a board whose remaining choice is the last square.
--
-- No postulate, no hole, no pragma beyond --guardedness.  Corecursion never crosses a
-- CSP operator: the only corecursive definitions are the two square processes, whose
-- calls sit under `just` inside their own named offer maps.

module CSP.Examples.UCS.Ch5.Sudoku2 where

open import Level using (Lift; lift) renaming (zero to lzero)
open import Data.Bool using (Bool; true; false; _∧_; _∨_)
open import Data.Bool.Properties using () renaming (_≟_ to _B≟_)
open import Data.Fin using (Fin) renaming (zero to fz; suc to fs)
open import Data.Unit using (⊤; tt)
open import Data.Unit.Polymorphic renaming (⊤ to ⊤poly) using ()
open import Data.Maybe using (Maybe; just; nothing)
open import Data.List using (List; []; _∷_)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥; ⊥-elim)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

-- the 4×4 reduction's value test and 2×2-box predicate, reused from chapter 4
open import CSP.Examples.UCS.Ch4.Sudoku using (_==F_; sameBox)

------------------------------------------------------------------------------------
-- §A. THE MODEL.
------------------------------------------------------------------------------------

-- The four channels of sudoku2.csp: the global `select.p.v` and `done`, plus the two
-- PRIVATE events of the generic square process that renaming turns into `select`.
data SEv2 : Set → Set where
  select         : SEv2 (Fin 4 × Fin 4 × Fin 4)   -- select.(i,j).v
  selhere seladj : SEv2 (Fin 4)                   -- generic: this square / a neighbour
  done           : SEv2 ⊤                         -- every square is filled

-- decidable equality on the event labels (needed by CSP.Operators)
SEv2-≟ : (x y : AnyTypes SEv2) → Dec (x ≡ y)
SEv2-≟ (_ , select)  (_ , select)  = yes refl
SEv2-≟ (_ , selhere) (_ , selhere) = yes refl
SEv2-≟ (_ , seladj)  (_ , seladj)  = yes refl
SEv2-≟ (_ , done)    (_ , done)    = yes refl
SEv2-≟ (_ , select)  (_ , selhere) = no (λ ())
SEv2-≟ (_ , select)  (_ , seladj)  = no (λ ())
SEv2-≟ (_ , select)  (_ , done)    = no (λ ())
SEv2-≟ (_ , selhere) (_ , select)  = no (λ ())
SEv2-≟ (_ , selhere) (_ , seladj)  = no (λ ())
SEv2-≟ (_ , selhere) (_ , done)    = no (λ ())
SEv2-≟ (_ , seladj)  (_ , select)  = no (λ ())
SEv2-≟ (_ , seladj)  (_ , selhere) = no (λ ())
SEv2-≟ (_ , seladj)  (_ , done)    = no (λ ())
SEv2-≟ (_ , done)    (_ , select)  = no (λ ())
SEv2-≟ (_ , done)    (_ , selhere) = no (λ ())
SEv2-≟ (_ , done)    (_ , seladj)  = no (λ ())

open import CSP.Operators SEv2-≟
open EventSet

-- same-alphabet renaming (identity ι), exactly as Ch5/Renaming.agda
open import CSP.Rename {E₁ = SEv2} {E₂ = SEv2} (λ e → e) (λ e → just e) (λ _ → refl)

open import Semantics.LTS      {E = SEv2} {I = ExtI SEv2}
open import Semantics.Failures {E = SEv2} {I = ExtI SEv2}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-τ; ⟹-ev; traces; _⊑T_)

-- co-ordinates, symbols and squares (Coord = {0..3}, Symbol = {1..4} renumbered)
Coord Symbol : Set
Coord  = Fin 4
Symbol = Fin 4

Sq : Set
Sq = Coord × Coord

-- a single-square process (both the generic and the direct form return ⊤)
SProc : Set₁
SProc = PTree SEv2 (ExtI SEv2) (⊤poly {lzero})

-- Fin 4 literals
0F 1F 2F 3F : Fin 4
0F = fz
1F = fs fz
2F = fs (fs fz)
3F = fs (fs (fs fz))

-- pick one of four values by co-ordinate (lets a board be written as an ASCII grid)
row4 : ∀ {A : Set} → A → A → A → A → Coord → A
row4 a b c d fz                = a
row4 a b c d (fs fz)           = b
row4 a b c d (fs (fs fz))      = c
row4 a b c d (fs (fs (fs _)))  = d

-- (r,c) ∈ nhd((i,j)): same row, same column, or same 2×2 box  (sudoku2.csp:184)
nhdB : Coord → Coord → Coord → Coord → Bool
nhdB i j r c = (i ==F r) ∨ ((j ==F c) ∨ sameBox i j r c)

-- the initial content of a square: blank, or a given symbol  (the script's `init`)
data CellState : Set where
  blank : CellState
  fixed : Symbol → CellState

-- a puzzle assigns an initial state to every square
Board : Set
Board = Coord → Coord → CellState

------------------------------------------------------------------------------------
-- §A.1  The GENERIC square process (sudoku2.csp:205-209) — the chapter-5 idiom.
--   GVar     = seladj?_ -> GVar  []  selhere?v -> GFixed(v)
--   GFixed v = done -> GFixed(v) []  seladj?_:diff(Symbol,{v}) -> GFixed(v)
-- ONE process, no co-ordinate anywhere in it: `select` is refused outright, and the
-- neighbour/self distinction is carried by the two private channels.
------------------------------------------------------------------------------------

genCell : CellState → SProc
-- the visible offers of the generic square (named, so its force always reduces)
genV : CellState → (at : AnyTypes SEv2) → ContinueType at (Maybe SProc)

genV blank     (_ , seladj)  _ = just (genCell blank)
genV blank     (_ , selhere) v = just (genCell (fixed v))
genV blank     (_ , done)    _ = nothing
genV blank     (_ , select)  _ = nothing
genV (fixed w) (_ , done)    _ = just (genCell (fixed w))
genV (fixed w) (_ , seladj)  v = case v ==F w of λ where
    true  → nothing                        -- a neighbour may not take this square's value
    false → just (genCell (fixed w))
genV (fixed w) (_ , selhere) _ = nothing   -- already fixed: cannot be selected again
genV (fixed w) (_ , select)  _ = nothing

force (genCell s) = react (genV s) ∅t

------------------------------------------------------------------------------------
-- §A.2  The per-square RENAMING (sudoku2.csp:224-225) and `Cell`.
------------------------------------------------------------------------------------

-- target → source: `select.p.v` comes from `selhere.v` at p itself and from
-- `seladj.v` at each neighbour q ∈ adj(p); `done` is not renamed; the private
-- events have no source (renaming makes them unavailable in the target alphabet).
cellInv : Sq → (bt : AnyTypes SEv2) → proj₁ bt → Maybe ConcEvent₁
cellInv (i , j) (_ , select) (r , c , v) = case (i ==F r) ∧ (j ==F c) of λ where
    true  → just ((Symbol , selhere) , v)
    false → case nhdB i j r c of λ where
        true  → just ((Symbol , seladj) , v)
        false → nothing
cellInv _ (_ , done)    a = just ((⊤ , done) , a)
cellInv _ (_ , selhere) _ = nothing
cellInv _ (_ , seladj)  _ = nothing

-- Cell(p): the ONE generic square process, renamed onto p's co-ordinate.
Cell : Board → Sq → SProc
Cell pz (i , j) = renameInv (genCell (pz i j)) (cellInv (i , j))

------------------------------------------------------------------------------------
-- §A.3  The DIRECT per-square family (sudoku2.csp:213-218) — the form the chapter-5
-- idiom replaces.  Here the co-ordinate is baked into every process, so there is one
-- process per square rather than one process renamed 16 ways.
--   Var(p)     = select?_:adj(p)?_ -> Var(p) [] select.p?v -> Fixed(p,v)
--   Fixed(p,v) = done -> Fixed(p,v) [] select?_:adj(p)?_:diff(Symbol,{v}) -> Fixed(p,v)
------------------------------------------------------------------------------------

dirCell : Sq → CellState → SProc
-- the visible offers of the direct square process
dirV : Sq → CellState → (at : AnyTypes SEv2) → ContinueType at (Maybe SProc)

dirV (i , j) blank (_ , select) (r , c , v) = case (i ==F r) ∧ (j ==F c) of λ where
    true  → just (dirCell (i , j) (fixed v))
    false → case nhdB i j r c of λ where
        true  → just (dirCell (i , j) blank)
        false → nothing
dirV (i , j) (fixed w) (_ , select) (r , c , v) = case (i ==F r) ∧ (j ==F c) of λ where
    true  → nothing
    false → case nhdB i j r c of λ where
        true  → case v ==F w of λ where
            true  → nothing
            false → just (dirCell (i , j) (fixed w))
        false → nothing
dirV p (fixed w) (_ , done)    _ = just (dirCell p (fixed w))
dirV p blank     (_ , done)    _ = nothing
dirV p _         (_ , selhere) _ = nothing
dirV p _         (_ , seladj)  _ = nothing

force (dirCell p s) = react (dirV p s) ∅t

-- Cell'(p): the direct form at p  (sudoku2.csp:229)
Cell′ : Board → Sq → SProc
Cell′ pz (i , j) = dirCell (i , j) (pz i j)

------------------------------------------------------------------------------------
-- §A.4  Alphabets and the network.
------------------------------------------------------------------------------------

-- an EventSet presented by a Bool test (membership proofs are then `refl`)
boolES : ((at : AnyTypes SEv2) → proj₁ at → Bool) → EventSet
boolES f .mem at a = f at a ≡ true
boolES f .dec at a = f at a B≟ true

-- Alpha(p) = {| select.q , done | q <- nhd(p) |}   (sudoku2.csp:231)
alphaB : Sq → (at : AnyTypes SEv2) → proj₁ at → Bool
alphaB (i , j) (_ , select)  (r , c , _) = nhdB i j r c
alphaB _       (_ , done)    _           = true
alphaB _       (_ , selhere) _           = false
alphaB _       (_ , seladj)  _           = false

-- the union of Alpha(q) over a list of squares (the fold's right-hand interface)
unionB : List Sq → (at : AnyTypes SEv2) → proj₁ at → Bool
unionB []       at a = false
unionB (q ∷ qs) at a = alphaB q at a ∨ unionB qs at a

-- {| select |}, the interface Reg synchronises on and the set that gets hidden
selB : (at : AnyTypes SEv2) → proj₁ at → Bool
selB (_ , select)  _ = true
selB (_ , done)    _ = false
selB (_ , selhere) _ = false
selB (_ , seladj)  _ = false

-- the whole visible alphabet (the System side of `[|{|select|}|]`: System keeps all
-- its own events, so pairing "everything" against `selB` reproduces the interface
-- parallel exactly for these two operands — Reg offers nothing outside `select`)
allB : (at : AnyTypes SEv2) → proj₁ at → Bool
allB _ _ = true

-- one ⊤ per component: the return type of a network over a square list
RetOf : List Sq → Set
RetOf []       = ⊤poly {lzero}
RetOf (_ ∷ ps) = ⊤poly {lzero} × RetOf ps

-- System = || p : Coords @ [Alpha(p)] cf(p)   (sudoku2.csp:233): a right fold of
-- binary alphabetised parallel, each head alphabet against the union of the tail's.
net : (Sq → SProc) → (p : Sq) → (ps : List Sq) → PTree SEv2 (ExtI SEv2) (RetOf ps)
net cf p []       = cf p
net cf p (q ∷ qs) = cf p ⟦ boolES (alphaB p) ∥ boolES (unionB (q ∷ qs)) ⟧ net cf q qs

-- the 16 squares in scan order, split as head + tail for the fold
sqTail : List Sq
sqTail =
                    (0F , 1F) ∷ (0F , 2F) ∷ (0F , 3F)
  ∷ (1F , 0F) ∷ (1F , 1F) ∷ (1F , 2F) ∷ (1F , 3F)
  ∷ (2F , 0F) ∷ (2F , 1F) ∷ (2F , 2F) ∷ (2F , 3F)
  ∷ (3F , 0F) ∷ (3F , 1F) ∷ (3F , 2F) ∷ (3F , 3F) ∷ []

-- Coordlist (sudoku2.csp:44): the squares in scan order, top-left = (0,0)
squares : List Sq
squares = (0F , 0F) ∷ sqTail

-- Reg(ls) (sudoku2.csp:244): fixes the order of selection; `Reg <>` is STOP.
Reg : List Sq → SProc
-- the visible offers of Reg (named, so its force always reduces)
regV : List Sq → (at : AnyTypes SEv2) → ContinueType at (Maybe SProc)

regV []             _            _           = nothing
regV ((i , j) ∷ ps) (_ , select) (r , c , _) = case (i ==F r) ∧ (j ==F c) of λ where
    true  → just (Reg ps)
    false → nothing
regV (_ ∷ _)        (_ , done)    _ = nothing
regV (_ ∷ _)        (_ , selhere) _ = nothing
regV (_ ∷ _)        (_ , seladj)  _ = nothing

force (Reg ls) = react (regV ls) ∅t

-- scanorder (sudoku2.csp:248), the script's default `order`: the blank squares in
-- scan order.  This is the ONE ordering ported; see the header's scoped omission.
blanks : Board → List Sq → List Sq
blanks pz []             = []
blanks pz ((i , j) ∷ ps) = case pz i j of λ where
    blank     → (i , j) ∷ blanks pz ps
    (fixed _) → blanks pz ps

order : Board → List Sq
order pz = blanks pz squares

-- RegSys = System [|{|select|}|] Reg(order)   (sudoku2.csp:255)
RegSys : (Sq → SProc) → List Sq → PTree SEv2 (ExtI SEv2) (RetOf sqTail × ⊤poly {lzero})
RegSys cf ord = net cf (0F , 0F) sqTail ⟦ boolES allB ∥ boolES selB ⟧ Reg ord

-- RegSys \ {|select|}: the process the two assertions are about
Hidden : (Sq → SProc) → List Sq → PTree SEv2 (ExtI SEv2) (RetOf sqTail × ⊤poly {lzero})
Hidden cf ord = RegSys cf ord ∖ boolES selB

------------------------------------------------------------------------------------
-- §A.5  The two boards.
------------------------------------------------------------------------------------

-- goodP: Ch4's solved grid with (3,3) blanked — 15 givens, unique completion 0.
--   0 1 2 3
--   2 3 0 1
--   1 0 3 2
--   3 2 1 .
goodP : Board
goodP = row4 (row4 (fixed 0F) (fixed 1F) (fixed 2F) (fixed 3F))
             (row4 (fixed 2F) (fixed 3F) (fixed 0F) (fixed 1F))
             (row4 (fixed 1F) (fixed 0F) (fixed 3F) (fixed 2F))
             (row4 (fixed 3F) (fixed 2F) (fixed 1F) blank)

-- badP: over-constrained (and not itself a consistent grid — the givens repeat, which
-- is allowed as an INITIAL configuration: the cells only constrain later selections).
-- The single blank (3,3) is blocked for every symbol: row 3 gives 1,2,3 and column 3
-- gives 0 at (0,3).  cf. Ch4's `badGrid`.
--   0 0 0 0
--   0 0 0 1
--   0 0 0 2
--   1 2 3 .
badP : Board
badP = row4 (row4 (fixed 0F) (fixed 0F) (fixed 0F) (fixed 0F))
            (row4 (fixed 0F) (fixed 0F) (fixed 0F) (fixed 1F))
            (row4 (fixed 0F) (fixed 0F) (fixed 0F) (fixed 2F))
            (row4 (fixed 1F) (fixed 2F) (fixed 3F) blank)

-- the four systems of interest: generic-plus-renamed and direct, on each board
SysGood SysGood′ SysBad : PTree SEv2 (ExtI SEv2) (RetOf sqTail × ⊤poly {lzero})
SysGood  = Hidden (Cell  goodP) (order goodP)
SysGood′ = Hidden (Cell′ goodP) (order goodP)
SysBad   = Hidden (Cell  badP)  (order badP)

------------------------------------------------------------------------------------
-- §B. THE ASSERTIONS ON `goodP`: both are FALSE (the puzzle is solvable).
--
-- `order goodP` is the one-element list ⟨(3,3)⟩, so `Reg` admits exactly one
-- selection.  The unique legal symbol there is 0: row 3 already holds 3,2,1, column 3
-- holds 3,1,2 and the bottom-right box holds 3,2,1, so every neighbour of (3,3) is
-- `GFixed w` with w ≠ 0 and therefore accepts `seladj.0` (renamed: `select.(3,3).0`),
-- while (3,3) itself is `GVar` and accepts `selhere.0`.  The 8 squares that are NOT
-- neighbours of (3,3) do not have `select.(3,3)` in their alphabet, so the fold routes
-- the event past them.  Hiding turns that single visible event into a τ; afterwards
-- all 16 squares are `GFixed`, `done` is in every alphabet and is NOT hidden, so it
-- escapes — a nonempty trace, which refutes `STOP [T= RegSys\{|select|}`.
------------------------------------------------------------------------------------

-- the one visible event the hidden system can perform
doneEv : Event√ (RetOf sqTail × ⊤poly {lzero})
doneEv = evl (evLabel ⊤ done tt)

-- Stop performs no event at all, so ⟨done⟩ is not one of its traces
stop-no-done : ¬ (traces (Stop {R = RetOf sqTail × ⊤poly {lzero}}) (doneEv ∷ []))
stop-no-done (_ , ⟹-τ  (sSil ()) _)
stop-no-done (_ , ⟹-τ  (sTau refl br) _) = case br of λ ()
stop-no-done (_ , ⟹-ev (sVis refl br) _) = case br of λ ()

-- ⟨done⟩ is a trace of the RENAMED network: the hidden `select.(3,3).0`, then `done`.
good-trace : traces SysGood (doneEv ∷ [])
good-trace = _ , ⟹-τ (sTau {i = _ , pair (fin {n = 2}) (base select)}
                           {a = lift (fs fz) , (3F , 3F , 0F)} refl refl)
                 (⟹-ev (sVis {at = ⊤ , done} {a = tt} refl refl) ⟹-refl)

-- ⟨done⟩ is a trace of the DIRECT network too (sudoku2.csp's `System'`).
good-trace′ : traces SysGood′ (doneEv ∷ [])
good-trace′ = _ , ⟹-τ (sTau {i = _ , pair (fin {n = 2}) (base select)}
                            {a = lift (fs fz) , (3F , 3F , 0F)} refl refl)
                  (⟹-ev (sVis {at = ⊤ , done} {a = tt} refl refl) ⟹-refl)

-- assert STOP [T= RegSys \{|select|}  FAILS on goodP  — the counterexample is ⟨done⟩,
-- reached by the solving selection.  This is sudoku2.csp:258 for the RENAMED network.
stop⋢hidden : ¬ (Stop ⊑T SysGood)
stop⋢hidden le = stop-no-done (le (doneEv ∷ []) good-trace)

-- assert STOP [T= RegSys'\{|select|}  FAILS on goodP  (sudoku2.csp:259, direct form).
stop⋢hidden′ : ¬ (Stop ⊑T SysGood′)
stop⋢hidden′ le = stop-no-done (le (doneEv ∷ []) good-trace′)

------------------------------------------------------------------------------------
-- §C. THE ASSERTION ON `badP`: it HOLDS (the puzzle is unsolvable, so nothing at all
-- is visible).  `order badP` is again ⟨(3,3)⟩, and the initial configuration is
-- already dead: `Reg` admits only `select.(3,3).v`, and each of the four symbols is
-- refused by some neighbour of (3,3) that is already `GFixed` with that value (0 by
-- (0,3), 1 by (3,0), 2 by (3,1), 3 by (3,2)).  Meanwhile `done` is refused because
-- (3,3) is still `GVar`.  So the hidden system is STUCK, its only trace is ⟨⟩, and
-- `STOP [T= RegSys\{|select|}` holds — FDR reports no counterexample, i.e. no solution.
--
-- Proving "stuck" needs, besides the visible refusals, that no τ is enabled anywhere.
-- The τ-space of the composite nests one `pair fin` tag per operator layer (16 folds +
-- the Reg interface + the hiding), so instead of case-splitting the nested index by
-- hand the three τ-introduction sites get one compositional lemma each, and the
-- 16-layer fact is then 16 applications of the parallel one.
------------------------------------------------------------------------------------

open import Relation.Binary.PropositionalEquality using (sym; trans)
open import Semantics.Deadlock {E = SEv2} {I = ExtI SEv2}
  using (IsStuck; HasDeadlock; ∖√-refl)

-- the visible-offer part / the τ-branch part of a process (they reduce whenever the
-- process does, which lets the lemmas below be STATED about a concrete network)
vOf : {R : Set} → PTree SEv2 (ExtI SEv2) R
    → (at : AnyTypes SEv2) → ContinueType at (Maybe (PTree SEv2 (ExtI SEv2) R))
vOf P = viewV (P .force)

τOf : {R : Set} → PTree SEv2 (ExtI SEv2) R
    → (i : AnyTypes (ExtI SEv2)) → ContinueType i (Maybe (PTree SEv2 (ExtI SEv2) R))
τOf P = viewT (P .force)

-- an everywhere-`nothing` τ-branch map: the node it belongs to is stable
NoT : {R : Set}
    → ((i : AnyTypes (ExtI SEv2)) → ContinueType i (Maybe (PTree SEv2 (ExtI SEv2) R)))
    → Set₁
NoT τc = ∀ i a → τc i a ≡ nothing

-- the empty τ-branch (every square process and Reg carry it) offers no τ
∅t-noT : {R : Set} → NoT (∅t {R = R})
∅t-noT _ _ = refl

-- RENAMING adds no τ: `extBranch` pulls the index back and feeds the source τ-map,
-- which is empty.  Both branches of its `with extBwd` collapse to `nothing`.
extBranch-noT :
    {R : Set} (inv : (bt : AnyTypes SEv2) → proj₁ bt → Maybe ConcEvent₁)
    {τcP : (i : AnyTypes (ExtI SEv2)) → ContinueType i (Maybe (PTree SEv2 (ExtI SEv2) R))}
  → NoT τcP → NoT (extBranch (invRel inv) (invPreimg inv) τcP)
extBranch-noT inv h (A , eι) a with extBwd eι
... | just eι₁ rewrite h (A , eι₁) a = refl
... | nothing                        = refl

-- ALPHABETISED PARALLEL adds no τ: its τ-map only forwards each side's own τ-branch,
-- tagged `pair fin` (tag0 = left, tag1 = right); every other index is empty.
αpar-noT :
    {R₁ R₂ R : Set} (A B : EventSet) (m : R₁ → R₂ → R)
    {τcP : (i : AnyTypes (ExtI SEv2)) → ContinueType i (Maybe (PTree SEv2 (ExtI SEv2) R₁))}
    {τcQ : (i : AnyTypes (ExtI SEv2)) → ContinueType i (Maybe (PTree SEv2 (ExtI SEv2) R₂))}
    {P : PTree SEv2 (ExtI SEv2) R₁} {Q : PTree SEv2 (ExtI SEv2) R₂}
  → NoT τcP → NoT τcQ → NoT (αpar-pTau A B m τcP τcQ P Q)
αpar-noT A B m hP hQ (_ , base _)            _ = refl
αpar-noT A B m hP hQ (_ , fin)               _ = refl
αpar-noT A B m hP hQ (_ , pair (base _) _)   _ = refl
αpar-noT A B m hP hQ (_ , pair (pair _ _) _) _ = refl
αpar-noT A B m hP hQ (_ , pair fin i) (lift fz , a)          rewrite hP (_ , i) a = refl
αpar-noT A B m hP hQ (_ , pair fin i) (lift (fs fz) , a)     rewrite hQ (_ , i) a = refl
αpar-noT A B m hP hQ (_ , pair fin i) (lift (fs (fs _)) , a)                      = refl

-- HIDING adds no τ when every hidden event is refused: tag0 forwards P's own τ (none),
-- tag1 is the newly-hidden visible event (none, by the refusal hypothesis).
hide-noT :
    {R : Set} (A : EventSet)
    {v  : (at : AnyTypes SEv2) → ContinueType at (Maybe (PTree SEv2 (ExtI SEv2) R))}
    {τc : (i : AnyTypes (ExtI SEv2)) → ContinueType i (Maybe (PTree SEv2 (ExtI SEv2) R))}
  → NoT τc
  → (∀ (at : AnyTypes SEv2) (a : proj₁ at) → A .mem at a → v at a ≡ nothing)
  → NoT (hide-hTau A (react v τc))
hide-noT A hT hV (_ , base _)            _ = refl
hide-noT A hT hV (_ , fin)               _ = refl
hide-noT A hT hV (_ , pair (base _) _)   _ = refl
hide-noT A hT hV (_ , pair (pair _ _) _) _ = refl
hide-noT A hT hV (_ , pair fin i) (lift fz , a) rewrite hT (_ , i) a = refl
hide-noT A hT hV (_ , pair fin (base e)) (lift (fs fz) , a) with A .dec (_ , e) a
... | yes mem rewrite hV (_ , e) a mem = refl
... | no  _                            = refl
hide-noT A hT hV (_ , pair fin (pair _ _)) (lift (fs fz) , a) = refl
hide-noT A hT hV (_ , pair fin fin)        (lift (fs fz) , a) = refl
hide-noT A hT hV (_ , pair fin i) (lift (fs (fs _)) , a)      = refl

-- The over-constrained network: NO square and NO fold layer offers a τ (16 layers,
-- each a `Cell` = renamed generic square whose own τ-branch is empty).
bad-net-noT : NoT (τOf (net (Cell badP) (0F , 0F) sqTail))
bad-net-noT =
  αpar-noT _ _ _ (extBranch-noT _ ∅t-noT) (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT)
  (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT) (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT)
  (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT) (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT)
  (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT) (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT)
  (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT) (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT)
  (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT) (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT)
  (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT) (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT)
  (αpar-noT _ _ _ (extBranch-noT _ ∅t-noT) (extBranch-noT _ ∅t-noT)))))))))))))))

-- No `select.(r,c).v` is offered by the over-constrained system, so hiding emits no τ.
-- For (r,c) ≠ (3,3) the square at (r,c) is itself already `GFixed`, so it refuses
-- `selhere` (i.e. its own selection) for every symbol; at (3,3) each symbol in turn is
-- refused by the neighbour that already holds it.
bad-sel-refused : ∀ (at : AnyTypes SEv2) (a : proj₁ at) → boolES selB .mem at a
                → vOf (RegSys (Cell badP) (order badP)) at a ≡ nothing
bad-sel-refused (_ , done)    _ ()
bad-sel-refused (_ , selhere) _ ()
bad-sel-refused (_ , seladj)  _ ()
bad-sel-refused (_ , select) (fz , fz , fz) _ = refl
bad-sel-refused (_ , select) (fz , fz , fs fz) _ = refl
bad-sel-refused (_ , select) (fz , fz , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fz , fz , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fz , fs fz , fz) _ = refl
bad-sel-refused (_ , select) (fz , fs fz , fs fz) _ = refl
bad-sel-refused (_ , select) (fz , fs fz , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fz , fs fz , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fz , fs (fs fz) , fz) _ = refl
bad-sel-refused (_ , select) (fz , fs (fs fz) , fs fz) _ = refl
bad-sel-refused (_ , select) (fz , fs (fs fz) , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fz , fs (fs fz) , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fz , fs (fs (fs fz)) , fz) _ = refl
bad-sel-refused (_ , select) (fz , fs (fs (fs fz)) , fs fz) _ = refl
bad-sel-refused (_ , select) (fz , fs (fs (fs fz)) , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fz , fs (fs (fs fz)) , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fs fz , fz , fz) _ = refl
bad-sel-refused (_ , select) (fs fz , fz , fs fz) _ = refl
bad-sel-refused (_ , select) (fs fz , fz , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs fz , fz , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fs fz , fs fz , fz) _ = refl
bad-sel-refused (_ , select) (fs fz , fs fz , fs fz) _ = refl
bad-sel-refused (_ , select) (fs fz , fs fz , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs fz , fs fz , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fs fz , fs (fs fz) , fz) _ = refl
bad-sel-refused (_ , select) (fs fz , fs (fs fz) , fs fz) _ = refl
bad-sel-refused (_ , select) (fs fz , fs (fs fz) , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs fz , fs (fs fz) , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fs fz , fs (fs (fs fz)) , fz) _ = refl
bad-sel-refused (_ , select) (fs fz , fs (fs (fs fz)) , fs fz) _ = refl
bad-sel-refused (_ , select) (fs fz , fs (fs (fs fz)) , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs fz , fs (fs (fs fz)) , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fz , fz) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fz , fs fz) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fz , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fz , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs fz , fz) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs fz , fs fz) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs fz , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs fz , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs (fs fz) , fz) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs (fs fz) , fs fz) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs (fs fz) , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs (fs fz) , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs (fs (fs fz)) , fz) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs (fs (fs fz)) , fs fz) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs (fs (fs fz)) , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs (fs fz) , fs (fs (fs fz)) , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fz , fz) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fz , fs fz) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fz , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fz , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs fz , fz) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs fz , fs fz) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs fz , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs fz , fs (fs (fs fz))) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs (fs fz) , fz) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs (fs fz) , fs fz) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs (fs fz) , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs (fs fz) , fs (fs (fs fz))) _ = refl
-- (3,3) is the blank square: each symbol is blocked by an already-fixed neighbour
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs (fs (fs fz)) , fz) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs (fs (fs fz)) , fs fz) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs (fs (fs fz)) , fs (fs fz)) _ = refl
bad-sel-refused (_ , select) (fs (fs (fs fz)) , fs (fs (fs fz)) , fs (fs (fs fz))) _ = refl

-- the hidden over-constrained system offers no τ (network + Reg interface + hiding)
bad-noT : NoT (τOf SysBad)
bad-noT = hide-noT (boolES selB) (αpar-noT _ _ _ bad-net-noT ∅t-noT) bad-sel-refused

-- and no visible event either: `select` is hidden, `done` is refused by the still-blank
-- (3,3), and the generic square's private events are in no square's alphabet.
bad-stuck : IsStuck SysBad
bad-stuck (sRet eq)      = case eq of λ ()
bad-stuck (sSil eq)      = case eq of λ ()
bad-stuck (sTau {i = i} {a = a} refl br) = case trans (sym (bad-noT i a)) br of λ ()
bad-stuck (sVis {at = _ , select}  refl br) = case br of λ ()
bad-stuck (sVis {at = _ , done}    refl br) = case br of λ ()
bad-stuck (sVis {at = _ , selhere} refl br) = case br of λ ()
bad-stuck (sVis {at = _ , seladj}  refl br) = case br of λ ()

-- a stuck process has only the empty trace
stuck-trace : {R : Set} {P Q : PTree SEv2 (ExtI SEv2) R} {s : List (Event√ R)}
            → IsStuck P → P ⟹⟨ s ⟩ Q → s ≡ []
stuck-trace st ⟹-refl        = refl
stuck-trace st (⟹-τ  step _) = ⊥-elim (st step)
stuck-trace st (⟹-ev step _) = ⊥-elim (st step)

-- assert STOP [T= RegSys\{|select|}  HOLDS on badP  (sudoku2.csp:258): the puzzle has
-- no solution, so FDR finds no counterexample.
stop⊑hidden-bad : Stop ⊑T SysBad
stop⊑hidden-bad s (P′ , run) with stuck-trace bad-stuck run
... | refl = Stop , ⟹-refl

-- the same fact read as Ch4 reads it: the over-constrained board deadlocks
bad-deadlocks : HasDeadlock SysBad
bad-deadlocks = [] , SysBad , ∖√-refl , bad-stuck

------------------------------------------------------------------------------------
-- §D. Sanity checks: the two results above are not vacuous.
------------------------------------------------------------------------------------

-- `order` really is scanorder: on both boards the one blank square is (3,3)
order-goodP : order goodP ≡ (3F , 3F) ∷ []
order-goodP = refl

order-badP : order badP ≡ (3F , 3F) ∷ []
order-badP = refl

-- `done` is NOT available before the last square is filled, so §B's ⟨done⟩ genuinely
-- needed the hidden selection: the still-blank (3,3) is `GVar`, which offers no `done`.
good-done-blocked : ∀ {X} → ¬ (SysGood ─[ ev doneEv ]─► X)
good-done-blocked (sVis {at = ⊤ , done} refl br) = case br of λ ()

-- the completion at (3,3) is unique: symbols 1, 2 and 3 are refused there, each by the
-- neighbour that already holds it (column 3 holds 1 and 2, row 3 holds 1, 2 and 3).
good-sel-1 :
  vOf (RegSys (Cell goodP) (order goodP)) ((Fin 4 × Fin 4 × Fin 4) , select) (3F , 3F , 1F)
    ≡ nothing
good-sel-1 = refl

good-sel-2 :
  vOf (RegSys (Cell goodP) (order goodP)) ((Fin 4 × Fin 4 × Fin 4) , select) (3F , 3F , 2F)
    ≡ nothing
good-sel-2 = refl

good-sel-3 :
  vOf (RegSys (Cell goodP) (order goodP)) ((Fin 4 × Fin 4 × Fin 4) , select) (3F , 3F , 3F)
    ≡ nothing
good-sel-3 = refl


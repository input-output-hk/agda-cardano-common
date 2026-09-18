{-# OPTIONS --guardedness #-}

-- UCS chapter 3, final sections (= TPC chapter 2, final sections): the roaming
-- robot, from `ucs/chapter03/robots.csp` (A.W. Roscoe).  The subject is PARALLEL
-- COMPOSITION AS CONJUNCTION: `ROBOT` roams the whole integer plane freely, and
-- every process put in parallel with it acts as a CONJUNCT that can only REMOVE
-- behaviour — never add any.
--
--   channel position : (Int,Int)      channel north, south, east, west
--
--   ROBOT(n,m) = position.(n,m) -> ROBOT(n,m)
--                [] north -> ROBOT(n+1,m)  [] south -> ROBOT(n-1,m)
--                [] east  -> ROBOT(n,m+1)  [] west  -> ROBOT(n,m-1)
--
-- MODEL-ONLY.  The source carries NO FDR `assert` whatsoever, and says of itself
-- that it is *"a 'pure' presentation that cannot be run on FDR, though it can on
-- ProBE"*, and of `ROBOT` that *"this is of course an infinite-state process and it
-- cannot be run on FDR, even if put in a context that would restrict it to finitely
-- many of its states."*  So the deliverable here is a productive, well-defined model
-- plus transition-sanity checks — there is NO refinement or FD theorem, and none is
-- claimed.  (Same posture as `Ch7/Counter.agda`.)
--
-- COORDINATES ARE `ℤ`, AND THE PROCESS IS GENUINELY INFINITE-STATE.  `ROBOT`'s two
-- coordinates are `Data.Integer.ℤ`, not a `Fin` grid: `ROBOT n m` really does have one
-- distinct state per point of ℤ × ℤ, and `north`/`south`/`east`/`west` really are
-- enabled from every one of them (see `robot-north` … `robot-west` below, which are
-- stated for ARBITRARY `n m : ℤ`).  This is a case where the Agda model captures
-- something FDR cannot: the development is coinductive and never enumerates a state
-- space, so an infinite-state process is no harder to define, force, or step than a
-- finite one, whereas FDR must explore and therefore cannot load this file at all.
-- Nothing below silently shrinks the coordinate type to make a check go through.
--
-- THE CRUX OF THE CONJUNCTION READING — how two counters confine one axis.  With
-- `CT(a,b,n)` a counter that always accepts `a` and accepts `b` only while its count
-- is non-zero:
--   * `CT(north,south,0)` counts (norths − souths) and refuses `south` at 0, so it
--     asserts  souths ≤ norths,  i.e.  ROW ≥ 0;
--   * `CT(south,north,N)` counts (N + souths − norths) and refuses `north` at 0, so it
--     asserts  norths − souths ≤ N,  i.e.  ROW ≤ N.
-- Neither counter mentions the robot's coordinates; each is simply a further
-- CONJUNCT, and their conjunction pins the row index into [0,N].  `CT(east,west,0)`
-- and `CT(west,east,M)` do exactly the same for the column, giving [0,M].  §B.2 and
-- §B.3 below are the checks that make this operational: the FREE robot offers a move
-- that the CONSTRAINED robot REFUSES.
--
-- A DISCREPANCY IN THE SOURCE, PORTED AS WRITTEN.  Roscoe writes that `BlockSet` gets
-- "the same sort of effect ... more efficiently" than the parallel composition
-- `Blocks`.  But the two comprehensions filter DIFFERENT squares:
--   * `Blocks` keeps  r%3==2, s%3==1   ⇒ blocked squares {(2,1),(2,4)}      (`blockSquares`)
--   * `S`      keeps  r%2==1, s%2==1   ⇒ blocked squares {(1,1),(1,3),(1,5),
--                                                          (3,1),(3,3),(3,5)}
-- so `RobotWithBlocks` and `RobotWithBlockSet` are NOT the same process.  Both filters
-- are ported exactly as written (and pinned by `blockSquares-is` / `S-is` in §B.5), no
-- equivalence between the two is attempted, and the filters are NOT quietly aligned to
-- make one hold.  The honest general statement would be about a COMMON blocked set,
-- which the source does not assert, so it is out of scope for a MODEL-ONLY port.
--
-- ONE MODELLING NOTE.  `CT`'s count is indexed by `ℕ`, not `ℤ`: it is a COUNT, is never
-- negative anywhere it is used, and the two `ℕ` clauses (`zero` / `suc n`) reproduce
-- the source's CSPM clause order — `CT(a,b,0)` matches BEFORE the general `CT(a,b,n)`,
-- so at 0 only `a` is offered — exactly, while keeping every node definitionally
-- reducible.  This is the counter's internal state, not a robot coordinate; the
-- coordinates stay `ℤ` (see above).
--
-- Guardedness: every recursion here (`ROBOT`, `CT`, `BLOCK`, `BlockSet`) is DIRECT —
-- a `force` copattern whose corecursive occurrences sit under `just` in the same
-- equation — never through a CSP operator, so the inlined-`react` idiom of
-- `Ch3/SyncIdentity` / `Ch2/Collatz` applies and no pragma, `mutual` block, sized
-- type or hole appears anywhere below.

module CSP.Examples.UCS.Ch3.Robots where

open import Level using () renaming (zero to lzero)
open import Data.Bool using (Bool; true; false; T)
open import Data.Bool.ListAction using (any)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Nat using (ℕ; zero; suc; _%_; _≡ᵇ_)
import Data.Integer as Int
open Int using (ℤ; +_; -1ℤ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.Product.Properties using (≡-dec)
open import Data.List using (List; []; _∷_; map; filter; cartesianProduct; upTo)
open import Function.Base using (case_of_)
open import Relation.Nullary using (Dec; yes; no; ¬_)
open import Relation.Nullary.Decidable using (T?; ⌊_⌋)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import Process_Trees
open PTree

------------------------------------------------------------------------------------
-- §A. Model.
------------------------------------------------------------------------------------

-- §A.1 the five channels: `position : (Int,Int)` and the four nullary directions.
data REv : Set → Set where
  position              : REv (ℤ × ℤ)
  north south east west  : REv ⊤

-- decidable equality on the event sort (needed by the CSP layer, and by `CT` below to
-- tell its own two parameter events `a` and `b` apart)
REv-≟ : (x y : AnyTypes REv) → Dec (x ≡ y)
REv-≟ (_ , position) (_ , position) = yes refl
REv-≟ (_ , position) (_ , north)    = no (λ ())
REv-≟ (_ , position) (_ , south)    = no (λ ())
REv-≟ (_ , position) (_ , east)     = no (λ ())
REv-≟ (_ , position) (_ , west)     = no (λ ())
REv-≟ (_ , north)    (_ , position) = no (λ ())
REv-≟ (_ , north)    (_ , north)    = yes refl
REv-≟ (_ , north)    (_ , south)    = no (λ ())
REv-≟ (_ , north)    (_ , east)     = no (λ ())
REv-≟ (_ , north)    (_ , west)     = no (λ ())
REv-≟ (_ , south)    (_ , position) = no (λ ())
REv-≟ (_ , south)    (_ , north)    = no (λ ())
REv-≟ (_ , south)    (_ , south)    = yes refl
REv-≟ (_ , south)    (_ , east)     = no (λ ())
REv-≟ (_ , south)    (_ , west)     = no (λ ())
REv-≟ (_ , east)     (_ , position) = no (λ ())
REv-≟ (_ , east)     (_ , north)    = no (λ ())
REv-≟ (_ , east)     (_ , south)    = no (λ ())
REv-≟ (_ , east)     (_ , east)     = yes refl
REv-≟ (_ , east)     (_ , west)     = no (λ ())
REv-≟ (_ , west)     (_ , position) = no (λ ())
REv-≟ (_ , west)     (_ , north)    = no (λ ())
REv-≟ (_ , west)     (_ , south)    = no (λ ())
REv-≟ (_ , west)     (_ , east)     = no (λ ())
REv-≟ (_ , west)     (_ , west)     = yes refl

open import CSP.Operators REv-≟
open EventSet

-- the CSP process type of this example
RProc : Set₁
RProc = PTree REv (ExtI REv) (⊤ {lzero})

-- decidable equality on coordinate pairs (used to PIN the output `position!(n,m)`,
-- and to test whether a move's target square is blocked)
_≟C_ : (p q : ℤ × ℤ) → Dec (p ≡ q)
_≟C_ = ≡-dec Int._≟_ Int._≟_

-- `member(p,S)` for a finite set of squares represented as a list
memberC : ℤ × ℤ → List (ℤ × ℤ) → Bool
memberC p ps = any (λ q → ⌊ p ≟C q ⌋) ps

-- the four direction events, as elements of the event sort (so they can be PASSED
-- to `CT`, which is parametric in its two events)
nE sE eE wE : AnyTypes REv
nE = (⊤ , north)
sE = (⊤ , south)
eE = (⊤ , east)
wE = (⊤ , west)

-- a channel-level `EventSet` from a Boolean channel test
chanBool : (AnyTypes REv → Bool) → EventSet
chanBool f .mem at _ = T (f at)
chanBool f .dec at _ = T? (f at)

-- {north,south}: the alphabet the two ROW counters control
NSα : EventSet
NSα = chanBool (λ where (_ , north) → true
                        (_ , south) → true
                        _           → false)

-- {east,west}: the alphabet the two COLUMN counters control
EWα : EventSet
EWα = chanBool (λ where (_ , east) → true
                        (_ , west) → true
                        _          → false)

-- {north,south,east,west}: the alphabet every BLOCK / BlockSet conjunct controls
NSEWα : EventSet
NSEWα = chanBool (λ where (_ , position) → false
                          _              → true)

-- §A.2 the roaming robot.  `position.(n,m)` is an OUTPUT, so only the pair `(n,m)`
-- is offered on that channel; the four directions are always available, from EVERY
-- square of ℤ × ℤ.
ROBOT : ℤ → ℤ → RProc
force (ROBOT n m) = react
  (λ where (_ , position) p → case p ≟C (n , m) of λ where
                                 (yes _) → just (ROBOT n m)
                                 (no  _) → nothing
           (_ , north) _    → just (ROBOT (Int.suc n) m)
           (_ , south) _    → just (ROBOT (Int.pred n) m)
           (_ , east)  _    → just (ROBOT n (Int.suc m))
           (_ , west)  _    → just (ROBOT n (Int.pred m)))
  ∅t

-- §A.3 the counter conjunct, PARAMETRIC in its two events `a` and `b` (it is
-- instantiated at four different event pairs below).  Clause order matters and
-- follows the source: `CT(a,b,0)` offers ONLY `a`; `CT(a,b,n)` offers `a` (count up)
-- and `b` (count down).
CT : AnyTypes REv → AnyTypes REv → ℕ → RProc
force (CT a b zero) = react
  (λ at _ → case REv-≟ at a of λ where
               (yes _) → just (CT a b 1)
               (no  _) → nothing)
  ∅t
force (CT a b (suc n)) = react
  (λ at _ → case REv-≟ at a of λ where
               (yes _) → just (CT a b (suc (suc n)))
               (no  _) → case REv-≟ at b of λ where
                            (yes _) → just (CT a b n)
                            (no  _) → nothing)
  ∅t

-- §A.4 the two DERIVED process-level operators of the source, really derived.
--
-- `AddCond(P,A,Q) = P [|A|] Q` — the interface parallel, i.e. this codebase's
-- `_∥⇘_⇙_` (`CSP/Operators.agda:658`, the `Par⊤` instance of the shared-set `Par`).
-- That is the operator whose types line up: the source's `[|A|]` is ONE shared set,
-- not a pair of per-component alphabets, so the alphabetised `_⟦_∥_⟧_`
-- (`CSP/Operators.agda:781`) is NOT what is wanted here — and the source explains
-- why it did not write the alphabetised form either ("this would not work in this
-- case since ... the set Events is infinite").

-- AddCond(P,A,Q) = P [|A|] Q : `Q` becomes a conjunct constraining `P` over `A`
AddCond : RProc → EventSet → RProc → RProc
AddCond P A Q = P ∥⇘ A ⇙ Q

-- ListConds(P,<>) = P ; ListConds(P,<(Q,A)>^cs) = ListConds(AddCond(P,A,Q),cs) —
-- a genuine fold over a list of (process, alphabet) pairs, mirroring the source's
-- sequence pattern-matching (empty sequence / head-cons-tail), NOT a hand-expanded
-- fixed nest.
ListConds : RProc → List (RProc × EventSet) → RProc
ListConds P []             = P
ListConds P ((Q , A) ∷ cs) = ListConds (AddCond P A Q) cs

-- §A.5 the table.  Rows 0..N, columns 0..M.
N M : ℕ
N = 3
M = 5

-- the general `RobotOnTable` state: robot at (n,m) with the four counters at c₁..c₄
-- (c₁ = CT(north,south), c₂ = CT(south,north), c₃ = CT(east,west), c₄ = CT(west,east))
Table : ℤ → ℤ → ℕ → ℕ → ℕ → ℕ → RProc
Table n m c₁ c₂ c₃ c₄ =
  ListConds (ROBOT n m)
    ((CT nE sE c₁ , NSα) ∷ (CT sE nE c₂ , NSα) ∷
     (CT eE wE c₃ , EWα) ∷ (CT wE eE c₄ , EWα) ∷ [])

-- RobotOnTable = ListConds(ROBOT(0,0), <(CT(north,south,0),{north,south}),
--   (CT(south,north,N),{north,south}), (CT(east,west,0),{east,west}),
--   (CT(west,east,M),{east,west})>)  — the four conjuncts confine the robot to [0,N]×[0,M]
RobotOnTable : RProc
RobotOnTable = Table (+ 0) (+ 0) 0 N 0 M

-- §A.6 a single forbidden square (r,s): each direction is guarded so that the move
-- is offered exactly when its TARGET square is not (r,s).  BLOCK tracks the robot's
-- position itself, and offers nothing on `position` (which is outside its alphabet).
BLOCK : ℤ → ℤ → ℤ → ℤ → RProc
force (BLOCK r s n m) = react
  (λ where (_ , position) _ → nothing
           (_ , north) _    → case (Int.suc n , m) ≟C (r , s) of λ where
                                 (yes _) → nothing
                                 (no  _) → just (BLOCK r s (Int.suc n) m)
           (_ , south) _    → case (Int.pred n , m) ≟C (r , s) of λ where
                                 (yes _) → nothing
                                 (no  _) → just (BLOCK r s (Int.pred n) m)
           (_ , east)  _    → case (n , Int.suc m) ≟C (r , s) of λ where
                                 (yes _) → nothing
                                 (no  _) → just (BLOCK r s n (Int.suc m))
           (_ , west)  _    → case (n , Int.pred m) ≟C (r , s) of λ where
                                 (yes _) → nothing
                                 (no  _) → just (BLOCK r s n (Int.pred m)))
  ∅t

-- `<0..k>` filtered by a residue test, as a list of ℤ (the source's comprehension
-- generators `r <- <0..N>, r%d==j`)
idxs : ℕ → (ℕ → Bool) → List ℤ
idxs k p = map (+_) (filter (λ i → T? (p i)) (upTo (suc k)))

-- the blocked squares of `Blocks`: r <- <0..N>, s <- <0..M>, r%3==2, s%3==1
blockSquares : List (ℤ × ℤ)
blockSquares = cartesianProduct (idxs N (λ r → r % 3 ≡ᵇ 2)) (idxs M (λ s → s % 3 ≡ᵇ 1))

-- Blocks = <(BLOCK(r,s,0,0),{north,south,east,west}) | (r,s) <- blockSquares>
Blocks : List (RProc × EventSet)
Blocks = map (λ rs → (BLOCK (proj₁ rs) (proj₂ rs) (+ 0) (+ 0) , NSEWα)) blockSquares

-- RobotWithBlocks = ListConds(RobotOnTable, Blocks)
RobotWithBlocks : RProc
RobotWithBlocks = ListConds RobotOnTable Blocks

-- §A.7 the same idea done with ONE conjunct carrying a finite set of illegal squares
-- (the source's "more efficient" version — but see the header: it blocks a DIFFERENT
-- set of squares than `Blocks` does).
BlockSet : List (ℤ × ℤ) → ℤ → ℤ → RProc
force (BlockSet Sq n m) = react
  (λ where (_ , position) _ → nothing
           (_ , north) _    → case memberC (Int.suc n , m) Sq of λ where
                                 true  → nothing
                                 false → just (BlockSet Sq (Int.suc n) m)
           (_ , south) _    → case memberC (Int.pred n , m) Sq of λ where
                                 true  → nothing
                                 false → just (BlockSet Sq (Int.pred n) m)
           (_ , east)  _    → case memberC (n , Int.suc m) Sq of λ where
                                 true  → nothing
                                 false → just (BlockSet Sq n (Int.suc m))
           (_ , west)  _    → case memberC (n , Int.pred m) Sq of λ where
                                 true  → nothing
                                 false → just (BlockSet Sq n (Int.pred m)))
  ∅t

-- S = {(r,s) | r <- {0..N}, s <- {0..M}, r%2==1, s%2==1}
S : List (ℤ × ℤ)
S = cartesianProduct (idxs N (λ r → r % 2 ≡ᵇ 1)) (idxs M (λ s → s % 2 ≡ᵇ 1))

-- the general `RobotWithBlockSet` state (the `BlockSet` conjunct shadows the robot's
-- own position, exactly as `BLOCK` does)
TableBS : ℤ → ℤ → ℕ → ℕ → ℕ → ℕ → RProc
TableBS n m c₁ c₂ c₃ c₄ = AddCond (Table n m c₁ c₂ c₃ c₄) NSEWα (BlockSet S n m)

-- RobotWithBlockSet = AddCond(RobotOnTable,{north,south,east,west},BlockSet(S,0,0))
RobotWithBlockSet : RProc
RobotWithBlockSet = TableBS (+ 0) (+ 0) 0 N 0 M

-- the general `RobotWithBlocks` state (the two `BLOCK` conjuncts of `Blocks`, each
-- shadowing the robot's position)
TableB : ℤ → ℤ → ℕ → ℕ → ℕ → ℕ → RProc
TableB n m c₁ c₂ c₃ c₄ =
  ListConds (Table n m c₁ c₂ c₃ c₄)
    ((BLOCK (+ 2) (+ 1) n m , NSEWα) ∷ (BLOCK (+ 2) (+ 4) n m , NSEWα) ∷ [])

------------------------------------------------------------------------------------
-- §B. Transition-sanity checks (model-only — no FD/refinement claim).
--
-- The point being exhibited is the CONJUNCTION reading: each check below pairs a move
-- the FREE robot offers with the SAME move REFUSED by a constrained robot in the same
-- square, so what the parallel conjuncts do is visibly to REMOVE behaviour.
------------------------------------------------------------------------------------

open import Semantics.LTS {E = REv} {I = ExtI REv} hiding (Diverges)
open import Semantics.Failures {E = REv} {I = ExtI REv}
  using (_⟹⟨_⟩_; ⟹-refl; ⟹-ev)

-- the four direction events as visible LTS labels
northL southL eastL westL : Event√ (⊤ {lzero})
northL = evl (evLabel ⊤ north tt)
southL = evl (evLabel ⊤ south tt)
eastL  = evl (evLabel ⊤ east  tt)
westL  = evl (evLabel ⊤ west  tt)

-- `position.(n,m)` as a visible LTS label
posL : ℤ → ℤ → Event√ (⊤ {lzero})
posL n m = evl (evLabel (ℤ × ℤ) position (n , m))

------------------------------------------------------------------------------------
-- §B.1 the FREE robot: all four directions from ANY square of ℤ × ℤ, and a walk
-- whose `position` report tracks where it has got to.
------------------------------------------------------------------------------------

-- north is enabled from every square (n,m) — `n` and `m` arbitrary integers
robot-north : ∀ (n m : ℤ) → ROBOT n m ─[ ev northL ]─► ROBOT (Int.suc n) m
robot-north n m = sVis refl refl

-- …and so are the other three
robot-south : ∀ (n m : ℤ) → ROBOT n m ─[ ev southL ]─► ROBOT (Int.pred n) m
robot-south n m = sVis refl refl

robot-east : ∀ (n m : ℤ) → ROBOT n m ─[ ev eastL ]─► ROBOT n (Int.suc m)
robot-east n m = sVis refl refl

robot-west : ∀ (n m : ℤ) → ROBOT n m ─[ ev westL ]─► ROBOT n (Int.pred m)
robot-west n m = sVis refl refl

-- the `position` report tracks the walk: north, north, east lands the free robot on
-- (2,1), and `position.(2,1)` is exactly what it then offers
robot-walk : ROBOT (+ 0) (+ 0)
             ⟹⟨ northL ∷ northL ∷ eastL ∷ posL (+ 2) (+ 1) ∷ [] ⟩
             ROBOT (+ 2) (+ 1)
robot-walk = ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
             (⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) ⟹-refl)))

-- the report is PINNED to the current square: at (2,1) the robot does NOT offer
-- `position.(0,0)` (so the walk above really did observe the coordinates)
robot-pos-pinned : ∀ {X} → ¬ (ROBOT (+ 2) (+ 1) ─[ ev (posL (+ 0) (+ 0)) ]─► X)
robot-pos-pinned (sVis refl br) = case br of λ ()

-- the free robot has NO row bound: it walks straight off the top of the table, and
-- straight below row 0 (both moves are what §B.2 shows the conjuncts removing)
robot-leaves-top : ∀ (m : ℤ) → ROBOT (+ N) m ─[ ev northL ]─► ROBOT (+ 4) m
robot-leaves-top m = sVis refl refl

robot-leaves-bottom : ∀ (m : ℤ) → ROBOT (+ 0) m ─[ ev southL ]─► ROBOT -1ℤ m
robot-leaves-bottom m = sVis refl refl

------------------------------------------------------------------------------------
-- §B.2 THE POINT OF THE EXAMPLE: the counter conjuncts REMOVE behaviour.  Each of
-- the two halves below is a pair — the free robot OFFERS the move (§B.1's
-- `robot-leaves-top` / `robot-leaves-bottom`), the constrained robot in the SAME
-- square REFUSES it.
------------------------------------------------------------------------------------

-- N norths are legal, and the counters move in step with the robot: c₁ counts up
-- (0→N), c₂ counts down (N→0).  Nothing here touches the column counters c₃/c₄,
-- since north ∉ {east,west}.
table-north-walk : RobotOnTable ⟹⟨ northL ∷ northL ∷ northL ∷ [] ⟩
                   Table (+ 3) (+ 0) 3 0 0 M
table-north-walk = ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
                   (⟹-ev (sVis refl refl) ⟹-refl))

-- HALF ONE.  After N norths the robot sits on row N and `CT(south,north,·)` has run
-- down to 0, so it refuses `north`; since north ∈ {north,south} the composition must
-- SYNCHRONISE, so the whole constrained robot refuses `north`.  Contrast
-- `robot-leaves-top`, where the FREE robot at row N happily steps to row N+1: the
-- conjunct has removed exactly that behaviour.
onTable-refuses-north : ∀ {X} → ¬ (Table (+ 3) (+ 0) 3 0 0 M ─[ ev northL ]─► X)
onTable-refuses-north (sVis refl br) = case br of λ ()

-- HALF TWO.  On row 0 the other row counter `CT(north,south,0)` is at 0, so it
-- refuses `south`, and again the synchronisation makes the whole constrained robot
-- refuse it.  Contrast `robot-leaves-bottom`, where the FREE robot at row 0 steps to
-- row −1.  Together with HALF ONE the row index is confined to [0,N].
onTable-refuses-south : ∀ {X} → ¬ (RobotOnTable ─[ ev southL ]─► X)
onTable-refuses-south (sVis refl br) = case br of λ ()

-- the column axis is confined the same way by the other counter pair: at column 0
-- `CT(east,west,0)` refuses `west` …
onTable-refuses-west : ∀ {X} → ¬ (RobotOnTable ─[ ev westL ]─► X)
onTable-refuses-west (sVis refl br) = case br of λ ()

-- … while the FREE robot at column 0 goes west without complaint
robot-leaves-left : ∀ (n : ℤ) → ROBOT n (+ 0) ─[ ev westL ]─► ROBOT n -1ℤ
robot-leaves-left n = sVis refl refl

------------------------------------------------------------------------------------
-- §B.3 NON-VACUITY: the constrained robot is CONFINED, not dead.  A legal walk
-- inside the table, and a `position` report confirming where it ended up.
------------------------------------------------------------------------------------

-- north, east, east is legal on the table (row 1 of [0,3], column 2 of [0,5]); the
-- counters end at c₁=1, c₂=2 (row), c₃=2, c₄=3 (column)
onTable-walk : RobotOnTable ⟹⟨ northL ∷ eastL ∷ eastL ∷ [] ⟩ Table (+ 1) (+ 2) 1 2 2 3
onTable-walk = ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
               (⟹-ev (sVis refl refl) ⟹-refl))

-- … and the robot then reports exactly (1,2).  `position` lies in NEITHER conjunct
-- alphabet, so it passes through all four parallel layers untouched — a conjunct can
-- only constrain the events it shares.
onTable-position : Table (+ 1) (+ 2) 1 2 2 3 ─[ ev (posL (+ 1) (+ 2)) ]─►
                   Table (+ 1) (+ 2) 1 2 2 3
onTable-position = sVis refl refl

-- so the whole walk-plus-report is one run of `RobotOnTable`
onTable-walk-report : RobotOnTable
                      ⟹⟨ northL ∷ eastL ∷ eastL ∷ posL (+ 1) (+ 2) ∷ [] ⟩
                      Table (+ 1) (+ 2) 1 2 2 3
onTable-walk-report = ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl)
                      (⟹-ev (sVis refl refl) (⟹-ev onTable-position ⟹-refl)))

------------------------------------------------------------------------------------
-- §B.4 the block conjuncts: `RobotWithBlockSet` refuses a move INTO a square of `S`,
-- and `RobotWithBlocks` refuses a move into one of `blockSquares` — each again paired
-- with the same move OFFERED by the robot without that conjunct.
------------------------------------------------------------------------------------

-- (0,1) ∉ S, so going east from the origin is still legal for `RobotWithBlockSet`
withBlockSet-east : RobotWithBlockSet ─[ ev eastL ]─► TableBS (+ 0) (+ 1) 0 N 1 4
withBlockSet-east = sVis refl refl

-- (1,1) ∈ S, so `BlockSet` refuses `north` from (0,1); north ∈ its alphabet, hence
-- the whole composition refuses it
withBlockSet-refuses-north : ∀ {X} → ¬ (TableBS (+ 0) (+ 1) 0 N 1 4 ─[ ev northL ]─► X)
withBlockSet-refuses-north (sVis refl br) = case br of λ ()

-- … whereas WITHOUT the `BlockSet` conjunct the very same on-table robot goes north
onTable-north-from-01 : Table (+ 0) (+ 1) 0 N 1 4 ─[ ev northL ]─► Table (+ 1) (+ 1) 1 2 1 4
onTable-north-from-01 = sVis refl refl

-- two norths are legal for `RobotWithBlocks`: neither (1,0) nor (2,0) is blocked
withBlocks-walk : RobotWithBlocks ⟹⟨ northL ∷ northL ∷ [] ⟩ TableB (+ 2) (+ 0) 2 1 0 M
withBlocks-walk = ⟹-ev (sVis refl refl) (⟹-ev (sVis refl refl) ⟹-refl)

-- (2,1) ∈ blockSquares, so `BLOCK(2,1,·,·)` refuses `east` from (2,0)
withBlocks-refuses-east : ∀ {X} → ¬ (TableB (+ 2) (+ 0) 2 1 0 M ─[ ev eastL ]─► X)
withBlocks-refuses-east (sVis refl br) = case br of λ ()

-- … whereas without the two `BLOCK` conjuncts the same on-table robot goes east
onTable-east-from-20 : Table (+ 2) (+ 0) 2 1 0 M ─[ ev eastL ]─► Table (+ 2) (+ 1) 2 1 1 4
onTable-east-from-20 = sVis refl refl

------------------------------------------------------------------------------------
-- §B.5 the two comprehensions, pinned.  These make the header's DISCREPANCY an
-- on-the-record fact rather than a remark: the two "blocked square" sets differ, so
-- `RobotWithBlocks` and `RobotWithBlockSet` are genuinely different processes and no
-- equivalence between them is claimed.
------------------------------------------------------------------------------------

-- Blocks filters r%3==2, s%3==1 over <0..3>×<0..5>
blockSquares-is : blockSquares ≡ (+ 2 , + 1) ∷ (+ 2 , + 4) ∷ []
blockSquares-is = refl

-- S filters r%2==1, s%2==1 over {0..3}×{0..5} — a DIFFERENT set of squares
S-is : S ≡ (+ 1 , + 1) ∷ (+ 1 , + 3) ∷ (+ 1 , + 5)
         ∷ (+ 3 , + 1) ∷ (+ 3 , + 3) ∷ (+ 3 , + 5) ∷ []
S-is = refl

-- concretely: (1,1) is blocked by `BlockSet` but not by `Blocks`, and (2,1) the other
-- way round — which is why §B.4's two refusals had to be shown at different squares
one-one-in-S : memberC (+ 1 , + 1) S ≡ true
one-one-in-S = refl

one-one-not-in-blockSquares : memberC (+ 1 , + 1) blockSquares ≡ false
one-one-not-in-blockSquares = refl

two-one-in-blockSquares : memberC (+ 2 , + 1) blockSquares ≡ true
two-one-in-blockSquares = refl

two-one-not-in-S : memberC (+ 2 , + 1) S ≡ false
two-one-not-in-S = refl

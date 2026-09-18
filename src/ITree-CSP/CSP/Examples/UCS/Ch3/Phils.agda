{-# OPTIONS --guardedness #-}

-- UCS chapter 3 (= TPC chapter 2): the five dining philosophers, from
-- `ucs/chapter03/phils.csp` (A.W. Roscoe).  The subject is DEADLOCK: a symmetric
-- ring of right-handed philosophers can wedge, and two standard fixes (a butler,
-- and one left-handed philosopher) remove the wedge.
--
--   N = 5
--   channel thinks, sits, eats, getsup : PHILNAMES
--   channel picks, putsdown : PHILNAMES.FORKNAMES
--
--   PHIL(i)  = thinks.i -> sits!i -> picks!i!i -> picks!i!((i+1)%N) ->
--              eats!i -> putsdown!i!((i+1)%N) -> putsdown!i!i -> getsup!i -> PHIL(i)
--   PHILs(i) = picks!i!i -> picks!i!((i+1)%N) ->
--              putsdown!i!((i+1)%N) -> putsdown!i!i -> PHILs(i)
--   FORK(i)  = picks!i!i -> putsdown!i!i -> FORK(i)
--             [] picks!((i-1)%N)!i -> putsdown!((i-1)%N)!i -> FORK(i)
--   LPHIL(i) / LPHILs(i): as PHIL / PHILs but picking ((i+1)%N) BEFORE i.
--   BUTLER(j) = j>0 & getsup?i -> BUTLER(j-1) [] j<N-1 & sits?i -> BUTLER(j+1)
--
-- READING THE SCRIPT'S SUFFIXES.  The `s` suffix means STRIPPED DOWN, not symmetric:
-- Roscoe writes at :22-23 that *"the only events relevant to deadlock are the picks
-- and putsdown ones"* and offers the stripped bodies as the variant to actually run
-- ("which will find the same deadlock a lot faster", :74).  The `B` prefix is the
-- BUTLER solution, `AS` is ASYMMETRIC (one left-handed philosopher).
--
-- THE FIVE ASSERTIONS OF THE SCRIPT, and what this module does about each:
--   1  :69   SYSTEM     :[deadlock free [F]]   FALSE  — not covered (refused, below)
--   2  :72   SYSTEMs    :[deadlock free [F]]   FALSE  — COVERED, §A
--   3  :86   BSYSTEM    :[deadlock free [F]]   true   — not covered (deferred, below)
--   4  :103  ASSYSTEM   :[deadlock free [F]]   true   — not covered (refused, below)
--   5  :115  ASSYSTEMs  :[deadlock free [F]]   true   — COVERED, §B
-- Asserts 1 and 2 are expected to FAIL in FDR: the symmetric ring deadlocks, and
-- that failure is the point of the example.  So the Agda statement of assert 2 is a
-- NEGATION (`¬ DeadlockFree`), not a `DeadlockFree`.
--
-- THIS IS A WITNESS MODULE, NOT A PORT.  Nothing is modelled here.  Both results
-- below are IMPORTED from an existing dining-philosophers development that predates
-- this UCS campaign's conventions and lives OUTSIDE the UCS tree, at
-- `src/CSP/Examples/DiningPhilosophers/`:
--   * `DiningPhilosophersCSP.lagda.md`             — the model and the deadlock witness
--     (`dp-csp-deadlock-reachable : HasDeadlock SYSTEMsym`, :808);
--   * `DiningPhilosophersCSP_DeadlockFree.agda`    — the deadlock-freedom proof
--     (`deadlock-free-asym : DeadlockFree SYSTEMasym`, :1563);
--   * `DiningPhilosophersRelational.lagda.md`      — a separate relational abstraction
--     (a hand-generated monolithic tree over a relational `Config`, with the
--     resource-ordering strategy rather than Roscoe's flipped philosopher 0).  That
--     module is an abstraction of the PROBLEM and is NOT a model of `phils.csp`; it
--     is listed here only so nobody goes looking for it as one.  It is not used below.
-- The purpose of this file is to give `phils.csp` an entry point in the UCS tree and
-- to record, in one place and honestly, exactly how much of the script is covered.
--
-- SCOPE LIMIT 1 — ONLY `picks`/`putsdown` EXIST IN THE MODEL.  The imported model's
-- event type has the two fork channels and nothing else: `thinks`, `sits`, `eats`
-- and `getsup` are ABSENT.  So the two theorems below correspond to the STRIPPED
-- variants `SYSTEMs` and `ASSYSTEMs` (asserts 2 and 5), never to the full-bodied
-- `SYSTEM` / `ASSYSTEM` (asserts 1 and 4).  The names `SYSTEMsym` / `SYSTEMasym`
-- in the imported development are the stripped processes despite their unsuffixed
-- names; the aliasing is done explicitly at each theorem below.
--
-- SCOPE LIMIT 2 — N = 2, NOT ROSCOE'S N = 5, AND NOT PARAMETRIC.  Both imported
-- results are instances of the model at `Sys 0`, i.e. `n = suc (suc 0) = 2`: two
-- philosophers, two forks.  Neither is parametric in `N`.  A 2-ring is still a
-- genuine instance of both phenomena — two right-handed philosophers each holding
-- one fork and waiting for the other is a real deadlock, and flipping one of them
-- really does remove it — but a reader wanting Roscoe's five will not find them here.
--
-- SCOPE LIMIT 3 — the model's parallel SHAPE is flattened.  `phils.csp` brackets
-- `SYSTEMs` as an indexed alphabetised parallel of philosopher/fork PAIRS (:53-54)
-- and `ASSYSTEMs` as interleaved philosophers synchronised with interleaved forks
-- (:113).  The imported model instead uses ONE flat non-empty alphabetised fold
-- `∥ₐ⁺` over all 2N components.  No equivalence between the bracketings is proved
-- here or claimed; the flat fold is what the theorems are about.
--
-- ASSERTS 1 AND 4 ARE REFUSED, NOT MISSING.  Adding `thinks`/`sits`/`eats`/`getsup`
-- to the model would take each philosopher from 5 positions to 9 (`PPos` in
-- `DiningPhilosophersCSP_DeadlockFree.agda:502`), so the `progress` case enumeration
-- that carries the deadlock-freedom proof would grow from its current 400 clauses
-- (= 5 phil × 4 fork × 5 phil × 4 fork) to about 1300 (9 × 4 × 9 × 4) — for ZERO
-- behavioural content, since the four extra channels are unsynchronised singletons
-- that can never block.  Roscoe says as much himself at :22-23 and :105-107, and
-- recommends running the stripped version.  This is a deliberate refusal.
--
-- ASSERT 3 IS DEFERRED AND GATED on three separate things, none of which exists:
--   (a) the BUTLER.  There is no butler process anywhere in this repository, and
--       `BUTLER(j)`'s guarded external choice over a seat count needs the `sits` and
--       `getsup` channels that scope limit 1 removed — the butler is precisely the
--       case where stripping is NOT sound, as the script notes at :88-89.
--   (b) N ≥ 3.  At N = 2 the butler's bound `j < N-1` admits only ONE seated
--       philosopher, so `BSYSTEM` at N = 2 serialises the philosophers completely.
--       That is not the solution being demonstrated, so proving it would be
--       misleading rather than partial credit.
--   (c) a PARAMETRIC progress argument.  `DiningPhilosophersCSP_DeadlockFreeN.agda`
--       is the attempt at general `N`; it typechecks (1603 lines, green) but has NO
--       `DeadlockFree` or `HasDeadlock` theorem in it at all — the parametric
--       progress argument is not closed.  Its own header line 3 still says
--       "WORK IN PROGRESS (uncommitted)", which is stale as to the commit status but
--       accurate as to the mathematics.
-- So assert 3 needs a butler, a bigger ring, and a proof technique that is not yet
-- available.  Nothing about it is attempted or approximated below.

module CSP.Examples.UCS.Ch3.Phils where

open import Relation.Nullary using (¬_)

open import Semantics.Deadlock using (DeadlockFree; hasDeadlock⇒¬deadlockFree)

open import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP
open Sys 0 using (SYSTEMsym; SYSTEMasym)
open DeadlockReachable using (dp-csp-deadlock-reachable)
open import CSP.Examples.DiningPhilosophers.DiningPhilosophersCSP_DeadlockFree
  using (deadlock-free-asym)

------------------------------------------------------------------------------------
-- §A.  assert 2 (`phils.csp:72`): `SYSTEMs :[deadlock free [F]]` — FALSE.
------------------------------------------------------------------------------------

-- The stripped symmetric ring, at N = 2: `SYSTEMsym` is the imported model's name
-- for the all-right-handed fold of `PHILs`/`FORK` components (stripped: see scope
-- limit 1), so it is Roscoe's `SYSTEMs` and not his `SYSTEM`.
SYSTEMs : _
SYSTEMs = SYSTEMsym

-- assert 2 REFUTED: `SYSTEMs` is not deadlock free.  `dp-csp-deadlock-reachable`
-- exhibits the wedge — both philosophers pick their own fork, then each waits for
-- its neighbour's — and `hasDeadlock⇒¬deadlockFree` turns that `HasDeadlock` witness
-- into the negation of the assertion FDR is asked to check.  Assert 1 has the same
-- truth value for the same reason, but is not stated here (see the refusal above).
phils-assert2-refuted : ¬ DeadlockFree SYSTEMs
phils-assert2-refuted = hasDeadlock⇒¬deadlockFree dp-csp-deadlock-reachable

------------------------------------------------------------------------------------
-- §B.  assert 5 (`phils.csp:115`): `ASSYSTEMs :[deadlock free [F]]` — TRUE.
------------------------------------------------------------------------------------

-- The stripped asymmetric ring, at N = 2: philosopher 0 reaches for fork 1 first
-- (left-handed, Roscoe's `LPHILs 0`), philosopher 1 for fork 1 first (right-handed,
-- `PHILs 1` — at N = 2 its own fork IS fork 1).  So this is Roscoe's `ASSYSTEMs`.
ASSYSTEMs : _
ASSYSTEMs = SYSTEMasym

-- assert 5 DISCHARGED: `ASSYSTEMs` is deadlock free.  This IS `deadlock-free-asym`;
-- the proof is a full case enumeration over the 400 reachable configurations of the
-- 4-component system, and is imported rather than restated.  Assert 4 has the same
-- truth value but a larger state space, and is not stated here (see the refusal).
phils-assert5 : DeadlockFree ASSYSTEMs
phils-assert5 = deadlock-free-asym

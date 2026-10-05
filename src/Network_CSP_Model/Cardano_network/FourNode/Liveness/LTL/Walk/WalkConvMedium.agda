{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- R3 — the MEDIUM-τ measure-decrease arithmetic (WalkConv item (b)).
--
-- A medium-τ of `radec r` is (by `SysOracle_TauCore.medium-τ-inv`) exactly one
-- copy cell of one link draining `draining x → empty`, reflected to the
-- successor `MedState`
--
--     mkMed (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀)) (broken m)
--
-- with `phase m i d₀ id₀ ≡ draining x` (the drained cell was `draining`).  The
-- measure `μτ = 3·nodesWt + medWt` (WalkConvMeasure) leaves `nodesWt` fixed on a
-- medium-τ (nodes unchanged), and the medium summand drops by exactly 2
-- (the flipped cell goes `cellWt (draining x) = 2 → cellWt empty = 0`).  This
-- module proves that `medWt` drop as a PURE combinatorial/arithmetic fact —
--
--     rowWt-flip : rowWt (flipCell g d₀ id₀) + 2 ≡ rowWt g   (one cell drained)
--     medWt-flip : medWt (phase-upd-successor) + 2 ≡ medWt m
--
-- feeding `WalkConvMeasure.μτ-med-dec` for the medium-τ branch of `τreflect`.
-- The 12 `rowWt-flip` cases (2 `Dir` × 6 `IDs`) and the 4 `medWt-flip` link
-- cases (`Link = Fin 4`) each reduce the concrete `flipCell`/`phase-upd`
-- `_≟_`-guards and close the residual ℕ identity with the commutative-semiring
-- solver.  LIGHT — only the data-level medium records + `SysOracle_TauCore`'s
-- `flipCell`/`phase-upd`.  No postulates, holes, or unsolved metas.
------------------------------------------------------------------------

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Data.Nat.Solver using (module +-*-Solver)
open +-*-Solver
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvMedium (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base
  using ( Dir; lo; hi; IDs
        ; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission
        ; N2N_KeepAlive; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.Net p using ( Link )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( MedState; mkMed; phase; broken; CopyPhase; empty; full; draining )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA
  using ( flipCell; phase-upd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvMeasure blkA
  using ( cellWt; rowWt; medWt )

------------------------------------------------------------------------
-- rowWt-flip — one cell of one link's phase-row drained `draining x → empty`
-- drops that row's `rowWt` by exactly 2.  The flipped cell is enumerated over
-- the 12 `(Dir, IDs)` keys; `flipCell`'s `_≟_`-guards reduce at each concrete
-- key, so the residual is a linear ℕ identity closed by the solver.
------------------------------------------------------------------------

rowWt-flip : (g : Dir → IDs → CopyPhase) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → g d₀ id₀ ≡ draining x
  → rowWt (flipCell g d₀ id₀) + 2 ≡ rowWt g
-- (lo, KeepAlive) — position 1
rowWt-flip g lo N2N_KeepAlive x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              con 0 :+ a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ con 2
           := con 2 :+ a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l) refl
    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
-- (hi, KeepAlive) — position 2
rowWt-flip g hi N2N_KeepAlive x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              a :+ con 0 :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ con 2
           := a :+ con 2 :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l) refl
    (cellWt (g lo N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
-- (lo, ChainSync) — position 3
rowWt-flip g lo N2N_ChainSync x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              a :+ b :+ con 0 :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ con 2
           := a :+ b :+ con 2 :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
-- (hi, ChainSync) — position 4
rowWt-flip g hi N2N_ChainSync x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              a :+ b :+ c :+ con 0 :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ con 2
           := a :+ b :+ c :+ con 2 :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
-- (lo, BlockFetch) — position 5
rowWt-flip g lo N2N_BlockFetch x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              a :+ b :+ c :+ d :+ con 0 :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ con 2
           := a :+ b :+ c :+ d :+ con 2 :+ e :+ f :+ h :+ i :+ j :+ k :+ l) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
-- (hi, BlockFetch) — position 6
rowWt-flip g hi N2N_BlockFetch x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              a :+ b :+ c :+ d :+ e :+ con 0 :+ f :+ h :+ i :+ j :+ k :+ l :+ con 2
           := a :+ b :+ c :+ d :+ e :+ con 2 :+ f :+ h :+ i :+ j :+ k :+ l) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
-- (lo, TxSubmission) — position 7
rowWt-flip g lo N2N_TxSubmission x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              a :+ b :+ c :+ d :+ e :+ f :+ con 0 :+ h :+ i :+ j :+ k :+ l :+ con 2
           := a :+ b :+ c :+ d :+ e :+ f :+ con 2 :+ h :+ i :+ j :+ k :+ l) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
-- (hi, TxSubmission) — position 8
rowWt-flip g hi N2N_TxSubmission x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              a :+ b :+ c :+ d :+ e :+ f :+ h :+ con 0 :+ i :+ j :+ k :+ l :+ con 2
           := a :+ b :+ c :+ d :+ e :+ f :+ h :+ con 2 :+ i :+ j :+ k :+ l) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
-- (lo, LeiosNotify) — position 9
rowWt-flip g lo N2N_LeiosNotify x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ con 0 :+ j :+ k :+ l :+ con 2
           := a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ con 2 :+ j :+ k :+ l) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
-- (hi, LeiosNotify) — position 10
rowWt-flip g hi N2N_LeiosNotify x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ con 0 :+ k :+ l :+ con 2
           := a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ con 2 :+ k :+ l) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))   (cellWt (g hi N2N_LeiosFetch))
-- (lo, LeiosFetch) — position 11
rowWt-flip g lo N2N_LeiosFetch x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ con 0 :+ l :+ con 2
           := a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ con 2 :+ l) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g hi N2N_LeiosFetch))
-- (hi, LeiosFetch) — position 12
rowWt-flip g hi N2N_LeiosFetch x eq rewrite eq =
  solve 11 (λ a b c d e f h i j k l →
              a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ con 0 :+ con 2
           := a :+ b :+ c :+ d :+ e :+ f :+ h :+ i :+ j :+ k :+ l :+ con 2) refl
    (cellWt (g lo N2N_KeepAlive))    (cellWt (g hi N2N_KeepAlive))
    (cellWt (g lo N2N_ChainSync))    (cellWt (g hi N2N_ChainSync))
    (cellWt (g lo N2N_BlockFetch))   (cellWt (g hi N2N_BlockFetch))
    (cellWt (g lo N2N_TxSubmission)) (cellWt (g hi N2N_TxSubmission))
    (cellWt (g lo N2N_LeiosNotify))  (cellWt (g hi N2N_LeiosNotify))
    (cellWt (g lo N2N_LeiosFetch))

------------------------------------------------------------------------
-- medWt-flip — the whole-medium drop.  `phase-upd` changes only link `i`'s row;
-- the four `Link = Fin 4` cases reduce `phase-upd`'s `_≟_`-guard concretely, and
-- `rowWt-flip` supplies the drained-row −2.  The residual link-sum rearrangement
-- is closed by the solver.
------------------------------------------------------------------------

medWt-flip : (m : MedState) (i : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → phase m i d₀ id₀ ≡ draining x
  → medWt (mkMed (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀)) (broken m)) + 2
     ≡ medWt m
medWt-flip m fzero d₀ id₀ x eq =
  trans (solve 4 (λ f r2 r3 r4 →
                    (((f :+ r2) :+ r3) :+ r4) :+ con 2
                 := (((f :+ con 2) :+ r2) :+ r3) :+ r4) refl
           (rowWt (flipCell (phase m linkAB) d₀ id₀))
           (rowWt (phase m linkAC)) (rowWt (phase m linkBD)) (rowWt (phase m linkCD)))
        (cong (λ z → ((z + rowWt (phase m linkAC)) + rowWt (phase m linkBD)) + rowWt (phase m linkCD))
              (rowWt-flip (phase m linkAB) d₀ id₀ x eq))
medWt-flip m (fsuc fzero) d₀ id₀ x eq =
  trans (solve 4 (λ r1 f r3 r4 →
                    (((r1 :+ f) :+ r3) :+ r4) :+ con 2
                 := (((r1 :+ (f :+ con 2)) :+ r3) :+ r4)) refl
           (rowWt (phase m linkAB))
           (rowWt (flipCell (phase m linkAC) d₀ id₀))
           (rowWt (phase m linkBD)) (rowWt (phase m linkCD)))
        (cong (λ z → ((rowWt (phase m linkAB) + z) + rowWt (phase m linkBD)) + rowWt (phase m linkCD))
              (rowWt-flip (phase m linkAC) d₀ id₀ x eq))
medWt-flip m (fsuc (fsuc fzero)) d₀ id₀ x eq =
  trans (solve 4 (λ r1 r2 f r4 →
                    (((r1 :+ r2) :+ f) :+ r4) :+ con 2
                 := (((r1 :+ r2) :+ (f :+ con 2)) :+ r4)) refl
           (rowWt (phase m linkAB)) (rowWt (phase m linkAC))
           (rowWt (flipCell (phase m linkBD) d₀ id₀))
           (rowWt (phase m linkCD)))
        (cong (λ z → ((rowWt (phase m linkAB) + rowWt (phase m linkAC)) + z) + rowWt (phase m linkCD))
              (rowWt-flip (phase m linkBD) d₀ id₀ x eq))
medWt-flip m (fsuc (fsuc (fsuc fzero))) d₀ id₀ x eq =
  trans (solve 4 (λ r1 r2 r3 f →
                    (((r1 :+ r2) :+ r3) :+ f) :+ con 2
                 := (((r1 :+ r2) :+ r3) :+ (f :+ con 2))) refl
           (rowWt (phase m linkAB)) (rowWt (phase m linkAC)) (rowWt (phase m linkBD))
           (rowWt (flipCell (phase m linkCD) d₀ id₀)))
        (cong (λ z → ((rowWt (phase m linkAB) + rowWt (phase m linkAC)) + rowWt (phase m linkBD)) + z)
              (rowWt-flip (phase m linkCD) d₀ id₀ x eq))

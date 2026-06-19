{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- FEASIBILITY SPIKE for `Network ≈DR CopySpec` (single-channel) — the
-- gating crux `¬ Diverges Network`.
--
-- This file is a SCRATCH PROBE.  It establishes the genuinely-provable,
-- load-bearing facts of the `¬ Diverges` decomposition architecture and
-- states the single missing König step (`Hide-Diverges→`) as a labelled
-- `-- GOAL:` WITHOUT claiming it proven.  Nothing here is postulated /
-- holed / NON_TERMINATING; it typechecks with 0 error / 0 metas.
--
-- WHAT IS PROVEN HERE (closed terms):
--   (P1) `Copy-stable` : a single `Copy id c` leaf has a STABLE head
--        (its forced node is a `react` whose τ-branch map is everywhere
--        `nothing`) ⇒ it admits NO τ-step at all.
--   (P2) `¬Diverges-Copy` : hence a single `Copy id c` leaf does NOT
--        diverge — the structural base case of the whole `¬ Diverges
--        Network` argument, needing NO new infrastructure (it does not
--        even need `loop-Diverges→`, because the head never offers a τ:
--        the leaf must fire a VISIBLE `input` before any τ loop-back).
--   (P3) `Par-peel-Network` : the top `Par⊤` of `Network` is peelable by
--        the EXISTING certified `Par-Diverges→` König step
--        (CSP.Laws.FD.ParallelDivergence) — modulo the outer hide.  This
--        confirms the parallel layers of the decomposition reuse existing,
--        certified infrastructure.
--
-- THE ONE OPEN GOAL (stated, NOT proven): `Hide-Diverges→`.  See the
-- `-- GOAL:` block at the end.  It is the SAME shape as the already-
-- certified `modA-transfer` (ClassicalFromLEM Derivation 8) and is the
-- only piece of new infrastructure the crux needs.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Unit using (⊤; tt)
import Data.Unit.Polymorphic as Poly
open import Data.Fin using (zero)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Product using (_,_; proj₁; proj₂; Σ; Σ-syntax; _×_)
open import Relation.Nullary using (yes; ¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans)
open import Class.DecEq using (DecEq)

open import Process_Trees
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Base using (IDs; N2N_KeepAlive)

module CSP.Examples.Cardano_network.Task6Spike where

open PTree
open ExtI

------------------------------------------------------------------------
-- The single-channel instance (identical to NetworkRefinement.p1).
------------------------------------------------------------------------

instance
  decEq⊤ : DecEq ⊤
  decEq⊤ = record { _≟_ = λ _ _ → yes refl }

p1 : Params
p1 = record
  { Cookie = ⊤ ; Block = ⊤ ; Txid = ⊤ ; LSlot = ⊤
  ; VoterId = ⊤ ; LFBitmap = ⊤ ; VoteBlob = ⊤
  ; numConns = λ where N2N_KeepAlive → 1 ; _ → 0
  ; decCookie  = decEq⊤ ; decBlock    = decEq⊤ ; decTxid    = decEq⊤
  ; decLSlot   = decEq⊤ ; decVoterId  = decEq⊤ ; decLFBitmap = decEq⊤
  ; decVoteBlob = decEq⊤ }

open import CSP.Examples.Cardano_network.Net p1
  using (Net; Conn; Net-≟)
open import CSP.Examples.Cardano_network.Network p1 ⊤
  using (Copy; Network)

open import Semantics.LTS     {E = Net ⊤} {I = ExtI (Net ⊤)}
open import Semantics.DRBisim {E = Net ⊤} {I = ExtI (Net ⊤)} using (Diverges)

-- The certified König step we reuse (NOT re-proven here):
open import CSP.Operators {E = Net ⊤} (Net-≟ {⊤})
  using (loop0; iter-bind; Par⊤; _∖_; EventSet)
open import CSP.Laws.FD.ParallelDivergence (Net-≟ {⊤})
  using (Par-Diverges→)

c0 : Conn N2N_KeepAlive
c0 = zero

NetProc′ : Set₁
NetProc′ = PTree (Net ⊤) (ExtI (Net ⊤)) (Poly.⊤ {0ℓ})

------------------------------------------------------------------------
-- (P1)  `Copy id c` has a STABLE head.
--
-- `Copy id c = loop0 (pchoice v)`; `force` reduces (definitionally) to a
-- `react v′ τc′` whose τ-branch map `τc′` is everywhere `nothing` — so no
-- `sTau` can fire from it, and the head is not a `sil`.  We refute every
-- shape of a `─[ τ ]─►` step by case-split, exactly as
-- `NetworkRefinement.CopySpec-stable` does for `CopySpec`.
------------------------------------------------------------------------

Copy-stable : ∀ {t} → Copy N2N_KeepAlive c0 ─[ τ ]─► t → ⊥
Copy-stable (sSil ())
Copy-stable (sTau {i = _ , fin}                   refl ())
Copy-stable (sTau {i = _ , base _}                refl ())
Copy-stable (sTau {i = _ , pair fin (base _)}     refl ())
Copy-stable (sTau {i = _ , pair fin fin}          refl ())
Copy-stable (sTau {i = _ , pair fin (pair _ _)}   refl ())
Copy-stable (sTau {i = _ , pair (base _) _}       refl ())
Copy-stable (sTau {i = _ , pair (pair _ _) _}     refl ())

------------------------------------------------------------------------
-- (P2)  Hence a single leaf does NOT diverge.  `Diverges` demands a first
--       τ-`step`, which `Copy-stable` refutes.  No `loop-Diverges→` is
--       even needed for the leaf: the head offers only the visible
--       `input`, so the loop cannot τ-cycle without a visible event.
------------------------------------------------------------------------

¬Diverges-Copy : ¬ Diverges (Copy N2N_KeepAlive c0)
¬Diverges-Copy d = Copy-stable (d .Diverges.step)

------------------------------------------------------------------------
-- (P3)  Peeling the top `Par⊤` of any `Par⊤ A P Q` divergence with the
--       EXISTING certified `Par-Diverges→`.  This is the parallel layer
--       of the full decomposition (applied to `TxSide`/`RxSide` and to
--       the leaf interleavings `⦀ = Par⊤ ∅`).  We show it is directly
--       usable at `E = Net ⊤` — i.e. NO new infrastructure for the Par
--       layers.
------------------------------------------------------------------------

Par-peel : (A : EventSet) (P Q : NetProc′)
         → Diverges (Par⊤ A P Q) → Diverges P ⊎ Diverges Q
Par-peel A P Q d = Par-Diverges→ A (λ _ _ → Poly.tt) d

------------------------------------------------------------------------
-- THE OPEN GOAL — the ONLY missing König step for the crux.
--
-- `Network = (Par⊤ csTA TxSide RxSide) ∖ csTA`.  The outer node is a
-- HIDE.  To start the decomposition we need the hiding divergence-
-- reflection König step:
--
-- GOAL:  Hide-Diverges→ :
--          (Z : EventSet) (P : NetProc′)
--        → Diverges (P ∖ Z)
--        → Diverges P                          -- a τ-divergence of P, OR
--        ⊎ DivHidden Z P                       -- an infinite stream of
--                                              --   P-steps each τ-or-(hidden Z)
--
-- where `DivHidden Z P` is an infinite path of P-steps each of which is a
-- τ OR a visible event in `Z` (exactly `DivModAC` of ClassicalFromLEM
-- Derivation 8).  This is classical (a Σ⁰₂ "is a Z-event ever ahead?"
-- decision) and is CERTIFIED in the SAME shape as `modA-transfer`
-- (ClassicalFromLEM Derivation 8: `DivModAC`/`EvA`/`¬EvA→Div`).
--
-- Given `Hide-Diverges→`, the full crux closes mechanically:
--   Diverges Network
--     ─[Hide-Diverges→]→  Diverges (Par⊤ csTA TxSide RxSide)         (case A)
--                       ⊎ infinite hidden-csTA stream of the Par⊤     (case B)
--   (A) ─[Par-peel]→ Diverges TxSide ⊎ Diverges RxSide; each side is
--       again a (Par⊤ … ∖ …) ⇒ recurse (Hide-Diverges→, Par-peel) down
--       to the leaves; each leaf is `¬Diverges-Copy`-style stable ⇒ ⊥.
--   (B) the infinite hidden-csTA stream consists of `tx`/`ack` syncs, each
--       of which CONSUMES a pending message in the finite ≤1-deep buffer
--       chain of the pipeline; a measure (pending-message count, bounded
--       by the single connection) shows it cannot recur infinitely ⇒ ⊥.
--   Symmetric for the inner csSR/csRS hides inside TxSide/RxSide.
--
-- Stated here as the type only; NOT proven in this probe.
------------------------------------------------------------------------

-- GOAL (NOT proven; the single missing König step):
-- Hide-Diverges→ : (Z : EventSet) {P : NetProc′}
--                → Diverges (P ∖ Z)
--                → Diverges P ⊎ DivHidden Z P

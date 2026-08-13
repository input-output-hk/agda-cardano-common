{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Cardano network example — THE N-NODE ⊑FD ASSEMBLY LEMMA.
--
-- This is the N-ary, topology-generic counterpart of the FIRST HALF of the
-- hard-coded 5-ary `liveness-FD-from-components` of
-- `FourNode/Liveness/CSP_Refinement/Spec.lagda.md` — NOT a drop-in
-- replacement for the whole lemma.  `liveness-FD-from-components` covers
-- TWO hide layers (`∖ ioES` then `∖ hidden b`), TWO divergence-freedom
-- hypotheses (one per hide level), and wraps the result with `⊑FD-trans`
-- against a residual goal about the still-unhidden abstract composite.
-- `systemN-mono` below reproduces only the node fold, the medium
-- composition, and the FIRST hide (`∖ ioES`): ONE obligation per node plus
-- one for the medium plus one divergence-freedom hypothesis, over an
-- arbitrary `Topology`.  A caller reaching the four-node lemma's full
-- conclusion still has to apply `Hide-mono-⊑FD-df (hidden b) … hDiv2` and
-- `⊑FD-trans` on top of `systemN-mono` themselves:
--
--   * `⦀Fin⁺-mono-⊑FD` folds the nodes with NO alphabet side condition
--     — that is the whole reason this campaign assembles at `⊑FD`
--     rather than at `≈DR`, whose replicated congruence needs pairwise
--     alphabet disjointness (refuted for nodes, which share link
--     alphabets with their neighbours);
--   * `∥-mono-⊑FD` composes the node fold with the medium on `ioES`;
--   * `Hide-mono-⊑FD-df` discharges the `∖ ioES` — the UNCONDITIONAL
--     `⊑FD` hiding law is false (counterexample in
--     `CSP/Laws/FD/HideMonoFD.agda`'s header), so the conditional one
--     is the only route and it demands divergence-freedom of the
--     implementation's hide.
--
-- WHY THE DIVERGENCE PREMISE IS EXPLICIT.  The decision record
-- `docs/superpowers/decisions/2026-08-12-hide-vs-fairness.md` (outcome
-- (B)) established that hiding `ioES` cannot create an infinite τ-run
-- — every peer cycle passes through an `apiKA`/`done` event, which
-- `ioES` does not hide — so the properties may stay on the HIDDEN
-- system and no fairness side condition is needed.  But that spike
-- rules out divergence only at the ROOT state, whereas
-- `Hide-mono-⊑FD-df` asks for `∀ {s} → ¬ divergences (Q ∖ A) s`, which
-- via `IsDivergence` quantifies over every `⟹⟨ prefix ⟩`-reachable
-- state.  Closing that gap needs a reachability-closed `ModAccᴿ` plus a
-- `Hide-trace-elim` prefix walk (§5.4 of the record) — genuinely extra,
-- unbuilt work.  It is therefore carried as an explicit HYPOTHESIS
-- rather than postulated away: the obligation stays visible in the
-- type where a later campaign can discharge it.
--
-- The file has two parts: the generic module `Generic`, parametric in
-- `Params`/`Topology`/`apiES` exactly like `Parametric.Node`, and a
-- concrete instantiation at the four-node diamond (§ below) that
-- checks the lemma is actually usable.  The file module is therefore
-- NOT parameterised — the diamond section needs the diamond's own
-- concrete `p`, which an outer parameter would shadow.
------------------------------------------------------------------------

module CSP.Examples.Cardano_network.Parametric.Assembly where

open import Data.Fin using (Fin)
open import Relation.Nullary using (¬_)

open import Process_Trees using (ExtI)
open import CSP.Examples.Cardano_network.Params using (Params)
open import CSP.Examples.Cardano_network.Parametric.Topology using (Topology)
import CSP.Examples.Cardano_network.Net as N
import CSP.Examples.Cardano_network.Data as D
import CSP.Operators as O

------------------------------------------------------------------------
-- The generic layer
------------------------------------------------------------------------

-- the assembly lemma, parametric in the network parameters, the topology and the
-- api alphabet — the same three parameters `Parametric.Node` takes, so that `node`
-- and `systemOf` below are literally that module's
module Generic
  (p : Params) (t : Topology p)
  (apiES : O.EventSet (N.Net_Api-≟ p {D.Payload p})) where

  open N p using (Net_Api; Net_Api-≟)
  open D p using (Payload)
  open import CSP.Examples.Cardano_network.NetCommon p
    using (CopySpecBreakableA; ioES)
  open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_∥⇘_⇙_; _∖_; ⦀Fin⁺)
  open Topology t using (Node; numNodes-1)
  open import CSP.Examples.Cardano_network.Parametric.Node p t apiES
    using (Proc; node; systemOf)

  open import Semantics.FailuresDivergences
    {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
    using (_⊑FD_; divergences)
  open import CSP.Laws.FD.ParallelMonoFD (Net_Api-≟ {Payload})
    using (∥-mono-⊑FD; ⦀Fin⁺-mono-⊑FD)
  open import CSP.Laws.FD.HideMonoFD (Net_Api-≟ {Payload})
    using (Hide-mono-⊑FD-df)

  -- THE ASSEMBLY LEMMA: a whole-network `⊑FD` goal reduces to one obligation per
  -- node (`nSpec n ⊑FD node n (lg n)`) plus one for the medium, given
  -- divergence-freedom of the hidden implementation.  `⦀Fin⁺-mono-⊑FD` folds the
  -- nodes with no alphabet side condition, `∥-mono-⊑FD` joins the medium at `ioES`,
  -- `Hide-mono-⊑FD-df` pushes the whole thing under `∖ ioES`.
  systemN-mono : (mSpec : Proc) (nSpec lg : Node → Proc)
               → mSpec ⊑FD CopySpecBreakableA
               → (∀ n → nSpec n ⊑FD node n (lg n))
               → (∀ {s} → ¬ divergences (systemOf lg) s)
               → ((mSpec ∥⇘ ioES ⇙ ⦀Fin⁺ numNodes-1 nSpec) ∖ ioES) ⊑FD systemOf lg
  systemN-mono mSpec nSpec lg hM hN hdf =
    Hide-mono-⊑FD-df ioES (∥-mono-⊑FD ioES hM (⦀Fin⁺-mono-⊑FD hN)) hdf

------------------------------------------------------------------------
-- Sanity check: the lemma instantiated at the four-node diamond
--
-- This is a USABILITY check, not a new theorem — it exhibits exactly
-- what a caller has to supply.  Note that the conclusion is stated
-- about the HAND-WRITTEN `systemBroken`, not about `systemOf
-- (diamondLogic blkA)`: the two are definitionally equal by
-- `Parametric.DiamondInstance.diamond-faithful` (`= refl`), so the
-- generic lemma applies to the existing four-node development with no
-- transport at all.
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using (p; Block₃; apiES)
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBroken
  using (systemBroken)
open import CSP.Examples.Cardano_network.Parametric.DiamondInstance
  using (diamond; diamondLogic)
open N p using (Net_Api; Net_Api-≟)
open D p using (Payload)
open import CSP.Examples.Cardano_network.NetCommon p
  using (CopySpecBreakableA; ioES)
open O {E = Net_Api Payload} (Net_Api-≟ {Payload}) using (_∥⇘_⇙_; _∖_; ⦀Fin⁺)
open import CSP.Examples.Cardano_network.Parametric.Node p diamond apiES
  using (Proc; node)
open import Semantics.FailuresDivergences
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using (_⊑FD_; divergences)

-- the diamond instantiation of `systemN-mono`: FOUR node obligations (one per
-- `Fin 4`), one medium obligation and one divergence-freedom obligation give the
-- whole four-node network refinement.  The generic lemma is applied verbatim; the
-- conclusion mentions `systemBroken` only because the faithfulness gate is `refl`.
diamond-assembly : ∀ (blkA : Block₃) (mSpec : Proc) (nSpec : Fin 4 → Proc)
                 → mSpec ⊑FD CopySpecBreakableA
                 → (∀ n → nSpec n ⊑FD node n (diamondLogic blkA n))
                 → (∀ {s} → ¬ divergences (systemBroken blkA) s)
                 → ((mSpec ∥⇘ ioES ⇙ ⦀Fin⁺ 3 nSpec) ∖ ioES) ⊑FD systemBroken blkA
diamond-assembly blkA mSpec nSpec hM hN hdf =
  Generic.systemN-mono p diamond apiES mSpec nSpec (diamondLogic blkA) hM hN hdf

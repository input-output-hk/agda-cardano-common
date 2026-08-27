{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 — S1: PROVENANCE AT NODE D (`Praos.ProvenanceD`).
--
-- *** THIS IS A SAFETY RESULT, NOT A LIVENESS ONE. ***  It sits under
-- `…/Liveness/LTL/` only because it reuses that campaign's machinery verbatim
-- (the τ-reduced `abstractSystem`, the per-leg block-VALUE invariant `PipeVal`
-- and its walk fold, and the banked `≈DR` transport).  Liveness says a block
-- EVENTUALLY reaches D; THIS says every block D ever receives IS the block A
-- produced — nothing in the diamond fabricates or corrupts a block.
--
--   provD blkA fr = arrivedD⁻ fr → arrivedD blkA fr   (an IMPLICATION between
--     the two shipped `Spec` atoms, so it is vacuously true off-trigger — the
--     polarity a `□ᵗ` body needs)
--   Provenance⁺ = ∀ blkA tr → □ᵗ (atom (provD blkA)) tr
--
-- ROUTE: (1) `PipeValWalk.pipeVal-fold` at `φ := arrivedD⁻` walks `PipeVal`
-- from `rinit` straight to the delivering frame, then `PipeValArrive.arrUpgrade`
-- reads the delivered value off the leg's client clause (at `b := blkA` its
-- `b ≡ blkA` argument is `refl`, so no `producedA` anchor and no descent);
-- (2) `BisimStable` — `provD` is an implication, so the antecedent travels
-- BACKWARDS via `FrameSim-sym`; (3) the postulate-free PER-POSITION transport
-- (`transportᴿ`/`drop-WTraceSim`/`⟦⟧ᵂ-transport`/`drop-sem-fwd`/`⟦G⟧⁺⇒□ᵗ`),
-- which never goes through `⟦ G φ ⟧` and so never spends `⟦G⟧⇒⟦G⟧⁺`.
--
-- PREMISE-FREE (no assumption record, no module parameter).  0 postulate/hole/
-- meta added; ONE classical AXIOM (`Classical.dne`), with exactly ONE USE-SITE on
-- this endpoint's term path — `Walk.TProg`'s `em`, which the liveness spine
-- already spends.  (`Walk.Walk`'s `getProd` and `conf⊎` are two further `dne`
-- use-sites sitting in the closure, but they feed only `abstractLive`, which this
-- endpoint never traverses.)
--
-- SCOPE — antecedent reachability is NOT closed here.  `provD` is an IMPLICATION,
-- so it is vacuously true at any frame that is not a D-delivery, and nothing in
-- the repo proves such a frame is ever REACHABLE on a trace of `breakableSystem
-- blkA`: no `Trace`/`WTrace` VALUE over `breakableSystem` exists anywhere in the
-- tree.  The missing artefact is one of those, or a lemma of shape
-- `∃ tr n → arrivedD⁻ (frameOf (drop n tr))`.  `FourNodeDiamondBreakable`
-- (§"Reading the witness — and a documented limitation") records why none is
-- given: one composed step costs ≈2.5 min and ≈20 GB, so only an isolated-link
-- witness is supplied.  The gap is INHERITED from the liveness endpoint, not
-- introduced here — `BlockLiveness⁺At` likewise TAKES its trace, its confinement
-- disjunct and a `producedA` frame as hypotheses rather than producing them, so
-- closing non-vacuity from liveness would be circular.  It is strictly SMALLER
-- for provenance: `provenance⁺` needs no confinement hypothesis, so it holds even
-- when BOTH routes are broken.  This is a scope boundary, NOT a defect in the
-- proof — nothing discharges by refuting the antecedent (the value chain is
-- positive throughout), and the checks in (5) below show `provD b1` is REFUTABLE
-- on a wrong-payload frame and SATISFIABLE on a right-payload one.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤ )
open import Data.Nat using ( ℕ )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( inj₁ )
open import Data.Empty using ( ⊥ )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; subst )

open import Process_Trees using ( PTree; ExtI )

module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.ProvenanceD where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( p; Block₃; b1; b2; linkBD )
open import CSP.Examples.Cardano_network.Base using ( hi )
open import CSP.Examples.Cardano_network.Net p
  using ( Net_Api; apiBF; recvBFBlock )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( evl; evLabel )
open import Semantics.LTL.Traces_Based
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Frame; FramePred; LTLᵗ; atom; Trace; □ᵗ; ⟦G⟧⁺⇒□ᵗ )
open import Semantics.LTL.WTrace
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTrace; frameOf; drop; dropIdx )
open import Semantics.LTL.FrameSim
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( FrameSim; FrameSim-sym; BisimStable; bs-atom )
open import Semantics.LTL.Convergence
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( ↠-refl )
open import Semantics.LTL.WBisimInvariant
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( WTraceSim-sym; drop-WTraceSim; ⟦⟧ᵂ-transport )
open import Semantics.LTL.WBisimInvariantR
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( transportᴿ )
open import Semantics.LTL.TraceBridge
  {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( Trace↪WTrace; drop-sem-fwd )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamondBreakable
  using ( breakableSystem )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Spec
  using ( arrivedD; arrivedD⁻; mkVis )

-- the `blkA`-parameterised machinery, imported UNAPPLIED so the ∀-closure over
-- `blkA` can live in this very module
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach as SR
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.AbstractSystem as ABS
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim as SB
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr as WPR
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.RealAbs as RA
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.TProg as TP
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv as PVI
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValEvStep as PVE
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValWalk as PVW
import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValArrive as PVA

------------------------------------------------------------------------
-- (1) THE SAFETY ATOM AND THE STATEMENT.
------------------------------------------------------------------------

-- at any D-delivery frame the carried block IS `blkA`; off-trigger both sides
-- are `⊥`, so the atom holds vacuously (the polarity a `□ᵗ` body needs)
provD : Block₃ → FramePred 0ℓ (⊤ {0ℓ})
provD blkA fr = arrivedD⁻ fr → arrivedD blkA fr

-- provenance at a FIXED produced block: the atom holds at every suffix
Provenance⁺At : Block₃ → Set _
Provenance⁺At blkA = ∀ (tr : Trace (⊤ {0ℓ}) (breakableSystem blkA))
                   → □ᵗ (atom (provD blkA)) tr

-- provenance at an arbitrary produced block: the ∀-closure of `Provenance⁺At`
Provenance⁺ : Set _
Provenance⁺ = ∀ (blkA : Block₃) → Provenance⁺At blkA

------------------------------------------------------------------------
-- (2) BISIM-STABILITY.  Both `Spec` atoms read only the frame's EVENT, so a
-- `FrameSim` (which forces the events equal) moves each by `refl`; because
-- `provD` is an IMPLICATION the antecedent must go the other way, which is the
-- one step that differs from the shipped `arrivedD-BS` template.
------------------------------------------------------------------------

-- `arrivedD⁻` travels along a `FrameSim` (every other frame shape is `⊥`)
arr⁻-stab : ∀ {fr₁ fr₂ : Frame (⊤ {0ℓ})} → FrameSim fr₁ fr₂ → arrivedD⁻ fr₁ → arrivedD⁻ fr₂
arr⁻-stab {Frame.step _ (evl (evLabel _ (apiBF l d recvBFBlock) a))}
          {Frame.step _ _} (refl , _) q = q

-- `arrivedD b` likewise (the shipped `arrivedD-BS` witness)
arr-stab : (b : Block₃) {fr₁ fr₂ : Frame (⊤ {0ℓ})}
         → FrameSim fr₁ fr₂ → arrivedD b fr₁ → arrivedD b fr₂
arr-stab b {Frame.step _ (evl (evLabel _ (apiBF l d recvBFBlock) a))}
            {Frame.step _ _} (refl , _) q = q

-- `provD b` is bisim-stable: push the antecedent BACK with `FrameSim-sym`
provD-BS : (b : Block₃) → BisimStable (atom (provD b))
provD-BS b = bs-atom (λ sim h ar → arr-stab b sim (h (arr⁻-stab (FrameSim-sym sim) ar)))

------------------------------------------------------------------------
-- (3) THE PER-`blkA` PROOF.
------------------------------------------------------------------------

module At (blkA : Block₃) where

  open SR  blkA using ( RState; radec; toSys; rinit; rinit-toSys; radec-init )
  open ABS blkA using ( abstractSystem )
  open SB  blkA using ( sysBisim )
  open WPR blkA using ( TwoLegs; legBD; legCD )
  open RA  blkA using ( realAbs )
  open TP  blkA using ( tprog )
  open PVI blkA using ( PipeVal; pipeVal-init )
  open PVE blkA using ( stepEmitVᶠ )
  open PVW blkA using ( pipeVal-fold )
  open PVA blkA using ( term-no-arr; arrUpgrade )

  -- the leg's block-value invariant folded from `rinit` STRAIGHT to a delivering
  -- frame — the generic fold at `φ := arrivedD⁻`, with no `producedA` anchor
  pipeVal-to-arr : (l : TwoLegs) (tr : WTrace (⊤ {0ℓ}) abstractSystem) (k : ℕ)
                 → arrivedD⁻ (frameOf (drop k tr))
                 → Σ[ r′ ∈ RState ] (dropIdx k tr ≡ radec r′) × PipeVal l (toSys r′)
  pipeVal-to-arr l tr k ar =
    pipeVal-fold l arrivedD⁻ term-no-arr (stepEmitVᶠ l) rinit (sym radec-init)
      (subst (PipeVal l) (sym rinit-toSys) (pipeVal-init l)) tr k ar

  -- ABSTRACT SIDE: on `abstractSystem`, every delivering frame carries `blkA`
  provAbs : (tr : WTrace (⊤ {0ℓ}) abstractSystem) (k : ℕ)
          → provD blkA (frameOf (drop k tr))
  provAbs tr k ar =
    let (rBD , eqBD , pvBD) = pipeVal-to-arr legBD tr k ar
        (rCD , eqCD , pvCD) = pipeVal-to-arr legCD tr k ar
    in  arrUpgrade blkA refl rBD rCD (drop k tr) eqBD eqCD pvBD pvCD ar

  -- CONCRETE SIDE: transport position-by-position along the banked bisimulation
  -- (never through `⟦ G φ ⟧`, so the postulated `⟦G⟧⇒⟦G⟧⁺` is never spent)
  provenance⁺At : Provenance⁺At blkA
  provenance⁺At tr with transportᴿ (realAbs tprog) ↠-refl sysBisim (Trace↪WTrace tr)
  ... | wabs , sim = ⟦G⟧⁺⇒□ᵗ
        (λ n → drop-sem-fwd (atom (provD blkA)) n tr
                 (⟦⟧ᵂ-transport (provD-BS blkA)
                    (WTraceSim-sym (drop-WTraceSim n sim))
                    (provAbs wabs n)))

------------------------------------------------------------------------
-- (4) THE ∀-CLOSURE — S1 HEADLINE, UNCONDITIONAL.
------------------------------------------------------------------------

-- S1: every block node D receives is the block node A produced, for ANY block
-- A may be configured to produce
provenance⁺ : Provenance⁺
provenance⁺ blkA = At.provenance⁺At blkA

------------------------------------------------------------------------
-- (5) NON-VACUITY, in the `Spec` atom-sanity idiom: `provD` is neither
-- trivially satisfiable nor trivially false.
------------------------------------------------------------------------

-- a D-delivery carrying the WRONG block REFUTES `provD b1` (so the theorem
-- says something: the walk must rule such a frame out, it cannot excuse it)
_ : provD b1 (mkVis (apiBF linkBD hi recvBFBlock) b2) → ⊥
_ = λ h → wrong (h (inj₁ refl , refl))
  where
    wrong : arrivedD b1 (mkVis (apiBF linkBD hi recvBFBlock) b2) → ⊥
    wrong (_ , _ , ())

-- and it DOES hold on a D-delivery carrying the right block
_ : provD b1 (mkVis (apiBF linkBD hi recvBFBlock) b1)
_ = λ _ → inj₁ refl , refl , refl

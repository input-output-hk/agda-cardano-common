{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Phase-2 Task 3 — `LiveLegStep`, the PER-STEP PRESERVATION engine for the
-- positive token-location invariant `LiveLegInv.LegInv`.
--
-- WHAT THIS MODULE IS.  `LegInv` (Task 1) says WHERE the block is; this module
-- says that a single step of the reachable system MOVES it rather than losing
-- it.  Concretely it re-mirrors the green R3 per-step engine
-- (`LTL/Value/PipeTauIo.agda`, `PipeEvStep.agda`, assembled by
-- `PipeInvProd.agda`) at the STRENGTHENED invariant: same medium inversions,
-- same node cones, same io bridges, same impossible-class refutations, but each
-- clause rebuilds a `LegPos` instead of transporting an implication.
--
-- PROVENANCE.  This module is the PROMOTION of the Task-2 measurement spike
-- `LiveLegStepSpike.agda` (615 lines, green at commit cd5e050, kept in git
-- history).  The spike is REMOVED from the tree rather than kept beside this
-- module for two reasons: (i) the (C1)/(C2) corrections the spike itself forced
-- have now landed in `LiveLegInv`, so the spike's own cell clauses no longer
-- typecheck as written; (ii) the gate verdict's concern (6) — "if Task 3 imports
-- `Fold` from a module named …Spike it acquires reviewer obligations" —
-- recommends hoisting its §1/§2/§7 here instead of importing them.  Nothing is
-- lost: §1 (the three combinator types), §2 (the invariant-generic folds), §3-§6
-- (the io-fill arm) and §7 (the medium-drain leaves) are all below, adapted.
--
-- THE STRUCTURAL FINDING THIS MODULE IS ORGANISED AROUND (gate verdict §4).
-- `PipeInvS` is ∀-SHAPED: a product of per-slot IMPLICATIONS, each vacuously
-- true when its slot is empty, so every clause transports independently and no
-- clause ever has to know WHERE the token is.  `LegInv` is Σ-SHAPED: it NAMES
-- the occupied slot.  Rebuilding it after a step therefore needs, at every step
-- that EMPTIES the occupied slot, a POSITIVE hand-over fact — "the token is now
-- in the NEXT slot" — and the green io cone supplies none: its
-- `PipeNodeIoEvo.SrvIoCls` is `(fixed) ⊎ (successor NOT holding)`, which is
-- exactly enough to discharge an implication and exactly not enough to rebuild
-- an occupancy.  Seven of the nine hops' positive facts are nevertheless BANKED
-- (`BfsSucc`'s right arm, `CliBlkVal`, `ldCons`'s anchors, `ldRelay`'s
-- session-45 conjunct); the two that are not are stated here as MODULE PREMISES
-- (`SrvInCls⁺`, `CliInKeep`) in the `PipeInvProd` style — no postulate, and no
-- premise added to any chain module.
--
-- CONTENTS
--   §1  the three per-step combinator types at `LegInv`
--   §2  the τ-run fold and the fine-step fold, generic in the invariant
--   §3  the io-side leaf classifiers — DISCHARGED by `LiveLegIoCone`'s ⁺ cone
--   §4  clause-level helpers
--   §5  `fillMove` — the ten-position dispatch across a hidden io INPUT
--   §6  `legInv-fill` — the io-SYNC INPUT (cell FILL) arm
--   §7  the medium-drain leaves that (C1) makes the medium-τ arm a transport
--   §8  `legFrame` (the position-PRESERVING dispatch) and `legInv-drain`,
--       the MEDIUM-τ arm — a pure transport, which is what (C1) bought
--   §9  the io-SYNC OUTPUT (cell READ) arm — the second MOVING arm, which (C1)
--       created; its ONE remaining premise is `cellCp3`
--  §10  the VISIBLE arm at STATE level: `legStep→legInv`, the `LegInv` mirror of
--       `PipeEvStep.legStep→pres`.  Exactly ONE leaf record is a premise here,
--       `NoTwoTokens` (four pairwise token exclusions); `VisLeaves` (FOUR
--       hand-over fields, leaves 6, 7 and 9) is IMPORTED from `LiveLegApiExpose`,
--       which PROVES it (`:492`, re-derived at T3b's fix round; the old `:1276` was out
--       of range and had been wrong since before the split).  Hop 4 and leaf 8 are
--       DERIVED from `ldRelay`.
--
-- *** THE RESIDUAL PREMISE SET (session-54; read this before adding any) ***
-- ALL NINE of the eleven leaf facts that are STEP facts are now discharged:
-- leaves 1-4 through `LiveLegIoCone`'s ⁺ io cone, hop 4 through the widened
-- `ldRelay`, leaf 8 as `PipeValRelay.cpStepKindL-of⁺`'s seventh component, and
-- leaves 6, 7 and 9 through `LiveLegApiExpose`'s ⁺ VISIBLE cone (`driverExpose⁺`
-- proves the `VisLeaves` imported above for every api step).  EXACTLY TWO
-- premises are left, and both are per-state REACHABILITY facts:
--
--   (a) `cellCp3` (leaf 5), §9's `module _` parameter — a leg whose own cell
--       still holds the UNREAD token has its reader's driver at exactly the
--       pre-`recvBFBlock` phase.  (C2)'s bill.  *** IT IS A THEOREM SINCE THE
--       CELLCP3 WINDOW (`LiveChanJoin.cellCp3-of`, off the carried join), so the
--       ROUTE no longer assumes it; this module's `legInv-read` keeps the parameter
--       because its only consumer is `LiveTokenExcl`'s parked bridge. ***
--   (b) `NoTwoTokens` (leaf 11), a parameter of `legStep→legInv` — four pairwise
--       token exclusions at the SOURCE state.  W2's bill.
--
-- These are the exactly-two PER-STATE facts one future `TokenExcl` component
-- discharges; by owner decision #4 they stay premises for this campaign,
-- deliberately, and must not be "discharged" by weakening them.
--
-- DEFERRED TO TASK 6 (the assembly), on purpose and not for lack of budget:
-- the `RState` wrappers of the two state-level arms — `τpreserveS-med`'s twin for
-- `legInv-drain` (it needs the heavy `WalkConvTauInv` layer, which the
-- cheap-prefix rule keeps out of this module) and the `stepEmitL`/`RState`
-- wiring of `legStep→legInv` into `EvStepL` through §2's folds.
--
-- STYLE (campaign-verified, each with an incident behind it).  `let`, never
-- `with`, in anything whose type mentions the imported `LegInv`/`AtPos` (the
-- `blkA`-parameter hazard: a `with` abstracts the block out of the imported
-- module application and the goal stops converting, printing `x != x` rather
-- than an error — `PipeValStep.agda:27-31`, `PipeInvProd.agda:188-190`).  Every
-- ⊎ is consumed by a pattern-matching HELPER instead.
--
-- Cheap-prefix discipline: no `Walk*` and no `Sys{Bisim,Oracle,IoLink}*` import
-- here; the heavy facts arrive as module premises.  (NB this is a DIRECT-import
-- check only — the module still sits in the heavy closure via `LiveLegInv` →
-- `PipeInv` → `WalkPr`.)  No postulate, no hole, no `mutual`.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Class.DecEq using ( DecEq; _≟_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegStep
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( Block )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link; input; output )
open import CSP.Examples.Cardano_network.Data p using ( Payload )
open import CSP.Examples.Cardano_network.Base using ( Dir; hi; IDs; N2N_BlockFetch )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel; Event )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[τ*]─►_; τ*-refl; τ*-step; _═[_]═►_; wev )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; mkSys; med; nA; nB; nC; nD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; empty; full; draining; MedState; mkMed; phase; broken; decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absNodesOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; mkR; radec; toSys; reach; Reachable )
open Reachable using ( rStepʷ )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( phase-upd; flipCell; ≟-yes-refl )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( setCell )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using ( BFcPos; BFsPos; bsBlk1; bcBlk1
              ; CPPh; consuming; producing
              ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
              ; ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD; phOf; InCp03; cblkOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf; relayOf; cellUp; cellDn; upClient; dnClient
        ; ProdSent; ProdNotSent; RelayPre; RelayHas; RelayFwd; ConsRecv
        ; CellHasBlk; BFcHasBlk
        ; prodSent-notSent-⊥; relayPre-has-⊥; relayPre-fwd-⊥; inCp03-recv-⊥ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( upSrv; dnSrv; padv-sent-mono; rk-fwd-mono )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( relayBlk )
-- slice C (leaf 8): the relay's recorded-block PREDICATE and its two bridges to
-- the accessor form `AtPos`'s `RelayIn⁺`/`RelayOut⁺` are stated with
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValRelay blkA
  using ( RelayAt; relayAt⇒eq; eq⇒relayAt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkMeasure blkA
  using ( ProdAdv; ConsAdv; c34 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkDAnchor blkA
  using ( ConsHeld )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriver blkA
  using ( ProdStepKind; pMove; pSend; prodadv-step
        ; RelayStepKind; rMove; rFwd; rRecv
        ; ConsStepKind; cMove; cRecv; consadv-step )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvDriverCone blkA
  using ( LegDriverStep; ldProd; ldRelay; ldCons; ldFix; LegValStep; lvCons )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeMedKey blkA
  using ( medium-ev-in-key; medium-ev-out-key; setRead )
-- slice E: the io cone at the two PREDECESSOR-directed slot families (leaves 1,
-- 2 and 3), an instance of `PipeNodeIoEvo`'s granted `IoFacts` generalisation
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegIoCone blkA
  using ( CliInKeep; CliRead⁺; CliIoCls⁺; SrvIoCls⁺; SrvWroteBlk; top-nodes-io-evo⁺ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauMed blkA
  using ( drainSucc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauIo blkA
  using ( legProd; legRelay; legCons; cellUp-key; cellDn-key; atKey; io-sync-wrun )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( blkPayload )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA
  using ( LegPos; lpPreSend; lpUpSrv; lpUpCell; lpUpClient; lpRelayIn; lpRelayOut
        ; lpDnSrv; lpDnCell; lpDnClient; lpDone
        ; AtPos; LegInv; RelayIn; RelayOut
        ; relayIn⇒has; relayOut⇒has; relayPre-in-⊥; relayPre-out-⊥
        ; CellFullBlk; cellFull⇒hasBlk; RelayCp3; relayCp3⇒pre; ConsCp3
        -- the §1c PINNED occupancy predicates + the forgetful maps
        ; SrvHas⁺; CliHas⁺; CellFull⁺; RelayIn⁺; RelayOut⁺
        ; srvHas⁺⇒hasBlk; cliHas⁺⇒hasBlk; cellFull⁺⇒fullBlk )

------------------------------------------------------------------------
-- §1  THE THREE PER-STEP COMBINATOR TYPES, AT `LegInv`.
--
-- Copied structurally from `PipeInvProd.agda:128-143` with `PipeInvS := LegInv`
-- (re-verified against that file, not against a table).  A mismatch between what
-- the folds want and what `LegInv` provides would be a type error HERE.
------------------------------------------------------------------------

-- one hidden τ hop preserves the token-location invariant
TauStepL : TwoLegs → Set₁
TauStepL l = (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
           → Σ[ r′ ∈ RState ]
               (M ≡ radec r′) × (LegInv l (toSys r) → LegInv l (toSys r′))

-- one strong visible hop preserves the token-location invariant
EvStepL : TwoLegs → Set₁
EvStepL l = (r : RState) {e : Event} {M : NetProc} → radec r ─[ ev (evl e) ]─► M
          → Σ[ r′ ∈ RState ]
              (M ≡ radec r′) × (LegInv l (toSys r) → LegInv l (toSys r′))

-- one WEAK visible move preserves the token-location invariant
StepEmitL : TwoLegs → Set₁
StepEmitL l = (r : RState) {e : Event} {t′ : NetProc} → radec r ═[ ev (evl e) ]═► t′
            → Σ[ r′ ∈ RState ]
                (t′ ≡ radec r′) × (LegInv l (toSys r) → LegInv l (toSys r′))

------------------------------------------------------------------------
-- §2  THE FOLDS, GENERIC IN THE INVARIANT.
--
-- CORRECTION TO THE TASK BRIEF, established by the Task-2 spike.  The brief said
-- the existing fold engines "apply unchanged — they are generic in the payload".
-- They are NOT: both `PipeStepEmit.liftτ*-preserve′`/`stepEmitFrom`
-- (`PipeStepEmit.agda:137`, `:149`) and `PipeInvProd.liftτ*S′`/`stepEmitFromS`
-- (`:248`, `:259`) MENTION their invariant (`PipeInv⁺` / `PipeInvS`) in their
-- types, and the completed `PipeVal` precedent did not reuse them — it COPIED
-- them (`PipeValStep.agda:210-233`).
--
-- That is a citation error, not a route failure: the folds carry NO invariant
-- content, so they GENERALISE, which is what this section does once and for all.
-- `Inv` is an arbitrary state predicate; these are the last copies anyone needs
-- to write.  NUANCE: `Fold` subsumes `PipeInvProd.stepEmitFromS` exactly, but NOT
-- `PipeStepEmit.stepEmitFrom`, whose last act is `psWeak (…)`
-- (`PipeStepEmit.agda:157`) — that wrapper is `PipeInv⁺`-specific by
-- construction and nothing at `LegInv` wants it.
------------------------------------------------------------------------

module Fold (Inv : TwoLegs → SysState → Set) (l : TwoLegs) where

  -- one hidden τ hop preserves `Inv` (the generic `TauStep`)
  TauStepG : Set₁
  TauStepG = (r : RState) {M : NetProc} → radec r ─[ τ ]─► M
           → Σ[ r′ ∈ RState ]
               (M ≡ radec r′) × (Inv l (toSys r) → Inv l (toSys r′))

  -- one strong visible hop preserves `Inv` (the generic `EvStep`)
  EvStepG : Set₁
  EvStepG = (r : RState) {e : Event} {M : NetProc} → radec r ─[ ev (evl e) ]─► M
          → Σ[ r′ ∈ RState ]
              (M ≡ radec r′) × (Inv l (toSys r) → Inv l (toSys r′))

  -- one weak visible move preserves `Inv` (the generic `StepEmit`)
  StepEmitG : Set₁
  StepEmitG = (r : RState) {e : Event} {t′ : NetProc} → radec r ═[ ev (evl e) ]═► t′
            → Σ[ r′ ∈ RState ]
                (t′ ≡ radec r′) × (Inv l (toSys r) → Inv l (toSys r′))

  -- fold `TauStepG` across a hidden τ-run, threading the composed preservation
  -- (generalised over the start tree with a `start ≡ radec r` witness so the
  -- `Star` sub-term recurses structurally — `PipeStepEmit.agda:137` verbatim
  -- except that the invariant is now a parameter)
  liftτ*G′ : TauStepG → (r : RState) {start u : NetProc}
           → start ≡ radec r → start ─[τ*]─► u
           → Σ[ r′ ∈ RState ]
               (u ≡ radec r′) × (Inv l (toSys r) → Inv l (toSys r′))
  liftτ*G′ ts r eq τ*-refl = r , eq , (λ x → x)
  liftτ*G′ ts r eq (τ*-step s rest)
    with ts r (subst (λ z → z ─[ τ ]─► _) eq s)
  ... | r₁ , eq₁ , p₁ with liftτ*G′ ts r₁ eq₁ rest
  ...   | r′ , equ , p′ = r′ , equ , (λ x → p′ (p₁ x))

  -- the fine-step fold: decompose `wev pre mid post`, fold the two τ-runs,
  -- dispatch the visible middle, compose the three preservation maps
  stepEmitFromG : TauStepG → EvStepG → StepEmitG
  stepEmitFromG ts es r (wev pre mid post)
    with liftτ*G′ ts r refl pre
  ... | r₁ , eq₁ , p₁
      with es r₁ (subst (λ z → z ─[ ev (evl _) ]─► _) eq₁ mid)
  ...   | r₂ , eq₂ , p₂
        with liftτ*G′ ts r₂ refl (subst (λ z → z ─[τ*]─► _) eq₂ post)
  ...     | r′ , equ , p₃ = r′ , equ , (λ x → p₃ (p₂ (p₁ x)))

-- the generic fold instantiated at `LegInv` has EXACTLY §1's three types (they
-- are definitionally the same `Σ`), so the engine is usable at the strengthened
-- invariant with no rework at all
stepEmitL : (l : TwoLegs) → TauStepL l → EvStepL l → StepEmitL l
stepEmitL l = Fold.stepEmitFromG LegInv l

------------------------------------------------------------------------
-- §3  THE NEW LEAF OBLIGATIONS — the two POSITIVE facts the green cone lacks.
--
-- `PipeNodeIoEvo.SrvIoCls bfs bfs′ = (bfs ≡ bfs′) ⊎ (BFsHasBlk bfs′ → ⊥)`.
-- Both arms are fine for an implication-shaped clause; for an OCCUPANCY the
-- second arm is a dead end — it says the token left the slot and nothing about
-- where it went.  `SrvInCls⁺` is the same classifier with that arm replaced by
-- the producer-site answer: the slot HELD block `b`, and THIS io is that
-- server's own wire WRITE of exactly `b` at its own key.  From it the fill arm
-- rebuilds the successor cell's occupancy with the green `setRead`.
--
-- WHY IT IS DISCHARGEABLE, AND CHEAPLY: `PipeSrvIoDec.decBFs-sendBF-succ` at the
-- `bsBlk1 b` row (`:226-237`) already performs all three decisions (`l′ ≟ l`,
-- `d′ ≟ d`, `a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))`)
-- and refutes every mismatch via `nothing-absurd`; it simply returns `(λ ())`
-- instead of the positive witness.  The payload equality `x ≡ blkPayload b` is
-- therefore available AT NO EXTRA COST — which is the evidence behind the
-- decision to let the payload pin ride along.
------------------------------------------------------------------------

-- SLICE E: the PRODUCER-SITE classifier is now `LiveLegIoCone.SrvIoCls⁺` at an
-- `input` label, i.e. what the ⁺ cone actually delivers, and it has THREE arms
-- rather than two.  *** THE TWO-ARM FORM WAS FALSE *** — a tracked server also
-- writes from `bsStart1`/`bsNoBlk1`/`bsBatchDone1`, where it is neither fixed nor
-- holding (`PipeSrvIoDec.decBFs-sendBF-succ:202/:214/:238`); the middle arm
-- `(BFsHasBlk bfs → ⊥)` is what makes the leaf TRUE, and `srvHop-in` refutes it
-- in one line from the position's own occupancy.  Definitionally equal to the
-- cone's own family, so `pickSrvUp⁺`/`pickSrvDn⁺` project it unchanged.
SrvInCls⁺ : (k : Link) (bfs bfs′ : BFsPos)
            (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) → Set
SrvInCls⁺ k bfs bfs′ l₀ d₀ id₀ x = SrvIoCls⁺ k hi bfs bfs′ (input l₀ d₀ id₀) x

-- the four `PipeSrvInv`-tracked servers' ⁺ classifiers, in `AllSrvIoCls`'s own
-- component order (`PipeNodeIoEvo.agda:457-462`) so the selectors below match
-- `PipeTauIo.pickSrv{Up,Dn}` line for line
AllSrvIn⁺ : (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) → Set
AllSrvIn⁺ s s′ l₀ d₀ id₀ x =
    SrvInCls⁺ (upLink legBD) (upSrv legBD s) (upSrv legBD s′) l₀ d₀ id₀ x
  × SrvInCls⁺ (upLink legCD) (upSrv legCD s) (upSrv legCD s′) l₀ d₀ id₀ x
  × SrvInCls⁺ (dnLink legBD) (dnSrv legBD s) (dnSrv legBD s′) l₀ d₀ id₀ x
  × SrvInCls⁺ (dnLink legCD) (dnSrv legCD s) (dnSrv legCD s′) l₀ d₀ id₀ x

-- the leg's UPSTREAM server ⁺ classifier out of the four
pickSrvUp⁺ : (l : TwoLegs) (s s′ : SysState)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
           → AllSrvIn⁺ s s′ l₀ d₀ id₀ x
           → SrvInCls⁺ (upLink l) (upSrv l s) (upSrv l s′) l₀ d₀ id₀ x
pickSrvUp⁺ legBD s s′ l₀ d₀ id₀ x (q , _ , _ , _) = q
pickSrvUp⁺ legCD s s′ l₀ d₀ id₀ x (_ , q , _ , _) = q

-- the leg's DOWNSTREAM server ⁺ classifier out of the four
pickSrvDn⁺ : (l : TwoLegs) (s s′ : SysState)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
           → AllSrvIn⁺ s s′ l₀ d₀ id₀ x
           → SrvInCls⁺ (dnLink l) (dnSrv l s) (dnSrv l s′) l₀ d₀ id₀ x
pickSrvDn⁺ legBD s s′ l₀ d₀ id₀ x (_ , _ , q , _) = q
pickSrvDn⁺ legCD s s′ l₀ d₀ id₀ x (_ , _ , _ , q) = q

-- THE SECOND new leaf, and it is the CHEAP kind: a BF client that HOLDS a block
-- is io-fixed on an INPUT (`bcBlk1`'s only outgoing row is the api
-- `recvBFBlock`, so a client cannot write to the wire while holding).  Stated in
-- the PREDECESSOR-negative form, which is what a `PipeCliIoDec` re-mirror
-- delivers by pattern-matching alone — `PipeNodeIoEvo.CliIoCls`'s existing
-- ¬-holding arm is at the SUCCESSOR and so cannot transport an occupancy.
-- (SLICE E: the predicate itself now lives in `LiveLegIoCone`, where the ⁺ cone
-- instantiates it; only the four-slot family and its two projections stay here.)

-- the four tracked clients' ⁺ facts, in `AllCliFacts`'s component order
-- (`PipeNodeIoEvo`'s §7 `AllCliFacts`, re-derived).  SESSION-53: each component
-- is now a PAIR — the keep (leaves 2, 3) and the READER IDENTIFICATION (leaf 4),
-- which the ownership layer of `PipeNodeIoEvo`'s §1b now supplies at every fixed
-- slot.  The label and its payload are EXPLICIT arguments of every selector,
-- because the read-hit reduces to `⊤` off an `output` and so erases them.
AllCli⁺ : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set
AllCli⁺ s s′ e a =
    CliIoCls⁺ (upLink legBD) hi (upClient legBD s) (upClient legBD s′) e a
  × CliIoCls⁺ (upLink legCD) hi (upClient legCD s) (upClient legCD s′) e a
  × CliIoCls⁺ (dnLink legBD) hi (dnClient legBD s) (dnClient legBD s′) e a
  × CliIoCls⁺ (dnLink legCD) hi (dnClient legCD s) (dnClient legCD s′) e a

-- the leg's UPSTREAM client keep-fact
pickCliUp⁺ : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ}
             (e : Net_Api Payload X) (a : X)
           → AllCli⁺ s s′ e a → CliInKeep (upClient l s) (upClient l s′)
pickCliUp⁺ legBD s s′ e a (q , _ , _ , _) = proj₁ q
pickCliUp⁺ legCD s s′ e a (_ , q , _ , _) = proj₁ q

-- the leg's DOWNSTREAM client keep-fact
pickCliDn⁺ : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ}
             (e : Net_Api Payload X) (a : X)
           → AllCli⁺ s s′ e a → CliInKeep (dnClient l s) (dnClient l s′)
pickCliDn⁺ legBD s s′ e a (_ , _ , q , _) = proj₁ q
pickCliDn⁺ legCD s s′ e a (_ , _ , _ , q) = proj₁ q

-- the leg's UPSTREAM client READ-HIT (leaf 4, discharged)
pickCliUpH : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ}
             (e : Net_Api Payload X) (a : X)
           → AllCli⁺ s s′ e a → CliRead⁺ (upLink l) hi (upClient l s′) e a
pickCliUpH legBD s s′ e a (q , _ , _ , _) = proj₂ q
pickCliUpH legCD s s′ e a (_ , q , _ , _) = proj₂ q

-- the leg's DOWNSTREAM client READ-HIT (leaf 4, discharged)
pickCliDnH : (l : TwoLegs) (s s′ : SysState) {X : Set 0ℓ}
             (e : Net_Api Payload X) (a : X)
           → AllCli⁺ s s′ e a → CliRead⁺ (dnLink l) hi (dnClient l s′) e a
pickCliDnH legBD s s′ e a (_ , _ , q , _) = proj₂ q
pickCliDnH legCD s s′ e a (_ , _ , _ , q) = proj₂ q

------------------------------------------------------------------------
-- §4  THE CLAUSE-LEVEL HELPERS.  Each consumes one ⊎ by PATTERN MATCHING (never
-- a `with` at a goal mentioning `AtPos`), so the arms themselves stay `let`-only.
------------------------------------------------------------------------

-- THE FIRED KEY'S CELL IS `full x` IN THE SUCCESSOR.
--
-- MEASUREMENT NOTE (one Task-2 build cycle spent here — kept because it is the
-- shape difference in miniature).  `PipeMedKey.setRead` CANNOT prove this: its
-- two arms are not mutually exclusive to the type checker, so at the matched key
-- its untouched arm is an unrefutable dead branch.  Every existing consumer
-- (`PipeTauIo.cellClause-in`, `PipeValTauIo.cellValIn`) is safe from that
-- because it lets `setRead` DECIDE and only ever CONSUMES the successor cell's
-- occupancy; an occupancy rebuild must PRODUCE it, and then the hit has to be
-- computed, not received.  The fix is the `≟`-reflexivity reduction already
-- banked as `SysOracle_TauCore.≟-yes-refl` (`:475`).
setHit-in : (g : Link → Dir → IDs → CopyPhase)
            (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
          → phase-upd g l₀ (setCell (g l₀) d₀ id₀ (full x)) l₀ d₀ id₀ ≡ full x
setHit-in g l₀ d₀ id₀ x
  rewrite ≟-yes-refl l₀ | ≟-yes-refl d₀ | ≟-yes-refl id₀ = refl

-- the leg's own cell IS `full x` once the fired key matches it (pure transport
-- on top of `setHit-in`, so the ARM needs no `with` and no `refl` pattern)
cellFill-eq : (g : Link → Dir → IDs → CopyPhase)
    (k : Link) (kd : Dir) (ki : IDs) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
    {cu′ : CopyPhase}
  → cu′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (full x)) k kd ki
  → k ≡ l₀ → kd ≡ d₀ → ki ≡ id₀ → cu′ ≡ full x
cellFill-eq g k kd ki l₀ d₀ id₀ x c′eq refl refl refl =
  trans c′eq (setHit-in g l₀ d₀ id₀ x)

-- a cell that HOLDS AN UNREAD block is UNTOUCHED by an INPUT io: the fired key's
-- source cell is `empty`, so a `full` cell can never be the fired one.
--
-- (C1) note: the property transported must be FALSE at `empty` — that is the
-- only thing the refutation arm needs.  (W1) note: it is stated GENERICALLY in
-- that property rather than at `CellFullBlk`, because the payload pin
-- transports `CellFull⁺ b` (a bare equality) rather than the unpinned
-- predicate, and both are `empty`-false.  Same single `subst`, new index.
cellKeep-in : (P : CopyPhase → Set) → (P empty → ⊥)
  → (g : Link → Dir → IDs → CopyPhase)
    (k : Link) (kd : Dir) (ki : IDs) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
    {cu cu′ : CopyPhase}
  → cu  ≡ g k kd ki
  → cu′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (full x)) k kd ki
  → g l₀ d₀ id₀ ≡ empty
  → P cu → P cu′
cellKeep-in P ¬e g k kd ki l₀ d₀ id₀ x ceq c′eq se h
  with setRead g l₀ d₀ id₀ (full x) k kd ki
... | inj₁ eq =
      subst P (trans ceq (trans eq (sym c′eq))) h
... | inj₂ (e1 , e2 , e3 , _) =
      ⊥-elim (¬e (subst P (trans ceq (atKey g e1 e2 e3 se)) h))

-- a HOLDING client is carried across by its keep-fact, WITH its block
cliKeep : {b : Block₃} {bfc bfc′ : BFcPos}
        → CliInKeep bfc bfc′ → CliHas⁺ b bfc → CliHas⁺ b bfc′
cliKeep (inj₁ refl) h = h
cliKeep {b} {bfc} (inj₂ ¬h) h = ⊥-elim (¬h (cliHas⁺⇒hasBlk b bfc h))

-- `bsBlk1` is a `BFsPos` CONSTRUCTOR, hence injective: this is what lets the
-- server hop identify the classifier's existential block with the position's
bsBlk1-inj : {b b′ : Block₃} → bsBlk1 b ≡ bsBlk1 b′ → b ≡ b′
bsBlk1-inj refl = refl

-- THE HOP, at the server slot: the ⁺ classifier's two arms are exactly the two
-- possible successor positions — the server still holds (`lpUpSrv` kept), or it
-- wrote the block to its own cell (`lpUpSrv → lpUpCell`, the position MOVES).
-- The `full x` payload fact comes off the classifier's own `x ≡ blkPayload b`,
-- and `CellFullBlk (full (blkPayload b))` reduces to `⊤` because `blkPayload b`
-- IS a `blockFetch (MsgBlock b)` wire tuple.
-- (W1) note: BOTH answers are now PINNED to the position's own block `b`.  The
-- `inj₂` arm is where the pin is EARNED rather than transported: the classifier
-- names its OWN block `b′` and its own payload equality `x ≡ blkPayload b′`, and
-- `bsBlk1`'s injectivity identifies `b′` with `b`.  No new leaf: the equality
-- was already in `SrvInCls⁺`, which is exactly the gate verdict's evidence for
-- letting the pin ride along.
srvHop-in : (k : Link) (b : Block₃) {bfs bfs′ : BFsPos} {cu′ : CopyPhase}
            (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
          → SrvInCls⁺ k bfs bfs′ l₀ d₀ id₀ x
          → ((k ≡ l₀) → (hi ≡ d₀) → (N2N_BlockFetch ≡ id₀) → cu′ ≡ full x)
          → SrvHas⁺ b bfs → SrvHas⁺ b bfs′ ⊎ CellFull⁺ b cu′
srvHop-in k b l₀ d₀ id₀ x (inj₁ eq) cellEq h = inj₁ (trans (sym eq) h)
-- SLICE E's new middle arm: the server was not holding, which the position's own
-- occupancy refutes outright
srvHop-in k b {bfs} l₀ d₀ id₀ x (inj₂ (inj₁ ¬h)) cellEq h =
  ⊥-elim (¬h (srvHas⁺⇒hasBlk b bfs h))
srvHop-in k b l₀ d₀ id₀ x (inj₂ (inj₂ (b′ , hb′ , e1 , e2 , e3 , refl))) cellEq h =
  inj₂ (trans (cellEq e1 e2 e3)
              (cong (λ z → full (blkPayload z))
                    (sym (bsBlk1-inj (trans (sym h) hb′)))))

-- read the up-hop answer as a POSITION: still in the server, or now in the cell
atUpHop : (l : TwoLegs) (b : Block₃) (s′ : SysState)
        → SrvHas⁺ b (upSrv l s′) ⊎ CellFull⁺ b (cellUp l s′)
        → ProdSent (prodOf l s′) → RelayPre (relayOf l s′) → InCp03 (phOf l s′)
        → LegInv l s′
atUpHop l b s′ (inj₁ hb) hp hr hc = b , lpUpSrv  , hb , hp , hr , hc
atUpHop l b s′ (inj₂ hb) hp hr hc = b , lpUpCell , hb , hp , hr , hc

-- read the down-hop answer as a POSITION
atDnHop : (l : TwoLegs) (b : Block₃) (s′ : SysState)
        → SrvHas⁺ b (dnSrv l s′) ⊎ CellFull⁺ b (cellDn l s′)
        → ProdSent (prodOf l s′) → RelayFwd (relayOf l s′) → InCp03 (phOf l s′)
        → LegInv l s′
atDnHop l b s′ (inj₁ hb) hp hr hc = b , lpDnSrv  , hb , hp , hr , hc
atDnHop l b s′ (inj₂ hb) hp hr hc = b , lpDnCell , hb , hp , hr , hc

-- the leg's node-D RECORDED-BLOCK fixity out of the cone's two node-D fixities
-- (the `cblkOf` twin of `PipeTauIo.legCons`; `lpDone`'s pin reads `cblkOf`, so
-- every position-preserving arm needs this tenth transport)
legCblk : (l : TwoLegs) {s s′ : SysState}
        → SN.NodeStateD.cons-BD (nD s) ≡ SN.NodeStateD.cons-BD (nD s′)
        → SN.NodeStateD.cons-CD (nD s) ≡ SN.NodeStateD.cons-CD (nD s′)
        → cblkOf l s ≡ cblkOf l s′
legCblk legBD dbd dcd = cong SN.cblk dbd
legCblk legCD dbd dcd = cong SN.cblk dcd

------------------------------------------------------------------------
-- §5  THE POSITION DISPATCH — ten clauses, one per `LegPos`.
--
-- This is the shape difference from `PipeTauIo` in one screen.  There the io arm
-- discharged FOUR implications; here TEN positions must be rebuilt.  Eight of
-- them TRANSPORT (the three drivers are io-fixed, an unread cell is untouched, a
-- holding client is io-frozen); the two SERVER positions are the genuine HOPS
-- and are the only ones that consume the new leaf.
------------------------------------------------------------------------

-- rebuild the token's position across a hidden io INPUT, CARRYING ITS BLOCK
-- (`b` is the SAME on both sides of every clause — that is what makes the pin
-- propagate along the hop chain by construction)
fillMove : (l : TwoLegs) (b : Block₃) (s s′ : SysState)
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
  → prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′ → phOf l s ≡ phOf l s′
  → cblkOf l s ≡ cblkOf l s′
  → (CellFull⁺ b (cellUp l s) → CellFull⁺ b (cellUp l s′))
  → (CellFull⁺ b (cellDn l s) → CellFull⁺ b (cellDn l s′))
  → SrvInCls⁺ (upLink l) (upSrv l s) (upSrv l s′) l₀ d₀ id₀ x
  → SrvInCls⁺ (dnLink l) (dnSrv l s) (dnSrv l s′) l₀ d₀ id₀ x
  → ((upLink l ≡ l₀) → (hi ≡ d₀) → (N2N_BlockFetch ≡ id₀) → cellUp l s′ ≡ full x)
  → ((dnLink l ≡ l₀) → (hi ≡ d₀) → (N2N_BlockFetch ≡ id₀) → cellDn l s′ ≡ full x)
  → CliInKeep (upClient l s) (upClient l s′)
  → CliInKeep (dnClient l s) (dnClient l s′)
  → (k : LegPos) → AtPos l k b s → LegInv l s′
fillMove l b s s′ l₀ d₀ id₀ x pe re ce be cuK cdK sU sD fU fD kU kD
  lpPreSend (hA , hn , hr , hc) =
    b , lpPreSend , hA
      , subst ProdNotSent pe hn , subst RelayPre re hr , subst InCp03 ce hc
fillMove l b s s′ l₀ d₀ id₀ x pe re ce be cuK cdK sU sD fU fD kU kD
  lpUpSrv (hb , hp , hr , hc) =
    atUpHop l b s′ (srvHop-in (upLink l) b l₀ d₀ id₀ x sU fU hb)
      (subst ProdSent pe hp) (subst RelayPre re hr) (subst InCp03 ce hc)
fillMove l b s s′ l₀ d₀ id₀ x pe re ce be cuK cdK sU sD fU fD kU kD
  lpUpCell (hb , hp , hr , hc) =
    b , lpUpCell , cuK hb
      , subst ProdSent pe hp , subst RelayPre re hr , subst InCp03 ce hc
fillMove l b s s′ l₀ d₀ id₀ x pe re ce be cuK cdK sU sD fU fD kU kD
  lpUpClient (hb , hp , hr , hc) =
    b , lpUpClient , cliKeep kU hb
      , subst ProdSent pe hp , subst RelayCp3 re hr , subst InCp03 ce hc
fillMove l b s s′ l₀ d₀ id₀ x pe re ce be cuK cdK sU sD fU fD kU kD
  lpRelayIn (hIn , hp , hc) =
    b , lpRelayIn , subst (RelayIn⁺ b) re hIn
      , subst ProdSent pe hp , subst InCp03 ce hc
fillMove l b s s′ l₀ d₀ id₀ x pe re ce be cuK cdK sU sD fU fD kU kD
  lpRelayOut (hOut , hp , hc) =
    b , lpRelayOut , subst (RelayOut⁺ b) re hOut
      , subst ProdSent pe hp , subst InCp03 ce hc
fillMove l b s s′ l₀ d₀ id₀ x pe re ce be cuK cdK sU sD fU fD kU kD
  lpDnSrv (hb , hp , hr , hc) =
    atDnHop l b s′ (srvHop-in (dnLink l) b l₀ d₀ id₀ x sD fD hb)
      (subst ProdSent pe hp) (subst RelayFwd re hr) (subst InCp03 ce hc)
fillMove l b s s′ l₀ d₀ id₀ x pe re ce be cuK cdK sU sD fU fD kU kD
  lpDnCell (hb , hp , hr , hc) =
    b , lpDnCell , cdK hb
      , subst ProdSent pe hp , subst RelayFwd re hr , subst InCp03 ce hc
fillMove l b s s′ l₀ d₀ id₀ x pe re ce be cuK cdK sU sD fU fD kU kD
  lpDnClient (hb , hp , hr , hc) =
    b , lpDnClient , cliKeep kD hb
      , subst ProdSent pe hp , subst RelayFwd re hr , subst ConsCp3 ce hc
fillMove l b s s′ l₀ d₀ id₀ x pe re ce be cuK cdK sU sD fU fD kU kD
  lpDone (hcb , hp , hr , hd) =
    b , lpDone , trans (sym be) hcb
      , subst ProdSent pe hp , subst RelayFwd re hr , subst ConsRecv ce hd

------------------------------------------------------------------------
-- §6  THE io-SYNC INPUT (CELL FILL) ARM.  The `let` skeleton is
-- `PipeTauIo.tauIo-in`'s (`PipeTauIo.agda:362-411`) VERBATIM down to the binder
-- names: the medium inversion, `m′`, the node cone, `s′ = mkSys m′ (nA s″) …`,
-- `r′` via `io-sync-wrun`, and the three driver fixities off
-- `legProd`/`legRelay`/`legCons`.  Only the `pres` field changes — from four
-- implication transports to one position rebuild.
--
-- LESSON, banked at the selector call below: the cone's successor `s″` must be
-- re-typed at the arm's own `s′`, exactly as `PipeTauIo.agda:399`/`:407` does.
------------------------------------------------------------------------

-- SLICE E: BOTH PREMISES OF THIS ARM ARE NOW DISCHARGED (leaves 1 and 2).
-- The ⁺ cone `LiveLegIoCone.top-nodes-io-evo⁺` reports `AllSrvIn⁺` and
-- `AllCliIn⁺` itself, so the arm is premise-free and the anonymous module
-- wrapper is gone; the two selector calls read the cone's own two families.

-- ONE hidden io-SYNC FILL, at `LegInv`: the INPUT arm of `TauStepL`.  The
-- position `lpUpSrv → lpUpCell` (and its downstream twin) is where the token
-- genuinely MOVES; the other eight positions transport.
legInv-fill : (l : TwoLegs) (r : RState)
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
  → ioES .mem (Payload , input l₀ d₀ id₀) x
  → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► M₁
  → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► N₁
  → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (LegInv l (toSys r) → LegInv l (toSys r′))
legInv-fill l r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
  let (srcEmpty , M₁≡) = medium-ev-in-key (med (toSys r)) l₀ d₀ id₀ x sM
      g : Link → Dir → IDs → CopyPhase
      g = phase (med (toSys r))
      m′ : MedState
      m′ = mkMed (phase-upd g l₀ (setCell (g l₀) d₀ id₀ (full x)))
                 (broken (med (toSys r)))
      cone = top-nodes-io-evo⁺ (toSys r) {Payload} {input l₀ d₀ id₀} {x} {N₁} iomem sN
      s″ : SysState
      s″ = proj₁ cone
      (_ , medEq , N₁≡ , cWeakRun , allCli , allSrv
         , epAB , epAC , ecB , ecC , edBD , edCD) = cone
      s′ : SysState
      s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
      r′ : RState
      r′ = mkR s′ (rStepʷ (reach r) (io-sync-wrun r m′ s″ iomem sM M₁≡ cWeakRun))
      pe : prodOf l (toSys r) ≡ prodOf l s′
      pe = legProd l epAB epAC
      re : relayOf l (toSys r) ≡ relayOf l s′
      re = legRelay l ecB ecC
      ce : phOf l (toSys r) ≡ phOf l s′
      ce = legCons l edBD edCD
      be : cblkOf l (toSys r) ≡ cblkOf l s′
      be = legCblk l edBD edCD
      -- the leg's own cell is `full x` once the fired key matches it
      fU : (upLink l ≡ l₀) → (hi ≡ d₀) → (N2N_BlockFetch ≡ id₀)
         → cellUp l s′ ≡ full x
      fU = cellFill-eq g (upLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
             (cellUp-key l s′)
      fD : (dnLink l ≡ l₀) → (hi ≡ d₀) → (N2N_BlockFetch ≡ id₀)
         → cellDn l s′ ≡ full x
      fD = cellFill-eq g (dnLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
             (cellDn-key l s′)
      -- an UNREAD cell is untouched by the fill (its source would be `empty`);
      -- at the PINNED predicate the `empty`-falsity is a bare `λ ()`
      cuK : (b : Block₃) → CellFull⁺ b (cellUp l (toSys r)) → CellFull⁺ b (cellUp l s′)
      cuK b = cellKeep-in (CellFull⁺ b) (λ ()) g (upLink l) hi N2N_BlockFetch
                l₀ d₀ id₀ x (cellUp-key l (toSys r)) (cellUp-key l s′) srcEmpty
      cdK : (b : Block₃) → CellFull⁺ b (cellDn l (toSys r)) → CellFull⁺ b (cellDn l s′)
      cdK b = cellKeep-in (CellFull⁺ b) (λ ()) g (dnLink l) hi N2N_BlockFetch
                l₀ d₀ id₀ x (cellDn-key l (toSys r)) (cellDn-key l s′) srcEmpty
      pres : LegInv l (toSys r) → LegInv l s′
      pres = λ li →
        let (b , k , at) = li
        in  fillMove l b (toSys r) s′ l₀ d₀ id₀ x pe re ce be (cuK b) (cdK b)
              (pickSrvUp⁺ l (toSys r) s′ l₀ d₀ id₀ x allSrv)
              (pickSrvDn⁺ l (toSys r) s′ l₀ d₀ id₀ x allSrv)
              fU fD
              (pickCliUp⁺ l (toSys r) s′ (input l₀ d₀ id₀) x allCli)
              (pickCliDn⁺ l (toSys r) s′ (input l₀ d₀ id₀) x allCli)
              k at
  in  r′ , trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡) , pres

------------------------------------------------------------------------
-- §7  THE MEDIUM-DRAIN LEAVES that (C1) buys.
--
-- Under Task 1's original `CellHasBlk` the medium-drain τ at the token's own
-- cell turned `draining x` into `empty` and DESTROYED the position, so `LegInv`
-- was not preserved by the medium τ at all.  Under `CellFullBlk` the drained
-- key's source phase is `draining x` (`WalkConvTauInv.medium-τ-inv-wt` reports
-- exactly that) and `CellFullBlk (draining _)` is `⊥`, so a token-bearing cell
-- can never be the drained one and the medium-τ arm becomes a PURE TRANSPORT.
-- These are the two leaves that make it so.
------------------------------------------------------------------------

-- `PipeTauMed.cell-drain-eq` STRENGTHENED to report ALL THREE key equalities on
-- the hit.  The banked version reports only `kl ≡ i` — enough to keep two
-- distinct links apart (its only present consumer), one equality short of
-- identifying the drained cell's SOURCE phase, which is what an occupancy needs.
-- Body is that lemma's own `_≟_` dispatch, verbatim.
cell-drain-eq⁺ : (m : MedState) (i : Link) (d₀ : Dir) (id₀ : IDs)
                 (kl : Link) (kd : Dir) (kid : IDs)
  → (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀) kl kd kid ≡ phase m kl kd kid)
    ⊎ ((kl ≡ i) × (kd ≡ d₀) × (kid ≡ id₀)
       × (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀) kl kd kid ≡ empty))
cell-drain-eq⁺ m i d₀ id₀ kl kd kid with kl ≟ i
... | no  _ = inj₁ refl
... | yes refl with kd ≟ d₀ | kid ≟ id₀
...   | yes refl | yes refl = inj₂ (refl , refl , refl , refl)
...   | no  _    | _        = inj₁ refl
...   | yes refl | no  _    = inj₁ refl

-- A `full` CELL SURVIVES EVERY MEDIUM DRAIN: the drained key's source phase is
-- `draining x` and a `full`-only cell predicate is `⊥` there, so a token-bearing
-- cell can never be the drained one.  THIS is the clause that makes the medium-τ
-- arm a pure transport at the tightened invariant — and its absence at
-- `CellHasBlk` is why Task 1's original statement could not be preserved.
--
-- (W1) note: stated GENERICALLY in the transported predicate, for the same
-- reason `cellKeep-in` is — the pin transports `CellFull⁺ b`, a bare equality,
-- whose `draining`-falsity is `λ ()`.  The only thing the refutation arm needs
-- is that the predicate fails at the drained key's SOURCE phase.
cellDrainKeep : (m : MedState) (i : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
    (kl : Link) (kd : Dir) (kid : IDs)
    (P : CopyPhase → Set) → (P (draining x) → ⊥)
  → phase m i d₀ id₀ ≡ draining x
  → P (phase m kl kd kid)
  → P (phase-upd (phase m) i (flipCell (phase m i) d₀ id₀) kl kd kid)
cellDrainKeep m i d₀ id₀ x kl kd kid P ¬d dr h
  with cell-drain-eq⁺ m i d₀ id₀ kl kd kid
... | inj₁ eq                       = subst P (sym eq) h
... | inj₂ (refl , refl , refl , _) = ⊥-elim (¬d (subst P dr h))

------------------------------------------------------------------------
-- §8  `legFrame` — THE POSITION-PRESERVING DISPATCH, and the MEDIUM-τ ARM.
--
-- `legFrame` is `fillMove` with the two server HOPS removed: it rebuilds the
-- SAME position, AT THE SAME BLOCK, out of TEN per-component transports.  Every
-- arm whose step moves no token needs exactly this, so it is written once here
-- and reused — the medium-τ arm below, and (in the visible axis) the `ldFix` and
-- `ldProd` classes, whose `LegDriverStep` constructors hand over seven of the
-- nine COMPONENT equalities outright (`ldProd` at
-- `PipeEvDriverCone.agda:606-612`, `ldFix` at `:648-653`; both were re-derived
-- at the point of use, the brief's `LTL/Walk/` path for that module is wrong —
-- it lives in `LTL/Value/`).
--
-- (W1) note: the TENTH transport is `cblkOf l s ≡ cblkOf l s′`, which the pinned
-- `lpDone` clause reads.  The visible axis supplies it from
-- `LegValStep.lvCons` (`PipeEvDriverCone.agda:676`) on the classes that fix node
-- D, and from `ldCons`'s SESSION-40 anchor (`:633-640`) on the hop itself; the
-- io axis gets it from `legCblk` off the cone's two node-D fixities.
--
-- It is stated in TRANSPORT form (`P s → P s′`) rather than with equalities so
-- that the two cell slots, which under a drain are NOT equal, can still use it.
------------------------------------------------------------------------

-- rebuild the token's position unchanged, AT THE SAME BLOCK, out of the TEN
-- component transports (the tenth is `cblkOf`, which `lpDone`'s pin reads)
-- (§10 note) the `cblkOf` transport is GATED on `ConsRecv (phOf l s)`, which is
-- `lpDone`'s own conjunct and the only clause that reads it.  The unconditional
-- form is the instance `λ _ → eq`; the gated one is what the VISIBLE axis can
-- supply, since `LegValStep.lvCons` reports the recorded block fixed only past
-- the receive (`PipeEvDriverCone.agda:676`).
legFrame : (l : TwoLegs) (b : Block₃) (s s′ : SysState)
  → prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′ → phOf l s ≡ phOf l s′
  → (ConsRecv (phOf l s) → cblkOf l s ≡ cblkOf l s′)
  → (CellFull⁺ b (cellUp   l s) → CellFull⁺ b (cellUp   l s′))
  → (CellFull⁺ b (cellDn   l s) → CellFull⁺ b (cellDn   l s′))
  → (SrvHas⁺   b (upSrv    l s) → SrvHas⁺   b (upSrv    l s′))
  → (SrvHas⁺   b (dnSrv    l s) → SrvHas⁺   b (dnSrv    l s′))
  → (CliHas⁺   b (upClient l s) → CliHas⁺   b (upClient l s′))
  → (CliHas⁺   b (dnClient l s) → CliHas⁺   b (dnClient l s′))
  → (k : LegPos) → AtPos l k b s → LegInv l s′
legFrame l b s s′ pe re ce be cuK cdK usK dsK ucK dcK lpPreSend (hA , hn , hr , hc) =
  b , lpPreSend  , hA
    , subst ProdNotSent pe hn , subst RelayPre re hr , subst InCp03 ce hc
legFrame l b s s′ pe re ce be cuK cdK usK dsK ucK dcK lpUpSrv (hb , hp , hr , hc) =
  b , lpUpSrv    , usK hb
    , subst ProdSent pe hp , subst RelayPre re hr , subst InCp03 ce hc
legFrame l b s s′ pe re ce be cuK cdK usK dsK ucK dcK lpUpCell (hb , hp , hr , hc) =
  b , lpUpCell   , cuK hb
    , subst ProdSent pe hp , subst RelayPre re hr , subst InCp03 ce hc
legFrame l b s s′ pe re ce be cuK cdK usK dsK ucK dcK lpUpClient (hb , hp , hr , hc) =
  b , lpUpClient , ucK hb
    , subst ProdSent pe hp , subst RelayCp3 re hr , subst InCp03 ce hc
legFrame l b s s′ pe re ce be cuK cdK usK dsK ucK dcK lpRelayIn (hIn , hp , hc) =
  b , lpRelayIn  , subst (RelayIn⁺  b) re hIn
    , subst ProdSent pe hp , subst InCp03 ce hc
legFrame l b s s′ pe re ce be cuK cdK usK dsK ucK dcK lpRelayOut (hOut , hp , hc) =
  b , lpRelayOut , subst (RelayOut⁺ b) re hOut
    , subst ProdSent pe hp , subst InCp03 ce hc
legFrame l b s s′ pe re ce be cuK cdK usK dsK ucK dcK lpDnSrv (hb , hp , hr , hc) =
  b , lpDnSrv    , dsK hb
    , subst ProdSent pe hp , subst RelayFwd re hr , subst InCp03 ce hc
legFrame l b s s′ pe re ce be cuK cdK usK dsK ucK dcK lpDnCell (hb , hp , hr , hc) =
  b , lpDnCell   , cdK hb
    , subst ProdSent pe hp , subst RelayFwd re hr , subst InCp03 ce hc
legFrame l b s s′ pe re ce be cuK cdK usK dsK ucK dcK lpDnClient (hb , hp , hr , hc) =
  b , lpDnClient , dcK hb
    , subst ProdSent pe hp , subst RelayFwd re hr , subst ConsCp3 ce hc
legFrame l b s s′ pe re ce be cuK cdK usK dsK ucK dcK lpDone (hcb , hp , hr , hd) =
  b , lpDone     , trans (sym (be hd)) hcb
    , subst ProdSent pe hp , subst RelayFwd re hr , subst ConsRecv ce hd

-- A DRAIN MOVES NO NODE: leg `l`'s seven node-side components are LITERALLY the
-- same terms at `drainSucc s i d₀ id₀`, since that state rebuilds only `med`
-- (`PipeTauMed.agda:87-91`).  Cased on `l` at the top for the same reason
-- `PipeInvProd.srvCoupled-drain` (`:180-185`) is: with `l` abstract the
-- accessors do not reduce and `refl` will not typecheck.
drain-nodes : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
  → (prodOf   l s ≡ prodOf   l (drainSucc s i d₀ id₀))
  × (relayOf  l s ≡ relayOf  l (drainSucc s i d₀ id₀))
  × (phOf     l s ≡ phOf     l (drainSucc s i d₀ id₀))
  × (cblkOf   l s ≡ cblkOf   l (drainSucc s i d₀ id₀))
  × (upSrv    l s ≡ upSrv    l (drainSucc s i d₀ id₀))
  × (dnSrv    l s ≡ dnSrv    l (drainSucc s i d₀ id₀))
  × (upClient l s ≡ upClient l (drainSucc s i d₀ id₀))
  × (dnClient l s ≡ dnClient l (drainSucc s i d₀ id₀))
drain-nodes legBD s i d₀ id₀ = refl , refl , refl , refl , refl , refl , refl , refl
drain-nodes legCD s i d₀ id₀ = refl , refl , refl , refl , refl , refl , refl , refl

-- THE MEDIUM-τ ARM, at `LegInv` — a PURE TRANSPORT, which is exactly what the
-- (C1) `full`-only fix bought.  Stated at STATE level, mirroring its `PipeInvS`
-- counterpart `PipeTauMed.drain-preserve` (`:121-122`); the `RState`-level
-- wrapper is `PipeInvProd.τpreserveS-med` (`:191-217`), which imports the heavy
-- `WalkConvTauInv`/whole-τ-lift layer and therefore belongs to the ASSEMBLY task,
-- not here (this module keeps the cheap-prefix discipline).
--
-- The drain hypothesis `phase (med s) i d₀ id₀ ≡ draining x` is precisely what
-- `WalkConvTauInv.medium-τ-inv-wt` (`:154-158`) reports, so the wrapper hands it
-- over with no glue.
legInv-drain : (l : TwoLegs) (s : SysState) (i : Link) (d₀ : Dir) (id₀ : IDs)
               (x : Payload)
             → phase (med s) i d₀ id₀ ≡ draining x
             → LegInv l s → LegInv l (drainSucc s i d₀ id₀)
legInv-drain l s i d₀ id₀ x dr li =
  let s′ : SysState
      s′ = drainSucc s i d₀ id₀
      (pe , re , ce , be , use , dse , uce , dce) = drain-nodes l s i d₀ id₀
      (b , k , at) = li
      -- the two cells: a `full` cell can never be the drained one, because the
      -- drained key's source phase is `draining x` and `CellFull⁺ b (draining _)`
      -- is `⊥` — this is the clause `CellHasBlk` could not provide
      cuD : CellFull⁺ b (cellUp l s) → CellFull⁺ b (cellUp l s′)
      cuD = λ h → subst (CellFull⁺ b) (sym (cellUp-key l s′))
             (cellDrainKeep (med s) i d₀ id₀ x (upLink l) hi N2N_BlockFetch
               (CellFull⁺ b) (λ ()) dr
               (subst (CellFull⁺ b) (cellUp-key l s) h))
      cdD : CellFull⁺ b (cellDn l s) → CellFull⁺ b (cellDn l s′)
      cdD = λ h → subst (CellFull⁺ b) (sym (cellDn-key l s′))
             (cellDrainKeep (med s) i d₀ id₀ x (dnLink l) hi N2N_BlockFetch
               (CellFull⁺ b) (λ ()) dr
               (subst (CellFull⁺ b) (cellDn-key l s) h))
  in  legFrame l b s s′ pe re ce (λ _ → be) cuD cdD
        (subst (SrvHas⁺ b) use) (subst (SrvHas⁺ b) dse)
        (subst (CliHas⁺ b) uce) (subst (CliHas⁺ b) dce)
        k at

------------------------------------------------------------------------
-- §9  THE io-SYNC OUTPUT (CELL READ) ARM.
--
-- (C1) turned this arm into a MOVING one.  Under Task 1's `CellHasBlk` a
-- `full x → draining x` read left the position put — that is exactly what
-- `PipeTauIo.drain⇒full` (`:214-215`) exploits — but `CellFull⁺` is `full`-only,
-- so the read of the TOKEN'S OWN cell is the hop `lpUpCell → lpUpClient` (and
-- its downstream twin `lpDnCell → lpDnClient`).  Everything else transports.
--
-- WHAT IS BANKED.  The OCCUPANCY-WITH-PAYLOAD half of the hop is banked exactly
-- as the gate verdict said: `PipeCliIoDec.CliBlkVal` (`:115-117`) reads
-- `q ≡ bcBlk1 b` at the `MsgBlock b` payload, which is LITERALLY `CliHas⁺ b` —
-- the predicate `AtPos l lpUpClient` now uses — and `bcStream --MsgBlock b-->
-- bcAblk b` is the ONLY block-gaining client row (`PipeCliIoDec.agda:191-196`).
--
-- *** WHAT IS NOT BANKED — A NEW FINDING OF THIS SLICE, AND IT IS (C2)'s BILL.
-- *** `AtPos l lpUpClient` pins the relay to EXACTLY `cp3` (C2), while
-- `AtPos l lpUpCell` carries only `RelayPre` (= cp0..cp3).  So the hop must
-- UPGRADE `RelayPre` to `RelayCp3` — and NO io fact can do it, because the relay
-- driver is FIXED across an io (`legRelay`), so the upgrade has to hold already
-- in the SOURCE state.  It does hold: the block reaches the wire only after the
-- relay's own `cp2→cp3` `apiBF sendBFRequestRange` (`SysNode.agda:938-944`), and
-- the driver leaves `cp3` only by RECEIVING the block, which cannot have happened
-- while the cell is still UNREAD.  But that is a REACHABILITY fact, not a step
-- fact, so it is this arm's third leaf (`CellCp3`) and it is stated at an
-- `RState` — which carries its own `Reachable` witness — because it is FALSE at
-- an arbitrary `SysState`.  Neither the gate verdict nor either predecessor
-- priced it; it is the price of (C2) and it is flagged to the controller.
------------------------------------------------------------------------

-- a BF SERVER that HOLDS a block is io-fixed: `bsBlk1`'s only outgoing row is
-- the wire WRITE, so it can never be the peer that READS.  The
-- PREDECESSOR-negative mirror of `CliInKeep` — `PipeNodeIoEvo.SrvIoCls`'s
-- ¬-holding arm sits at the SUCCESSOR and so cannot transport an occupancy.
-- SLICE E: `SrvIoCls⁺` at an `output` label IS this keep-fact — its third arm
-- (`SrvWroteBlk` at an `output`) is `⊥`, because no wire READ moves a block out
-- of a server.  Stated through the cone's own classifier so the projections are
-- definitional.
SrvOutKeep : (k : Link) (bfs bfs′ : BFsPos)
          (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) → Set
SrvOutKeep k bfs bfs′ l₀ d₀ id₀ x = SrvIoCls⁺ k hi bfs bfs′ (output l₀ d₀ id₀) x

-- the four tracked servers' keep-facts, in `AllSrvIoCls`'s component order
AllSrvOutKeep : (s s′ : SysState) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) → Set
AllSrvOutKeep s s′ l₀ d₀ id₀ x =
    SrvOutKeep (upLink legBD) (upSrv legBD s) (upSrv legBD s′) l₀ d₀ id₀ x
  × SrvOutKeep (upLink legCD) (upSrv legCD s) (upSrv legCD s′) l₀ d₀ id₀ x
  × SrvOutKeep (dnLink legBD) (dnSrv legBD s) (dnSrv legBD s′) l₀ d₀ id₀ x
  × SrvOutKeep (dnLink legCD) (dnSrv legCD s) (dnSrv legCD s′) l₀ d₀ id₀ x

-- the leg's UPSTREAM server keep-fact
pickSrvUpK : (l : TwoLegs) (s s′ : SysState)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
           → AllSrvOutKeep s s′ l₀ d₀ id₀ x
           → SrvOutKeep (upLink l) (upSrv l s) (upSrv l s′) l₀ d₀ id₀ x
pickSrvUpK legBD s s′ l₀ d₀ id₀ x (q , _ , _ , _) = q
pickSrvUpK legCD s s′ l₀ d₀ id₀ x (_ , q , _ , _) = q

-- the leg's DOWNSTREAM server keep-fact
pickSrvDnK : (l : TwoLegs) (s s′ : SysState)
             (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
           → AllSrvOutKeep s s′ l₀ d₀ id₀ x
           → SrvOutKeep (dnLink l) (dnSrv l s) (dnSrv l s′) l₀ d₀ id₀ x
pickSrvDnK legBD s s′ l₀ d₀ id₀ x (_ , _ , q , _) = q
pickSrvDnK legCD s s′ l₀ d₀ id₀ x (_ , _ , _ , q) = q

-- a HOLDING server is carried across by its keep-fact, WITH its block (three
-- arms since slice E: fixed / not-holding, refuted / a wire WRITE, IMPOSSIBLE on
-- an `output` label and refuted by the classifier's own `⊥`)
-- (the key and the label are EXPLICIT: at an `output` label the classifier's
-- third arm reduces to `⊥`, which ERASES both from the argument type, so nothing
-- would determine them)
srvKeepIo : (k : Link) {b : Block₃} {bfs bfs′ : BFsPos}
            (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
          → SrvOutKeep k bfs bfs′ l₀ d₀ id₀ x → SrvHas⁺ b bfs → SrvHas⁺ b bfs′
srvKeepIo k l₀ d₀ id₀ x (inj₁ refl) h = h
srvKeepIo k {b} {bfs} l₀ d₀ id₀ x (inj₂ (inj₁ ¬h)) h = ⊥-elim (¬h (srvHas⁺⇒hasBlk b bfs h))
srvKeepIo k l₀ d₀ id₀ x (inj₂ (inj₂ ())) h

-- THE api SIBLING, label-free: the VISIBLE arm's `VisLeaves` (§10a) carries the
-- same predecessor-negative keep with no io label in sight, so it keeps the plain
-- two-arm form and its own one-line consumer.
SrvKeep : (bfs bfs′ : BFsPos) → Set
SrvKeep bfs bfs′ = (bfs ≡ bfs′) ⊎ (BFsHasBlk bfs → ⊥)

-- a HOLDING server is carried across by its api keep-fact, WITH its block
srvKeep : {b : Block₃} {bfs bfs′ : BFsPos}
        → SrvKeep bfs bfs′ → SrvHas⁺ b bfs → SrvHas⁺ b bfs′
srvKeep (inj₁ refl) h = h
srvKeep {b} {bfs} (inj₂ ¬h) h = ⊥-elim (¬h (srvHas⁺⇒hasBlk b bfs h))

-- SESSION-53: the READER-SITE positive fact is no longer stated here.  It IS the
-- ⁺ cone's own `CliRead⁺` (`LiveLegIoCone`), whose fixed-slot half the ownership
-- layer of `PipeNodeIoEvo`'s §1b discharges, so §3's `pickCliUpH`/`pickCliDnH`
-- read it straight off `allCli` and LEAF 4 IS GONE FROM THIS MODULE'S PREMISES.
-- What it says, unchanged: at a client's OWN key `(k , hi , BF)` a wire READ whose
-- payload is `blkPayload b` leaves THAT client holding exactly `b`
-- (`CliHas⁺ b bfc′` IS `bfc′ ≡ bcBlk1 b`, definitionally the cone's conclusion).

-- (C2)'s BILL, as a leaf: a leg whose own cell still holds the UNREAD token has
-- its reader's driver at EXACTLY the pre-`recvBFBlock` phase.  Stated at an
-- `RState` because it is a REACHABILITY fact (see this section's header) — at an
-- arbitrary `SysState` it is false.
--
-- *** TokenExcl INSTALMENT 2, SLICE B — THE CONDITIONAL FORM (reviewer-adopted
-- interface reshape). ***  Each half now takes the reader's PENDING-PHASE fact
-- (`RelayPre` upstream, `InCp03` downstream) as a second hypothesis and UPGRADES
-- it to the exact `cp3` pin.  This is FREE to the consumers: the only consumer is
-- §9's io-READ arm, and the position it reads the antecedent from —
-- `AtPos l lpUpCell` / `lpDnCell` (`LiveLegInv:430-431`, `:440-441`) — carries
-- that very conjunct beside the cell occupancy, so `readMove` already HAS it and
-- merely did not pass it in.  The point of the reshape is the PROVER's side: the
-- honest inductive object behind this leaf is the relay's request WINDOW (see
-- `LiveTokenExcl` §5), and the phase-MONOTONE route to it needs to know the
-- reader is still pending — without that hypothesis the statement has to re-derive
-- "not yet past `cp3`" at every use.  Nothing in this module's proofs changes.
CellCp3 : (l : TwoLegs) (b : Block₃) (r : RState) → Set
CellCp3 l b r =
    (CellFull⁺ b (cellUp l (toSys r)) → RelayPre (relayOf l (toSys r))
       → RelayCp3 (relayOf l (toSys r)))
  × (CellFull⁺ b (cellDn l (toSys r)) → InCp03 (phOf l (toSys r))
       → ConsCp3 (phOf   l (toSys r)))

-- `full` is a `CopyPhase` CONSTRUCTOR, hence injective: this is what turns the
-- read cell's own payload equality into the classifier's `x ≡ blkPayload b`
full-inj : {x y : Payload} → full x ≡ full y → x ≡ y
full-inj refl = refl

-- AN UNREAD CELL ACROSS AN OUTPUT io: either the fired key is not its own and it
-- survives untouched, or it IS the read cell — and then the three key equalities
-- plus its own `full x` content are handed to the continuation, which turns them
-- into the NEXT position.  (Generic in the transported predicate for the same
-- reason `cellKeep-in` is.)
cellRead-out : {B : Set} (P : CopyPhase → Set)
    (g : Link → Dir → IDs → CopyPhase)
    (k : Link) (kd : Dir) (ki : IDs) (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload)
    {cu cu′ : CopyPhase}
  → cu  ≡ g k kd ki
  → cu′ ≡ phase-upd g l₀ (setCell (g l₀) d₀ id₀ (draining x)) k kd ki
  → g l₀ d₀ id₀ ≡ full x
  → ((k ≡ l₀) → (kd ≡ d₀) → (ki ≡ id₀) → P (full x) → B)
  → P cu → P cu′ ⊎ B
cellRead-out P g k kd ki l₀ d₀ id₀ x ceq c′eq srcFull hit h
  with setRead g l₀ d₀ id₀ (draining x) k kd ki
... | inj₁ eq = inj₁ (subst P (trans ceq (trans eq (sym c′eq))) h)
... | inj₂ (e1 , e2 , e3 , _) =
      inj₂ (hit e1 e2 e3 (subst P (trans ceq (atKey g e1 e2 e3 srcFull)) h))

-- read the UP cell's OUTPUT answer as a POSITION: still unread in the cell, or
-- delivered into the leg's up client — the hop (C1) created
atUpRead : (l : TwoLegs) (b : Block₃) (s′ : SysState)
         → CellFull⁺ b (cellUp l s′)
           ⊎ (CliHas⁺ b (upClient l s′) × RelayCp3 (relayOf l s′))
         → ProdSent (prodOf l s′) → RelayPre (relayOf l s′) → InCp03 (phOf l s′)
         → LegInv l s′
atUpRead l b s′ (inj₁ hb)          hp hr hc = b , lpUpCell   , hb  , hp , hr  , hc
atUpRead l b s′ (inj₂ (hcl , hr3)) hp hr hc = b , lpUpClient , hcl , hp , hr3 , hc

-- read the DOWN cell's OUTPUT answer as a POSITION
atDnRead : (l : TwoLegs) (b : Block₃) (s′ : SysState)
         → CellFull⁺ b (cellDn l s′)
           ⊎ (CliHas⁺ b (dnClient l s′) × ConsCp3 (phOf l s′))
         → ProdSent (prodOf l s′) → RelayFwd (relayOf l s′) → InCp03 (phOf l s′)
         → LegInv l s′
atDnRead l b s′ (inj₁ hb)          hp hr hc = b , lpDnCell   , hb  , hp , hr , hc
atDnRead l b s′ (inj₂ (hcl , hc3)) hp hr hc = b , lpDnClient , hcl , hp , hr , hc3

-- rebuild the token's position across a hidden io OUTPUT, CARRYING ITS BLOCK.
-- `legFrame` with the two CELL slots replaced by the read dichotomy: eight
-- clauses transport, the two cells are the genuine HOPS.
readMove : (l : TwoLegs) (b : Block₃) (s s′ : SysState)
  → prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′ → phOf l s ≡ phOf l s′
  → cblkOf l s ≡ cblkOf l s′
  -- SLICE B: the two read dichotomies now take the position's own PENDING-PHASE
  -- conjunct as well, which is what the conditional `CellCp3` asks for; the two
  -- cell clauses below have it in hand (`hr`/`hc`) and pass it straight through
  → (CellFull⁺ b (cellUp l s) → RelayPre (relayOf l s)
       → CellFull⁺ b (cellUp l s′)
         ⊎ (CliHas⁺ b (upClient l s′) × RelayCp3 (relayOf l s′)))
  → (CellFull⁺ b (cellDn l s) → InCp03 (phOf l s)
       → CellFull⁺ b (cellDn l s′)
         ⊎ (CliHas⁺ b (dnClient l s′) × ConsCp3 (phOf l s′)))
  → (SrvHas⁺ b (upSrv    l s) → SrvHas⁺ b (upSrv    l s′))
  → (SrvHas⁺ b (dnSrv    l s) → SrvHas⁺ b (dnSrv    l s′))
  → (CliHas⁺ b (upClient l s) → CliHas⁺ b (upClient l s′))
  → (CliHas⁺ b (dnClient l s) → CliHas⁺ b (dnClient l s′))
  → (k : LegPos) → AtPos l k b s → LegInv l s′
readMove l b s s′ pe re ce be cuR cdR usK dsK ucK dcK lpPreSend (hA , hn , hr , hc) =
  b , lpPreSend  , hA
    , subst ProdNotSent pe hn , subst RelayPre re hr , subst InCp03 ce hc
readMove l b s s′ pe re ce be cuR cdR usK dsK ucK dcK lpUpSrv (hb , hp , hr , hc) =
  b , lpUpSrv    , usK hb
    , subst ProdSent pe hp , subst RelayPre re hr , subst InCp03 ce hc
readMove l b s s′ pe re ce be cuR cdR usK dsK ucK dcK lpUpCell (hb , hp , hr , hc) =
  atUpRead l b s′ (cuR hb hr)
    (subst ProdSent pe hp) (subst RelayPre re hr) (subst InCp03 ce hc)
readMove l b s s′ pe re ce be cuR cdR usK dsK ucK dcK lpUpClient (hb , hp , hr , hc) =
  b , lpUpClient , ucK hb
    , subst ProdSent pe hp , subst RelayCp3 re hr , subst InCp03 ce hc
readMove l b s s′ pe re ce be cuR cdR usK dsK ucK dcK lpRelayIn (hIn , hp , hc) =
  b , lpRelayIn  , subst (RelayIn⁺  b) re hIn
    , subst ProdSent pe hp , subst InCp03 ce hc
readMove l b s s′ pe re ce be cuR cdR usK dsK ucK dcK lpRelayOut (hOut , hp , hc) =
  b , lpRelayOut , subst (RelayOut⁺ b) re hOut
    , subst ProdSent pe hp , subst InCp03 ce hc
readMove l b s s′ pe re ce be cuR cdR usK dsK ucK dcK lpDnSrv (hb , hp , hr , hc) =
  b , lpDnSrv    , dsK hb
    , subst ProdSent pe hp , subst RelayFwd re hr , subst InCp03 ce hc
readMove l b s s′ pe re ce be cuR cdR usK dsK ucK dcK lpDnCell (hb , hp , hr , hc) =
  atDnRead l b s′ (cdR hb hc)
    (subst ProdSent pe hp) (subst RelayFwd re hr) (subst InCp03 ce hc)
readMove l b s s′ pe re ce be cuR cdR usK dsK ucK dcK lpDnClient (hb , hp , hr , hc) =
  b , lpDnClient , dcK hb
    , subst ProdSent pe hp , subst RelayFwd re hr , subst ConsCp3 ce hc
readMove l b s s′ pe re ce be cuR cdR usK dsK ucK dcK lpDone (hcb , hp , hr , hd) =
  b , lpDone     , trans (sym be) hcb
    , subst ProdSent pe hp , subst RelayFwd re hr , subst ConsRecv ce hd

-- SESSION-53: LEAVES 1, 2, 3 AND 4 ARE ALL DISCHARGED — the ⁺ cone reports the
-- keeps AND the reader identification, the latter on the CHANNEL-OWNERSHIP layer
-- that `PipeNodeIoEvo`'s §1b now threads through `cRefl`: the leg's own upstream
-- SERVER does share the read key `(upLink l , hi , BF)` with its client
-- (`PipeCliIoDec:26-30`), and what separates them is the bundle's io ROLE
-- fingerprint (a block payload on an `output` is client-role, so no server can be
-- the reader) plus the link disequalities at every other site.
--
-- THE ONE PREMISE LEFT ON THIS ARM is `cellCp3` (leaf 5) — (C2)'s REACHABILITY
-- bill, and by owner decision #4 it stays a module premise for this campaign:
-- it is one of the exactly two per-state facts a future `TokenExcl` component
-- discharges (the other is `NoTwoTokens`, §10a).
-- *** CONSUMER-FREE, NOT AN ASSUMPTION OF THE ROUTE (the cellCp3 window). ***  The
-- fact is a THEOREM — `LiveChanJoin.cellCp3-of`, off the carried join — and the route
-- discharges it on `LiveLegAssembly`'s io-READ MAP.  This parameter survives because
-- `legInv-read`'s only consumer is `LiveTokenExcl.legInv-read⁺`, which sits under a
-- never-applied `module _ (ch : …)`: the PARKED chain-alignment route.  So nothing
-- reachable assumes it.  A grower who wants it premise-free should copy slice D's
-- reshape (put the fact on the preservation map, at the arm's own `r`).
module _ (cellCp3 : (l : TwoLegs) (b : Block₃) (r : RState) → CellCp3 l b r)
  where

  -- ONE hidden io-SYNC READ, at `LegInv`: the OUTPUT arm of `TauStepL`.  The
  -- `let` skeleton is `PipeTauIo.tauIo-out`'s (`:414-471`) verbatim down to the
  -- binder names; only `pres` changes, from four implication transports to one
  -- position rebuild.
  legInv-read : (l : TwoLegs) (r : RState)
      (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
    → ioES .mem (Payload , output l₀ d₀ id₀) x
    → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► M₁
    → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► N₁
    → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
    → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (LegInv l (toSys r) → LegInv l (toSys r′))
  legInv-read l r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
    let (srcFull , M₁≡) = medium-ev-out-key (med (toSys r)) l₀ d₀ id₀ x sM
        g : Link → Dir → IDs → CopyPhase
        g = phase (med (toSys r))
        m′ : MedState
        m′ = mkMed (phase-upd g l₀ (setCell (g l₀) d₀ id₀ (draining x)))
                   (broken (med (toSys r)))
        cone = top-nodes-io-evo⁺ (toSys r) {Payload} {output l₀ d₀ id₀} {x} {N₁} iomem sN
        s″ : SysState
        s″ = proj₁ cone
        (_ , medEq , N₁≡ , cWeakRun , allCli , allSrv
           , epAB , epAC , ecB , ecC , edBD , edCD) = cone
        s′ : SysState
        s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
        r′ : RState
        r′ = mkR s′ (rStepʷ (reach r) (io-sync-wrun r m′ s″ iomem sM M₁≡ cWeakRun))
        pe : prodOf l (toSys r) ≡ prodOf l s′
        pe = legProd l epAB epAC
        re : relayOf l (toSys r) ≡ relayOf l s′
        re = legRelay l ecB ecC
        ce : phOf l (toSys r) ≡ phOf l s′
        ce = legCons l edBD edCD
        be : cblkOf l (toSys r) ≡ cblkOf l s′
        be = legCblk l edBD edCD
        -- the two READ dichotomies: untouched cell, or the hop into the reader
        -- SLICE B: `hpre`/`hin` are the reader's PENDING-PHASE conjuncts, which
        -- `readMove`'s two cell clauses pass down from the position itself; the
        -- conditional `CellCp3` consumes them and returns the `cp3` pin
        cuR : (b : Block₃) → CellFull⁺ b (cellUp l (toSys r))
            → RelayPre (relayOf l (toSys r))
            → CellFull⁺ b (cellUp l s′)
              ⊎ (CliHas⁺ b (upClient l s′) × RelayCp3 (relayOf l s′))
        cuR b = λ h hpre →
          cellRead-out (CellFull⁺ b) g (upLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
            (cellUp-key l (toSys r)) (cellUp-key l s′) srcFull
            (λ e1 e2 e3 hf →
                pickCliUpH l (toSys r) s′ (output l₀ d₀ id₀) x allCli
                  e1 e2 e3 b _ _ _ (full-inj hf)
              , subst RelayCp3 re (proj₁ (cellCp3 l b r) h hpre))
            h
        cdR : (b : Block₃) → CellFull⁺ b (cellDn l (toSys r))
            → InCp03 (phOf l (toSys r))
            → CellFull⁺ b (cellDn l s′)
              ⊎ (CliHas⁺ b (dnClient l s′) × ConsCp3 (phOf l s′))
        cdR b = λ h hin →
          cellRead-out (CellFull⁺ b) g (dnLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
            (cellDn-key l (toSys r)) (cellDn-key l s′) srcFull
            (λ e1 e2 e3 hf →
                pickCliDnH l (toSys r) s′ (output l₀ d₀ id₀) x allCli
                  e1 e2 e3 b _ _ _ (full-inj hf)
              , subst ConsCp3 ce (proj₂ (cellCp3 l b r) h hin))
            h
        pres : LegInv l (toSys r) → LegInv l s′
        pres = λ li →
          let (b , k , at) = li
          in  readMove l b (toSys r) s′ pe re ce be (cuR b) (cdR b)
                (srvKeepIo (upLink l) l₀ d₀ id₀ x (pickSrvUpK l (toSys r) s′ l₀ d₀ id₀ x allSrv))
                (srvKeepIo (dnLink l) l₀ d₀ id₀ x (pickSrvDnK l (toSys r) s′ l₀ d₀ id₀ x allSrv))
                (cliKeep (pickCliUp⁺ l (toSys r) s′ (output l₀ d₀ id₀) x allCli))
                (cliKeep (pickCliDn⁺ l (toSys r) s′ (output l₀ d₀ id₀) x allCli))
                k at
    in  r′ , trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡) , pres

------------------------------------------------------------------------
-- §10  THE VISIBLE ARM, at STATE level.
--
-- SHAPE, and why it is stated at STATE level.  `PipeEvStep.evStepS` (`:500-526`)
-- is a LABEL dispatch: twelve impossible classes refuted through
-- `SysBisim.oevB-refute`/`oevB-no-io`, `break` framed, and the api-CSBF case
-- routed through the reflect bridge `reach-ev-driver` (`:249-278`) to
-- `legStep→pres` (`:183-196`).  Everything in that dispatch EXCEPT
-- `legStep→pres` is payload-INDEPENDENT and transfers verbatim — and all of it
-- imports `SysBisim`, which the cheap-prefix discipline keeps out of this
-- module.  So the genuinely new content, and the whole of this section, is the
-- `LegInv` mirror of `legStep→pres`: a `LegDriverStep`-driven position rebuild.
-- Its `RState` wrapper belongs to the ASSEMBLY task, exactly as the medium-τ
-- arm's does (§8).
--
-- *** THE FINDING OF THIS SLICE, AND IT IS W2's BILL. ***  Nine of the forty
-- position×constructor obligations cannot be discharged from the cone at all,
-- and FOUR of them are PAIRWISE TOKEN EXCLUSIONS — "the up server and the
-- relay's up client are never both holding", and its three siblings.  They arise
-- because `AtPos` asserts ONE slot occupied and says nothing about the other
-- eight (the W2 "DO NOT ADD exclusivity" decision), so when the cone reports
-- "the relay RECEIVED" (`ldRelay`'s `wUp`, or `ldCons`'s `wDn`) at a position
-- whose token is UPSTREAM, nothing contradicts it — even though it would mean
-- two blocks in flight.  Where a driver-phase disjointness DOES contradict it
-- the refutation is free and is taken (six such sites: `relayPre-has-⊥`,
-- `relayPre-fwd-⊥`, `relayHas-fwd-⊥`, `prodSent-notSent-⊥`, `inCp03-recv-⊥`);
-- the four that remain are the four cases where both slots sit on the SAME side
-- of every phase gate.  They ship as `NoTwoTokens`, a four-field record of
-- pairwise exclusions — i.e. the CHEAPEST POSSIBLE fragment of exclusivity, four
-- implications rather than the ~2,600 lines the gate priced for the full form.
--
-- The other five WERE positive hand-over facts; slice C retired two of them, so
-- `VisLeaves` now has FOUR fields (covering THREE leaves): the two visible
-- server keeps (leaf 6, one per leg end), the producer's
-- `sendBFBlock` hop (hop 1) and the relay's `sendBFBlock` hop (hop 6).  The
-- relay's recorded-block fixity (leaf 8) and hop 4 are DERIVED — the former from
-- `PipeValRelay.cpStepKindL-of⁺`'s seventh component, the latter through §10b′'s
-- `relayRecv-of` off slice D's widened `lblR` gate.
------------------------------------------------------------------------

-- `RelayHas` and `RelayFwd` are DISJOINT (`consuming cp4-6` ∪ `producing pp0-5`
-- against `producing pp6-9`) — the refutation six of this section's clauses use
relayHas-fwd-⊥ : (r : CPPh) → RelayHas r → RelayFwd r → ⊥
relayHas-fwd-⊥ (consuming _ cp0) () _
relayHas-fwd-⊥ (consuming _ cp1) () _
relayHas-fwd-⊥ (consuming _ cp2) () _
relayHas-fwd-⊥ (consuming _ cp3) () _
relayHas-fwd-⊥ (consuming _ cp4) _ ()
relayHas-fwd-⊥ (consuming _ cp5) _ ()
relayHas-fwd-⊥ (consuming _ cp6) _ ()
relayHas-fwd-⊥ (producing _ pp0) _ ()
relayHas-fwd-⊥ (producing _ pp1) _ ()
relayHas-fwd-⊥ (producing _ pp2) _ ()
relayHas-fwd-⊥ (producing _ pp3) _ ()
relayHas-fwd-⊥ (producing _ pp4) _ ()
relayHas-fwd-⊥ (producing _ pp5) _ ()
relayHas-fwd-⊥ (producing _ pp6) () _
relayHas-fwd-⊥ (producing _ pp7) () _
relayHas-fwd-⊥ (producing _ pp8) () _
relayHas-fwd-⊥ (producing _ pp9) () _

-- `RelayHas` splits EXHAUSTIVELY into the consume tail and the produce tail —
-- the two `LegPos` slots `PipeInv` fuses into its `L2`
relayHas⇒in⊎out : (r : CPPh) → RelayHas r → RelayIn r ⊎ RelayOut r
relayHas⇒in⊎out (consuming _ cp0) ()
relayHas⇒in⊎out (consuming _ cp1) ()
relayHas⇒in⊎out (consuming _ cp2) ()
relayHas⇒in⊎out (consuming _ cp3) ()
relayHas⇒in⊎out (consuming _ cp4) _ = inj₁ tt
relayHas⇒in⊎out (consuming _ cp5) _ = inj₁ tt
relayHas⇒in⊎out (consuming _ cp6) _ = inj₁ tt
relayHas⇒in⊎out (producing _ pp0) _ = inj₂ tt
relayHas⇒in⊎out (producing _ pp1) _ = inj₂ tt
relayHas⇒in⊎out (producing _ pp2) _ = inj₂ tt
relayHas⇒in⊎out (producing _ pp3) _ = inj₂ tt
relayHas⇒in⊎out (producing _ pp4) _ = inj₂ tt
relayHas⇒in⊎out (producing _ pp5) _ = inj₂ tt
relayHas⇒in⊎out (producing _ pp6) ()
relayHas⇒in⊎out (producing _ pp7) ()
relayHas⇒in⊎out (producing _ pp8) ()
relayHas⇒in⊎out (producing _ pp9) ()

-- the (C2) consumer pin, as the EQUALITY the `ldCons` anchor is gated on
consCp3⇒eq : (c : ConsPh) → ConsCp3 c → c ≡ cp3
consCp3⇒eq cp0 ()
consCp3⇒eq cp1 ()
consCp3⇒eq cp2 ()
consCp3⇒eq cp3 _ = refl
consCp3⇒eq cp4 ()
consCp3⇒eq cp5 ()
consCp3⇒eq cp6 ()

-- the (C2) relay pin, as the EQUALITY the widened `lblR` gate is stated with
-- (`Σ[ b ] x ≡ consuming b cp3`) — the glue lemma slice D's discharge needs
relayCp3⇒eq : (r : CPPh) → RelayCp3 r → Σ[ b ∈ Block₃ ] r ≡ consuming b cp3
relayCp3⇒eq (consuming _ cp0) ()
relayCp3⇒eq (consuming _ cp1) ()
relayCp3⇒eq (consuming _ cp2) ()
relayCp3⇒eq (consuming b cp3) _ = b , refl
relayCp3⇒eq (consuming _ cp4) ()
relayCp3⇒eq (consuming _ cp5) ()
relayCp3⇒eq (consuming _ cp6) ()
relayCp3⇒eq (producing _ _)   ()

-- `bcBlk1` is a `BFcPos` CONSTRUCTOR, hence injective: this is what identifies
-- the gate's relayed block with the position's
bcBlk1-inj : {b b′ : Block₃} → bcBlk1 b ≡ bcBlk1 b′ → b ≡ b′
bcBlk1-inj refl = refl

-- `ConsHeld` (the cone's recorded-block gate) and `ConsRecv` (the invariant's)
-- are the SAME predicate under different names — cp4..cp6 both
consRecv⇒held : (c : ConsPh) → ConsRecv c → ConsHeld c
consRecv⇒held cp0 ()
consRecv⇒held cp1 ()
consRecv⇒held cp2 ()
consRecv⇒held cp3 ()
consRecv⇒held cp4 _ = tt
consRecv⇒held cp5 _ = tt
consRecv⇒held cp6 _ = tt

-- from `cp3` the ONLY consumer adjacency is the receive `c34`, so the successor
-- has received.  Stated with an abstract target so the constructor match can
-- solve it (`ConsAdv cp3 (phOf l s′)` would be a stuck unification).
consAdv-cp3-recv : {c : ConsPh} → ConsAdv cp3 c → ConsRecv c
consAdv-cp3-recv c34 = tt

------------------------------------------------------------------------
-- §10a  THE VISIBLE-AXIS LEAVES.
------------------------------------------------------------------------

-- THE FOUR PAIRWISE TOKEN EXCLUSIONS — the cheapest fragment of W2.  Each says
-- that a slot and the BF CLIENT DOWNSTREAM of it are never both holding, which
-- is what refutes "the reader received" at a position whose token is upstream of
-- the reader and on the same side of every driver-phase gate.  Reachability
-- facts (two blocks are never in flight on one leg), stated per state.
--
-- *** (C1) AGAIN — THE TWO CELL FIELDS ARE `CellFullBlk`, NOT `CellHasBlk`. ***
-- TokenExcl instalment 1 (commit `37e4e75`) MACHINE-CHECKED that with
-- `CellHasBlk` this record is FALSE AS STATED, and instalment 2 applied the fix
-- below (controller-approved, blast radius 4 lines).  The refutation, for the
-- record: `CellHasBlk` holds of `draining` as well as `full`
-- (`PipeInv:467-470`), and `draining` is the POST-READ phase at which the far-end
-- BF client HOLDS THE BLOCK — `LiveLegInv:227-241` (C1) says so in as many words,
-- and §9's io-READ arm BUILDS such a reachable successor: `legInv-read` sets the
-- fired cell to `draining x` (`setCell`, the `m′` binder) while `cellRead-out`'s
-- hit continuation hands the reader `CliHas⁺ b (upClient l s′)` through
-- `pickCliUpH`.  So at every read-but-not-yet-drained state BOTH antecedents of
-- the old `nUpCellCli` held, and the field asserted their conjunction absurd.
-- The witnesses were `noTwo-post-read-{up,dn}-⊥`/`noTwoTokens-unprovable` in
-- `LiveTokenExcl` §6 at `37e4e75` (kept in git history, retired by this fix —
-- they no longer typecheck, which IS the fix's signal).  The `full`-only form
-- costs the consumers nothing: both use sites below already hold
-- `CellFull⁺ b`-derived evidence and merely forgot it through `cellFull⇒hasBlk`.
record NoTwoTokens (l : TwoLegs) (s : SysState) : Set where
  constructor noTwo
  field
    nUpSrvCli  : BFsHasBlk   (upSrv  l s) → BFcHasBlk (upClient l s) → ⊥
    nUpCellCli : CellFullBlk (cellUp l s) → BFcHasBlk (upClient l s) → ⊥
    nDnSrvCli  : BFsHasBlk   (dnSrv  l s) → BFcHasBlk (dnClient l s) → ⊥
    nDnCellCli : CellFullBlk (cellDn l s) → BFcHasBlk (dnClient l s) → ⊥
open NoTwoTokens public

-- THE FOUR HAND-OVER FIELDS (three leaves) the visible cone does not carry.
--
-- *** SLICE B: NO LONGER A PREMISE. ***  `LiveLegApiExpose.VisLeaves⁺` has exactly
-- these four field types and its `driverExpose⁺` PROVES them for every visible
-- api step (leaf 6 from "`bsBlk1` has no api row", decoded at the fired server
-- slot; leaf 7 off `decProd`'s `pp5` row; leaf 9 off the relay's own `pp5 → pp6`
-- crossing), so the record is imported rather than assumed.  The only shape
-- change is leaf 9's second argument: the PREDICATE `RelayAt b (relayOf l s)`
-- instead of `relayBlk (relayOf l s) ≡ b`, because `relayBlk` is projection-like
-- and reproduces `PipeValRelay`'s banked Agda 2.8 ICE inside a `with`-abstracted
-- result.  `relayHasStep` converts with the `eq⇒relayAt` it already imports.
--
-- SLICE C had already retired two fields (the record was FIVE):
--   · `vRelayRecv` (hop 4) — slice D widened `ldRelay`'s `wUp` gate; §10b′'s
--     `relayRecv-of` turns it into the hop.
--   · `vRelayBlk` (leaf 8) — `PipeValRelay.cpStepKindL-of⁺`'s SEVENTH component.
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiExpose blkA
  using ( vUpSrvKeep; vDnSrvKeep; vProdSend; vRelayFwd⁺; driverExpose⁺ )
  renaming ( VisLeaves⁺ to VisLeaves; visLeaves⁺ to visLeaves )

------------------------------------------------------------------------
-- §10b  THE PER-STEP-KIND CLAUSE HELPERS.  Each pattern-matches its step kind,
-- so the dispatches below stay `with`-free at goals mentioning `AtPos`.
------------------------------------------------------------------------

-- at a PRE-RECEIVE position the relay stays pre-receive: a `rFwd` contradicts
-- the position's own phase, and a `rRecv` would put a block in the relay's up
-- client, which the caller refutes (`¬cli`)
relayPreKeep : (l : TwoLegs) (s s′ : SysState)
  → RelayStepKind (relayOf l s) (relayOf l s′)
  → (RelayPre (relayOf l s) → RelayHas (relayOf l s′) → BFcHasBlk (upClient l s))
  → (BFcHasBlk (upClient l s) → ⊥)
  → RelayPre (relayOf l s) → RelayPre (relayOf l s′)
relayPreKeep l s s′ (rMove fP _ _ _)  wUp ¬cli hr = fP hr
relayPreKeep l s s′ (rFwd hHas _ _)   wUp ¬cli hr = ⊥-elim (relayPre-has-⊥ _ hr hHas)
relayPreKeep l s s′ (rRecv hPre hHas) wUp ¬cli hr = ⊥-elim (¬cli (wUp hPre hHas))

-- read a relay successor that still HOLDS as a position: the consume tail or
-- the produce tail, at the SAME block
atRelayHas : (l : TwoLegs) (b : Block₃) (s′ : SysState)
           → RelayIn (relayOf l s′) ⊎ RelayOut (relayOf l s′)
           → relayBlk (relayOf l s′) ≡ b
           → ProdSent (prodOf l s′) → InCp03 (phOf l s′) → LegInv l s′
atRelayHas l b s′ (inj₁ hIn)  eb hp hc = b , lpRelayIn  , (hIn  , eb) , hp , hc
atRelayHas l b s′ (inj₂ hOut) eb hp hc = b , lpRelayOut , (hOut , eb) , hp , hc

-- at a relay-HOLDING position the relay either keeps the block (staying in one
-- of its two slots) or FORWARDS it into its own BF server; a `rRecv` is refuted
-- by the position's own phase
relayHasStep : (l : TwoLegs) (b : Block₃) (s s′ : SysState)
  → RelayStepKind (relayOf l s) (relayOf l s′)
  → VisLeaves l s s′
  -- LEAF 8, now SUPPLIED BY THE CONE (`ldRelay`'s new field) rather than by
  -- `VisLeaves`: the relay's recorded block is fixed off the receive region
  → ((RelayPre (relayOf l s) → ⊥) → (bb : Block₃)
     → RelayAt bb (relayOf l s) → RelayAt bb (relayOf l s′))
  → RelayHas (relayOf l s) → (RelayPre (relayOf l s) → ⊥)
  → relayBlk (relayOf l s) ≡ b
  → ProdSent (prodOf l s′) → InCp03 (phOf l s′)
  → LegInv l s′
relayHasStep l b s s′ (rMove _ fH _ _) vl blkR hHas npre eb hp hc =
  atRelayHas l b s′ (relayHas⇒in⊎out _ (fH hHas))
    (relayAt⇒eq b (relayOf l s′) (blkR npre b (eq⇒relayAt b (relayOf l s) eb))) hp hc
relayHasStep l b s s′ (rFwd _ hFwd _)  vl blkR hHas npre eb hp hc =
  b , lpDnSrv , vRelayFwd⁺ vl b (eq⇒relayAt b (relayOf l s) eb) hHas hFwd , hp , hFwd , hc
relayHasStep l b s s′ (rRecv hPre _)   vl blkR hHas npre eb hp hc = ⊥-elim (npre hPre)

-- HOP 4 read as a position: the relayed block is the position's own (`bcBlk1`
-- injectivity) and the successor phase `consuming b cp4` IS `lpRelayIn`
atRelayRecv : (l : TwoLegs) (b : Block₃) (s s′ : SysState)
  → (Σ[ bc ∈ Block₃ ] (upClient l s ≡ bcBlk1 bc) × (relayOf l s′ ≡ consuming bc cp4))
  → CliHas⁺ b (upClient l s)
  → ProdSent (prodOf l s′) → InCp03 (phOf l s′) → LegInv l s′
atRelayRecv l b s s′ (bc , ecl , ere) hb hp hc =
  b , lpRelayIn
    , subst (RelayIn⁺ b) (sym ere) (tt , sym (bcBlk1-inj (trans (sym hb) ecl)))
    , hp , hc

-- the producer step at `lpPreSend`: an internal move keeps the token unsent, the
-- `a56` `sendBFBlock` hands it to the leg's own BF server
atProdSend : (l : TwoLegs) (b : Block₃) (s s′ : SysState) → b ≡ blkA
  → ProdStepKind (prodOf l s) (prodOf l s′)
  → (ProdSent (prodOf l s′) → SrvHas⁺ b (upSrv l s′))
  → ProdNotSent (prodOf l s)
  → RelayPre (relayOf l s′) → InCp03 (phOf l s′) → LegInv l s′
atProdSend l b s s′ hA (pMove fN _) hop hn hr hc = b , lpPreSend , hA     , fN hn , hr , hc
atProdSend l b s s′ hA (pSend _ sS) hop hn hr hc = b , lpUpSrv   , hop sS , sS    , hr , hc

-- at a position UPSTREAM of node D the consumer stays pending: a receive would
-- put a block in D's own client, which the caller refutes (`¬cli`)
consInKeep : (l : TwoLegs) (s s′ : SysState)
  → ConsStepKind (phOf l s) (phOf l s′)
  → (InCp03 (phOf l s) → ConsRecv (phOf l s′) → BFcHasBlk (dnClient l s))
  → (BFcHasBlk (dnClient l s) → ⊥)
  → InCp03 (phOf l s) → InCp03 (phOf l s′)
consInKeep l s s′ (cMove fI _ _)     wDn ¬cli hc = fI hc
consInKeep l s s′ (cRecv hPre hRecv) wDn ¬cli hc = ⊥-elim (¬cli (wDn hPre hRecv))

-- past the receive the consumer stays received (a second receive is refuted by
-- the position's own phase)
consRecvKeep : (l : TwoLegs) (s s′ : SysState)
  → ConsStepKind (phOf l s) (phOf l s′)
  → ConsRecv (phOf l s) → ConsRecv (phOf l s′)
consRecvKeep l s s′ (cMove _ fR _) hd = fR hd
consRecvKeep l s s′ (cRecv hPre _) hd = ⊥-elim (inCp03-recv-⊥ _ hPre hd)

------------------------------------------------------------------------
-- §10b′  HOP 4, DISCHARGED (slice D, re-sited by slice C).
--
-- `VisLeaves`' `vRelayRecv` WAS the interim premise; slice C RETIRED that field
-- and `legStep→legInv` now calls this lemma directly, so the hop is DISCHARGED
-- in-module rather than merely dischargeable.  With the widened
-- `ldRelay` gate — `PipeValRelay.cpStepKindL-of⁺`'s label component, and hence
-- `NodeBDrv`/`NodeCDrv`/`ldRelay`'s `wUp`, now take
-- `(RelayPre × RelayHas) ⊎ (Σ[ b ] x ≡ consuming b cp3)` — it is a DIRECT
-- APPLICATION: `relayCp3⇒eq` turns the (C2) pin into the `inj₂` payload and the
-- gate returns the hop outright.  The two glue lemmas the estimate omitted
-- (`relayCp3⇒eq`, `bcBlk1-inj`) live in §10 above; `bcBlk1-inj` is consumed by
-- `atRelayRecv`, which is what identifies the gate's `bc` with the position's `b`.
------------------------------------------------------------------------

-- turn the WIDENED `ldRelay` gate into the hop-4 hand-over fact: at a
-- `cp3` relay the fired api IS the `recvBFBlock` receive, so the relay's own up
-- client held the block and the successor phase records it
relayRecv-of : (l : TwoLegs) (s s′ : SysState)
  → (((RelayPre (relayOf l s) × RelayHas (relayOf l s′))
      ⊎ (Σ[ b ∈ Block₃ ] relayOf l s ≡ consuming b cp3))
     → BFcHasBlk (upClient l s)
       × (Σ[ bc ∈ Block₃ ] (upClient l s ≡ bcBlk1 bc)
                          × (relayOf l s′ ≡ consuming bc cp4)))
  → RelayCp3 (relayOf l s)
  → Σ[ bc ∈ Block₃ ] (upClient l s ≡ bcBlk1 bc) × (relayOf l s′ ≡ consuming bc cp4)
relayRecv-of l s s′ w hr = proj₂ (w (inj₂ (relayCp3⇒eq (relayOf l s) hr)))

------------------------------------------------------------------------
-- §10c  THE FOUR PER-CONSTRUCTOR TEN-POSITION DISPATCHES.
------------------------------------------------------------------------

-- node A fired leg `l`'s producer: `lpPreSend` is the HOP, everything else
-- transports (`ProdSent` along `padv-sent-mono`)
prodMove : (l : TwoLegs) (b : Block₃) (s s′ : SysState)
  → ProdAdv (prodOf l s) (prodOf l s′)
  → relayOf  l s ≡ relayOf  l s′ → phOf     l s ≡ phOf     l s′
  → cellUp   l s ≡ cellUp   l s′ → cellDn   l s ≡ cellDn   l s′
  → upClient l s ≡ upClient l s′ → dnClient l s ≡ dnClient l s′
  → VisLeaves l s s′ → (ConsRecv (phOf l s) → cblkOf l s′ ≡ cblkOf l s)
  → (k : LegPos) → AtPos l k b s → LegInv l s′
prodMove l b s s′ padv re ce cue cde ue de vl cbk lpPreSend (hA , hn , hr , hc) =
  atProdSend l b s s′ hA (prodadv-step padv)
    (λ hs → subst (λ z → SrvHas⁺ z (upSrv l s′)) (sym hA) (vProdSend vl hn hs))
    hn (subst RelayPre re hr) (subst InCp03 ce hc)
prodMove l b s s′ padv re ce cue cde ue de vl cbk lpUpSrv (hb , hp , hr , hc) =
  b , lpUpSrv    , srvKeep (vUpSrvKeep vl) hb
    , padv-sent-mono padv hp , subst RelayPre re hr , subst InCp03 ce hc
prodMove l b s s′ padv re ce cue cde ue de vl cbk lpUpCell (hb , hp , hr , hc) =
  b , lpUpCell   , subst (CellFull⁺ b) cue hb
    , padv-sent-mono padv hp , subst RelayPre re hr , subst InCp03 ce hc
prodMove l b s s′ padv re ce cue cde ue de vl cbk lpUpClient (hb , hp , hr , hc) =
  b , lpUpClient , subst (CliHas⁺ b) ue hb
    , padv-sent-mono padv hp , subst RelayCp3 re hr , subst InCp03 ce hc
prodMove l b s s′ padv re ce cue cde ue de vl cbk lpRelayIn (hIn , hp , hc) =
  b , lpRelayIn  , subst (RelayIn⁺  b) re hIn
    , padv-sent-mono padv hp , subst InCp03 ce hc
prodMove l b s s′ padv re ce cue cde ue de vl cbk lpRelayOut (hOut , hp , hc) =
  b , lpRelayOut , subst (RelayOut⁺ b) re hOut
    , padv-sent-mono padv hp , subst InCp03 ce hc
prodMove l b s s′ padv re ce cue cde ue de vl cbk lpDnSrv (hb , hp , hr , hc) =
  b , lpDnSrv    , srvKeep (vDnSrvKeep vl) hb
    , padv-sent-mono padv hp , subst RelayFwd re hr , subst InCp03 ce hc
prodMove l b s s′ padv re ce cue cde ue de vl cbk lpDnCell (hb , hp , hr , hc) =
  b , lpDnCell   , subst (CellFull⁺ b) cde hb
    , padv-sent-mono padv hp , subst RelayFwd re hr , subst InCp03 ce hc
prodMove l b s s′ padv re ce cue cde ue de vl cbk lpDnClient (hb , hp , hr , hc) =
  b , lpDnClient , subst (CliHas⁺ b) de hb
    , padv-sent-mono padv hp , subst RelayFwd re hr , subst ConsCp3 ce hc
prodMove l b s s′ padv re ce cue cde ue de vl cbk lpDone (hcb , hp , hr , hd) =
  b , lpDone     , trans (cbk hd) hcb
    , padv-sent-mono padv hp , subst RelayFwd re hr , subst ConsRecv ce hd

-- node B/C fired leg `l`'s relay: `lpUpClient` is HOP 4, the two relay slots
-- either keep or FORWARD (HOP 6), the three pre-receive positions need the relay
-- to stay pre-receive (`relayPreKeep`, three different refutations), and the
-- four downstream positions ride `rk-fwd-mono`
relayMove : (l : TwoLegs) (b : Block₃) (s s′ : SysState)
  → RelayStepKind (relayOf l s) (relayOf l s′)
  → prodOf l s ≡ prodOf l s′ → phOf l s ≡ phOf l s′
  → cellUp l s ≡ cellUp l s′ → cellDn l s ≡ cellDn l s′
  → dnClient l s ≡ dnClient l s′
  → (RelayPre (relayOf l s) → RelayHas (relayOf l s′) → BFcHasBlk (upClient l s))
  → (BFcHasBlk (upClient l s) → ProdSent (prodOf l s))
  → NoTwoTokens l s → VisLeaves l s s′
  -- LEAF 8 and HOP 4, both now handed over by the WIDENED `ldRelay` instead of
  -- by `VisLeaves`: the recorded-block fixity, and the receive itself
  → ((RelayPre (relayOf l s) → ⊥) → (bb : Block₃)
     → RelayAt bb (relayOf l s) → RelayAt bb (relayOf l s′))
  → (RelayCp3 (relayOf l s)
     → Σ[ bc ∈ Block₃ ] (upClient l s ≡ bcBlk1 bc) × (relayOf l s′ ≡ consuming bc cp4))
  → (ConsRecv (phOf l s) → cblkOf l s′ ≡ cblkOf l s)
  → (k : LegPos) → AtPos l k b s → LegInv l s′
relayMove l b s s′ rk pe ce cue cde de wUp ucC nt vl blkR recvR cbk lpPreSend (hA , hn , hr , hc) =
  b , lpPreSend  , hA , subst ProdNotSent pe hn
    , relayPreKeep l s s′ rk wUp (λ hcb → prodSent-notSent-⊥ _ (ucC hcb) hn) hr
    , subst InCp03 ce hc
relayMove l b s s′ rk pe ce cue cde de wUp ucC nt vl blkR recvR cbk lpUpSrv (hb , hp , hr , hc) =
  b , lpUpSrv    , srvKeep (vUpSrvKeep vl) hb , subst ProdSent pe hp
    , relayPreKeep l s s′ rk wUp
        (λ hcb → nUpSrvCli nt (srvHas⁺⇒hasBlk b (upSrv l s) hb) hcb) hr
    , subst InCp03 ce hc
relayMove l b s s′ rk pe ce cue cde de wUp ucC nt vl blkR recvR cbk lpUpCell (hb , hp , hr , hc) =
  b , lpUpCell   , subst (CellFull⁺ b) cue hb , subst ProdSent pe hp
    , relayPreKeep l s s′ rk wUp
        (λ hcb → nUpCellCli nt (cellFull⁺⇒fullBlk b (cellUp l s) hb) hcb) hr
    , subst InCp03 ce hc
relayMove l b s s′ rk pe ce cue cde de wUp ucC nt vl blkR recvR cbk lpUpClient (hb , hp , hr , hc) =
  atRelayRecv l b s s′ (recvR hr) hb (subst ProdSent pe hp) (subst InCp03 ce hc)
relayMove l b s s′ rk pe ce cue cde de wUp ucC nt vl blkR recvR cbk lpRelayIn ((hI , eb) , hp , hc) =
  relayHasStep l b s s′ rk vl blkR (relayIn⇒has (relayOf l s) hI)
    (λ hpre → relayPre-in-⊥ (relayOf l s) hpre hI) eb
    (subst ProdSent pe hp) (subst InCp03 ce hc)
relayMove l b s s′ rk pe ce cue cde de wUp ucC nt vl blkR recvR cbk lpRelayOut ((hO , eb) , hp , hc) =
  relayHasStep l b s s′ rk vl blkR (relayOut⇒has (relayOf l s) hO)
    (λ hpre → relayPre-out-⊥ (relayOf l s) hpre hO) eb
    (subst ProdSent pe hp) (subst InCp03 ce hc)
relayMove l b s s′ rk pe ce cue cde de wUp ucC nt vl blkR recvR cbk lpDnSrv (hb , hp , hr , hc) =
  b , lpDnSrv    , srvKeep (vDnSrvKeep vl) hb
    , subst ProdSent pe hp , rk-fwd-mono rk hr , subst InCp03 ce hc
relayMove l b s s′ rk pe ce cue cde de wUp ucC nt vl blkR recvR cbk lpDnCell (hb , hp , hr , hc) =
  b , lpDnCell   , subst (CellFull⁺ b) cde hb
    , subst ProdSent pe hp , rk-fwd-mono rk hr , subst InCp03 ce hc
relayMove l b s s′ rk pe ce cue cde de wUp ucC nt vl blkR recvR cbk lpDnClient (hb , hp , hr , hc) =
  b , lpDnClient , subst (CliHas⁺ b) de hb
    , subst ProdSent pe hp , rk-fwd-mono rk hr , subst ConsCp3 ce hc
relayMove l b s s′ rk pe ce cue cde de wUp ucC nt vl blkR recvR cbk lpDone (hcb , hp , hr , hd) =
  b , lpDone     , trans (cbk hd) hcb
    , subst ProdSent pe hp , rk-fwd-mono rk hr , subst ConsRecv ce hd

-- node D fired leg `l`'s consumer: `lpDnClient` is HOP 9 (fully banked — the
-- `ldCons` SESSION-40/41 anchor hands over the recorded block AND the co-firing
-- client's block), `lpDone` rides `consRecvKeep`, and the seven upstream
-- positions need `InCp03` to survive (`consInKeep`, with the position's own
-- refutation of "D received")
consMove : (l : TwoLegs) (b : Block₃) (s s′ : SysState)
  → ConsAdv (phOf l s) (phOf l s′)
  → (phOf l s ≡ cp3
     → Σ[ b″ ∈ Block₃ ] (cblkOf l s′ ≡ b″) × (dnClient l s ≡ bcBlk1 b″))
  → prodOf l s ≡ prodOf l s′ → relayOf l s ≡ relayOf l s′
  → cellUp l s ≡ cellUp l s′ → cellDn l s ≡ cellDn l s′
  → upClient l s ≡ upClient l s′
  → (InCp03 (phOf l s) → ConsRecv (phOf l s′) → BFcHasBlk (dnClient l s))
  → (BFcHasBlk (dnClient l s) → RelayFwd (relayOf l s))
  → NoTwoTokens l s → VisLeaves l s s′
  → (ConsRecv (phOf l s) → cblkOf l s′ ≡ cblkOf l s)
  → (k : LegPos) → AtPos l k b s → LegInv l s′
consMove l b s s′ cadv anc pe re cue cde ue wDn dcC nt vl cbk lpPreSend (hA , hn , hr , hc) =
  b , lpPreSend  , hA , subst ProdNotSent pe hn , subst RelayPre re hr
    , consInKeep l s s′ (consadv-step cadv) wDn
        (λ hcb → relayPre-fwd-⊥ (relayOf l s) hr (dcC hcb)) hc
consMove l b s s′ cadv anc pe re cue cde ue wDn dcC nt vl cbk lpUpSrv (hb , hp , hr , hc) =
  b , lpUpSrv    , srvKeep (vUpSrvKeep vl) hb , subst ProdSent pe hp , subst RelayPre re hr
    , consInKeep l s s′ (consadv-step cadv) wDn
        (λ hcb → relayPre-fwd-⊥ (relayOf l s) hr (dcC hcb)) hc
consMove l b s s′ cadv anc pe re cue cde ue wDn dcC nt vl cbk lpUpCell (hb , hp , hr , hc) =
  b , lpUpCell   , subst (CellFull⁺ b) cue hb , subst ProdSent pe hp , subst RelayPre re hr
    , consInKeep l s s′ (consadv-step cadv) wDn
        (λ hcb → relayPre-fwd-⊥ (relayOf l s) hr (dcC hcb)) hc
consMove l b s s′ cadv anc pe re cue cde ue wDn dcC nt vl cbk lpUpClient (hb , hp , hr , hc) =
  b , lpUpClient , subst (CliHas⁺ b) ue hb , subst ProdSent pe hp , subst RelayCp3 re hr
    , consInKeep l s s′ (consadv-step cadv) wDn
        (λ hcb → relayPre-fwd-⊥ (relayOf l s) (relayCp3⇒pre (relayOf l s) hr) (dcC hcb)) hc
consMove l b s s′ cadv anc pe re cue cde ue wDn dcC nt vl cbk lpRelayIn ((hI , eb) , hp , hc) =
  b , lpRelayIn  , subst (RelayIn⁺  b) re (hI , eb) , subst ProdSent pe hp
    , consInKeep l s s′ (consadv-step cadv) wDn
        (λ hcb → relayHas-fwd-⊥ (relayOf l s) (relayIn⇒has (relayOf l s) hI) (dcC hcb)) hc
consMove l b s s′ cadv anc pe re cue cde ue wDn dcC nt vl cbk lpRelayOut ((hO , eb) , hp , hc) =
  b , lpRelayOut , subst (RelayOut⁺ b) re (hO , eb) , subst ProdSent pe hp
    , consInKeep l s s′ (consadv-step cadv) wDn
        (λ hcb → relayHas-fwd-⊥ (relayOf l s) (relayOut⇒has (relayOf l s) hO) (dcC hcb)) hc
consMove l b s s′ cadv anc pe re cue cde ue wDn dcC nt vl cbk lpDnSrv (hb , hp , hr , hc) =
  b , lpDnSrv    , srvKeep (vDnSrvKeep vl) hb , subst ProdSent pe hp , subst RelayFwd re hr
    , consInKeep l s s′ (consadv-step cadv) wDn
        (λ hcb → nDnSrvCli nt (srvHas⁺⇒hasBlk b (dnSrv l s) hb) hcb) hc
consMove l b s s′ cadv anc pe re cue cde ue wDn dcC nt vl cbk lpDnCell (hb , hp , hr , hc) =
  b , lpDnCell   , subst (CellFull⁺ b) cde hb , subst ProdSent pe hp , subst RelayFwd re hr
    , consInKeep l s s′ (consadv-step cadv) wDn
        (λ hcb → nDnCellCli nt (cellFull⁺⇒fullBlk b (cellDn l s) hb) hcb) hc
consMove l b s s′ cadv anc pe re cue cde ue wDn dcC nt vl cbk lpDnClient (hb , hp , hr , hc) =
  let e3 : phOf l s ≡ cp3
      e3 = consCp3⇒eq (phOf l s) hc
      (b″ , ecb , ecl) = anc e3
  in  b , lpDone
        , trans ecb (sym (bcBlk1-inj (trans (sym hb) ecl)))
        , subst ProdSent pe hp , subst RelayFwd re hr
        , consAdv-cp3-recv (subst (λ z → ConsAdv z (phOf l s′)) e3 cadv)
consMove l b s s′ cadv anc pe re cue cde ue wDn dcC nt vl cbk lpDone (hcb , hp , hr , hd) =
  b , lpDone     , trans (cbk hd) hcb
    , subst ProdSent pe hp , subst RelayFwd re hr
    , consRecvKeep l s s′ (consadv-step cadv) hd

------------------------------------------------------------------------
-- §10d  THE ARM.  `legStep→legInv` is the `LegInv` mirror of
-- `PipeEvStep.legStep→pres` (`:183-196`): one clause per `LegDriverStep`
-- constructor, each delegating to its ten-position dispatch.  `ldFix` reuses
-- `legFrame` (§8) outright — the position-preserving case is exactly what that
-- was written for.
--
-- The two `PipeInv⁺` clauses it takes (`ucC`/`dcC`) are the ones the green
-- engine already preserves; the assembly threads `LegInv` BESIDE `PipeInv⁺`, so
-- they cost nothing there.
------------------------------------------------------------------------

-- ONE visible api-CSBF step preserves the token-location invariant
legStep→legInv : (l : TwoLegs) (s s′ : SysState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → (BFcHasBlk (upClient l s) → ProdSent (prodOf l s))
  → (BFcHasBlk (dnClient l s) → RelayFwd (relayOf l s))
  → NoTwoTokens l s → VisLeaves l s s′
  → LegDriverStep l s s′ e a → LegValStep l s s′ e a
  → LegInv l s → LegInv l s′
legStep→legInv l s s′ ucC dcC nt vl (ldProd padv re ce cue cde ue de) lv (b , k , at) =
  prodMove l b s s′ padv re ce cue cde ue de vl
    (λ hd → lvCons lv (consRecv⇒held (phOf l s) hd)) k at
legStep→legInv l s s′ ucC dcC nt vl (ldRelay rk pe ce cue cde de upEvo wUp blkR) lv (b , k , at) =
  -- (slice D) `wUp`'s premise is now the DISJUNCTION; `relayMove` wants the
  -- original narrow form, which is the `inj₁` instance.  (slice C) HOP 4 is
  -- `relayRecv-of` applied to the SAME gate, and LEAF 8 is `ldRelay`'s new
  -- ninth field — neither is a `VisLeaves` premise any more.
  relayMove l b s s′ rk pe ce cue cde de
    (λ hPre hHas → proj₁ (wUp (inj₁ (hPre , hHas)))) ucC nt vl
    blkR (relayRecv-of l s s′ wUp)
    (λ hd → lvCons lv (consRecv⇒held (phOf l s) hd)) k at
legStep→legInv l s s′ ucC dcC nt vl (ldCons cadv anc pe re cue cde ue dnEvo wDn) lv (b , k , at) =
  consMove l b s s′ cadv
    (λ e3 → let (b″ , _ , ecb , ecl) = anc e3 in b″ , ecb , ecl)
    pe re cue cde ue wDn dcC nt vl
    (λ hd → lvCons lv (consRecv⇒held (phOf l s) hd)) k at
legStep→legInv l s s′ ucC dcC nt vl (ldFix pe re ce cue cde ue de) lv (b , k , at) =
  legFrame l b s s′ pe re ce
    (λ hd → sym (lvCons lv (consRecv⇒held (phOf l s) hd)))
    (subst (CellFull⁺ b) cue) (subst (CellFull⁺ b) cde)
    (srvKeep (vUpSrvKeep vl)) (srvKeep (vDnSrvKeep vl))
    (subst (CliHas⁺ b) ue) (subst (CliHas⁺ b) de)
    k at


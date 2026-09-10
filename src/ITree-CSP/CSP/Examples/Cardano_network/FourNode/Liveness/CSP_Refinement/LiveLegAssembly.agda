{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- ASSEMBLY campaign (A2/A3) — `LiveLegAssembly`, *** THE JOINT PER-STEP
-- PRESERVATION THEOREM *** at `RState` level.
--
-- WHAT THIS MODULE IS.  Three per-leg invariants were proved preserved SEPARATELY
-- on this branch — the R3 engine's product `PipeInvS` (`PipeInvProd`), the token
-- LOCATION `LegInv` (Task 3, `LiveLegStep`) and the exclusions `TokenExcl` (the
-- TokenExcl campaign, `LiveTokenExcl`) — each at STATE level, each with its
-- `RState` wrapper deliberately deferred to "the assembly" because the wrapper
-- needs the heavy `SysBisim`/`SysOracle`/`SysRoute`/`WalkConvTauInv` layer that
-- the cheap-prefix rule kept out of those modules (`LiveLegStep:77-81`,
-- `LiveTokenExcl:1089-1094`).  THIS is that assembly: one object `LegJoint`, one
-- theorem `legJoint-step`, and the four step classes joined arm by arm.  No
-- invariant content is re-proved here — every arm is the banked state-level arm.
--
-- WHY IT IS A JOIN AND NOT THREE THEOREMS SIDE BY SIDE (finding F2, the
-- EXISTENTIAL-SUCCESSOR RULE).  Every node cone returns its successor
-- existentially, and nothing in the repo makes `absNodesOf`/`absDec` injective
-- (the negative is banked at `PipeNodeAEvo:25`, `WalkBrkFire:277`).  Two peels of
-- two cones on one step therefore land at `s′₁`/`s′₂` with nothing identifying
-- them, so three separate theorems could never be PAIRED along a run: each arm
-- must peel ONCE and emit all three preservation halves at that one successor.
-- That is why `LiveTokenExcl.legJointVis` (visible axis) returns both campaign
-- maps beside the driver step, and why the two io arms below transcribe the frozen
-- `PipeTauIo` `pres` bodies instead of calling them (those `let`-peel the PLAIN io
-- cone; the hoist that would let them be called was priced and DECLINED — a
-- frozen-module edit for ≈70 lines — under the condition that each transcription
-- carries its keep-in-sync anchor, which it does).
--
-- CONTENTS
--   §1  `LegJoint` (= `PipeInvS × LegInv × TokenExcl`) and `legJoint-init`
--   §2  `TauStepJ`/`EvStepJ`/`StepEmitJ` + `stepEmitJ` — `LiveLegStep`'s
--       invariant-generic `Fold` INSTANTIATED (that generalisation was built for
--       this moment; nothing is copied)
--   §3  `plusCli`/`plusSrv` — the ⁺ view of the PAIRED io cone (the missing
--       componentwise `proj₁`, so ONE cone call feeds all three components)
--   §4  `τpreserveJ-med` — the medium-τ class.  CALLS `PipeInvProd.τpreserveS-med`
--       (its successor is COMPUTED, so it reduces) and pairs it with
--       `legInv-drain` + `tokenExcl-drain`
--   §5  `evStepJ` — the visible class: `api-nodes-solo` (inversion only),
--       `evStepJ-api` over slice A1's `legJointVis`, `legInv-break`/
--       `tokenExcl-break` + `evStepJ-break`, and the 16-clause label dispatch
--   §6  the hidden io class: the one-cone-call rule stated, `TauIoJ`, and
--       `tauIoJ-in` (the cell-FILL arm)
--   §7  `tauIoJ-out` (the cell-READ arm, where the token HOPS into its reader), the
--       io label dispatch `tauIoJ`, and the τ dispatch `tauStepJ`.  This section
--       used to sit under a `cellCp3` MODULE PARAMETER; at the cellCp3 window that
--       parameter went and the fact rides the read class's own preservation MAP
--   §8  `legJoint-step` — THE JOINT THEOREM, and what a future FSim `Rel` does
--       with it
--   §6b `LegJoint⁺`/`LegJointB` — the WIDENED invariant (stated before §7 so it
--       carries no `cellCp3`), and `legJointB-init`
--   §9  *** THE FOLD WIDENING *** (LiveStableOffer package (2)): `PipeVal` joined
--       for the BLOCK PIN (F2/G5) and BOTH legs carried in ∀-form (assembly G4).
--       The five widened arms, the two label dispatches, and `legJointB-step` —
--       same premise set as §8's theorem, which since the window is EMPTY
--
-- *** PREMISE SET: EMPTY (the cellCp3 window). ***  It read "`cellCp3` ONLY" — the
-- (C2) reachability fact of §7, in the conditional shape `LiveLegStep`'s own §9
-- states, threaded ONCE as a module parameter and consumed at exactly two sites (the
-- two read dichotomies).  It is now an ARGUMENT of the io READ class's preservation
-- map, at that arm's OWN source state, and `LiveChanJoin.cellCp3-of` discharges it
-- there off the carried join — so nothing in this module is assumed.  `NoTwoTokens` —
-- `LiveLegStep`'s other premise when Task 3 closed — is a COMPONENT of the product
-- this theorem transports.  The PARKED supplier `LiveTokenExcl.cellCp3-of` (the two
-- chain alignments) was NOT the route taken; it stays parked and unused.
--
-- STYLE (each rule with an incident behind it).  `let`, never `with`, at any goal
-- whose type mentions the imported `LegInv`/`TokenExcl`/`CellCp3` (the
-- `blkA`-parameter hazard); all case analysis lives in helpers whose types mention
-- no invariant (`api-nodes-solo`, and the frozen `break-invert`).  Every cone
-- output is re-typed at the arm's own `s′`, whose node components ARE the cone
-- successor's (`PipeTauIo:399`'s banked lesson).  `LiveLegStep` arrives as ONE
-- module application (`LS`).  No postulate, no hole, no meta, no `mutual`, no
-- `NON_TERMINATING`, and NO base-module edit.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Product using ( Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit using () renaming ( ⊤ to ⊤₀ )
open import Data.Unit.Polymorphic using ( tt )
open import Relation.Binary.PropositionalEquality
  using ( _≡_; refl; sym; trans; cong; cong₂; subst )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegAssembly
  (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using
  ( p; apiES; linkAB; linkAC; linkBD; linkCD )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; break
  ; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF; done; input; output
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack ; store; env )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import CSP.Examples.Cardano_network.Base using ( Dir; hi; IDs; N2N_BlockFetch )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _∖_; EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; τ; ev; evl; evLabel; Event )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; τ*-refl )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; initial; mkSys; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( CopyPhase; full; draining; MedState; mkMed; phase; broken; decMed )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA
  using ( NetProc; absNodesOf; nodesOf; lift-med-whole-ev
        ; reflect-top-ev; medEv; nodesEv
        ; reflect-absDec-τ; innerτ; hidSync; reflect-inner-τ; medτ; nodesτ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysReach blkA
  using ( RState; mkR; radec; rdec; toSys; reach; Reachable; rcloseʷ; rcloseʷ-abs )
open Reachable using ( rStepʷ )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_TauCore blkA as STC
open STC using ( phase-upd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( setCell; absNodesOf-no-τ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle blkA
  using ( IsApiCSBF; aicCS; aicBF; aicDone )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysRoute blkA as SR
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj blkA
  using ( noOffer→viewV )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysBisim blkA
  using ( lift-nodes-whole-wev; oevB-no-io; oevB-refute )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkPr blkA
  using ( TwoLegs; legBD; legCD; phOf; InCp03; cblkOf )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvTauInv blkA
  using ( medium-τ-inv-wt )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA
  using ( prodOf; relayOf; cellUp; cellDn; upClient; dnClient
        ; ProdSent; RelayPre; RelayFwd; CellHasBlk )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeNodeIoEvo blkA
  using ( AllCliFacts; AllSrvFacts )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeFillSource blkA
  using ( upLink; dnLink )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvFire blkA
  using ( fill-up-nodes; fill-dn-nodes; nodes-blockfill-hi; srvHit-up; srvHit-dn )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeMedKey blkA
  using ( medium-ev-in-key; medium-ev-out-key )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauMed blkA
  using ( drainSucc )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeTauIo blkA
  using ( legProd; legRelay; legCons; cellUp-key; cellDn-key; atKey; stepAtKey
        ; io-sync-wrun; pipeInv⁺-io-imp; srvIo⇒evo
        ; cellClause-in; cellClause-out; cliClause-in; cliClause-out
        ; pickCliUp; pickCliDn; pickSrvUp; pickSrvDn )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeEvStep blkA
  using ( legStep→pres; legStep→pmono; legStep→rmono
        ; break-invert; frame-break; srvCoupled-break )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvInv blkA
  using ( srvCoupled-pres; upSrv; dnSrv )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInvProd blkA
  using ( PipeInvS; pipeInvS-init; τpreserveS-med )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegInv blkA
  using ( LegInv; legInv-init; CellFull⁺; CliHas⁺; RelayCp3; ConsCp3 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegIoCone blkA
  using ( AllCliP; AllSrvP; facts⁺; frozenCli; frozenSrv; top-nodes-io-evoP⁺ )
import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegStep blkA as LS
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveTokenExcl blkA
  using ( TokenExcl; tokenExcl-init; tokenExcl-drain; tokenExcl-frame; legJointVis
        ; tokenExcl-fill; tokenExcl-read )
-- §9 (the fold widening): the banked BLOCK-VALUE layer.  READ ONLY — no
-- `PipeVal*` module is edited by this campaign.
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValInv blkA
  using ( PipeVal; pipeVal-init; SrvValOK; CellValOK; RelayValOK; ConsDValOK )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFill blkA
  using ( hasBlk⇒isBlk1 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValFire blkA
  using ( nodes-blockfill-val; srvHitVal-up; srvHitVal-dn )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValTauIo blkA
  using ( orElse; plBlk?; srvIoV; cliValIn; cellValIn; cellValOut; cliValOutC
        ; legConsD )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValStep blkA
  using ( τpreserveV-med )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeValEvStep blkA
  using ( legStepV; evStepV-break )
-- (P5) the inert-freeze conjunct and its `refl` seed: ONE permanently non-`Fin`
-- peer (node B's link-AB KA client), which is what refutes a `ret` of the whole
-- abstract decode (`LiveRetFree.absDec-noRet` does the refuting; the conjunct
-- itself lives with the inversion that preserves it)
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveKAFrozen blkA
  using ( KAcFrz; KAcFrz-init )
open import CSP.Examples.Cardano_network.FourNode.Liveness.CSP_Refinement.LiveLegApiExpose blkA
  using ( driverExpose⁺
        -- (T3b) the cone's report is a RECORD; these are the slots this module reads
        ; deSucc; deLdBD; deLdCD; deLvBD; deLvCD; deFrzB )

------------------------------------------------------------------------
-- §1  THE JOINT INVARIANT.
--
-- The three components are the three per-leg objects the campaign proved
-- preservation for, and they must ride TOGETHER for a reason that is structural
-- rather than economical: each one's arms consume the others' facts.
--
--   · `PipeInvS = PipeInv⁺ × SrvCoupled` (`PipeInvProd:109`) is the R3 engine's
--     own product.  Its `Coupled` half is `proj₂ (proj₁ …)` — NO glue is needed
--     to read it — and that half is exactly what `LiveTokenExcl.tokenExcl-vis`
--     and `LiveLegStep.legStep→legInv` demand at a visible api step (the latter
--     as its `ucC`/`dcC` arguments, `LiveLegStep:1628-1629`).
--   · `LegInv` (`LiveLegInv:456`) is the token LOCATION — the Σ-shaped object the
--     liveness argument needs.
--   · `TokenExcl` (`LiveTokenExcl:283`) is what makes the location inductive: its
--     `NoTwoTokens` field is `legStep→legInv`'s remaining per-state premise.
--
-- The SrvCoupled half is not optional either: the io FILL arm's `PipeInv⁺` clause
-- consumes it (`PipeTauIo.tauIo-in`'s `fill-{up,dn}-nodes … sc`).
------------------------------------------------------------------------

-- the object a future FSim `Rel` carries: the R3 engine's own product, the token
-- LOCATION, and the exclusions that make the location inductive
LegJoint : TwoLegs → SysState → Set
LegJoint l s = PipeInvS l s × LegInv l s × TokenExcl l s

-- BASE — all three components hold at `initial`, each by its own banked base case
legJoint-init : (l : TwoLegs) → LegJoint l initial
legJoint-init l = pipeInvS-init l , legInv-init l , tokenExcl-init l

------------------------------------------------------------------------
-- §2  THE THREE PER-STEP COMBINATORS, AT THE JOINT INVARIANT.
--
-- `LiveLegStep`'s §2 `Fold` (`:246`) is generic in the invariant — that
-- generalisation was built for exactly this moment — so the three combinator
-- types and the fine-step fold are instantiations, not copies.  `LegJoint` is
-- `Set`-valued (all three components are), so no level lift is needed.
------------------------------------------------------------------------

-- one hidden τ hop preserves the joint invariant
TauStepJ : TwoLegs → Set₁
TauStepJ l = LS.Fold.TauStepG LegJoint l

-- one strong visible hop preserves the joint invariant
EvStepJ : TwoLegs → Set₁
EvStepJ l = LS.Fold.EvStepG LegJoint l

-- one WEAK visible move preserves the joint invariant
StepEmitJ : TwoLegs → Set₁
StepEmitJ l = LS.Fold.StepEmitG LegJoint l

-- the fine-step fold at the joint invariant (`LiveLegStep.Fold` verbatim)
stepEmitJ : (l : TwoLegs) → TauStepJ l → EvStepJ l → StepEmitJ l
stepEmitJ l = LS.Fold.stepEmitFromG LegJoint l

------------------------------------------------------------------------
-- §3  THE ⁺ VIEW OF THE PAIRED io CONE (design finding F5).
--
-- `LiveLegIoCone` reports the PAIRED families (`AllCliP`/`AllSrvP`, the ⁺ facts
-- BESIDE the frozen ones) and reads the FROZEN halves off them
-- (`frozenCli`/`frozenSrv`, `:789`/`:794`).  The ⁺ halves — which is what
-- `LiveLegStep`'s own io arms consume — had no reading, because `LiveLegStep`
-- calls the ⁺-only cone itself.  The JOINT arms cannot: ONE cone call must serve
-- all three components (F2, the existential-successor rule), and that call is the
-- PAIRED one.  So these two are the missing componentwise `proj₁`s.
--
-- They are stated at `AllCliFacts facts⁺` / `AllSrvFacts facts⁺`, i.e. at the
-- type the ⁺ cone itself returns, so `LiveLegStep`'s four ⁺ selectors
-- (`pickCliUp⁺`/`pickCliDn⁺`/`pickSrvUp⁺`/`pickSrvDn⁺` and their `-H`/`-K`
-- siblings) apply to the result unchanged.
------------------------------------------------------------------------

-- the ⁺ client family, read off the paired one (componentwise `proj₁`)
plusCli : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
        → AllCliP s s′ e a → AllCliFacts facts⁺ s s′ e a
plusCli s s′ e a (c1 , c2 , c3 , c4) = proj₁ c1 , proj₁ c2 , proj₁ c3 , proj₁ c4

-- the ⁺ server family, read off the paired one (the paired server fact is a
-- TRIPLE — ⁺ / frozen / write-ownership — so the ⁺ view is again `proj₁`)
plusSrv : (s s′ : SysState) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
        → AllSrvP s s′ e a → AllSrvFacts facts⁺ s s′ e a
plusSrv s s′ e a (q1 , q2 , q3 , q4) = proj₁ q1 , proj₁ q2 , proj₁ q3 , proj₁ q4

------------------------------------------------------------------------
-- §4  THE MEDIUM-τ CLASS, AT THE JOINT INVARIANT.
--
-- The cheapest of the three step classes, and the one that proves the joint
-- pairing works at all.  It is NOT a mirror of `PipeInvProd.τpreserveS-med`
-- (`:191-212`) — that would duplicate the inversion, the concrete τ-run and the
-- reachability witness.  It CALLS it (the instalment-1 reviewer's repricing):
-- `τpreserveS-med` is `let`-only at a COMPUTED successor
-- (`drainSucc (toSys r) i d₀ id₀`, `PipeTauMed:87`), so its `r′` REDUCES, and a
-- second call of the SAME inversion `medium-τ-inv-wt` here yields the SAME
-- `(i , d₀ , id₀ , x)` projections — syntactically the same neutral terms.  This
-- is exactly the situation the io cones are NOT in (F2): the successor is
-- COMPUTED from the medium, not bound existentially by a cone.
--
--   | half        | discharged by                                              |
--   |-------------|------------------------------------------------------------|
--   | `PipeInvS`  | `τpreserveS-med`'s own map (`drain-preserve` +              |
--   |             | `srvCoupled-drain` inside it)                              |
--   | `LegInv`    | `LiveLegStep.legInv-drain` (`:819`) — its drain hypothesis  |
--   |             | IS `medium-τ-inv-wt`'s `draining` fact, so no glue          |
--   | `TokenExcl` | `LiveTokenExcl.tokenExcl-drain` (`:744`) — the four cell    |
--   |             | equations are `cellUp-key`/`cellDn-key` at the source and   |
--   |             | at `drainSucc` (`phase (med (drainSucc …))` reduces to the  |
--   |             | `phase-upd`/`flipCell` term the lemma asks for), the four   |
--   |             | node equalities are `LiveLegStep.drain-nodes` (`:797`)      |
------------------------------------------------------------------------

-- ONE medium-τ drain preserves the joint invariant, at `RState` level
τpreserveJ-med : (l : TwoLegs) (r : RState) {M M′ : NetProc}
    (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
    (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (LegJoint l (toSys r) → LegJoint l (toSys r′))
τpreserveJ-med l r {M} {M′} ms Meq =
  let (i , d₀ , id₀ , x , drainEq , M′≡) = medium-τ-inv-wt (med (toSys r)) ms
      (r′ , Meq′ , presS) = τpreserveS-med l r ms Meq
      s′ : SysState
      s′ = drainSucc (toSys r) i d₀ id₀
      (_ , _ , _ , _ , use , dse , uce , dce) = LS.drain-nodes l (toSys r) i d₀ id₀
  in  r′ , Meq′
    , λ pj → presS (proj₁ pj)
           , LS.legInv-drain l (toSys r) i d₀ id₀ x drainEq (proj₁ (proj₂ pj))
           , tokenExcl-drain l (toSys r) s′ (med (toSys r)) i d₀ id₀
               (cellUp-key l (toSys r)) (cellDn-key l (toSys r))
               (cellUp-key l s′) (cellDn-key l s′)
               use dse uce dce (proj₂ (proj₂ pj))

------------------------------------------------------------------------
-- §5  THE VISIBLE CLASS, AT THE JOINT INVARIANT.
--
-- Label dispatch verbatim `PipeEvStep.evStepS` (`:503-529`): the twelve
-- impossible classes are payload-INDEPENDENT refutations and transfer unchanged,
-- `break` is a medium solo and `apiCS`/`apiBF`/`done` go through the api arm.
--
-- The api arm is where slice A1's `legJointVis` pays for itself: it peels the ⁺
-- cone ONCE and returns the successor, the `LegDriverStep`, the two server
-- evolutions AND the two campaign preservation maps at that one successor, so
-- this module never peels a cone on the visible axis at all.  The `PipeInvS` half
-- is then the frozen pair (`legStep→pres` + `srvCoupled-pres`) applied to the SAME
-- driver step — which is exactly why the arm passes it out (F2).
------------------------------------------------------------------------

-- INVERSION ONLY (no invariant in this type — the `blkA`/`with` rule): a visible
-- api-CSBF step of `radec r` is a NODES SOLO, since the medium offers no api
-- event (`SysRoute.medium-api-non-offer`).  Kept in its own top-level function
-- for the reason `PipeEvStep.break-invert` is (`:324-328`): all the case analysis
-- lives here, and the arm below is a single `let` at a goal that mentions the
-- imported `LegInv`/`TokenExcl`.
api-nodes-solo : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
                 {M : NetProc}
  → IsApiCSBF e → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ N₁ ∈ NetProc ] (absNodesOf (toSys r) ─[ ev (evl (evLabel X e a)) ]─► N₁)
      × (M ≡ ((decMed (med (toSys r)) ∥⇘ ioES ⇙ N₁) ∖ ioES))
api-nodes-solo r aic step
  with reflect-top-ev (decMed (med (toSys r))) (absNodesOf (toSys r))
         (inj₁ (SR.medium-api-non-offer (med (toSys r)) aic)) step
... | medEv M₁ ms _      = ⊥-elim (SR.medium-api-non-offer (med (toSys r)) aic (M₁ , ms))
... | nodesEv N₁ ns Meq  = N₁ , ns , Meq

-- THE api-CSBF ARM at the joint invariant: ONE `let`, `with`-free by design.
-- The reachable successor is built exactly as `PipeEvStep.reach-ev-driver`
-- (`:252-281`) builds its own — `lift-nodes-whole-wev` under the medium's
-- non-offer, then `rcloseʷ` — and `toSys r′` reduces to `s′` on the nose, which is
-- what lets the three preservation halves be stated at `s′`.
evStepJ-api : (l : TwoLegs) (r : RState)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → IsApiCSBF e → apiES .mem (X , e) a
  → radec r ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (LegJoint l (toSys r) → LegJoint l (toSys r′))
evStepJ-api l r {X} {e} {a} {M} aic apimem step =
  let (N₁ , ns , Meq) = api-nodes-solo r aic step
      (s′ , medEq , N₁≡ , cWeakRun , ld , srvEvo , mapJ)
        = legJointVis l (toSys r) apimem ns
      wrun : rdec r ═[ ev (evl (evLabel X e a)) ]═► ⟦ s′ ⟧
      wrun = subst (λ mm → rdec r ═[ ev (evl (evLabel X e a)) ]═►
                            ((decMed mm ∥⇘ ioES ⇙ nodesOf s′) ∖ ioES))
               medEq
               (lift-nodes-whole-wev (decMed (med (toSys r))) (nodesOf (toSys r))
                 (SR.api∉ioES {X} {e} {a} aic)
                 (noOffer→viewV _ (SR.medium-api-non-offer (med (toSys r)) aic))
                 cWeakRun)
      r′ : RState
      r′ = proj₁ (rcloseʷ r {s′ = s′} wrun)
      Mr : M ≡ radec r′
      Mr = trans Meq
             (trans (cong₂ (λ mm nn → (decMed mm ∥⇘ ioES ⇙ nn) ∖ ioES) medEq N₁≡)
                    (sym (rcloseʷ-abs r {s′ = s′} wrun)))
  in  r′ , Mr
    , λ pj →
        let ((pinv , sc) , li , tex) = pj
            (mapL , tex′) = mapJ (proj₂ pinv) tex
        in  (legStep→pres l (toSys r) s′ ld pinv
            , srvCoupled-pres l (toSys r) s′
                (legStep→pmono l (toSys r) s′ ld) (legStep→rmono l (toSys r) s′ ld)
                (proj₁ srvEvo) (proj₂ srvEvo) sc)
          , mapL li , tex′

-- A `break` MOVES NO NODE and PRESERVES every copy cell (`phase m′ ≡ phase (med s)`,
-- `PipeEvStep.break-invert`), so leg `l`'s ten `LegInv` components are all fixed and
-- the position is rebuilt by `LiveLegStep.legFrame` (`:751`).  Cased on `l` for the
-- same reason `PipeEvStep.frame-break` (`:312`) is: with `l` abstract the slot
-- accessors do not reduce and the two cell `cong`s do not typecheck.
legInv-break : (l : TwoLegs) (s : SysState) (m′ : MedState)
             → phase m′ ≡ phase (med s)
             → LegInv l s → LegInv l (mkSys m′ (nA s) (nB s) (nC s) (nD s))
legInv-break legBD s m′ pheq (b , k , at) =
  LS.legFrame legBD b s (mkSys m′ (nA s) (nB s) (nC s) (nD s))
    refl refl refl (λ _ → refl)
    (subst (CellFull⁺ b) (cong (λ ph → ph linkAB hi N2N_BlockFetch) (sym pheq)))
    (subst (CellFull⁺ b) (cong (λ ph → ph linkBD hi N2N_BlockFetch) (sym pheq)))
    (λ h → h) (λ h → h) (λ h → h) (λ h → h) k at
legInv-break legCD s m′ pheq (b , k , at) =
  LS.legFrame legCD b s (mkSys m′ (nA s) (nB s) (nC s) (nD s))
    refl refl refl (λ _ → refl)
    (subst (CellFull⁺ b) (cong (λ ph → ph linkAC hi N2N_BlockFetch) (sym pheq)))
    (subst (CellFull⁺ b) (cong (λ ph → ph linkCD hi N2N_BlockFetch) (sym pheq)))
    (λ h → h) (λ h → h) (λ h → h) (λ h → h) k at

-- the exclusions across a `break`: the four peer slots are literally equal and
-- both cells are preserved, so `LiveTokenExcl.tokenExcl-frame` (`:379`) applies
-- with the same two `phase`-`cong`s.  Cased on `l` for the same reason
-- `legInv-break` above is.
tokenExcl-break : (l : TwoLegs) (s : SysState) (m′ : MedState)
                → phase m′ ≡ phase (med s)
                → TokenExcl l s → TokenExcl l (mkSys m′ (nA s) (nB s) (nC s) (nD s))
tokenExcl-break legBD s m′ pheq =
  tokenExcl-frame legBD s (mkSys m′ (nA s) (nB s) (nC s) (nD s)) refl refl
    (cong (λ ph → ph linkAB hi N2N_BlockFetch) (sym pheq))
    (cong (λ ph → ph linkBD hi N2N_BlockFetch) (sym pheq)) refl refl
tokenExcl-break legCD s m′ pheq =
  tokenExcl-frame legCD s (mkSys m′ (nA s) (nB s) (nC s) (nD s)) refl refl
    (cong (λ ph → ph linkAC hi N2N_BlockFetch) (sym pheq))
    (cong (λ ph → ph linkCD hi N2N_BlockFetch) (sym pheq)) refl refl

-- THE `break` ARM at the joint: mirror `PipeEvStep.evStepS-break` (`:479-499`)
-- with the third component appended.  It is MIRRORED rather than CALLED (unlike
-- §4's medium-τ arm) because pairing with a call would require reproducing this
-- very `wrun` to name the same successor — the same line count with an extra
-- conversion risk, so the frame halves are applied directly instead.
evStepJ-break : (l : TwoLegs) (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
  → radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (LegJoint l (toSys r) → LegJoint l (toSys r′))
evStepJ-break l r l₀ {a} step =
  let (m′ , medStep , pheq , Meq , _) = break-invert r l₀ {a} step
      s′ : SysState
      s′ = mkSys m′ (nA (toSys r)) (nB (toSys r)) (nC (toSys r)) (nD (toSys r))
      wrun : rdec r ═[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]═► ⟦ s′ ⟧
      wrun = wev τ*-refl
               (lift-med-whole-ev (decMed (med (toSys r))) (nodesOf (toSys r))
                 (SR.break∉ioES {l₀} {a}) medStep
                 (noOffer→viewV _ (SR.nodes-no-break (toSys r))))
               τ*-refl
      r′ : RState
      r′ = proj₁ (rcloseʷ r {s′ = s′} wrun)
  in  r′ , trans Meq (sym (rcloseʷ-abs r {s′ = s′} wrun))
    , λ pj →
        let ((pinv , sc) , li , tex) = pj
        in  (frame-break l (toSys r) m′ pheq pinv
            , srvCoupled-break l (toSys r) m′ sc)
          , legInv-break l (toSys r) m′ pheq li
          , tokenExcl-break l (toSys r) m′ pheq tex

-- THE VISIBLE CLASS, total: `LiveLegStep.Fold.EvStepG` at the joint invariant
evStepJ : (l : TwoLegs) → EvStepJ l
evStepJ l r {evLabel _ (apiCS l₀ d₀ m) a} step = evStepJ-api l r aicCS tt step
evStepJ l r {evLabel _ (apiBF l₀ d₀ m) a} step = evStepJ-api l r aicBF tt step
evStepJ l r {evLabel _ (done  l₀ d₀ id) a} step = evStepJ-api l r aicDone tt step
evStepJ l r {evLabel _ (break l₀) a} step = evStepJ-break l r l₀ step
evStepJ l r {evLabel _ (input  l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
evStepJ l r {evLabel _ (output l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
evStepJ l r {evLabel _ (apiKA l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiKA (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepJ l r {evLabel _ (apiTS l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiTS (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepJ l r {evLabel _ (apiLN l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLN (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepJ l r {evLabel _ (apiLF l₀ d₀ m) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-apiLF (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
evStepJ l r {evLabel _ (sndmsg l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndmsg (med (toSys r))) (SR.absnodes-no-sndmsg (toSys r)) step)
evStepJ l r {evLabel _ (rcvmsg l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvmsg (med (toSys r))) (SR.absnodes-no-rcvmsg (toSys r)) step)
evStepJ l r {evLabel _ (tx     l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-tx (med (toSys r))) (SR.absnodes-no-tx (toSys r)) step)
evStepJ l r {evLabel _ (sndack l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-sndack (med (toSys r))) (SR.absnodes-no-sndack (toSys r)) step)
evStepJ l r {evLabel _ (rcvack l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-rcvack (med (toSys r))) (SR.absnodes-no-rcvack (toSys r)) step)
evStepJ l r {evLabel _ (ack    l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-ack (med (toSys r))) (SR.absnodes-no-ack (toSys r)) step)
evStepJ l r {evLabel _ (store l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-store (med (toSys r))) (SR.absnodes-no-store (toSys r)) step)
evStepJ l r {evLabel _ (env l₀ d₀ id) a} step =
  ⊥-elim (oevB-refute r (SR.medium-no-env (med (toSys r))) (SR.absnodes-no-env (toSys r)) step)

------------------------------------------------------------------------
-- §6  THE HIDDEN io CLASS — the risk locus, and why it is transcribed.
--
-- THE ONE-CONE-CALL RULE (design finding F2, confirmed by the review).  Every
-- node cone binds its successor EXISTENTIALLY, and nothing in the repo makes
-- `absNodesOf` injective (`PipeNodeAEvo:25`, `WalkBrkFire:277` bank the negative),
-- so two peels on one step give `s′₁`/`s′₂` with nothing identifying them.  The
-- joint io arms must therefore make ONE call — and it has to be the PAIRED cone
-- `LiveLegIoCone.top-nodes-io-evoP⁺`, because that is the only one reporting both
-- fact directions at one successor.  Three views come off that one call:
--
--   · `frozenCli`/`frozenSrv` — the SUCCESSOR-directed classifiers (`LiveLegIoCone`
--     §6): what `PipeTauIo`'s clause machinery and `tokenExcl-*` read;
--   · `plusCli`/`plusSrv` (§3 above) — the PREDECESSOR-directed ⁺ facts: what
--     `LiveLegStep`'s ten-position dispatches read;
--   · the paired families THEMSELVES — what `tokenExcl-fill`/`tokenExcl-read` take
--     (they do the frozen reading internally and, for the fill, project the
--     write-ownership answer that no other consumer wants).
--
-- CONSEQUENCE, and it is the honest cost of this campaign: `PipeTauIo.tauIo-in`
-- and `tauIo-out` (FROZEN) CANNOT be called — they `let`-peel the PLAIN io cone
-- inside their own bodies, so their successor is a different existential.  Their
-- `pres` bodies are therefore TRANSCRIBED below against the paired cone's frozen
-- view.  A ≈6-line hoist in `PipeTauIo` (a `tauIo-in-at` taking the cone output)
-- would save ≈70 lines; it was priced, recommended AGAINST by the implementer and
-- DECLINED by the review — a frozen-module edit plus an endpoint rebuild is the
-- worse trade — on the standing condition that each transcription carries the
-- sync anchor written above it.  `legInv-fill`/`legInv-read` are OUR modules but
-- call the ⁺-only cone for the same reason, so their `pres` bodies are
-- transcribed too, from the same public pieces (`fillMove`/`readMove` and the
-- eight selectors), which is why no edit to `LiveLegStep` was needed.
------------------------------------------------------------------------

-- the io-SYNC arm of `TauStepJ`, at the joint invariant (the shape of
-- `PipeInvProd.TauIoS`, spelled out because that one is `PipeInvS`-specific)
TauIoJ : TwoLegs → Set₁
TauIoJ l = (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
           {M₁ N₁ M : NetProc}
         → ioES .mem (X , e) a
         → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁
         → absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁
         → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
         → Σ[ r′ ∈ RState ]
             (M ≡ radec r′) × (LegJoint l (toSys r) → LegJoint l (toSys r′))

-- ONE hidden io-SYNC FILL (`input`: the fired cell goes `empty → full x`) at the
-- JOINT invariant.  The `let` skeleton is `PipeTauIo.tauIo-in`'s (`:369-411`) and
-- `LiveLegStep.legInv-fill`'s (`:618-669`) — they are the SAME skeleton, which is
-- what makes the join possible: ONE cone call, one successor, three `pres` halves.
tauIoJ-in : (l : TwoLegs) (r : RState)
    (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
  → ioES .mem (Payload , input l₀ d₀ id₀) x
  → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► M₁
  → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► N₁
  → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
  → Σ[ r′ ∈ RState ] (M ≡ radec r′) × (LegJoint l (toSys r) → LegJoint l (toSys r′))
tauIoJ-in l r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
  let (srcEmpty , M₁≡) = medium-ev-in-key (med (toSys r)) l₀ d₀ id₀ x sM
      g : Link → Dir → IDs → CopyPhase
      g = phase (med (toSys r))
      m′ : MedState
      m′ = mkMed (phase-upd g l₀ (setCell (g l₀) d₀ id₀ (full x)))
                 (broken (med (toSys r)))
      cone = top-nodes-io-evoP⁺ (toSys r) {Payload} {input l₀ d₀ id₀} {x} {N₁} iomem sN
      s″ : SysState
      s″ = proj₁ cone
      (_ , medEq , N₁≡ , cWeakRun , cliP , srvP
         , epAB , epAC , ecB , ecC , edBD , edCD , _) = cone
      s′ : SysState
      s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
      r′ : RState
      r′ = mkR s′ (rStepʷ (reach r) (io-sync-wrun r m′ s″ iomem sM M₁≡ cWeakRun))
      -- THE THREE VIEWS OF THE ONE CONE CALL (re-typed at the arm's own `s′`,
      -- whose node components ARE `s″`'s — `PipeTauIo:399`'s banked lesson)
      allCli = frozenCli (toSys r) s′ (input l₀ d₀ id₀) x cliP
      allSrv = frozenSrv (toSys r) s′ (input l₀ d₀ id₀) x srvP
      cli⁺   = plusCli   (toSys r) s′ (input l₀ d₀ id₀) x cliP
      srv⁺   = plusSrv   (toSys r) s′ (input l₀ d₀ id₀) x srvP
      -- the four driver fixities, plus the tenth (`cblkOf`) the pin reads
      pe : prodOf l (toSys r) ≡ prodOf l s′
      pe = legProd l epAB epAC
      re : relayOf l (toSys r) ≡ relayOf l s′
      re = legRelay l ecB ecC
      ce : phOf l (toSys r) ≡ phOf l s′
      ce = legCons l edBD edCD
      be : cblkOf l (toSys r) ≡ cblkOf l s′
      be = LS.legCblk l edBD edCD
      -- the leg's own cell is `full x` once the fired key matches it
      fU : (upLink l ≡ l₀) → (hi ≡ d₀) → (N2N_BlockFetch ≡ id₀)
         → cellUp l s′ ≡ full x
      fU = LS.cellFill-eq g (upLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
             (cellUp-key l s′)
      fD : (dnLink l ≡ l₀) → (hi ≡ d₀) → (N2N_BlockFetch ≡ id₀)
         → cellDn l s′ ≡ full x
      fD = LS.cellFill-eq g (dnLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
             (cellDn-key l s′)
      -- an UNREAD cell is untouched by a fill (the fired key's source is `empty`)
      cuK : (b : Block₃) → CellFull⁺ b (cellUp l (toSys r)) → CellFull⁺ b (cellUp l s′)
      cuK b = LS.cellKeep-in (CellFull⁺ b) (λ ()) g (upLink l) hi N2N_BlockFetch
                l₀ d₀ id₀ x (cellUp-key l (toSys r)) (cellUp-key l s′) srcEmpty
      cdK : (b : Block₃) → CellFull⁺ b (cellDn l (toSys r)) → CellFull⁺ b (cellDn l s′)
      cdK b = LS.cellKeep-in (CellFull⁺ b) (λ ()) g (dnLink l) hi N2N_BlockFetch
                l₀ d₀ id₀ x (cellDn-key l (toSys r)) (cellDn-key l s′) srcEmpty
      -- HALF 1 — the R3 engine's own product.  *** verbatim copy of
      -- `PipeTauIo.tauIo-in` pres (`:388-410`) — keep in sync; re-open the
      -- declined `tauIo-in-at` hoist if a third consumer appears. ***  The ONLY
      -- change is that `allCli`/`allSrv` are the FROZEN VIEW of the paired cone
      -- above instead of the plain cone's own binders.
      presS : PipeInvS l (toSys r) → PipeInvS l s′
      presS = λ ps →
        let ((pinv , cuOld , ucOld , cdOld , dcOld) , sc) = ps
        in  pipeInv⁺-io-imp l (toSys r) s′ pe re ce pinv
              (cellClause-in g (upLink l) hi N2N_BlockFetch
                 l₀ d₀ id₀ x (subst ProdSent pe)
                 (cellUp-key l (toSys r)) (cellUp-key l s′)
                 (λ e1 e2 e3 blk → subst ProdSent pe
                    (fill-up-nodes l (toSys r) (stepAtKey (toSys r) e1 e2 e3 sN) blk sc))
                 cuOld)
              (cliClause-in (subst ProdSent pe)
                 (pickCliUp l (toSys r) s′ (input l₀ d₀ id₀) x allCli) ucOld)
              (cellClause-in g (dnLink l) hi N2N_BlockFetch
                 l₀ d₀ id₀ x (subst RelayFwd re)
                 (cellDn-key l (toSys r)) (cellDn-key l s′)
                 (λ e1 e2 e3 blk → subst RelayFwd re
                    (fill-dn-nodes l (toSys r) (stepAtKey (toSys r) e1 e2 e3 sN) blk sc))
                 cdOld)
              (cliClause-in (subst RelayFwd re)
                 (pickCliDn l (toSys r) s′ (input l₀ d₀ id₀) x allCli) dcOld)
          , srvCoupled-pres l (toSys r) s′ (subst ProdSent pe) (subst RelayFwd re)
              (srvIo⇒evo (pickSrvUp l (toSys r) s′ allSrv))
              (srvIo⇒evo (pickSrvDn l (toSys r) s′ allSrv)) sc
      -- HALF 2 — the token LOCATION.  Transcribed from `LiveLegStep.legInv-fill`'s
      -- own `pres` (`:659-668`), fed the ⁺ VIEW of the same cone call.
      -- *** KEEP IN SYNC with that `pres` — this is a TRANSCRIPTION, the same
      -- drift surface HALF 1 above is flagged for; the only intended difference
      -- is the ⁺ view of the PAIRED cone in place of the ⁺-only cone's binders. ***
      presL : LegInv l (toSys r) → LegInv l s′
      presL = λ li →
        let (b , k , at) = li
        in  LS.fillMove l b (toSys r) s′ l₀ d₀ id₀ x pe re ce be (cuK b) (cdK b)
              (LS.pickSrvUp⁺ l (toSys r) s′ l₀ d₀ id₀ x srv⁺)
              (LS.pickSrvDn⁺ l (toSys r) s′ l₀ d₀ id₀ x srv⁺)
              fU fD
              (LS.pickCliUp⁺ l (toSys r) s′ (input l₀ d₀ id₀) x cli⁺)
              (LS.pickCliDn⁺ l (toSys r) s′ (input l₀ d₀ id₀) x cli⁺)
              k at
  in  r′ , trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡)
    -- HALF 3 — the exclusions, PREMISE-FREE and taking the PAIRED families as the
    -- cone output they are (`tokenExcl-fill` does its own frozen reading and
    -- projects the write-ownership answer)
    , λ pj → presS (proj₁ pj) , presL (proj₁ (proj₂ pj))
           , tokenExcl-fill l (toSys r) s′ g l₀ d₀ id₀ x
               (cellUp-key l (toSys r)) (cellDn-key l (toSys r))
               (cellUp-key l s′) (cellDn-key l s′)
               (cliP , srvP) (proj₂ (proj₂ pj))

------------------------------------------------------------------------
-- §6b  THE WIDENED INVARIANT (§9's object, stated here so it is free of §7's
-- `cellCp3` parameter — the future FSim `Rel` and `LiveStableOffer`'s bridge
-- name it, and neither should inherit a premise the OBJECT does not need).
------------------------------------------------------------------------

-- the joint invariant WITH the block pin AND the inert freeze, per leg (F2/G5):
-- `LegInv` binds its block existentially, `PipeVal` is what says that block is
-- `blkA`, and `KAcFrz` — (P5)'s conjunct, TRAILING so every `proj₁`-rooted access
-- in the consumers is unmoved — is what says one peer is permanently non-terminal.  The
-- conjunct is LEG-INDEPENDENT (it is a fact about node B's link-AB bundle, not
-- about a leg); it rides the per-leg product because that is where the fold
-- threads facts, and both legs carry the same proof.
LegJoint⁺ : TwoLegs → SysState → Set
LegJoint⁺ l s = LegJoint l s × PipeVal l s × KAcFrz s

-- BOTH legs at once (G4), in ∀-form over the two-element `TwoLegs`: the object a
-- future FSim `Rel` carries, since `specPos` reads BOTH legs.
-- *** TRAP, named on purpose: the leg index is VESTIGIAL here. ***  It exists only
-- to fit `LiveLegStep.Fold`'s interface (`Inv : TwoLegs → SysState → Set`) and is
-- IGNORED, so `LegJointB legCD s` is the SAME TYPE as `LegJointB legBD s` — every
-- §9 statement fixes it at `legBD` and a reader must not infer a per-leg reading
-- from the index.  The two legs live in the ∀ INSIDE, not in this argument.
LegJointB : TwoLegs → SysState → Set
LegJointB _ s = (l : TwoLegs) → LegJoint⁺ l s

-- BASE: both legs, both components, at `initial`
legJointB-init : (l : TwoLegs) → LegJointB l initial
legJointB-init _ l = legJoint-init l , pipeVal-init l , KAcFrz-init

------------------------------------------------------------------------
-- §7  THE READ ARM AND EVERYTHING DOWNSTREAM OF IT.
--
-- `cellCp3` is (C2)'s reachability bill: a leg whose own cell still holds the
-- UNREAD token has its reader's driver at exactly the pre-`recvBFBlock` phase
-- (`LiveLegStep.CellCp3`, re-derived; its conditional shape takes the reader's
-- pending-phase conjunct and upgrades it to the `cp3` pin).
--
-- *** (D, cellCp3) IT IS NO LONGER A MODULE PREMISE — IT IS AN ARGUMENT OF THE
-- PRESERVATION MAP, AT THE ARM'S OWN SOURCE `r`. ***  This module block used to be
-- `module _ (cellCp3 : (l) (b) (r) → LS.CellCp3 l b r) where`, i.e. a ∀-`RState`
-- assumption, which no supplier can meet: `Reachable`'s `rStepʷ` carries a weak
-- DECODE run, so nothing can induct down to the `SysState` level (the eliminator-free
-- finding), and the honest supplier — `LiveChanJoin.cellCp3-of` — needs the CARRIED
-- join at that very state.  The `ifoBD`/`ifoCD` precedent (`LiveFSim:1276-1277`,
-- Task 4's "THE CARRIED INVARIANT IS AN ARGUMENT OF THE SUPPLIER") is the shape, and
-- the reshape is a premise WEAKENING: the two arms that consume it (`tauIoJ-out` and
-- `tauIoB-out`, the io READ class at the two invariant levels) take it as the FIRST
-- argument of their third Σ component, so `LiveChanJoin`'s wrapper — where the join
-- `f` is in hand — supplies it INSIDE its own `λ f`.  Two consequences, both wanted:
-- the SUCCESSOR of every arm is now premise-free by construction (nothing in `r′`
-- mentions the fact at all), and the eight other definitions of §7-§9 lost an
-- argument they never used.
--
-- The six FOLD-SHAPED assemblies (`tauIoJ`/`tauStepJ`/`legJoint-step` and their §9
-- twins) cannot put it on the map — their maps are `LS.Fold`'s fixed shapes — so they
-- take the ∀-`RState` form explicitly and apply it at their own `r`.  They have no
-- consumers (`LiveFSim` re-does both dispatches itself, `LiveChanJoin` consumes only
-- the five class arms), so nothing downstream inherits that quantifier.
--
-- *** LANDMINE, AND IT IS THE ONE THING TO READ BEFORE APPLYING ANY OF THOSE SIX
-- (`tauIoJ` :850, `tauStepJ` :876, `legJoint-step` :928, `tauIoB` :1247, `tauStepB`
-- :1270, `legJointB-step` :1283 — every one carries the marker `(D-LANDMINE)`). ***
-- The `cc3` they ask for is `(… (r : RState) → LS.CellCp3 l b r)` at EVERY reachable
-- state, and *** THAT QUANTIFIER IS UNSATISFIABLE BY CONSTRUCTION *** — it is precisely
-- the form slice D established no supplier can meet, because `Reachable`'s `rStepʷ`
-- carries a weak DECODE run and nothing can descend from it to the `SysState` level.
-- `LiveChanJoin.cellCp3-of` cannot be passed either: the import runs the other way.
-- It is HARMLESS today only because the two call chains (`tauIoJ → tauStepJ →
-- legJoint-step` and `tauIoB → tauStepB → legJointB-step`) each terminate in a
-- definition NOTHING applies, so these six are conditional statements nobody spends
-- and they weaken nothing.  *** A grower who reaches for `legJointB-step` will hit an
-- obligation that cannot be met and must NOT postulate it: *** give that chain the same
-- treatment the two arms got — move the fact onto the preservation map, at the arm's own
-- `r`, and supply it from the caller where the carried join is in hand.  Deleting the
-- six is the other legitimate answer (they are checked content nothing needs).
------------------------------------------------------------------------

module _ where

  -- ONE hidden io-SYNC READ (`output`: the fired cell goes `full x → draining x`)
  -- at the JOINT invariant.  Skeleton as §6's fill arm; the two differences are
  -- that the CELL clauses are the (C1) HOPS `lpUpCell → lpUpClient` (and its
  -- downstream twin) rather than transports, and that those two hops are the ONE
  -- place `cellCp3` is consumed.
  tauIoJ-out : (l : TwoLegs) (r : RState)
      (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
    → ioES .mem (Payload , output l₀ d₀ id₀) x
    → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► M₁
    → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► N₁
    → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
    → Σ[ r′ ∈ RState ] (M ≡ radec r′)
        × (((b : Block₃) → LS.CellCp3 l b r)
             → LegJoint l (toSys r) → LegJoint l (toSys r′))
  tauIoJ-out l r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
    let (srcFull , M₁≡) = medium-ev-out-key (med (toSys r)) l₀ d₀ id₀ x sM
        g : Link → Dir → IDs → CopyPhase
        g = phase (med (toSys r))
        m′ : MedState
        m′ = mkMed (phase-upd g l₀ (setCell (g l₀) d₀ id₀ (draining x)))
                   (broken (med (toSys r)))
        cone = top-nodes-io-evoP⁺ (toSys r) {Payload} {output l₀ d₀ id₀} {x} {N₁} iomem sN
        s″ : SysState
        s″ = proj₁ cone
        (_ , medEq , N₁≡ , cWeakRun , cliP , srvP
           , epAB , epAC , ecB , ecC , edBD , edCD , _) = cone
        s′ : SysState
        s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
        r′ : RState
        r′ = mkR s′ (rStepʷ (reach r) (io-sync-wrun r m′ s″ iomem sM M₁≡ cWeakRun))
        -- the THREE views of the ONE cone call (§6's rule)
        allCli = frozenCli (toSys r) s′ (output l₀ d₀ id₀) x cliP
        allSrv = frozenSrv (toSys r) s′ (output l₀ d₀ id₀) x srvP
        cli⁺   = plusCli   (toSys r) s′ (output l₀ d₀ id₀) x cliP
        srv⁺   = plusSrv   (toSys r) s′ (output l₀ d₀ id₀) x srvP
        pe : prodOf l (toSys r) ≡ prodOf l s′
        pe = legProd l epAB epAC
        re : relayOf l (toSys r) ≡ relayOf l s′
        re = legRelay l ecB ecC
        ce : phOf l (toSys r) ≡ phOf l s′
        ce = legCons l edBD edCD
        be : cblkOf l (toSys r) ≡ cblkOf l s′
        be = LS.legCblk l edBD edCD
        -- HALF 1 — the R3 engine's own product.  *** verbatim copy of
        -- `PipeTauIo.tauIo-out` pres (`:440-470`) — keep in sync; re-open the
        -- declined `tauIo-out-at` hoist if a third consumer appears. ***  Again the
        -- ONLY change is that `allCli`/`allSrv` are the FROZEN VIEW of the paired
        -- cone rather than the plain cone's own binders.
        presS : PipeInvS l (toSys r) → PipeInvS l s′
        presS = λ ps →
          let ((pinv , cuOld , ucOld , cdOld , dcOld) , sc) = ps
          in  pipeInv⁺-io-imp l (toSys r) s′ pe re ce pinv
                (cellClause-out g (upLink l) hi N2N_BlockFetch
                   l₀ d₀ id₀ x (subst ProdSent pe)
                   (cellUp-key l (toSys r)) (cellUp-key l s′) srcFull cuOld)
                (cliClause-out (upLink l) hi l₀ d₀ id₀ x (subst ProdSent pe)
                   (pickCliUp l (toSys r) s′ (output l₀ d₀ id₀) x allCli)
                   (λ e1 e2 e3 blk → subst ProdSent pe
                      (cuOld (subst CellHasBlk
                                (sym (trans (cellUp-key l (toSys r))
                                       (atKey g (sym e1) (sym e2) (sym e3) srcFull)))
                                blk)))
                   ucOld)
                (cellClause-out g (dnLink l) hi N2N_BlockFetch
                   l₀ d₀ id₀ x (subst RelayFwd re)
                   (cellDn-key l (toSys r)) (cellDn-key l s′) srcFull cdOld)
                (cliClause-out (dnLink l) hi l₀ d₀ id₀ x (subst RelayFwd re)
                   (pickCliDn l (toSys r) s′ (output l₀ d₀ id₀) x allCli)
                   (λ e1 e2 e3 blk → subst RelayFwd re
                      (cdOld (subst CellHasBlk
                                (sym (trans (cellDn-key l (toSys r))
                                       (atKey g (sym e1) (sym e2) (sym e3) srcFull)))
                                blk)))
                   dcOld)
            , srvCoupled-pres l (toSys r) s′ (subst ProdSent pe) (subst RelayFwd re)
                (srvIo⇒evo (pickSrvUp l (toSys r) s′ allSrv))
                (srvIo⇒evo (pickSrvDn l (toSys r) s′ allSrv)) sc
        -- the two READ dichotomies: the cell is untouched, or it IS the read cell
        -- and the token hops into the reader — the ONE place `cellCp3` is used
        -- (transcribed from `LiveLegStep.legInv-read`'s `cuR`/`cdR`, `:1118-1141`)
        -- (D, cellCp3) the fact is now a PARAMETER of the two dichotomies rather than
        -- of the module: `cc` is `LS.CellCp3 l _ r` at this arm's own source state
        cuR : (cc : (b : Block₃) → LS.CellCp3 l b r)
              (b : Block₃) → CellFull⁺ b (cellUp l (toSys r))
            → RelayPre (relayOf l (toSys r))
            → CellFull⁺ b (cellUp l s′)
              ⊎ (CliHas⁺ b (upClient l s′) × RelayCp3 (relayOf l s′))
        cuR cc b = λ h hpre →
          LS.cellRead-out (CellFull⁺ b) g (upLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
            (cellUp-key l (toSys r)) (cellUp-key l s′) srcFull
            (λ e1 e2 e3 hf →
                LS.pickCliUpH l (toSys r) s′ (output l₀ d₀ id₀) x cli⁺
                  e1 e2 e3 b _ _ _ (LS.full-inj hf)
              , subst RelayCp3 re (proj₁ (cc b) h hpre))
            h
        cdR : (cc : (b : Block₃) → LS.CellCp3 l b r)
              (b : Block₃) → CellFull⁺ b (cellDn l (toSys r))
            → InCp03 (phOf l (toSys r))
            → CellFull⁺ b (cellDn l s′)
              ⊎ (CliHas⁺ b (dnClient l s′) × ConsCp3 (phOf l s′))
        cdR cc b = λ h hin →
          LS.cellRead-out (CellFull⁺ b) g (dnLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
            (cellDn-key l (toSys r)) (cellDn-key l s′) srcFull
            (λ e1 e2 e3 hf →
                LS.pickCliDnH l (toSys r) s′ (output l₀ d₀ id₀) x cli⁺
                  e1 e2 e3 b _ _ _ (LS.full-inj hf)
              , subst ConsCp3 ce (proj₂ (cc b) h hin))
            h
        -- HALF 2 — the token LOCATION, off the ⁺ view of the same cone call.
        -- *** KEEP IN SYNC with `LiveLegStep.legInv-read`'s own `pres` — a
        -- TRANSCRIPTION, same drift surface as §6's HALF 2 and HALF 1. ***
        presL : (cc : (b : Block₃) → LS.CellCp3 l b r)
              → LegInv l (toSys r) → LegInv l s′
        presL cc = λ li →
          let (b , k , at) = li
          in  LS.readMove l b (toSys r) s′ pe re ce be (cuR cc b) (cdR cc b)
                (LS.srvKeepIo (upLink l) l₀ d₀ id₀ x
                   (LS.pickSrvUpK l (toSys r) s′ l₀ d₀ id₀ x srv⁺))
                (LS.srvKeepIo (dnLink l) l₀ d₀ id₀ x
                   (LS.pickSrvDnK l (toSys r) s′ l₀ d₀ id₀ x srv⁺))
                (LS.cliKeep (LS.pickCliUp⁺ l (toSys r) s′ (output l₀ d₀ id₀) x cli⁺))
                (LS.cliKeep (LS.pickCliDn⁺ l (toSys r) s′ (output l₀ d₀ id₀) x cli⁺))
                k at
    in  r′ , trans Meq (cong₂ (λ mm nn → (mm ∥⇘ ioES ⇙ nn) ∖ ioES) M₁≡ N₁≡)
      -- HALF 3 — the exclusions: `tokenExcl-read` is premise-free and needs the
      -- source cell's own `full x` fact, which the medium inversion already gave
      , λ cc pj → presS (proj₁ pj) , presL cc (proj₁ (proj₂ pj))
             , tokenExcl-read l (toSys r) s′ g l₀ d₀ id₀ x
                 (cellUp-key l (toSys r)) (cellDn-key l (toSys r))
                 (cellUp-key l s′) (cellDn-key l s′) srcFull
                 (cliP , srvP) (proj₂ (proj₂ pj))

  -- THE io LABEL DISPATCH: only `input`/`output` are in `ioES`, so the other
  -- fourteen `Net_Api` constructors are refuted by the membership witness itself
  -- (mirror `PipeTauIo.tauIo`, `:479-495`)
  -- (D, cellCp3) FOLD-SHAPED, so the fact rides the TELESCOPE (∀-`RState`) and is
  -- applied at this dispatcher's own `r`: `TauIoJ`'s map is `LS.Fold`'s fixed shape
  -- *** (D-LANDMINE) `cc3`'s ∀-`RState` quantifier is UNSATISFIABLE BY CONSTRUCTION —
  -- read §7's header before applying this; do not postulate it. ***
  tauIoJ : (l : TwoLegs)
           (cc3 : (b : Block₃) (r : RState) → LS.CellCp3 l b r) → TauIoJ l
  tauIoJ l cc3 r {e = input  l₀ d₀ id₀} {a = x} iomem sM sN Meq =
    let (r′ , Mr , pres) = tauIoJ-in  l r l₀ d₀ id₀ x iomem sM sN Meq
    in  r′ , Mr , pres
  tauIoJ l cc3 r {e = output l₀ d₀ id₀} {a = x} iomem sM sN Meq =
    let (r′ , Mr , pres) = tauIoJ-out l r l₀ d₀ id₀ x iomem sM sN Meq
    in  r′ , Mr , pres (λ b → cc3 b r)
  tauIoJ l cc3 r {e = sndmsg _ _ _} ()
  tauIoJ l cc3 r {e = rcvmsg _ _ _} ()
  tauIoJ l cc3 r {e = tx     _ _ _} ()
  tauIoJ l cc3 r {e = sndack _ _ _} ()
  tauIoJ l cc3 r {e = rcvack _ _ _} ()
  tauIoJ l cc3 r {e = ack    _ _ _} ()
  tauIoJ l cc3 r {e = done   _ _ _} ()
  tauIoJ l cc3 r {e = apiCS  _ _ _} ()
  tauIoJ l cc3 r {e = apiBF  _ _ _} ()
  tauIoJ l cc3 r {e = apiTS  _ _ _} ()
  tauIoJ l cc3 r {e = apiKA  _ _ _} ()
  tauIoJ l cc3 r {e = apiLN  _ _ _} ()
  tauIoJ l cc3 r {e = apiLF  _ _ _} ()
  tauIoJ l cc3 r {e = break  _}     ()

  -- THE HIDDEN τ CLASS, total: a hidden τ is a medium drain (§4) or an io SYNC
  -- (§6/§7); `absNodesOf` has no autonomous τ.  Dispatch verbatim
  -- `PipeInvProd.tauStepS-from` (`:221-227`)
  -- *** (D-LANDMINE) `cc3` is UNSATISFIABLE BY CONSTRUCTION (§7's header). ***
  tauStepJ : (l : TwoLegs)
             (cc3 : (b : Block₃) (r : RState) → LS.CellCp3 l b r) → TauStepJ l
  tauStepJ l cc3 r stp with reflect-absDec-τ (toSys r) stp
  ... | innerτ P′ innerStep Peq
      with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
  ...   | medτ   M′ ms eqP = τpreserveJ-med l r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
  ...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
  tauStepJ l cc3 r stp | hidSync M₁ N₁ iomem sM sN Peq = tauIoJ l cc3 r iomem sM sN Peq

------------------------------------------------------------------------
-- §8  *** THE JOINT THEOREM. ***
--
-- ONE weak visible move of the REACHABLE system preserves all three components at
-- once.  Unfolded, `legJoint-step l` is
--
--   (r : RState) {e : Event} {t′ : NetProc} → radec r ═[ ev (evl e) ]═► t′
--     → Σ[ r′ ∈ RState ] (t′ ≡ radec r′)
--         × (LegJoint l (toSys r) → LegJoint l (toSys r′))
--
-- which is exactly the object a future `LiveFSim` `Rel` carries along a run: the
-- `Rel` holds `LegJoint l (toSys r)` at the source, this theorem transports it to
-- the successor the same weak move lands at, and `legJoint-init` seeds it at
-- `initial`.  No `Reachable` induction anywhere — preservation is per single step,
-- exactly as for `PipeInvS` (finding F3).
--
-- PREMISE SET: EMPTY.  It read "`cellCp3` ONLY (the enclosing `module _`)" until the
-- cellCp3 window; `legJoint-step` now takes that fact as an explicit ∀-`RState`
-- argument (it is fold-shaped, so it cannot ride a map) and has no consumer at all.
-- Nothing else: the four step classes' arms take step-local equations, cone outputs
-- and the invariant's own components, and `NoTwoTokens` — which was `LiveLegStep`'s
-- second premise — is now the `TokenExcl` component this very product carries.
--
-- HOW THE NEXT CAMPAIGN CONSUMES IT (`LiveFSim`, not in this scope).  The `Rel`
-- carries the PAIR `(r , LegJoint l (toSys r))`: `legJoint-init` seeds it at
-- `initial`, and this theorem is the INVARIANT HALF of the forward clause —
-- "the related tree makes a weak visible move ⇒ there is an INVARIANT-PRESERVING
-- successor" — with the successor delivered as an `RState`, so its `Reachable`
-- witness travels along and no `Reachable` induction is ever needed.
-- *** CORRECTION, booked as assembly gap G1 and confirmed by `LiveFSim`
-- instalment 1: it is NOT the forward clause. ***  `FSimFromRel`'s `fwdE`/`fwdT`
-- (`Semantics/BisimFromRel.agda:99-102`) additionally owe the SPEC successor and
-- its weak move (gap G2), and they consume the two STRONG classes — at the
-- WIDENED invariant, i.e. §9's `evStepB`/`tauStepB`, since the `Rel` carries
-- `LegJointB` — not this weak-move fold at all.  The fold remains the right
-- object for any walk-level consumer.  The `t′ ≡ radec r′` component is what lets the `Rel`
-- be stated on TREES rather than on states, which is the shape every bridge in
-- `Semantics/` consumes.  A WALK-level fold, if one is wanted later, is the banked
-- shape `PipeInvProd.pipeInvS-along-walk′` (invariant-parametric in the same way
-- §2's `Fold` is) — deliberately NOT built here.
------------------------------------------------------------------------

  -- ONE weak visible move of the reachable system preserves the joint invariant
  -- *** (D-LANDMINE) `cc3` is UNSATISFIABLE BY CONSTRUCTION, and this definition has
  -- NO CONSUMER — so the theorem is a conditional nobody spends (§7's header). ***
  legJoint-step : (l : TwoLegs)
                  (cc3 : (b : Block₃) (r : RState) → LS.CellCp3 l b r) → StepEmitJ l
  legJoint-step l cc3 = stepEmitJ l (tauStepJ l cc3) (evStepJ l)

------------------------------------------------------------------------
-- §9  *** THE FOLD WIDENING *** — the BLOCK PIN (F2/G5) and BOTH-LEGS
-- CARRIAGE (G4), the two gaps `LiveStableOffer` parked.
--
-- WHY THE PIN CANNOT BE CHEAPER (the route the review asked to try first).
-- `LiveStableOffer`'s parked premises are `AtPos leg lpDnClient blkA` — at the
-- SPEC's block — while `LegInv l s = Σ[ b ] Σ[ k ] AtPos l k b s` binds the block
-- EXISTENTIALLY.  The cheap route ("read `b ≡ blkA` off value-tightness without
-- joining the component") is DEAD for a structural reason, machine-visible in two
-- places: (i) every value fact is stated as a POSITIVE clause of `PipeVal`
-- (`PipeValInv:25-31` records WHY — the payload predicates occur NEGATIVELY inside
-- `Coupled`/`SrvCoupled`, so strengthening those weakens them), hence no
-- state-local combination of `PipeInvS`/`LegInv`/`TokenExcl` implies it; and
-- (ii) the four token-hop lemmas all RETURN `LegInv l s′` (`LiveLegStep:549`,
-- `:761`, `:1028`, `:1632`), i.e. they re-hide the block, so identity with the
-- source block is not recoverable downstream either.  Value-tightness is an
-- INVARIANT: it has to be carried.  So `PipeVal` joins the product — which is what
-- `LiveStableOffer:95-103` already declared as its fifth gap.
--
-- WHY THE JOIN IS CHEAP ANYWAY, AND THE MEASURED FINDING BEHIND IT.  F2 (no
-- `absDec` injectivity) was expected to force new peels for both widenings.  It
-- does not: *** every arm of §4-§7 is a SINGLE-CLAUSE `let`-only definition whose
-- successor mentions no leg, so `proj₁ (arm l …)` DELTA-REDUCES to a leg-free term
-- and the leg-instantiated successors are CONVERTIBLE — `refl`-checked as a probe
-- before this section was written. ***  Three consequences, all measured:
--   · the banked `PipeVal` medium-τ arm (`PipeValStep.τpreserveV-med:167`) and
--     `break` arm (`PipeValEvStep.evStepV-break:411`) build their successors by the
--     SAME terms §4/§5 do, so they are CALLED, not transcribed (`refl`-checked);
--   · the visible api arm needs only `legStepV` (`PipeValEvStep:331`) fed the `ld`
--     and `lv` of `driverExpose⁺` (`LiveLegApiExpose`) — the SAME application `legJointVis` peels via
--     `driverExpose⁺-at` (`refl`-checked), i.e. G2's "same-application trick" at
--     the value layer; that arm is the one place a leg CASE is needed (see it);
--   · only the two io arms are transcribed, because `PipeValTauIo.tauIoV-in/-out`
--     `let`-peel the PLAIN cone (`top-nodes-io-evo`) while §6/§7 peel the PAIRED
--     one — the §6 situation exactly, and the same hoist trade was declined.
--
-- G4 IS THEN A RESTATEMENT, NOT A CONSTRUCTION.  `LegJointB` carries BOTH legs in
-- ∀-form (`specPos` reads both legs, assembly finding G4), and each arm's map is
-- `λ f l → …` at the ONE successor the `legBD` instance names.  No second peel
-- anywhere: every `arm l` call below is the same application as the `arm legBD`
-- call that named the successor.
--
-- PREMISE SET UNCHANGED, i.e. EMPTY since the window (it read "`cellCp3` only").
-- `PipeVal`'s own preservation is
-- UNCONDITIONAL — §9 consumes its component ARMS (`τpreserveV-med`,
-- `evStepV-break`, `legStepV`), NOT the assembled fold `PipeValEvStep.stepEmitVᶠ`,
-- which could not be used here at all (two folds name two successors) — so the
-- widening adds no premise;
-- §9 sat inside the `cellCp3` parameter merely because §7's read arm did.
------------------------------------------------------------------------

  -- the medium-τ class at the widened invariant: §4's arm per leg, paired with the
  -- banked value arm at the SAME successor (`τpreserveV-med`'s `drainSucc` term IS
  -- §4's — `refl`-checked)
  τpreserveB-med : (r : RState) {M M′ : NetProc}
      (ms  : decMed (med (toSys r)) ─[ τ ]─► M′)
      (Meq : M ≡ ((M′ ∥⇘ ioES ⇙ absNodesOf (toSys r)) ∖ ioES))
    → Σ[ r′ ∈ RState ] (M ≡ radec r′)
        × (LegJointB legBD (toSys r) → LegJointB legBD (toSys r′))
  τpreserveB-med r ms Meq =
    let (r′ , Meq′ , _) = τpreserveJ-med legBD r ms Meq
    in  r′ , Meq′
      , λ f l → proj₂ (proj₂ (τpreserveJ-med l r ms Meq)) (proj₁ (f l))
              , proj₂ (proj₂ (τpreserveV-med l r ms Meq)) (proj₁ (proj₂ (f l)))
              -- (P5): a medium-τ successor keeps all four node records LITERALLY
              , proj₂ (proj₂ (f l))

  -- MEASURED EXCEPTION TO THE CONVERTIBILITY FINDING, and the reason this arm is
  -- CASED ON THE LEG: `driverExpose⁺-at` (`LiveLegApiExpose:1081`; §10's header is `:1068`) is the ONE piece
  -- in the chain that PATTERN-MATCHES on the leg, so `proj₁ (evStepJ-api l …)` is
  -- STUCK for an abstract `l` and the two legs' successors are convertible only
  -- once `l` is a constructor (`[UnequalTerms] s′ != driverExpose⁺ … .proj₁` —
  -- the error this shape was written to answer; that is the `Σ`-era spelling, and
  -- since T3b the same term prints as `driverExpose⁺ … .deSucc`).  With `l` concrete both clauses
  -- reduce to the SAME `driverExpose⁺` peel, which is exactly the "both legs from
  -- one peel" the assembly review prescribed for G4: `ldBD`/`lvBD` and
  -- `ldCD`/`lvCD` come out of ONE application here.
  evStepB-api-at : (l : TwoLegs) (r : RState)
      {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
      (aic : IsApiCSBF e) (apimem : apiES .mem (X , e) a)
      (step : radec r ─[ ev (evl (evLabel X e a)) ]─► M)
    → LegJoint⁺ l (toSys r)
    → LegJoint⁺ l (toSys (proj₁ (evStepJ-api legBD r aic apimem step)))
  evStepB-api-at legBD r aic apimem step (j , pv , frz) =
    let (N₁ , ns , _) = api-nodes-solo r aic step
        de = driverExpose⁺ (toSys r) apimem ns
    in  proj₂ (proj₂ (evStepJ-api legBD r aic apimem step)) j
      , legStepV legBD r (deSucc de) step (deLdBD de) (deLvBD de) pv
      -- (P5): `driverExpose⁺`'s `deFrzB` slot, at THIS label's CS/BF/`done` witness
      , deFrzB de aic frz
  evStepB-api-at legCD r aic apimem step (j , pv , frz) =
    let (N₁ , ns , _) = api-nodes-solo r aic step
        de = driverExpose⁺ (toSys r) apimem ns
    in  proj₂ (proj₂ (evStepJ-api legCD r aic apimem step)) j
      , legStepV legCD r (deSucc de) step (deLdCD de) (deLvCD de) pv
      , deFrzB de aic frz

  -- the visible api class at the widened invariant: §5's arm per leg, with the
  -- value half delegated to the leg-cased helper above
  evStepB-api : (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
      {M : NetProc}
    → IsApiCSBF e → apiES .mem (X , e) a
    → radec r ─[ ev (evl (evLabel X e a)) ]─► M
    → Σ[ r′ ∈ RState ] (M ≡ radec r′)
        × (LegJointB legBD (toSys r) → LegJointB legBD (toSys r′))
  evStepB-api r {X} {e} {a} {M} aic apimem step =
    let (r′ , Mr , _) = evStepJ-api legBD r aic apimem step
    in  r′ , Mr , λ f l → evStepB-api-at l r aic apimem step (f l)

  -- the `break` class at the widened invariant: §5's arm per leg, paired with the
  -- banked value frame at the SAME successor (`refl`-checked)
  evStepB-break : (r : RState) (l₀ : Link) {a : ⊤₀} {M : NetProc}
    → radec r ─[ ev (evl (evLabel ⊤₀ (break l₀) a)) ]─► M
    → Σ[ r′ ∈ RState ] (M ≡ radec r′)
        × (LegJointB legBD (toSys r) → LegJointB legBD (toSys r′))
  evStepB-break r l₀ {a} step =
    let (r′ , Mr , _) = evStepJ-break legBD r l₀ step
    in  r′ , Mr
      , λ f l → proj₂ (proj₂ (evStepJ-break l r l₀ step)) (proj₁ (f l))
              , proj₂ (proj₂ (evStepV-break l r l₀ step)) (proj₁ (proj₂ (f l)))
              -- (P5): so does a `break` successor (it moves the medium only)
              , proj₂ (proj₂ (f l))

  -- THE VISIBLE CLASS at the widened invariant: label dispatch verbatim §5's
  evStepB : LS.Fold.EvStepG LegJointB legBD
  evStepB r {evLabel _ (apiCS l₀ d₀ m) a} step = evStepB-api r aicCS tt step
  evStepB r {evLabel _ (apiBF l₀ d₀ m) a} step = evStepB-api r aicBF tt step
  evStepB r {evLabel _ (done  l₀ d₀ id) a} step = evStepB-api r aicDone tt step
  evStepB r {evLabel _ (break l₀) a} step = evStepB-break r l₀ step
  evStepB r {evLabel _ (input  l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
  evStepB r {evLabel _ (output l₀ d₀ id) a} step = ⊥-elim (oevB-no-io r tt step)
  evStepB r {evLabel _ (apiKA l₀ d₀ m) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-apiKA (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
  evStepB r {evLabel _ (apiTS l₀ d₀ m) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-apiTS (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
  evStepB r {evLabel _ (apiLN l₀ d₀ m) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-apiLN (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
  evStepB r {evLabel _ (apiLF l₀ d₀ m) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-apiLF (med (toSys r))) (SR.absnodes-no-nonCSBF (toSys r) tt (λ ())) step)
  evStepB r {evLabel _ (sndmsg l₀ d₀ id) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-sndmsg (med (toSys r))) (SR.absnodes-no-sndmsg (toSys r)) step)
  evStepB r {evLabel _ (rcvmsg l₀ d₀ id) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-rcvmsg (med (toSys r))) (SR.absnodes-no-rcvmsg (toSys r)) step)
  evStepB r {evLabel _ (tx     l₀ d₀ id) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-tx (med (toSys r))) (SR.absnodes-no-tx (toSys r)) step)
  evStepB r {evLabel _ (sndack l₀ d₀ id) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-sndack (med (toSys r))) (SR.absnodes-no-sndack (toSys r)) step)
  evStepB r {evLabel _ (rcvack l₀ d₀ id) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-rcvack (med (toSys r))) (SR.absnodes-no-rcvack (toSys r)) step)
  evStepB r {evLabel _ (ack    l₀ d₀ id) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-ack (med (toSys r))) (SR.absnodes-no-ack (toSys r)) step)
  evStepB r {evLabel _ (store l₀ d₀ id) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-store (med (toSys r))) (SR.absnodes-no-store (toSys r)) step)
  evStepB r {evLabel _ (env l₀ d₀ id) a} step =
    ⊥-elim (oevB-refute r (SR.medium-no-env (med (toSys r))) (SR.absnodes-no-env (toSys r)) step)

  -- THE io FILL class at the widened invariant.  §6's arm per leg for the three
  -- carried halves; the value half is *** a verbatim copy of
  -- `PipeValTauIo.tauIoV-in`'s `pres` (`:272-308`) — keep in sync ***, with the
  -- ONLY change that `allCli`/`allSrv` are the FROZEN VIEW of §6's PAIRED cone
  -- (the same application, hence the same successor) instead of the plain cone's
  -- own binders.  Re-open the declined `tauIoV-in-at` hoist if a third consumer
  -- appears.
  tauIoB-in : (r : RState)
      (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
    → ioES .mem (Payload , input l₀ d₀ id₀) x
    → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► M₁
    → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (input l₀ d₀ id₀) x)) ]─► N₁
    → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
    → Σ[ r′ ∈ RState ] (M ≡ radec r′)
        × (LegJointB legBD (toSys r) → LegJointB legBD (toSys r′))
  tauIoB-in r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
    let (rB , eqB , _) = tauIoJ-in legBD r l₀ d₀ id₀ x iomem sM sN Meq
        g : Link → Dir → IDs → CopyPhase
        g = phase (med (toSys r))
        m′ : MedState
        m′ = mkMed (phase-upd g l₀ (setCell (g l₀) d₀ id₀ (full x)))
                   (broken (med (toSys r)))
        cone = top-nodes-io-evoP⁺ (toSys r) {Payload} {input l₀ d₀ id₀} {x} {N₁} iomem sN
        s″ : SysState
        s″ = proj₁ cone
        (_ , _ , _ , _ , cliP , srvP
           , epAB , epAC , ecB , ecC , edBD , edCD
           -- (T5, grant #11) the inert group is no longer the cone's LAST
           -- component, so it is destructured as a GROUP and the new CS-server pair
           -- rides in the trailing wildcard
           , (_ , _ , frzB , _ , _ , _ , _ , _) , _) = cone
        s′ : SysState
        s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
        allCli = frozenCli (toSys r) s′ (input l₀ d₀ id₀) x cliP
        allSrv = frozenSrv (toSys r) s′ (input l₀ d₀ id₀) x srvP
        presV : (l : TwoLegs) → PipeVal l (toSys r) → PipeVal l s′
        presV l = λ pv →
          let (h1 , h2 , h3 , h4 , h5 , h6 , h7 , h8) = pv
              -- the leg's UPSTREAM fill: route to the leg's own sender, read its
              -- block off clause (1) and pin the written payload to it
              fillUp : (upLink l ≡ l₀) → (hi ≡ d₀) → (N2N_BlockFetch ≡ id₀)
                     → CellValOK (full x)
              fillUp e1 e2 e3 = orElse (plBlk? x) (λ pb →
                let stp = stepAtKey (toSys r) e1 e2 e3 sN
                    (b , eqpos) = hasBlk⇒isBlk1 (upSrv l (toSys r))
                                    (srvHit-up l (toSys r)
                                      (nodes-blockfill-hi (toSys r) stp pb))
                    pineq = srvHitVal-up l (toSys r) b x
                              (nodes-blockfill-val (toSys r) b stp pb) eqpos
                in  subst (λ z → CellValOK (full z)) (sym pineq)
                      (subst SrvValOK eqpos h1))
              -- … and the DOWNSTREAM fill, off clause (5)
              fillDn : (dnLink l ≡ l₀) → (hi ≡ d₀) → (N2N_BlockFetch ≡ id₀)
                     → CellValOK (full x)
              fillDn e1 e2 e3 = orElse (plBlk? x) (λ pb →
                let stp = stepAtKey (toSys r) e1 e2 e3 sN
                    (b , eqpos) = hasBlk⇒isBlk1 (dnSrv l (toSys r))
                                    (srvHit-dn l (toSys r)
                                      (nodes-blockfill-hi (toSys r) stp pb))
                    pineq = srvHitVal-dn l (toSys r) b x
                              (nodes-blockfill-val (toSys r) b stp pb) eqpos
                in  subst (λ z → CellValOK (full z)) (sym pineq)
                      (subst SrvValOK eqpos h5))
          in  srvIoV (pickSrvUp l (toSys r) s′ allSrv) h1
            , cellValIn g (upLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
                (cellUp-key l (toSys r)) (cellUp-key l s′) fillUp h2
            , cliValIn (pickCliUp l (toSys r) s′ (input l₀ d₀ id₀) x allCli) h3
            , subst RelayValOK (legRelay l ecB ecC) h4
            , srvIoV (pickSrvDn l (toSys r) s′ allSrv) h5
            , cellValIn g (dnLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
                (cellDn-key l (toSys r)) (cellDn-key l s′) fillDn h6
            , cliValIn (pickCliDn l (toSys r) s′ (input l₀ d₀ id₀) x allCli) h7
            , subst ConsDValOK (legConsD l edBD edCD) h8
    in  rB , eqB
      , λ f l → proj₂ (proj₂ (tauIoJ-in l r l₀ d₀ id₀ x iomem sM sN Meq)) (proj₁ (f l))
              , presV l (proj₁ (proj₂ (f l)))
              -- (P5): the io cone's THIRD inert slot is node B's link-AB bundle
              , frzB (proj₂ (proj₂ (f l)))

  -- THE io READ class at the widened invariant.  §7's arm per leg; the value half
  -- is *** a verbatim copy of `PipeValTauIo.tauIoV-out`'s `pres` (`:333-371`) —
  -- keep in sync ***, again with the paired cone's frozen view in place of the
  -- plain cone's binders.  The reader's own key IS the leg's cell, so the two
  -- `read*` helpers hand the reader the block value the cell clause carries.
  tauIoB-out : (r : RState)
      (l₀ : Link) (d₀ : Dir) (id₀ : IDs) (x : Payload) {M₁ N₁ M : NetProc}
    → ioES .mem (Payload , output l₀ d₀ id₀) x
    → decMed (med (toSys r)) ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► M₁
    → absNodesOf (toSys r)   ─[ ev (evl (evLabel Payload (output l₀ d₀ id₀) x)) ]─► N₁
    → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
    → Σ[ r′ ∈ RState ] (M ≡ radec r′)
        × (((l : TwoLegs) (b : Block₃) → LS.CellCp3 l b r)
             → LegJointB legBD (toSys r) → LegJointB legBD (toSys r′))
  tauIoB-out r l₀ d₀ id₀ x {M₁} {N₁} {M} iomem sM sN Meq =
    let (rB , eqB , _) = tauIoJ-out legBD r l₀ d₀ id₀ x iomem sM sN Meq
        (srcFull , M₁≡) = medium-ev-out-key (med (toSys r)) l₀ d₀ id₀ x sM
        g : Link → Dir → IDs → CopyPhase
        g = phase (med (toSys r))
        m′ : MedState
        m′ = mkMed (phase-upd g l₀ (setCell (g l₀) d₀ id₀ (draining x)))
                   (broken (med (toSys r)))
        cone = top-nodes-io-evoP⁺ (toSys r) {Payload} {output l₀ d₀ id₀} {x} {N₁} iomem sN
        s″ : SysState
        s″ = proj₁ cone
        (_ , _ , _ , _ , cliP , srvP
           , epAB , epAC , ecB , ecC , edBD , edCD
           -- (T5, grant #11) the inert group is no longer the cone's LAST
           -- component, so it is destructured as a GROUP and the new CS-server pair
           -- rides in the trailing wildcard
           , (_ , _ , frzB , _ , _ , _ , _ , _) , _) = cone
        s′ : SysState
        s′ = mkSys m′ (nA s″) (nB s″) (nC s″) (nD s″)
        allCli = frozenCli (toSys r) s′ (output l₀ d₀ id₀) x cliP
        allSrv = frozenSrv (toSys r) s′ (output l₀ d₀ id₀) x srvP
        presV : (l : TwoLegs) → PipeVal l (toSys r) → PipeVal l s′
        presV l = λ pv →
          let (h1 , h2 , h3 , h4 , h5 , h6 , h7 , h8) = pv
              readUp : (l₀ ≡ upLink l) → (d₀ ≡ hi) → (id₀ ≡ N2N_BlockFetch)
                     → CellValOK (full x)
              readUp e1 e2 e3 =
                subst CellValOK
                  (trans (cellUp-key l (toSys r))
                         (atKey g (sym e1) (sym e2) (sym e3) srcFull))
                  h2
              readDn : (l₀ ≡ dnLink l) → (d₀ ≡ hi) → (id₀ ≡ N2N_BlockFetch)
                     → CellValOK (full x)
              readDn e1 e2 e3 =
                subst CellValOK
                  (trans (cellDn-key l (toSys r))
                         (atKey g (sym e1) (sym e2) (sym e3) srcFull))
                  h6
          in  srvIoV (pickSrvUp l (toSys r) s′ allSrv) h1
            , cellValOut g (upLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
                (cellUp-key l (toSys r)) (cellUp-key l s′) srcFull h2
            , cliValOutC (upLink l) hi l₀ d₀ id₀ x
                (pickCliUp l (toSys r) s′ (output l₀ d₀ id₀) x allCli) readUp h3
            , subst RelayValOK (legRelay l ecB ecC) h4
            , srvIoV (pickSrvDn l (toSys r) s′ allSrv) h5
            , cellValOut g (dnLink l) hi N2N_BlockFetch l₀ d₀ id₀ x
                (cellDn-key l (toSys r)) (cellDn-key l s′) srcFull h6
            , cliValOutC (dnLink l) hi l₀ d₀ id₀ x
                (pickCliDn l (toSys r) s′ (output l₀ d₀ id₀) x allCli) readDn h7
            , subst ConsDValOK (legConsD l edBD edCD) h8
    in  rB , eqB
      -- (D, cellCp3) the fact arrives HERE, per leg, from `LiveChanJoin`'s own `λ f`
      , λ cc f l → proj₂ (proj₂ (tauIoJ-out l r l₀ d₀ id₀ x iomem sM sN Meq))
                     (cc l) (proj₁ (f l))
              , presV l (proj₁ (proj₂ (f l)))
              -- (P5): ditto on the READ side
              , frzB (proj₂ (proj₂ (f l)))

  -- the io-SYNC arm of the widened τ class (the shape of §6's `TauIoJ`)
  TauIoB : Set₁
  TauIoB = (r : RState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
           {M₁ N₁ M : NetProc}
         → ioES .mem (X , e) a
         → decMed (med (toSys r)) ─[ ev (evl (evLabel X e a)) ]─► M₁
         → absNodesOf (toSys r)   ─[ ev (evl (evLabel X e a)) ]─► N₁
         → M ≡ ((M₁ ∥⇘ ioES ⇙ N₁) ∖ ioES)
         → Σ[ r′ ∈ RState ] (M ≡ radec r′)
             × (LegJointB legBD (toSys r) → LegJointB legBD (toSys r′))

  -- THE io LABEL DISPATCH at the widened invariant (mirror §7's `tauIoJ`)
  -- (D, cellCp3) fold-shaped, as §7's `tauIoJ`: the fact rides the telescope
  -- *** (D-LANDMINE) `cc3` is UNSATISFIABLE BY CONSTRUCTION (§7's header). ***
  tauIoB : (cc3 : (l : TwoLegs) (b : Block₃) (r : RState) → LS.CellCp3 l b r) → TauIoB
  tauIoB cc3 r {e = input  l₀ d₀ id₀} {a = x} iomem sM sN Meq =
    let (r′ , Mr , pres) = tauIoB-in  r l₀ d₀ id₀ x iomem sM sN Meq
    in  r′ , Mr , pres
  tauIoB cc3 r {e = output l₀ d₀ id₀} {a = x} iomem sM sN Meq =
    let (r′ , Mr , pres) = tauIoB-out r l₀ d₀ id₀ x iomem sM sN Meq
    in  r′ , Mr , pres (λ l b → cc3 l b r)
  tauIoB cc3 r {e = sndmsg _ _ _} ()
  tauIoB cc3 r {e = rcvmsg _ _ _} ()
  tauIoB cc3 r {e = tx     _ _ _} ()
  tauIoB cc3 r {e = sndack _ _ _} ()
  tauIoB cc3 r {e = rcvack _ _ _} ()
  tauIoB cc3 r {e = ack    _ _ _} ()
  tauIoB cc3 r {e = done   _ _ _} ()
  tauIoB cc3 r {e = apiCS  _ _ _} ()
  tauIoB cc3 r {e = apiBF  _ _ _} ()
  tauIoB cc3 r {e = apiTS  _ _ _} ()
  tauIoB cc3 r {e = apiKA  _ _ _} ()
  tauIoB cc3 r {e = apiLN  _ _ _} ()
  tauIoB cc3 r {e = apiLF  _ _ _} ()
  tauIoB cc3 r {e = break  _}     ()

  -- THE HIDDEN τ CLASS at the widened invariant (dispatch verbatim §7's `tauStepJ`)
  -- *** (D-LANDMINE) `cc3` is UNSATISFIABLE BY CONSTRUCTION (§7's header). ***
  tauStepB : (cc3 : (l : TwoLegs) (b : Block₃) (r : RState) → LS.CellCp3 l b r)
           → LS.Fold.TauStepG LegJointB legBD
  tauStepB cc3 r stp with reflect-absDec-τ (toSys r) stp
  ... | innerτ P′ innerStep Peq
      with reflect-inner-τ (decMed (med (toSys r))) (absNodesOf (toSys r)) innerStep
  ...   | medτ   M′ ms eqP = τpreserveB-med r ms (trans Peq (cong (λ z → z ∖ ioES) eqP))
  ...   | nodesτ N′ ns eqP = ⊥-elim (absNodesOf-no-τ (toSys r) ns)
  tauStepB cc3 r stp | hidSync M₁ N₁ iomem sM sN Peq = tauIoB cc3 r iomem sM sN Peq

  -- *** THE WIDENED JOINT THEOREM ***  one weak visible move of the reachable
  -- system preserves, at ONE successor, BOTH legs' token location, exclusions,
  -- `PipeInvS` AND block-value pin.  The leg index of `LegJointB` is ignored (both
  -- instances are the same type), so it is fixed at `legBD` here.
  -- *** (D-LANDMINE) `cc3` is UNSATISFIABLE BY CONSTRUCTION, and this definition has
  -- NO CONSUMER — the fold `LiveFSim` actually uses is its own (`fwdT-*`/`fwdE-*`
  -- through `LCJ.*`), never this one.  Read §7's header before applying it; the fix is
  -- slice D's reshape (fact onto the map), never a postulate. ***
  legJointB-step : (cc3 : (l : TwoLegs) (b : Block₃) (r : RState) → LS.CellCp3 l b r)
                 → LS.Fold.StepEmitG LegJointB legBD
  legJointB-step cc3 = LS.Fold.stepEmitFromG LegJointB legBD (tauStepB cc3) evStepB

------------------------------------------------------------------------
-- FALSIFICATION NOTES for §9 (arity-preserving mutations; each was applied,
-- built to completion and reverted byte-identically — anchors are §9's own).
--
-- (M2) In `evStepB-api-at`'s `legCD` clause (`:950-955`) feed `legStepV` the
--      OTHER leg's driver/value steps (`ldBD`/`lvBD` for `ldCD`/`lvCD`).
--      *** RED as predicted ***: `:955.34-38: error: [UnequalTerms] legBD !=
--      legCD of type TwoLegs … when checking that the expression ldBD has type
--      … LegDriverStep blkA legCD (toSys r) s′ e a`, EXIT=42.  So the both-legs
--      carriage really is leg-CORRECT and not merely leg-shaped: one peel serves
--      two legs, but each leg's own components are load-bearing.
-- (M3) In `tauIoB-in`'s `fillDn` (`:1058-1068`) read the value off clause (1)
--      (the UP server, `h1`) instead of clause (5) (`h5`).
--      *** RED as predicted ***: `:1068.45-47: error: [UnequalTerms] (upSrv l
--      (toSys r)) != (dnSrv l (RState.sys r)) … when checking that the
--      expression h1 has type SrvValOK (dnSrv l (RState.sys r))`, EXIT=42.  So
--      the transcription's slot routing (which of the leg's two servers wrote
--      the fired payload) is machine-checked, not assumed.
-- (F116) In `tauIoB-out`'s map (`:1226-1228`, the cellCp3 window's own reshape) feed
--      the window fact at `legBD` — the leg that NAMED the successor — instead of at
--      `l`, the leg being mapped.  Both are `TwoLegs` and the map's own `λ f l` reads
--      `f l` correctly beside it, so a reader could plausibly write it.
--      *** RED as predicted ***: `:1223.23-31: error: [UnequalTerms] cellUp l (toSys r)
--      != phase (med (RState.sys r)) linkAB hi N2N_BlockFetch of type CopyPhase … when
--      checking that the expression cc legBD has type (b : Block₃) → LS.CellCp3 l b r`,
--      EXIT=42.  So the (M2) finding holds for the WINDOW carry as well: one peel serves
--      two legs, but the per-leg fact must be read at the leg it is about.  Reverted by
--      string inversion.
-- A third mutation, on the PIN itself, lives with the pin
-- (`LiveStableOffer`'s §9 notes).
------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the BUNDLE-level BF-CLIENT EVOLUTION exposer
-- (`Praos.PipeBundleEvo`).
--
-- `PipeEvDriverCone.driverExpose`'s peel sites consume the R2 bundle
-- inversion `SysIoLink6.absBundleG-api-prod`, whose result `bgEB … bfc′ …`
-- DROPS how the bundle's BF-client slot evolved — exactly the witness the
-- receive-coupling `pres-relay`/`pres-cons` glue needs (session-25 gap).
-- THIS module rebuilds that inversion ONCE, maximally provisioned: the
-- result `bgEB⁺` carries everything `bgEB` carried PLUS the CLIENT-EVOLUTION
-- disjunct
--
--     (bfc ≡ bfc′)  ⊎  (BFcHasBlk bfc′ → ⊥)
--
-- i.e. either the BF client did not fire (its slot is LITERAL — true for the
-- 5 non-BF protocols and for a BF-server fire), or it fired VISIBLY and its
-- successor is ¬-block (a BF client ENTERS `bcBlk1` only via a hidden io
-- delivery, never on a visible api step).
--
-- Structure (all mirrors of green R2 code, base modules READ-ONLY):
--   · `decBFc-apiBF-succ⁺`  — isolated-client decode for `apiBFev l′ d′ m`
--     fires: successor + concrete weak run + `¬ BFcHasBlk` (mirror of
--     `SysIoLink5.decBFc-ev-prod-abs` / `bfc-hstep` restricted to api tags;
--     the three enabled fires land `bcReq1`/`bcDone1`/`bcSil stStreaming`,
--     all ¬-block; every other (phase, tag) refutes by `nothing-absurd`).
--   · `decBFc-doneBF-absurd` — a BF client never offers `doneBF`.
--   · `absBundleBF-ev-evo`  — the 12-peer `Par-ev-elim` cascade (mirror of
--     `absBundleBF-ev-prod`), generic in `e₁`, routing the isolated client
--     fire through a caller DECODE callback (so the successor and the ¬-block
--     fact come from ONE decode — no determinism matching), and folding the
--     result back into the bundle successor exactly as `finishBFc-ev-abs`/
--     `finishBFs-ev-abs` do.
--   · `absBundleG-api-evo`  — the 7-protocol api dispatcher (mirror of
--     `absBundleG-api-prod`): non-BF protocols reuse the frozen per-protocol
--     exposers (their results keep `bfc` LITERAL ⇒ `inj₁ refl`); `apiBF`/BF
--     `done` route through `absBundleBF-ev-evo`.
--
-- No postulate/hole/meta.  Base modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Maybe using ( just; nothing )
open import Data.Maybe.Properties using ( just-injective )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; cong; trans; sym; _≢_ )

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; N2N_ChainSync; N2N_BlockFetch; N2N_KeepAlive; N2N_TxSubmission; N2N_LeiosNotify; N2N_LeiosFetch )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Link; ApiBFTag; ApiBFCar
  ; sendBFRequestRange; sendBFClientDone; sendBFStartBatch; sendBFNoBlocks
  ; sendBFBlock; sendBFBatchDone; recvBFBlock; reqBFRange
  ; apiCS; apiBF; apiKA; apiTS; apiLN; apiLF; done; input; output
  ; sndmsg; rcvmsg; tx; sndack; rcvack; ack; break )
open import CSP.Examples.Cardano_network.Data p using ( Payload; DecEq-ChainRange )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( decBlock )
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιCS; ιBF; ιKA; ιTS; ιLN; ιLF )
open import Class.DecEq using ( _≟_ )
import Class.DecEq.Instances as DecEqI

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; τ*-refl; τ*-step )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _⦀_ ) renaming ( ∅ES to ∅ESa )

import CSP.Examples.Cardano_network.ChainSync p as CS
import CSP.Examples.Cardano_network.BlockFetch p as BF
import CSP.Examples.Cardano_network.KeepAlive p as KA
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.LeiosNotify p as LN
import CSP.Examples.Cardano_network.LeiosFetch p as LF

import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using
  ( NetProc; absBundleG; absKAc; absKAs; absCSc; absCSs; absBFc; absBFs
  ; absTSc; absTSs; absLNc; absLNs; absLFc; absLFs
  ; coarsenBFc; decBFc-sil-step; coarsenBFs; decBFs-sil-step )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN using
  ( CScPos; CSsPos; BFcPos; BFsPos; InertPos; kac; kas; tsc; tss; lnc; lns; lfc; lfs
  ; bundleG; decKAc; decKAs; decCSc; decCSs; decBFc; decBFs
  ; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
  ; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA using
  ( tableSpec-ev-inv; nothing-absurd )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA using
  ( noOffer→viewV
  ; decKAc-noOffer; decKAs-noOffer; ιKA⁻¹∘ιBF
  ; decCSc-noBFgen; decCSs-noBFgen; decBFc-dir-noOffer
  ; bfTail-bfs-noOffer; bfTail-tsc-noOffer
  ; absKAc-noBF; absKAs-noBF; absCSc-noBF; absCSs-noBF; absTSc-noBF; absTSs-noBF
  ; absLNc-noBF; absLNs-noBF; absLFc-noBF; absLFs-noBF
  ; absBFs-dir-noBoth )
-- SysIoLink6 re-exports SysIoLink5 publicly; take everything through one alias
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA as SIL6
open SIL6 using
  ( Tbfc; mkMbfc; bfc-fire-req; bfc-fire-cdone; bfc-fire-blk1
  ; Tbfs; mkMbfs
  ; bfs-fire-req1; bfs-fire-done1; bfs-fire-start; bfs-fire-noblk; bfs-fire-blk; bfs-fire-batch
  ; decBFs-ev-prod-abs; absBFc-ev-dir; absBFs-ev-dir
  ; ⦀-wev-L; ⦀-wev-R
  ; BundleCSEvR-abs; bcscEB; bcssEB
  ; BundleKAEvR-abs; bkacEB; bkasEB
  ; BundleTSEvR-abs; btscEB; btssEB
  ; BundleLNEvR-abs; blncEB; blnsEB
  ; BundleLFEvR-abs; blfcEB; blfsEB
  ; absBundleCS-ev-prod; absBundleKA-ev-prod; absBundleTS-ev-prod
  ; absBundleLN-ev-prod; absBundleLF-ev-prod )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeInv blkA using
  ( BFcHasBlk )

------------------------------------------------------------------------
-- ISOLATED-CLIENT DECODE (api tags).  A visible `apiBFev l′ d′ m` fire out of
-- a BF client at phase `pos` lands at a successor `pos′` that is ¬-block, with
-- the concrete weak run and the abstract successor equality.  Mirror of
-- `decBFc-ev-prod-abs` restricted to the api tags: the enabled (phase, tag)
-- pairs are (idle-head, sendBFRequestRange) → `bcReq1`, (idle-head,
-- sendBFClientDone) → `bcDone1`, (`bcBlk1`, recvBFBlock) → `bcSil stStreaming`;
-- everything else refutes by the table (`nothing-absurd`).
------------------------------------------------------------------------

decBFc-apiBF-succ⁺ : (l : Link) (d : Dir) (pos : BFcPos)
    {l′ : Link} {d′ : Dir} {m : ApiBFTag} {a : ApiBFCar m} {M : NetProc}
  → absBFc l d pos ─[ ev (evl (evLabel (ApiBFCar m) (ιBF (BF.apiBFev l′ d′ m)) a)) ]─► M
  → Σ[ pos′ ∈ BFcPos ]
      (decBFc l d pos ═[ ev (evl (evLabel (ApiBFCar m) (ιBF (BF.apiBFev l′ d′ m)) a)) ]═► decBFc l d pos′)
      × (M ≡ absBFc l d pos′) × (BFcHasBlk pos′ → ⊥)
-- idle head: the two client sends fire (mirror `bfc-hstep` stIdle)
decBFc-apiBF-succ⁺ l d (bcHead BF.stIdle) {l′} {d′} {m = sendBFRequestRange} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bcReq1 a
      , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfc-fire-req l d a)) τ*-refl
      , mkMbfc l d (bcReq1 a) Meq (just-injective (sym ceq))
      , (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcHead BF.stIdle) {l′} {d′} {m = sendBFClientDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bcDone1
      , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfc-fire-cdone l d)) τ*-refl
      , mkMbfc l d bcDone1 Meq (just-injective (sym ceq))
      , (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcHead BF.stIdle) {m = sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcHead BF.stIdle) {m = sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcHead BF.stIdle) {m = sendBFBlock} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcHead BF.stIdle) {m = sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcHead BF.stIdle) {m = recvBFBlock} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcHead BF.stIdle) {m = reqBFRange} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- idle sil: same two fires, τ-prefixed by the sil loop-back
decBFc-apiBF-succ⁺ l d (bcSil BF.stIdle) {l′} {d′} {m = sendBFRequestRange} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bcReq1 a
      , wev (τ*-step (decBFc-sil-step l d BF.stIdle) τ*-refl)
            (SIL6.RFBF.renameMap-ev-fwd (bfc-fire-req l d a)) τ*-refl
      , mkMbfc l d (bcReq1 a) Meq (just-injective (sym ceq))
      , (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcSil BF.stIdle) {l′} {d′} {m = sendBFClientDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bcDone1
      , wev (τ*-step (decBFc-sil-step l d BF.stIdle) τ*-refl)
            (SIL6.RFBF.renameMap-ev-fwd (bfc-fire-cdone l d)) τ*-refl
      , mkMbfc l d bcDone1 Meq (just-injective (sym ceq))
      , (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcSil BF.stIdle) {m = sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcSil BF.stIdle) {m = sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcSil BF.stIdle) {m = sendBFBlock} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcSil BF.stIdle) {m = sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcSil BF.stIdle) {m = recvBFBlock} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcSil BF.stIdle) {m = reqBFRange} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- non-idle head/sil states: the table has NO api row (tag-abstract refutation)
decBFc-apiBF-succ⁺ l d (bcHead BF.stBusy) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcHead BF.stStreaming) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcHead BF.stDone) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcSil BF.stBusy) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcSil BF.stStreaming) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcSil BF.stDone) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- wire-wait phases: the table has NO api row (tag-abstract refutation)
decBFc-apiBF-succ⁺ l d (bcReq1 r) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d bcDone1 step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc bcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- has-block phase: ONLY `recvBFBlock` fires (mirror `decBFc-ev-prod-abs`)
decBFc-apiBF-succ⁺ l d (bcBlk1 b) {m = sendBFRequestRange} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcBlk1 b) {m = sendBFClientDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcBlk1 b) {m = sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcBlk1 b) {m = sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcBlk1 b) {m = sendBFBlock} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcBlk1 b) {m = sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcBlk1 b) {l′} {d′} {m = recvBFBlock} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl with _≟_ ⦃ decBlock ⦄ a b
...     | yes refl =
          bcSil BF.stStreaming
        , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfc-fire-blk1 l d b)) τ*-refl
        , mkMbfc l d (bcSil BF.stStreaming) Meq (just-injective (sym ceq))
        , (λ ())
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcBlk1 b) {m = recvBFBlock} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcBlk1 b) {m = recvBFBlock} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFc-apiBF-succ⁺ l d (bcBlk1 b) {m = reqBFRange} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- a BF CLIENT never offers `doneBF` (the client table has no done row)
decBFc-doneBF-absurd : (l : Link) (d : Dir) (pos : BFcPos)
    {l′ : Link} {d′ : Dir} {a : _} {M : NetProc}
  → absBFc l d pos ─[ ev (evl (evLabel _ (ιBF (BF.doneBF l′ d′)) a)) ]─► M → ⊥
decBFc-doneBF-absurd l d (bcHead BF.stIdle) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = nothing-absurd ceq
decBFc-doneBF-absurd l d (bcHead BF.stBusy) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = nothing-absurd ceq
decBFc-doneBF-absurd l d (bcHead BF.stStreaming) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = nothing-absurd ceq
decBFc-doneBF-absurd l d (bcHead BF.stDone) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = nothing-absurd ceq
decBFc-doneBF-absurd l d (bcSil BF.stIdle) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stIdle)) step
... | q′ , ceq , Meq = nothing-absurd ceq
decBFc-doneBF-absurd l d (bcSil BF.stBusy) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stBusy)) step
... | q′ , ceq , Meq = nothing-absurd ceq
decBFc-doneBF-absurd l d (bcSil BF.stStreaming) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stStreaming)) step
... | q′ , ceq , Meq = nothing-absurd ceq
decBFc-doneBF-absurd l d (bcSil BF.stDone) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcSil BF.stDone)) step
... | q′ , ceq , Meq = nothing-absurd ceq
decBFc-doneBF-absurd l d (bcReq1 r) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = nothing-absurd ceq
decBFc-doneBF-absurd l d bcDone1 step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc bcDone1) step
... | q′ , ceq , Meq = nothing-absurd ceq
decBFc-doneBF-absurd l d (bcBlk1 b) step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = nothing-absurd ceq

------------------------------------------------------------------------
-- ISOLATED-SERVER DECODE (api tags) — the SERVER twin (session-26b, the
-- `FillSource` invariant substrate).  A BF server HOLDS a block exactly at
-- `bsBlk1` (waiting to wire-send it), which it ENTERS only via the api
-- `sendBFBlock` fire (`stStreaming → bsBlk1`).  So a visible `apiBFev` fire
-- out of a server lands ¬-block — UNLESS the tag is `sendBFBlock`, in which
-- case the LABEL PIN + the `bsBlk1 b″` successor equality are carried (the
-- consumer ties the label to the co-firing produce driver's `a56`).
------------------------------------------------------------------------

-- a BF server peer HOLDS a block (is at `bsBlk1`, about to wire-send it)
BFsHasBlk : BFsPos → Set
BFsHasBlk (bsHead _)   = ⊥
BFsHasBlk (bsReq1 _)   = ⊥
BFsHasBlk bsDone1      = ⊥
BFsHasBlk bsStart1     = ⊥
BFsHasBlk bsNoBlk1     = ⊥
BFsHasBlk (bsBlk1 _)   = ⊤
BFsHasBlk bsBatchDone1 = ⊥
BFsHasBlk (bsSil _)    = ⊥

-- the server-successor block classification: ¬-block, or ENTERED `bsBlk1` via
-- the `sendBFBlock` api fire (label pin + successor equality)
BfsSucc : (l : Link) (d : Dir) (bfs′ : BFsPos) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) → Set₁
BfsSucc l d bfs′ {X} e a =
    (BFsHasBlk bfs′ → ⊥)
  ⊎ (Σ[ b″ ∈ Block₃ ] (evLabel X e a ≡ evLabel Block₃ (apiBF l d sendBFBlock) b″)
       × (bfs′ ≡ bsBlk1 b″))

-- an `apiBFev l′ d′ m` fire out of `absBFs l d bfs`: successor + concrete weak
-- run + abstract equality + the block classification (mirror of
-- `decBFs-ev-prod-abs`/`bfs-hstep` restricted to the api tags)
decBFs-apiBF-succ⁺ : (l : Link) (d : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {m : ApiBFTag} {a : ApiBFCar m} {M : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel (ApiBFCar m) (ιBF (BF.apiBFev l′ d′ m)) a)) ]─► M
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l d bfs ═[ ev (evl (evLabel (ApiBFCar m) (ιBF (BF.apiBFev l′ d′ m)) a)) ]═► decBFs l d bfs′)
      × (M ≡ absBFs l d bfs′) × BfsSucc l d bfs′ (ιBF (BF.apiBFev l′ d′ m)) a
-- idle / done heads: no api row (tag-abstract refutation)
decBFs-apiBF-succ⁺ l d (bsHead BF.stIdle) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stDone) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stIdle) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stDone) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- busy head: the two batch-opening api sends fire (mirror `bfs-hstep` stBusy)
decBFs-apiBF-succ⁺ l d (bsHead BF.stBusy) {l′} {d′} {m = sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsStart1
      , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-start l d)) τ*-refl
      , mkMbfs l d bsStart1 Meq (just-injective (sym ceq))
      , inj₁ (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stBusy) {l′} {d′} {m = sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsNoBlk1
      , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-noblk l d)) τ*-refl
      , mkMbfs l d bsNoBlk1 Meq (just-injective (sym ceq))
      , inj₁ (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stBusy) {m = sendBFRequestRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stBusy) {m = sendBFClientDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stBusy) {m = sendBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stBusy) {m = sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stBusy) {m = recvBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stBusy) {m = reqBFRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- streaming head: `sendBFBlock` ENTERS `bsBlk1` (the block arm); `sendBFBatchDone` closes
decBFs-apiBF-succ⁺ l d (bsHead BF.stStreaming) {l′} {d′} {m = sendBFBlock} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsBlk1 a
      , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-blk l d a)) τ*-refl
      , mkMbfs l d (bsBlk1 a) Meq (just-injective (sym ceq))
      , inj₂ (a , refl , refl)
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stStreaming) {l′} {d′} {m = sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsBatchDone1
      , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-batch l d)) τ*-refl
      , mkMbfs l d bsBatchDone1 Meq (just-injective (sym ceq))
      , inj₁ (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stStreaming) {m = sendBFRequestRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stStreaming) {m = sendBFClientDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stStreaming) {m = sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stStreaming) {m = sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stStreaming) {m = recvBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsHead BF.stStreaming) {m = reqBFRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- sil states: same as the heads, τ-prefixed by the sil loop-back
decBFs-apiBF-succ⁺ l d (bsSil BF.stBusy) {l′} {d′} {m = sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsStart1
      , wev (τ*-step (decBFs-sil-step l d BF.stBusy) τ*-refl)
            (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-start l d)) τ*-refl
      , mkMbfs l d bsStart1 Meq (just-injective (sym ceq))
      , inj₁ (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stBusy) {l′} {d′} {m = sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsNoBlk1
      , wev (τ*-step (decBFs-sil-step l d BF.stBusy) τ*-refl)
            (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-noblk l d)) τ*-refl
      , mkMbfs l d bsNoBlk1 Meq (just-injective (sym ceq))
      , inj₁ (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stBusy) {m = sendBFRequestRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stBusy) {m = sendBFClientDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stBusy) {m = sendBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stBusy) {m = sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stBusy) {m = recvBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stBusy) {m = reqBFRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stStreaming) {l′} {d′} {m = sendBFBlock} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsBlk1 a
      , wev (τ*-step (decBFs-sil-step l d BF.stStreaming) τ*-refl)
            (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-blk l d a)) τ*-refl
      , mkMbfs l d (bsBlk1 a) Meq (just-injective (sym ceq))
      , inj₂ (a , refl , refl)
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stStreaming) {l′} {d′} {m = sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsBatchDone1
      , wev (τ*-step (decBFs-sil-step l d BF.stStreaming) τ*-refl)
            (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-batch l d)) τ*-refl
      , mkMbfs l d bsBatchDone1 Meq (just-injective (sym ceq))
      , inj₁ (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stStreaming) {m = sendBFRequestRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stStreaming) {m = sendBFClientDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stStreaming) {m = sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stStreaming) {m = sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stStreaming) {m = recvBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsSil BF.stStreaming) {m = reqBFRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- `bsReq1 r`: ONLY `reqBFRange` fires (the driver-notification gate)
decBFs-apiBF-succ⁺ l d (bsReq1 r) {l′} {d′} {m = reqBFRange} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl with _≟_ ⦃ DecEq-ChainRange ⦄ a r
...     | yes refl =
          bsSil BF.stBusy
        , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-req1 l d r)) τ*-refl
        , mkMbfs l d (bsSil BF.stBusy) Meq (just-injective (sym ceq))
        , inj₁ (λ ())
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsReq1 r) {m = reqBFRange} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsReq1 r) {m = reqBFRange} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsReq1 r) {m = sendBFRequestRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsReq1 r) {m = sendBFClientDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsReq1 r) {m = sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsReq1 r) {m = sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsReq1 r) {m = sendBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsReq1 r) {m = sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsReq1 r) {m = recvBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- wire-wait / done phases: no api row (tag-abstract refutation)
decBFs-apiBF-succ⁺ l d bsDone1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d bsStart1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsStart1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d bsNoBlk1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsNoBlk1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d (bsBlk1 b) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-apiBF-succ⁺ l d bsBatchDone1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsBatchDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- a `doneBF` fire out of a BF server: only `bsDone1` fires (→ `bsSil stDone`,
-- ¬-block); every other phase refutes
decBFs-doneBF-succ⁺ : (l : Link) (d : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {a : _} {M : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel _ (ιBF (BF.doneBF l′ d′)) a)) ]─► M
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l d bfs ═[ ev (evl (evLabel _ (ιBF (BF.doneBF l′ d′)) a)) ]═► decBFs l d bfs′)
      × (M ≡ absBFs l d bfs′) × BfsSucc l d bfs′ (ιBF (BF.doneBF l′ d′)) a
decBFs-doneBF-succ⁺ l d bsDone1 {l′} {d′} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsDone1) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsSil BF.stDone
      , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-done1 l d)) τ*-refl
      , mkMbfs l d (bsSil BF.stDone) Meq (just-injective (sym ceq))
      , inj₁ (λ ())
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d (bsHead BF.stIdle) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d (bsHead BF.stBusy) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d (bsHead BF.stStreaming) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d (bsHead BF.stDone) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d (bsSil BF.stIdle) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d (bsSil BF.stBusy) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d (bsSil BF.stStreaming) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d (bsSil BF.stDone) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsSil BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d (bsReq1 r) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d bsStart1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsStart1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d bsNoBlk1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsNoBlk1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d (bsBlk1 b) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-doneBF-succ⁺ l d bsBatchDone1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsBatchDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

------------------------------------------------------------------------
-- The BF bundle inversion WITH client AND server evolution.  Mirror of
-- `BundleBFEvR-abs`/`finishBFc-ev-abs`/`finishBFs-ev-abs`/
-- `absBundleBF-ev-prod`, with the client / server fire decoded by
-- caller-supplied callbacks (so each successor and its block fact are produced
-- by ONE decode) and both facts carried in the result.
------------------------------------------------------------------------

-- the caller-supplied isolated-client decode: successor + concrete weak run +
-- abstract equality + ¬-block
BFcDecode : (l : Link) (cl : Dir) (bfc : BFcPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) (a : X) → Set₁
BFcDecode l cl bfc {X} e₁ a =
  ∀ {P′ : NetProc} → absBFc l cl bfc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → Σ[ bfc′ ∈ BFcPos ]
      (decBFc l cl bfc ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFc l cl bfc′)
      × (P′ ≡ absBFc l cl bfc′) × (BFcHasBlk bfc′ → ⊥)

-- the caller-supplied isolated-server decode: successor + concrete weak run +
-- abstract equality + the block classification (`BfsSucc`)
BFsDecode : (l : Link) (sv : Dir) (bfs : BFsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) (a : X) → Set₁
BFsDecode l sv bfs {X} e₁ a =
  ∀ {P′ : NetProc} → absBFs l sv bfs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l sv bfs ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFs l sv bfs′)
      × (P′ ≡ absBFs l sv bfs′) × BfsSucc l sv bfs′ (ιBF e₁) a

-- which driven BF peer fired + updated position + concrete weak run + the
-- BF-client/-server evolution facts (mirror `BundleBFEvR-abs` + block facts)
data BundleBFEvR⁺ (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : BF.BFEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  bcbcEB⁺ : (bfc′ : BFcPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc′ bfs ip
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► bundleG l cl sv csc css bfc′ bfs ip
        → (BFcHasBlk bfc′ → ⊥)
        → BundleBFEvR⁺ l cl sv csc css bfc bfs ip e₁ a Bd′
  bcbsEB⁺ : (bfs′ : BFsPos)
        → Bd′ ≡ absBundleG l cl sv csc css bfc bfs′ ip
        → bundleG l cl sv csc css bfc bfs ip
            ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► bundleG l cl sv csc css bfc bfs′ ip
        → BfsSucc l sv bfs′ (ιBF e₁) a
        → BundleBFEvR⁺ l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a decoded BF-client fire into the bundle result (mirror
-- `finishBFc-ev-abs`, decode supplied by the caller)
finishBFc⁺ : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → (sM : absBFc l cl bfc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′)
  → Σ[ bfc′ ∈ BFcPos ]
      (decBFc l cl bfc ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFc l cl bfc′)
      × (P′ ≡ absBFc l cl bfc′) × (BFcHasBlk bfc′ → ⊥)
  → BundleBFEvR⁺ l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (P′
        ⦀ (absBFs l sv bfs ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishBFc⁺ l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM (bfc′ , run , Meq , ¬blk) =
      bcbcEB⁺ bfc′
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (z
               ⦀ (absBFs l sv bfs ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _
            (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁)))
            (⦀-wev-R (decCSc l cl csc) _
              (noOffer→viewV (decCSc l cl csc) (decCSc-noBFgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _
                (noOffer→viewV (decCSs l sv css) (decCSs-noBFgen l sv css e₁))
                (⦀-wev-L (decBFc l cl bfc) _
                  (noOffer→viewV _
                    (bfTail-bfs-noOffer l cl sv bfs ip e₁
                      (λ q → cl≢sv (trans (sym (absBFc-ev-dir l cl bfc sM)) q))))
                  run)))))
        ¬blk

-- fold a decoded BF-server fire into the bundle result (mirror
-- `finishBFs-ev-abs`, decode supplied by the caller; the client slot is LITERAL)
finishBFs⁺ : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → (sM : absBFs l sv bfs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′)
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l sv bfs ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFs l sv bfs′)
      × (P′ ≡ absBFs l sv bfs′) × BfsSucc l sv bfs′ (ιBF e₁) a
  → BundleBFEvR⁺ l cl sv csc css bfc bfs ip e₁ a
      (absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (P′
        ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
        ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip))))))))))))
finishBFs⁺ l cl sv csc css bfc bfs ip {e₁ = e₁} cl≢sv sM (bfs′ , run , Meq , bsucc) =
      bcbsEB⁺ bfs′
        (cong (λ z → absKAc l cl (kac ip) ⦀ (absKAs l sv (kas ip) ⦀ (absCSc l cl csc ⦀ (absCSs l sv css ⦀ (absBFc l cl bfc ⦀ (z
               ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
               ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))))) Meq)
        (⦀-wev-R (decKAc l cl (kac ip)) _
          (noOffer→viewV (decKAc l cl (kac ip)) (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁)))
          (⦀-wev-R (decKAs l sv (kas ip)) _
            (noOffer→viewV (decKAs l sv (kas ip)) (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁)))
            (⦀-wev-R (decCSc l cl csc) _
              (noOffer→viewV (decCSc l cl csc) (decCSc-noBFgen l cl csc e₁))
              (⦀-wev-R (decCSs l sv css) _
                (noOffer→viewV (decCSs l sv css) (decCSs-noBFgen l sv css e₁))
                (⦀-wev-R (decBFc l cl bfc) _
                  (noOffer→viewV (decBFc l cl bfc)
                    (decBFc-dir-noOffer l cl bfc e₁ (λ q → cl≢sv (trans (sym q) (absBFs-ev-dir l sv bfs sM)))))
                  (⦀-wev-L (decBFs l sv bfs) _
                    (noOffer→viewV _ (bfTail-tsc-noOffer l cl sv ip e₁))
                    run))))))
        bsucc

-- 12-peer abstract bundle ev-inversion (BF) with client evolution (mirror of
-- `absBundleBF-ev-prod`; the isolated client fire is routed through `kc`)
absBundleBF-ev-evo : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → BFcDecode l cl bfc e₁ a
  → BFsDecode l sv bfs e₁ a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► Bd′
  → BundleBFEvR⁺ l cl sv csc css bfc bfs ip e₁ a Bd′
absBundleBF-ev-evo l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} kc ks step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM     = ⊥-elim (absKAc-noBF l cl (kac ip) e₁ (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (absKAc-noBF l cl (kac ip) e₁ (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM     = ⊥-elim (absKAs-noBF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (absKAs-noBF l sv (kas ip) e₁ (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM     = ⊥-elim (absCSc-noBF l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (absCSc-noBF l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM     = ⊥-elim (absCSs-noBF l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (absCSs-noBF l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = finishBFc⁺ l cl sv csc css bfc bfs ip cl≢sv sM (kc sM)
...         | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absBFs l sv bfs) _ (absBFs-dir-noBoth l sv bfs e₁ (λ q → cl≢sv (trans (sym (absBFc-ev-dir l cl bfc sM)) q))) (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁)))))) (_ , sTail))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = finishBFs⁺ l cl sv csc css bfc bfs ip cl≢sv sM (ks sM)
...           | PEA.evBoth _ sM sTail = ⊥-elim (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁) (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁) (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁) (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁) (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁))))) (_ , sTail))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM     = ⊥-elim (absTSc-noBF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (absTSc-noBF l cl (tsc ip) e₁ (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM     = ⊥-elim (absTSs-noBF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (absTSs-noBF l sv (tss ip) e₁ (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM     = ⊥-elim (absLNc-noBF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (absLNc-noBF l cl (lnc ip) e₁ (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM     = ⊥-elim (absLNs-noBF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (absLNs-noBF l sv (lns ip) e₁ (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM     = ⊥-elim (absLFc-noBF l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (absLFc-noBF l cl (lfc ip) e₁ (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (absLFs-noBF l sv (lfs ip) e₁ (_ , qs))

------------------------------------------------------------------------
-- The unified api result WITH the client-evolution disjunct (mirror
-- `BundleGEvR-abs`/`bgEB`), and the six per-channel lifters (non-BF channels
-- keep the client slot LITERAL ⇒ `inj₁ refl`).
------------------------------------------------------------------------

-- unified abstract bundle ev-inversion result + the BF-client evolution fact
data BundleGEvR⁺ (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) (Bd′ : NetProc) : Set₁ where
  bgEB⁺ : (csc′ : CScPos) (css′ : CSsPos) (bfc′ : BFcPos) (bfs′ : BFsPos) (ip′ : InertPos)
       → Bd′ ≡ absBundleG l cl sv csc′ css′ bfc′ bfs′ ip′
       → bundleG l cl sv csc css bfc bfs ip
           ═[ ev (evl (evLabel X e a)) ]═► bundleG l cl sv csc′ css′ bfc′ bfs′ ip′
       → ((bfc ≡ bfc′) ⊎ (BFcHasBlk bfc′ → ⊥))
       → ((bfs ≡ bfs′) ⊎ BfsSucc l sv bfs′ e a)
       → BundleGEvR⁺ l cl sv csc css bfc bfs ip e a Bd′

-- per-channel lifters (mirror `csEvR→g` …; non-BF channels: client literal)
csEvR→g⁺ : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → BundleCSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR⁺ l cl sv csc css bfc bfs ip (ιCS e₁) a Bd′
csEvR→g⁺ {csc = csc} {css} {bfc} {bfs} {ip} (bcscEB csc′ eq run) = bgEB⁺ csc′ css  bfc bfs ip eq run (inj₁ refl) (inj₁ refl)
csEvR→g⁺ {csc = csc} {css} {bfc} {bfs} {ip} (bcssEB css′ eq run) = bgEB⁺ csc  css′ bfc bfs ip eq run (inj₁ refl) (inj₁ refl)

bfEvR⁺→g : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → BundleBFEvR⁺ l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR⁺ l cl sv csc css bfc bfs ip (ιBF e₁) a Bd′
bfEvR⁺→g {csc = csc} {css} {bfc} {bfs} {ip} (bcbcEB⁺ bfc′ eq run ¬blk) = bgEB⁺ csc css bfc′ bfs  ip eq run (inj₂ ¬blk) (inj₁ refl)
bfEvR⁺→g {csc = csc} {css} {bfc} {bfs} {ip} (bcbsEB⁺ bfs′ eq run bsucc) = bgEB⁺ csc css bfc  bfs′ ip eq run (inj₁ refl) (inj₂ bsucc)

kaEvR→g⁺ : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {Bd′ : NetProc}
  → BundleKAEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR⁺ l cl sv csc css bfc bfs ip (ιKA e₁) a Bd′
kaEvR→g⁺ {csc = csc} {css} {bfc} {bfs} {ip} (bkacEB kac′ eq run) = bgEB⁺ csc css bfc bfs (record ip { kac = kac′ }) eq run (inj₁ refl) (inj₁ refl)
kaEvR→g⁺ {csc = csc} {css} {bfc} {bfs} {ip} (bkasEB kas′ eq run) = bgEB⁺ csc css bfc bfs (record ip { kas = kas′ }) eq run (inj₁ refl) (inj₁ refl)

tsEvR→g⁺ : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {Bd′ : NetProc}
  → BundleTSEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR⁺ l cl sv csc css bfc bfs ip (ιTS e₁) a Bd′
tsEvR→g⁺ {csc = csc} {css} {bfc} {bfs} {ip} (btscEB tsc′ eq run) = bgEB⁺ csc css bfc bfs (record ip { tsc = tsc′ }) eq run (inj₁ refl) (inj₁ refl)
tsEvR→g⁺ {csc = csc} {css} {bfc} {bfs} {ip} (btssEB tss′ eq run) = bgEB⁺ csc css bfc bfs (record ip { tss = tss′ }) eq run (inj₁ refl) (inj₁ refl)

lnEvR→g⁺ : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {Bd′ : NetProc}
  → BundleLNEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR⁺ l cl sv csc css bfc bfs ip (ιLN e₁) a Bd′
lnEvR→g⁺ {csc = csc} {css} {bfc} {bfs} {ip} (blncEB lnc′ eq run) = bgEB⁺ csc css bfc bfs (record ip { lnc = lnc′ }) eq run (inj₁ refl) (inj₁ refl)
lnEvR→g⁺ {csc = csc} {css} {bfc} {bfs} {ip} (blnsEB lns′ eq run) = bgEB⁺ csc css bfc bfs (record ip { lns = lns′ }) eq run (inj₁ refl) (inj₁ refl)

lfEvR→g⁺ : {l : Link} {cl sv : Dir} {csc : CScPos} {css : CSsPos} {bfc : BFcPos} {bfs : BFsPos} {ip : InertPos}
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {Bd′ : NetProc}
  → BundleLFEvR-abs l cl sv csc css bfc bfs ip e₁ a Bd′
  → BundleGEvR⁺ l cl sv csc css bfc bfs ip (ιLF e₁) a Bd′
lfEvR→g⁺ {csc = csc} {css} {bfc} {bfs} {ip} (blfcEB lfc′ eq run) = bgEB⁺ csc css bfc bfs (record ip { lfc = lfc′ }) eq run (inj₁ refl) (inj₁ refl)
lfEvR→g⁺ {csc = csc} {css} {bfc} {bfs} {ip} (blfsEB lfs′ eq run) = bgEB⁺ csc css bfc bfs (record ip { lfs = lfs′ }) eq run (inj₁ refl) (inj₁ refl)

------------------------------------------------------------------------
-- The unified api dispatcher WITH client evolution (mirror of
-- `absBundleG-api-prod`): case on the raw api/done event, invoke the frozen
-- per-channel exposer (BF: the `⁺` cascade above), lift into `BundleGEvR⁺`.
------------------------------------------------------------------------

open Op using ( EventSet )
open EventSet using ( mem )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( apiES )

-- unified api dispatcher with the BF-client evolution fact
absBundleG-api-evo : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → apiES .mem (X , e) a
  → absBundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → BundleGEvR⁺ l cl sv csc css bfc bfs ip e a Bd′
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiCS l′ d′ m} apimem step = csEvR→g⁺ (absBundleCS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.apiCSev l′ d′ m} step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiBF l′ d′ m} apimem step = bfEvR⁺→g (absBundleBF-ev-evo l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.apiBFev l′ d′ m} (decBFc-apiBF-succ⁺ l cl bfc) (decBFs-apiBF-succ⁺ l sv bfs) step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiKA l′ d′ m} apimem step = kaEvR→g⁺ (absBundleKA-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.apiKAev l′ d′ m} step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiTS l′ d′ m} apimem step = tsEvR→g⁺ (absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.apiTSev l′ d′ m} step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiLN l′ d′ m} apimem step = lnEvR→g⁺ (absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.apiLNev l′ d′ m} step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = apiLF l′ d′ m} apimem step = lfEvR→g⁺ (absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.apiLFev l′ d′ m} step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_ChainSync}    apimem step = csEvR→g⁺ (absBundleCS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.doneCS l′ d′} step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_BlockFetch}   apimem step = bfEvR⁺→g (absBundleBF-ev-evo l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.doneBF l′ d′} (λ sM → ⊥-elim (decBFc-doneBF-absurd l cl bfc sM)) (decBFs-doneBF-succ⁺ l sv bfs) step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_KeepAlive}    apimem step = kaEvR→g⁺ (absBundleKA-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.doneKA l′ d′} step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_TxSubmission} apimem step = tsEvR→g⁺ (absBundleTS-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.doneTS l′ d′} step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_LeiosNotify}  apimem step = lnEvR→g⁺ (absBundleLN-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LN.doneLN l′ d′} step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = done l′ d′ N2N_LeiosFetch}   apimem step = lfEvR→g⁺ (absBundleLF-ev-prod l cl sv cl≢sv csc css bfc bfs ip {e₁ = LF.doneLF l′ d′} step)
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = input  _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = output _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = tx     _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = ack    _ _ _} apimem step = ⊥-elim apimem
absBundleG-api-evo l cl sv cl≢sv csc css bfc bfs ip {e = break  _}     apimem step = ⊥-elim apimem

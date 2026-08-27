{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R3 — the ISOLATED BF-SERVER io SUCCESSOR DECODE
-- (`Praos.PipeSrvIoDec`), sub-obligation (c) of the `PipeInvProd.TauIoS` arm.
--
-- The `SrvCoupled` half of the io step needs, for the fired BF server,
-- `BFsHasBlk bfs′ → ⊥` at the SUCCESSOR — i.e. the `inj₁` arm of
-- `PipeBundleEvo.BfsSucc`, which is exactly what `PipeBundleEvo.BFsDecode`
-- already asks for.  So NO bundle-level re-mirror is needed on the server
-- side; only this isolated decode, at the two io events of the BlockFetch
-- alphabet (`BF.sendBF` ↦ `input l d N2N_BlockFetch`, `BF.receiveBF` ↦
-- `output l d N2N_BlockFetch`).
--
-- METHOD-MANDATE TABLE CHECK (done BEFORE building, per session 28): the R2
-- abstract server table `NodeSpecs.bfSnxt` enters `bsWblk` at EXACTLY ONE row —
-- `bsStream --apiBF l d sendBFBlock--> bsWblk b` (NodeSpecs:622-623).  Every
-- io row (`bsIdle` on `output`, and `bsWsb`/`bsWnb`/`bsWblk`/`bsWbd` on `input`)
-- lands on `bsAreq`/`bsDdone`/`bsStream`/`bsIdle`.  So "an io fire of a BF
-- server never lands on a holding position" is TRUE.
--
-- Session 29 established that the CHEAP routes do not work: `decBFs-ev-prod-abs`
-- returns its successor EXISTENTIALLY, and `tableSpec` is not known injective in
-- its position, so `coarsenBFs bfs′ ≡ q′` cannot be recovered from the decode's
-- `Meq` — the ¬-block fact cannot be bolted on afterwards.  Hence this genuine
-- position decode: every clause NAMES its concrete successor, off which
-- `BFsHasBlk` reduces to `⊥` syntactically (`λ ()`).
--
-- *** CORRECTION (CSP-refinement T3/T3b; comment only, NO code change here). ***  The
-- clause above — "`tableSpec` is not known injective in its position" — is FALSE at the
-- COARSE level, and this module states it unqualified over ~527 code lines of mirror.
-- Coarse `tableSpec` position injectivity is DERIVABLE in 11 lines by composing two
-- lemmas that were already banked when this module was written: `tableSpec-ev-fwd`
-- (`SysOracle_NodeTauEv:979-984`) fires `q₁`'s row, the `tableSpec T q₁ ≡ tableSpec T q₂`
-- equation transports that step, and `tableSpec-ev-inv` (`:963-966`) reads `q₂`'s row off
-- it — so a `tableSpec` equation TRANSFERS OFFER SUPPORT.  The derivation is
-- machine-checked (T3's throwaway spike, green in both the CSP and the LTL layer) and its
-- side condition is that the table's coarse positions have pairwise-distinct offer
-- SUPPORTS — a standing review obligation on `NodeSpecs`, not a proof obligation here.
-- What IS non-injective is the FINE coarsening map (`absBF{c,s}-sil-collapse`,
-- `SysStep:1156-1162`), whose witness pair is DIAGONAL (`collapse-is-diagonal = refl`,
-- machine-checked) and therefore says nothing about the coarse level.
--
-- Nothing below is retracted: this module is SOUND and its bodies are unaffected.  What
-- is open, and DELIBERATELY NOT measured here, is whether the row-recovery route would
-- have made the mirror unnecessary — it is not in this campaign's scope, and the mirror is
-- landed and green.  Do not quote the sentence above as evidence that a row cannot be
-- recovered post hoc.
--
-- Bodies mirror `SysIoLink5.bfs-hstep` / `decBFs-ev-prod-abs` VERBATIM on the
-- io slice, reusing the frozen `bfs-fire-*` firing lemmas, `mkMbfs`, `Tbfs`,
-- `tableSpec-ev-inv` and `decBFs-sil-step`; the ONLY addition is the named
-- successor's ¬-block certificate.
--
-- STALE-HEADER CORRECTION (T3b fix round): "Imported by nothing yet" was true when
-- written and is now FALSE — this module is imported by `PipeBundleIoEvo:122` and by
-- `LiveLegIoCone:145`/`:149`, so it IS inside the CSP-refinement endpoint's closure and
-- a change here is checked by the `LivenessProof` build.  No postulate/hole/meta.  Base
-- modules READ-ONLY.
------------------------------------------------------------------------

open import Level using ( 0ℓ )
open import Data.Empty using ( ⊥; ⊥-elim )
open import Data.Product using ( Σ; Σ-syntax; _×_; _,_; proj₁; proj₂ )
open import Data.Sum using ( _⊎_; inj₁; inj₂ )
open import Data.Maybe using ( just; nothing )
open import Data.Maybe.Properties using ( just-injective )
open import Data.Unit.Polymorphic using ( ⊤; tt )
open import Relation.Nullary using ( yes; no )
open import Relation.Binary.PropositionalEquality using ( _≡_; refl; sym; trans; cong )

open import Class.DecEq using ( DecEq; _≟_ )
import Class.DecEq.Instances as DecEqI

open import Process_Trees using ( PTree; ExtI )

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeSrvIoDec (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p
open import CSP.Examples.Cardano_network.Base using ( Dir; N2N_BlockFetch; FromResponder )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιBF )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; τ*-refl; τ*-step )

import CSP.Examples.Cardano_network.BlockFetch p as BF

import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep using ( NetProc; absBFs; coarsenBFs; decBFs-sil-step )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
-- (grant #7) the BF server's next-state table, for the FIRED ROW the three
-- inversions below now report (`Tbfs l d` IS `record { nxt = NS.bfSnxt l d ; … }`)
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open SN using ( BFsPos; decBFs
              ; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA
  using ( tableSpec-ev-inv; nothing-absurd )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink6 blkA as SIL6
open SIL6 using ( Tbfs; mkMbfs
                ; bfs-fire-req; bfs-fire-cdone
                ; bfs-fire-start1; bfs-fire-noblk1; bfs-fire-blk1; bfs-fire-batch1 )
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Value.PipeBundleEvo blkA
  using ( BFsHasBlk; BfsSucc )

------------------------------------------------------------------------
-- (GRANT #7)  *** THE FIRED COARSE ROW, REPORTED INSTEAD OF DISCARDED. ***
--
-- The server mirror of `PipeCliIoDec`'s grant-#7 section: every firing clause
-- below binds the row as `ceq` and then forgets it inside `mkMbfs`, and it is
-- unrecoverable afterwards by any FINE route (fine-position injectivity is FALSE —
-- `SysStep.absBFs-sil-collapse`).  *** SCOPE CORRECTED (CSP-refinement T3/T3b, and this
-- is the same correction as the header's, restated HERE because the header's says "the
-- clause above" and does not reach this section: *** the parenthesis originally read
-- "abstract-position injectivity is FALSE" unqualified.  At the COARSE level it is
-- DERIVABLE (11 lines off `tableSpec-ev-fwd`/`tableSpec-ev-inv`, under a
-- support-distinctness side condition on `NodeSpecs`), and `absBFs-sil-collapse` is a
-- FINE-map fact whose coarse witness pair is diagonal.  So there are TWO routes to a
-- consumer's adjacency, not one; the widening below is the route this module takes, and
-- it remains correct.  Do not cite `absBFs-sil-collapse` against coarse row recovery.
-- Each inversion returns it as a strict TRAILING
-- component under `…-row`; the original names are re-derived at the end of the
-- module as one-line projections, byte-identical in type.
--
-- The row is at the FIRED key with the two key equations beside it (the measured
-- constraint recorded at `PipeBundleEvo`'s grant-#8 section).
------------------------------------------------------------------------

-- a BF SERVER's fired coarse row on the wire WRITE (`sendBF`), at the fired key
SrvSendRow : (l : Link) (d : Dir) (l′ : Link) (d′ : Dir) (bfs bfs′ : BFsPos)
             (a : Payload) → Set
SrvSendRow l d l′ d′ bfs bfs′ a =
  (l′ ≡ l) × (d′ ≡ d)
  × (NS.bfSnxt l d (coarsenBFs bfs) (Payload , ιBF (BF.sendBF l′ d′)) a
       ≡ just (coarsenBFs bfs′))

-- … and on the wire READ (`receiveBF`) — the server taking the client's message
SrvReadRow : (l : Link) (d : Dir) (l′ : Link) (d′ : Dir) (bfs bfs′ : BFsPos)
             (a : Payload) → Set
SrvReadRow l d l′ d′ bfs bfs′ a =
  (l′ ≡ l) × (d′ ≡ d)
  × (NS.bfSnxt l d (coarsenBFs bfs) (Payload , ιBF (BF.receiveBF l′ d′)) a
       ≡ just (coarsenBFs bfs′))

------------------------------------------------------------------------
-- (1) HEAD/SIL SLICE, `receiveBF` (the wire READ `output l d N2N_BlockFetch`).
-- Only the IDLE head reads: `MsgRequestRange r → bsReq1 r`, `MsgClientDone →
-- bsDone1`.  Both successors are ¬-block; every other head state and every
-- other payload has NO table row.
------------------------------------------------------------------------

-- a `receiveBF` fire out of a BF-server HEAD: named successor + firing step +
-- abstract equality + the ¬-block certificate
bfs-recv-hstep-row : (l : Link) (d : Dir) (st : BF.BFState)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFs l d (bsHead st) ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► M
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l d (bsHead st)
         ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► decBFs l d bfs′)
      × (M ≡ absBFs l d bfs′) × (BFsHasBlk bfs′ → ⊥)
      × SrvReadRow l d l′ d′ (bsHead st) bfs′ a
-- IDLE: the two client-originated wire messages the server reads
bfs-recv-hstep-row l d BF.stIdle {l′} {d′} {a = t0 , md , ln , blockFetch (MsgRequestRange r)} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsReq1 r , SIL6.RFBF.renameMap-ev-fwd (bfs-fire-req l d r t0 md ln)
      , mkMbfs l d (bsReq1 r) Meq (just-injective (sym ceq)) , (λ ()) , (refl , refl , trans ceq (cong just (just-injective (sym ceq))))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stIdle {l′} {d′} {a = t0 , md , ln , blockFetch MsgClientDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl =
        bsDone1 , SIL6.RFBF.renameMap-ev-fwd (bfs-fire-cdone l d t0 md ln)
      , mkMbfs l d bsDone1 Meq (just-injective (sym ceq)) , (λ ()) , (refl , refl , trans ceq (cong just (just-injective (sym ceq))))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _     | _    = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stIdle {a = _ , _ , _ , blockFetch MsgStartBatch} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stIdle {a = _ , _ , _ , blockFetch MsgNoBlocks} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stIdle {a = _ , _ , _ , blockFetch (MsgBlock b)} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stIdle {a = _ , _ , _ , blockFetch MsgBatchDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stIdle {a = _ , _ , _ , keepAlive _} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stIdle {a = _ , _ , _ , chainSync _} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stIdle {a = _ , _ , _ , txSubmission _} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stIdle {a = _ , _ , _ , leiosNotify _} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stIdle {a = _ , _ , _ , leiosFetch _} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- BUSY / STREAMING / DONE heads: the table has no wire-read row
bfs-recv-hstep-row l d BF.stBusy step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stStreaming step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-recv-hstep-row l d BF.stDone step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

------------------------------------------------------------------------
-- (2) HEAD/SIL SLICE, `sendBF` (the wire WRITE `input l d N2N_BlockFetch`).
-- No head state writes: the four writing positions are the dedicated wire-send
-- ones (`bsStart1`/`bsNoBlk1`/`bsBlk1`/`bsBatchDone1`), handled in (3).
------------------------------------------------------------------------

-- a `sendBF` fire out of a BF-server HEAD is impossible (no table row)
bfs-send-hstep : (l : Link) (d : Dir) (st : BF.BFState)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFs l d (bsHead st) ─[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]─► M
  → ⊥
bfs-send-hstep l d BF.stIdle step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = nothing-absurd ceq
bfs-send-hstep l d BF.stBusy step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = nothing-absurd ceq
bfs-send-hstep l d BF.stStreaming step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = nothing-absurd ceq
bfs-send-hstep l d BF.stDone step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stDone)) step
... | q′ , ceq , Meq = nothing-absurd ceq

------------------------------------------------------------------------
-- (3) THE TWO WHOLE-POSITION io DECODES.  Both deliver the `BFsDecode`-shaped
-- package (successor + concrete WEAK run + abstract equality) plus `BFsHasBlk
-- bfs′ → ⊥`; the four wire-send positions land on `bsSil stStreaming` /
-- `bsSil stIdle`, the two wire-read successors on `bsReq1` / `bsDone1` — all
-- ¬-block by `λ ()`.
------------------------------------------------------------------------

-- a BF server firing the wire WRITE io: successor is a `bsSil`, hence ¬-block
decBFs-sendBF-succ-row : (l : Link) (d : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]─► M
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l d bfs ═[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]═► decBFs l d bfs′)
      × (M ≡ absBFs l d bfs′) × (BFsHasBlk bfs′ → ⊥)
      × SrvSendRow l d l′ d′ bfs bfs′ a
decBFs-sendBF-succ-row l d (bsHead st) step = ⊥-elim (bfs-send-hstep l d st step)
decBFs-sendBF-succ-row l d (bsSil st)  step = ⊥-elim (bfs-send-hstep l d st step)
decBFs-sendBF-succ-row l d (bsReq1 r) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d bsDone1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d bsStart1 {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsStart1) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl
      with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | yes refl =
          bsSil BF.stStreaming
        , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-start1 l d)) τ*-refl
        , mkMbfs l d (bsSil BF.stStreaming) Meq (just-injective (sym ceq)) , (λ ()) , (refl , refl , trans ceq (cong just (just-injective (sym ceq))))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d bsStart1 step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d bsStart1 step | q′ , ceq , Meq | no _    | _    = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d bsNoBlk1 {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsNoBlk1) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl
      with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | yes refl =
          bsSil BF.stIdle
        , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-noblk1 l d)) τ*-refl
        , mkMbfs l d (bsSil BF.stIdle) Meq (just-injective (sym ceq)) , (λ ()) , (refl , refl , trans ceq (cong just (just-injective (sym ceq))))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d bsNoBlk1 step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d bsNoBlk1 step | q′ , ceq , Meq | no _    | _    = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d (bsBlk1 b) {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl
      with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | yes refl =
          bsSil BF.stStreaming
        , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-blk1 l d b)) τ*-refl
        , mkMbfs l d (bsSil BF.stStreaming) Meq (just-injective (sym ceq)) , (λ ()) , (refl , refl , trans ceq (cong just (just-injective (sym ceq))))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d (bsBlk1 b) step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d (bsBlk1 b) step | q′ , ceq , Meq | no _    | _    = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d bsBatchDone1 {l′} {d′} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsBatchDone1) step
... | q′ , ceq , Meq with l′ ≟ l | d′ ≟ d
...   | yes refl | yes refl
      with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | yes refl =
          bsSil BF.stIdle
        , wev τ*-refl (SIL6.RFBF.renameMap-ev-fwd (bfs-fire-batch1 l d)) τ*-refl
        , mkMbfs l d (bsSil BF.stIdle) Meq (just-injective (sym ceq)) , (λ ()) , (refl , refl , trans ceq (cong just (just-injective (sym ceq))))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d bsBatchDone1 step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-sendBF-succ-row l d bsBatchDone1 step | q′ , ceq , Meq | no _    | _    = ⊥-elim (nothing-absurd ceq)

-- a BF server firing the wire READ io: successor is `bsReq1`/`bsDone1`, ¬-block
decBFs-receiveBF-succ-row : (l : Link) (d : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► M
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l d bfs ═[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]═► decBFs l d bfs′)
      × (M ≡ absBFs l d bfs′) × (BFsHasBlk bfs′ → ⊥)
      × SrvReadRow l d l′ d′ bfs bfs′ a
decBFs-receiveBF-succ-row l d (bsHead st) step with bfs-recv-hstep-row l d st step
... | bfs′ , f , m , nb , row = bfs′ , wev τ*-refl f τ*-refl , m , nb , row
-- (grant #7) the SIL position's row IS the HEAD's: `coarsenBFs (bsSil st)` and
-- `coarsenBFs (bsHead st)` are the same coarse position (`absBFs-sil-collapse`)
decBFs-receiveBF-succ-row l d (bsSil st) step with bfs-recv-hstep-row l d st step
... | bfs′ , f , m , nb , row =
      bfs′ , wev (τ*-step (decBFs-sil-step l d st) τ*-refl) f τ*-refl , m , nb , row
decBFs-receiveBF-succ-row l d (bsReq1 r) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-receiveBF-succ-row l d bsDone1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-receiveBF-succ-row l d bsStart1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsStart1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-receiveBF-succ-row l d bsNoBlk1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsNoBlk1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-receiveBF-succ-row l d (bsBlk1 b) step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-receiveBF-succ-row l d bsBatchDone1 step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs bsBatchDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

------------------------------------------------------------------------
-- (GRANT #7) THE THREE ORIGINAL INTERFACES, as projections of the row-carrying
-- inversions above — byte-identical in type, so every consumer (the two
-- `BFsDecode` packages of §4 included) is untouched.
------------------------------------------------------------------------

-- the head-slice read inversion, without the row
bfs-recv-hstep : (l : Link) (d : Dir) (st : BF.BFState)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFs l d (bsHead st) ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► M
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l d (bsHead st)
         ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► decBFs l d bfs′)
      × (M ≡ absBFs l d bfs′) × (BFsHasBlk bfs′ → ⊥)
bfs-recv-hstep l d st step =
  let (bfs′ , f , m , nb , _) = bfs-recv-hstep-row l d st step
  in  bfs′ , f , m , nb

-- the whole-position WRITE decode, without the row
decBFs-sendBF-succ : (l : Link) (d : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]─► M
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l d bfs ═[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]═► decBFs l d bfs′)
      × (M ≡ absBFs l d bfs′) × (BFsHasBlk bfs′ → ⊥)
decBFs-sendBF-succ l d bfs step =
  let (bfs′ , run , m , nb , _) = decBFs-sendBF-succ-row l d bfs step
  in  bfs′ , run , m , nb

-- the whole-position READ decode, without the row
decBFs-receiveBF-succ : (l : Link) (d : Dir) (bfs : BFsPos)
    {l′ : Link} {d′ : Dir} {a : Payload} {M : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► M
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l d bfs ═[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]═► decBFs l d bfs′)
      × (M ≡ absBFs l d bfs′) × (BFsHasBlk bfs′ → ⊥)
decBFs-receiveBF-succ l d bfs step =
  let (bfs′ , run , m , nb , _) = decBFs-receiveBF-succ-row l d bfs step
  in  bfs′ , run , m , nb

------------------------------------------------------------------------
-- (4) THE `BFsDecode` PACKAGES.  `PipeBundleEvo.BFsDecode` asks for exactly
-- this shape with a `BfsSucc`; on an io the LEFT disjunct is the answer, so the
-- existing `absBundleBF-ev-evo` server callback slot is satisfied UNCHANGED —
-- no server-side bundle re-mirror is needed for the io `TauStep`.
------------------------------------------------------------------------

-- the io wire-WRITE server callback, in `BFsDecode` form
decBFs-sendBF-decode : (l : Link) (d : Dir) (bfs : BFsPos) {l′ : Link} {d′ : Dir}
    {a : Payload} {P′ : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]─► P′
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l d bfs ═[ ev (evl (evLabel Payload (ιBF (BF.sendBF l′ d′)) a)) ]═► decBFs l d bfs′)
      × (P′ ≡ absBFs l d bfs′) × BfsSucc l d bfs′ (ιBF (BF.sendBF l′ d′)) a
decBFs-sendBF-decode l d bfs step with decBFs-sendBF-succ l d bfs step
... | bfs′ , run , Meq , nb = bfs′ , run , Meq , inj₁ nb

-- the io wire-READ server callback, in `BFsDecode` form
decBFs-receiveBF-decode : (l : Link) (d : Dir) (bfs : BFsPos) {l′ : Link} {d′ : Dir}
    {a : Payload} {P′ : NetProc}
  → absBFs l d bfs ─[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]─► P′
  → Σ[ bfs′ ∈ BFsPos ]
      (decBFs l d bfs ═[ ev (evl (evLabel Payload (ιBF (BF.receiveBF l′ d′)) a)) ]═► decBFs l d bfs′)
      × (P′ ≡ absBFs l d bfs′) × BfsSucc l d bfs′ (ιBF (BF.receiveBF l′ d′)) a
decBFs-receiveBF-decode l d bfs step with decBFs-receiveBF-succ l d bfs step
... | bfs′ , run , Meq , nb = bfs′ , run , Meq , inj₁ nb

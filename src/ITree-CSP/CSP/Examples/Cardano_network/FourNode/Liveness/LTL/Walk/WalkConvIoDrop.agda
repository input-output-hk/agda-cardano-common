{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- R3 — the io-sync NODE cone LEAF DROPS (`decXc/Xs-ev-io-drop`, WalkConv item
-- (1)).  For each abstract peer FSM, an abstract visible fire of `absXc/Xs`
-- RESTRICTED to an io event (`sendX`/`receiveX`, i.e. `ιX e₁ ∈ ioES`) is
-- matched by a WEAK concrete run of `decXc/Xs` landing on a successor position
-- `pos′`, AND the per-peer measure `posWt-Xc/Xs pos′` STRICTLY DROPS below
-- `posWt-Xc/Xs pos`.  This is the per-peer node summand of `μτ-io-dec`.
--
-- The frozen `SysIoLink5.decXc/Xs-ev-prod-abs` leaves expose their successor
-- OPAQUELY, so the drop cannot be harvested by `with` — each leaf is
-- RE-MIRRORED here, tracking `pos′` CONCRETELY per clause so `posWt-Xc pos′`
-- reduces to a numeral and the `<` closes by `s≤s`/`z≤n`.  The mirror reuses
-- the frozen firing builders (`csc-fire-*`, …), coarse tables (`Tcsc`, …),
-- `mkMcsc`/…, `tableSpec-ev-inv`, and `nothing-absurd` VERBATIM (imported,
-- never edited).  Because every fired event is io, ALL api-offer / `done`
-- branches collapse to a single `⊥-elim iomem` (their `ioES` membership is `⊥`).
--
-- No postulate/hole/meta.
------------------------------------------------------------------------

open import Level using (0ℓ)
open import Data.Nat using (ℕ; zero; suc; _<_; _≤_; s≤s; z≤n)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Data.Empty using (⊥-elim)
open import Data.Maybe.Properties using (just-injective)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Relation.Nullary using (yes; no)
open import Class.DecEq using (_≟_)
import Class.DecEq.Instances as DecEqI
open import Process_Trees using (PTree; ExtI)

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvIoDrop (blkA : Block₃) where

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api; Net_Api-≟; Link )
open import CSP.Examples.Cardano_network.Data p using
  ( Payload; Header; Tip; Point
  ; chainSync; keepAlive; blockFetch; txSubmission; leiosNotify; leiosFetch
  ; MsgCSRollForward; MsgCSRollBackward; MsgCSAwaitReply
  ; MsgCSIntersectFound; MsgCSIntersectNotFound
  ; MsgCSRequestNext; MsgCSFindIntersect; MsgCSDone
  ; ChainRange; DecEq-ChainRange
  ; MsgRequestRange; MsgClientDone; MsgStartBatch; MsgNoBlocks; MsgBlock; MsgBatchDone
  ; MsgKeepAlive; MsgKeepAliveResponse; MsgKADone
  ; MsgTSInit; MsgTSRequestTxIds; MsgTSReplyTxIds; MsgTSRequestTxs; MsgTSReplyTxs; MsgTSDone
  ; MsgLNRequestNext; MsgLNBlockAnnouncement; MsgLNBlockOffer; MsgLNBlockTxsOffer; MsgLNVotesOffer; MsgLNDone
  ; MsgLFBlockRequest; MsgLFBlockTxsRequest; MsgLFVotesRequest; MsgLFBlockRangeRequest; MsgLFDone
  ; MsgLFBlock; MsgLFBlockTxs; MsgLFVoteDelivery; MsgLFNextBlockAndTxsInRange; MsgLFLastBlockAndTxsInRange
  ; DecEq-Payload; DecEq-Header; DecEq-Tip; DecEq-Point; DecEq-Tx )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; lo; hi; FromInitiator; FromResponder; BlockingStyle; Blocking; NonBlocking )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( time₀; length₀; Block )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES )

import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as OpA
open OpA using ( EventSet )
open EventSet using ( mem )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _═[_]═►_; wev; τ*-refl; τ*-step )

import CSP.Examples.Cardano_network.ChainSync p as CS
import CSP.Examples.Cardano_network.BlockFetch p as BF
import CSP.Examples.Cardano_network.KeepAlive p as KA
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.LeiosNotify p as LN
import CSP.Examples.Cardano_network.LeiosFetch p as LF
open import CSP.Examples.Cardano_network.NetworkPar p using ( ιCS; ιBF; ιKA; ιTS; ιLN; ιLF )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA using
  ( CScPos; csHead; csReqNext1; csFindInt1; csDone1
  ; csRF1; csRB1; csIF1; csINF1; csSil; decCSc
  ; CSsPos; ssHead; ssReqNext1; ssFindInt1; ssDone1
  ; ssRF1; ssRB1; ssAw1; ssIF1; ssINF1; ssSil; decCSs
  ; BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil; decBFc
  ; BFsPos; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil; decBFs
  ; KAcPos; kcHead; kcErr1; kcReq1; kcDone1; kcSil; kcTermE1; decKAc
  ; KAsPos; ksHead; ksRecv1; ksDdone1; ksSil; decKAs
  ; TScPos; tcHead; tcReqIdsB1; tcReqIdsNB1; tcReqTxs1; tcRepB1; tcDone1; tcRepNB1; tcRepTxs1; tcSil; decTSc
  ; TSsPos; tsHead; tsDone1; tsReqB1; tsReqNB1; tsReqTxs1; tsSil; decTSs
  ; LNcPos; lncHead; lncRann1; lncRoff1; lncRtxs1; lncRvot1; lncReq1; lncDone1; lncSil; decLNc
  ; LNsPos; lnsHead; lnsDone1; lnsWann1; lnsWoff1; lnsWtxs1; lnsWvot1; lnsSil; decLNs
  ; LFcPos; lfcHead; lfcRblk1; lfcRbtx1; lfcRvot1; lfcRnext1; lfcRlast1
  ; lfcWblk1; lfcWtxs1; lfcWvot1; lfcWrng1; lfcDone1; lfcSil; decLFc
  ; LFsPos; lfsHead; lfsDone1; lfsWblk1; lfsWtxs1; lfsWvot1; lfsWnext1; lfsWlast1; lfsSil; decLFs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA using
  ( NetProc; absCSc; coarsenCSc; decCSc-sil-step
  ; absCSs; coarsenCSs; decCSs-sil-step
  ; absBFc; coarsenBFc; decBFc-sil-step
  ; absBFs; coarsenBFs; decBFs-sil-step
  ; absKAc; coarsenKAc; absKAs; coarsenKAs
  ; absTSc; coarsenTSc; absTSs; coarsenTSs
  ; absLNc; coarsenLNc; absLNs; coarsenLNs
  ; absLFc; coarsenLFc; absLFs; coarsenLFs )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_NodeTauEv blkA using
  ( tableSpec-ev-inv; nothing-absurd )

-- reuse the frozen SIL5 leaf infrastructure (firing builders, coarse tables,
-- `mkMcsc`/`RFCS`/…, the strong sils) — imported, never edited
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysIoLink5 blkA using
  ( Tcsc; mkMcsc; module RFCS
  ; csc-fire-rf-CA; csc-fire-rb-CA; csc-fire-aw-CA
  ; csc-fire-rf-MR; csc-fire-rb-MR; csc-fire-if; csc-fire-inf
  ; csc-fire-reqNext1; csc-fire-findInt1; csc-fire-done1
  ; Tcss; mkMcss
  ; css-fire-reqNext; css-fire-findInt; css-fire-done
  ; css-fire-rf1; css-fire-rb1; css-fire-aw1; css-fire-if1; css-fire-inf1
  ; module RFBF
  ; Tbfc; mkMbfc
  ; bfc-fire-start; bfc-fire-noblk; bfc-fire-blk; bfc-fire-batch
  ; bfc-fire-req1; bfc-fire-cdone1
  ; Tbfs; mkMbfs
  ; bfs-fire-req; bfs-fire-cdone
  ; bfs-fire-start1; bfs-fire-noblk1; bfs-fire-blk1; bfs-fire-batch1
  ; module RFKA
  ; Tkac; mkMkac; decKAc-sil-step
  ; kac-fire-resp; kac-fire-req1; kac-fire-done1
  ; Tkas; mkMkas; decKAs-sil-step
  ; kas-fire-recv; kas-fire-ddone; kas-fire-sresp
  ; module RFTS
  ; Ttsc; mkMtsc; decTSc-sil-step
  ; tc-fire-init; tc-fire-reqB; tc-fire-reqNB; tc-fire-reqTxs
  ; tc-fire-wri1B; tc-fire-wdone1; tc-fire-wri1NB; tc-fire-wrt1
  ; Ttss; mkMtss; decTSs-sil-step
  ; ts-fire-init; ts-fire-blkReply; ts-fire-blkDone; ts-fire-nblReply; ts-fire-txsReply
  ; ts-fire-wib1; ts-fire-win1; ts-fire-wrt1
  ; module RFLN
  ; Tlnc; mkMlnc; decLNc-sil-step
  ; lnc-fire-rann; lnc-fire-roff; lnc-fire-rtxs; lnc-fire-rvot
  ; lnc-fire-wreq1; lnc-fire-wdone1
  ; Tlns; mkMlns; decLNs-sil-step
  ; lns-fire-idleReq; lns-fire-idleDone
  ; lns-fire-wann1; lns-fire-woff1; lns-fire-wtxs1; lns-fire-wvot1
  ; module RFLF
  ; Tlfc; mkMlfc; decLFc-sil-step
  ; lfc-fire-rblk; lfc-fire-rbtx; lfc-fire-rvot; lfc-fire-rnext; lfc-fire-rlast
  ; lfc-fire-wblk1; lfc-fire-wtxs1; lfc-fire-wvot1; lfc-fire-wrng1; lfc-fire-wdone1
  ; Tlfs; mkMlfs; decLFs-sil-step
  ; lfs-fire-ireq-blk; lfs-fire-ireq-txs; lfs-fire-ireq-vot; lfs-fire-ireq-rng; lfs-fire-idone
  ; lfs-fire-wblk1; lfs-fire-wtxs1; lfs-fire-wvot1; lfs-fire-wnext1; lfs-fire-wlast1 )

-- the per-peer wire-event budgets
open import CSP.Examples.Cardano_network.FourNode.Liveness.LTL.Walk.WalkConvMeasure blkA using
  ( posWt-CSc; posWt-CScSt; posWt-CSs; posWt-CSsSt
  ; posWt-BFc; posWt-BFcSt; posWt-BFs; posWt-BFsSt
  ; posWt-KAc; posWt-KAcSt; posWt-KAs; posWt-KAsSt
  ; posWt-TSc; posWt-TScSt; posWt-TSs; posWt-TSsSt
  ; posWt-LNc; posWt-LNcSt; posWt-LNs; posWt-LNsSt
  ; posWt-LFc; posWt-LFcSt; posWt-LFs; posWt-LFsSt )

------------------------------------------------------------------------
-- CS-CLIENT (`decCSc-ev-io-drop`).
------------------------------------------------------------------------

-- head-state io fire + drop, shared by the leaf's `csHead`/`csSil` clauses.
-- Every firing io is a `receiveCS` at `stCanAwait`/`stMustReply`/`stIntersect`;
-- `stIdle`/`stDone` fire no io (all refuted).  api/`done` collapse via `iomem`.
csc-hstep-io-drop : (l : Link) (d : Dir) (st : CS.CSState)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιCS e₁) a
  → absCSc l d (csHead st) ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → Σ[ pos′ ∈ CScPos ] (decCSc l d (csHead st) ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► decCSc l d pos′)
      × (M ≡ absCSc l d pos′)
      × (posWt-CSc pos′ < posWt-CScSt st)

-- stIdle: no io fire
csc-hstep-io-drop l d CS.stIdle {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stCanAwait: receiveCS RollForward/RollBackward/AwaitReply fire
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRF1 h t , RFCS.renameMap-ev-fwd (csc-fire-rf-CA l d h t t0 md ln) , mkMcsc l d (csRF1 h t) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRB1 pt tp , RFCS.renameMap-ev-fwd (csc-fire-rb-CA l d pt tp t0 md ln) , mkMcsc l d (csRB1 pt tp) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSAwaitReply} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csSil CS.stMustReply , RFCS.renameMap-ev-fwd (csc-fire-aw-CA l d t0 md ln) , mkMcsc l d (csSil CS.stMustReply) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stCanAwait {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stMustReply: receiveCS RollForward/RollBackward fire
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRF1 h t , RFCS.renameMap-ev-fwd (csc-fire-rf-MR l d h t t0 md ln) , mkMcsc l d (csRF1 h t) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRB1 pt tp , RFCS.renameMap-ev-fwd (csc-fire-rb-MR l d pt tp t0 md ln) , mkMcsc l d (csRB1 pt tp) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stMustReply {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stIntersect: receiveCS IntersectFound/IntersectNotFound fire
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csIF1 pt tp , RFCS.renameMap-ev-fwd (csc-fire-if l d pt tp t0 md ln) , mkMcsc l d (csIF1 pt tp) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csINF1 tp , RFCS.renameMap-ev-fwd (csc-fire-inf l d tp t0 md ln) , mkMcsc l d (csINF1 tp) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch _} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stIntersect {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stDone: terminal — no io fire
csc-hstep-io-drop l d CS.stDone {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep-io-drop l d CS.stDone {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible (ioES membership is ⊥)
csc-hstep-io-drop l d st {e₁ = CS.apiCSev l' d' m} iomem step = ⊥-elim iomem
csc-hstep-io-drop l d st {e₁ = CS.doneCS  l' d'}   iomem step = ⊥-elim iomem

-- the CS-client io-drop leaf
decCSc-ev-io-drop : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιCS e₁) a
  → absCSc l d pos ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → Σ[ pos′ ∈ CScPos ] (decCSc l d pos ═[ ev (evl (evLabel X (ιCS e₁) a)) ]═► decCSc l d pos′)
      × (M ≡ absCSc l d pos′)
      × (posWt-CSc pos′ < posWt-CSc pos)

-- head / loop-reentry sil delegate to the head fire (0 / 1 τ)
decCSc-ev-io-drop l d (csHead st) iomem step with csc-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decCSc-ev-io-drop l d (csSil st) iomem step with csc-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decCSc-sil-step l d st) τ*-refl) f τ*-refl , m , dr

-- csReqNext1: sendCS → csSil stCanAwait (3 → 2)
decCSc-ev-io-drop l d (csReqNext1) {e₁ = CS.sendCS l' d'} {a} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csReqNext1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...     | yes refl = csSil CS.stCanAwait , wev τ*-refl (RFCS.renameMap-ev-fwd (csc-fire-reqNext1 l d)) τ*-refl , mkMcsc l d (csSil CS.stCanAwait) Meq (just-injective (sym ceq)) , s≤s (s≤s (s≤s z≤n))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csReqNext1) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csReqNext1) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csReqNext1) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- csFindInt1 ps: sendCS → csSil stIntersect (2 → 1)
decCSc-ev-io-drop l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} {a} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csFindInt1 ps)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
...     | yes refl = csSil CS.stIntersect , wev τ*-refl (RFCS.renameMap-ev-fwd (csc-fire-findInt1 l d ps)) τ*-refl , mkMcsc l d (csSil CS.stIntersect) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csFindInt1 ps) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- csDone1: sendCS → csSil stDone (1 → 0)
decCSc-ev-io-drop l d (csDone1) {e₁ = CS.sendCS l' d'} {a} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csDone1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...     | yes refl = csSil CS.stDone , wev τ*-refl (RFCS.renameMap-ev-fwd (csc-fire-done1 l d)) τ*-refl , mkMcsc l d (csSil CS.stDone) Meq (just-injective (sym ceq)) , s≤s z≤n
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csDone1) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csDone1) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csDone1) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- csRF1/csRB1/csIF1/csINF1: fire only api recvCS* → no io fire (all refuted)
decCSc-ev-io-drop l d (csRF1 h t) {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csRF1 h t) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csRB1 pt tp) {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csRB1 pt tp) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csIF1 pt tp) {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csIF1 pt tp) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csINF1 tp) {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-io-drop l d (csINF1 tp) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible for every position
decCSc-ev-io-drop l d pos {e₁ = CS.apiCSev l' d' m} iomem step = ⊥-elim iomem
decCSc-ev-io-drop l d pos {e₁ = CS.doneCS  l' d'}   iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- CS-SERVER (`decCSs-ev-io-drop`).  Role-swapped: `ssHead stIdle` RECEIVES a
-- request (io) → an api-offer leaf (drop 1→0); the reply/await SEND positions
-- fire `sendCS` → `ssSil stIdle`(1) / `ssSil stMustReply`(0) (drop 2→1 / 1→0).
------------------------------------------------------------------------

-- head-state io fire + drop, shared by the leaf's `ssHead`/`ssSil` clauses.
css-hstep-io-drop : (l : Link) (d : Dir) (st : CS.CSState)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιCS e₁) a
  → absCSs l d (ssHead st) ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → Σ[ pos′ ∈ CSsPos ] (decCSs l d (ssHead st) ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► decCSs l d pos′)
      × (M ≡ absCSs l d pos′)
      × (posWt-CSs pos′ < posWt-CSsSt st)

-- stIdle: receives RequestNext / FindIntersect / Done → api-offer leaf (drop 0<1)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSRequestNext} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssReqNext1 , RFCS.renameMap-ev-fwd (css-fire-reqNext l d t0 md ln) , mkMcss l d (ssReqNext1) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSFindIntersect ps)} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssFindInt1 ps , RFCS.renameMap-ev-fwd (css-fire-findInt l d ps t0 md ln) , mkMcss l d (ssFindInt1 ps) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSDone} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssDone1 , RFCS.renameMap-ev-fwd (css-fire-done l d t0 md ln) , mkMcss l d (ssDone1) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward pt tp)} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound pt tp)} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound tp)} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive _} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch _} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission _} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify _} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch _} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIdle {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- other heads api-send only → no io fire
css-hstep-io-drop l d CS.stCanAwait {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stMustReply {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stMustReply {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIntersect {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stIntersect {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stDone {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep-io-drop l d CS.stDone {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible
css-hstep-io-drop l d st {e₁ = CS.apiCSev l' d' m} iomem step = ⊥-elim iomem
css-hstep-io-drop l d st {e₁ = CS.doneCS  l' d'}   iomem step = ⊥-elim iomem

-- the CS-server io-drop leaf
decCSs-ev-io-drop : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιCS e₁) a
  → absCSs l d pos ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → Σ[ pos′ ∈ CSsPos ] (decCSs l d pos ═[ ev (evl (evLabel X (ιCS e₁) a)) ]═► decCSs l d pos′)
      × (M ≡ absCSs l d pos′)
      × (posWt-CSs pos′ < posWt-CSs pos)

decCSs-ev-io-drop l d (ssHead st) iomem step with css-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decCSs-ev-io-drop l d (ssSil st) iomem step with css-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decCSs-sil-step l d st) τ*-refl) f τ*-refl , m , dr

-- ssRF1 h t: sendCS → ssSil stIdle (2 → 1)
decCSs-ev-io-drop l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} {a} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRF1 h t)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t))
...     | yes refl = ssSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-rf1 l d h t)) τ*-refl , mkMcss l d (ssSil CS.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssRF1 h t) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssRB1 pt tp: sendCS → ssSil stIdle (2 → 1)
decCSs-ev-io-drop l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} {a} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRB1 pt tp)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...     | yes refl = ssSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-rb1 l d pt tp)) τ*-refl , mkMcss l d (ssSil CS.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssRB1 pt tp) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssAw1: sendCS → ssSil stMustReply (1 → 0)
decCSs-ev-io-drop l d (ssAw1) {e₁ = CS.sendCS l' d'} {a} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssAw1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | yes refl = ssSil CS.stMustReply , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-aw1 l d)) τ*-refl , mkMcss l d (ssSil CS.stMustReply) Meq (just-injective (sym ceq)) , s≤s z≤n
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssAw1) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssAw1) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssAw1) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssAw1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssIF1 pt tp: sendCS → ssSil stIdle (2 → 1)
decCSs-ev-io-drop l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} {a} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssIF1 pt tp)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...     | yes refl = ssSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-if1 l d pt tp)) τ*-refl , mkMcss l d (ssSil CS.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssIF1 pt tp) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssINF1 tp: sendCS → ssSil stIdle (2 → 1)
decCSs-ev-io-drop l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} {a} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssINF1 tp)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...     | yes refl = ssSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-inf1 l d tp)) τ*-refl , mkMcss l d (ssSil CS.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssINF1 tp) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssReqNext1/ssFindInt1/ssDone1: api-offer / done leaves → no io fire (refuted)
decCSs-ev-io-drop l d (ssReqNext1) {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssReqNext1) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssFindInt1 ps) {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssFindInt1 ps) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssDone1) {e₁ = CS.sendCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-io-drop l d (ssDone1) {e₁ = CS.receiveCS l' d'} iomem step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible for every position
decCSs-ev-io-drop l d pos {e₁ = CS.apiCSev l' d' m} iomem step = ⊥-elim iomem
decCSs-ev-io-drop l d pos {e₁ = CS.doneCS  l' d'}   iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- BF-CLIENT (`decBFc-ev-io-drop`).  `stBusy`/`stStreaming` RECEIVE payloads;
-- the send positions `bcReq1`/`bcDone1` fire `sendBF`.
------------------------------------------------------------------------

bfc-hstep-io-drop : (l : Link) (d : Dir) (st : BF.BFState)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιBF e₁) a
  → absBFc l d (bcHead st) ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M
  → Σ[ pos′ ∈ BFcPos ] (decBFc l d (bcHead st) ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► decBFc l d pos′)
      × (M ≡ absBFc l d pos′)
      × (posWt-BFc pos′ < posWt-BFcSt st)

-- stIdle: api-send only → no io fire
bfc-hstep-io-drop l d BF.stIdle {e₁ = BF.sendBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stBusy: receives StartBatch (→stStreaming, 1<2) / NoBlocks (→stIdle, 0<2)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgStartBatch} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stStreaming , RFBF.renameMap-ev-fwd (bfc-fire-start l d t0 md ln) , mkMbfc l d (bcSil BF.stStreaming) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgNoBlocks} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stIdle , RFBF.renameMap-ev-fwd (bfc-fire-noblk l d t0 md ln) , mkMbfc l d (bcSil BF.stIdle) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive _} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync _} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission _} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify _} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch _} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stBusy {e₁ = BF.sendBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stStreaming: receives Block (→bcBlk1, 0<1) / BatchDone (→stIdle, 0<1)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgBlock b)} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcBlk1 b , RFBF.renameMap-ev-fwd (bfc-fire-blk l d b t0 md ln) , mkMbfc l d (bcBlk1 b) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgBatchDone} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stIdle , RFBF.renameMap-ev-fwd (bfc-fire-batch l d t0 md ln) , mkMbfc l d (bcSil BF.stIdle) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive _} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync _} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission _} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify _} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch _} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stStreaming {e₁ = BF.sendBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stDone: terminal
bfc-hstep-io-drop l d BF.stDone {e₁ = BF.sendBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep-io-drop l d BF.stDone {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible
bfc-hstep-io-drop l d st {e₁ = BF.apiBFev l' d' m} iomem step = ⊥-elim iomem
bfc-hstep-io-drop l d st {e₁ = BF.doneBF  l' d'}   iomem step = ⊥-elim iomem

-- the BF-client io-drop leaf
decBFc-ev-io-drop : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιBF e₁) a
  → absBFc l d pos ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M
  → Σ[ pos′ ∈ BFcPos ] (decBFc l d pos ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFc l d pos′)
      × (M ≡ absBFc l d pos′)
      × (posWt-BFc pos′ < posWt-BFc pos)

decBFc-ev-io-drop l d (bcHead st) iomem step with bfc-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decBFc-ev-io-drop l d (bcSil st) iomem step with bfc-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decBFc-sil-step l d st) τ*-refl) f τ*-refl , m , dr

-- bcReq1 r: sendBF → bcSil stBusy (3 → 2)
decBFc-ev-io-drop l d (bcReq1 r) {e₁ = BF.sendBF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | yes refl = bcSil BF.stBusy , wev τ*-refl (RFBF.renameMap-ev-fwd (bfc-fire-req1 l d r)) τ*-refl , mkMbfc l d (bcSil BF.stBusy) Meq (just-injective (sym ceq)) , s≤s (s≤s (s≤s z≤n))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-io-drop l d (bcReq1 r) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-io-drop l d (bcReq1 r) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-io-drop l d (bcReq1 r) {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bcDone1: sendBF → bcSil stDone (1 → 0)
decBFc-ev-io-drop l d (bcDone1) {e₁ = BF.sendBF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcDone1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | yes refl = bcSil BF.stDone , wev τ*-refl (RFBF.renameMap-ev-fwd (bfc-fire-cdone1 l d)) τ*-refl , mkMbfc l d (bcSil BF.stDone) Meq (just-injective (sym ceq)) , s≤s z≤n
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-io-drop l d (bcDone1) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-io-drop l d (bcDone1) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-io-drop l d (bcDone1) {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bcBlk1 b: fires api recvBFBlock → no io fire (refuted)
decBFc-ev-io-drop l d (bcBlk1 b) {e₁ = BF.sendBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-io-drop l d (bcBlk1 b) {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible for every position
decBFc-ev-io-drop l d pos {e₁ = BF.apiBFev l' d' m} iomem step = ⊥-elim iomem
decBFc-ev-io-drop l d pos {e₁ = BF.doneBF  l' d'}   iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- BF-SERVER (`decBFs-ev-io-drop`).  `bsHead stIdle` RECEIVES a request (io) →
-- api-offer / done leaf; the reply SEND positions fire `sendBF`.
------------------------------------------------------------------------

bfs-hstep-io-drop : (l : Link) (d : Dir) (st : BF.BFState)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιBF e₁) a
  → absBFs l d (bsHead st) ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M
  → Σ[ pos′ ∈ BFsPos ] (decBFs l d (bsHead st) ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► decBFs l d pos′)
      × (M ≡ absBFs l d pos′)
      × (posWt-BFs pos′ < posWt-BFsSt st)

-- stIdle: receives RequestRange (→bsReq1, 0<1) / ClientDone (→bsDone1, 0<1)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgRequestRange r)} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsReq1 r , RFBF.renameMap-ev-fwd (bfs-fire-req l d r t0 md ln) , mkMbfs l d (bsReq1 r) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgClientDone} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsDone1 , RFBF.renameMap-ev-fwd (bfs-fire-cdone l d t0 md ln) , mkMbfs l d (bsDone1) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive _} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync _} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission _} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify _} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch _} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stIdle {e₁ = BF.sendBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stBusy / stStreaming: api-send only → no io fire
bfs-hstep-io-drop l d BF.stBusy {e₁ = BF.sendBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stBusy {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stStreaming {e₁ = BF.sendBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stStreaming {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stDone {e₁ = BF.sendBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep-io-drop l d BF.stDone {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible
bfs-hstep-io-drop l d st {e₁ = BF.apiBFev l' d' m} iomem step = ⊥-elim iomem
bfs-hstep-io-drop l d st {e₁ = BF.doneBF  l' d'}   iomem step = ⊥-elim iomem

-- the BF-server io-drop leaf
decBFs-ev-io-drop : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιBF e₁) a
  → absBFs l d pos ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M
  → Σ[ pos′ ∈ BFsPos ] (decBFs l d pos ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFs l d pos′)
      × (M ≡ absBFs l d pos′)
      × (posWt-BFs pos′ < posWt-BFs pos)

decBFs-ev-io-drop l d (bsHead st) iomem step with bfs-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decBFs-ev-io-drop l d (bsSil st) iomem step with bfs-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decBFs-sil-step l d st) τ*-refl) f τ*-refl , m , dr

-- bsReq1 r / bsDone1: api-offer / done leaf → no io fire (refuted)
decBFs-ev-io-drop l d (bsReq1 r) {e₁ = BF.sendBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsReq1 r) {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsDone1) {e₁ = BF.sendBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsDone1) {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bsStart1: sendBF → bsSil stStreaming (1 → 0)
decBFs-ev-io-drop l d (bsStart1) {e₁ = BF.sendBF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsStart1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | yes refl = bsSil BF.stStreaming , wev τ*-refl (RFBF.renameMap-ev-fwd (bfs-fire-start1 l d)) τ*-refl , mkMbfs l d (bsSil BF.stStreaming) Meq (just-injective (sym ceq)) , s≤s z≤n
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsStart1) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsStart1) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsStart1) {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsStart1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bsNoBlk1: sendBF → bsSil stIdle (2 → 1)
decBFs-ev-io-drop l d (bsNoBlk1) {e₁ = BF.sendBF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsNoBlk1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | yes refl = bsSil BF.stIdle , wev τ*-refl (RFBF.renameMap-ev-fwd (bfs-fire-noblk1 l d)) τ*-refl , mkMbfs l d (bsSil BF.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsNoBlk1) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsNoBlk1) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsNoBlk1) {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsNoBlk1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bsBlk1 b: sendBF → bsSil stStreaming (1 → 0)
decBFs-ev-io-drop l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | yes refl = bsSil BF.stStreaming , wev τ*-refl (RFBF.renameMap-ev-fwd (bfs-fire-blk1 l d b)) τ*-refl , mkMbfs l d (bsSil BF.stStreaming) Meq (just-injective (sym ceq)) , s≤s z≤n
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsBlk1 b) {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bsBatchDone1: sendBF → bsSil stIdle (2 → 1)
decBFs-ev-io-drop l d (bsBatchDone1) {e₁ = BF.sendBF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBatchDone1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | yes refl = bsSil BF.stIdle , wev τ*-refl (RFBF.renameMap-ev-fwd (bfs-fire-batch1 l d)) τ*-refl , mkMbfs l d (bsSil BF.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsBatchDone1) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsBatchDone1) {e₁ = BF.sendBF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-io-drop l d (bsBatchDone1) {e₁ = BF.receiveBF l' d'} iomem step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBatchDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible for every position
decBFs-ev-io-drop l d pos {e₁ = BF.apiBFev l' d' m} iomem step = ⊥-elim iomem
decBFs-ev-io-drop l d pos {e₁ = BF.doneBF  l' d'}   iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- KA-CLIENT (`decKAc-ev-io-drop`).  `stServer` RECEIVES the response (io);
-- `kcReq1`/`kcDone1` fire `sendKA`.  `kcErr1` refutes via its `≢` witness.
------------------------------------------------------------------------

kac-hstep-io-drop : (l : Link) (d : Dir) (st : KA.KAState)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιKA e₁) a
  → absKAc l d (kcHead st) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M
  → Σ[ pos′ ∈ KAcPos ] (decKAc l d (kcHead st) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► decKAc l d pos′)
      × (M ≡ absKAc l d pos′)
      × (posWt-KAc pos′ < posWt-KAcSt st)

-- stClient: api-send only → no io fire
kac-hstep-io-drop l d KA.stClient {e₁ = KA.sendKA l' d'} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep-io-drop l d KA.stClient {e₁ = KA.receiveKA l' d'} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stServer cq: receives MsgKeepAliveResponse → kcSil stClient (0<1)
kac-hstep-io-drop l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAliveResponse cr)} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = kcSil KA.stClient , RFKA.renameMap-ev-fwd (kac-fire-resp l d cq cr t0 md ln) , mkMkac l d (kcSil KA.stClient) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
kac-hstep-io-drop l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAlive c)} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep-io-drop l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive MsgKADone} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep-io-drop l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep-io-drop l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep-io-drop l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep-io-drop l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep-io-drop l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep-io-drop l d (KA.stServer cq) {e₁ = KA.sendKA l' d'} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stDone: terminal
kac-hstep-io-drop l d KA.stDone {e₁ = KA.sendKA l' d'} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep-io-drop l d KA.stDone {e₁ = KA.receiveKA l' d'} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible
kac-hstep-io-drop l d st {e₁ = KA.apiKAev l' d' m} iomem step = ⊥-elim iomem
kac-hstep-io-drop l d st {e₁ = KA.doneKA  l' d'}   iomem step = ⊥-elim iomem

-- the KA-client io-drop leaf
decKAc-ev-io-drop : (l : Link) (d : Dir) (pos : KAcPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιKA e₁) a
  → absKAc l d pos ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M
  → Σ[ pos′ ∈ KAcPos ] (decKAc l d pos ═[ ev (evl (evLabel X (ιKA e₁) a)) ]═► decKAc l d pos′)
      × (M ≡ absKAc l d pos′)
      × (posWt-KAc pos′ < posWt-KAc pos)

decKAc-ev-io-drop l d (kcHead st) iomem step with kac-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decKAc-ev-io-drop l d (kcSil st) iomem step with kac-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decKAc-sil-step l d st) τ*-refl) f τ*-refl , m , dr
-- kcErr1: refuted by its own inequality witness
decKAc-ev-io-drop l d (kcErr1 cq cr ne) iomem step = ⊥-elim (ne refl)

-- kcReq1 c: sendKA → kcSil (stServer c) (2 → 1)
decKAc-ev-io-drop l d (kcReq1 c) {e₁ = KA.sendKA l' d'} {a} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcReq1 c)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c))
...     | yes refl = kcSil (KA.stServer c) , wev τ*-refl (RFKA.renameMap-ev-fwd (kac-fire-req1 l d c)) τ*-refl , mkMkac l d (kcSil (KA.stServer c)) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-io-drop l d (kcReq1 c) {e₁ = KA.sendKA l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-io-drop l d (kcReq1 c) {e₁ = KA.sendKA l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-io-drop l d (kcReq1 c) {e₁ = KA.receiveKA l' d'} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcReq1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- kcDone1: sendKA → kcSil stDone (1 → 0)
decKAc-ev-io-drop l d kcDone1 {e₁ = KA.sendKA l' d'} {a} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc kcDone1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive MsgKADone)
...     | yes refl = kcSil KA.stDone , wev τ*-refl (RFKA.renameMap-ev-fwd (kac-fire-done1 l d)) τ*-refl , mkMkac l d (kcSil KA.stDone) Meq (just-injective (sym ceq)) , s≤s z≤n
...     | no _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-io-drop l d kcDone1 {e₁ = KA.sendKA l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-io-drop l d kcDone1 {e₁ = KA.sendKA l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-io-drop l d kcDone1 {e₁ = KA.receiveKA l' d'} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc kcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- kcTermE1: terminal
decKAc-ev-io-drop l d kcTermE1 {e₁ = KA.sendKA l' d'} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc kcTermE1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAc-ev-io-drop l d kcTermE1 {e₁ = KA.receiveKA l' d'} iomem step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc kcTermE1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible for every position
decKAc-ev-io-drop l d pos {e₁ = KA.apiKAev l' d' m} iomem step = ⊥-elim iomem
decKAc-ev-io-drop l d pos {e₁ = KA.doneKA  l' d'}   iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- KA-SERVER (`decKAs-ev-io-drop`).  `stClient` RECEIVES a request; `stServer`
-- SENDS the response (both head fires).  `ksRecv1`/`ksDdone1` fire api/done.
------------------------------------------------------------------------

kas-hstep-io-drop : (l : Link) (d : Dir) (st : KA.KAState)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιKA e₁) a
  → absKAs l d (ksHead st) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M
  → Σ[ pos′ ∈ KAsPos ] (decKAs l d (ksHead st) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► decKAs l d pos′)
      × (M ≡ absKAs l d pos′)
      × (posWt-KAs pos′ < posWt-KAsSt st)

-- stClient: receives MsgKeepAlive (→ksRecv1, 0<1) / MsgKADone (→ksDdone1, 0<1)
kas-hstep-io-drop l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAlive c)} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ksRecv1 c , RFKA.renameMap-ev-fwd (kas-fire-recv l d c t0 md ln) , mkMkas l d (ksRecv1 c) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive MsgKADone} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ksDdone1 , RFKA.renameMap-ev-fwd (kas-fire-ddone l d t0 md ln) , mkMkas l d ksDdone1 Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAliveResponse c)} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d KA.stClient {e₁ = KA.sendKA l' d'} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stServer c: sends MsgKeepAliveResponse → ksSil stClient (2 → 1)
kas-hstep-io-drop l d (KA.stServer c) {e₁ = KA.sendKA l' d'} {a} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead (KA.stServer c))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c))
...     | yes refl = ksSil KA.stClient , RFKA.renameMap-ev-fwd (kas-fire-sresp l d c) , mkMkas l d (ksSil KA.stClient) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d (KA.stServer c) {e₁ = KA.sendKA l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d (KA.stServer c) {e₁ = KA.sendKA l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d (KA.stServer c) {e₁ = KA.receiveKA l' d'} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead (KA.stServer c))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stDone: terminal
kas-hstep-io-drop l d KA.stDone {e₁ = KA.sendKA l' d'} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep-io-drop l d KA.stDone {e₁ = KA.receiveKA l' d'} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible
kas-hstep-io-drop l d st {e₁ = KA.apiKAev l' d' m} iomem step = ⊥-elim iomem
kas-hstep-io-drop l d st {e₁ = KA.doneKA  l' d'}   iomem step = ⊥-elim iomem

-- the KA-server io-drop leaf
decKAs-ev-io-drop : (l : Link) (d : Dir) (pos : KAsPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιKA e₁) a
  → absKAs l d pos ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M
  → Σ[ pos′ ∈ KAsPos ] (decKAs l d pos ═[ ev (evl (evLabel X (ιKA e₁) a)) ]═► decKAs l d pos′)
      × (M ≡ absKAs l d pos′)
      × (posWt-KAs pos′ < posWt-KAs pos)

decKAs-ev-io-drop l d (ksHead st) iomem step with kas-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decKAs-ev-io-drop l d (ksSil st) iomem step with kas-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decKAs-sil-step l d st) τ*-refl) f τ*-refl , m , dr

-- ksRecv1 c / ksDdone1: api / done leaf → no io fire (refuted)
decKAs-ev-io-drop l d (ksRecv1 c) {e₁ = KA.sendKA l' d'} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksRecv1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAs-ev-io-drop l d (ksRecv1 c) {e₁ = KA.receiveKA l' d'} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksRecv1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAs-ev-io-drop l d ksDdone1 {e₁ = KA.sendKA l' d'} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs ksDdone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAs-ev-io-drop l d ksDdone1 {e₁ = KA.receiveKA l' d'} iomem step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs ksDdone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible for every position
decKAs-ev-io-drop l d pos {e₁ = KA.apiKAev l' d' m} iomem step = ⊥-elim iomem
decKAs-ev-io-drop l d pos {e₁ = KA.doneKA  l' d'}   iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- TS-CLIENT (`decTSc-ev-io-drop`).  Role-inverted: `stInit` auto-SENDS Init;
-- `stIdle` RECEIVES requests; the reply positions fire `sendTS`.
------------------------------------------------------------------------

tc-hstep-io-drop : (l : Link) (d : Dir) (st : TS.TSState)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιTS e₁) a
  → absTSc l d (tcHead st) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M
  → Σ[ pos′ ∈ TScPos ] (decTSc l d (tcHead st) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► decTSc l d pos′)
      × (M ≡ absTSc l d pos′)
      × (posWt-TSc pos′ < posWt-TScSt st)

-- stInit: sends Init → tcSil stIdle (2 → 1)
tc-hstep-io-drop l d TS.stInit {e₁ = TS.sendTS l' d'} {a} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stInit)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit)
...     | yes refl = tcSil TS.stIdle , RFTS.renameMap-ev-fwd (tc-fire-init l d) , mkMtsc l d (tcSil TS.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stInit {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stInit {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stIdle: receives RequestTxIds (Blocking/NonBlocking) / RequestTxs (0<1)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds Blocking aa rr)} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tcReqIdsB1 aa rr , RFTS.renameMap-ev-fwd (tc-fire-reqB l d aa rr t0 md ln) , mkMtsc l d (tcReqIdsB1 aa rr) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds NonBlocking aa rr)} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tcReqIdsNB1 aa rr , RFTS.renameMap-ev-fwd (tc-fire-reqNB l d aa rr t0 md ln) , mkMtsc l d (tcReqIdsNB1 aa rr) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxs ids)} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tcReqTxs1 ids , RFTS.renameMap-ev-fwd (tc-fire-reqTxs l d ids t0 md ln) , mkMtsc l d (tcReqTxs1 ids) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stIdle {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stTxIdsBlocking / stTxIdsNonBlocking / stTxs: api-send → no io fire
tc-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stTxs {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stDone {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep-io-drop l d TS.stDone {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible
tc-hstep-io-drop l d st {e₁ = TS.apiTSev l' d' m} iomem step = ⊥-elim iomem
tc-hstep-io-drop l d st {e₁ = TS.doneTS  l' d'}   iomem step = ⊥-elim iomem

-- the TS-client io-drop leaf
decTSc-ev-io-drop : (l : Link) (d : Dir) (pos : TScPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιTS e₁) a
  → absTSc l d pos ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M
  → Σ[ pos′ ∈ TScPos ] (decTSc l d pos ═[ ev (evl (evLabel X (ιTS e₁) a)) ]═► decTSc l d pos′)
      × (M ≡ absTSc l d pos′)
      × (posWt-TSc pos′ < posWt-TSc pos)

decTSc-ev-io-drop l d (tcHead st) iomem step with tc-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decTSc-ev-io-drop l d (tcSil st) iomem step with tc-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decTSc-sil-step l d st) τ*-refl) f τ*-refl , m , dr

-- tcReqIdsB1/tcReqIdsNB1/tcReqTxs1: api-offer leaves → no io fire (refuted)
decTSc-ev-io-drop l d (tcReqIdsB1 aa rr) {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcReqIdsB1 aa rr) {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcReqIdsNB1 aa rr) {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcReqIdsNB1 aa rr) {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcReqTxs1 ids) {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcReqTxs1 ids) {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- tcRepB1 ids: sendTS → tcSil stIdle (2 → 1)
decTSc-ev-io-drop l d (tcRepB1 ids) {e₁ = TS.sendTS l' d'} {a} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepB1 ids)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | yes refl = tcSil TS.stIdle , wev τ*-refl (RFTS.renameMap-ev-fwd (tc-fire-wri1B l d ids)) τ*-refl , mkMtsc l d (tcSil TS.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcRepB1 ids) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcRepB1 ids) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcRepB1 ids) {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepB1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- tcRepNB1 ids: sendTS → tcSil stIdle (2 → 1)
decTSc-ev-io-drop l d (tcRepNB1 ids) {e₁ = TS.sendTS l' d'} {a} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepNB1 ids)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | yes refl = tcSil TS.stIdle , wev τ*-refl (RFTS.renameMap-ev-fwd (tc-fire-wri1NB l d ids)) τ*-refl , mkMtsc l d (tcSil TS.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcRepNB1 ids) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcRepNB1 ids) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcRepNB1 ids) {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepNB1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- tcRepTxs1 txs: sendTS → tcSil stIdle (2 → 1)
decTSc-ev-io-drop l d (tcRepTxs1 txs) {e₁ = TS.sendTS l' d'} {a} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepTxs1 txs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs))
...     | yes refl = tcSil TS.stIdle , wev τ*-refl (RFTS.renameMap-ev-fwd (tc-fire-wrt1 l d txs)) τ*-refl , mkMtsc l d (tcSil TS.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcRepTxs1 txs) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcRepTxs1 txs) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d (tcRepTxs1 txs) {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepTxs1 txs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- tcDone1: sendTS → tcSil stDone (1 → 0)
decTSc-ev-io-drop l d tcDone1 {e₁ = TS.sendTS l' d'} {a} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc tcDone1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone)
...     | yes refl = tcSil TS.stDone , wev τ*-refl (RFTS.renameMap-ev-fwd (tc-fire-wdone1 l d)) τ*-refl , mkMtsc l d (tcSil TS.stDone) Meq (just-injective (sym ceq)) , s≤s z≤n
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d tcDone1 {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d tcDone1 {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-io-drop l d tcDone1 {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc tcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible for every position
decTSc-ev-io-drop l d pos {e₁ = TS.apiTSev l' d' m} iomem step = ⊥-elim iomem
decTSc-ev-io-drop l d pos {e₁ = TS.doneTS  l' d'}   iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- TS-SERVER (`decTSs-ev-io-drop`).  `stInit` RECEIVES Init; the outstanding
-- states RECEIVE replies; the request positions fire `sendTS`.
------------------------------------------------------------------------

ts-hstep-io-drop : (l : Link) (d : Dir) (st : TS.TSState)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιTS e₁) a
  → absTSs l d (tsHead st) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M
  → Σ[ pos′ ∈ TSsPos ] (decTSs l d (tsHead st) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► decTSs l d pos′)
      × (M ≡ absTSs l d pos′)
      × (posWt-TSs pos′ < posWt-TSsSt st)

-- stInit: receives Init → tsSil stIdle (0<1)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSInit} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsSil TS.stIdle , RFTS.renameMap-ev-fwd (ts-fire-init l d t0 md ln) , mkMtss l d (tsSil TS.stIdle) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stInit {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stIdle: api-send requests → no io fire
ts-hstep-io-drop l d TS.stIdle {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stIdle {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stTxIdsBlocking: receives ReplyTxIds (→stIdle) / Done (→tsDone1) (0<1)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsSil TS.stIdle , RFTS.renameMap-ev-fwd (ts-fire-blkReply l d ids t0 md ln) , mkMtss l d (tsSil TS.stIdle) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSDone} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsDone1 , RFTS.renameMap-ev-fwd (ts-fire-blkDone l d t0 md ln) , mkMtss l d tsDone1 Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsBlocking {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stTxIdsNonBlocking: receives ReplyTxIds → stIdle (0<1)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsSil TS.stIdle , RFTS.renameMap-ev-fwd (ts-fire-nblReply l d ids t0 md ln) , mkMtss l d (tsSil TS.stIdle) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxIdsNonBlocking {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stTxs: receives ReplyTxs → stIdle (0<1)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxs txs)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsSil TS.stIdle , RFTS.renameMap-ev-fwd (ts-fire-txsReply l d txs t0 md ln) , mkMtss l d (tsSil TS.stIdle) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stTxs {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stDone: terminal
ts-hstep-io-drop l d TS.stDone {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep-io-drop l d TS.stDone {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible
ts-hstep-io-drop l d st {e₁ = TS.apiTSev l' d' m} iomem step = ⊥-elim iomem
ts-hstep-io-drop l d st {e₁ = TS.doneTS  l' d'}   iomem step = ⊥-elim iomem

-- the TS-server io-drop leaf
decTSs-ev-io-drop : (l : Link) (d : Dir) (pos : TSsPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιTS e₁) a
  → absTSs l d pos ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M
  → Σ[ pos′ ∈ TSsPos ] (decTSs l d pos ═[ ev (evl (evLabel X (ιTS e₁) a)) ]═► decTSs l d pos′)
      × (M ≡ absTSs l d pos′)
      × (posWt-TSs pos′ < posWt-TSs pos)

decTSs-ev-io-drop l d (tsHead st) iomem step with ts-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decTSs-ev-io-drop l d (tsSil st) iomem step with ts-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decTSs-sil-step l d st) τ*-refl) f τ*-refl , m , dr

-- tsReqB1 (aa,rr): sendTS → tsSil stTxIdsBlocking (2 → 1)
decTSs-ev-io-drop l d (tsReqB1 (aa , rr)) {e₁ = TS.sendTS l' d'} {a} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqB1 (aa , rr))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking aa rr))
...     | yes refl = tsSil TS.stTxIdsBlocking , wev τ*-refl (RFTS.renameMap-ev-fwd (ts-fire-wib1 l d aa rr)) τ*-refl , mkMtss l d (tsSil TS.stTxIdsBlocking) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-io-drop l d (tsReqB1 (aa , rr)) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-io-drop l d (tsReqB1 (aa , rr)) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-io-drop l d (tsReqB1 (aa , rr)) {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqB1 (aa , rr))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- tsReqNB1 (aa,rr): sendTS → tsSil stTxIdsNonBlocking (2 → 1)
decTSs-ev-io-drop l d (tsReqNB1 (aa , rr)) {e₁ = TS.sendTS l' d'} {a} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqNB1 (aa , rr))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking aa rr))
...     | yes refl = tsSil TS.stTxIdsNonBlocking , wev τ*-refl (RFTS.renameMap-ev-fwd (ts-fire-win1 l d aa rr)) τ*-refl , mkMtss l d (tsSil TS.stTxIdsNonBlocking) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-io-drop l d (tsReqNB1 (aa , rr)) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-io-drop l d (tsReqNB1 (aa , rr)) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-io-drop l d (tsReqNB1 (aa , rr)) {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqNB1 (aa , rr))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- tsReqTxs1 ids: sendTS → tsSil stTxs (2 → 1)
decTSs-ev-io-drop l d (tsReqTxs1 ids) {e₁ = TS.sendTS l' d'} {a} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqTxs1 ids)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids))
...     | yes refl = tsSil TS.stTxs , wev τ*-refl (RFTS.renameMap-ev-fwd (ts-fire-wrt1 l d ids)) τ*-refl , mkMtss l d (tsSil TS.stTxs) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-io-drop l d (tsReqTxs1 ids) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-io-drop l d (tsReqTxs1 ids) {e₁ = TS.sendTS l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-io-drop l d (tsReqTxs1 ids) {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- tsDone1: fires doneTS → no io fire (refuted)
decTSs-ev-io-drop l d tsDone1 {e₁ = TS.sendTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs tsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-io-drop l d tsDone1 {e₁ = TS.receiveTS l' d'} iomem step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs tsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible for every position
decTSs-ev-io-drop l d pos {e₁ = TS.apiTSev l' d' m} iomem step = ⊥-elim iomem
decTSs-ev-io-drop l d pos {e₁ = TS.doneTS  l' d'}   iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- LN-CLIENT (`decLNc-ev-io-drop`).  `stBusy` RECEIVES a notification (io);
-- `lncReq1`/`lncDone1` fire `sendLN`.
------------------------------------------------------------------------

lnc-hstep-io-drop : (l : Link) (d : Dir) (st : LN.LNState)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιLN e₁) a
  → absLNc l d (lncHead st) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M
  → Σ[ pos′ ∈ LNcPos ] (decLNc l d (lncHead st) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► decLNc l d pos′)
      × (M ≡ absLNc l d pos′)
      × (posWt-LNc pos′ < posWt-LNcSt st)

-- stIdle: api-send only → no io fire
lnc-hstep-io-drop l d LN.stIdle {e₁ = LN.sendLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stBusy: receives one notification → lncR*1 (0<1)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockAnnouncement h)} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lncRann1 h , RFLN.renameMap-ev-fwd (lnc-fire-rann l d h t0 md ln) , mkMlnc l d (lncRann1 h) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockOffer q)} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lncRoff1 q , RFLN.renameMap-ev-fwd (lnc-fire-roff l d q t0 md ln) , mkMlnc l d (lncRoff1 q) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockTxsOffer q)} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lncRtxs1 q , RFLN.renameMap-ev-fwd (lnc-fire-rtxs l d q t0 md ln) , mkMlnc l d (lncRtxs1 q) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNVotesOffer vs)} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lncRvot1 vs , RFLN.renameMap-ev-fwd (lnc-fire-rvot l d vs t0 md ln) , mkMlnc l d (lncRvot1 vs) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNRequestNext} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNDone} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stBusy {e₁ = LN.sendLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stDone: terminal
lnc-hstep-io-drop l d LN.stDone {e₁ = LN.sendLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep-io-drop l d LN.stDone {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible
lnc-hstep-io-drop l d st {e₁ = LN.apiLNev l' d' m} iomem step = ⊥-elim iomem
lnc-hstep-io-drop l d st {e₁ = LN.doneLN  l' d'}   iomem step = ⊥-elim iomem

-- the LN-client io-drop leaf
decLNc-ev-io-drop : (l : Link) (d : Dir) (pos : LNcPos)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιLN e₁) a
  → absLNc l d pos ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M
  → Σ[ pos′ ∈ LNcPos ] (decLNc l d pos ═[ ev (evl (evLabel X (ιLN e₁) a)) ]═► decLNc l d pos′)
      × (M ≡ absLNc l d pos′)
      × (posWt-LNc pos′ < posWt-LNc pos)

decLNc-ev-io-drop l d (lncHead st) iomem step with lnc-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decLNc-ev-io-drop l d (lncSil st) iomem step with lnc-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decLNc-sil-step l d st) τ*-refl) f τ*-refl , m , dr

-- lncRann1/lncRoff1/lncRtxs1/lncRvot1: api-offer leaves → no io fire (refuted)
decLNc-ev-io-drop l d (lncRann1 h) {e₁ = LN.sendLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d (lncRann1 h) {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d (lncRoff1 q) {e₁ = LN.sendLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d (lncRoff1 q) {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d (lncRtxs1 q) {e₁ = LN.sendLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d (lncRtxs1 q) {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d (lncRvot1 vs) {e₁ = LN.sendLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d (lncRvot1 vs) {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- lncReq1: sendLN → lncSil stBusy (2 → 1)
decLNc-ev-io-drop l d lncReq1 {e₁ = LN.sendLN l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncReq1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext)
...     | yes refl = lncSil LN.stBusy , wev τ*-refl (RFLN.renameMap-ev-fwd (lnc-fire-wreq1 l d)) τ*-refl , mkMlnc l d (lncSil LN.stBusy) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d lncReq1 {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d lncReq1 {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d lncReq1 {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncReq1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- lncDone1: sendLN → lncSil stDone (1 → 0)
decLNc-ev-io-drop l d lncDone1 {e₁ = LN.sendLN l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncDone1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone)
...     | yes refl = lncSil LN.stDone , wev τ*-refl (RFLN.renameMap-ev-fwd (lnc-fire-wdone1 l d)) τ*-refl , mkMlnc l d (lncSil LN.stDone) Meq (just-injective (sym ceq)) , s≤s z≤n
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d lncDone1 {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d lncDone1 {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-io-drop l d lncDone1 {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible for every position
decLNc-ev-io-drop l d pos {e₁ = LN.apiLNev l' d' m} iomem step = ⊥-elim iomem
decLNc-ev-io-drop l d pos {e₁ = LN.doneLN  l' d'}   iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- LN-SERVER (`decLNs-ev-io-drop`).  `stIdle` RECEIVES the request; the notify
-- SEND positions fire `sendLN`.
------------------------------------------------------------------------

lns-hstep-io-drop : (l : Link) (d : Dir) (st : LN.LNState)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιLN e₁) a
  → absLNs l d (lnsHead st) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M
  → Σ[ pos′ ∈ LNsPos ] (decLNs l d (lnsHead st) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► decLNs l d pos′)
      × (M ≡ absLNs l d pos′)
      × (posWt-LNs pos′ < posWt-LNsSt st)

-- stIdle: receives RequestNext (→stBusy) / Done (→lnsDone1) (0<1)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNRequestNext} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lnsSil LN.stBusy , RFLN.renameMap-ev-fwd (lns-fire-idleReq l d t0 md ln) , mkMlns l d (lnsSil LN.stBusy) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNDone} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lnsDone1 , RFLN.renameMap-ev-fwd (lns-fire-idleDone l d t0 md ln) , mkMlns l d (lnsDone1) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stIdle {e₁ = LN.sendLN l' d'} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stBusy: api-send notifications → no io fire
lns-hstep-io-drop l d LN.stBusy {e₁ = LN.sendLN l' d'} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stBusy {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stDone {e₁ = LN.sendLN l' d'} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep-io-drop l d LN.stDone {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible
lns-hstep-io-drop l d st {e₁ = LN.apiLNev l' d' m} iomem step = ⊥-elim iomem
lns-hstep-io-drop l d st {e₁ = LN.doneLN  l' d'}   iomem step = ⊥-elim iomem

-- the LN-server io-drop leaf
decLNs-ev-io-drop : (l : Link) (d : Dir) (pos : LNsPos)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιLN e₁) a
  → absLNs l d pos ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M
  → Σ[ pos′ ∈ LNsPos ] (decLNs l d pos ═[ ev (evl (evLabel X (ιLN e₁) a)) ]═► decLNs l d pos′)
      × (M ≡ absLNs l d pos′)
      × (posWt-LNs pos′ < posWt-LNs pos)

decLNs-ev-io-drop l d (lnsHead st) iomem step with lns-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decLNs-ev-io-drop l d (lnsSil st) iomem step with lns-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decLNs-sil-step l d st) τ*-refl) f τ*-refl , m , dr

-- lnsDone1: fires doneLN → no io fire (refuted)
decLNs-ev-io-drop l d lnsDone1 {e₁ = LN.sendLN l' d'} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs lnsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d lnsDone1 {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs lnsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- lnsWann1/lnsWoff1/lnsWtxs1/lnsWvot1: sendLN → lnsSil stIdle (2 → 1)
decLNs-ev-io-drop l d (lnsWann1 h) {e₁ = LN.sendLN l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWann1 h)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h))
...     | yes refl = lnsSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lns-fire-wann1 l d h)) τ*-refl , mkMlns l d (lnsSil LN.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWann1 h) {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWann1 h) {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWann1 h) {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWoff1 q) {e₁ = LN.sendLN l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWoff1 q)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q))
...     | yes refl = lnsSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lns-fire-woff1 l d q)) τ*-refl , mkMlns l d (lnsSil LN.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWoff1 q) {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWoff1 q) {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWoff1 q) {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWtxs1 q) {e₁ = LN.sendLN l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWtxs1 q)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q))
...     | yes refl = lnsSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lns-fire-wtxs1 l d q)) τ*-refl , mkMlns l d (lnsSil LN.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWtxs1 q) {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWtxs1 q) {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWtxs1 q) {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWvot1 vs) {e₁ = LN.sendLN l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWvot1 vs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs))
...     | yes refl = lnsSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lns-fire-wvot1 l d vs)) τ*-refl , mkMlns l d (lnsSil LN.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWvot1 vs) {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWvot1 vs) {e₁ = LN.sendLN l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-io-drop l d (lnsWvot1 vs) {e₁ = LN.receiveLN l' d'} iomem step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- api / done under io are impossible for every position
decLNs-ev-io-drop l d pos {e₁ = LN.apiLNev l' d' m} iomem step = ⊥-elim iomem
decLNs-ev-io-drop l d pos {e₁ = LN.doneLN  l' d'}   iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- LF-CLIENT (`decLFc-ev-io-drop`).  Delivery states RECEIVE payloads; the
-- request positions fire `sendLF`.
------------------------------------------------------------------------

lfc-hstep-io-drop : (l : Link) (d : Dir) (st : LF.LFState)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιLF e₁) a
  → absLFc l d (lfcHead st) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M
  → Σ[ pos′ ∈ LFcPos ] (decLFc l d (lfcHead st) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► decLFc l d pos′)
      × (M ≡ absLFc l d pos′)
      × (posWt-LFc pos′ < posWt-LFcSt st)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlock b)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcRblk1 b , RFLF.renameMap-ev-fwd (lfc-fire-rblk l d b t0 md ln) , mkMlfc l d (lfcRblk1 b) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlock {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxs ts)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcRbtx1 ts , RFLF.renameMap-ev-fwd (lfc-fire-rbtx l d ts t0 md ln) , mkMlfc l d (lfcRbtx1 ts) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVoteDelivery vs)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcRvot1 vs , RFLF.renameMap-ev-fwd (lfc-fire-rvot l d vs t0 md ln) , mkMlfc l d (lfcRvot1 vs) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stVotes {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcRnext1 b ts , RFLF.renameMap-ev-fwd (lfc-fire-rnext l d b ts t0 md ln) , mkMlfc l d (lfcRnext1 b ts) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcRlast1 b ts , RFLF.renameMap-ev-fwd (lfc-fire-rlast l d b ts t0 md ln) , mkMlfc l d (lfcRlast1 b ts) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stBlockRange {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stIdle {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stDone {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d LF.stDone {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep-io-drop l d st {e₁ = LF.apiLFev l' d' m} iomem step = ⊥-elim iomem
lfc-hstep-io-drop l d st {e₁ = LF.doneLF  l' d'}   iomem step = ⊥-elim iomem

decLFc-ev-io-drop : (l : Link) (d : Dir) (pos : LFcPos)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιLF e₁) a
  → absLFc l d pos ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M
  → Σ[ pos′ ∈ LFcPos ] (decLFc l d pos ═[ ev (evl (evLabel X (ιLF e₁) a)) ]═► decLFc l d pos′)
      × (M ≡ absLFc l d pos′)
      × (posWt-LFc pos′ < posWt-LFc pos)
decLFc-ev-io-drop l d (lfcHead st) iomem step with lfc-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decLFc-ev-io-drop l d (lfcSil st) iomem step with lfc-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decLFc-sil-step l d st) τ*-refl) f τ*-refl , m , dr
decLFc-ev-io-drop l d (lfcRblk1 b) {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcRblk1 b) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcRbtx1 ts) {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcRbtx1 ts) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcRvot1 vs) {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcRvot1 vs) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcRnext1 b ts) {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcRnext1 b ts) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcRlast1 b ts) {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcRlast1 b ts) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWblk1 pt) {e₁ = LF.sendLF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWblk1 pt)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt))
...     | yes refl = lfcSil LF.stBlock , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-wblk1 l d pt)) τ*-refl , mkMlfc l d (lfcSil LF.stBlock) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWblk1 pt) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWblk1 pt) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWblk1 pt) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWblk1 pt)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWtxs1 (pt , bm)) {e₁ = LF.sendLF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWtxs1 (pt , bm))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm))
...     | yes refl = lfcSil LF.stBlockTxs , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-wtxs1 l d pt bm)) τ*-refl , mkMlfc l d (lfcSil LF.stBlockTxs) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWtxs1 (pt , bm)) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWtxs1 (pt , bm)) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWtxs1 (pt , bm)) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWtxs1 (pt , bm))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWvot1 vs) {e₁ = LF.sendLF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWvot1 vs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs))
...     | yes refl = lfcSil LF.stVotes , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-wvot1 l d vs)) τ*-refl , mkMlfc l d (lfcSil LF.stVotes) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWvot1 vs) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWvot1 vs) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWvot1 vs) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWrng1 r) {e₁ = LF.sendLF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWrng1 r)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r))
...     | yes refl = lfcSil LF.stBlockRange , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-wrng1 l d r)) τ*-refl , mkMlfc l d (lfcSil LF.stBlockRange) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWrng1 r) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWrng1 r) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcWrng1 r) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWrng1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcDone1) {e₁ = LF.sendLF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcDone1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFDone))
...     | yes refl = lfcSil LF.stDone , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-wdone1 l d)) τ*-refl , mkMlfc l d (lfcSil LF.stDone) Meq (just-injective (sym ceq)) , s≤s z≤n
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcDone1) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcDone1) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d (lfcDone1) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-io-drop l d pos {e₁ = LF.apiLFev l' d' m} iomem step = ⊥-elim iomem
decLFc-ev-io-drop l d pos {e₁ = LF.doneLF  l' d'}   iomem step = ⊥-elim iomem


------------------------------------------------------------------------
-- LF-SERVER (`decLFs-ev-io-drop`).  `stIdle` RECEIVES a request; the delivery
-- SEND positions fire `sendLF`.
------------------------------------------------------------------------

lfs-hstep-io-drop : (l : Link) (d : Dir) (st : LF.LFState)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιLF e₁) a
  → absLFs l d (lfsHead st) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M
  → Σ[ pos′ ∈ LFsPos ] (decLFs l d (lfsHead st) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► decLFs l d pos′)
      × (M ≡ absLFs l d pos′)
      × (posWt-LFs pos′ < posWt-LFsSt st)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRequest pt)} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsSil LF.stBlock , RFLF.renameMap-ev-fwd (lfs-fire-ireq-blk l d pt t0 md ln) , mkMlfs l d (lfsSil LF.stBlock) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxsRequest pt bm)} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsSil LF.stBlockTxs , RFLF.renameMap-ev-fwd (lfs-fire-ireq-txs l d pt bm t0 md ln) , mkMlfs l d (lfsSil LF.stBlockTxs) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVotesRequest vs)} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsSil LF.stVotes , RFLF.renameMap-ev-fwd (lfs-fire-ireq-vot l d vs t0 md ln) , mkMlfs l d (lfsSil LF.stVotes) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRangeRequest r)} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsSil LF.stBlockRange , RFLF.renameMap-ev-fwd (lfs-fire-ireq-rng l d r t0 md ln) , mkMlfs l d (lfsSil LF.stBlockRange) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFDone)} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsDone1 , RFLF.renameMap-ev-fwd (lfs-fire-idone l d t0 md ln) , mkMlfs l d (lfsDone1) Meq (just-injective (sym ceq)) , s≤s z≤n
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , chainSync x} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stIdle {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stBlock {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stBlock {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stVotes {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stVotes {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stBlockRange {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stDone {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d LF.stDone {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep-io-drop l d st {e₁ = LF.apiLFev l' d' m} iomem step = ⊥-elim iomem
lfs-hstep-io-drop l d st {e₁ = LF.doneLF  l' d'}   iomem step = ⊥-elim iomem

decLFs-ev-io-drop : (l : Link) (d : Dir) (pos : LFsPos)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {M : NetProc}
  → ioES .mem (X , ιLF e₁) a
  → absLFs l d pos ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M
  → Σ[ pos′ ∈ LFsPos ] (decLFs l d pos ═[ ev (evl (evLabel X (ιLF e₁) a)) ]═► decLFs l d pos′)
      × (M ≡ absLFs l d pos′)
      × (posWt-LFs pos′ < posWt-LFs pos)
decLFs-ev-io-drop l d (lfsHead st) iomem step with lfs-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev τ*-refl f τ*-refl , m , dr
decLFs-ev-io-drop l d (lfsSil st) iomem step with lfs-hstep-io-drop l d st iomem step
... | pos′ , f , m , dr = pos′ , wev (τ*-step (decLFs-sil-step l d st) τ*-refl) f τ*-refl , m , dr
decLFs-ev-io-drop l d (lfsDone1) {e₁ = LF.sendLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsDone1) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWblk1 b) {e₁ = LF.sendLF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWblk1 b)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b))
...     | yes refl = lfsSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfs-fire-wblk1 l d b)) τ*-refl , mkMlfs l d (lfsSil LF.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWblk1 b) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWblk1 b) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWblk1 b) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWtxs1 ts) {e₁ = LF.sendLF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWtxs1 ts)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts))
...     | yes refl = lfsSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfs-fire-wtxs1 l d ts)) τ*-refl , mkMlfs l d (lfsSil LF.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWtxs1 ts) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWtxs1 ts) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWtxs1 ts) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWtxs1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWvot1 vs) {e₁ = LF.sendLF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWvot1 vs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs))
...     | yes refl = lfsSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfs-fire-wvot1 l d vs)) τ*-refl , mkMlfs l d (lfsSil LF.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWvot1 vs) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWvot1 vs) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWvot1 vs) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWnext1 (b , ts)) {e₁ = LF.sendLF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWnext1 (b , ts))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts))
...     | yes refl = lfsSil LF.stBlockRange , wev τ*-refl (RFLF.renameMap-ev-fwd (lfs-fire-wnext1 l d b ts)) τ*-refl , mkMlfs l d (lfsSil LF.stBlockRange) Meq (just-injective (sym ceq)) , s≤s z≤n
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWnext1 (b , ts)) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWnext1 (b , ts)) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWnext1 (b , ts)) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWnext1 (b , ts))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWlast1 (b , ts)) {e₁ = LF.sendLF l' d'} {a} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWlast1 (b , ts))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts))
...     | yes refl = lfsSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfs-fire-wlast1 l d b ts)) τ*-refl , mkMlfs l d (lfsSil LF.stIdle) Meq (just-injective (sym ceq)) , s≤s (s≤s z≤n)
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWlast1 (b , ts)) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWlast1 (b , ts)) {e₁ = LF.sendLF l' d'} iomem step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d (lfsWlast1 (b , ts)) {e₁ = LF.receiveLF l' d'} iomem step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWlast1 (b , ts))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-io-drop l d pos {e₁ = LF.apiLFev l' d' m} iomem step = ⊥-elim iomem
decLFs-ev-io-drop l d pos {e₁ = LF.doneLF  l' d'}   iomem step = ⊥-elim iomem


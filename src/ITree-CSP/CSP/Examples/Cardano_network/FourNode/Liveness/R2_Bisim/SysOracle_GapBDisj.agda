{-# OPTIONS --guardedness #-}

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_GapBDisj (blkA : Block₃) where

open import Level using (0ℓ; Level)
open import Data.Unit.Polymorphic using (⊤; tt)
open import Data.Unit using () renaming (tt to ttU; ⊤ to ⊤U)
open import Data.Bool using (Bool; true; false)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Maybe.Properties using (just-injective)
open import Data.Sum using (inj₁; inj₂; _⊎_)
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin) renaming (zero to fzero; suc to fsuc)
open import Data.Fin.Properties using (suc-injective)
open import Level using (Lift; lift)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Nullary using (¬_)
open import Relation.Binary.PropositionalEquality using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst)
open import Process_Trees using
  ( PTree; ExtI; AnyTypes; ContinueType; react; ret; sil; react-injective; sil-injective
  ; base; pair; fin )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using
  ( Net_Api; Net_Api-≟; Net; Net-≟; break
  ; input; output; sndmsg; rcvmsg; tx; sndack; rcvack; ack
  ; done; apiCS; apiBF; apiTS; apiKA; apiLN; apiLF )
open import CSP.Examples.Cardano_network.Data p using ( Payload; DecEq-Payload; Header; header; Vote )
open import CSP.Examples.Cardano_network.NetCommon p using ( ioES; ιNet; ιNet⁻¹; ιNet-linv )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( numLinks; linkConfig; Cookie )
import CSP.Operators {E = Net_Api Payload} (Net_Api-≟ {Payload}) as Op
open Op using ( _∥⇘_⇙_; _⦀_; _∖_; EventSet; _△_; △-merge; △-τ; ⦀Fin; Prefix₀ )
open Op using ( _>>_; _>>=_ )
import CSP.Laws.Traces.TraceLawsBind (Net_Api-≟ {Payload}) as TLB
open TLB using ( fBind-react; bindV-elim )
open EventSet using ( mem )
import CSP.Laws.Traces.TraceLawsParallelElim (Net_Api-≟ {Payload}) as PEA
open Op using () renaming (∅ES to ∅ESa)
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysDecode blkA
  using ( SysState; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysMedium blkA
  using ( decMed; decLink; decCopy; MedState; mkMed; phase; broken
        ; CopyPhase; empty; full; draining; NetProcN; vis-of )
open import CSP.Examples.Cardano_network.Network p Payload using ( Copy )
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆; Skip; ∅ES )
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as LN
import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {Payload}) as PEN
open import CSP.Laws.Traces.TraceLawsParallel (Net-≟ {Payload}) using ( fPar-er; fPar-sr; fPar-nn )
open import Data.List using ( List; []; _∷_; length; lookup; updateAt; map )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysNode blkA as SN
open SN
  using ( decNodeA; decNodeB; decNodeC; decNodeD; bundleG; bundleA )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysStep blkA as SStep
open SStep
  using ( absDec; nodesOf; absNodesOf
        ; ReflOut; innerτ; hidSync; reflect-⟦⟧-τ; reflect-absDec-τ
        ; InnerτR; medτ; nodesτ; reflect-inner-τ
        ; NodesτR; nAτ; nBτ; nCτ; nDτ; reflect-nodes-τ
        ; NodeτR; bundleτ; driverτ; reflect-node-τ
        -- the abstract (τ-free `tableSpec`) node decodes + their bundles/peers
        ; absNodeA; absNodeB; absNodeC; absNodeD
        ; absBundleG; absCSc; absCSs; absBFc; absBFs; absTSc; absTSs; absKAc; absKAs
        ; absLNc; absLNs; absLFc; absLFs
        ; coarsenCSc; coarsenCSs; coarsenBFc; coarsenBFs; coarsenTSc; coarsenTSs; coarsenKAc; coarsenKAs
        ; coarsenLNc; coarsenLNs; coarsenLFc; coarsenLFs
        -- io-offer predicate (GAP-B disjointness leaves; `RenNO` via `SStep`)
        ; IoOffers )
open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond
  using ( apiES; linkAB; linkAC; linkBD; linkCD; Block₃; produce )
import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.NodeSpecs blkA as NS
open NS using ( tableSpec; tsNode; tMenu; tGo
              ; kaClientSpec; kaServerSpec; tsClientSpec; tsServerSpec )
open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; Label; ev; τ; evl; evLabel; τ-inv; ev-inv; sRet; sSil; sTau; sVis )
open import Class.DecEq using ( DecEq; _≟_ )
open import Relation.Nullary using ( yes; no )
open import CSP.Examples.Cardano_network.Base using
  ( Dir; lo; hi
  ; IDs; N2N_ChainSync; N2N_BlockFetch; N2N_TxSubmission; N2N_KeepAlive
  ; N2N_LeiosNotify; N2N_LeiosFetch
  ; BlockingStyle; Blocking; NonBlocking )
open import CSP.Examples.Cardano_network.Net p using ( Link )
open import CSP.Examples.Cardano_network.NetworkPar p
  using ( ιCS; ιCS⁻¹; ιCS-linv; ιBF; ιBF⁻¹; ιBF-linv )
import CSP.Examples.Cardano_network.ChainSync    p as CS
import CSP.Examples.Cardano_network.BlockFetch   p as BF
import CSP.Examples.Cardano_network.TxSubmission p as TS
import CSP.Examples.Cardano_network.KeepAlive    p as KA
import CSP.Examples.Cardano_network.LeiosNotify  p as LNp
import CSP.Examples.Cardano_network.LeiosFetch   p as LFp
open SN
  using ( CScPos; csHead; csReqNext1; csFindInt1; csDone1
        ; csRF1; csRB1; csIF1; csINF1; csSil
        ; decCSc; decCSc-src )
open SN
  using ( CSsPos; ssHead; ssReqNext1; ssFindInt1; ssDone1
        ; ssRF1; ssRB1; ssAw1; ssIF1; ssINF1; ssSil
        ; BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
        ; BFsPos; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil
        ; TScPos; tcHead; tcReqIdsB1; tcReqIdsNB1; tcReqTxs1; tcRepB1; tcDone1; tcRepNB1; tcRepTxs1; tcSil; TSsPos; tsHead; tsDone1; tsReqB1; tsReqNB1; tsReqTxs1; tsSil
        ; KAcPos; kcHead; kcErr1; kcReq1; kcDone1; kcSil; kcTermE1; KAsPos; ksHead; ksRecv1; ksDdone1; ksSil
        ; LNcPos; lncHead; lncRann1; lncRoff1; lncRtxs1; lncRvot1; lncReq1; lncDone1; lncSil; LNsPos; lnsHead; lnsDone1; lnsWann1; lnsWoff1; lnsWtxs1; lnsWvot1; lnsSil
        ; LFcPos; lfcHead; lfcRblk1; lfcRbtx1; lfcRvot1; lfcRnext1; lfcRlast1; lfcWblk1; lfcWtxs1; lfcWvot1; lfcWrng1; lfcDone1; lfcSil; LFsPos; lfsHead; lfsDone1; lfsWblk1; lfsWtxs1; lfsWvot1; lfsWnext1; lfsWlast1; lfsSil
        ; InertPos; mkInert; tsc; tss; kac; kas; lnc; lns; lfc; lfs
        ; decTSc; decTSc-src; decTSs; decTSs-src
        ; decKAc; decKAc-src; decKAs; decKAs-src
        ; decLNc; decLNc-src; decLNs; decLNs-src
        ; decLFc; decLFc-src; decLFs; decLFs-src
        ; decCSs; decCSs-src; decBFc; decBFc-src; decBFs; decBFs-src )
open SN
  using ( ProdPh; pp0; pp1; pp2; pp3; pp4; pp5; pp6; pp7; pp8; pp9
        ; ConsPh; cp0; cp1; cp2; cp3; cp4; cp5; cp6
        ; ConsDPh; consD
        ; CPPh; consuming; producing
        ; decProd; decCons; decConsD; decCP )
open import CSP.Examples.Cardano_network.NetworkPar p
  using ( ιKA; ιKA⁻¹; ιKA-linv; ιTS; ιTS⁻¹; ιTS-linv
        ; ιLN; ιLN⁻¹; ιLN-linv; ιLF; ιLF⁻¹; ιLF-linv
        ; KAclientA; KAserverA; TSclientA; TSserverA
        ; LNclientA; LNserverA; LFclientA; LFserverA )
open import CSP.Examples.Cardano_network.KeepAlive p using ( KAclientStClient; KAserverStClient )
open import CSP.Examples.Cardano_network.TxSubmission p using ( TSclientStClient; TSserverStClient )
open import CSP.Examples.Cardano_network.LeiosNotify p using ( LNclientStClient; LNserverStClient )
open import CSP.Examples.Cardano_network.LeiosFetch p using ( LFclientStClient; LFserverStClient )
open import CSP.Rename {E₁ = Net Payload} {E₂ = Net_Api Payload} ιNet ιNet⁻¹ ιNet-linv using ( renameMap )
import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload}) as PInv
open PInv using ( ⟶₀-ev-inv; Prefix-cont-fires )
open Op using ( Prefix; Output; Output-cont )
open import Class.DecEq using ( DecEq )
open SN
  using ( succVC; vis-ofC; CSProc; succVB; vis-ofB; BFProc )
import Semantics.LTS {E = CS.CSEv} {I = ExtI CS.CSEv} as CSL
import Semantics.LTS {E = BF.BFEv} {I = ExtI BF.BFEv} as BFL
open import CSP.Examples.Cardano_network.Net p using
  ( sendCSRequestNext; sendCSFindIntersect; sendCSDone; sendCSAwaitReply
  ; sendCSRollForward; sendCSRollBackward; sendCSIntersectFound; sendCSIntersectNotFound
  ; recvCSRollforward; recvCSRollback; recvCSIntersectFound; recvCSIntersectNotFound
  ; reqCSRequestNext; reqCSFindIntersect )
open import CSP.Examples.Cardano_network.Data p using
  ( chainSync; keepAlive; blockFetch; txSubmission; leiosNotify; leiosFetch
  ; MsgCSRequestNext; MsgCSAwaitReply; MsgCSRollForward; MsgCSRollBackward
  ; MsgCSFindIntersect; MsgCSIntersectFound; MsgCSIntersectNotFound; MsgCSDone
  ; Point; Tip; DecEq-Header; DecEq-Tip; DecEq-Point )
open import CSP.Examples.Cardano_network.Base using ( FromInitiator )
open Params p using ( time₀; length₀ )
import Class.DecEq.Instances as DecEqI
import CSP.Rename {E₁ = CS.CSEv} {E₂ = Net_Api Payload} ιCS ιCS⁻¹ ιCS-linv as RenCS
open import CSP.Examples.Cardano_network.Base using ( FromResponder )
open import Data.List using ( List )
open import CSP.Examples.Cardano_network.Net p using
  ( sendBFRequestRange; sendBFClientDone; sendBFStartBatch; sendBFNoBlocks
  ; sendBFBlock; sendBFBatchDone; recvBFBlock; reqBFRange )
open import CSP.Examples.Cardano_network.Data p using
  ( ChainRange; DecEq-ChainRange
  ; MsgRequestRange; MsgStartBatch; MsgNoBlocks; MsgBlock
  ; MsgBatchDone; MsgClientDone )
open Params p using ( Block; decBlock )
import CSP.Rename {E₁ = BF.BFEv} {E₂ = Net_Api Payload} ιBF ιBF⁻¹ ιBF-linv as RenBF
import CSP.Rename {E₁ = KA.KAEv} {E₂ = Net_Api Payload} ιKA ιKA⁻¹ ιKA-linv as RenKA
import CSP.Rename {E₁ = TS.TSEv} {E₂ = Net_Api Payload} ιTS ιTS⁻¹ ιTS-linv as RenTS
import CSP.Rename {E₁ = LNp.LNEv} {E₂ = Net_Api Payload} ιLN ιLN⁻¹ ιLN-linv as RenLN
import CSP.Rename {E₁ = LFp.LFEv} {E₂ = Net_Api Payload} ιLF ιLF⁻¹ ιLF-linv as RenLF
open SN
  using ( succVK; vis-ofK; KAProc )
import Semantics.LTS {E = KA.KAEv} {I = ExtI KA.KAEv} as KAL
open import CSP.Examples.Cardano_network.Net p using
  ( sendKAMsg; sendKADone; errCookie; recvKACookie )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgKeepAlive; MsgKeepAliveResponse; MsgKADone )
open SN
  using ( succVT; vis-ofT; TSProc )
import Semantics.LTS {E = TS.TSEv} {I = ExtI TS.TSEv} as TSL
open import CSP.Examples.Cardano_network.Net p using
  ( sendTSReplyTxIds; sendTSReplyTxs; sendTSDone
  ; sendTSRequestTxIdsBlocking; sendTSRequestTxIdsPipelined; sendTSRequestTxsPipelined
  ; recvTSRequestTxIds; recvTSRequestTxs )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgTSInit; MsgTSRequestTxIds; MsgTSReplyTxIds; MsgTSRequestTxs; MsgTSReplyTxs; MsgTSDone )
open import Data.List.Properties using (≡-dec)
open SN
  using ( succVN; vis-ofN; LNProc )
import Semantics.LTS {E = LNp.LNEv} {I = ExtI LNp.LNEv} as LNL
open import CSP.Examples.Cardano_network.Net p using
  ( sendLNRequestNext; sendLNDone; sendLNBlockAnnouncement; sendLNBlockOffer
  ; sendLNBlockTxsOffer; sendLNVotesOffer; recvLNBlockAnnouncement
  ; recvLNBlockOffer; recvLNBlockTxsOffer; recvLNVotesOffer )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgLNRequestNext; MsgLNBlockAnnouncement; MsgLNBlockOffer
  ; MsgLNBlockTxsOffer; MsgLNVotesOffer; MsgLNDone )
open SN
  using ( succVF; vis-ofF; LFProc )
import Semantics.LTS {E = LFp.LFEv} {I = ExtI LFp.LFEv} as LFL
open import CSP.Examples.Cardano_network.Net p using
  ( sendLFBlockRequest; sendLFBlockTxsRequest; sendLFVotesRequest
  ; sendLFBlockRangeRequest; sendLFDone; sendLFBlock; sendLFBlockTxs
  ; sendLFVoteDelivery; sendLFNextBlockAndTxsInRange; sendLFLastBlockAndTxsInRange
  ; recvLFBlock; recvLFBlockTxs; recvLFVoteDelivery; recvLFRangeBlock )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgLFBlockRequest; MsgLFBlock; MsgLFBlockTxsRequest; MsgLFBlockTxs
  ; MsgLFVotesRequest; MsgLFVoteDelivery; MsgLFBlockRangeRequest
  ; MsgLFNextBlockAndTxsInRange; MsgLFLastBlockAndTxsInRange; MsgLFDone )

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_PeerEvIo blkA public

------------------------------------------------------------------------
-- GAP-B FOUNDATION — inert-peer channel DISJOINTNESS (the non-offer leaves).
--
-- Unlike the τ routing (where the eight inert KA/TS/LN/LF peers are refuted
-- UNCONDITIONALLY by `*-no-τ`), an ev/io bundle peel cannot refute an inert
-- peer outright — each inert peer DOES offer its OWN protocol's visible/io
-- events.  So the ev/io peel is per-protocol: once the fired event is KNOWN to
-- be a ChainSync- or BlockFetch-channel event, the eight inert peers (and the
-- opposite driven protocol's pair) are refuted by NON-OFFER.  Each inert peer
-- is a renamed FSM `RenXX.renameMap (…StClient l d)`, and `ιXX⁻¹` sends every
-- FOREIGN (non-XX) channel to `nothing`, so `renameMap-noOffer-χ …refl` gives
-- the non-offer at ANY foreign event `e₂` with `ιXX⁻¹ e₂ ≡ nothing` (both io
-- channels `input/output _ _ N2N_{ChainSync,BlockFetch}` and the api events).
-- These are exactly the `evBoth`-refutation witnesses `bundle-ev-inv` consumes.
------------------------------------------------------------------------

-- SysStep qualified (its `RenNO` parameterised module is not brought in by the
-- `using` open above — a module member needs a qualified path)

-- RenNO instances for the four inert protocols (mirror SysStep's `CSNO`/`BFNO`;
-- the RenTC `KANO`/… names above are for the τ-freedom no-τ transport)
module KANOff = SStep.RenNO ιKA ιKA⁻¹ ιKA-linv
module TSNOff = SStep.RenNO ιTS ιTS⁻¹ ιTS-linv
module LNNOff = SStep.RenNO ιLN ιLN⁻¹ ιLN-linv
module LFNOff = SStep.RenNO ιLF ιLF⁻¹ ιLF-linv

-- KA client / server: no offer of any event whose ιKA-preimage is `nothing`
KAclientA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιKA⁻¹ e ≡ nothing → ¬ IoOffers (KAclientA l d) e a
KAclientA-noOffer l d eqn = KANOff.renameMap-noOffer-χ (KAclientStClient l d) eqn
KAserverA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιKA⁻¹ e ≡ nothing → ¬ IoOffers (KAserverA l d) e a
KAserverA-noOffer l d eqn = KANOff.renameMap-noOffer-χ (KAserverStClient l d) eqn

-- TS client / server: no offer of any event whose ιTS-preimage is `nothing`
TSclientA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιTS⁻¹ e ≡ nothing → ¬ IoOffers (TSclientA l d) e a
TSclientA-noOffer l d eqn = TSNOff.renameMap-noOffer-χ (TSclientStClient l d) eqn
TSserverA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιTS⁻¹ e ≡ nothing → ¬ IoOffers (TSserverA l d) e a
TSserverA-noOffer l d eqn = TSNOff.renameMap-noOffer-χ (TSserverStClient l d) eqn

-- generalised (position-independent) TS non-offers: at ANY tracked position a
-- TxSubmission peer offers only TS-channel events, so a foreign-channel event
-- (`ιTS⁻¹ e ≡ nothing`) is refused (channel mismatch survives the threading)
decTSc-noOffer : (l : Link) (d : Dir) (pos : TScPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιTS⁻¹ e ≡ nothing → ¬ IoOffers (decTSc l d pos) e a
decTSc-noOffer l d pos eqn = TSNOff.renameMap-noOffer-χ (decTSc-src l d pos) eqn
decTSs-noOffer : (l : Link) (d : Dir) (pos : TSsPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιTS⁻¹ e ≡ nothing → ¬ IoOffers (decTSs l d pos) e a
decTSs-noOffer l d pos eqn = TSNOff.renameMap-noOffer-χ (decTSs-src l d pos) eqn

-- position-general KA non-offer at a foreign channel (channel mismatch survives the threading)
decKAc-noOffer : (l : Link) (d : Dir) (pos : KAcPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιKA⁻¹ e ≡ nothing → ¬ IoOffers (decKAc l d pos) e a
decKAc-noOffer l d pos eqn = KANOff.renameMap-noOffer-χ (decKAc-src l d pos) eqn
decKAs-noOffer : (l : Link) (d : Dir) (pos : KAsPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιKA⁻¹ e ≡ nothing → ¬ IoOffers (decKAs l d pos) e a
decKAs-noOffer l d pos eqn = KANOff.renameMap-noOffer-χ (decKAs-src l d pos) eqn

-- position-general LN non-offer at a foreign channel (channel mismatch survives the threading)
decLNc-noOffer : (l : Link) (d : Dir) (pos : LNcPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLN⁻¹ e ≡ nothing → ¬ IoOffers (decLNc l d pos) e a
decLNc-noOffer l d pos eqn = LNNOff.renameMap-noOffer-χ (decLNc-src l d pos) eqn
decLNs-noOffer : (l : Link) (d : Dir) (pos : LNsPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLN⁻¹ e ≡ nothing → ¬ IoOffers (decLNs l d pos) e a
decLNs-noOffer l d pos eqn = LNNOff.renameMap-noOffer-χ (decLNs-src l d pos) eqn

-- position-general LF non-offer at a foreign channel (DORMANT step-4 leaf: used
-- by the LF-tracking ⦀-noOffer peels once `bundleG` carries `decLFc/decLFs`)
decLFc-noOffer : (l : Link) (d : Dir) (pos : LFcPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLF⁻¹ e ≡ nothing → ¬ IoOffers (decLFc l d pos) e a
decLFc-noOffer l d pos eqn = LFNOff.renameMap-noOffer-χ (decLFc-src l d pos) eqn
decLFs-noOffer : (l : Link) (d : Dir) (pos : LFsPos) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLF⁻¹ e ≡ nothing → ¬ IoOffers (decLFs l d pos) e a
decLFs-noOffer l d pos eqn = LFNOff.renameMap-noOffer-χ (decLFs-src l d pos) eqn

-- LN client / server: no offer of any event whose ιLN-preimage is `nothing`
LNclientA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLN⁻¹ e ≡ nothing → ¬ IoOffers (LNclientA l d) e a
LNclientA-noOffer l d eqn = LNNOff.renameMap-noOffer-χ (LNclientStClient l d) eqn
LNserverA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLN⁻¹ e ≡ nothing → ¬ IoOffers (LNserverA l d) e a
LNserverA-noOffer l d eqn = LNNOff.renameMap-noOffer-χ (LNserverStClient l d) eqn

-- LF client / server: no offer of any event whose ιLF-preimage is `nothing`
LFclientA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLF⁻¹ e ≡ nothing → ¬ IoOffers (LFclientA l d) e a
LFclientA-noOffer l d eqn = LFNOff.renameMap-noOffer-χ (LFclientStClient l d) eqn
LFserverA-noOffer : (l : Link) (d : Dir) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ιLF⁻¹ e ≡ nothing → ¬ IoOffers (LFserverA l d) e a
LFserverA-noOffer l d eqn = LFNOff.renameMap-noOffer-χ (LFserverStClient l d) eqn

------------------------------------------------------------------------
-- GAP-B L2 — concrete same-protocol disjointness (CSc↔CSs, BFc↔BFs).
-- The two driven peers of a protocol sit at DIFFERENT directions (`cl ≠ sv`
-- in every node bundle).  Every event a peer at direction `d` fires carries
-- `d` as its Net_Api direction component, so the same event cannot be fired
-- by both a `cl`-peer and an `sv`-peer — refuting the `⦀`-evBoth the bundle
-- ev-peel would otherwise leave as an overlap node.
------------------------------------------------------------------------

-- the direction component of a ChainSync source event
csEvDir : {X : Set 0ℓ} → CS.CSEv X → Dir
csEvDir (CS.sendCS l d)    = d
csEvDir (CS.receiveCS l d) = d
csEvDir (CS.apiCSev l d m) = d
csEvDir (CS.doneCS l d)    = d

-- the direction component of a BlockFetch source event
bfEvDir : {X : Set 0ℓ} → BF.BFEv X → Dir
bfEvDir (BF.sendBF l d)    = d
bfEvDir (BF.receiveBF l d) = d
bfEvDir (BF.apiBFev l d m) = d
bfEvDir (BF.doneBF l d)    = d
-- L2: decCSc-src-dir — the visible source step of a fine position fires
-- an event whose direction component is `d` (csEvDir extracts it).
decCSc-src-dir : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSc-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → csEvDir e₁ ≡ d
-- head stIdle : fires apiCSev sendCSRequestNext / FindIntersect / Done
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRequestNext} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} {a} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSDone} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollForward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollBackward}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollforward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollback}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-dir l d (csHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
-- head stCanAwait : fires receiveCS RollForward / RollBackward / AwaitReply
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSAwaitReply} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' m}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-dir l d (csHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
-- head stMustReply : fires receiveCS RollForward / RollBackward
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-dir l d (csHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
-- head stIntersect : fires receiveCS IntersectFound / IntersectNotFound
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-dir l d (csHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSc-src-dir l d (csHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid csReqNext1 : fires sendCS payload → csSil stCanAwait
decCSc-src-dir l d csReqNext1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d csReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-dir l d csReqNext1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-dir l d csReqNext1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
-- mid csFindInt1 ps : fires sendCS payload → csSil stIntersect
decCSc-src-dir l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d (csFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-dir l d (csFindInt1 ps) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-dir l d (csFindInt1 ps) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
-- mid csDone1 : fires sendCS payload → csSil stDone (client has no node-local done)
decCSc-src-dir l d csDone1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d csDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-dir l d csDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-dir l d csDone1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
-- mid csRF1 : fires apiCSev recvCSRollforward (h,t) → csSil stIdle
decCSc-src-dir l d (csRF1 h t) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollforward) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (h , t)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d (csRF1 h t) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-dir l d (csRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-dir l d (csRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
-- mid csRB1 : fires apiCSev recvCSRollback (pt,tp) → csSil stIdle
decCSc-src-dir l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollback) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d (csRB1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-dir l d (csRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-dir l d (csRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
-- mid csIF1 : fires apiCSev recvCSIntersectFound (pt,tp) → csSil stIdle
decCSc-src-dir l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d (csIF1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-dir l d (csIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-dir l d (csIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
-- mid csINF1 : fires apiCSev recvCSIntersectNotFound tp → csSil stIdle
decCSc-src-dir l d (csINF1 tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectNotFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ tp
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-dir l d (csINF1 tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-dir l d (csINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-dir l d (csINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
-- loop re-entry csSil : forces to `sil`, no visible step
decCSc-src-dir l d (csSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- L2: decCSs-src-dir — the visible source step of a fine position fires
-- an event whose direction component is `d` (csEvDir extracts it).
decCSs-src-dir : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSs-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → csEvDir e₁ ≡ d
-- head stIdle : receives RequestNext / FindIntersect / Done on the wire
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSRequestNext} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSFindIntersect ps)} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSDone} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-dir l d (ssHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
-- head stCanAwait : sends RollForward / RollBackward / AwaitReply via api
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-dir l d (ssHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
-- head stMustReply : sends RollForward / RollBackward via api
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-dir l d (ssHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
-- head stIntersect : sends IntersectFound / IntersectNotFound via api
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollForward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollBackward}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollforward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollback}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSRequestNext}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-dir l d (ssHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSs-src-dir l d (ssHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid ssReqNext1 : fires api reqCSRequestNext (Prefix₀) → ssSil stCanAwait
decCSs-src-dir l d ssReqNext1 {e₁ = CS.apiCSev l' d' m} s with step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSRequestNext) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decCSs-src-dir l d ssReqNext1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-dir l d ssReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-dir l d ssReqNext1 {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
-- mid ssFindInt1 ps : fires api reqCSFindIntersect ps (Output) → ssSil stIntersect
decCSs-src-dir l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSFindIntersect) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ CS.DecEq-ListPoint ⦄ a ps
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d (ssFindInt1 ps) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-dir l d (ssFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-dir l d (ssFindInt1 ps) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
-- mid ssDone1 : fires doneCS (Prefix₀) → ssSil stDone
decCSs-src-dir l d ssDone1 {e₁ = CS.doneCS l' d'} s with step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.doneCS l d) (_ , CS.doneCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decCSs-src-dir l d ssDone1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-dir l d ssDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-dir l d ssDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
-- mid ssRF1 : fires sendCS payload → ssSil stIdle
decCSs-src-dir l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d (ssRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-dir l d (ssRF1 h t) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-dir l d (ssRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
-- mid ssRB1 : fires sendCS payload → ssSil stIdle
decCSs-src-dir l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d (ssRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-dir l d (ssRB1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-dir l d (ssRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
-- mid ssAw1 : fires sendCS payload → ssSil stMustReply
decCSs-src-dir l d ssAw1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d ssAw1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-dir l d ssAw1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-dir l d ssAw1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
-- mid ssIF1 : fires sendCS payload → ssSil stIdle
decCSs-src-dir l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d (ssIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-dir l d (ssIF1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-dir l d (ssIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
-- mid ssINF1 : fires sendCS payload → ssSil stIdle
decCSs-src-dir l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-dir l d (ssINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-dir l d (ssINF1 tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-dir l d (ssINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
-- loop re-entry ssSil : forces to `sil`, no visible step
decCSs-src-dir l d (ssSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- L2: decBFc-src-dir — the visible source step of a fine position fires
-- an event whose direction component is `d` (bfEvDir extracts it).
decBFc-src-dir : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFc-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → bfEvDir e₁ ≡ d
-- head stIdle : sends RequestRange / ClientDone via api
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFRequestRange} {a} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFClientDone} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' recvBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' reqBFRange}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-dir l d (bcHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
-- head stBusy : receives StartBatch / NoBlocks (both go straight to a re-entry sil)
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgStartBatch} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgNoBlocks} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-dir l d (bcHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
-- head stStreaming : receives Block (→ bcBlk1) / BatchDone (→ re-entry sil)
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgBlock b)} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgBatchDone} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-dir l d (bcHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
-- head stDone : `ret`, no visible step
decBFc-src-dir l d (bcHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bcReq1 r : fires sendBF payload → bcSil stBusy
decBFc-src-dir l d (bcReq1 r) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-dir l d (bcReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-dir l d (bcReq1 r) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-dir l d (bcReq1 r) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
-- mid bcDone1 : fires sendBF payload → bcSil stDone
decBFc-src-dir l d bcDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-dir l d bcDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-dir l d bcDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-dir l d bcDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
-- mid bcBlk1 b : fires apiBFev recvBFBlock b → bcSil stStreaming
decBFc-src-dir l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d recvBFBlock) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ decBlock ⦄ a b
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-dir l d (bcBlk1 b) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-dir l d (bcBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-dir l d (bcBlk1 b) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
-- loop re-entry bcSil : forces to `sil`, no visible step
decBFc-src-dir l d (bcSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- L2: decBFs-src-dir — the visible source step of a fine position fires
-- an event whose direction component is `d` (bfEvDir extracts it).
decBFs-src-dir : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFs-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → bfEvDir e₁ ≡ d
-- head stIdle : receives RequestRange (→ bsReq1) / ClientDone (→ bsDone1)
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgRequestRange r)} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgClientDone} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-dir l d (bsHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
-- head stBusy : sends StartBatch (→ bsStart1) / NoBlocks (→ bsNoBlk1) via api
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFNoBlocks} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBatchDone}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-dir l d (bsHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
-- head stStreaming : sends Block (→ bsBlk1) / BatchDone (→ bsBatchDone1) via api
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBlock} {a} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBatchDone} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFStartBatch}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}     s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-dir l d (bsHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
-- head stDone : `ret`
decBFs-src-dir l d (bsHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bsReq1 r : fires api reqBFRange r (Output) → bsSil stBusy
decBFs-src-dir l d (bsReq1 r) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d reqBFRange) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEq-ChainRange ⦄ a r
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-dir l d (bsReq1 r) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-dir l d (bsReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-dir l d (bsReq1 r) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
-- mid bsDone1 : fires doneBF (Prefix₀) → bsSil stDone
decBFs-src-dir l d bsDone1 {e₁ = BF.doneBF l' d'} s with step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.doneBF l d) (_ , BF.doneBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decBFs-src-dir l d bsDone1 {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-dir l d bsDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-dir l d bsDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
-- mid bsStart1 : fires sendBF payload → bsSil stStreaming
decBFs-src-dir l d bsStart1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-dir l d bsStart1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-dir l d bsStart1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-dir l d bsStart1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
-- mid bsNoBlk1 : fires sendBF payload → bsSil stIdle
decBFs-src-dir l d bsNoBlk1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-dir l d bsNoBlk1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-dir l d bsNoBlk1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-dir l d bsNoBlk1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
-- mid bsBlk1 b : fires sendBF payload → bsSil stStreaming
decBFs-src-dir l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-dir l d (bsBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-dir l d (bsBlk1 b) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-dir l d (bsBlk1 b) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
-- mid bsBatchDone1 : fires sendBF payload → bsSil stIdle
decBFs-src-dir l d bsBatchDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-dir l d bsBatchDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-dir l d bsBatchDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-dir l d bsBatchDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
-- loop re-entry bsSil : forces to `sil`, no visible step
decBFs-src-dir l d (bsSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()


-- a Net_Api event carrying direction `d` in its channel component (exactly the
-- constructor shapes the CS/BF peers emit under ιCS/ιBF)
data ApiHasDir (d : Dir) : {X : Set 0ℓ} → Net_Api Payload X → Set₁ where
  ahIn   : ∀ {l ch} → ApiHasDir d (input  l d ch)
  ahOut  : ∀ {l ch} → ApiHasDir d (output l d ch)
  ahDone : ∀ {l ch} → ApiHasDir d (done   l d ch)
  ahCS   : ∀ {l m}  → ApiHasDir d (apiCS  l d m)
  ahBF   : ∀ {l m}  → ApiHasDir d (apiBF  l d m)
  ahKA   : ∀ {l m}  → ApiHasDir d (apiKA  l d m)
  ahTS   : ∀ {l m}  → ApiHasDir d (apiTS  l d m)
  ahLN   : ∀ {l m}  → ApiHasDir d (apiLN  l d m)
  ahLF   : ∀ {l m}  → ApiHasDir d (apiLF  l d m)

-- the direction of a fixed event is unique (both witnesses pin the same slot)
apiDir-inj : {X : Set 0ℓ} {e : Net_Api Payload X} {d d′ : Dir}
  → ApiHasDir d e → ApiHasDir d′ e → d ≡ d′
apiDir-inj ahIn   ahIn   = refl
apiDir-inj ahOut  ahOut  = refl
apiDir-inj ahDone ahDone = refl
apiDir-inj ahCS   ahCS   = refl
apiDir-inj ahBF   ahBF   = refl
apiDir-inj ahKA   ahKA   = refl
apiDir-inj ahTS   ahTS   = refl
apiDir-inj ahLN   ahLN   = refl
apiDir-inj ahLF   ahLF   = refl

-- ιCS carries the source direction into the Net_Api event
csApiDir : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ApiHasDir (csEvDir e₁) (ιCS e₁)
csApiDir (CS.sendCS l d)    = ahIn
csApiDir (CS.receiveCS l d) = ahOut
csApiDir (CS.apiCSev l d m) = ahCS
csApiDir (CS.doneCS l d)    = ahDone

-- ιBF carries the source direction into the Net_Api event
bfApiDir : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ApiHasDir (bfEvDir e₁) (ιBF e₁)
bfApiDir (BF.sendBF l d)    = ahIn
bfApiDir (BF.receiveBF l d) = ahOut
bfApiDir (BF.apiBFev l d m) = ahBF
bfApiDir (BF.doneBF l d)    = ahDone

-- the direction a driven CS-client step exposes on the Net_Api event
csc-ev-dir : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
csc-ev-dir l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιCS-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιCS e₁)) (decCSc-src-dir l d pos srcStep) (csApiDir e₁))

-- the direction a driven CS-server step exposes on the Net_Api event
css-ev-dir : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
css-ev-dir l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιCS-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιCS e₁)) (decCSs-src-dir l d pos srcStep) (csApiDir e₁))

-- the direction a driven BF-client step exposes on the Net_Api event
bfc-ev-dir : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
bfc-ev-dir l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιBF-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιBF e₁)) (decBFc-src-dir l d pos srcStep) (bfApiDir e₁))

-- the direction a driven BF-server step exposes on the Net_Api event
bfs-ev-dir : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
bfs-ev-dir l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιBF-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιBF e₁)) (decBFs-src-dir l d pos srcStep) (bfApiDir e₁))

-- L2 (CS): the client (dir cl) and server (dir sv≠cl) never fire the SAME event
CSc-CSs-noBoth : (l : Link) (cl sv : Dir) → cl ≢ sv → (pc : CScPos) (ps : CSsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {Mc Ms : NetProc}
  → decCSc l cl pc ─[ ev (evl (evLabel X e₂ a)) ]─► Mc
  → decCSs l sv ps ─[ ev (evl (evLabel X e₂ a)) ]─► Ms → ⊥
CSc-CSs-noBoth l cl sv cl≢sv pc ps sc ss =
  cl≢sv (apiDir-inj (csc-ev-dir l cl pc sc) (css-ev-dir l sv ps ss))

-- L2 (BF): the client (dir cl) and server (dir sv≠cl) never fire the SAME event
BFc-BFs-noBoth : (l : Link) (cl sv : Dir) → cl ≢ sv → (pc : BFcPos) (ps : BFsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {Mc Ms : NetProc}
  → decBFc l cl pc ─[ ev (evl (evLabel X e₂ a)) ]─► Mc
  → decBFs l sv ps ─[ ev (evl (evLabel X e₂ a)) ]─► Ms → ⊥
BFc-BFs-noBoth l cl sv cl≢sv pc ps sc ss =
  cl≢sv (apiDir-inj (bfc-ev-dir l cl pc sc) (bfs-ev-dir l sv ps ss))

------------------------------------------------------------------------
-- GAP-B L3 (core) — abstract-side peer viewV non-offer reductions.  The
-- abstract bundle reassembly (`⦀-ev-L/R` seals) needs each idle SIBLING's
-- `viewV (force …) ≡ nothing`.  Every abstract peer is a `tableSpec T q`, so
-- its offer map reduces to `tGo T ∘ nxt T q`; these bridge a `nxt`-nothing (a
-- position/event with no table edge) OR a terminal `isFin` to the seal's form.
------------------------------------------------------------------------

-- a non-terminal tableSpec peer offers nothing at a no-edge (e,a)
tableSpec-viewV-noOffer : {Pos : Set} (T : NS.Table Pos) (q : Pos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.Table.isFin T q ≡ false
  → NS.Table.nxt T q (X , e) a ≡ nothing
  → Op.viewV (PTree.force (tableSpec T q)) (X , e) a ≡ nothing
tableSpec-viewV-noOffer T q {X} {e} {a} finEq nxtEq =
  trans (cong (λ n → Op.viewV n (X , e) a) (tsForce-react T q finEq))
        (cong (tGo T) nxtEq)

-- a terminated tableSpec peer offers nothing at all
tableSpec-viewV-fin : {Pos : Set} (T : NS.Table Pos) (q : Pos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.Table.isFin T q ≡ true
  → Op.viewV (PTree.force (tableSpec T q)) (X , e) a ≡ nothing
tableSpec-viewV-fin T q {X} {e} {a} finEq =
  cong (λ n → Op.viewV n (X , e) a) (tsForce-ret T q finEq)

------------------------------------------------------------------------
-- GAP-B L3-full (foundations) — the ¬IoOffers↔viewV bridge and the
-- cross-protocol preimage facts.  These turn a peer's `¬ IoOffers` (the
-- SysStep non-offer currency) into the `viewV (force _) ≡ nothing` the
-- `⦀-ev-L/R` seals consume, and certify that a driven peer's ι-image event
-- has NO preimage under a sibling protocol's ι (so the sibling's ιX⁻¹-keyed
-- `*nxt-foreign` non-offer applies at the fired event).
------------------------------------------------------------------------

-- a process offering no visible step at (e,a) has `viewV (force _) ≡ nothing`
-- there (a `just` offer would give an `sVis` step, contradicting `¬ IoOffers`)
noOffer→viewV : (P : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ¬ IoOffers P e a
  → Op.viewV (PTree.force P) (X , e) a ≡ nothing
noOffer→viewV P {X} {e} {a} ¬off with PTree.force P in fEq
... | ret _       = refl
... | sil _       = refl
... | react v τc with v (X , e) a in vEq
...   | nothing   = refl
...   | just P′   = ⊥-elim (¬off (P′ , sVis fEq vEq))

-- viewV-of-⦀ group builder: a `⦀` group offers nothing at (e,a) when both
-- operands do (compose the per-operand `¬ IoOffers` via a `Par-ev-elim ∅ES`
-- peel, then bridge to `viewV`).  This is the sibling-group non-offer the
-- abstract-bundle `⦀-ev-L/R` reassembly threads past the driven peer.
⦀-viewV-nothing : (P Q : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ¬ IoOffers P e a → ¬ IoOffers Q e a
  → Op.viewV (PTree.force (P ⦀ Q)) (X , e) a ≡ nothing
⦀-viewV-nothing P Q {X} {e} {a} ¬P ¬Q =
  noOffer→viewV (P ⦀ Q) ¬PQ
  where
    -- the interleave `⦀` offers io only if some operand does (no ∅ES sync)
    ¬PQ : ¬ IoOffers (P ⦀ Q) e a
    ¬PQ (M , step) with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) P Q step
    ... | PEA.evSync mem _ _ = ⊥-elim mem
    ... | PEA.evL  _ sP     = ¬P (_ , sP)
    ... | PEA.evR  _ sQ     = ¬Q (_ , sQ)
    ... | PEA.evBoth _ sP _ = ¬P (_ , sP)

-- cross-protocol preimage: a ChainSync-image event has NO KeepAlive preimage
ιKA⁻¹∘ιCS : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ιKA⁻¹ (ιCS e₁) ≡ nothing
ιKA⁻¹∘ιCS (CS.sendCS l d)      = refl
ιKA⁻¹∘ιCS (CS.receiveCS l d)   = refl
ιKA⁻¹∘ιCS (CS.apiCSev l d m)   = refl
ιKA⁻¹∘ιCS (CS.doneCS l d)      = refl

-- cross-protocol preimage: a ChainSync-image event has NO BlockFetch preimage
ιBF⁻¹∘ιCS : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ιBF⁻¹ (ιCS e₁) ≡ nothing
ιBF⁻¹∘ιCS (CS.sendCS l d)      = refl
ιBF⁻¹∘ιCS (CS.receiveCS l d)   = refl
ιBF⁻¹∘ιCS (CS.apiCSev l d m)   = refl
ιBF⁻¹∘ιCS (CS.doneCS l d)      = refl

-- cross-protocol preimage: a ChainSync-image event has NO TxSubmission preimage
ιTS⁻¹∘ιCS : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ιTS⁻¹ (ιCS e₁) ≡ nothing
ιTS⁻¹∘ιCS (CS.sendCS l d)      = refl
ιTS⁻¹∘ιCS (CS.receiveCS l d)   = refl
ιTS⁻¹∘ιCS (CS.apiCSev l d m)   = refl
ιTS⁻¹∘ιCS (CS.doneCS l d)      = refl

-- cross-protocol preimage: a BlockFetch-image event has NO KeepAlive preimage
ιKA⁻¹∘ιBF : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ιKA⁻¹ (ιBF e₁) ≡ nothing
ιKA⁻¹∘ιBF (BF.sendBF l d)      = refl
ιKA⁻¹∘ιBF (BF.receiveBF l d)   = refl
ιKA⁻¹∘ιBF (BF.apiBFev l d m)   = refl
ιKA⁻¹∘ιBF (BF.doneBF l d)      = refl

-- cross-protocol preimage: a BlockFetch-image event has NO ChainSync preimage
ιCS⁻¹∘ιBF : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ιCS⁻¹ (ιBF e₁) ≡ nothing
ιCS⁻¹∘ιBF (BF.sendBF l d)      = refl
ιCS⁻¹∘ιBF (BF.receiveBF l d)   = refl
ιCS⁻¹∘ιBF (BF.apiBFev l d m)   = refl
ιCS⁻¹∘ιBF (BF.doneBF l d)      = refl

-- cross-protocol preimage: a BlockFetch-image event has NO TxSubmission preimage
ιTS⁻¹∘ιBF : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ιTS⁻¹ (ιBF e₁) ≡ nothing
ιTS⁻¹∘ιBF (BF.sendBF l d)      = refl
ιTS⁻¹∘ιBF (BF.receiveBF l d)   = refl
ιTS⁻¹∘ιBF (BF.apiBFev l d m)   = refl
ιTS⁻¹∘ιBF (BF.doneBF l d)      = refl

-- cross-protocol preimage: a ChainSync-image event has NO LeiosNotify preimage
ιLN⁻¹∘ιCS : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ιLN⁻¹ (ιCS e₁) ≡ nothing
ιLN⁻¹∘ιCS (CS.sendCS l d)      = refl
ιLN⁻¹∘ιCS (CS.receiveCS l d)   = refl
ιLN⁻¹∘ιCS (CS.apiCSev l d m)   = refl
ιLN⁻¹∘ιCS (CS.doneCS l d)      = refl

-- cross-protocol preimage: a ChainSync-image event has NO LeiosFetch preimage
ιLF⁻¹∘ιCS : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ιLF⁻¹ (ιCS e₁) ≡ nothing
ιLF⁻¹∘ιCS (CS.sendCS l d)      = refl
ιLF⁻¹∘ιCS (CS.receiveCS l d)   = refl
ιLF⁻¹∘ιCS (CS.apiCSev l d m)   = refl
ιLF⁻¹∘ιCS (CS.doneCS l d)      = refl

-- cross-protocol preimage: a BlockFetch-image event has NO LeiosNotify preimage
ιLN⁻¹∘ιBF : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ιLN⁻¹ (ιBF e₁) ≡ nothing
ιLN⁻¹∘ιBF (BF.sendBF l d)      = refl
ιLN⁻¹∘ιBF (BF.receiveBF l d)   = refl
ιLN⁻¹∘ιBF (BF.apiBFev l d m)   = refl
ιLN⁻¹∘ιBF (BF.doneBF l d)      = refl

-- cross-protocol preimage: a BlockFetch-image event has NO LeiosFetch preimage
ιLF⁻¹∘ιBF : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ιLF⁻¹ (ιBF e₁) ≡ nothing
ιLF⁻¹∘ιBF (BF.sendBF l d)      = refl
ιLF⁻¹∘ιBF (BF.receiveBF l d)   = refl
ιLF⁻¹∘ιBF (BF.apiBFev l d m)   = refl
ιLF⁻¹∘ιBF (BF.doneBF l d)      = refl

------------------------------------------------------------------------
-- GAP-B L3-full — FOREIGN `nxt` non-offers (all `refl`, family-specific).
-- A sibling peer of protocol X never fires a driven peer's ι-image event of
-- a DIFFERENT protocol Y (its table clauses only match X-protocol events, so
-- a Y-image falls to the per-table catch-all `nothing`).  KA/TS peers are at a
-- FIXED spec head in `absBundleG`; CS/BF peers range over their coarse
-- positions.  SCRIPT-GENERATED (`.superpowers/sdd/gen-l3-foreign.py`).
------------------------------------------------------------------------

-- kaCnxt-noCS: the head-kcClient kaCnxt peer offers nothing at any CS.CSEv-image
kaCnxt-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.kaCnxt l d NS.kcClient (X , ιCS e₁) a ≡ nothing
kaCnxt-noCS l d (CS.sendCS _ _) = refl
kaCnxt-noCS l d (CS.receiveCS _ _) = refl
kaCnxt-noCS l d (CS.apiCSev _ _ _) = refl
kaCnxt-noCS l d (CS.doneCS _ _) = refl

-- kaCnxt-noBF: the head-kcClient kaCnxt peer offers nothing at any BF.BFEv-image
kaCnxt-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.kaCnxt l d NS.kcClient (X , ιBF e₁) a ≡ nothing
kaCnxt-noBF l d (BF.sendBF _ _) = refl
kaCnxt-noBF l d (BF.receiveBF _ _) = refl
kaCnxt-noBF l d (BF.apiBFev _ _ _) = refl
kaCnxt-noBF l d (BF.doneBF _ _) = refl

-- kaSnxt-noCS: the head-ksClient kaSnxt peer offers nothing at any CS.CSEv-image
kaSnxt-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.kaSnxt l d NS.ksClient (X , ιCS e₁) a ≡ nothing
kaSnxt-noCS l d (CS.sendCS _ _) = refl
kaSnxt-noCS l d (CS.receiveCS _ _) = refl
kaSnxt-noCS l d (CS.apiCSev _ _ _) = refl
kaSnxt-noCS l d (CS.doneCS _ _) = refl

-- kaSnxt-noBF: the head-ksClient kaSnxt peer offers nothing at any BF.BFEv-image
kaSnxt-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.kaSnxt l d NS.ksClient (X , ιBF e₁) a ≡ nothing
kaSnxt-noBF l d (BF.sendBF _ _) = refl
kaSnxt-noBF l d (BF.receiveBF _ _) = refl
kaSnxt-noBF l d (BF.apiBFev _ _ _) = refl
kaSnxt-noBF l d (BF.doneBF _ _) = refl

-- tsCnxt-noCS: the head-tcInit tsCnxt peer offers nothing at any CS.CSEv-image
tsCnxt-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.tsCnxt l d NS.tcInit (X , ιCS e₁) a ≡ nothing
tsCnxt-noCS l d (CS.sendCS _ _) = refl
tsCnxt-noCS l d (CS.receiveCS _ _) = refl
tsCnxt-noCS l d (CS.apiCSev _ _ _) = refl
tsCnxt-noCS l d (CS.doneCS _ _) = refl

-- tsCnxt-noBF: the head-tcInit tsCnxt peer offers nothing at any BF.BFEv-image
tsCnxt-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.tsCnxt l d NS.tcInit (X , ιBF e₁) a ≡ nothing
tsCnxt-noBF l d (BF.sendBF _ _) = refl
tsCnxt-noBF l d (BF.receiveBF _ _) = refl
tsCnxt-noBF l d (BF.apiBFev _ _ _) = refl
tsCnxt-noBF l d (BF.doneBF _ _) = refl

-- tsSnxt-noCS: the head-tsInit tsSnxt peer offers nothing at any CS.CSEv-image
tsSnxt-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.tsSnxt l d NS.tsInit (X , ιCS e₁) a ≡ nothing
tsSnxt-noCS l d (CS.sendCS _ _) = refl
tsSnxt-noCS l d (CS.receiveCS _ _) = refl
tsSnxt-noCS l d (CS.apiCSev _ _ _) = refl
tsSnxt-noCS l d (CS.doneCS _ _) = refl

-- tsSnxt-noBF: the head-tsInit tsSnxt peer offers nothing at any BF.BFEv-image
tsSnxt-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.tsSnxt l d NS.tsInit (X , ιBF e₁) a ≡ nothing
tsSnxt-noBF l d (BF.sendBF _ _) = refl
tsSnxt-noBF l d (BF.receiveBF _ _) = refl
tsSnxt-noBF l d (BF.apiBFev _ _ _) = refl
tsSnxt-noBF l d (BF.doneBF _ _) = refl

-- csCnxt-noBF: csCnxt offers no table edge at any BF.BFEv-image event
csCnxt-noBF : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.csCnxt l d q (X , ιBF e₁) a ≡ nothing
csCnxt-noBF l d NS.ccIdle (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccIdle (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccIdle (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccIdle (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccWreq (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccWreq (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccWreq (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccWreq (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccAwait (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccAwait (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccAwait (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccAwait (BF.doneBF _ _) = refl
csCnxt-noBF l d (NS.ccWfi _) (BF.sendBF _ _) = refl
csCnxt-noBF l d (NS.ccWfi _) (BF.receiveBF _ _) = refl
csCnxt-noBF l d (NS.ccWfi _) (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d (NS.ccWfi _) (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccInt (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccInt (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccInt (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccInt (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccWdone (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccWdone (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccWdone (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccWdone (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccMust (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccMust (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccMust (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccMust (BF.doneBF _ _) = refl
csCnxt-noBF l d (NS.ccArf _) (BF.sendBF _ _) = refl
csCnxt-noBF l d (NS.ccArf _) (BF.receiveBF _ _) = refl
csCnxt-noBF l d (NS.ccArf _) (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d (NS.ccArf _) (BF.doneBF _ _) = refl
csCnxt-noBF l d (NS.ccArb _) (BF.sendBF _ _) = refl
csCnxt-noBF l d (NS.ccArb _) (BF.receiveBF _ _) = refl
csCnxt-noBF l d (NS.ccArb _) (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d (NS.ccArb _) (BF.doneBF _ _) = refl
csCnxt-noBF l d (NS.ccAif _) (BF.sendBF _ _) = refl
csCnxt-noBF l d (NS.ccAif _) (BF.receiveBF _ _) = refl
csCnxt-noBF l d (NS.ccAif _) (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d (NS.ccAif _) (BF.doneBF _ _) = refl
csCnxt-noBF l d (NS.ccAin _) (BF.sendBF _ _) = refl
csCnxt-noBF l d (NS.ccAin _) (BF.receiveBF _ _) = refl
csCnxt-noBF l d (NS.ccAin _) (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d (NS.ccAin _) (BF.doneBF _ _) = refl
csCnxt-noBF l d NS.ccTerm (BF.sendBF _ _) = refl
csCnxt-noBF l d NS.ccTerm (BF.receiveBF _ _) = refl
csCnxt-noBF l d NS.ccTerm (BF.apiBFev _ _ _) = refl
csCnxt-noBF l d NS.ccTerm (BF.doneBF _ _) = refl

-- csSnxt-noBF: csSnxt offers no table edge at any BF.BFEv-image event
csSnxt-noBF : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.csSnxt l d q (X , ιBF e₁) a ≡ nothing
csSnxt-noBF l d NS.csIdle (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csIdle (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csIdle (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csIdle (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csAreq (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csAreq (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csAreq (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csAreq (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csCanAwait (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csCanAwait (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csCanAwait (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csCanAwait (BF.doneBF _ _) = refl
csSnxt-noBF l d (NS.csAfi _) (BF.sendBF _ _) = refl
csSnxt-noBF l d (NS.csAfi _) (BF.receiveBF _ _) = refl
csSnxt-noBF l d (NS.csAfi _) (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d (NS.csAfi _) (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csInt (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csInt (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csInt (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csInt (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csDdone (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csDdone (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csDdone (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csDdone (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csMust (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csMust (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csMust (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csMust (BF.doneBF _ _) = refl
csSnxt-noBF l d (NS.csWrf _) (BF.sendBF _ _) = refl
csSnxt-noBF l d (NS.csWrf _) (BF.receiveBF _ _) = refl
csSnxt-noBF l d (NS.csWrf _) (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d (NS.csWrf _) (BF.doneBF _ _) = refl
csSnxt-noBF l d (NS.csWrb _) (BF.sendBF _ _) = refl
csSnxt-noBF l d (NS.csWrb _) (BF.receiveBF _ _) = refl
csSnxt-noBF l d (NS.csWrb _) (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d (NS.csWrb _) (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csWar (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csWar (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csWar (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csWar (BF.doneBF _ _) = refl
csSnxt-noBF l d (NS.csWif _) (BF.sendBF _ _) = refl
csSnxt-noBF l d (NS.csWif _) (BF.receiveBF _ _) = refl
csSnxt-noBF l d (NS.csWif _) (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d (NS.csWif _) (BF.doneBF _ _) = refl
csSnxt-noBF l d (NS.csWin _) (BF.sendBF _ _) = refl
csSnxt-noBF l d (NS.csWin _) (BF.receiveBF _ _) = refl
csSnxt-noBF l d (NS.csWin _) (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d (NS.csWin _) (BF.doneBF _ _) = refl
csSnxt-noBF l d NS.csTerm (BF.sendBF _ _) = refl
csSnxt-noBF l d NS.csTerm (BF.receiveBF _ _) = refl
csSnxt-noBF l d NS.csTerm (BF.apiBFev _ _ _) = refl
csSnxt-noBF l d NS.csTerm (BF.doneBF _ _) = refl

-- bfCnxt-noCS: bfCnxt offers no table edge at any CS.CSEv-image event
bfCnxt-noCS : (l : Link) (d : Dir) (q : NS.BFcPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.bfCnxt l d q (X , ιCS e₁) a ≡ nothing
bfCnxt-noCS l d NS.bcIdle (CS.sendCS _ _) = refl
bfCnxt-noCS l d NS.bcIdle (CS.receiveCS _ _) = refl
bfCnxt-noCS l d NS.bcIdle (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d NS.bcIdle (CS.doneCS _ _) = refl
bfCnxt-noCS l d (NS.bcWrr _) (CS.sendCS _ _) = refl
bfCnxt-noCS l d (NS.bcWrr _) (CS.receiveCS _ _) = refl
bfCnxt-noCS l d (NS.bcWrr _) (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d (NS.bcWrr _) (CS.doneCS _ _) = refl
bfCnxt-noCS l d NS.bcBusy (CS.sendCS _ _) = refl
bfCnxt-noCS l d NS.bcBusy (CS.receiveCS _ _) = refl
bfCnxt-noCS l d NS.bcBusy (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d NS.bcBusy (CS.doneCS _ _) = refl
bfCnxt-noCS l d NS.bcWcd (CS.sendCS _ _) = refl
bfCnxt-noCS l d NS.bcWcd (CS.receiveCS _ _) = refl
bfCnxt-noCS l d NS.bcWcd (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d NS.bcWcd (CS.doneCS _ _) = refl
bfCnxt-noCS l d NS.bcStream (CS.sendCS _ _) = refl
bfCnxt-noCS l d NS.bcStream (CS.receiveCS _ _) = refl
bfCnxt-noCS l d NS.bcStream (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d NS.bcStream (CS.doneCS _ _) = refl
bfCnxt-noCS l d (NS.bcAblk _) (CS.sendCS _ _) = refl
bfCnxt-noCS l d (NS.bcAblk _) (CS.receiveCS _ _) = refl
bfCnxt-noCS l d (NS.bcAblk _) (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d (NS.bcAblk _) (CS.doneCS _ _) = refl
bfCnxt-noCS l d NS.bcTerm (CS.sendCS _ _) = refl
bfCnxt-noCS l d NS.bcTerm (CS.receiveCS _ _) = refl
bfCnxt-noCS l d NS.bcTerm (CS.apiCSev _ _ _) = refl
bfCnxt-noCS l d NS.bcTerm (CS.doneCS _ _) = refl

-- bfSnxt-noCS: bfSnxt offers no table edge at any CS.CSEv-image event
bfSnxt-noCS : (l : Link) (d : Dir) (q : NS.BFsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.bfSnxt l d q (X , ιCS e₁) a ≡ nothing
bfSnxt-noCS l d NS.bsIdle (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsIdle (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsIdle (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsIdle (CS.doneCS _ _) = refl
bfSnxt-noCS l d (NS.bsAreq _) (CS.sendCS _ _) = refl
bfSnxt-noCS l d (NS.bsAreq _) (CS.receiveCS _ _) = refl
bfSnxt-noCS l d (NS.bsAreq _) (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d (NS.bsAreq _) (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsBusy (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsBusy (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsBusy (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsBusy (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsDdone (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsDdone (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsDdone (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsDdone (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsWsb (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsWsb (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsWsb (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsWsb (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsStream (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsStream (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsStream (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsStream (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsWnb (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsWnb (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsWnb (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsWnb (CS.doneCS _ _) = refl
bfSnxt-noCS l d (NS.bsWblk _) (CS.sendCS _ _) = refl
bfSnxt-noCS l d (NS.bsWblk _) (CS.receiveCS _ _) = refl
bfSnxt-noCS l d (NS.bsWblk _) (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d (NS.bsWblk _) (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsWbd (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsWbd (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsWbd (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsWbd (CS.doneCS _ _) = refl
bfSnxt-noCS l d NS.bsTerm (CS.sendCS _ _) = refl
bfSnxt-noCS l d NS.bsTerm (CS.receiveCS _ _) = refl
bfSnxt-noCS l d NS.bsTerm (CS.apiCSev _ _ _) = refl
bfSnxt-noCS l d NS.bsTerm (CS.doneCS _ _) = refl

------------------------------------------------------------------------
-- GAP-B L4 (abstract-bundle sibling non-offers) — the `¬ IoOffers` facts the
-- abstract-bundle `⦀-ev-L/R` reassembly threads past the driven peer.  The
-- `⦀-viewV-nothing` group builder consumes per-operand `¬ IoOffers`; these are
-- the CROSS-PROTOCOL siblings (a KA/TS/opposite-protocol spec peer never fires
-- the driven peer's ι-image event).  Built by the reverse-of-`noOffer→viewV`
-- bridge `viewV→noOffer` over the `tableSpec-viewV-{noOffer,fin}` reductions.
------------------------------------------------------------------------

-- reverse of `noOffer→viewV`: a `viewV (force P) ≡ nothing` at (e,a) rules out
-- any visible io step there (a step would give `v (e,a) ≡ just`, via `ev-inv`)
viewV→noOffer : (P : NetProc) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → Op.viewV (PTree.force P) (X , e) a ≡ nothing → ¬ IoOffers P e a
viewV→noOffer P {X} {e} {a} vn (M , step) with ev-inv step
... | v , τc , feq , veq =
      nothing-absurd
        (trans (sym (trans (sym (cong (λ n → Op.viewV n (X , e) a) feq)) vn)) veq)

-- kaClientSpec never fires a ChainSync-image event (foreign to its KA table)
kaClientSpec-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (kaClientSpec l d) (ιCS e₁) a
kaClientSpec-noCS l d e₁ {a} = viewV→noOffer (kaClientSpec l d) {e = ιCS e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
     NS.kcClient {e = ιCS e₁} {a = a} refl (kaCnxt-noCS l d e₁ {a = a}))

-- kaServerSpec never fires a ChainSync-image event
kaServerSpec-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (kaServerSpec l d) (ιCS e₁) a
kaServerSpec-noCS l d e₁ {a} = viewV→noOffer (kaServerSpec l d) {e = ιCS e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
     NS.ksClient {e = ιCS e₁} {a = a} refl (kaSnxt-noCS l d e₁ {a = a}))

-- tsClientSpec never fires a ChainSync-image event
tsClientSpec-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (tsClientSpec l d) (ιCS e₁) a
tsClientSpec-noCS l d e₁ {a} = viewV→noOffer (tsClientSpec l d) {e = ιCS e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
     NS.tcInit {e = ιCS e₁} {a = a} refl (tsCnxt-noCS l d e₁ {a = a}))

-- tsServerSpec never fires a ChainSync-image event
tsServerSpec-noCS : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (tsServerSpec l d) (ιCS e₁) a
tsServerSpec-noCS l d e₁ {a} = viewV→noOffer (tsServerSpec l d) {e = ιCS e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
     NS.tsInit {e = ιCS e₁} {a = a} refl (tsSnxt-noCS l d e₁ {a = a}))

-- the abstract BF client never fires a ChainSync-image event (terminal or
-- foreign no-edge; case its coarse `isFin`)
absBFc-noCS : (l : Link) (d : Dir) (q : BFcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absBFc l d q) (ιCS e₁) a
absBFc-noCS l d q e₁ {a} with NS.bfCfin (coarsenBFc q) in fEq
... | true  = viewV→noOffer (absBFc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιCS e₁} {a = a} fEq (bfCnxt-noCS l d (coarsenBFc q) e₁ {a = a}))

-- the abstract BF server never fires a ChainSync-image event
absBFs-noCS : (l : Link) (d : Dir) (q : BFsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absBFs l d q) (ιCS e₁) a
absBFs-noCS l d q e₁ {a} with NS.bfSfin (coarsenBFs q) in fEq
... | true  = viewV→noOffer (absBFs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιCS e₁} {a = a} fEq (bfSnxt-noCS l d (coarsenBFs q) e₁ {a = a}))

-- kaClientSpec never fires a BlockFetch-image event
kaClientSpec-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (kaClientSpec l d) (ιBF e₁) a
kaClientSpec-noBF l d e₁ {a} = viewV→noOffer (kaClientSpec l d) {e = ιBF e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
     NS.kcClient {e = ιBF e₁} {a = a} refl (kaCnxt-noBF l d e₁ {a = a}))

-- kaServerSpec never fires a BlockFetch-image event
kaServerSpec-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (kaServerSpec l d) (ιBF e₁) a
kaServerSpec-noBF l d e₁ {a} = viewV→noOffer (kaServerSpec l d) {e = ιBF e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
     NS.ksClient {e = ιBF e₁} {a = a} refl (kaSnxt-noBF l d e₁ {a = a}))

-- tsClientSpec never fires a BlockFetch-image event
tsClientSpec-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (tsClientSpec l d) (ιBF e₁) a
tsClientSpec-noBF l d e₁ {a} = viewV→noOffer (tsClientSpec l d) {e = ιBF e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
     NS.tcInit {e = ιBF e₁} {a = a} refl (tsCnxt-noBF l d e₁ {a = a}))

-- tsServerSpec never fires a BlockFetch-image event
tsServerSpec-noBF : (l : Link) (d : Dir) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (tsServerSpec l d) (ιBF e₁) a
tsServerSpec-noBF l d e₁ {a} = viewV→noOffer (tsServerSpec l d) {e = ιBF e₁} {a = a}
  (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
     NS.tsInit {e = ιBF e₁} {a = a} refl (tsSnxt-noBF l d e₁ {a = a}))

-- tsCnxt-noCS-pos: the abstract tsCnxt peer offers no table edge at any CS.CSEv-image event (any position)
tsCnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.TScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.tsCnxt l d q (X , ιCS e₁) a ≡ nothing
tsCnxt-noCS-pos l d NS.tcInit (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcInit (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcInit (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcInit (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcIdle (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcIdle (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcIdle (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcIdle (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (Blocking , _ , _)) (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (NonBlocking , _ , _)) (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (Blocking , _ , _)) (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (NonBlocking , _ , _)) (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (Blocking , _ , _)) (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (NonBlocking , _ , _)) (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (Blocking , _ , _)) (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcAri (NonBlocking , _ , _)) (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcBlk (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcBlk (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcBlk (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcBlk (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcNbl (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcNbl (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcNbl (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcNbl (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcArt _) (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcArt _) (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcArt _) (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d (NS.tcArt _) (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTxs (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTxs (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTxs (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcTxs (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWri _) (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWri _) (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWri _) (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWri _) (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcWdone (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcWdone (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcWdone (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcWdone (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWrt _) (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWrt _) (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWrt _) (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d (NS.tcWrt _) (CS.doneCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTerm (CS.sendCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTerm (CS.receiveCS _ _) = refl
tsCnxt-noCS-pos l d NS.tcTerm (CS.apiCSev _ _ _) = refl
tsCnxt-noCS-pos l d NS.tcTerm (CS.doneCS _ _) = refl

-- tsCnxt-noBF-pos: the abstract tsCnxt peer offers no table edge at any BF.BFEv-image event (any position)
tsCnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.TScPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.tsCnxt l d q (X , ιBF e₁) a ≡ nothing
tsCnxt-noBF-pos l d NS.tcInit (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcInit (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcInit (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcInit (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcIdle (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcIdle (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcIdle (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcIdle (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (Blocking , _ , _)) (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (NonBlocking , _ , _)) (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (Blocking , _ , _)) (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (NonBlocking , _ , _)) (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (Blocking , _ , _)) (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (NonBlocking , _ , _)) (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (Blocking , _ , _)) (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcAri (NonBlocking , _ , _)) (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcBlk (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcBlk (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcBlk (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcBlk (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcNbl (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcNbl (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcNbl (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcNbl (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcArt _) (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcArt _) (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcArt _) (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d (NS.tcArt _) (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTxs (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTxs (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTxs (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcTxs (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWri _) (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWri _) (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWri _) (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWri _) (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcWdone (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcWdone (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcWdone (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcWdone (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWrt _) (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWrt _) (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWrt _) (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d (NS.tcWrt _) (BF.doneBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTerm (BF.sendBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTerm (BF.receiveBF _ _) = refl
tsCnxt-noBF-pos l d NS.tcTerm (BF.apiBFev _ _ _) = refl
tsCnxt-noBF-pos l d NS.tcTerm (BF.doneBF _ _) = refl

-- tsSnxt-noCS-pos: the abstract tsSnxt peer offers no table edge at any CS.CSEv-image event (any position)
tsSnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.TSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.tsSnxt l d q (X , ιCS e₁) a ≡ nothing
tsSnxt-noCS-pos l d NS.tsInit (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsInit (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsInit (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsInit (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsIdle (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsIdle (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsIdle (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsIdle (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWib _) (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWib _) (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWib _) (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWib _) (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWin _) (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWin _) (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWin _) (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWin _) (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWrt _) (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWrt _) (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWrt _) (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d (NS.tsWrt _) (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsBlk (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsBlk (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsBlk (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsBlk (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsNbl (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsNbl (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsNbl (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsNbl (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTxs (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTxs (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTxs (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsTxs (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsDdone (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsDdone (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsDdone (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsDdone (CS.doneCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTerm (CS.sendCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTerm (CS.receiveCS _ _) = refl
tsSnxt-noCS-pos l d NS.tsTerm (CS.apiCSev _ _ _) = refl
tsSnxt-noCS-pos l d NS.tsTerm (CS.doneCS _ _) = refl

-- tsSnxt-noBF-pos: the abstract tsSnxt peer offers no table edge at any BF.BFEv-image event (any position)
tsSnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.TSsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.tsSnxt l d q (X , ιBF e₁) a ≡ nothing
tsSnxt-noBF-pos l d NS.tsInit (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsInit (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsInit (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsInit (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsIdle (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsIdle (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsIdle (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsIdle (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWib _) (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWib _) (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWib _) (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWib _) (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWin _) (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWin _) (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWin _) (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWin _) (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWrt _) (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWrt _) (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWrt _) (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d (NS.tsWrt _) (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsBlk (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsBlk (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsBlk (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsBlk (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsNbl (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsNbl (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsNbl (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsNbl (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTxs (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTxs (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTxs (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsTxs (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsDdone (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsDdone (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsDdone (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsDdone (BF.doneBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTerm (BF.sendBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTerm (BF.receiveBF _ _) = refl
tsSnxt-noBF-pos l d NS.tsTerm (BF.apiBFev _ _ _) = refl
tsSnxt-noBF-pos l d NS.tsTerm (BF.doneBF _ _) = refl

-- the abstract TS client never fires a CS.CSEv-image event (any tracked position)
absTSc-noCS : (l : Link) (d : Dir) (q : TScPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absTSc l d q) (ιCS e₁) a
absTSc-noCS l d q e₁ {a} with NS.tsCfin (coarsenTSc q) in fEq
... | true  = viewV→noOffer (absTSc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιCS e₁} {a = a} fEq (tsCnxt-noCS-pos l d (coarsenTSc q) e₁ {a = a}))

-- the abstract TS client never fires a BF.BFEv-image event (any tracked position)
absTSc-noBF : (l : Link) (d : Dir) (q : TScPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absTSc l d q) (ιBF e₁) a
absTSc-noBF l d q e₁ {a} with NS.tsCfin (coarsenTSc q) in fEq
... | true  = viewV→noOffer (absTSc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιBF e₁} {a = a} fEq (tsCnxt-noBF-pos l d (coarsenTSc q) e₁ {a = a}))

-- the abstract TS server never fires a CS.CSEv-image event (any tracked position)
absTSs-noCS : (l : Link) (d : Dir) (q : TSsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absTSs l d q) (ιCS e₁) a
absTSs-noCS l d q e₁ {a} with NS.tsSfin (coarsenTSs q) in fEq
... | true  = viewV→noOffer (absTSs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιCS e₁} {a = a} fEq (tsSnxt-noCS-pos l d (coarsenTSs q) e₁ {a = a}))

-- the abstract TS server never fires a BF.BFEv-image event (any tracked position)
absTSs-noBF : (l : Link) (d : Dir) (q : TSsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absTSs l d q) (ιBF e₁) a
absTSs-noBF l d q e₁ {a} with NS.tsSfin (coarsenTSs q) in fEq
... | true  = viewV→noOffer (absTSs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιBF e₁} {a = a} fEq (tsSnxt-noBF-pos l d (coarsenTSs q) e₁ {a = a}))

-- KA table foreign-channel non-offers (position-enumerated: `kaCnxt`/`kaSnxt`
-- match the position first, so `refl` needs a concrete position; the foreign
-- CS/BF-image event then hits the `nothing` catch-all at every position)
kaCnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.KAcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.kaCnxt l d q (X , ιCS e₁) a ≡ nothing
kaCnxt-noCS-pos l d NS.kcClient (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcClient (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcClient (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d NS.kcClient (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcWmsg _) (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcWmsg _) (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcWmsg _) (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d (NS.kcWmsg _) (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcAwait _) (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcAwait _) (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcAwait _) (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d (NS.kcAwait _) (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcWdone (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcWdone (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcWdone (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d NS.kcWdone (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcErr _ _) (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcErr _ _) (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d (NS.kcErr _ _) (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d (NS.kcErr _ _) (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTerm (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTerm (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTerm (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d NS.kcTerm (CS.doneCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTermE (CS.sendCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTermE (CS.receiveCS _ _) = refl
kaCnxt-noCS-pos l d NS.kcTermE (CS.apiCSev _ _ _) = refl
kaCnxt-noCS-pos l d NS.kcTermE (CS.doneCS _ _) = refl
kaCnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.KAcPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.kaCnxt l d q (X , ιBF e₁) a ≡ nothing
kaCnxt-noBF-pos l d NS.kcClient (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcClient (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcClient (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d NS.kcClient (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcWmsg _) (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcWmsg _) (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcWmsg _) (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d (NS.kcWmsg _) (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcAwait _) (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcAwait _) (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcAwait _) (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d (NS.kcAwait _) (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcWdone (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcWdone (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcWdone (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d NS.kcWdone (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcErr _ _) (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcErr _ _) (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d (NS.kcErr _ _) (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d (NS.kcErr _ _) (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTerm (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTerm (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTerm (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d NS.kcTerm (BF.doneBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTermE (BF.sendBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTermE (BF.receiveBF _ _) = refl
kaCnxt-noBF-pos l d NS.kcTermE (BF.apiBFev _ _ _) = refl
kaCnxt-noBF-pos l d NS.kcTermE (BF.doneBF _ _) = refl
kaSnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.KAsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.kaSnxt l d q (X , ιCS e₁) a ≡ nothing
kaSnxt-noCS-pos l d NS.ksClient (CS.sendCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksClient (CS.receiveCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksClient (CS.apiCSev _ _ _) = refl
kaSnxt-noCS-pos l d NS.ksClient (CS.doneCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksRecv _) (CS.sendCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksRecv _) (CS.receiveCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksRecv _) (CS.apiCSev _ _ _) = refl
kaSnxt-noCS-pos l d (NS.ksRecv _) (CS.doneCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksResp _) (CS.sendCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksResp _) (CS.receiveCS _ _) = refl
kaSnxt-noCS-pos l d (NS.ksResp _) (CS.apiCSev _ _ _) = refl
kaSnxt-noCS-pos l d (NS.ksResp _) (CS.doneCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksDdone (CS.sendCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksDdone (CS.receiveCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksDdone (CS.apiCSev _ _ _) = refl
kaSnxt-noCS-pos l d NS.ksDdone (CS.doneCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksTerm (CS.sendCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksTerm (CS.receiveCS _ _) = refl
kaSnxt-noCS-pos l d NS.ksTerm (CS.apiCSev _ _ _) = refl
kaSnxt-noCS-pos l d NS.ksTerm (CS.doneCS _ _) = refl
kaSnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.KAsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.kaSnxt l d q (X , ιBF e₁) a ≡ nothing
kaSnxt-noBF-pos l d NS.ksClient (BF.sendBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksClient (BF.receiveBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksClient (BF.apiBFev _ _ _) = refl
kaSnxt-noBF-pos l d NS.ksClient (BF.doneBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksRecv _) (BF.sendBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksRecv _) (BF.receiveBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksRecv _) (BF.apiBFev _ _ _) = refl
kaSnxt-noBF-pos l d (NS.ksRecv _) (BF.doneBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksResp _) (BF.sendBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksResp _) (BF.receiveBF _ _) = refl
kaSnxt-noBF-pos l d (NS.ksResp _) (BF.apiBFev _ _ _) = refl
kaSnxt-noBF-pos l d (NS.ksResp _) (BF.doneBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksDdone (BF.sendBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksDdone (BF.receiveBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksDdone (BF.apiBFev _ _ _) = refl
kaSnxt-noBF-pos l d NS.ksDdone (BF.doneBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksTerm (BF.sendBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksTerm (BF.receiveBF _ _) = refl
kaSnxt-noBF-pos l d NS.ksTerm (BF.apiBFev _ _ _) = refl
kaSnxt-noBF-pos l d NS.ksTerm (BF.doneBF _ _) = refl

-- the abstract KA client never fires a CS.CSEv-image event (any tracked position)
absKAc-noCS : (l : Link) (d : Dir) (q : KAcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absKAc l d q) (ιCS e₁) a
absKAc-noCS l d q e₁ {a} with NS.kaCfin (coarsenKAc q) in fEq
... | true  = viewV→noOffer (absKAc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιCS e₁} {a = a} fEq (kaCnxt-noCS-pos l d (coarsenKAc q) e₁ {a = a}))

-- the abstract KA client never fires a BF.BFEv-image event (any tracked position)
absKAc-noBF : (l : Link) (d : Dir) (q : KAcPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absKAc l d q) (ιBF e₁) a
absKAc-noBF l d q e₁ {a} with NS.kaCfin (coarsenKAc q) in fEq
... | true  = viewV→noOffer (absKAc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιBF e₁} {a = a} fEq (kaCnxt-noBF-pos l d (coarsenKAc q) e₁ {a = a}))

-- the abstract KA server never fires a CS.CSEv-image event (any tracked position)
absKAs-noCS : (l : Link) (d : Dir) (q : KAsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absKAs l d q) (ιCS e₁) a
absKAs-noCS l d q e₁ {a} with NS.kaSfin (coarsenKAs q) in fEq
... | true  = viewV→noOffer (absKAs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιCS e₁} {a = a} fEq (kaSnxt-noCS-pos l d (coarsenKAs q) e₁ {a = a}))

-- the abstract KA server never fires a BF.BFEv-image event (any tracked position)
absKAs-noBF : (l : Link) (d : Dir) (q : KAsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absKAs l d q) (ιBF e₁) a
absKAs-noBF l d q e₁ {a} with NS.kaSfin (coarsenKAs q) in fEq
... | true  = viewV→noOffer (absKAs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιBF e₁} {a = a} fEq (kaSnxt-noBF-pos l d (coarsenKAs q) e₁ {a = a}))

-- the abstract CS client never fires a BlockFetch-image event
absCSc-noBF : (l : Link) (d : Dir) (q : CScPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absCSc l d q) (ιBF e₁) a
absCSc-noBF l d q e₁ {a} with NS.csCfin (coarsenCSc q) in fEq
... | true  = viewV→noOffer (absCSc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιBF e₁} {a = a} fEq (csCnxt-noBF l d (coarsenCSc q) e₁ {a = a}))

-- the abstract CS server never fires a BlockFetch-image event
absCSs-noBF : (l : Link) (d : Dir) (q : CSsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absCSs l d q) (ιBF e₁) a
absCSs-noBF l d q e₁ {a} with NS.csSfin (coarsenCSs q) in fEq
... | true  = viewV→noOffer (absCSs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιBF e₁} {a = a} fEq (csSnxt-noBF l d (coarsenCSs q) e₁ {a = a}))

------------------------------------------------------------------------
-- GAP-B step 2 — AUGMENTED per-peer sims.  Extend `sim{peer}` to ALSO expose
-- the source event `e₁`, the ι-image equation `e ≡ ιX e₁`, and the fired
-- direction `{cs,bf}EvDir e₁ ≡ d` — the extra data `bundle-{CS,BF}-ev-inv`
-- needs to ROUTE the peel (which protocol/direction) and rebuild the abstract
-- bundle.  Thin wrappers over the existing `sim{peer}` machinery.
------------------------------------------------------------------------

-- augmented CS-client sim (exposes e₁ / e≡ιCS e₁ / csEvDir e₁≡d)
simCSc′ : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ CS.CSEv X ] Σ[ pos′ ∈ CScPos ]
       (e ≡ ιCS e₁) × (csEvDir e₁ ≡ d) × (M ≡ decCSc l d pos′)
       × (absCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSc l d pos′)
simCSc′ l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decCSc-src-ev-inv l d pos srcStep | ιCS-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decCSc-src-dir l d pos srcStep ,
        trans Meq (cong RenCS.renameMap P′eq) , aStep

-- augmented CS-server sim
simCSs′ : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ CS.CSEv X ] Σ[ pos′ ∈ CSsPos ]
       (e ≡ ιCS e₁) × (csEvDir e₁ ≡ d) × (M ≡ decCSs l d pos′)
       × (absCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSs l d pos′)
simCSs′ l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decCSs-src-ev-inv l d pos srcStep | ιCS-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decCSs-src-dir l d pos srcStep ,
        trans Meq (cong RenCS.renameMap P′eq) , aStep

-- augmented BF-client sim
simBFc′ : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ BF.BFEv X ] Σ[ pos′ ∈ BFcPos ]
       (e ≡ ιBF e₁) × (bfEvDir e₁ ≡ d) × (M ≡ decBFc l d pos′)
       × (absBFc l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFc l d pos′)
simBFc′ l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decBFc-src-ev-inv l d pos srcStep | ιBF-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decBFc-src-dir l d pos srcStep ,
        trans Meq (cong RenBF.renameMap P′eq) , aStep

-- augmented BF-server sim
simBFs′ : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ BF.BFEv X ] Σ[ pos′ ∈ BFsPos ]
       (e ≡ ιBF e₁) × (bfEvDir e₁ ≡ d) × (M ≡ decBFs l d pos′)
       × (absBFs l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFs l d pos′)
simBFs′ l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decBFs-src-ev-inv l d pos srcStep | ιBF-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decBFs-src-dir l d pos srcStep ,
        trans Meq (cong RenBF.renameMap P′eq) , aStep


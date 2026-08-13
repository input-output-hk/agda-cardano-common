{-# OPTIONS --guardedness #-}

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle (blkA : Block₃) where

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

open import CSP.Examples.Cardano_network.FourNode.Liveness.R2_Bisim.SysOracle_RouteLnLf blkA public

------------------------------------------------------------------------
-- GAP-B LINK-pinning leaf (mirror of the DIRECTION layer).  Each driven
-- peer at any position fires only its OWN link's api/done events, so two
-- distinct-link bundles never fire the same api event (the node two-link
-- ⦀ evBoth refutation for the visible/api case).
------------------------------------------------------------------------

-- the link component of a ChainSync source event
csEvLink : {X : Set 0ℓ} → CS.CSEv X → Link
csEvLink (CS.sendCS l d)    = l
csEvLink (CS.receiveCS l d) = l
csEvLink (CS.apiCSev l d m) = l
csEvLink (CS.doneCS l d)    = l

-- the link component of a BlockFetch source event
bfEvLink : {X : Set 0ℓ} → BF.BFEv X → Link
bfEvLink (BF.sendBF l d)    = l
bfEvLink (BF.receiveBF l d) = l
bfEvLink (BF.apiBFev l d m) = l
bfEvLink (BF.doneBF l d)    = l

-- LINK: decCSc-src-link — the visible source step of a fine position fires
-- an event whose link component is `l` (csEvLink extracts it).
decCSc-src-link : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSc-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → csEvLink e₁ ≡ l
-- head stIdle : fires apiCSev sendCSRequestNext / FindIntersect / Done
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRequestNext} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} {a} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSDone} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollForward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollBackward}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollforward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollback}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-link l d (csHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
-- head stCanAwait : fires receiveCS RollForward / RollBackward / AwaitReply
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSAwaitReply} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' m}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-link l d (csHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
-- head stMustReply : fires receiveCS RollForward / RollBackward
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-link l d (csHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
-- head stIntersect : fires receiveCS IntersectFound / IntersectNotFound
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-link l d (csHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSc-src-link l d (csHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid csReqNext1 : fires sendCS payload → csSil stCanAwait
decCSc-src-link l d csReqNext1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d csReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-link l d csReqNext1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-link l d csReqNext1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
-- mid csFindInt1 ps : fires sendCS payload → csSil stIntersect
decCSc-src-link l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d (csFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-link l d (csFindInt1 ps) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-link l d (csFindInt1 ps) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
-- mid csDone1 : fires sendCS payload → csSil stDone
decCSc-src-link l d csDone1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d csDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-link l d csDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-link l d csDone1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
-- mid csRF1 : fires apiCSev recvCSRollforward (h,t) → csSil stIdle
decCSc-src-link l d (csRF1 h t) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollforward) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (h , t)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d (csRF1 h t) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-link l d (csRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-link l d (csRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
-- mid csRB1 : fires apiCSev recvCSRollback (pt,tp) → csSil stIdle
decCSc-src-link l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollback) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d (csRB1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-link l d (csRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-link l d (csRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
-- mid csIF1 : fires apiCSev recvCSIntersectFound (pt,tp) → csSil stIdle
decCSc-src-link l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d (csIF1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-link l d (csIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-link l d (csIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
-- mid csINF1 : fires apiCSev recvCSIntersectNotFound tp → csSil stIdle
decCSc-src-link l d (csINF1 tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectNotFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ tp
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSc-src-link l d (csINF1 tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-link l d (csINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-link l d (csINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
-- loop re-entry csSil : forces to `sil`, no visible step
decCSc-src-link l d (csSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- LINK: decCSs-src-link — the visible source step of a fine position fires
-- an event whose link component is `l` (csEvLink extracts it).
decCSs-src-link : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSs-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → csEvLink e₁ ≡ l
-- head stIdle : receives RequestNext / FindIntersect / Done on the wire
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSRequestNext} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSFindIntersect ps)} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSDone} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-link l d (ssHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
-- head stCanAwait : sends RollForward / RollBackward / AwaitReply via api
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-link l d (ssHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
-- head stMustReply : sends RollForward / RollBackward via api
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-link l d (ssHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
-- head stIntersect : sends IntersectFound / IntersectNotFound via api
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollForward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollBackward}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollforward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollback}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSRequestNext}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-link l d (ssHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSs-src-link l d (ssHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid ssReqNext1 : fires api reqCSRequestNext (Prefix₀) → ssSil stCanAwait
decCSs-src-link l d ssReqNext1 {e₁ = CS.apiCSev l' d' m} s with step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSRequestNext) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decCSs-src-link l d ssReqNext1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-link l d ssReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-link l d ssReqNext1 {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
-- mid ssFindInt1 ps : fires api reqCSFindIntersect ps (Output) → ssSil stIntersect
decCSs-src-link l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSFindIntersect) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ CS.DecEq-ListPoint ⦄ a ps
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d (ssFindInt1 ps) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-link l d (ssFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-link l d (ssFindInt1 ps) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
-- mid ssDone1 : fires doneCS (Prefix₀) → ssSil stDone
decCSs-src-link l d ssDone1 {e₁ = CS.doneCS l' d'} s with step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.doneCS l d) (_ , CS.doneCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decCSs-src-link l d ssDone1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-link l d ssDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-link l d ssDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
-- mid ssRF1 : fires sendCS payload → ssSil stIdle
decCSs-src-link l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d (ssRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-link l d (ssRF1 h t) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-link l d (ssRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
-- mid ssRB1 : fires sendCS payload → ssSil stIdle
decCSs-src-link l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d (ssRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-link l d (ssRB1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-link l d (ssRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
-- mid ssAw1 : fires sendCS payload → ssSil stMustReply
decCSs-src-link l d ssAw1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d ssAw1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-link l d ssAw1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-link l d ssAw1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
-- mid ssIF1 : fires sendCS payload → ssSil stIdle
decCSs-src-link l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d (ssIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-link l d (ssIF1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-link l d (ssIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
-- mid ssINF1 : fires sendCS payload → ssSil stIdle
decCSs-src-link l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decCSs-src-link l d (ssINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-link l d (ssINF1 tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-link l d (ssINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
-- loop re-entry ssSil : forces to `sil`, no visible step
decCSs-src-link l d (ssSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- LINK: decBFc-src-link — the visible source step of a fine position fires
-- an event whose link component is `l` (bfEvLink extracts it).
decBFc-src-link : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFc-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → bfEvLink e₁ ≡ l
-- head stIdle : sends RequestRange / ClientDone via api
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFRequestRange} {a} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFClientDone} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' recvBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' reqBFRange}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-link l d (bcHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
-- head stBusy : receives StartBatch / NoBlocks (both go straight to a re-entry sil)
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgStartBatch} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgNoBlocks} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-link l d (bcHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
-- head stStreaming : receives Block (→ bcBlk1) / BatchDone (→ re-entry sil)
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgBlock b)} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgBatchDone} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-link l d (bcHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
-- head stDone : `ret`, no visible step
decBFc-src-link l d (bcHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bcReq1 r : fires sendBF payload → bcSil stBusy
decBFc-src-link l d (bcReq1 r) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-link l d (bcReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-link l d (bcReq1 r) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-link l d (bcReq1 r) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
-- mid bcDone1 : fires sendBF payload → bcSil stDone
decBFc-src-link l d bcDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-link l d bcDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-link l d bcDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-link l d bcDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
-- mid bcBlk1 b : fires apiBFev recvBFBlock b → bcSil stStreaming
decBFc-src-link l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d recvBFBlock) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ decBlock ⦄ a b
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFc-src-link l d (bcBlk1 b) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-link l d (bcBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-link l d (bcBlk1 b) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
-- loop re-entry bcSil : forces to `sil`, no visible step
decBFc-src-link l d (bcSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- LINK: decBFs-src-link — the visible source step of a fine position fires
-- an event whose link component is `l` (bfEvLink extracts it).
decBFs-src-link : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFs-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → bfEvLink e₁ ≡ l
-- head stIdle : receives RequestRange (→ bsReq1) / ClientDone (→ bsDone1)
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgRequestRange r)} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgClientDone} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-link l d (bsHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
-- head stBusy : sends StartBatch (→ bsStart1) / NoBlocks (→ bsNoBlk1) via api
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFNoBlocks} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBatchDone}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-link l d (bsHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
-- head stStreaming : sends Block (→ bsBlk1) / BatchDone (→ bsBatchDone1) via api
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBlock} {a} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBatchDone} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFStartBatch}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}     s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-link l d (bsHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
-- head stDone : `ret`
decBFs-src-link l d (bsHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bsReq1 r : fires api reqBFRange r (Output) → bsSil stBusy
decBFs-src-link l d (bsReq1 r) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d reqBFRange) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEq-ChainRange ⦄ a r
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-link l d (bsReq1 r) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-link l d (bsReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-link l d (bsReq1 r) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
-- mid bsDone1 : fires doneBF (Prefix₀) → bsSil stDone
decBFs-src-link l d bsDone1 {e₁ = BF.doneBF l' d'} s with step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.doneBF l d) (_ , BF.doneBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decBFs-src-link l d bsDone1 {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-link l d bsDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-link l d bsDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
-- mid bsStart1 : fires sendBF payload → bsSil stStreaming
decBFs-src-link l d bsStart1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-link l d bsStart1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-link l d bsStart1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-link l d bsStart1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
-- mid bsNoBlk1 : fires sendBF payload → bsSil stIdle
decBFs-src-link l d bsNoBlk1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-link l d bsNoBlk1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-link l d bsNoBlk1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-link l d bsNoBlk1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
-- mid bsBlk1 b : fires sendBF payload → bsSil stStreaming
decBFs-src-link l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-link l d (bsBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-link l d (bsBlk1 b) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-link l d (bsBlk1 b) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
-- mid bsBatchDone1 : fires sendBF payload → bsSil stIdle
decBFs-src-link l d bsBatchDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decBFs-src-link l d bsBatchDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-link l d bsBatchDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-link l d bsBatchDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
-- loop re-entry bsSil : forces to `sil`, no visible step
decBFs-src-link l d (bsSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- a Net_Api event carrying link `l` in its link component (exactly the
-- constructor shapes the CS/BF peers emit under ιCS/ιBF)
data ApiHasLink (l : Link) : {X : Set 0ℓ} → Net_Api Payload X → Set₁ where
  ahlIn   : ∀ {d ch} → ApiHasLink l (input  l d ch)
  ahlOut  : ∀ {d ch} → ApiHasLink l (output l d ch)
  ahlDone : ∀ {d ch} → ApiHasLink l (done   l d ch)
  ahlCS   : ∀ {d m}  → ApiHasLink l (apiCS  l d m)
  ahlBF   : ∀ {d m}  → ApiHasLink l (apiBF  l d m)
  ahlKA   : ∀ {d m}  → ApiHasLink l (apiKA  l d m)
  ahlTS   : ∀ {d m}  → ApiHasLink l (apiTS  l d m)
  ahlLN   : ∀ {d m}  → ApiHasLink l (apiLN  l d m)
  ahlLF   : ∀ {d m}  → ApiHasLink l (apiLF  l d m)

-- the link of a fixed event is unique (both witnesses pin the same slot)
apiLink-inj : {X : Set 0ℓ} {e : Net_Api Payload X} {l l′ : Link}
  → ApiHasLink l e → ApiHasLink l′ e → l ≡ l′
apiLink-inj ahlIn   ahlIn   = refl
apiLink-inj ahlOut  ahlOut  = refl
apiLink-inj ahlDone ahlDone = refl
apiLink-inj ahlCS   ahlCS   = refl
apiLink-inj ahlBF   ahlBF   = refl
apiLink-inj ahlKA   ahlKA   = refl
apiLink-inj ahlTS   ahlTS   = refl
apiLink-inj ahlLN   ahlLN   = refl
apiLink-inj ahlLF   ahlLF   = refl

-- ιCS carries the source link into the Net_Api event
csApiLink : {X : Set 0ℓ} (e₁ : CS.CSEv X) → ApiHasLink (csEvLink e₁) (ιCS e₁)
csApiLink (CS.sendCS l d)    = ahlIn
csApiLink (CS.receiveCS l d) = ahlOut
csApiLink (CS.apiCSev l d m) = ahlCS
csApiLink (CS.doneCS l d)    = ahlDone

-- ιBF carries the source link into the Net_Api event
bfApiLink : {X : Set 0ℓ} (e₁ : BF.BFEv X) → ApiHasLink (bfEvLink e₁) (ιBF e₁)
bfApiLink (BF.sendBF l d)    = ahlIn
bfApiLink (BF.receiveBF l d) = ahlOut
bfApiLink (BF.apiBFev l d m) = ahlBF
bfApiLink (BF.doneBF l d)    = ahlDone

-- the link a driven CS-client step exposes on the Net_Api event
csc-ev-link : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
csc-ev-link l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιCS-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιCS e₁)) (decCSc-src-link l d pos srcStep) (csApiLink e₁))

-- the link a driven CS-server step exposes on the Net_Api event
css-ev-link : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
css-ev-link l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιCS-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιCS e₁)) (decCSs-src-link l d pos srcStep) (csApiLink e₁))

-- the link a driven BF-client step exposes on the Net_Api event
bfc-ev-link : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
bfc-ev-link l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιBF-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιBF e₁)) (decBFc-src-link l d pos srcStep) (bfApiLink e₁))

-- the link a driven BF-server step exposes on the Net_Api event
bfs-ev-link : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
bfs-ev-link l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιBF-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιBF e₁)) (decBFs-src-link l d pos srcStep) (bfApiLink e₁))


------------------------------------------------------------------------
-- GAP-B — bundle link-pinning.  A bundleG step on a CS/BF-image event pins the
-- bundle's OWN link (ApiHasLink l e), so two distinct-link bundles of a node
-- never both fire the same api event (the node two-link ⦀ evBoth refutation).
------------------------------------------------------------------------

-- a bundleG CS-image step pins the bundle's link
bundleCS-ev-link : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► Bd′
  → ApiHasLink l (ιCS e₁)
bundleCS-ev-link l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL  _ sK     = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
... | PEA.evBoth _ sK _ = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL  _ sK     = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
...   | PEA.evBoth _ sK _ = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιCS e₁) (_ , sK))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM      = csc-ev-link l cl csc sM
...     | PEA.evBoth _ sM sTail =
            ⊥-elim (csTail-css-noOffer l cl sv css bfc bfs ip e₁
                      (λ q → cl≢sv (trans (apiDir-inj (csc-ev-dir l cl csc sM) (csApiDir e₁)) q))
                      (_ , sTail))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = css-ev-link l sv css sM
...       | PEA.evBoth _ sM sTail =
              ⊥-elim (csTail-bfc-noOffer l cl sv bfc bfs ip e₁ (_ , sTail))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM      = ⊥-elim (decBFc-noCSgen l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (decBFc-noCSgen l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = ⊥-elim (decBFs-noCSgen l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (decBFs-noCSgen l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM      = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM      = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιCS e₁) (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM      = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM      = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιCS e₁) (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιCS e₁) (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιCS e₁) (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιCS e₁) (_ , qs))

-- a bundleG BF-image step pins the bundle's link
bundleBF-ev-link : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► Bd′
  → ApiHasLink l (ιBF e₁)
bundleBF-ev-link l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL  _ sK     = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
... | PEA.evBoth _ sK _ = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL  _ sK     = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
...   | PEA.evBoth _ sK _ = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιBF e₁) (_ , sK))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM      = ⊥-elim (decCSc-noBFgen l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (decCSc-noBFgen l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = ⊥-elim (decCSs-noBFgen l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (decCSs-noBFgen l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM      = bfc-ev-link l cl bfc sM
...         | PEA.evBoth _ sM sTail =
              ⊥-elim (bfTail-bfs-noOffer l cl sv bfs ip e₁
                        (λ q → cl≢sv (trans (apiDir-inj (bfc-ev-dir l cl bfc sM) (bfApiDir e₁)) q))
                        (_ , sTail))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = bfs-ev-link l sv bfs sM
...           | PEA.evBoth _ sM sTail =
                ⊥-elim (bfTail-tsc-noOffer l cl sv ip e₁ (_ , sTail))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM      = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM      = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιBF e₁) (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM      = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM      = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιBF e₁) (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιBF e₁) (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιBF e₁) (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιBF e₁) (_ , qs))


------------------------------------------------------------------------
-- GAP-B DRIVER link-pinning.  Every driver phase fires an api event on the
-- driver's OWN link (`apiCS l d …` / `apiBF l d …`); the fired event's link is
-- pinned by extracting the fired label and matching it against the phase's
-- head channel (`refl` unifies `e` to `apiCS/apiBF l d …` ⇒ `ahlCS`/`ahlBF`).
-- Needed to ALIGN the driver's firing link with the bundle's in `nodeX-ev-inv`
-- (and to refute the two-driver `⦀` evBoth of nodes A/D).
------------------------------------------------------------------------

-- an `Output` visible step exposes its own label (the fired event ≡ the head
-- channel `ce` at value `v`) — the label-returning twin of `output-ev-inv`
output-ev-lab : {R : Set} {B : Set 0ℓ} {deqB : DecEq B} {ce : Net_Api Payload B} {v : B}
    {P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
  → (Output ⦃ deqB ⦄ ce v P) ─[ ev (evl (evLabel X e a)) ]─► M
  → evl {R = R} (evLabel X e a) ≡ evl (evLabel B ce v)
output-ev-lab {R} {B} {deqB} {ce} {v} {P} {X} {e} {a} (sVis refl br)
    with Net_Api-≟ {Payload} (B , ce) (X , e)
... | no  ¬eq  = ⊥-elim (nothing-absurd br)
... | yes refl with _≟_ ⦃ deqB ⦄ a v
...   | yes refl = refl
...   | no  _    = ⊥-elim (nothing-absurd br)

-- a `Prefix` visible step exposes its own label (the fired event ≡ the head
-- channel `ce`) — the label-returning twin of `prefix-ev-inv`
prefix-ev-lab : {R : Set} {A : Set 0ℓ} {ce : Net_Api Payload A}
    {P : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
  → (Prefix ce P) ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ x ∈ A ] (evl {R = R} (evLabel X e a) ≡ evl (evLabel A ce x))
prefix-ev-lab {a = a} (sVis refl br) with Prefix-cont-fires br
... | refl , _ , _ = a , refl

-- producer-driver link-pinning: every phase fires apiCS/apiBF on link `l`
decProd-ev-link : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decProd l d blk pp ─[ ev (evl (evLabel X e a)) ]─► M → ApiHasLink l e
decProd-ev-link l d blk pp0 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlCS
decProd-ev-link l d blk pp1 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlCS
decProd-ev-link l d blk pp2 step with output-ev-lab step
... | refl = ahlCS
decProd-ev-link l d blk pp3 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlBF
decProd-ev-link l d blk pp4 step with output-ev-lab step
... | refl = ahlBF
decProd-ev-link l d blk pp5 step with output-ev-lab step
... | refl = ahlBF
decProd-ev-link l d blk pp6 step with output-ev-lab step
... | refl = ahlBF
decProd-ev-link l d blk pp7 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlDone
decProd-ev-link l d blk pp8 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlDone
decProd-ev-link l d blk pp9 step = ⊥-elim (ret-no-ev {P = decProd l d blk pp9} refl step)

-- consumer-driver link-pinning: every phase fires apiCS/apiBF on link `l`
decCons-ev-link : (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → decCons l d b cp ─[ ev (evl (evLabel X e a)) ]─► M → ApiHasLink l e
decCons-ev-link l d b cp0 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlCS
decCons-ev-link l d b cp1 step with prefix-ev-lab step
... | _ , refl = ahlCS
decCons-ev-link l d b cp2 step with output-ev-lab step
... | refl = ahlBF
decCons-ev-link l d b cp3 step with prefix-ev-lab step
... | _ , refl = ahlBF
decCons-ev-link l d b cp4 step with output-ev-lab step
... | refl = ahlBF
decCons-ev-link l d b cp5 step with ⟶₀-ev-inv step
... | _ , refl , _ = ahlCS
decCons-ev-link l d b cp6 step = ⊥-elim (ret-no-ev {P = decCons l d b cp6} refl step)

-- node-D consume-driver link-pinning (`decCons … >> Skip`): fire through the
-- bind, pin the inner consume event's link
decConsD-ev-link : (l : Link) (cph : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l cph ─[ ev (evl (evLabel X e a)) ]─► M → ApiHasLink l e
decConsD-ev-link l (consD b cp0) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp0) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp0 sc
decConsD-ev-link l (consD b cp1) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp1) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp1 sc
decConsD-ev-link l (consD b cp2) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp2) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp2 sc
decConsD-ev-link l (consD b cp3) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp3) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp3 sc
decConsD-ev-link l (consD b cp4) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp4) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp4 sc
decConsD-ev-link l (consD b cp5) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp5) refl step
... | _ , sc , refl = decCons-ev-link l hi b cp5 sc
decConsD-ev-link l (consD b cp6) step = ⊥-elim (ret-no-ev {P = decConsD l (consD b cp6)} refl step)

-- relay-driver link-pinning (`consume l₁ hi >>= produce l₂ hi`): consuming pins
-- `l₁`; the cp6 handoff + producing leg pin `l₂` (reusing `decProd-ev-link`)
decCP-ev-link : (l₁ l₂ : Link) (ph : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ ph ─[ ev (evl (evLabel X e a)) ]─► M
  → ApiHasLink l₁ e ⊎ ApiHasLink l₂ e
decCP-ev-link l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp0 sc)
decCP-ev-link l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp1 sc)
decCP-ev-link l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp2 sc)
decCP-ev-link l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp3 sc)
decCP-ev-link l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp4 sc)
decCP-ev-link l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl = inj₁ (decCons-ev-link l₁ hi b cp5 sc)
decCP-ev-link l₁ l₂ (consuming b cp6) step = inj₂ (decProd-ev-link l₂ hi b pp0 (step-fcong refl step))
decCP-ev-link l₁ l₂ (producing b pp) step = inj₂ (decProd-ev-link l₂ hi b pp step)


------------------------------------------------------------------------
-- GAP-B LEAF 1 — abstract-bundle idle-LINK sibling non-offers.  An idle
-- same-protocol abstract bundle at a DIFFERENT link l never offers the driven
-- peer's event (which carries the driven link cl ≢ l): every firing
-- clause of the abstract `nxt` table guards on `l′ ≟ l`, so a wrong-link
-- event falls to the per-table catch-all `nothing`.  SCRIPT-GENERATED
-- (`.superpowers/sdd/gen-l4-link.py`).
------------------------------------------------------------------------
-- csSnxt-link-no: a wrong-link CS-image event (csEvLink e₁ ≢ l)
-- has no csSnxt table edge (every firing clause guards on l′ ≟ l)
csSnxt-link-no : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvLink e₁ ≢ l → NS.csSnxt l d q (X , ιCS e₁) a ≡ nothing
csSnxt-link-no l d NS.csIdle (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d NS.csIdle (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' reqCSRequestNext) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csAreq (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csAreq (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSAwaitReply) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRollForward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRollBackward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csCanAwait (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-link-no l d (NS.csAfi _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d (NS.csAfi _) (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSIntersectFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csInt (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csDdone (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csDdone (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csDdone (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d NS.csDdone (CS.doneCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csMust (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSRollForward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSRollBackward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-link-no l d NS.csMust (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWrf _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d (NS.csWrf _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWrf _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d (NS.csWrf _) (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWrb _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d (NS.csWrb _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWrb _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d (NS.csWrb _) (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csWar (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d NS.csWar (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csWar (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d NS.csWar (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWif _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d (NS.csWif _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWif _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d (NS.csWif _) (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWin _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-link-no l d (NS.csWin _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d (NS.csWin _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d (NS.csWin _) (CS.doneCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csTerm (CS.sendCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csTerm (CS.receiveCS l' d') ¬eq = refl
csSnxt-link-no l d NS.csTerm (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-link-no l d NS.csTerm (CS.doneCS l' d') ¬eq = refl

-- csCnxt-link-no: a wrong-link CS-image event (csEvLink e₁ ≢ l)
-- has no csCnxt table edge (every firing clause guards on l′ ≟ l)
csCnxt-link-no : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvLink e₁ ≢ l → NS.csCnxt l d q (X , ιCS e₁) a ≡ nothing
csCnxt-link-no l d NS.ccIdle (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRequestNext) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSFindIntersect) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-link-no l d NS.ccIdle (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccWreq (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccWreq (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccWreq (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccWreq (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccAwait (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccWfi _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d (NS.ccWfi _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccWfi _) (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d (NS.ccWfi _) (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccInt (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccWdone (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccWdone (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccWdone (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccWdone (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccMust (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSRollforward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccArf _) (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSRollback) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccArb _) (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccAif _) (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-link-no l d (NS.ccAin _) (CS.doneCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccTerm (CS.sendCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccTerm (CS.receiveCS l' d') ¬eq = refl
csCnxt-link-no l d NS.ccTerm (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-link-no l d NS.ccTerm (CS.doneCS l' d') ¬eq = refl

-- bfCnxt-link-no: a wrong-link BF-image event (bfEvLink e₁ ≢ l)
-- has no bfCnxt table edge (every firing clause guards on l′ ≟ l)
bfCnxt-link-no : (l : Link) (d : Dir) (q : NS.BFcPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvLink e₁ ≢ l → NS.bfCnxt l d q (X , ιBF e₁) a ≡ nothing
bfCnxt-link-no l d NS.bcIdle (BF.sendBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.receiveBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFRequestRange) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFClientDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfCnxt-link-no l d NS.bcIdle (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d (NS.bcWrr _) (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d (NS.bcWrr _) (BF.receiveBF l' d') ¬eq = refl
bfCnxt-link-no l d (NS.bcWrr _) (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-link-no l d (NS.bcWrr _) (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.sendBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-link-no l d NS.bcBusy (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcWcd (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcWcd (BF.receiveBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcWcd (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-link-no l d NS.bcWcd (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.sendBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-link-no l d NS.bcStream (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.sendBF l' d') ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.receiveBF l' d') ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' recvBFBlock) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfCnxt-link-no l d (NS.bcAblk _) (BF.doneBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcTerm (BF.sendBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcTerm (BF.receiveBF l' d') ¬eq = refl
bfCnxt-link-no l d NS.bcTerm (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-link-no l d NS.bcTerm (BF.doneBF l' d') ¬eq = refl

-- bfSnxt-link-no: a wrong-link BF-image event (bfEvLink e₁ ≢ l)
-- has no bfSnxt table edge (every firing clause guards on l′ ≟ l)
bfSnxt-link-no : (l : Link) (d : Dir) (q : NS.BFsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvLink e₁ ≢ l → NS.bfSnxt l d q (X , ιBF e₁) a ≡ nothing
bfSnxt-link-no l d NS.bsIdle (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsIdle (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.apiBFev l' d' reqBFRange) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d (NS.bsAreq _) (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFStartBatch) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFNoBlocks) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfSnxt-link-no l d NS.bsBusy (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsDdone (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsDdone (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsDdone (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsDdone (BF.doneBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsWsb (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsWsb (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsWsb (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsWsb (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFBlock) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' sendBFBatchDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfSnxt-link-no l d NS.bsStream (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsWnb (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsWnb (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsWnb (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsWnb (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d (NS.bsWblk _) (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d (NS.bsWblk _) (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d (NS.bsWblk _) (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d (NS.bsWblk _) (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsWbd (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = ⊥-elim (¬eq refl)
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-link-no l d NS.bsWbd (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsWbd (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsWbd (BF.doneBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsTerm (BF.sendBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsTerm (BF.receiveBF l' d') ¬eq = refl
bfSnxt-link-no l d NS.bsTerm (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-link-no l d NS.bsTerm (BF.doneBF l' d') ¬eq = refl

-- absCSs-link-noBoth: an idle same-protocol bundle at a DIFFERENT link does
-- not fire the driven peer's event (which is on link cl ≢ l) (via csSnxt-link-no)
absCSs-link-noBoth : (l : Link) (sv : Dir) (q : CSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvLink e₁ ≢ l → ¬ IoOffers (absCSs l sv q) (ιCS e₁) a
absCSs-link-noBoth l sv q e₁ {a} ¬l with NS.csSfin (coarsenCSs q) in fEq
... | true  = viewV→noOffer (absCSs l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csSfin ; nxt = NS.csSnxt l sv })
                   (coarsenCSs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSs l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csSfin ; nxt = NS.csSnxt l sv })
                   (coarsenCSs q) {e = ιCS e₁} {a = a} fEq (csSnxt-link-no l sv (coarsenCSs q) e₁ {a = a} ¬l))

-- absCSc-link-noBoth: an idle same-protocol bundle at a DIFFERENT link does
-- not fire the driven peer's event (which is on link cl ≢ l) (via csCnxt-link-no)
absCSc-link-noBoth : (l : Link) (sv : Dir) (q : CScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvLink e₁ ≢ l → ¬ IoOffers (absCSc l sv q) (ιCS e₁) a
absCSc-link-noBoth l sv q e₁ {a} ¬l with NS.csCfin (coarsenCSc q) in fEq
... | true  = viewV→noOffer (absCSc l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csCfin ; nxt = NS.csCnxt l sv })
                   (coarsenCSc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSc l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csCfin ; nxt = NS.csCnxt l sv })
                   (coarsenCSc q) {e = ιCS e₁} {a = a} fEq (csCnxt-link-no l sv (coarsenCSc q) e₁ {a = a} ¬l))

-- absBFc-link-noBoth: an idle same-protocol bundle at a DIFFERENT link does
-- not fire the driven peer's event (which is on link cl ≢ l) (via bfCnxt-link-no)
absBFc-link-noBoth : (l : Link) (sv : Dir) (q : BFcPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvLink e₁ ≢ l → ¬ IoOffers (absBFc l sv q) (ιBF e₁) a
absBFc-link-noBoth l sv q e₁ {a} ¬l with NS.bfCfin (coarsenBFc q) in fEq
... | true  = viewV→noOffer (absBFc l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l sv })
                   (coarsenBFc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFc l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l sv })
                   (coarsenBFc q) {e = ιBF e₁} {a = a} fEq (bfCnxt-link-no l sv (coarsenBFc q) e₁ {a = a} ¬l))

-- absBFs-link-noBoth: an idle same-protocol bundle at a DIFFERENT link does
-- not fire the driven peer's event (which is on link cl ≢ l) (via bfSnxt-link-no)
absBFs-link-noBoth : (l : Link) (sv : Dir) (q : BFsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvLink e₁ ≢ l → ¬ IoOffers (absBFs l sv q) (ιBF e₁) a
absBFs-link-noBoth l sv q e₁ {a} ¬l with NS.bfSfin (coarsenBFs q) in fEq
... | true  = viewV→noOffer (absBFs l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l sv })
                   (coarsenBFs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFs l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l sv })
                   (coarsenBFs q) {e = ιBF e₁} {a = a} fEq (bfSnxt-link-no l sv (coarsenBFs q) e₁ {a = a} ¬l))



------------------------------------------------------------------------
-- GAP-B LEAF 2 — driver io-non-offer.  The produce/consume/relay drivers
-- fire ONLY apiCS/apiBF events (their phases are api prefixes/outputs), never
-- an io `input`/`output`.  We first pin the fired head as apiCS-or-apiBF
-- (`IsApiCSBF`, a textual mirror of the `*-ev-link` link-pinnings), then a
-- non-apiCSBF (io) event refutes any driver offer — the `¬ IoOffers driver`
-- side of the node's `∥⇘apiES⇙` io-solo peel.
------------------------------------------------------------------------

-- witness that a Net_Api event is an api CS/BF event (the only kinds a driver fires)
data IsApiCSBF : {X : Set 0ℓ} → Net_Api Payload X → Set₁ where
  aicCS   : ∀ {l d m}  → IsApiCSBF (apiCS l d m)
  aicBF   : ∀ {l d m}  → IsApiCSBF (apiBF l d m)
  aicDone : ∀ {l d ch} → IsApiCSBF (done  l d ch)   -- driver receives the CS server's api done callback

-- produce-driver fires an api CS/BF head (mirror of decProd-ev-link)
decProd-apiCSBF : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decProd l d blk pp ─[ ev (evl (evLabel X e a)) ]─► M → IsApiCSBF e
decProd-apiCSBF l d blk pp0 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicCS
decProd-apiCSBF l d blk pp1 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicCS
decProd-apiCSBF l d blk pp2 step with output-ev-lab step
... | refl = aicCS
decProd-apiCSBF l d blk pp3 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicBF
decProd-apiCSBF l d blk pp4 step with output-ev-lab step
... | refl = aicBF
decProd-apiCSBF l d blk pp5 step with output-ev-lab step
... | refl = aicBF
decProd-apiCSBF l d blk pp6 step with output-ev-lab step
... | refl = aicBF
decProd-apiCSBF l d blk pp7 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicDone
decProd-apiCSBF l d blk pp8 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicDone
decProd-apiCSBF l d blk pp9 step = ⊥-elim (ret-no-ev {P = decProd l d blk pp9} refl step)

-- consume-driver fires an api CS/BF head (mirror of decCons-ev-link)
decCons-apiCSBF : (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → decCons l d b cp ─[ ev (evl (evLabel X e a)) ]─► M → IsApiCSBF e
decCons-apiCSBF l d b cp0 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicCS
decCons-apiCSBF l d b cp1 step with prefix-ev-lab step
... | _ , refl = aicCS
decCons-apiCSBF l d b cp2 step with output-ev-lab step
... | refl = aicBF
decCons-apiCSBF l d b cp3 step with prefix-ev-lab step
... | _ , refl = aicBF
decCons-apiCSBF l d b cp4 step with output-ev-lab step
... | refl = aicBF
decCons-apiCSBF l d b cp5 step with ⟶₀-ev-inv step
... | _ , refl , _ = aicCS
decCons-apiCSBF l d b cp6 step = ⊥-elim (ret-no-ev {P = decCons l d b cp6} refl step)

-- node-D consume-driver fires an api CS/BF head (mirror of decConsD-ev-link)
decConsD-apiCSBF : (l : Link) (cph : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l cph ─[ ev (evl (evLabel X e a)) ]─► M → IsApiCSBF e
decConsD-apiCSBF l (consD b cp0) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp0) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp0 sc
decConsD-apiCSBF l (consD b cp1) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp1) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp1 sc
decConsD-apiCSBF l (consD b cp2) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp2) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp2 sc
decConsD-apiCSBF l (consD b cp3) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp3) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp3 sc
decConsD-apiCSBF l (consD b cp4) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp4) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp4 sc
decConsD-apiCSBF l (consD b cp5) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp5) refl step
... | _ , sc , refl = decCons-apiCSBF l hi b cp5 sc
decConsD-apiCSBF l (consD b cp6) step = ⊥-elim (ret-no-ev {P = decConsD l (consD b cp6)} refl step)

-- relay-driver fires an api CS/BF head on one of its two links (mirror of decCP-ev-link)
decCP-apiCSBF : (l₁ l₂ : Link) (ph : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ ph ─[ ev (evl (evLabel X e a)) ]─► M → IsApiCSBF e
decCP-apiCSBF l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp0 sc
decCP-apiCSBF l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp1 sc
decCP-apiCSBF l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp2 sc
decCP-apiCSBF l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp3 sc
decCP-apiCSBF l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp4 sc
decCP-apiCSBF l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl = decCons-apiCSBF l₁ hi b cp5 sc
decCP-apiCSBF l₁ l₂ (consuming b cp6) step = decProd-apiCSBF l₂ hi b pp0 (step-fcong refl step)
decCP-apiCSBF l₁ l₂ (producing b pp) step = decProd-apiCSBF l₂ hi b pp step

-- driver io-non-offer: a non-apiCSBF (io) event has no produce-driver offer
decProd-io-no : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ¬ IsApiCSBF e → ¬ IoOffers (decProd l d blk pp) e a
decProd-io-no l d blk pp ¬api (_ , step) = ¬api (decProd-apiCSBF l d blk pp step)

-- driver io-non-offer: node-D consume driver
decConsD-io-no : (l : Link) (cph : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ¬ IsApiCSBF e → ¬ IoOffers (decConsD l cph) e a
decConsD-io-no l cph ¬api (_ , step) = ¬api (decConsD-apiCSBF l cph step)

-- driver io-non-offer: relay driver
decCP-io-no : (l₁ l₂ : Link) (ph : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ¬ IsApiCSBF e → ¬ IoOffers (decCP l₁ l₂ ph) e a
decCP-io-no l₁ l₂ ph ¬api (_ , step) = ¬api (decCP-apiCSBF l₁ l₂ ph step)


------------------------------------------------------------------------
-- GAP-B LEAF 1b — whole abstract-bundle idle-LINK non-offer.  An entire idle
-- `absBundleG` at link `l` offers NOTHING on a driven peer's event that lives
-- on a DIFFERENT link (`{cs,bf}EvLink e₁ ≢ l`): the same-protocol CS/BF peers
-- are refuted by the LINK leaf (LEAF 1 `abs*-link-noBoth`), the cross-protocol
-- KA/TS + opposite-protocol siblings by the committed `*-no{CS,BF}` leaves.
-- Composed over the eight `⦀` peers via `SStep.⦀-noOffer`.  This is the idle
-- sibling non-offer the node's two-link abstract `⦀-ev-L/R` reassembly needs.
------------------------------------------------------------------------

-- CS-image case: the whole idle bundle at `l` offers nothing on `ιCS e₁` (link ≢ l)
absBundleG-CS-link-noIoOffer : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvLink e₁ ≢ l → ¬ IoOffers (absBundleG l cl sv qcc qcs qbc qbs ip) (ιCS e₁) a
absBundleG-CS-link-noIoOffer l cl sv qcc qcs qbc qbs ip e₁ ¬l =
  SStep.⦀-noOffer (absKAc l cl (kac ip)) _ (absKAc-noCS l cl (kac ip) e₁)
   (SStep.⦀-noOffer (absKAs l sv (kas ip)) _ (absKAs-noCS l sv (kas ip) e₁)
    (SStep.⦀-noOffer (absCSc l cl qcc) _ (absCSc-link-noBoth l cl qcc e₁ ¬l)
     (SStep.⦀-noOffer (absCSs l sv qcs) _ (absCSs-link-noBoth l sv qcs e₁ ¬l)
      (SStep.⦀-noOffer (absBFc l cl qbc) _ (absBFc-noCS l cl qbc e₁)
       (SStep.⦀-noOffer (absBFs l sv qbs) _ (absBFs-noCS l sv qbs e₁)
        (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noCS l cl (tsc ip) e₁)
          (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noCS l sv (tss ip) e₁)
            (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noCS l cl (lnc ip) e₁)
              (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noCS l sv (lns ip) e₁)
                (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
                  (absLFc-noCS l cl (lfc ip) e₁) (absLFs-noCS l sv (lfs ip) e₁)))))))))))

-- BF-image case: the whole idle bundle at `l` offers nothing on `ιBF e₁` (link ≢ l)
absBundleG-BF-link-noIoOffer : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvLink e₁ ≢ l → ¬ IoOffers (absBundleG l cl sv qcc qcs qbc qbs ip) (ιBF e₁) a
absBundleG-BF-link-noIoOffer l cl sv qcc qcs qbc qbs ip e₁ ¬l =
  SStep.⦀-noOffer (absKAc l cl (kac ip)) _ (absKAc-noBF l cl (kac ip) e₁)
   (SStep.⦀-noOffer (absKAs l sv (kas ip)) _ (absKAs-noBF l sv (kas ip) e₁)
    (SStep.⦀-noOffer (absCSc l cl qcc) _ (absCSc-noBF l cl qcc e₁)
     (SStep.⦀-noOffer (absCSs l sv qcs) _ (absCSs-noBF l sv qcs e₁)
      (SStep.⦀-noOffer (absBFc l cl qbc) _ (absBFc-link-noBoth l cl qbc e₁ ¬l)
       (SStep.⦀-noOffer (absBFs l sv qbs) _ (absBFs-link-noBoth l sv qbs e₁ ¬l)
        (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁)
          (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁)
            (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁)
              (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁)
                (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
                  (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁)))))))))))


------------------------------------------------------------------------
-- GAP-B — node-A visible api-event inversion.  A node `= (bundleA linkAB ⦀
-- bundleA linkAC) ∥⇘apiES⇙ (decProd linkAB ⦀ decProd linkAC)`.  An api event
-- (∈ apiES) is a driver↔peer SYNC (`SStep.reflect-node-api`); the driver `⦀`
-- pins the firing link (evBoth by `apiLink-inj`+`linkAB≢linkAC`) and, via
-- `decProd-apiCSBF`, the protocol; the bundle `⦀` is aligned to the same link
-- and inverted by `bundle-{CS,BF}-ev-inv`; the driver phase by `decProd-ev-inv`.
-- The abstract node redoes the SAME sync (shared drivers; abstract bundle step
-- from the inversion; idle-link non-offer from `absBundleG-*-link-noIoOffer`).
-- Per-firing-link helpers (`nodeA-AB`/`nodeA-AC`) split protocol via FUNCTION
-- clauses so the deep bundle-peel `with`s never need ellipsis-popping.
------------------------------------------------------------------------

-- node-A visible-event result: the successor node-state + concrete/abstract match
data NodeAEvR (na : SN.NodeStateA) {X : Set 0ℓ} (e : Net_Api Payload X) (a : X)
              (A′ : NetProc) : Set₁ where
  naEv : (na′ : SN.NodeStateA) → A′ ≡ decNodeA na′
       → absNodeA na ─[ ev (evl (evLabel X e a)) ]─► absNodeA na′
       → NodeAEvR na e a A′

-- distinct node-A links (Fin 4 literals)
linkAB≢linkAC : ¬ (linkAB ≡ linkAC)
linkAB≢linkAC ()

-- driver on linkAC offers nothing on a linkAB-pinned api event (reuse apiLink-inj)
nodeA-drvAC-no : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ApiHasLink linkAB e → ¬ IoOffers (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) e a
nodeA-drvAC-no na ahl (_ , s) =
  linkAB≢linkAC (sym (apiLink-inj (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) s) ahl))

-- driver on linkAB offers nothing on a linkAC-pinned api event
nodeA-drvAB-no : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ApiHasLink linkAC e → ¬ IoOffers (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) e a
nodeA-drvAB-no na ahl (_ , s) =
  linkAB≢linkAC (apiLink-inj (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) s) ahl)

-- `produce` fires a `done` event ONLY at pp7 (ChainSync done-receipt, → pp8) and
-- pp8 (BlockFetch done-receipt, → pp9 = Skip): it pins the event to
-- `done l d N2N_ChainSync` / `done l d N2N_BlockFetch` and the target phase.  Used
-- by the `aicDone` co-move to reconstruct the driver leg + pin the event's protocol.
decProd-done-inv : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {a : ⊤U} {d₀ : Dir} {ch : IDs} {M : NetProc}
  → decProd l d blk pp ─[ ev (evl (evLabel ⊤U (done l d₀ ch) a)) ]─► M
  → (d₀ ≡ d) × ( (ch ≡ N2N_ChainSync  × M ≡ decProd l d blk pp8)
              ⊎ (ch ≡ N2N_BlockFetch × M ≡ decProd l d blk pp9) )
decProd-done-inv l d blk pp0 step with ⟶₀-ev-inv step
... | _ , () , _
decProd-done-inv l d blk pp1 step with ⟶₀-ev-inv step
... | _ , () , _
decProd-done-inv l d blk pp2 step with output-ev-lab step
... | ()
decProd-done-inv l d blk pp3 step with ⟶₀-ev-inv step
... | _ , () , _
decProd-done-inv l d blk pp4 step with output-ev-lab step
... | ()
decProd-done-inv l d blk pp5 step with output-ev-lab step
... | ()
decProd-done-inv l d blk pp6 step with output-ev-lab step
... | ()
decProd-done-inv l d blk pp7 step with ⟶₀-ev-inv step
... | _ , refl , refl = refl , inj₁ (refl , refl)
decProd-done-inv l d blk pp8 step with ⟶₀-ev-inv step
... | _ , refl , refl = refl , inj₂ (refl , refl)
decProd-done-inv l d blk pp9 step = ⊥-elim (ret-no-ev {P = decProd l d blk pp9} refl step)

-- firing link = linkAB, protocol determined by `IsApiCSBF`/`ApiHasLink`
nodeA-AB : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {B₁ D₁AB : NetProc}
  → apiES .mem (X , e) a
  → (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
     ⦀ bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ─[ ev (evl (evLabel X e a)) ]─► D₁AB
  → IsApiCSBF e → ApiHasLink linkAB e
  → NodeAEvR na e a (B₁ ∥⇘ apiES ⇙ (D₁AB ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
nodeA-AB na {X} {a = a} mem bStep sDAB aicCS (ahlCS {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.apiCSev linkAB d m} sBAB)
                     (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.apiCSev linkAB d m} sBAC)))
... | PEA.evR _ sBAC = ⊥-elim (linkAB≢linkAC (sym
        (apiLink-inj (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.apiCSev linkAB d m} sBAC) ahlCS)))
... | PEA.evL _ sBAB
    with bundle-CS-ev-inv linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.apiCSev linkAB d m} sBAB
       | decProd-ev-inv linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB
...   | bcscE csc′ refl aStepAB | peR pp′ refl =
        naEv (SN.mkNodeA csc′ (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (CS.apiCSev linkAB d m) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na ahlCS))))
...   | bcssE css′ refl aStepAB | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) css′ (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (CS.apiCSev linkAB d m) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na ahlCS))))
nodeA-AB na {X} {a = a} mem bStep sDAB aicBF (ahlBF {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.apiBFev linkAB d m} sBAB)
                     (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.apiBFev linkAB d m} sBAC)))
... | PEA.evR _ sBAC = ⊥-elim (linkAB≢linkAC (sym
        (apiLink-inj (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.apiBFev linkAB d m} sBAC) ahlBF)))
... | PEA.evL _ sBAB
    with bundle-BF-ev-inv linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.apiBFev linkAB d m} sBAB
       | decProd-ev-inv linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB
...   | bcbcE bfc′ refl aStepAB | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) bfc′ (SN.NodeStateA.bfS-AB na) pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (BF.apiBFev linkAB d m) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na ahlBF))))
...   | bcbsE bfs′ refl aStepAB | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) bfs′ pp′ (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (BF.apiBFev linkAB d m) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na ahlBF))))
-- linkAB `done` (ChainSync): the CS SERVER fires doneCS, synced with the produce driver's pp7 done-receipt
nodeA-AB na {X} {a = a} mem bStep sDAB aicDone (ahlDone {d} {ch})
  with decProd-done-inv linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB
nodeA-AB na {X} {a = a} mem bStep sDAB aicDone (ahlDone {d} {ch}) | refl , inj₁ (refl , refl)
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.doneCS linkAB hi} sBAB)
                     (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.doneCS linkAB hi} sBAC)))
... | PEA.evR _ sBAC = ⊥-elim (linkAB≢linkAC (sym
        (apiLink-inj (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.doneCS linkAB hi} sBAC) (ahlDone {d = hi} {ch = N2N_ChainSync}))))
... | PEA.evL _ sBAB
    with bundle-CS-ev-inv linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.doneCS linkAB hi} sBAB
...   | bcscE csc′ refl aStepAB =
        naEv (SN.mkNodeA csc′ (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) pp8 (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (CS.doneCS linkAB hi) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na (ahlDone {d = hi} {ch = N2N_ChainSync})))))
...   | bcssE css′ refl aStepAB =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) css′ (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) pp8 (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (CS.doneCS linkAB hi) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na (ahlDone {d = hi} {ch = N2N_ChainSync})))))
-- linkAB `done` (BlockFetch): the BF SERVER fires doneBF, synced with the produce driver's pp8 done-receipt
nodeA-AB na {X} {a = a} mem bStep sDAB aicDone (ahlDone {d} {ch}) | refl , inj₂ (refl , refl)
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.doneBF linkAB hi} sBAB)
                     (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.doneBF linkAB hi} sBAC)))
... | PEA.evR _ sBAC = ⊥-elim (linkAB≢linkAC (sym
        (apiLink-inj (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.doneBF linkAB hi} sBAC) (ahlDone {d = hi} {ch = N2N_BlockFetch}))))
... | PEA.evL _ sBAB
    with bundle-BF-ev-inv linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.doneBF linkAB hi} sBAB
...   | bcbcE bfc′ refl aStepAB =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) bfc′ (SN.NodeStateA.bfS-AB na) pp9 (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (BF.doneBF linkAB hi) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na (ahlDone {d = hi} {ch = N2N_BlockFetch})))))
...   | bcbsE bfs′ refl aStepAB =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) bfs′ pp9 (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-L (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _
               aStepAB
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) (BF.doneBF linkAB hi) linkAB≢linkAC)))
            (SStep.⦀-ev-L (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ sDAB
               (noOffer→viewV _ (nodeA-drvAC-no na (ahlDone {d = hi} {ch = N2N_BlockFetch})))))

-- firing link = linkAC (mirror of nodeA-AB via `⦀-ev-R`)
nodeA-AC : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {B₁ D₁AC : NetProc}
  → apiES .mem (X , e) a
  → (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
     ⦀ bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
      ─[ ev (evl (evLabel X e a)) ]─► B₁
  → decProd linkAC hi blkA (SN.NodeStateA.prod-AC na) ─[ ev (evl (evLabel X e a)) ]─► D₁AC
  → IsApiCSBF e → ApiHasLink linkAC e
  → NodeAEvR na e a (B₁ ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ D₁AC))
nodeA-AC na {X} {a = a} mem bStep sDAC aicCS (ahlCS {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.apiCSev linkAC d m} sBAB)
                     (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.apiCSev linkAC d m} sBAC)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.apiCSev linkAC d m} sBAB) ahlCS))
... | PEA.evR _ sBAC
    with bundle-CS-ev-inv linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.apiCSev linkAC d m} sBAC
       | decProd-ev-inv linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC
...   | bcscE csc′ refl aStepAC | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) pp′ (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (CS.apiCSev linkAC d m) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na ahlCS))))
...   | bcssE css′ refl aStepAC | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) css′ (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) pp′ (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (CS.apiCSev linkAC d m) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na ahlCS))))
nodeA-AC na {X} {a = a} mem bStep sDAC aicBF (ahlBF {d} {m})
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.apiBFev linkAC d m} sBAB)
                     (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.apiBFev linkAC d m} sBAC)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.apiBFev linkAC d m} sBAB) ahlBF))
... | PEA.evR _ sBAC
    with bundle-BF-ev-inv linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.apiBFev linkAC d m} sBAC
       | decProd-ev-inv linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC
...   | bcbcE bfc′ refl aStepAC | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) bfc′ (SN.NodeStateA.bfS-AC na) pp′ (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (BF.apiBFev linkAC d m) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na ahlBF))))
...   | bcbsE bfs′ refl aStepAC | peR pp′ refl =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) bfs′ pp′ (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (BF.apiBFev linkAC d m) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na ahlBF))))
-- linkAC `done` (ChainSync): mirror of the linkAB done co-move via `⦀-ev-R`
nodeA-AC na {X} {a = a} mem bStep sDAC aicDone (ahlDone {d} {ch})
  with decProd-done-inv linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC
nodeA-AC na {X} {a = a} mem bStep sDAC aicDone (ahlDone {d} {ch}) | refl , inj₁ (refl , refl)
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.doneCS linkAC hi} sBAB)
                     (bundleCS-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.doneCS linkAC hi} sBAC)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleCS-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = CS.doneCS linkAC hi} sBAB) (ahlDone {d = hi} {ch = N2N_ChainSync})))
... | PEA.evR _ sBAC
    with bundle-CS-ev-inv linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = CS.doneCS linkAC hi} sBAC
...   | bcscE csc′ refl aStepAC =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) csc′ (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) pp8 (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (CS.doneCS linkAC hi) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na (ahlDone {d = hi} {ch = N2N_ChainSync})))))
...   | bcssE css′ refl aStepAC =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) css′ (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) pp8 (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-CS-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (CS.doneCS linkAC hi) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na (ahlDone {d = hi} {ch = N2N_ChainSync})))))
-- linkAC `done` (BlockFetch): the BF SERVER fires doneBF, synced with the produce driver's pp8 done-receipt
nodeA-AC na {X} {a = a} mem bStep sDAC aicDone (ahlDone {d} {ch}) | refl , inj₂ (refl , refl)
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na))
         (bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na)) bStep
... | PEA.evSync () _ _
... | PEA.evBoth _ sBAB sBAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.doneBF linkAC hi} sBAB)
                     (bundleBF-ev-link linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.doneBF linkAC hi} sBAC)))
... | PEA.evL _ sBAB = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (bundleBF-ev-link linkAB lo hi (λ ()) (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) {e₁ = BF.doneBF linkAC hi} sBAB) (ahlDone {d = hi} {ch = N2N_BlockFetch})))
... | PEA.evR _ sBAC
    with bundle-BF-ev-inv linkAC lo hi (λ ()) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) {e₁ = BF.doneBF linkAC hi} sBAC
...   | bcbcE bfc′ refl aStepAC =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) bfc′ (SN.NodeStateA.bfS-AC na) pp9 (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (BF.doneBF linkAC hi) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na (ahlDone {d = hi} {ch = N2N_BlockFetch})))))
...   | bcbsE bfs′ refl aStepAC =
        naEv (SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na) (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) bfs′ pp9 (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na)) refl
          (SStep.∥⇘⇙-ev-sync apiES _ _ mem
            (SStep.⦀-ev-R _ (absBundleG linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
               aStepAC
               (noOffer→viewV _ (absBundleG-BF-link-noIoOffer linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) (BF.doneBF linkAC hi) (λ q → linkAB≢linkAC (sym q)))))
            (SStep.⦀-ev-R _ (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) sDAC
               (noOffer→viewV _ (nodeA-drvAB-no na (ahlDone {d = hi} {ch = N2N_BlockFetch})))))

-- node-A api inversion: reflect the driver↔peer sync, peel the driver `⦀`, dispatch
nodeA-ev-api : (na : SN.NodeStateA) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {A′ : NetProc}
  → apiES .mem (X , e) a
  → decNodeA na ─[ ev (evl (evLabel X e a)) ]─► A′
  → NodeAEvR na e a A′
nodeA-ev-api na {X} {e} {a} mem step
  with SStep.reflect-node-api
         (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)
          ⦀ bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
         (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na))
         mem step
... | SStep.apiSync B₁ D₁ bStep dStep refl
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt)
           (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) dStep
... | PEA.evSync () _ _
... | PEA.evL _ sDAB =
        nodeA-AB na mem bStep sDAB
          (decProd-apiCSBF linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB)
          (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB)
... | PEA.evR _ sDAC =
        nodeA-AC na mem bStep sDAC
          (decProd-apiCSBF linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC)
          (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC)
... | PEA.evBoth _ sDAB sDAC = ⊥-elim (linkAB≢linkAC
        (apiLink-inj (decProd-ev-link linkAB hi blkA (SN.NodeStateA.prod-AB na) sDAB)
                     (decProd-ev-link linkAC hi blkA (SN.NodeStateA.prod-AC na) sDAC)))


------------------------------------------------------------------------
-- ITEM-4 (io routing) — the generic `bundle-io-inv` DISPATCHER.
-- Routes a bundle io step `bundleG … ─[ev(io)]─► Bd′` to the firing
-- protocol's `bundle-X-ev-inv` (all 6 channels CS/BF/KA/TS/LN/LF now built),
-- repackaging each per-channel `BundleXEvR` into the unified `BundleIoR`.
-- Non-io Net_Api events are excluded by the `ioES` membership witness (⊥).
------------------------------------------------------------------------

-- unified bundle io-inversion result: the io step advances one peer slot
data BundleIoR (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e : Net_Api Payload X) (a : X) (Bd′ : NetProc) : Set₁ where
  bio : (csc′ : CScPos) (css′ : CSsPos) (bfc′ : BFcPos) (bfs′ : BFsPos) (ip′ : InertPos)
      → Bd′ ≡ bundleG l cl sv csc′ css′ bfc′ bfs′ ip′
      → absBundleG l cl sv csc css bfc bfs ip
          ─[ ev (evl (evLabel X e a)) ]─► absBundleG l cl sv csc′ css′ bfc′ bfs′ ip′
      → BundleIoR l cl sv csc css bfc bfs ip e a Bd′

bundle-io-inv : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {Bd′ : NetProc}
  → ioES .mem (X , e) a
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X e a)) ]─► Bd′
  → BundleIoR l cl sv csc css bfc bfs ip e a Bd′
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_ChainSync} iomem step
  with bundle-CS-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.sendCS l′ d′} step
... | bcscE csc′ eq astep = bio csc′ css bfc bfs ip eq astep
... | bcssE css′ eq astep = bio csc css′ bfc bfs ip eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_ChainSync} iomem step
  with bundle-CS-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.receiveCS l′ d′} step
... | bcscE csc′ eq astep = bio csc′ css bfc bfs ip eq astep
... | bcssE css′ eq astep = bio csc css′ bfc bfs ip eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_BlockFetch} iomem step
  with bundle-BF-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.sendBF l′ d′} step
... | bcbcE bfc′ eq astep = bio csc css bfc′ bfs ip eq astep
... | bcbsE bfs′ eq astep = bio csc css bfc bfs′ ip eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_BlockFetch} iomem step
  with bundle-BF-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.receiveBF l′ d′} step
... | bcbcE bfc′ eq astep = bio csc css bfc′ bfs ip eq astep
... | bcbsE bfs′ eq astep = bio csc css bfc bfs′ ip eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_KeepAlive} iomem step
  with bundle-KA-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.sendKA l′ d′} step
... | bkacE kac′ eq astep = bio csc css bfc bfs (record ip { kac = kac′ }) eq astep
... | bkasE kas′ eq astep = bio csc css bfc bfs (record ip { kas = kas′ }) eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_KeepAlive} iomem step
  with bundle-KA-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.receiveKA l′ d′} step
... | bkacE kac′ eq astep = bio csc css bfc bfs (record ip { kac = kac′ }) eq astep
... | bkasE kas′ eq astep = bio csc css bfc bfs (record ip { kas = kas′ }) eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_TxSubmission} iomem step
  with bundle-TS-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.sendTS l′ d′} step
... | btscE tsc′ eq astep = bio csc css bfc bfs (record ip { tsc = tsc′ }) eq astep
... | btssE tss′ eq astep = bio csc css bfc bfs (record ip { tss = tss′ }) eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_TxSubmission} iomem step
  with bundle-TS-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.receiveTS l′ d′} step
... | btscE tsc′ eq astep = bio csc css bfc bfs (record ip { tsc = tsc′ }) eq astep
... | btssE tss′ eq astep = bio csc css bfc bfs (record ip { tss = tss′ }) eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_LeiosNotify} iomem step
  with bundle-LN-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = LNp.sendLN l′ d′} step
... | btlncE lnc′ eq astep = bio csc css bfc bfs (record ip { lnc = lnc′ }) eq astep
... | btlnsE lns′ eq astep = bio csc css bfc bfs (record ip { lns = lns′ }) eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosNotify} iomem step
  with bundle-LN-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = LNp.receiveLN l′ d′} step
... | btlncE lnc′ eq astep = bio csc css bfc bfs (record ip { lnc = lnc′ }) eq astep
... | btlnsE lns′ eq astep = bio csc css bfc bfs (record ip { lns = lns′ }) eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = input l′ d′ N2N_LeiosFetch} iomem step
  with bundle-LF-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = LFp.sendLF l′ d′} step
... | btlfcE lfc′ eq astep = bio csc css bfc bfs (record ip { lfc = lfc′ }) eq astep
... | btlfsE lfs′ eq astep = bio csc css bfc bfs (record ip { lfs = lfs′ }) eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = output l′ d′ N2N_LeiosFetch} iomem step
  with bundle-LF-ev-inv l cl sv cl≢sv csc css bfc bfs ip {e₁ = LFp.receiveLF l′ d′} step
... | btlfcE lfc′ eq astep = bio csc css bfc bfs (record ip { lfc = lfc′ }) eq astep
... | btlfsE lfs′ eq astep = bio csc css bfc bfs (record ip { lfs = lfs′ }) eq astep
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = done _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = apiCS _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = apiBF _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = apiKA _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = apiTS _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = apiLN _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = apiLF _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = sndmsg _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = rcvmsg _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = tx _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = sndack _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = rcvack _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = ack _ _ _} iomem step = ⊥-elim iomem
bundle-io-inv l cl sv cl≢sv csc css bfc bfs ip {e = break _} iomem step = ⊥-elim iomem

------------------------------------------------------------------------
-- ITEM-6 GROUNDWORK — node-level io peel bricks.  A node is
-- `(bundleG l₁ ⦀ bundleG l₂) ∥⇘ apiES ⇙ driver`; a delivered io `(e,a) ∈ ioES`
-- fires SOLO on ONE bundle: io ∉ apiES (`io⇒¬api`) rules out a driver↔bundle
-- sync, and the driver offers only api (`decProd/decCP/decConsD-io-no`), so the
-- `∥⇘apiES⇙` peel lands on the bundle.  The bundle-`⦀` `evBoth` overlap (BOTH
-- links firing the same io) is refuted by the io's OWN link: a CS/BF bundle io
-- step pins the io's link to the bundle's link (`bundle{CS,BF}-io-link-{in,out}`
-- via `bundle{CS,BF}-ev-link` + the `ApiHasLink` io inverters), and the two node
-- links are distinct.  (KA/TS/LN/LF link-pins + `nodeX-ev-io`/`top-nodes-io`
-- remain — see the report.)
------------------------------------------------------------------------

-- io membership excludes api membership (input/output ∉ apiES; api ∉ ioES)
io⇒¬api : {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a → ¬ apiES .mem (X , e) a
io⇒¬api {e = input  _ _ _} _ ()
io⇒¬api {e = output _ _ _} _ ()
io⇒¬api {e = sndmsg _ _ _} ()
io⇒¬api {e = rcvmsg _ _ _} ()
io⇒¬api {e = tx     _ _ _} ()
io⇒¬api {e = sndack _ _ _} ()
io⇒¬api {e = rcvack _ _ _} ()
io⇒¬api {e = ack    _ _ _} ()
io⇒¬api {e = done   _ _ _} ()
io⇒¬api {e = apiCS  _ _ _} ()
io⇒¬api {e = apiBF  _ _ _} ()
io⇒¬api {e = apiKA  _ _ _} ()
io⇒¬api {e = apiTS  _ _ _} ()
io⇒¬api {e = apiLN  _ _ _} ()
io⇒¬api {e = apiLF  _ _ _} ()
io⇒¬api {e = break  _}     ()

-- `ApiHasLink` at an `input`/`output` event pins the io's OWN link
ahlIn-link  : {l l′ : Link} {d : Dir} {ch : IDs} → ApiHasLink l (input  l′ d ch) → l ≡ l′
ahlIn-link  ahlIn  = refl
ahlOut-link : {l l′ : Link} {d : Dir} {ch : IDs} → ApiHasLink l (output l′ d ch) → l ≡ l′
ahlOut-link ahlOut = refl

-- a CS-channel `input` io step of a bundle pins the io's link to the bundle's
bundleCS-io-link-in : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (input l′ d′ N2N_ChainSync) a)) ]─► Bd′
  → l ≡ l′
bundleCS-io-link-in l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlIn-link (bundleCS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.sendCS l′ d′} step)

-- a CS-channel `output` io step of a bundle pins the io's link to the bundle's
bundleCS-io-link-out : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (output l′ d′ N2N_ChainSync) a)) ]─► Bd′
  → l ≡ l′
bundleCS-io-link-out l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlOut-link (bundleCS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = CS.receiveCS l′ d′} step)

-- a BF-channel `input` io step of a bundle pins the io's link to the bundle's
bundleBF-io-link-in : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (input l′ d′ N2N_BlockFetch) a)) ]─► Bd′
  → l ≡ l′
bundleBF-io-link-in l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlIn-link (bundleBF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.sendBF l′ d′} step)

-- a BF-channel `output` io step of a bundle pins the io's link to the bundle's
bundleBF-io-link-out : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (output l′ d′ N2N_BlockFetch) a)) ]─► Bd′
  → l ≡ l′
bundleBF-io-link-out l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlOut-link (bundleBF-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = BF.receiveBF l′ d′} step)

------------------------------------------------------------------------
-- ITEM-6 (io-peel) — KeepAlive channel bundle io-link pins.  Mirror of the
-- CS/BF link machinery (`csEvLink`/`decCSc-src-link`/`csc-ev-link`/
-- `bundleCS-ev-link`/`bundleCS-io-link-*`) for the KA peers: a bundleG KA-image
-- step pins the bundle's OWN link, so a KA wire io (input/output N2N_KeepAlive)
-- of a bundle pins the io's link to the bundle's link.  `decKAc/KAs-src-link`
-- are byte-copies of `decKAc/KAs-src-dir` returning `kaEvLink e₁ ≡ l`;
-- `bundleKA-ev-link` copies `bundle-KA-ev-inv`'s 12-peer peel, routing the two
-- KA peers to `kac/kas-ev-link` (link) instead of `finishKA*-ev`.
------------------------------------------------------------------------

-- the link component of a KeepAlive source event
kaEvLink : {X : Set 0ℓ} → KA.KAEv X → Link
kaEvLink (KA.sendKA l d)    = l
kaEvLink (KA.receiveKA l d) = l
kaEvLink (KA.apiKAev l d m) = l
kaEvLink (KA.doneKA l d)    = l

-- ιKA carries the source link into the Net_Api event
kaApiLink : {X : Set 0ℓ} (e₁ : KA.KAEv X) → ApiHasLink (kaEvLink e₁) (ιKA e₁)
kaApiLink (KA.sendKA l d)    = ahlIn
kaApiLink (KA.receiveKA l d) = ahlOut
kaApiLink (KA.apiKAev l d m) = ahlKA
kaApiLink (KA.doneKA l d)    = ahlDone

-- LINK: decKAc-src-link — a fine KA-client source step fires an event whose
-- link component is `l` (kaEvLink extracts it).
decKAc-src-link : (l : Link) (d : Dir) (pos : KAcPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : KAProc}
  → decKAc-src l d pos KAL.─[ KAL.ev (KAL.evl (KAL.evLabel X e₁ a)) ]─► P′
  → kaEvLink e₁ ≡ l
decKAc-src-link l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' sendKAMsg} {a} s with step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decKAc-src-link l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' sendKADone} {a} s with step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decKAc-src-link l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' errCookie}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-link l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' recvKACookie} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-link l d (kcHead KA.stClient) {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-link l d (kcHead KA.stClient) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-link l d (kcHead KA.stClient) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-link l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAliveResponse cr)} s with step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decKAc-src-link l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAlive c)} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-link l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive MsgKADone}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-link l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-link l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-link l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-link l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-link l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-link l d (kcHead (KA.stServer cq)) {e₁ = KA.sendKA l' d'}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-link l d (kcHead (KA.stServer cq)) {e₁ = KA.apiKAev l' d' m}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-link l d (kcHead (KA.stServer cq)) {e₁ = KA.doneKA l' d'}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-link l d (kcHead KA.stDone) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decKAc-src-link l d (kcErr1 cq cr ne) s = ⊥-elim (ne refl)
decKAc-src-link l d (kcReq1 c) {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decKAc-src-link l d (kcReq1 c) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
decKAc-src-link l d (kcReq1 c) {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
decKAc-src-link l d (kcReq1 c) {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
decKAc-src-link l d kcDone1 {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive MsgKADone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decKAc-src-link l d kcDone1 {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
decKAc-src-link l d kcDone1 {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
decKAc-src-link l d kcDone1 {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
decKAc-src-link l d (kcSil st) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decKAc-src-link l d kcTermE1 s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- LINK: decKAs-src-link — mirror for the KA-server positions
decKAs-src-link : (l : Link) (d : Dir) (pos : KAsPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : KAProc}
  → decKAs-src l d pos KAL.─[ KAL.ev (KAL.evl (KAL.evLabel X e₁ a)) ]─► P′
  → kaEvLink e₁ ≡ l
decKAs-src-link l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAlive c)} s with step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decKAs-src-link l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive MsgKADone} s with step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decKAs-src-link l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAliveResponse c)} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-link l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-link l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-link l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-link l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-link l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-link l d (ksHead KA.stClient) {e₁ = KA.sendKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-link l d (ksHead KA.stClient) {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-link l d (ksHead KA.stClient) {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-link l d (ksHead (KA.stServer c)) {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decKAs-src-link l d (ksHead (KA.stServer c)) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
decKAs-src-link l d (ksHead (KA.stServer c)) {e₁ = KA.apiKAev l' d' m} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
decKAs-src-link l d (ksHead (KA.stServer c)) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
decKAs-src-link l d (ksHead KA.stDone) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decKAs-src-link l d (ksRecv1 c) {e₁ = KA.apiKAev l' d' m} {a} s with step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s
... | offer with KA.KAEv-≟ (_ , KA.apiKAev l d recvKACookie) (_ , KA.apiKAev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decKAs-src-link l d (ksRecv1 c) {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
decKAs-src-link l d (ksRecv1 c) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
decKAs-src-link l d (ksRecv1 c) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
decKAs-src-link l d ksDdone1 {e₁ = KA.doneKA l' d'} {a} s with step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s
... | offer with KA.KAEv-≟ (_ , KA.doneKA l d) (_ , KA.doneKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decKAs-src-link l d ksDdone1 {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
decKAs-src-link l d ksDdone1 {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
decKAs-src-link l d ksDdone1 {e₁ = KA.apiKAev l' d' m} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
decKAs-src-link l d (ksSil st) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- the link a driven KA-client step exposes on the Net_Api event
kac-ev-link : (l : Link) (d : Dir) (pos : KAcPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decKAc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
kac-ev-link l d pos step with KANO.renameMap-ev-reflect-ι {P = decKAc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιKA-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιKA e₁)) (decKAc-src-link l d pos srcStep) (kaApiLink e₁))

-- the link a driven KA-server step exposes on the Net_Api event
kas-ev-link : (l : Link) (d : Dir) (pos : KAsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decKAs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
kas-ev-link l d pos step with KANO.renameMap-ev-reflect-ι {P = decKAs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιKA-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιKA e₁)) (decKAs-src-link l d pos srcStep) (kaApiLink e₁))

-- a bundleG KA-image step pins the bundle's link
bundleKA-ev-link : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► Bd′
  → ApiHasLink l (ιKA e₁)
bundleKA-ev-link l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = kac-ev-link l cl (kac ip) sM
... | PEA.evBoth _ sM sTail =
        ⊥-elim (kaTail-kas-noOffer l cl sv csc css bfc bfs ip e₁
                  (λ q → cl≢sv (trans (apiDir-inj (kac-ev-dir l cl (kac ip) sM) (kaApiDir e₁)) q))
                  (_ , sTail))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = kas-ev-link l sv (kas ip) sM
...   | PEA.evBoth _ sM sTail =
          ⊥-elim (kaTail-csc-noOffer l cl sv csc css bfc bfs ip e₁ (_ , sTail))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM      = ⊥-elim (decCSc-noKAgen l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (decCSc-noKAgen l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = ⊥-elim (decCSs-noKAgen l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (decCSs-noKAgen l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM      = ⊥-elim (decBFc-noKAgen l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (decBFc-noKAgen l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = ⊥-elim (decBFs-noKAgen l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (decBFs-noKAgen l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM      = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιKA e₁) (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιKA e₁) (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM      = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιKA e₁) (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιKA e₁) (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM      = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιKA e₁) (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιKA e₁) (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM      = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιKA e₁) (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιKA e₁) (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιKA e₁) (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιKA e₁) (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιKA e₁) (_ , qs))

-- a KA-channel `input` io step of a bundle pins the io's link to the bundle's
bundleKA-io-link-in : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (input l′ d′ N2N_KeepAlive) a)) ]─► Bd′
  → l ≡ l′
bundleKA-io-link-in l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlIn-link (bundleKA-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.sendKA l′ d′} step)

-- a KA-channel `output` io step of a bundle pins the io's link to the bundle's
bundleKA-io-link-out : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (output l′ d′ N2N_KeepAlive) a)) ]─► Bd′
  → l ≡ l′
bundleKA-io-link-out l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlOut-link (bundleKA-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = KA.receiveKA l′ d′} step)

------------------------------------------------------------------------
-- ITEM-6 (io-peel) — TS channel bundle io-link pins (mirror of CS/BF).
-- `decTSc/TSs-src-link` are byte-copies of the `-src-dir` blocks
-- returning `tsEvLink e₁ ≡ l`; `bundleTS-ev-link` copies
-- `bundle-TS-ev-inv`'s 12-peer peel, routing the two TS peers to
-- `tsc/tss-ev-link` (link).
------------------------------------------------------------------------

-- the link component of a TS source event
tsEvLink : {X : Set 0ℓ} → TS.TSEv X → Link
tsEvLink (TS.sendTS l d) = l
tsEvLink (TS.receiveTS l d) = l
tsEvLink (TS.apiTSev l d m) = l
tsEvLink (TS.doneTS l d) = l

-- ιTS carries the source link into the Net_Api event
tsApiLink : {X : Set 0ℓ} (e₁ : TS.TSEv X) → ApiHasLink (tsEvLink e₁) (ιTS e₁)
tsApiLink (TS.sendTS l d) = ahlIn
tsApiLink (TS.receiveTS l d) = ahlOut
tsApiLink (TS.apiTSev l d m) = ahlTS
tsApiLink (TS.doneTS l d) = ahlDone

-- LINK: decTSc-src-link — a fine TS-client source step's event link is `l`
decTSc-src-link : (l : Link) (d : Dir) (pos : TScPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : TSProc}
  → decTSc-src l d pos TSL.─[ TSL.ev (TSL.evl (TSL.evLabel X e₁ a)) ]─► P′
  → tsEvLink e₁ ≡ l
-- head stInit : sends MsgTSInit (io) → tcSil stIdle
decTSc-src-link l d (tcHead TS.stInit) {e₁ = TS.sendTS l' d'} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-link l d (tcHead TS.stInit) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
decTSc-src-link l d (tcHead TS.stInit) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
decTSc-src-link l d (tcHead TS.stInit) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
-- head stIdle : receives a wire request → tcReqIdsB1 / tcReqIdsNB1 / tcReqTxs1
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds Blocking a r)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds NonBlocking a r)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxs ids)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit}        s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone}        s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-link l d (tcHead TS.stIdle) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
-- head stTxIdsBlocking : fires apiTSev sendTSReplyTxIds / sendTSDone
decTSc-src-link l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-link l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSDone} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-link l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}          s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
-- head stTxIdsNonBlocking : fires apiTSev sendTSReplyTxIds
decTSc-src-link l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-link l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSDone}                 s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}          s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-link l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
-- head stTxs : fires apiTSev sendTSReplyTxs
decTSc-src-link l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSReplyTxs} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-link l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-link l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSDone}                  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-link l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-link l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-link l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-link l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}           s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-link l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-link l d (tcHead TS.stTxs) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-link l d (tcHead TS.stTxs) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-link l d (tcHead TS.stTxs) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
-- head stDone : ret, no visible step
decTSc-src-link l d (tcHead TS.stDone) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaf tcReqIdsB1 : fires apiTSev recvTSRequestTxIds (Blocking,a,r) → tcSil stTxIdsBlocking
decTSc-src-link l d (tcReqIdsB1 a r) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxIds) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (Blocking , a , r)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-link l d (tcReqIdsB1 a r) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
decTSc-src-link l d (tcReqIdsB1 a r) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
decTSc-src-link l d (tcReqIdsB1 a r) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
-- recv leaf tcReqIdsNB1 : fires apiTSev recvTSRequestTxIds (NonBlocking,a,r) → tcSil stTxIdsNonBlocking
decTSc-src-link l d (tcReqIdsNB1 a r) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxIds) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (NonBlocking , a , r)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-link l d (tcReqIdsNB1 a r) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
decTSc-src-link l d (tcReqIdsNB1 a r) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
decTSc-src-link l d (tcReqIdsNB1 a r) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
-- recv leaf tcReqTxs1 : fires apiTSev recvTSRequestTxs ids → tcSil stTxs
decTSc-src-link l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxs) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec (λ _ _ → yes refl) val ids
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-link l d (tcReqTxs1 ids) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
decTSc-src-link l d (tcReqTxs1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
decTSc-src-link l d (tcReqTxs1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
-- send leaf tcRepB1 : fires sendTS (MsgTSReplyTxIds ids) → tcSil stIdle
decTSc-src-link l d (tcRepB1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-link l d (tcRepB1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
decTSc-src-link l d (tcRepB1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
decTSc-src-link l d (tcRepB1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
-- send leaf tcDone1 : fires sendTS MsgTSDone → tcSil stDone
decTSc-src-link l d tcDone1 {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-link l d tcDone1 {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
decTSc-src-link l d tcDone1 {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
decTSc-src-link l d tcDone1 {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
-- send leaf tcRepNB1 : fires sendTS (MsgTSReplyTxIds ids) → tcSil stIdle
decTSc-src-link l d (tcRepNB1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-link l d (tcRepNB1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
decTSc-src-link l d (tcRepNB1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
decTSc-src-link l d (tcRepNB1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
-- send leaf tcRepTxs1 : fires sendTS (MsgTSReplyTxs txs) → tcSil stIdle
decTSc-src-link l d (tcRepTxs1 txs) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-link l d (tcRepTxs1 txs) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
decTSc-src-link l d (tcRepTxs1 txs) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
decTSc-src-link l d (tcRepTxs1 txs) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
-- loop re-entry : sil, no visible step
decTSc-src-link l d (tcSil st) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- LINK: decTSs-src-link — mirror for the TS-server positions
decTSs-src-link : (l : Link) (d : Dir) (pos : TSsPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : TSProc}
  → decTSs-src l d pos TSL.─[ TSL.ev (TSL.evl (TSL.evLabel X e₁ a)) ]─► P′
  → tsEvLink e₁ ≡ l
-- head stInit : receives MsgTSInit → tsSil stIdle
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSInit} s with step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-link l d (tsHead TS.stInit) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
-- head stIdle : fires the three api pull requests
decTSs-src-link l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-link l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-link l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-link l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-link l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-link l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSDone}       s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-link l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-link l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-link l d (tsHead TS.stIdle) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-link l d (tsHead TS.stIdle) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-link l d (tsHead TS.stIdle) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
-- head stTxIdsBlocking : receives MsgTSReplyTxIds (→ tsSil stIdle) / MsgTSDone (→ tsDone1)
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSDone} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
-- head stTxIdsNonBlocking : receives MsgTSReplyTxIds → tsSil stIdle
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-link l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
-- head stTxs : receives MsgTSReplyTxs → tsSil stIdle
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxs txs)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-link l d (tsHead TS.stTxs) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
-- head stDone : ret, no visible step
decTSs-src-link l d (tsHead TS.stDone) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf tsDone1 : fires doneTS → tsSil stDone
decTSs-src-link l d tsDone1 {e₁ = TS.doneTS l' d'} {a} s with step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s
... | offer with TS.TSEv-≟ (_ , TS.doneTS l d) (_ , TS.doneTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decTSs-src-link l d tsDone1 {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
decTSs-src-link l d tsDone1 {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
decTSs-src-link l d tsDone1 {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
-- send leaf tsReqB1 : fires sendTS (MsgTSRequestTxIds Blocking a r) → tsSil stTxIdsBlocking
decTSs-src-link l d (tsReqB1 (a , r)) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSs-src-link l d (tsReqB1 (a , r)) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
decTSs-src-link l d (tsReqB1 (a , r)) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
decTSs-src-link l d (tsReqB1 (a , r)) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
-- send leaf tsReqNB1 : fires sendTS (MsgTSRequestTxIds NonBlocking a r) → tsSil stTxIdsNonBlocking
decTSs-src-link l d (tsReqNB1 (a , r)) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSs-src-link l d (tsReqNB1 (a , r)) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
decTSs-src-link l d (tsReqNB1 (a , r)) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
decTSs-src-link l d (tsReqNB1 (a , r)) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
-- send leaf tsReqTxs1 : fires sendTS (MsgTSRequestTxs ids) → tsSil stTxs
decTSs-src-link l d (tsReqTxs1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSs-src-link l d (tsReqTxs1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
decTSs-src-link l d (tsReqTxs1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
decTSs-src-link l d (tsReqTxs1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
-- loop re-entry : sil, no visible step
decTSs-src-link l d (tsSil st) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- the direction a driven TS-client / TS-server step exposes on the Net_Api event

-- the link a driven TS-client step exposes on the Net_Api event
tsc-ev-link : (l : Link) (d : Dir) (pos : TScPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decTSc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
tsc-ev-link l d pos step with TSNO.renameMap-ev-reflect-ι {P = decTSc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιTS-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιTS e₁)) (decTSc-src-link l d pos srcStep) (tsApiLink e₁))

-- the link a driven TS-server step exposes on the Net_Api event
tss-ev-link : (l : Link) (d : Dir) (pos : TSsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decTSs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
tss-ev-link l d pos step with TSNO.renameMap-ev-reflect-ι {P = decTSs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιTS-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιTS e₁)) (decTSs-src-link l d pos srcStep) (tsApiLink e₁))

-- a bundleG TS-image step pins the bundle's link
bundleTS-ev-link : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► Bd′
  → ApiHasLink l (ιTS e₁)
bundleTS-ev-link l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL  _ sK     = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιTS e₁) (_ , sK))
... | PEA.evBoth _ sK _ = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιTS e₁) (_ , sK))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL  _ sK     = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιTS e₁) (_ , sK))
...   | PEA.evBoth _ sK _ = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιTS e₁) (_ , sK))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM      = ⊥-elim (decCSc-noTSgen l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (decCSc-noTSgen l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = ⊥-elim (decCSs-noTSgen l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (decCSs-noTSgen l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM      = ⊥-elim (decBFc-noTSgen l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (decBFc-noTSgen l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = ⊥-elim (decBFs-noTSgen l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (decBFs-noTSgen l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM = tsc-ev-link l cl (tsc ip) sM
...             | PEA.evBoth _ sM sTail =
                    ⊥-elim (tsTail-tss-noOffer l cl sv ip e₁
                              (λ q → cl≢sv (trans (apiDir-inj (tsc-ev-dir l cl (tsc ip) sM) (tsApiDir e₁)) q))
                              (_ , sTail))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = tss-ev-link l sv (tss ip) sM
...               | PEA.evBoth _ sM sTail =
                      ⊥-elim (tsTail-lnc-noOffer l cl sv ip e₁ (_ , sTail))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM      = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιTS e₁) (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιTS e₁) (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM      = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιTS e₁) (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιTS e₁) (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιTS e₁) (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιTS e₁) (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιTS e₁) (_ , qs))

-- a TS-channel `input` io step of a bundle pins the io's link to the bundle's
bundleTS-io-link-in : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (input l′ d′ N2N_TxSubmission) a)) ]─► Bd′
  → l ≡ l′
bundleTS-io-link-in l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlIn-link (bundleTS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.sendTS l′ d′} step)

-- a TS-channel `output` io step of a bundle pins the io's link to the bundle's
bundleTS-io-link-out : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (output l′ d′ N2N_TxSubmission) a)) ]─► Bd′
  → l ≡ l′
bundleTS-io-link-out l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlOut-link (bundleTS-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = TS.receiveTS l′ d′} step)

------------------------------------------------------------------------
-- ITEM-6 (io-peel) — LN channel bundle io-link pins (mirror of CS/BF).
-- `decLNc/LNs-src-link` are byte-copies of the `-src-dir` blocks
-- returning `lnEvLink e₁ ≡ l`; `bundleLN-ev-link` copies
-- `bundle-LN-ev-inv`'s 12-peer peel, routing the two LN peers to
-- `lnc/lns-ev-link` (link).
------------------------------------------------------------------------

-- the link component of a LN source event
lnEvLink : {X : Set 0ℓ} → LNp.LNEv X → Link
lnEvLink (LNp.sendLN l d) = l
lnEvLink (LNp.receiveLN l d) = l
lnEvLink (LNp.apiLNev l d m) = l
lnEvLink (LNp.doneLN l d) = l

-- ιLN carries the source link into the Net_Api event
lnApiLink : {X : Set 0ℓ} (e₁ : LNp.LNEv X) → ApiHasLink (lnEvLink e₁) (ιLN e₁)
lnApiLink (LNp.sendLN l d) = ahlIn
lnApiLink (LNp.receiveLN l d) = ahlOut
lnApiLink (LNp.apiLNev l d m) = ahlLN
lnApiLink (LNp.doneLN l d) = ahlDone

-- LINK: decLNc-src-link — a fine LN-client source step's event link is `l`
decLNc-src-link : (l : Link) (d : Dir) (pos : LNcPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {P′ : LNProc}
  → decLNc-src l d pos LNL.─[ LNL.ev (LNL.evl (LNL.evLabel X e₁ a)) ]─► P′
  → lnEvLink e₁ ≡ l
-- head stIdle : fires apiLNev sendLNRequestNext / sendLNDone
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNRequestNext} {a} s with step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNDone} {a} s with step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockTxsOffer}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNVotesOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockTxsOffer}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNVotesOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-link l d (lncHead LNp.stIdle) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
-- head stBusy : receives one of four notifications
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockAnnouncement h)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockOffer q)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockTxsOffer q)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNVotesOffer vs)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNRequestNext} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNDone} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-link l d (lncHead LNp.stBusy) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
-- head stDone : ret, no visible step
decLNc-src-link l d (lncHead LNp.stDone) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaf lncRann1 : fires apiLNev recvLNBlockAnnouncement h → lncSil stIdle
decLNc-src-link l d (lncRann1 h) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockAnnouncement) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ h
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-link l d (lncRann1 h) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
decLNc-src-link l d (lncRann1 h) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
decLNc-src-link l d (lncRann1 h) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
-- recv leaf lncRoff1 : fires apiLNev recvLNBlockOffer q → lncSil stIdle
decLNc-src-link l d (lncRoff1 q) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ q
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-link l d (lncRoff1 q) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
decLNc-src-link l d (lncRoff1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
decLNc-src-link l d (lncRoff1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
-- recv leaf lncRtxs1 : fires apiLNev recvLNBlockTxsOffer q → lncSil stIdle
decLNc-src-link l d (lncRtxs1 q) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockTxsOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ q
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-link l d (lncRtxs1 q) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
decLNc-src-link l d (lncRtxs1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
decLNc-src-link l d (lncRtxs1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
-- recv leaf lncRvot1 : fires apiLNev recvLNVotesOffer vs → lncSil stIdle
decLNc-src-link l d (lncRvot1 vs) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNVotesOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val vs
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-link l d (lncRvot1 vs) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
decLNc-src-link l d (lncRvot1 vs) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
decLNc-src-link l d (lncRvot1 vs) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
-- send leaf lncReq1 : fires sendLN MsgLNRequestNext → lncSil stBusy
decLNc-src-link l d lncReq1 {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-link l d lncReq1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
decLNc-src-link l d lncReq1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
decLNc-src-link l d lncReq1 {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
-- send leaf lncDone1 : fires sendLN MsgLNDone → lncSil stDone
decLNc-src-link l d lncDone1 {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-link l d lncDone1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
decLNc-src-link l d lncDone1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
decLNc-src-link l d lncDone1 {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
-- loop re-entry : sil, no visible step
decLNc-src-link l d (lncSil st) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- LINK: decLNs-src-link — mirror for the LN-server positions
decLNs-src-link : (l : Link) (d : Dir) (pos : LNsPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {P′ : LNProc}
  → decLNs-src l d pos LNL.─[ LNL.ev (LNL.evl (LNL.evLabel X e₁ a)) ]─► P′
  → lnEvLink e₁ ≡ l
-- head stIdle : receives MsgLNRequestNext (→ lnsSil stBusy) / MsgLNDone (→ lnsDone1)
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNRequestNext} s with step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNDone} s with step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-link l d (lnsHead LNp.stIdle) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
-- head stBusy : fires one of four api sends
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockAnnouncement} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockTxsOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNVotesOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNRequestNext} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNDone}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockOffer}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockTxsOffer} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNVotesOffer}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-link l d (lnsHead LNp.stBusy) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
-- head stDone : ret, no visible step
decLNs-src-link l d (lnsHead LNp.stDone) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf lnsDone1 : fires doneLN → lnsSil stDone
decLNs-src-link l d lnsDone1 {e₁ = LNp.doneLN l' d'} {a} s with step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.doneLN l d) (_ , LNp.doneLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decLNs-src-link l d lnsDone1 {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
decLNs-src-link l d lnsDone1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
decLNs-src-link l d lnsDone1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
-- send leaf lnsWann1 : fires sendLN (MsgLNBlockAnnouncement h) → lnsSil stIdle
decLNs-src-link l d (lnsWann1 h) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-src-link l d (lnsWann1 h) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
decLNs-src-link l d (lnsWann1 h) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
decLNs-src-link l d (lnsWann1 h) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
-- send leaf lnsWoff1 : fires sendLN (MsgLNBlockOffer q) → lnsSil stIdle
decLNs-src-link l d (lnsWoff1 q) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-src-link l d (lnsWoff1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
decLNs-src-link l d (lnsWoff1 q) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
decLNs-src-link l d (lnsWoff1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
-- send leaf lnsWtxs1 : fires sendLN (MsgLNBlockTxsOffer q) → lnsSil stIdle
decLNs-src-link l d (lnsWtxs1 q) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-src-link l d (lnsWtxs1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
decLNs-src-link l d (lnsWtxs1 q) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
decLNs-src-link l d (lnsWtxs1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
-- send leaf lnsWvot1 : fires sendLN (MsgLNVotesOffer vs) → lnsSil stIdle
decLNs-src-link l d (lnsWvot1 vs) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-src-link l d (lnsWvot1 vs) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
decLNs-src-link l d (lnsWvot1 vs) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
decLNs-src-link l d (lnsWvot1 vs) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
-- loop re-entry : sil, no visible step
decLNs-src-link l d (lnsSil st) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()


-- the link a driven LN-client step exposes on the Net_Api event
lnc-ev-link : (l : Link) (d : Dir) (pos : LNcPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decLNc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
lnc-ev-link l d pos step with LNNO.renameMap-ev-reflect-ι {P = decLNc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιLN-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιLN e₁)) (decLNc-src-link l d pos srcStep) (lnApiLink e₁))

-- the link a driven LN-server step exposes on the Net_Api event
lns-ev-link : (l : Link) (d : Dir) (pos : LNsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decLNs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasLink l e₂
lns-ev-link l d pos step with LNNO.renameMap-ev-reflect-ι {P = decLNs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasLink l z) (sym (ιLN-inv-shape iota))
        (subst (λ ll → ApiHasLink ll (ιLN e₁)) (decLNs-src-link l d pos srcStep) (lnApiLink e₁))

-- a bundleG LN-image step pins the bundle's link
bundleLN-ev-link : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► Bd′
  → ApiHasLink l (ιLN e₁)
bundleLN-ev-link l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL  _ sM     = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιLN e₁) (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιLN e₁) (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL  _ sM     = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιLN e₁) (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιLN e₁) (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM      = ⊥-elim (decCSc-noLNgen l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (decCSc-noLNgen l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = ⊥-elim (decCSs-noLNgen l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (decCSs-noLNgen l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM      = ⊥-elim (decBFc-noLNgen l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (decBFc-noLNgen l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = ⊥-elim (decBFs-noLNgen l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (decBFs-noLNgen l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM      = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιLN e₁) (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιLN e₁) (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM      = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιLN e₁) (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιLN e₁) (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM = lnc-ev-link l cl (lnc ip) sM
...                 | PEA.evBoth _ sM sTail =
                        ⊥-elim (lnTail-lns-noOffer l cl sv ip e₁
                                  (λ q → cl≢sv (trans (apiDir-inj (lnc-ev-dir l cl (lnc ip) sM) (lnApiDir e₁)) q))
                                  (_ , sTail))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = lns-ev-link l sv (lns ip) sM
...                   | PEA.evBoth _ sM sTail =
                          ⊥-elim (lnTail-lfc-noOffer l cl sv ip e₁ (_ , sTail))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιLN e₁) (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιLN e₁) (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιLN e₁) (_ , qs))

-- a LN-channel `input` io step of a bundle pins the io's link to the bundle's
bundleLN-io-link-in : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (input l′ d′ N2N_LeiosNotify) a)) ]─► Bd′
  → l ≡ l′
bundleLN-io-link-in l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlIn-link (bundleLN-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LNp.sendLN l′ d′} step)

-- a LN-channel `output` io step of a bundle pins the io's link to the bundle's
bundleLN-io-link-out : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {l′ : Link} {d′ : Dir} {a : Payload} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel Payload (output l′ d′ N2N_LeiosNotify) a)) ]─► Bd′
  → l ≡ l′
bundleLN-io-link-out l cl sv cl≢sv csc css bfc bfs ip {l′} {d′} step =
  ahlOut-link (bundleLN-ev-link l cl sv cl≢sv csc css bfc bfs ip {e₁ = LNp.receiveLN l′ d′} step)

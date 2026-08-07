{-# OPTIONS --guardedness #-}

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_RouteKaTs (blkA : Block₃) where

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
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode blkA
  using ( SysState; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium blkA
  using ( decMed; decLink; decCopy; MedState; mkMed; phase; broken
        ; CopyPhase; empty; full; draining; NetProcN; vis-of )
open import CSP.Examples.Cardano_network.Network p Payload using ( Copy )
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆; Skip; ∅ES )
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as LN
import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {Payload}) as PEN
open import CSP.Laws.Traces.TraceLawsParallel (Net-≟ {Payload}) using ( fPar-er; fPar-sr; fPar-nn )
open import Data.List using ( List; []; _∷_; length; lookup; updateAt; map )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA as SN
open SN
  using ( decNodeA; decNodeB; decNodeC; decNodeD; bundleG; bundleA )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA as SStep
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
import CSP.Examples.Cardano_network.NetworkVerification.Praos.NodeSpecs blkA as NS
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

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_GapBDisj blkA public

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER A — KeepAlive channel direction machinery,
-- concrete/abstract non-offers and augmented sims.  Mirrors the CS/BF
-- direction+sim layer (`csEvDir`/`csc-ev-dir`/`decCSc-src-dir`/`simCSc′`/
-- `CSc-CSs-noBoth`); the KA peer's io/direction structure is identical to CS.
------------------------------------------------------------------------

-- cross-protocol preimages towards a KA-image event (all `nothing`: ιX and
-- ιKA hit disjoint Net_Api channels), for refuting non-KA concrete siblings
ιCS⁻¹∘ιKA : {X : Set 0ℓ} (e₁ : KA.KAEv X) → ιCS⁻¹ (ιKA e₁) ≡ nothing
ιCS⁻¹∘ιKA (KA.sendKA l d)    = refl
ιCS⁻¹∘ιKA (KA.receiveKA l d) = refl
ιCS⁻¹∘ιKA (KA.apiKAev l d m) = refl
ιCS⁻¹∘ιKA (KA.doneKA l d)    = refl
ιBF⁻¹∘ιKA : {X : Set 0ℓ} (e₁ : KA.KAEv X) → ιBF⁻¹ (ιKA e₁) ≡ nothing
ιBF⁻¹∘ιKA (KA.sendKA l d)    = refl
ιBF⁻¹∘ιKA (KA.receiveKA l d) = refl
ιBF⁻¹∘ιKA (KA.apiKAev l d m) = refl
ιBF⁻¹∘ιKA (KA.doneKA l d)    = refl
ιTS⁻¹∘ιKA : {X : Set 0ℓ} (e₁ : KA.KAEv X) → ιTS⁻¹ (ιKA e₁) ≡ nothing
ιTS⁻¹∘ιKA (KA.sendKA l d)    = refl
ιTS⁻¹∘ιKA (KA.receiveKA l d) = refl
ιTS⁻¹∘ιKA (KA.apiKAev l d m) = refl
ιTS⁻¹∘ιKA (KA.doneKA l d)    = refl
ιLN⁻¹∘ιKA : {X : Set 0ℓ} (e₁ : KA.KAEv X) → ιLN⁻¹ (ιKA e₁) ≡ nothing
ιLN⁻¹∘ιKA (KA.sendKA l d)    = refl
ιLN⁻¹∘ιKA (KA.receiveKA l d) = refl
ιLN⁻¹∘ιKA (KA.apiKAev l d m) = refl
ιLN⁻¹∘ιKA (KA.doneKA l d)    = refl
ιLF⁻¹∘ιKA : {X : Set 0ℓ} (e₁ : KA.KAEv X) → ιLF⁻¹ (ιKA e₁) ≡ nothing
ιLF⁻¹∘ιKA (KA.sendKA l d)    = refl
ιLF⁻¹∘ιKA (KA.receiveKA l d) = refl
ιLF⁻¹∘ιKA (KA.apiKAev l d m) = refl
ιLF⁻¹∘ιKA (KA.doneKA l d)    = refl

-- (concrete CS/BF `decX-noKAgen` non-offers live in Layer C, after CSNOff/BFNOff)

-- the direction component of a KeepAlive source event
kaEvDir : {X : Set 0ℓ} → KA.KAEv X → Dir
kaEvDir (KA.sendKA l d)    = d
kaEvDir (KA.receiveKA l d) = d
kaEvDir (KA.apiKAev l d m) = d
kaEvDir (KA.doneKA l d)    = d

-- ιKA carries the source direction into the Net_Api event
kaApiDir : {X : Set 0ℓ} (e₁ : KA.KAEv X) → ApiHasDir (kaEvDir e₁) (ιKA e₁)
kaApiDir (KA.sendKA l d)    = ahIn
kaApiDir (KA.receiveKA l d) = ahOut
kaApiDir (KA.apiKAev l d m) = ahKA
kaApiDir (KA.doneKA l d)    = ahDone

-- L2 (KA client): the visible source step of a fine position fires an event
-- whose direction component is `d` (kaEvDir extracts it).  Mirrors
-- `decKAc-src-ev-inv` clause-for-clause; firing clauses return `refl`.
decKAc-src-dir : (l : Link) (d : Dir) (pos : KAcPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : KAProc}
  → decKAc-src l d pos KAL.─[ KAL.ev (KAL.evl (KAL.evLabel X e₁ a)) ]─► P′
  → kaEvDir e₁ ≡ d
decKAc-src-dir l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' sendKAMsg} {a} s with step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decKAc-src-dir l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' sendKADone} {a} s with step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = refl
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decKAc-src-dir l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' errCookie}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-dir l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' recvKACookie} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-dir l d (kcHead KA.stClient) {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-dir l d (kcHead KA.stClient) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-dir l d (kcHead KA.stClient) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-dir l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAliveResponse cr)} s with step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decKAc-src-dir l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAlive c)} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-dir l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive MsgKADone}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-dir l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-dir l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-dir l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-dir l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-dir l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-dir l d (kcHead (KA.stServer cq)) {e₁ = KA.sendKA l' d'}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-dir l d (kcHead (KA.stServer cq)) {e₁ = KA.apiKAev l' d' m}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-dir l d (kcHead (KA.stServer cq)) {e₁ = KA.doneKA l' d'}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-dir l d (kcHead KA.stDone) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decKAc-src-dir l d (kcErr1 cq cr ne) s = ⊥-elim (ne refl)
decKAc-src-dir l d (kcReq1 c) {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decKAc-src-dir l d (kcReq1 c) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
decKAc-src-dir l d (kcReq1 c) {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
decKAc-src-dir l d (kcReq1 c) {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
decKAc-src-dir l d kcDone1 {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive MsgKADone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decKAc-src-dir l d kcDone1 {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
decKAc-src-dir l d kcDone1 {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
decKAc-src-dir l d kcDone1 {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
decKAc-src-dir l d (kcSil st) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decKAc-src-dir l d kcTermE1 s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- L2 (KA server): mirror of `decKAs-src-ev-inv`; firing clauses return `refl`.
decKAs-src-dir : (l : Link) (d : Dir) (pos : KAsPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : KAProc}
  → decKAs-src l d pos KAL.─[ KAL.ev (KAL.evl (KAL.evLabel X e₁ a)) ]─► P′
  → kaEvDir e₁ ≡ d
decKAs-src-dir l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAlive c)} s with step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decKAs-src-dir l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive MsgKADone} s with step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decKAs-src-dir l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAliveResponse c)} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-dir l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-dir l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-dir l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-dir l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-dir l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-dir l d (ksHead KA.stClient) {e₁ = KA.sendKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-dir l d (ksHead KA.stClient) {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-dir l d (ksHead KA.stClient) {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-dir l d (ksHead (KA.stServer c)) {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decKAs-src-dir l d (ksHead (KA.stServer c)) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
decKAs-src-dir l d (ksHead (KA.stServer c)) {e₁ = KA.apiKAev l' d' m} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
decKAs-src-dir l d (ksHead (KA.stServer c)) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
decKAs-src-dir l d (ksHead KA.stDone) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decKAs-src-dir l d (ksRecv1 c) {e₁ = KA.apiKAev l' d' m} {a} s with step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s
... | offer with KA.KAEv-≟ (_ , KA.apiKAev l d recvKACookie) (_ , KA.apiKAev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decKAs-src-dir l d (ksRecv1 c) {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
decKAs-src-dir l d (ksRecv1 c) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
decKAs-src-dir l d (ksRecv1 c) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
decKAs-src-dir l d ksDdone1 {e₁ = KA.doneKA l' d'} {a} s with step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s
... | offer with KA.KAEv-≟ (_ , KA.doneKA l d) (_ , KA.doneKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decKAs-src-dir l d ksDdone1 {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
decKAs-src-dir l d ksDdone1 {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
decKAs-src-dir l d ksDdone1 {e₁ = KA.apiKAev l' d' m} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
decKAs-src-dir l d (ksSil st) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- the direction a driven KA-client / KA-server step exposes on the Net_Api event
kac-ev-dir : (l : Link) (d : Dir) (pos : KAcPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decKAc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
kac-ev-dir l d pos step with KANO.renameMap-ev-reflect-ι {P = decKAc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιKA-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιKA e₁)) (decKAc-src-dir l d pos srcStep) (kaApiDir e₁))
kas-ev-dir : (l : Link) (d : Dir) (pos : KAsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decKAs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
kas-ev-dir l d pos step with KANO.renameMap-ev-reflect-ι {P = decKAs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιKA-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιKA e₁)) (decKAs-src-dir l d pos srcStep) (kaApiDir e₁))

-- L2 (KA): the client (dir cl) and server (dir sv≠cl) never fire the SAME event
KAc-KAs-noBoth : (l : Link) (cl sv : Dir) → cl ≢ sv → (pc : KAcPos) (ps : KAsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {Mc Ms : NetProc}
  → decKAc l cl pc ─[ ev (evl (evLabel X e₂ a)) ]─► Mc
  → decKAs l sv ps ─[ ev (evl (evLabel X e₂ a)) ]─► Ms → ⊥
KAc-KAs-noBoth l cl sv cl≢sv pc ps sc ss =
  cl≢sv (apiDir-inj (kac-ev-dir l cl pc sc) (kas-ev-dir l sv ps ss))

-- concrete KA peers never fire a wrong-direction KA-image event
decKAc-dir-noOffer : (l : Link) (d : Dir) (pos : KAcPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → kaEvDir e₁ ≢ d → ¬ IoOffers (decKAc l d pos) (ιKA e₁) a
decKAc-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (kac-ev-dir l d pos step) (kaApiDir e₁)))
decKAs-dir-noOffer : (l : Link) (d : Dir) (pos : KAsPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → kaEvDir e₁ ≢ d → ¬ IoOffers (decKAs l d pos) (ιKA e₁) a
decKAs-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (kas-ev-dir l d pos step) (kaApiDir e₁)))

-- augmented KA-client / KA-server sim (exposes e₁ / e≡ιKA e₁ / kaEvDir e₁≡d)
simKAc′ : (l : Link) (d : Dir) (pos : KAcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decKAc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ KA.KAEv X ] Σ[ pos′ ∈ KAcPos ]
       (e ≡ ιKA e₁) × (kaEvDir e₁ ≡ d) × (M ≡ decKAc l d pos′)
       × (absKAc l d pos ─[ ev (evl (evLabel X e a)) ]─► absKAc l d pos′)
simKAc′ l d pos step with KANO.renameMap-ev-reflect-ι {P = decKAc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decKAc-src-ev-inv l d pos srcStep | ιKA-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decKAc-src-dir l d pos srcStep ,
        trans Meq (cong RenKA.renameMap P′eq) , aStep
simKAs′ : (l : Link) (d : Dir) (pos : KAsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decKAs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ KA.KAEv X ] Σ[ pos′ ∈ KAsPos ]
       (e ≡ ιKA e₁) × (kaEvDir e₁ ≡ d) × (M ≡ decKAs l d pos′)
       × (absKAs l d pos ─[ ev (evl (evLabel X e a)) ]─► absKAs l d pos′)
simKAs′ l d pos step with KANO.renameMap-ev-reflect-ι {P = decKAs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decKAs-src-ev-inv l d pos srcStep | ιKA-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decKAs-src-dir l d pos srcStep ,
        trans Meq (cong RenKA.renameMap P′eq) , aStep

------------------------------------------------------------------------
-- GAP-B step 1 — abstract-DIRECTION sibling non-offers.  The same-protocol
-- OPPOSITE-role abstract peer (at direction sv) never offers the driven
-- peer's event (which carries the driven direction cl ≢ sv): every firing
-- clause of the abstract `nxt` table guards on `d′ ≟ d`, so a wrong-direction
-- event falls to the per-table catch-all `nothing`.  SCRIPT-GENERATED
-- (`.superpowers/sdd/gen-l4-dir.py`).
------------------------------------------------------------------------
-- csSnxt-dir-no: a wrong-direction CS-image event (csEvDir e₁ ≢ d)
-- has no csSnxt table edge (every firing clause guards on d′ ≟ d)
csSnxt-dir-no : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ d → NS.csSnxt l d q (X , ιCS e₁) a ≡ nothing
csSnxt-dir-no l d NS.csIdle (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d NS.csIdle (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' reqCSRequestNext) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csAreq (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csAreq (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSAwaitReply) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRollForward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSRollBackward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csCanAwait (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d (NS.csAfi _) (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSIntersectFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csInt (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csDdone (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csDdone (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csDdone (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d NS.csDdone (CS.doneCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csMust (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSRollForward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSRollBackward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csSnxt-dir-no l d NS.csMust (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWrf _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d (NS.csWrf _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWrf _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d (NS.csWrf _) (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWrb _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d (NS.csWrb _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWrb _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d (NS.csWrb _) (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csWar (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d NS.csWar (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csWar (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d NS.csWar (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWif _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d (NS.csWif _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWif _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d (NS.csWif _) (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWin _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csSnxt-dir-no l d (NS.csWin _) (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d (NS.csWin _) (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d (NS.csWin _) (CS.doneCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csTerm (CS.sendCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csTerm (CS.receiveCS l' d') ¬eq = refl
csSnxt-dir-no l d NS.csTerm (CS.apiCSev l' d' m) ¬eq = refl
csSnxt-dir-no l d NS.csTerm (CS.doneCS l' d') ¬eq = refl

-- csCnxt-dir-no: a wrong-direction CS-image event (csEvDir e₁ ≢ d)
-- has no csCnxt table edge (every firing clause guards on d′ ≟ d)
csCnxt-dir-no : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ d → NS.csCnxt l d q (X , ιCS e₁) a ≡ nothing
csCnxt-dir-no l d NS.ccIdle (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRequestNext) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSFindIntersect) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d NS.ccIdle (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccWreq (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccWreq (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccWreq (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccWreq (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccAwait (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccWfi _) (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d (NS.ccWfi _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccWfi _) (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d (NS.ccWfi _) (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccInt (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccWdone (CS.sendCS l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccWdone (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccWdone (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccWdone (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSRequestNext} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSAwaitReply} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , chainSync MsgCSDone} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , blockFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.receiveCS l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccMust (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSRollforward) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccArf _) (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSRollback) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccArb _) (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccAif _) (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSDone) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSAwaitReply) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRollForward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSRollBackward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' sendCSIntersectNotFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSRollforward) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSRollback) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSIntersectFound) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' recvCSIntersectNotFound) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' reqCSRequestNext) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.apiCSev l' d' reqCSFindIntersect) ¬eq = refl
csCnxt-dir-no l d (NS.ccAin _) (CS.doneCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccTerm (CS.sendCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccTerm (CS.receiveCS l' d') ¬eq = refl
csCnxt-dir-no l d NS.ccTerm (CS.apiCSev l' d' m) ¬eq = refl
csCnxt-dir-no l d NS.ccTerm (CS.doneCS l' d') ¬eq = refl

-- bfCnxt-dir-no: a wrong-direction BF-image event (bfEvDir e₁ ≢ d)
-- has no bfCnxt table edge (every firing clause guards on d′ ≟ d)
bfCnxt-dir-no : (l : Link) (d : Dir) (q : NS.BFcPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ d → NS.bfCnxt l d q (X , ιBF e₁) a ≡ nothing
bfCnxt-dir-no l d NS.bcIdle (BF.sendBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.receiveBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFRequestRange) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFClientDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfCnxt-dir-no l d NS.bcIdle (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d (NS.bcWrr _) (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d (NS.bcWrr _) (BF.receiveBF l' d') ¬eq = refl
bfCnxt-dir-no l d (NS.bcWrr _) (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-dir-no l d (NS.bcWrr _) (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.sendBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-dir-no l d NS.bcBusy (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcWcd (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcWcd (BF.receiveBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcWcd (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-dir-no l d NS.bcWcd (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.sendBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-dir-no l d NS.bcStream (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.sendBF l' d') ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.receiveBF l' d') ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' recvBFBlock) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfCnxt-dir-no l d (NS.bcAblk _) (BF.doneBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcTerm (BF.sendBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcTerm (BF.receiveBF l' d') ¬eq = refl
bfCnxt-dir-no l d NS.bcTerm (BF.apiBFev l' d' m) ¬eq = refl
bfCnxt-dir-no l d NS.bcTerm (BF.doneBF l' d') ¬eq = refl

-- bfSnxt-dir-no: a wrong-direction BF-image event (bfEvDir e₁ ≢ d)
-- has no bfSnxt table edge (every firing clause guards on d′ ≟ d)
bfSnxt-dir-no : (l : Link) (d : Dir) (q : NS.BFsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ d → NS.bfSnxt l d q (X , ιBF e₁) a ≡ nothing
bfSnxt-dir-no l d NS.bsIdle (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgRequestRange _)} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgStartBatch} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgNoBlocks} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch (MsgBlock _)} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgBatchDone} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , blockFetch MsgClientDone} ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , keepAlive _} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , chainSync _} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , txSubmission _} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , leiosNotify _} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.receiveBF l' d') {a = _ , _ , _ , leiosFetch _} ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsIdle (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.apiBFev l' d' reqBFRange) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d (NS.bsAreq _) (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFStartBatch) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFNoBlocks) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFBlock) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' sendBFBatchDone) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfSnxt-dir-no l d NS.bsBusy (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsDdone (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsDdone (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsDdone (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsDdone (BF.doneBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsWsb (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsWsb (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsWsb (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsWsb (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFRequestRange) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFClientDone) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFStartBatch) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFNoBlocks) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFBlock) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' sendBFBatchDone) ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' recvBFBlock) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.apiBFev l' d' reqBFRange) ¬eq = refl
bfSnxt-dir-no l d NS.bsStream (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsWnb (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsWnb (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsWnb (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsWnb (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d (NS.bsWblk _) (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d (NS.bsWblk _) (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d (NS.bsWblk _) (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d (NS.bsWblk _) (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsWbd (BF.sendBF l' d') ¬eq with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬eq refl)
... | yes refl | no _ = refl
... | no _ | yes refl = refl
... | no _ | no _ = refl
bfSnxt-dir-no l d NS.bsWbd (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsWbd (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsWbd (BF.doneBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsTerm (BF.sendBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsTerm (BF.receiveBF l' d') ¬eq = refl
bfSnxt-dir-no l d NS.bsTerm (BF.apiBFev l' d' m) ¬eq = refl
bfSnxt-dir-no l d NS.bsTerm (BF.doneBF l' d') ¬eq = refl

-- absCSs-dir-noBoth: the same-protocol OPPOSITE-role sibling (dir CS) does
-- not fire the driven peer's wrong-direction event (via csSnxt-dir-no)
absCSs-dir-noBoth : (l : Link) (sv : Dir) (q : CSsPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ sv → ¬ IoOffers (absCSs l sv q) (ιCS e₁) a
absCSs-dir-noBoth l sv q e₁ {a} ¬d with NS.csSfin (coarsenCSs q) in fEq
... | true  = viewV→noOffer (absCSs l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csSfin ; nxt = NS.csSnxt l sv })
                   (coarsenCSs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSs l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csSfin ; nxt = NS.csSnxt l sv })
                   (coarsenCSs q) {e = ιCS e₁} {a = a} fEq (csSnxt-dir-no l sv (coarsenCSs q) e₁ {a = a} ¬d))

-- absCSc-dir-noBoth: the same-protocol OPPOSITE-role sibling (dir CS) does
-- not fire the driven peer's wrong-direction event (via csCnxt-dir-no)
absCSc-dir-noBoth : (l : Link) (sv : Dir) (q : CScPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ sv → ¬ IoOffers (absCSc l sv q) (ιCS e₁) a
absCSc-dir-noBoth l sv q e₁ {a} ¬d with NS.csCfin (coarsenCSc q) in fEq
... | true  = viewV→noOffer (absCSc l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csCfin ; nxt = NS.csCnxt l sv })
                   (coarsenCSc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSc l sv q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csCfin ; nxt = NS.csCnxt l sv })
                   (coarsenCSc q) {e = ιCS e₁} {a = a} fEq (csCnxt-dir-no l sv (coarsenCSc q) e₁ {a = a} ¬d))

-- absBFc-dir-noBoth: the same-protocol OPPOSITE-role sibling (dir BF) does
-- not fire the driven peer's wrong-direction event (via bfCnxt-dir-no)
absBFc-dir-noBoth : (l : Link) (sv : Dir) (q : BFcPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ sv → ¬ IoOffers (absBFc l sv q) (ιBF e₁) a
absBFc-dir-noBoth l sv q e₁ {a} ¬d with NS.bfCfin (coarsenBFc q) in fEq
... | true  = viewV→noOffer (absBFc l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l sv })
                   (coarsenBFc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFc l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l sv })
                   (coarsenBFc q) {e = ιBF e₁} {a = a} fEq (bfCnxt-dir-no l sv (coarsenBFc q) e₁ {a = a} ¬d))

-- absBFs-dir-noBoth: the same-protocol OPPOSITE-role sibling (dir BF) does
-- not fire the driven peer's wrong-direction event (via bfSnxt-dir-no)
absBFs-dir-noBoth : (l : Link) (sv : Dir) (q : BFsPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ sv → ¬ IoOffers (absBFs l sv q) (ιBF e₁) a
absBFs-dir-noBoth l sv q e₁ {a} ¬d with NS.bfSfin (coarsenBFs q) in fEq
... | true  = viewV→noOffer (absBFs l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l sv })
                   (coarsenBFs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFs l sv q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l sv })
                   (coarsenBFs q) {e = ιBF e₁} {a = a} fEq (bfSnxt-dir-no l sv (coarsenBFs q) e₁ {a = a} ¬d))



------------------------------------------------------------------------
-- GAP-B step 3 (abstract-bundle REASSEMBLY) — rebuild an `absBundleG` visible
-- step from a single driven-peer step, threading the sibling non-offers past
-- the eight `⦀` layers (`⦀-ev-L/R` take a `viewV (force _) ≡ nothing`; single
-- peers via `noOffer→viewV`, the sibling GROUP via `⦀-viewV-nothing`/`⦀-noOffer`).
-- Cross-protocol siblings by the committed `*-no{CS,BF}` leaves; the same-
-- protocol opposite-role sibling by the direction leaf `abs*-dir-noBoth`.
-- These are the UPWARD half of `bundle-{CS,BF}-ev-inv` (downward peel residual).
------------------------------------------------------------------------

------------------------------------------------------------------------
-- STEP 5 — abstract LN/LF foreign-channel non-offers.  Position-enumerated
-- table lemmas (`*nxt-no{CS,BF}-pos`, total over the abstract position type)
-- then lifted per coarsened position (`absX-no{CS,BF}`), mirroring the
-- KA/TS `*Cnxt-no{CS,BF}-pos` / `absX-no{CS,BF}` pattern.  Every foreign
-- (CS/BF-image) event hits the table `nothing` catch-all at every position.
------------------------------------------------------------------------

lnCnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.LNcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.lnCnxt l d q (X , ιCS e₁) a ≡ nothing
lnCnxt-noCS-pos l d NS.lncIdle (CS.sendCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncIdle (CS.receiveCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncIdle (CS.apiCSev _ _ _) = refl
lnCnxt-noCS-pos l d NS.lncIdle (CS.doneCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncWreq (CS.sendCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncWreq (CS.receiveCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncWreq (CS.apiCSev _ _ _) = refl
lnCnxt-noCS-pos l d NS.lncWreq (CS.doneCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncWdone (CS.sendCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncWdone (CS.receiveCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncWdone (CS.apiCSev _ _ _) = refl
lnCnxt-noCS-pos l d NS.lncWdone (CS.doneCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncBusy (CS.sendCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncBusy (CS.receiveCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncBusy (CS.apiCSev _ _ _) = refl
lnCnxt-noCS-pos l d NS.lncBusy (CS.doneCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRann _) (CS.sendCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRann _) (CS.receiveCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRann _) (CS.apiCSev _ _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRann _) (CS.doneCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRoff _) (CS.sendCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRoff _) (CS.receiveCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRoff _) (CS.apiCSev _ _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRoff _) (CS.doneCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRtxs _) (CS.sendCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRtxs _) (CS.receiveCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRtxs _) (CS.apiCSev _ _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRtxs _) (CS.doneCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRvot _) (CS.sendCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRvot _) (CS.receiveCS _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRvot _) (CS.apiCSev _ _ _) = refl
lnCnxt-noCS-pos l d (NS.lncRvot _) (CS.doneCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncTerm (CS.sendCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncTerm (CS.receiveCS _ _) = refl
lnCnxt-noCS-pos l d NS.lncTerm (CS.apiCSev _ _ _) = refl
lnCnxt-noCS-pos l d NS.lncTerm (CS.doneCS _ _) = refl

lnCnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.LNcPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.lnCnxt l d q (X , ιBF e₁) a ≡ nothing
lnCnxt-noBF-pos l d NS.lncIdle (BF.sendBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncIdle (BF.receiveBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncIdle (BF.apiBFev _ _ _) = refl
lnCnxt-noBF-pos l d NS.lncIdle (BF.doneBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncWreq (BF.sendBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncWreq (BF.receiveBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncWreq (BF.apiBFev _ _ _) = refl
lnCnxt-noBF-pos l d NS.lncWreq (BF.doneBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncWdone (BF.sendBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncWdone (BF.receiveBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncWdone (BF.apiBFev _ _ _) = refl
lnCnxt-noBF-pos l d NS.lncWdone (BF.doneBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncBusy (BF.sendBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncBusy (BF.receiveBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncBusy (BF.apiBFev _ _ _) = refl
lnCnxt-noBF-pos l d NS.lncBusy (BF.doneBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRann _) (BF.sendBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRann _) (BF.receiveBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRann _) (BF.apiBFev _ _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRann _) (BF.doneBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRoff _) (BF.sendBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRoff _) (BF.receiveBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRoff _) (BF.apiBFev _ _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRoff _) (BF.doneBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRtxs _) (BF.sendBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRtxs _) (BF.receiveBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRtxs _) (BF.apiBFev _ _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRtxs _) (BF.doneBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRvot _) (BF.sendBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRvot _) (BF.receiveBF _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRvot _) (BF.apiBFev _ _ _) = refl
lnCnxt-noBF-pos l d (NS.lncRvot _) (BF.doneBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncTerm (BF.sendBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncTerm (BF.receiveBF _ _) = refl
lnCnxt-noBF-pos l d NS.lncTerm (BF.apiBFev _ _ _) = refl
lnCnxt-noBF-pos l d NS.lncTerm (BF.doneBF _ _) = refl

lnSnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.LNsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.lnSnxt l d q (X , ιCS e₁) a ≡ nothing
lnSnxt-noCS-pos l d NS.lnsIdle (CS.sendCS _ _) = refl
lnSnxt-noCS-pos l d NS.lnsIdle (CS.receiveCS _ _) = refl
lnSnxt-noCS-pos l d NS.lnsIdle (CS.apiCSev _ _ _) = refl
lnSnxt-noCS-pos l d NS.lnsIdle (CS.doneCS _ _) = refl
lnSnxt-noCS-pos l d NS.lnsBusy (CS.sendCS _ _) = refl
lnSnxt-noCS-pos l d NS.lnsBusy (CS.receiveCS _ _) = refl
lnSnxt-noCS-pos l d NS.lnsBusy (CS.apiCSev _ _ _) = refl
lnSnxt-noCS-pos l d NS.lnsBusy (CS.doneCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWann _) (CS.sendCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWann _) (CS.receiveCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWann _) (CS.apiCSev _ _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWann _) (CS.doneCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWoff _) (CS.sendCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWoff _) (CS.receiveCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWoff _) (CS.apiCSev _ _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWoff _) (CS.doneCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWtxs _) (CS.sendCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWtxs _) (CS.receiveCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWtxs _) (CS.apiCSev _ _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWtxs _) (CS.doneCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWvot _) (CS.sendCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWvot _) (CS.receiveCS _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWvot _) (CS.apiCSev _ _ _) = refl
lnSnxt-noCS-pos l d (NS.lnsWvot _) (CS.doneCS _ _) = refl
lnSnxt-noCS-pos l d NS.lnsDone (CS.sendCS _ _) = refl
lnSnxt-noCS-pos l d NS.lnsDone (CS.receiveCS _ _) = refl
lnSnxt-noCS-pos l d NS.lnsDone (CS.apiCSev _ _ _) = refl
lnSnxt-noCS-pos l d NS.lnsDone (CS.doneCS _ _) = refl
lnSnxt-noCS-pos l d NS.lnsTerm (CS.sendCS _ _) = refl
lnSnxt-noCS-pos l d NS.lnsTerm (CS.receiveCS _ _) = refl
lnSnxt-noCS-pos l d NS.lnsTerm (CS.apiCSev _ _ _) = refl
lnSnxt-noCS-pos l d NS.lnsTerm (CS.doneCS _ _) = refl

lnSnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.LNsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.lnSnxt l d q (X , ιBF e₁) a ≡ nothing
lnSnxt-noBF-pos l d NS.lnsIdle (BF.sendBF _ _) = refl
lnSnxt-noBF-pos l d NS.lnsIdle (BF.receiveBF _ _) = refl
lnSnxt-noBF-pos l d NS.lnsIdle (BF.apiBFev _ _ _) = refl
lnSnxt-noBF-pos l d NS.lnsIdle (BF.doneBF _ _) = refl
lnSnxt-noBF-pos l d NS.lnsBusy (BF.sendBF _ _) = refl
lnSnxt-noBF-pos l d NS.lnsBusy (BF.receiveBF _ _) = refl
lnSnxt-noBF-pos l d NS.lnsBusy (BF.apiBFev _ _ _) = refl
lnSnxt-noBF-pos l d NS.lnsBusy (BF.doneBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWann _) (BF.sendBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWann _) (BF.receiveBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWann _) (BF.apiBFev _ _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWann _) (BF.doneBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWoff _) (BF.sendBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWoff _) (BF.receiveBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWoff _) (BF.apiBFev _ _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWoff _) (BF.doneBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWtxs _) (BF.sendBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWtxs _) (BF.receiveBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWtxs _) (BF.apiBFev _ _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWtxs _) (BF.doneBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWvot _) (BF.sendBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWvot _) (BF.receiveBF _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWvot _) (BF.apiBFev _ _ _) = refl
lnSnxt-noBF-pos l d (NS.lnsWvot _) (BF.doneBF _ _) = refl
lnSnxt-noBF-pos l d NS.lnsDone (BF.sendBF _ _) = refl
lnSnxt-noBF-pos l d NS.lnsDone (BF.receiveBF _ _) = refl
lnSnxt-noBF-pos l d NS.lnsDone (BF.apiBFev _ _ _) = refl
lnSnxt-noBF-pos l d NS.lnsDone (BF.doneBF _ _) = refl
lnSnxt-noBF-pos l d NS.lnsTerm (BF.sendBF _ _) = refl
lnSnxt-noBF-pos l d NS.lnsTerm (BF.receiveBF _ _) = refl
lnSnxt-noBF-pos l d NS.lnsTerm (BF.apiBFev _ _ _) = refl
lnSnxt-noBF-pos l d NS.lnsTerm (BF.doneBF _ _) = refl

lfCnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.LFcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.lfCnxt l d q (X , ιCS e₁) a ≡ nothing
lfCnxt-noCS-pos l d NS.lfcIdle (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcIdle (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcIdle (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d NS.lfcIdle (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWblk _) (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWblk _) (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWblk _) (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWblk _) (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWtxs _) (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWtxs _) (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWtxs _) (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWtxs _) (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWvot _) (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWvot _) (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWvot _) (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWvot _) (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWrng _) (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWrng _) (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWrng _) (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcWrng _) (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcWdone (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcWdone (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcWdone (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d NS.lfcWdone (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcBlk (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcBlk (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcBlk (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d NS.lfcBlk (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcBtx (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcBtx (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcBtx (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d NS.lfcBtx (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcVot (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcVot (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcVot (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d NS.lfcVot (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcRng (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcRng (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcRng (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d NS.lfcRng (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRblk _) (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRblk _) (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRblk _) (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRblk _) (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRbtx _) (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRbtx _) (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRbtx _) (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRbtx _) (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRvot _) (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRvot _) (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRvot _) (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRvot _) (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRnextRng _) (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRnextRng _) (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRnextRng _) (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRnextRng _) (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRlastRng _) (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRlastRng _) (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRlastRng _) (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d (NS.lfcRlastRng _) (CS.doneCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcTerm (CS.sendCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcTerm (CS.receiveCS _ _) = refl
lfCnxt-noCS-pos l d NS.lfcTerm (CS.apiCSev _ _ _) = refl
lfCnxt-noCS-pos l d NS.lfcTerm (CS.doneCS _ _) = refl

lfCnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.LFcPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.lfCnxt l d q (X , ιBF e₁) a ≡ nothing
lfCnxt-noBF-pos l d NS.lfcIdle (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcIdle (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcIdle (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d NS.lfcIdle (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWblk _) (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWblk _) (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWblk _) (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWblk _) (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWtxs _) (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWtxs _) (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWtxs _) (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWtxs _) (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWvot _) (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWvot _) (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWvot _) (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWvot _) (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWrng _) (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWrng _) (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWrng _) (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcWrng _) (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcWdone (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcWdone (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcWdone (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d NS.lfcWdone (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcBlk (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcBlk (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcBlk (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d NS.lfcBlk (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcBtx (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcBtx (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcBtx (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d NS.lfcBtx (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcVot (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcVot (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcVot (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d NS.lfcVot (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcRng (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcRng (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcRng (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d NS.lfcRng (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRblk _) (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRblk _) (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRblk _) (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRblk _) (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRbtx _) (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRbtx _) (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRbtx _) (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRbtx _) (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRvot _) (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRvot _) (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRvot _) (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRvot _) (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRnextRng _) (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRnextRng _) (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRnextRng _) (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRnextRng _) (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRlastRng _) (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRlastRng _) (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRlastRng _) (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d (NS.lfcRlastRng _) (BF.doneBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcTerm (BF.sendBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcTerm (BF.receiveBF _ _) = refl
lfCnxt-noBF-pos l d NS.lfcTerm (BF.apiBFev _ _ _) = refl
lfCnxt-noBF-pos l d NS.lfcTerm (BF.doneBF _ _) = refl

lfSnxt-noCS-pos : (l : Link) (d : Dir) (q : NS.LFsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → NS.lfSnxt l d q (X , ιCS e₁) a ≡ nothing
lfSnxt-noCS-pos l d NS.lfsIdle (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsIdle (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsIdle (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d NS.lfsIdle (CS.doneCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsBlk (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsBlk (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsBlk (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d NS.lfsBlk (CS.doneCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsBtx (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsBtx (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsBtx (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d NS.lfsBtx (CS.doneCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsVot (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsVot (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsVot (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d NS.lfsVot (CS.doneCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsRng (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsRng (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsRng (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d NS.lfsRng (CS.doneCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsDone (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsDone (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsDone (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d NS.lfsDone (CS.doneCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWblk _) (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWblk _) (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWblk _) (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWblk _) (CS.doneCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWtxs _) (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWtxs _) (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWtxs _) (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWtxs _) (CS.doneCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWvot _) (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWvot _) (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWvot _) (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWvot _) (CS.doneCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWnext _) (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWnext _) (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWnext _) (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWnext _) (CS.doneCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWlast _) (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWlast _) (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWlast _) (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d (NS.lfsWlast _) (CS.doneCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsTerm (CS.sendCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsTerm (CS.receiveCS _ _) = refl
lfSnxt-noCS-pos l d NS.lfsTerm (CS.apiCSev _ _ _) = refl
lfSnxt-noCS-pos l d NS.lfsTerm (CS.doneCS _ _) = refl

lfSnxt-noBF-pos : (l : Link) (d : Dir) (q : NS.LFsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → NS.lfSnxt l d q (X , ιBF e₁) a ≡ nothing
lfSnxt-noBF-pos l d NS.lfsIdle (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsIdle (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsIdle (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d NS.lfsIdle (BF.doneBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsBlk (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsBlk (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsBlk (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d NS.lfsBlk (BF.doneBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsBtx (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsBtx (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsBtx (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d NS.lfsBtx (BF.doneBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsVot (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsVot (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsVot (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d NS.lfsVot (BF.doneBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsRng (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsRng (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsRng (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d NS.lfsRng (BF.doneBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsDone (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsDone (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsDone (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d NS.lfsDone (BF.doneBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWblk _) (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWblk _) (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWblk _) (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWblk _) (BF.doneBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWtxs _) (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWtxs _) (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWtxs _) (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWtxs _) (BF.doneBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWvot _) (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWvot _) (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWvot _) (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWvot _) (BF.doneBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWnext _) (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWnext _) (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWnext _) (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWnext _) (BF.doneBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWlast _) (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWlast _) (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWlast _) (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d (NS.lfsWlast _) (BF.doneBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsTerm (BF.sendBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsTerm (BF.receiveBF _ _) = refl
lfSnxt-noBF-pos l d NS.lfsTerm (BF.apiBFev _ _ _) = refl
lfSnxt-noBF-pos l d NS.lfsTerm (BF.doneBF _ _) = refl

absLNc-noCS : (l : Link) (d : Dir) (q : LNcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absLNc l d q) (ιCS e₁) a
absLNc-noCS l d q e₁ {a} with NS.lnCfin (coarsenLNc q) in fEq
... | true  = viewV→noOffer (absLNc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d })
                   (coarsenLNc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d })
                   (coarsenLNc q) {e = ιCS e₁} {a = a} fEq (lnCnxt-noCS-pos l d (coarsenLNc q) e₁ {a = a}))

absLNc-noBF : (l : Link) (d : Dir) (q : LNcPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absLNc l d q) (ιBF e₁) a
absLNc-noBF l d q e₁ {a} with NS.lnCfin (coarsenLNc q) in fEq
... | true  = viewV→noOffer (absLNc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d })
                   (coarsenLNc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d })
                   (coarsenLNc q) {e = ιBF e₁} {a = a} fEq (lnCnxt-noBF-pos l d (coarsenLNc q) e₁ {a = a}))

absLNs-noCS : (l : Link) (d : Dir) (q : LNsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absLNs l d q) (ιCS e₁) a
absLNs-noCS l d q e₁ {a} with NS.lnSfin (coarsenLNs q) in fEq
... | true  = viewV→noOffer (absLNs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d })
                   (coarsenLNs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d })
                   (coarsenLNs q) {e = ιCS e₁} {a = a} fEq (lnSnxt-noCS-pos l d (coarsenLNs q) e₁ {a = a}))

absLNs-noBF : (l : Link) (d : Dir) (q : LNsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absLNs l d q) (ιBF e₁) a
absLNs-noBF l d q e₁ {a} with NS.lnSfin (coarsenLNs q) in fEq
... | true  = viewV→noOffer (absLNs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d })
                   (coarsenLNs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d })
                   (coarsenLNs q) {e = ιBF e₁} {a = a} fEq (lnSnxt-noBF-pos l d (coarsenLNs q) e₁ {a = a}))

absLFc-noCS : (l : Link) (d : Dir) (q : LFcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absLFc l d q) (ιCS e₁) a
absLFc-noCS l d q e₁ {a} with NS.lfCfin (coarsenLFc q) in fEq
... | true  = viewV→noOffer (absLFc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d })
                   (coarsenLFc q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFc l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d })
                   (coarsenLFc q) {e = ιCS e₁} {a = a} fEq (lfCnxt-noCS-pos l d (coarsenLFc q) e₁ {a = a}))

absLFc-noBF : (l : Link) (d : Dir) (q : LFcPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absLFc l d q) (ιBF e₁) a
absLFc-noBF l d q e₁ {a} with NS.lfCfin (coarsenLFc q) in fEq
... | true  = viewV→noOffer (absLFc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d })
                   (coarsenLFc q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFc l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d })
                   (coarsenLFc q) {e = ιBF e₁} {a = a} fEq (lfCnxt-noBF-pos l d (coarsenLFc q) e₁ {a = a}))

absLFs-noCS : (l : Link) (d : Dir) (q : LFsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (absLFs l d q) (ιCS e₁) a
absLFs-noCS l d q e₁ {a} with NS.lfSfin (coarsenLFs q) in fEq
... | true  = viewV→noOffer (absLFs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d })
                   (coarsenLFs q) {e = ιCS e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFs l d q) {e = ιCS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d })
                   (coarsenLFs q) {e = ιCS e₁} {a = a} fEq (lfSnxt-noCS-pos l d (coarsenLFs q) e₁ {a = a}))

absLFs-noBF : (l : Link) (d : Dir) (q : LFsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (absLFs l d q) (ιBF e₁) a
absLFs-noBF l d q e₁ {a} with NS.lfSfin (coarsenLFs q) in fEq
... | true  = viewV→noOffer (absLFs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d })
                   (coarsenLFs q) {e = ιBF e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFs l d q) {e = ιBF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d })
                   (coarsenLFs q) {e = ιBF e₁} {a = a} fEq (lfSnxt-noBF-pos l d (coarsenLFs q) e₁ {a = a}))


-- CS-client advances: rebuild the abstract bundle step (dir cl, csEvDir e₁≡cl)
absBundle-CSc-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {qcc′ : CScPos}
  → cl ≢ sv → csEvDir e₁ ≡ cl
  → absCSc l cl qcc ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absCSc l cl qcc′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absBundleG l cl sv qcc′ qcs qbc qbs ip
absBundle-CSc-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-L (absCSc l cl qcc) _ astep
        (⦀-viewV-nothing (absCSs l sv qcs) _ (absCSs-dir-noBoth l sv qcs e₁ ¬sv)
          (SStep.⦀-noOffer (absBFc l cl qbc) _ (absBFc-noCS l cl qbc e₁)
            (SStep.⦀-noOffer (absBFs l sv qbs) _ (absBFs-noCS l sv qbs e₁)
              (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noCS l cl (tsc ip) e₁)
                (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noCS l sv (tss ip) e₁)
                  (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noCS l cl (lnc ip) e₁)
                    (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noCS l sv (lns ip) e₁)
                      (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
                        (absLFc-noCS l cl (lfc ip) e₁) (absLFs-noCS l sv (lfs ip) e₁))))))))))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noCS l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noCS l cl (kac ip) e₁))
  where ¬sv : csEvDir e₁ ≢ sv
        ¬sv q = cl≢sv (trans (sym eqd) q)

-- CS-server advances: rebuild the abstract bundle step (dir sv, csEvDir e₁≡sv)
absBundle-CSs-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {qcs′ : CSsPos}
  → cl ≢ sv → csEvDir e₁ ≡ sv
  → absCSs l sv qcs ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absCSs l sv qcs′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absBundleG l cl sv qcc qcs′ qbc qbs ip
absBundle-CSs-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-L (absCSs l sv qcs) _ astep
          (⦀-viewV-nothing (absBFc l cl qbc) _ (absBFc-noCS l cl qbc e₁)
            (SStep.⦀-noOffer (absBFs l sv qbs) _ (absBFs-noCS l sv qbs e₁)
              (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noCS l cl (tsc ip) e₁)
                (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noCS l sv (tss ip) e₁)
                  (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noCS l cl (lnc ip) e₁)
                    (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noCS l sv (lns ip) e₁)
                      (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
                        (absLFc-noCS l cl (lfc ip) e₁) (absLFs-noCS l sv (lfs ip) e₁)))))))))
        (noOffer→viewV (absCSc l cl qcc) (absCSc-dir-noBoth l cl qcc e₁ ¬cl)))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noCS l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noCS l cl (kac ip) e₁))
  where ¬cl : csEvDir e₁ ≢ cl
        ¬cl q = cl≢sv (sym (trans (sym eqd) q))

-- BF-client advances: rebuild the abstract bundle step (dir cl, bfEvDir e₁≡cl)
absBundle-BFc-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {qbc′ : BFcPos}
  → cl ≢ sv → bfEvDir e₁ ≡ cl
  → absBFc l cl qbc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBFc l cl qbc′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc′ qbs ip
absBundle-BFc-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-R (absCSs l sv qcs) _
          (SStep.⦀-ev-L (absBFc l cl qbc) _ astep
            (⦀-viewV-nothing (absBFs l sv qbs) _ (absBFs-dir-noBoth l sv qbs e₁ ¬sv)
              (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁)
                (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁)
                  (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁)
                    (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁)
                      (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
                        (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁))))))))
          (noOffer→viewV (absCSs l sv qcs) (absCSs-noBF l sv qcs e₁)))
        (noOffer→viewV (absCSc l cl qcc) (absCSc-noBF l cl qcc e₁)))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noBF l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noBF l cl (kac ip) e₁))
  where ¬sv : bfEvDir e₁ ≢ sv
        ¬sv q = cl≢sv (trans (sym eqd) q)

-- BF-server advances: rebuild the abstract bundle step (dir sv, bfEvDir e₁≡sv)
absBundle-BFs-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {qbs′ : BFsPos}
  → cl ≢ sv → bfEvDir e₁ ≡ sv
  → absBFs l sv qbs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBFs l sv qbs′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc qbs′ ip
absBundle-BFs-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-R (absCSs l sv qcs) _
          (SStep.⦀-ev-R (absBFc l cl qbc) _
            (SStep.⦀-ev-L (absBFs l sv qbs) _ astep
              (⦀-viewV-nothing (absTSc l cl (tsc ip)) _ (absTSc-noBF l cl (tsc ip) e₁)
                (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noBF l sv (tss ip) e₁)
                  (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noBF l cl (lnc ip) e₁)
                    (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noBF l sv (lns ip) e₁)
                      (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
                        (absLFc-noBF l cl (lfc ip) e₁) (absLFs-noBF l sv (lfs ip) e₁)))))))
            (noOffer→viewV (absBFc l cl qbc) (absBFc-dir-noBoth l cl qbc e₁ ¬cl)))
          (noOffer→viewV (absCSs l sv qcs) (absCSs-noBF l sv qcs e₁)))
        (noOffer→viewV (absCSc l cl qcc) (absCSc-noBF l cl qcc e₁)))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noBF l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noBF l cl (kac ip) e₁))
  where ¬cl : bfEvDir e₁ ≢ cl
        ¬cl q = cl≢sv (sym (trans (sym eqd) q))

------------------------------------------------------------------------
-- GAP-B step 3 (concrete-bundle leaves) — the CONCRETE-side non-offers the
-- DOWNWARD peel of `bundle-{CS,BF}-ev-inv` consumes to refute the wrong peers:
--   · the same-protocol opposite-role driven peer at the WRONG direction
--     (`dec*-dir-noOffer`, dual of `abs*-dir-noBoth`, via `*-ev-dir`+`apiDir-inj`);
--   · the opposite-PROTOCOL driven peer at ANY image event (`dec*-no*gen`, via
--     `RenNO.renameMap-noOffer-χ` + the committed cross-preimage `ιX⁻¹∘ιY`).
------------------------------------------------------------------------

-- RenNO instances for the two driven protocols (for the general cross-protocol
-- non-offers; `CSNO`/`BFNO` above are RenTC reflect modules, not RenNO)
module CSNOff = SStep.RenNO ιCS ιCS⁻¹ ιCS-linv
module BFNOff = SStep.RenNO ιBF ιBF⁻¹ ιBF-linv

-- concrete CS-client never fires a wrong-direction CS-image event
decCSc-dir-noOffer : (l : Link) (d : Dir) (pos : CScPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ d → ¬ IoOffers (decCSc l d pos) (ιCS e₁) a
decCSc-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (csc-ev-dir l d pos step) (csApiDir e₁)))

-- concrete CS-server never fires a wrong-direction CS-image event
decCSs-dir-noOffer : (l : Link) (d : Dir) (pos : CSsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → csEvDir e₁ ≢ d → ¬ IoOffers (decCSs l d pos) (ιCS e₁) a
decCSs-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (css-ev-dir l d pos step) (csApiDir e₁)))

-- concrete BF-client never fires a wrong-direction BF-image event
decBFc-dir-noOffer : (l : Link) (d : Dir) (pos : BFcPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ d → ¬ IoOffers (decBFc l d pos) (ιBF e₁) a
decBFc-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (bfc-ev-dir l d pos step) (bfApiDir e₁)))

-- concrete BF-server never fires a wrong-direction BF-image event
decBFs-dir-noOffer : (l : Link) (d : Dir) (pos : BFsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → bfEvDir e₁ ≢ d → ¬ IoOffers (decBFs l d pos) (ιBF e₁) a
decBFs-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (bfs-ev-dir l d pos step) (bfApiDir e₁)))

-- concrete BF peers never fire ANY CS-image event (opposite protocol)
decBFc-noCSgen : (l : Link) (d : Dir) (pos : BFcPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (decBFc l d pos) (ιCS e₁) a
decBFc-noCSgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFc-src l d pos) (ιBF⁻¹∘ιCS e₁)
decBFs-noCSgen : (l : Link) (d : Dir) (pos : BFsPos) {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (decBFs l d pos) (ιCS e₁) a
decBFs-noCSgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFs-src l d pos) (ιBF⁻¹∘ιCS e₁)

-- concrete CS peers never fire ANY BF-image event (opposite protocol)
decCSc-noBFgen : (l : Link) (d : Dir) (pos : CScPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (decCSc l d pos) (ιBF e₁) a
decCSc-noBFgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSc-src l d pos) (ιCS⁻¹∘ιBF e₁)
decCSs-noBFgen : (l : Link) (d : Dir) (pos : CSsPos) {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (decCSs l d pos) (ιBF e₁) a
decCSs-noBFgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSs-src l d pos) (ιCS⁻¹∘ιBF e₁)


------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER B — KeepAlive channel abstract-side non-offers.
-- Each foreign abstract table (CS/BF/TS/LN/LF) gives `nothing` at every
-- position for a KA-image event (own-channel-only edges); wrappers lift that
-- to `¬ IoOffers`.  Transformed 1:1 from the `-noBF`/`-noCS` twins.
------------------------------------------------------------------------

csCnxt-noKA : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → NS.csCnxt l d q (X , ιKA e₁) a ≡ nothing
csCnxt-noKA l d NS.ccIdle (KA.sendKA _ _) = refl
csCnxt-noKA l d NS.ccIdle (KA.receiveKA _ _) = refl
csCnxt-noKA l d NS.ccIdle (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d NS.ccIdle (KA.doneKA _ _) = refl
csCnxt-noKA l d NS.ccWreq (KA.sendKA _ _) = refl
csCnxt-noKA l d NS.ccWreq (KA.receiveKA _ _) = refl
csCnxt-noKA l d NS.ccWreq (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d NS.ccWreq (KA.doneKA _ _) = refl
csCnxt-noKA l d NS.ccAwait (KA.sendKA _ _) = refl
csCnxt-noKA l d NS.ccAwait (KA.receiveKA _ _) = refl
csCnxt-noKA l d NS.ccAwait (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d NS.ccAwait (KA.doneKA _ _) = refl
csCnxt-noKA l d (NS.ccWfi _) (KA.sendKA _ _) = refl
csCnxt-noKA l d (NS.ccWfi _) (KA.receiveKA _ _) = refl
csCnxt-noKA l d (NS.ccWfi _) (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d (NS.ccWfi _) (KA.doneKA _ _) = refl
csCnxt-noKA l d NS.ccInt (KA.sendKA _ _) = refl
csCnxt-noKA l d NS.ccInt (KA.receiveKA _ _) = refl
csCnxt-noKA l d NS.ccInt (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d NS.ccInt (KA.doneKA _ _) = refl
csCnxt-noKA l d NS.ccWdone (KA.sendKA _ _) = refl
csCnxt-noKA l d NS.ccWdone (KA.receiveKA _ _) = refl
csCnxt-noKA l d NS.ccWdone (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d NS.ccWdone (KA.doneKA _ _) = refl
csCnxt-noKA l d NS.ccMust (KA.sendKA _ _) = refl
csCnxt-noKA l d NS.ccMust (KA.receiveKA _ _) = refl
csCnxt-noKA l d NS.ccMust (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d NS.ccMust (KA.doneKA _ _) = refl
csCnxt-noKA l d (NS.ccArf _) (KA.sendKA _ _) = refl
csCnxt-noKA l d (NS.ccArf _) (KA.receiveKA _ _) = refl
csCnxt-noKA l d (NS.ccArf _) (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d (NS.ccArf _) (KA.doneKA _ _) = refl
csCnxt-noKA l d (NS.ccArb _) (KA.sendKA _ _) = refl
csCnxt-noKA l d (NS.ccArb _) (KA.receiveKA _ _) = refl
csCnxt-noKA l d (NS.ccArb _) (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d (NS.ccArb _) (KA.doneKA _ _) = refl
csCnxt-noKA l d (NS.ccAif _) (KA.sendKA _ _) = refl
csCnxt-noKA l d (NS.ccAif _) (KA.receiveKA _ _) = refl
csCnxt-noKA l d (NS.ccAif _) (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d (NS.ccAif _) (KA.doneKA _ _) = refl
csCnxt-noKA l d (NS.ccAin _) (KA.sendKA _ _) = refl
csCnxt-noKA l d (NS.ccAin _) (KA.receiveKA _ _) = refl
csCnxt-noKA l d (NS.ccAin _) (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d (NS.ccAin _) (KA.doneKA _ _) = refl
csCnxt-noKA l d NS.ccTerm (KA.sendKA _ _) = refl
csCnxt-noKA l d NS.ccTerm (KA.receiveKA _ _) = refl
csCnxt-noKA l d NS.ccTerm (KA.apiKAev _ _ _) = refl
csCnxt-noKA l d NS.ccTerm (KA.doneKA _ _) = refl

csSnxt-noKA : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → NS.csSnxt l d q (X , ιKA e₁) a ≡ nothing
csSnxt-noKA l d NS.csIdle (KA.sendKA _ _) = refl
csSnxt-noKA l d NS.csIdle (KA.receiveKA _ _) = refl
csSnxt-noKA l d NS.csIdle (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d NS.csIdle (KA.doneKA _ _) = refl
csSnxt-noKA l d NS.csAreq (KA.sendKA _ _) = refl
csSnxt-noKA l d NS.csAreq (KA.receiveKA _ _) = refl
csSnxt-noKA l d NS.csAreq (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d NS.csAreq (KA.doneKA _ _) = refl
csSnxt-noKA l d NS.csCanAwait (KA.sendKA _ _) = refl
csSnxt-noKA l d NS.csCanAwait (KA.receiveKA _ _) = refl
csSnxt-noKA l d NS.csCanAwait (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d NS.csCanAwait (KA.doneKA _ _) = refl
csSnxt-noKA l d (NS.csAfi _) (KA.sendKA _ _) = refl
csSnxt-noKA l d (NS.csAfi _) (KA.receiveKA _ _) = refl
csSnxt-noKA l d (NS.csAfi _) (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d (NS.csAfi _) (KA.doneKA _ _) = refl
csSnxt-noKA l d NS.csInt (KA.sendKA _ _) = refl
csSnxt-noKA l d NS.csInt (KA.receiveKA _ _) = refl
csSnxt-noKA l d NS.csInt (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d NS.csInt (KA.doneKA _ _) = refl
csSnxt-noKA l d NS.csDdone (KA.sendKA _ _) = refl
csSnxt-noKA l d NS.csDdone (KA.receiveKA _ _) = refl
csSnxt-noKA l d NS.csDdone (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d NS.csDdone (KA.doneKA _ _) = refl
csSnxt-noKA l d NS.csMust (KA.sendKA _ _) = refl
csSnxt-noKA l d NS.csMust (KA.receiveKA _ _) = refl
csSnxt-noKA l d NS.csMust (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d NS.csMust (KA.doneKA _ _) = refl
csSnxt-noKA l d (NS.csWrf _) (KA.sendKA _ _) = refl
csSnxt-noKA l d (NS.csWrf _) (KA.receiveKA _ _) = refl
csSnxt-noKA l d (NS.csWrf _) (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d (NS.csWrf _) (KA.doneKA _ _) = refl
csSnxt-noKA l d (NS.csWrb _) (KA.sendKA _ _) = refl
csSnxt-noKA l d (NS.csWrb _) (KA.receiveKA _ _) = refl
csSnxt-noKA l d (NS.csWrb _) (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d (NS.csWrb _) (KA.doneKA _ _) = refl
csSnxt-noKA l d NS.csWar (KA.sendKA _ _) = refl
csSnxt-noKA l d NS.csWar (KA.receiveKA _ _) = refl
csSnxt-noKA l d NS.csWar (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d NS.csWar (KA.doneKA _ _) = refl
csSnxt-noKA l d (NS.csWif _) (KA.sendKA _ _) = refl
csSnxt-noKA l d (NS.csWif _) (KA.receiveKA _ _) = refl
csSnxt-noKA l d (NS.csWif _) (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d (NS.csWif _) (KA.doneKA _ _) = refl
csSnxt-noKA l d (NS.csWin _) (KA.sendKA _ _) = refl
csSnxt-noKA l d (NS.csWin _) (KA.receiveKA _ _) = refl
csSnxt-noKA l d (NS.csWin _) (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d (NS.csWin _) (KA.doneKA _ _) = refl
csSnxt-noKA l d NS.csTerm (KA.sendKA _ _) = refl
csSnxt-noKA l d NS.csTerm (KA.receiveKA _ _) = refl
csSnxt-noKA l d NS.csTerm (KA.apiKAev _ _ _) = refl
csSnxt-noKA l d NS.csTerm (KA.doneKA _ _) = refl

bfCnxt-noKA : (l : Link) (d : Dir) (q : NS.BFcPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → NS.bfCnxt l d q (X , ιKA e₁) a ≡ nothing
bfCnxt-noKA l d NS.bcIdle (KA.sendKA _ _) = refl
bfCnxt-noKA l d NS.bcIdle (KA.receiveKA _ _) = refl
bfCnxt-noKA l d NS.bcIdle (KA.apiKAev _ _ _) = refl
bfCnxt-noKA l d NS.bcIdle (KA.doneKA _ _) = refl
bfCnxt-noKA l d (NS.bcWrr _) (KA.sendKA _ _) = refl
bfCnxt-noKA l d (NS.bcWrr _) (KA.receiveKA _ _) = refl
bfCnxt-noKA l d (NS.bcWrr _) (KA.apiKAev _ _ _) = refl
bfCnxt-noKA l d (NS.bcWrr _) (KA.doneKA _ _) = refl
bfCnxt-noKA l d NS.bcBusy (KA.sendKA _ _) = refl
bfCnxt-noKA l d NS.bcBusy (KA.receiveKA _ _) = refl
bfCnxt-noKA l d NS.bcBusy (KA.apiKAev _ _ _) = refl
bfCnxt-noKA l d NS.bcBusy (KA.doneKA _ _) = refl
bfCnxt-noKA l d NS.bcWcd (KA.sendKA _ _) = refl
bfCnxt-noKA l d NS.bcWcd (KA.receiveKA _ _) = refl
bfCnxt-noKA l d NS.bcWcd (KA.apiKAev _ _ _) = refl
bfCnxt-noKA l d NS.bcWcd (KA.doneKA _ _) = refl
bfCnxt-noKA l d NS.bcStream (KA.sendKA _ _) = refl
bfCnxt-noKA l d NS.bcStream (KA.receiveKA _ _) = refl
bfCnxt-noKA l d NS.bcStream (KA.apiKAev _ _ _) = refl
bfCnxt-noKA l d NS.bcStream (KA.doneKA _ _) = refl
bfCnxt-noKA l d (NS.bcAblk _) (KA.sendKA _ _) = refl
bfCnxt-noKA l d (NS.bcAblk _) (KA.receiveKA _ _) = refl
bfCnxt-noKA l d (NS.bcAblk _) (KA.apiKAev _ _ _) = refl
bfCnxt-noKA l d (NS.bcAblk _) (KA.doneKA _ _) = refl
bfCnxt-noKA l d NS.bcTerm (KA.sendKA _ _) = refl
bfCnxt-noKA l d NS.bcTerm (KA.receiveKA _ _) = refl
bfCnxt-noKA l d NS.bcTerm (KA.apiKAev _ _ _) = refl
bfCnxt-noKA l d NS.bcTerm (KA.doneKA _ _) = refl

bfSnxt-noKA : (l : Link) (d : Dir) (q : NS.BFsPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → NS.bfSnxt l d q (X , ιKA e₁) a ≡ nothing
bfSnxt-noKA l d NS.bsIdle (KA.sendKA _ _) = refl
bfSnxt-noKA l d NS.bsIdle (KA.receiveKA _ _) = refl
bfSnxt-noKA l d NS.bsIdle (KA.apiKAev _ _ _) = refl
bfSnxt-noKA l d NS.bsIdle (KA.doneKA _ _) = refl
bfSnxt-noKA l d (NS.bsAreq _) (KA.sendKA _ _) = refl
bfSnxt-noKA l d (NS.bsAreq _) (KA.receiveKA _ _) = refl
bfSnxt-noKA l d (NS.bsAreq _) (KA.apiKAev _ _ _) = refl
bfSnxt-noKA l d (NS.bsAreq _) (KA.doneKA _ _) = refl
bfSnxt-noKA l d NS.bsBusy (KA.sendKA _ _) = refl
bfSnxt-noKA l d NS.bsBusy (KA.receiveKA _ _) = refl
bfSnxt-noKA l d NS.bsBusy (KA.apiKAev _ _ _) = refl
bfSnxt-noKA l d NS.bsBusy (KA.doneKA _ _) = refl
bfSnxt-noKA l d NS.bsDdone (KA.sendKA _ _) = refl
bfSnxt-noKA l d NS.bsDdone (KA.receiveKA _ _) = refl
bfSnxt-noKA l d NS.bsDdone (KA.apiKAev _ _ _) = refl
bfSnxt-noKA l d NS.bsDdone (KA.doneKA _ _) = refl
bfSnxt-noKA l d NS.bsWsb (KA.sendKA _ _) = refl
bfSnxt-noKA l d NS.bsWsb (KA.receiveKA _ _) = refl
bfSnxt-noKA l d NS.bsWsb (KA.apiKAev _ _ _) = refl
bfSnxt-noKA l d NS.bsWsb (KA.doneKA _ _) = refl
bfSnxt-noKA l d NS.bsStream (KA.sendKA _ _) = refl
bfSnxt-noKA l d NS.bsStream (KA.receiveKA _ _) = refl
bfSnxt-noKA l d NS.bsStream (KA.apiKAev _ _ _) = refl
bfSnxt-noKA l d NS.bsStream (KA.doneKA _ _) = refl
bfSnxt-noKA l d NS.bsWnb (KA.sendKA _ _) = refl
bfSnxt-noKA l d NS.bsWnb (KA.receiveKA _ _) = refl
bfSnxt-noKA l d NS.bsWnb (KA.apiKAev _ _ _) = refl
bfSnxt-noKA l d NS.bsWnb (KA.doneKA _ _) = refl
bfSnxt-noKA l d (NS.bsWblk _) (KA.sendKA _ _) = refl
bfSnxt-noKA l d (NS.bsWblk _) (KA.receiveKA _ _) = refl
bfSnxt-noKA l d (NS.bsWblk _) (KA.apiKAev _ _ _) = refl
bfSnxt-noKA l d (NS.bsWblk _) (KA.doneKA _ _) = refl
bfSnxt-noKA l d NS.bsWbd (KA.sendKA _ _) = refl
bfSnxt-noKA l d NS.bsWbd (KA.receiveKA _ _) = refl
bfSnxt-noKA l d NS.bsWbd (KA.apiKAev _ _ _) = refl
bfSnxt-noKA l d NS.bsWbd (KA.doneKA _ _) = refl
bfSnxt-noKA l d NS.bsTerm (KA.sendKA _ _) = refl
bfSnxt-noKA l d NS.bsTerm (KA.receiveKA _ _) = refl
bfSnxt-noKA l d NS.bsTerm (KA.apiKAev _ _ _) = refl
bfSnxt-noKA l d NS.bsTerm (KA.doneKA _ _) = refl

tsCnxt-noKA-pos : (l : Link) (d : Dir) (q : NS.TScPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → NS.tsCnxt l d q (X , ιKA e₁) a ≡ nothing
tsCnxt-noKA-pos l d NS.tcInit (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcInit (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcInit (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d NS.tcInit (KA.doneKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcIdle (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcIdle (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcIdle (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d NS.tcIdle (KA.doneKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcAri (Blocking , _ , _)) (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcAri (NonBlocking , _ , _)) (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcAri (Blocking , _ , _)) (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcAri (NonBlocking , _ , _)) (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcAri (Blocking , _ , _)) (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d (NS.tcAri (NonBlocking , _ , _)) (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d (NS.tcAri (Blocking , _ , _)) (KA.doneKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcAri (NonBlocking , _ , _)) (KA.doneKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcBlk (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcBlk (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcBlk (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d NS.tcBlk (KA.doneKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcNbl (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcNbl (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcNbl (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d NS.tcNbl (KA.doneKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcArt _) (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcArt _) (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcArt _) (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d (NS.tcArt _) (KA.doneKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcTxs (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcTxs (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcTxs (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d NS.tcTxs (KA.doneKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcWri _) (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcWri _) (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcWri _) (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d (NS.tcWri _) (KA.doneKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcWdone (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcWdone (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcWdone (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d NS.tcWdone (KA.doneKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcWrt _) (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcWrt _) (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d (NS.tcWrt _) (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d (NS.tcWrt _) (KA.doneKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcTerm (KA.sendKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcTerm (KA.receiveKA _ _) = refl
tsCnxt-noKA-pos l d NS.tcTerm (KA.apiKAev _ _ _) = refl
tsCnxt-noKA-pos l d NS.tcTerm (KA.doneKA _ _) = refl

tsSnxt-noKA-pos : (l : Link) (d : Dir) (q : NS.TSsPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → NS.tsSnxt l d q (X , ιKA e₁) a ≡ nothing
tsSnxt-noKA-pos l d NS.tsInit (KA.sendKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsInit (KA.receiveKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsInit (KA.apiKAev _ _ _) = refl
tsSnxt-noKA-pos l d NS.tsInit (KA.doneKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsIdle (KA.sendKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsIdle (KA.receiveKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsIdle (KA.apiKAev _ _ _) = refl
tsSnxt-noKA-pos l d NS.tsIdle (KA.doneKA _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWib _) (KA.sendKA _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWib _) (KA.receiveKA _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWib _) (KA.apiKAev _ _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWib _) (KA.doneKA _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWin _) (KA.sendKA _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWin _) (KA.receiveKA _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWin _) (KA.apiKAev _ _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWin _) (KA.doneKA _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWrt _) (KA.sendKA _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWrt _) (KA.receiveKA _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWrt _) (KA.apiKAev _ _ _) = refl
tsSnxt-noKA-pos l d (NS.tsWrt _) (KA.doneKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsBlk (KA.sendKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsBlk (KA.receiveKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsBlk (KA.apiKAev _ _ _) = refl
tsSnxt-noKA-pos l d NS.tsBlk (KA.doneKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsNbl (KA.sendKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsNbl (KA.receiveKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsNbl (KA.apiKAev _ _ _) = refl
tsSnxt-noKA-pos l d NS.tsNbl (KA.doneKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsTxs (KA.sendKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsTxs (KA.receiveKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsTxs (KA.apiKAev _ _ _) = refl
tsSnxt-noKA-pos l d NS.tsTxs (KA.doneKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsDdone (KA.sendKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsDdone (KA.receiveKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsDdone (KA.apiKAev _ _ _) = refl
tsSnxt-noKA-pos l d NS.tsDdone (KA.doneKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsTerm (KA.sendKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsTerm (KA.receiveKA _ _) = refl
tsSnxt-noKA-pos l d NS.tsTerm (KA.apiKAev _ _ _) = refl
tsSnxt-noKA-pos l d NS.tsTerm (KA.doneKA _ _) = refl

lnCnxt-noKA-pos : (l : Link) (d : Dir) (q : NS.LNcPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → NS.lnCnxt l d q (X , ιKA e₁) a ≡ nothing
lnCnxt-noKA-pos l d NS.lncIdle (KA.sendKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncIdle (KA.receiveKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncIdle (KA.apiKAev _ _ _) = refl
lnCnxt-noKA-pos l d NS.lncIdle (KA.doneKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncWreq (KA.sendKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncWreq (KA.receiveKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncWreq (KA.apiKAev _ _ _) = refl
lnCnxt-noKA-pos l d NS.lncWreq (KA.doneKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncWdone (KA.sendKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncWdone (KA.receiveKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncWdone (KA.apiKAev _ _ _) = refl
lnCnxt-noKA-pos l d NS.lncWdone (KA.doneKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncBusy (KA.sendKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncBusy (KA.receiveKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncBusy (KA.apiKAev _ _ _) = refl
lnCnxt-noKA-pos l d NS.lncBusy (KA.doneKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRann _) (KA.sendKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRann _) (KA.receiveKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRann _) (KA.apiKAev _ _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRann _) (KA.doneKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRoff _) (KA.sendKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRoff _) (KA.receiveKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRoff _) (KA.apiKAev _ _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRoff _) (KA.doneKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRtxs _) (KA.sendKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRtxs _) (KA.receiveKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRtxs _) (KA.apiKAev _ _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRtxs _) (KA.doneKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRvot _) (KA.sendKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRvot _) (KA.receiveKA _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRvot _) (KA.apiKAev _ _ _) = refl
lnCnxt-noKA-pos l d (NS.lncRvot _) (KA.doneKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncTerm (KA.sendKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncTerm (KA.receiveKA _ _) = refl
lnCnxt-noKA-pos l d NS.lncTerm (KA.apiKAev _ _ _) = refl
lnCnxt-noKA-pos l d NS.lncTerm (KA.doneKA _ _) = refl

lnSnxt-noKA-pos : (l : Link) (d : Dir) (q : NS.LNsPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → NS.lnSnxt l d q (X , ιKA e₁) a ≡ nothing
lnSnxt-noKA-pos l d NS.lnsIdle (KA.sendKA _ _) = refl
lnSnxt-noKA-pos l d NS.lnsIdle (KA.receiveKA _ _) = refl
lnSnxt-noKA-pos l d NS.lnsIdle (KA.apiKAev _ _ _) = refl
lnSnxt-noKA-pos l d NS.lnsIdle (KA.doneKA _ _) = refl
lnSnxt-noKA-pos l d NS.lnsBusy (KA.sendKA _ _) = refl
lnSnxt-noKA-pos l d NS.lnsBusy (KA.receiveKA _ _) = refl
lnSnxt-noKA-pos l d NS.lnsBusy (KA.apiKAev _ _ _) = refl
lnSnxt-noKA-pos l d NS.lnsBusy (KA.doneKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWann _) (KA.sendKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWann _) (KA.receiveKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWann _) (KA.apiKAev _ _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWann _) (KA.doneKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWoff _) (KA.sendKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWoff _) (KA.receiveKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWoff _) (KA.apiKAev _ _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWoff _) (KA.doneKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWtxs _) (KA.sendKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWtxs _) (KA.receiveKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWtxs _) (KA.apiKAev _ _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWtxs _) (KA.doneKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWvot _) (KA.sendKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWvot _) (KA.receiveKA _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWvot _) (KA.apiKAev _ _ _) = refl
lnSnxt-noKA-pos l d (NS.lnsWvot _) (KA.doneKA _ _) = refl
lnSnxt-noKA-pos l d NS.lnsDone (KA.sendKA _ _) = refl
lnSnxt-noKA-pos l d NS.lnsDone (KA.receiveKA _ _) = refl
lnSnxt-noKA-pos l d NS.lnsDone (KA.apiKAev _ _ _) = refl
lnSnxt-noKA-pos l d NS.lnsDone (KA.doneKA _ _) = refl
lnSnxt-noKA-pos l d NS.lnsTerm (KA.sendKA _ _) = refl
lnSnxt-noKA-pos l d NS.lnsTerm (KA.receiveKA _ _) = refl
lnSnxt-noKA-pos l d NS.lnsTerm (KA.apiKAev _ _ _) = refl
lnSnxt-noKA-pos l d NS.lnsTerm (KA.doneKA _ _) = refl

lfCnxt-noKA-pos : (l : Link) (d : Dir) (q : NS.LFcPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → NS.lfCnxt l d q (X , ιKA e₁) a ≡ nothing
lfCnxt-noKA-pos l d NS.lfcIdle (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcIdle (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcIdle (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d NS.lfcIdle (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWblk _) (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWblk _) (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWblk _) (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWblk _) (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWtxs _) (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWtxs _) (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWtxs _) (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWtxs _) (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWvot _) (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWvot _) (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWvot _) (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWvot _) (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWrng _) (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWrng _) (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWrng _) (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcWrng _) (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcWdone (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcWdone (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcWdone (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d NS.lfcWdone (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcBlk (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcBlk (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcBlk (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d NS.lfcBlk (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcBtx (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcBtx (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcBtx (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d NS.lfcBtx (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcVot (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcVot (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcVot (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d NS.lfcVot (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcRng (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcRng (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcRng (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d NS.lfcRng (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRblk _) (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRblk _) (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRblk _) (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRblk _) (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRbtx _) (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRbtx _) (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRbtx _) (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRbtx _) (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRvot _) (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRvot _) (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRvot _) (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRvot _) (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRnextRng _) (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRnextRng _) (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRnextRng _) (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRnextRng _) (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRlastRng _) (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRlastRng _) (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRlastRng _) (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d (NS.lfcRlastRng _) (KA.doneKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcTerm (KA.sendKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcTerm (KA.receiveKA _ _) = refl
lfCnxt-noKA-pos l d NS.lfcTerm (KA.apiKAev _ _ _) = refl
lfCnxt-noKA-pos l d NS.lfcTerm (KA.doneKA _ _) = refl

lfSnxt-noKA-pos : (l : Link) (d : Dir) (q : NS.LFsPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → NS.lfSnxt l d q (X , ιKA e₁) a ≡ nothing
lfSnxt-noKA-pos l d NS.lfsIdle (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsIdle (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsIdle (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d NS.lfsIdle (KA.doneKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsBlk (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsBlk (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsBlk (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d NS.lfsBlk (KA.doneKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsBtx (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsBtx (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsBtx (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d NS.lfsBtx (KA.doneKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsVot (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsVot (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsVot (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d NS.lfsVot (KA.doneKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsRng (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsRng (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsRng (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d NS.lfsRng (KA.doneKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsDone (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsDone (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsDone (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d NS.lfsDone (KA.doneKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWblk _) (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWblk _) (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWblk _) (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWblk _) (KA.doneKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWtxs _) (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWtxs _) (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWtxs _) (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWtxs _) (KA.doneKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWvot _) (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWvot _) (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWvot _) (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWvot _) (KA.doneKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWnext _) (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWnext _) (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWnext _) (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWnext _) (KA.doneKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWlast _) (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWlast _) (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWlast _) (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d (NS.lfsWlast _) (KA.doneKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsTerm (KA.sendKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsTerm (KA.receiveKA _ _) = refl
lfSnxt-noKA-pos l d NS.lfsTerm (KA.apiKAev _ _ _) = refl
lfSnxt-noKA-pos l d NS.lfsTerm (KA.doneKA _ _) = refl

absCSc-noKA : (l : Link) (d : Dir) (q : CScPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (absCSc l d q) (ιKA e₁) a
absCSc-noKA l d q e₁ {a} with NS.csCfin (coarsenCSc q) in fEq
... | true  = viewV→noOffer (absCSc l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSc l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιKA e₁} {a = a} fEq (csCnxt-noKA l d (coarsenCSc q) e₁ {a = a}))

absCSs-noKA : (l : Link) (d : Dir) (q : CSsPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (absCSs l d q) (ιKA e₁) a
absCSs-noKA l d q e₁ {a} with NS.csSfin (coarsenCSs q) in fEq
... | true  = viewV→noOffer (absCSs l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSs l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιKA e₁} {a = a} fEq (csSnxt-noKA l d (coarsenCSs q) e₁ {a = a}))

absBFc-noKA : (l : Link) (d : Dir) (q : BFcPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (absBFc l d q) (ιKA e₁) a
absBFc-noKA l d q e₁ {a} with NS.bfCfin (coarsenBFc q) in fEq
... | true  = viewV→noOffer (absBFc l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFc l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιKA e₁} {a = a} fEq (bfCnxt-noKA l d (coarsenBFc q) e₁ {a = a}))

absBFs-noKA : (l : Link) (d : Dir) (q : BFsPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (absBFs l d q) (ιKA e₁) a
absBFs-noKA l d q e₁ {a} with NS.bfSfin (coarsenBFs q) in fEq
... | true  = viewV→noOffer (absBFs l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFs l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιKA e₁} {a = a} fEq (bfSnxt-noKA l d (coarsenBFs q) e₁ {a = a}))

absTSc-noKA : (l : Link) (d : Dir) (q : TScPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (absTSc l d q) (ιKA e₁) a
absTSc-noKA l d q e₁ {a} with NS.tsCfin (coarsenTSc q) in fEq
... | true  = viewV→noOffer (absTSc l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSc l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιKA e₁} {a = a} fEq (tsCnxt-noKA-pos l d (coarsenTSc q) e₁ {a = a}))

absTSs-noKA : (l : Link) (d : Dir) (q : TSsPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (absTSs l d q) (ιKA e₁) a
absTSs-noKA l d q e₁ {a} with NS.tsSfin (coarsenTSs q) in fEq
... | true  = viewV→noOffer (absTSs l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSs l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιKA e₁} {a = a} fEq (tsSnxt-noKA-pos l d (coarsenTSs q) e₁ {a = a}))

absLNc-noKA : (l : Link) (d : Dir) (q : LNcPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (absLNc l d q) (ιKA e₁) a
absLNc-noKA l d q e₁ {a} with NS.lnCfin (coarsenLNc q) in fEq
... | true  = viewV→noOffer (absLNc l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d })
                   (coarsenLNc q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNc l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d })
                   (coarsenLNc q) {e = ιKA e₁} {a = a} fEq (lnCnxt-noKA-pos l d (coarsenLNc q) e₁ {a = a}))

absLNs-noKA : (l : Link) (d : Dir) (q : LNsPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (absLNs l d q) (ιKA e₁) a
absLNs-noKA l d q e₁ {a} with NS.lnSfin (coarsenLNs q) in fEq
... | true  = viewV→noOffer (absLNs l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d })
                   (coarsenLNs q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNs l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d })
                   (coarsenLNs q) {e = ιKA e₁} {a = a} fEq (lnSnxt-noKA-pos l d (coarsenLNs q) e₁ {a = a}))

absLFc-noKA : (l : Link) (d : Dir) (q : LFcPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (absLFc l d q) (ιKA e₁) a
absLFc-noKA l d q e₁ {a} with NS.lfCfin (coarsenLFc q) in fEq
... | true  = viewV→noOffer (absLFc l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d })
                   (coarsenLFc q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFc l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d })
                   (coarsenLFc q) {e = ιKA e₁} {a = a} fEq (lfCnxt-noKA-pos l d (coarsenLFc q) e₁ {a = a}))

absLFs-noKA : (l : Link) (d : Dir) (q : LFsPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (absLFs l d q) (ιKA e₁) a
absLFs-noKA l d q e₁ {a} with NS.lfSfin (coarsenLFs q) in fEq
... | true  = viewV→noOffer (absLFs l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d })
                   (coarsenLFs q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFs l d q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d })
                   (coarsenLFs q) {e = ιKA e₁} {a = a} fEq (lfSnxt-noKA-pos l d (coarsenLFs q) e₁ {a = a}))

-- concrete CS/BF peers never fire ANY KA-image event (opposite protocol)
decCSc-noKAgen : (l : Link) (d : Dir) (pos : CScPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (decCSc l d pos) (ιKA e₁) a
decCSc-noKAgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSc-src l d pos) (ιCS⁻¹∘ιKA e₁)
decCSs-noKAgen : (l : Link) (d : Dir) (pos : CSsPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (decCSs l d pos) (ιKA e₁) a
decCSs-noKAgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSs-src l d pos) (ιCS⁻¹∘ιKA e₁)
decBFc-noKAgen : (l : Link) (d : Dir) (pos : BFcPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (decBFc l d pos) (ιKA e₁) a
decBFc-noKAgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFc-src l d pos) (ιBF⁻¹∘ιKA e₁)
decBFs-noKAgen : (l : Link) (d : Dir) (pos : BFsPos) {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (decBFs l d pos) (ιKA e₁) a
decBFs-noKAgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFs-src l d pos) (ιBF⁻¹∘ιKA e₁)

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER C1 — KeepAlive direction table-nothing lemmas
-- (`kaCnxt/kaSnxt-dir-no`), the same-role opposite-direction abstract
-- non-offers (`absKAc/KAs-dir-noBoth`), and the two `⦀`-tail non-offers used
-- by the `bundle-KA-ev-inv` evBoth refutations.  Mirrors CS's dir-no layer.
------------------------------------------------------------------------

-- kaCnxt-dir-no: a wrong-direction KA-image event has no kaCnxt table edge
kaCnxt-dir-no : (l : Link) (d : Dir) (q : NS.KAcPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → kaEvDir e₁ ≢ d → NS.kaCnxt l d q (X , ιKA e₁) a ≡ nothing
-- kcClient : fires apiKA sendKAMsg / sendKADone
kaCnxt-dir-no l d NS.kcClient (KA.apiKAev l' d' sendKAMsg) ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
kaCnxt-dir-no l d NS.kcClient (KA.apiKAev l' d' sendKADone) ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
kaCnxt-dir-no l d NS.kcClient (KA.apiKAev l' d' errCookie) ¬d = refl
kaCnxt-dir-no l d NS.kcClient (KA.apiKAev l' d' recvKACookie) ¬d = refl
kaCnxt-dir-no l d NS.kcClient (KA.sendKA l' d') ¬d = refl
kaCnxt-dir-no l d NS.kcClient (KA.receiveKA l' d') ¬d = refl
kaCnxt-dir-no l d NS.kcClient (KA.doneKA l' d') ¬d = refl
-- kcWmsg c : fires sendKA (input N2N_KeepAlive)
kaCnxt-dir-no l d (NS.kcWmsg c) (KA.sendKA l' d') ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
kaCnxt-dir-no l d (NS.kcWmsg c) (KA.receiveKA l' d') ¬d = refl
kaCnxt-dir-no l d (NS.kcWmsg c) (KA.apiKAev l' d' m) ¬d = refl
kaCnxt-dir-no l d (NS.kcWmsg c) (KA.doneKA l' d') ¬d = refl
-- kcWdone : fires sendKA (input N2N_KeepAlive)
kaCnxt-dir-no l d NS.kcWdone (KA.sendKA l' d') ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
kaCnxt-dir-no l d NS.kcWdone (KA.receiveKA l' d') ¬d = refl
kaCnxt-dir-no l d NS.kcWdone (KA.apiKAev l' d' m) ¬d = refl
kaCnxt-dir-no l d NS.kcWdone (KA.doneKA l' d') ¬d = refl
-- kcAwait c : fires receiveKA (output N2N_KeepAlive) with MsgKeepAliveResponse
kaCnxt-dir-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAliveResponse c')} ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
kaCnxt-dir-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAlive _)} ¬d = refl
kaCnxt-dir-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , keepAlive MsgKADone} ¬d = refl
kaCnxt-dir-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , chainSync _} ¬d = refl
kaCnxt-dir-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , blockFetch _} ¬d = refl
kaCnxt-dir-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , txSubmission _} ¬d = refl
kaCnxt-dir-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , leiosNotify _} ¬d = refl
kaCnxt-dir-no l d (NS.kcAwait c) (KA.receiveKA l' d') {a = t , m , len , leiosFetch _} ¬d = refl
kaCnxt-dir-no l d (NS.kcAwait c) (KA.sendKA l' d') ¬d = refl
kaCnxt-dir-no l d (NS.kcAwait c) (KA.apiKAev l' d' m) ¬d = refl
kaCnxt-dir-no l d (NS.kcAwait c) (KA.doneKA l' d') ¬d = refl
-- kcErr cq cr : fires apiKA errCookie
kaCnxt-dir-no l d (NS.kcErr cq cr) (KA.apiKAev l' d' errCookie) ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
kaCnxt-dir-no l d (NS.kcErr cq cr) (KA.apiKAev l' d' sendKAMsg) ¬d = refl
kaCnxt-dir-no l d (NS.kcErr cq cr) (KA.apiKAev l' d' sendKADone) ¬d = refl
kaCnxt-dir-no l d (NS.kcErr cq cr) (KA.apiKAev l' d' recvKACookie) ¬d = refl
kaCnxt-dir-no l d (NS.kcErr cq cr) (KA.sendKA l' d') ¬d = refl
kaCnxt-dir-no l d (NS.kcErr cq cr) (KA.receiveKA l' d') ¬d = refl
kaCnxt-dir-no l d (NS.kcErr cq cr) (KA.doneKA l' d') ¬d = refl
-- kcTerm / kcTermE : terminal, no edges
kaCnxt-dir-no l d NS.kcTerm  e₁ ¬d = refl
kaCnxt-dir-no l d NS.kcTermE e₁ ¬d = refl

-- kaSnxt-dir-no: a wrong-direction KA-image event has no kaSnxt table edge
kaSnxt-dir-no : (l : Link) (d : Dir) (q : NS.KAsPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → kaEvDir e₁ ≢ d → NS.kaSnxt l d q (X , ιKA e₁) a ≡ nothing
-- ksClient : fires receiveKA (output N2N_KeepAlive) with MsgKeepAlive / MsgKADone
kaSnxt-dir-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAlive c)} ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
kaSnxt-dir-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , keepAlive MsgKADone} ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
kaSnxt-dir-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , keepAlive (MsgKeepAliveResponse _)} ¬d = refl
kaSnxt-dir-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , chainSync _} ¬d = refl
kaSnxt-dir-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , blockFetch _} ¬d = refl
kaSnxt-dir-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , txSubmission _} ¬d = refl
kaSnxt-dir-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , leiosNotify _} ¬d = refl
kaSnxt-dir-no l d NS.ksClient (KA.receiveKA l' d') {a = t , m , len , leiosFetch _} ¬d = refl
kaSnxt-dir-no l d NS.ksClient (KA.sendKA l' d') ¬d = refl
kaSnxt-dir-no l d NS.ksClient (KA.apiKAev l' d' m) ¬d = refl
kaSnxt-dir-no l d NS.ksClient (KA.doneKA l' d') ¬d = refl
-- ksRecv c : fires apiKA recvKACookie
kaSnxt-dir-no l d (NS.ksRecv c) (KA.apiKAev l' d' recvKACookie) ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
kaSnxt-dir-no l d (NS.ksRecv c) (KA.apiKAev l' d' sendKAMsg) ¬d = refl
kaSnxt-dir-no l d (NS.ksRecv c) (KA.apiKAev l' d' sendKADone) ¬d = refl
kaSnxt-dir-no l d (NS.ksRecv c) (KA.apiKAev l' d' errCookie) ¬d = refl
kaSnxt-dir-no l d (NS.ksRecv c) (KA.sendKA l' d') ¬d = refl
kaSnxt-dir-no l d (NS.ksRecv c) (KA.receiveKA l' d') ¬d = refl
kaSnxt-dir-no l d (NS.ksRecv c) (KA.doneKA l' d') ¬d = refl
-- ksResp c : fires sendKA (input N2N_KeepAlive) with MsgKeepAliveResponse
kaSnxt-dir-no l d (NS.ksResp c) (KA.sendKA l' d') ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
kaSnxt-dir-no l d (NS.ksResp c) (KA.receiveKA l' d') ¬d = refl
kaSnxt-dir-no l d (NS.ksResp c) (KA.apiKAev l' d' m) ¬d = refl
kaSnxt-dir-no l d (NS.ksResp c) (KA.doneKA l' d') ¬d = refl
-- ksDdone : fires doneKA (done N2N_KeepAlive)
kaSnxt-dir-no l d NS.ksDdone (KA.doneKA l' d') ¬d with l' ≟ l | d' ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
kaSnxt-dir-no l d NS.ksDdone (KA.sendKA l' d') ¬d = refl
kaSnxt-dir-no l d NS.ksDdone (KA.receiveKA l' d') ¬d = refl
kaSnxt-dir-no l d NS.ksDdone (KA.apiKAev l' d' m) ¬d = refl
-- ksTerm : terminal, no edges
kaSnxt-dir-no l d NS.ksTerm e₁ ¬d = refl

-- absKAc-dir-noBoth / absKAs-dir-noBoth: the same-protocol OPPOSITE-role abstract
-- sibling (dir sv) does not fire the driven peer's wrong-direction KA event
absKAc-dir-noBoth : (l : Link) (sv : Dir) (q : KAcPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → kaEvDir e₁ ≢ sv → ¬ IoOffers (absKAc l sv q) (ιKA e₁) a
absKAc-dir-noBoth l sv q e₁ {a} ¬d with NS.kaCfin (coarsenKAc q) in fEq
... | true  = viewV→noOffer (absKAc l sv q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l sv })
                   (coarsenKAc q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAc l sv q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l sv })
                   (coarsenKAc q) {e = ιKA e₁} {a = a} fEq (kaCnxt-dir-no l sv (coarsenKAc q) e₁ {a = a} ¬d))
absKAs-dir-noBoth : (l : Link) (sv : Dir) (q : KAsPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → kaEvDir e₁ ≢ sv → ¬ IoOffers (absKAs l sv q) (ιKA e₁) a
absKAs-dir-noBoth l sv q e₁ {a} ¬d with NS.kaSfin (coarsenKAs q) in fEq
... | true  = viewV→noOffer (absKAs l sv q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l sv })
                   (coarsenKAs q) {e = ιKA e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAs l sv q) {e = ιKA e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l sv })
                   (coarsenKAs q) {e = ιKA e₁} {a = a} fEq (kaSnxt-dir-no l sv (coarsenKAs q) e₁ {a = a} ¬d))

-- tail (CSc ⦀ CSs ⦀ BFc ⦀ BFs ⦀ TS ⦀ LN ⦀ LF) offers no KA-image event (all non-KA)
kaTail-csc-noOffer : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X}
  → ¬ IoOffers (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
       ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))) (ιKA e₁) a
kaTail-csc-noOffer l cl sv csc css bfc bfs ip e₁ =
  SStep.⦀-noOffer (decCSc l cl csc) _ (decCSc-noKAgen l cl csc e₁)
    (SStep.⦀-noOffer (decCSs l sv css) _ (decCSs-noKAgen l sv css e₁)
      (SStep.⦀-noOffer (decBFc l cl bfc) _ (decBFc-noKAgen l cl bfc e₁)
        (SStep.⦀-noOffer (decBFs l sv bfs) _ (decBFs-noKAgen l sv bfs e₁)
          (SStep.⦀-noOffer (decTSc l cl (tsc ip)) _ (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιKA e₁))
            (SStep.⦀-noOffer (decTSs l sv (tss ip)) _ (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιKA e₁))
              (SStep.⦀-noOffer (decLNc l cl (lnc ip)) _ (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιKA e₁))
                (SStep.⦀-noOffer (decLNs l sv (lns ip)) _ (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιKA e₁))
                  (SStep.⦀-noOffer (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip))
                    (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιKA e₁))
                    (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιKA e₁))))))))))

-- tail (decKAs ⦀ CSc ⦀ …) offers no KA-image event when kaEvDir e₁ ≢ sv (KA-client peel)
kaTail-kas-noOffer : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : KA.KAEv X) {a : X} → kaEvDir e₁ ≢ sv
  → ¬ IoOffers (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
       ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))) (ιKA e₁) a
kaTail-kas-noOffer l cl sv csc css bfc bfs ip e₁ ¬sv =
  SStep.⦀-noOffer (decKAs l sv (kas ip)) _ (decKAs-dir-noOffer l sv (kas ip) e₁ ¬sv)
    (kaTail-csc-noOffer l cl sv csc css bfc bfs ip e₁)

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER C2 — the 12-peer bundle ev-inversion, KA channel.
-- A visible KA-image event `ιKA e₁` of `bundleG` is fired by exactly ONE of
-- the two driven-in-place KA peers (client at cl / server at sv, tracked by the
-- `kac`/`kas` InertPos fields); the ten siblings are refuted by non-offer
-- (opposite-protocol CS/BF via `decCS/BF*-noKAgen`; inert TS/LN/LF via the
-- `ιX⁻¹∘ιKA` cross-preimages; the same-protocol opposite-role KA peer via the
-- direction leaf, cl ≢ sv).  RE-VERIFIES the M4 evBoth sidestep for a non-CS/BF
-- channel: io routes to the UNIQUE peer, the both-offer refuted by kaTail.
------------------------------------------------------------------------

-- KA-client advances: rebuild the abstract bundle step (dir cl, kaEvDir e₁≡cl)
absBundle-KAc-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {kac′ : KAcPos}
  → cl ≢ sv → kaEvDir e₁ ≡ cl
  → absKAc l cl (kac ip) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► absKAc l cl kac′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc qbs (record ip { kac = kac′ })
absBundle-KAc-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} {kac′} cl≢sv eqd astep =
  SStep.⦀-ev-L (absKAc l cl (kac ip)) _ astep
    (noOffer→viewV _
      (SStep.⦀-noOffer (absKAs l sv (kas ip)) _ (absKAs-dir-noBoth l sv (kas ip) e₁ ¬sv) absTail))
  where
    ¬sv : kaEvDir e₁ ≢ sv
    ¬sv q = cl≢sv (trans (sym eqd) q)
    absTail : ¬ IoOffers (absCSc l cl qcc ⦀ (absCSs l sv qcs ⦀ (absBFc l cl qbc ⦀ (absBFs l sv qbs
       ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
       ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))) (ιKA e₁) a
    absTail = SStep.⦀-noOffer (absCSc l cl qcc) _ (absCSc-noKA l cl qcc e₁)
      (SStep.⦀-noOffer (absCSs l sv qcs) _ (absCSs-noKA l sv qcs e₁)
        (SStep.⦀-noOffer (absBFc l cl qbc) _ (absBFc-noKA l cl qbc e₁)
          (SStep.⦀-noOffer (absBFs l sv qbs) _ (absBFs-noKA l sv qbs e₁)
            (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noKA l cl (tsc ip) e₁)
              (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noKA l sv (tss ip) e₁)
                (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noKA l cl (lnc ip) e₁)
                  (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noKA l sv (lns ip) e₁)
                    (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
                      (absLFc-noKA l cl (lfc ip) e₁) (absLFs-noKA l sv (lfs ip) e₁)))))))))

-- KA-server advances: rebuild the abstract bundle step (dir sv, kaEvDir e₁≡sv)
absBundle-KAs-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {kas′ : KAsPos}
  → cl ≢ sv → kaEvDir e₁ ≡ sv
  → absKAs l sv (kas ip) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► absKAs l sv kas′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc qbs (record ip { kas = kas′ })
absBundle-KAs-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} {kas′} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-L (absKAs l sv (kas ip)) _ astep (noOffer→viewV _ absTail))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-dir-noBoth l cl (kac ip) e₁ ¬cl))
  where
    ¬cl : kaEvDir e₁ ≢ cl
    ¬cl q = cl≢sv (sym (trans (sym eqd) q))
    absTail : ¬ IoOffers (absCSc l cl qcc ⦀ (absCSs l sv qcs ⦀ (absBFc l cl qbc ⦀ (absBFs l sv qbs
       ⦀ (absTSc l cl (tsc ip) ⦀ (absTSs l sv (tss ip) ⦀ (absLNc l cl (lnc ip) ⦀ (absLNs l sv (lns ip)
       ⦀ (absLFc l cl (lfc ip) ⦀ absLFs l sv (lfs ip)))))))))) (ιKA e₁) a
    absTail = SStep.⦀-noOffer (absCSc l cl qcc) _ (absCSc-noKA l cl qcc e₁)
      (SStep.⦀-noOffer (absCSs l sv qcs) _ (absCSs-noKA l sv qcs e₁)
        (SStep.⦀-noOffer (absBFc l cl qbc) _ (absBFc-noKA l cl qbc e₁)
          (SStep.⦀-noOffer (absBFs l sv qbs) _ (absBFs-noKA l sv qbs e₁)
            (SStep.⦀-noOffer (absTSc l cl (tsc ip)) _ (absTSc-noKA l cl (tsc ip) e₁)
              (SStep.⦀-noOffer (absTSs l sv (tss ip)) _ (absTSs-noKA l sv (tss ip) e₁)
                (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noKA l cl (lnc ip) e₁)
                  (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noKA l sv (lns ip) e₁)
                    (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
                      (absLFc-noKA l cl (lfc ip) e₁) (absLFs-noKA l sv (lfs ip) e₁)))))))))

-- which driven KA peer of the bundle fired the KA-image event (+ target + abstract step)
data BundleKAEvR (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : KA.KAEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  bkacE : (kac′ : KAcPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc bfs (record ip { kac = kac′ })
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► absBundleG l cl sv csc css bfc bfs (record ip { kac = kac′ })
        → BundleKAEvR l cl sv csc css bfc bfs ip e₁ a Bd′
  bkasE : (kas′ : KAsPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc bfs (record ip { kas = kas′ })
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► absBundleG l cl sv csc css bfc bfs (record ip { kas = kas′ })
        → BundleKAEvR l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a KA-client driven step into the bundle result (KA client is peer #0)
finishKAc-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decKAc l cl (kac ip) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► P′
  → BundleKAEvR l cl sv csc css bfc bfs ip e₁ a
      (P′ ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
        ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))))
finishKAc-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simKAc′ l cl (kac ip) sM
... | _ , kac′ , _ , _ , Meq , aStep0 =
      bkacE kac′
        (cong (λ z → z ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
               ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))) Meq)
        (absBundle-KAc-ev l cl sv csc css bfc bfs ip {kac′ = kac′} cl≢sv
          (sym (apiDir-inj (kac-ev-dir l cl (kac ip) sM) (kaApiDir e₁))) aStep0)

-- fold a KA-server driven step into the bundle result (KA server is peer #1)
finishKAs-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decKAs l sv (kas ip) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► P′
  → BundleKAEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (P′ ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
        ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))))
finishKAs-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simKAs′ l sv (kas ip) sM
... | _ , kas′ , _ , _ , Meq , aStep0 =
      bkasE kas′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (z ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
               ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))) Meq)
        (absBundle-KAs-ev l cl sv csc css bfc bfs ip {kas′ = kas′} cl≢sv
          (sym (apiDir-inj (kas-ev-dir l sv (kas ip) sM) (kaApiDir e₁))) aStep0)

-- 12-peer bundle ev-inversion (KA): peel each `⦀`, refute the ten siblings, invert the driven KA peer
bundle-KA-ev-inv : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► Bd′
  → BundleKAEvR l cl sv csc css bfc bfs ip e₁ a Bd′
bundle-KA-ev-inv l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = finishKAc-ev l cl sv csc css bfc bfs ip cl≢sv sM
... | PEA.evBoth _ sM sTail =
        ⊥-elim (kaTail-kas-noOffer l cl sv csc css bfc bfs ip e₁
                  (λ q → cl≢sv (trans (apiDir-inj (kac-ev-dir l cl (kac ip) sM) (kaApiDir e₁)) q))
                  (_ , sTail))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = finishKAs-ev l cl sv csc css bfc bfs ip cl≢sv sM
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


------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER A — TxSubmission channel direction machinery.
-- Mirrors the CS/BF/KA direction+sim layer for the TS peer (peers #6/#7 of
-- the bundle).  TS carries non-trivial value carriers, but direction routing
-- is uniform.
------------------------------------------------------------------------

-- cross-protocol preimages towards a TS-image event (all `nothing`)
ιCS⁻¹∘ιTS : {X : Set 0ℓ} (e₁ : TS.TSEv X) → ιCS⁻¹ (ιTS e₁) ≡ nothing
ιCS⁻¹∘ιTS (TS.sendTS l d)    = refl
ιCS⁻¹∘ιTS (TS.receiveTS l d) = refl
ιCS⁻¹∘ιTS (TS.apiTSev l d m) = refl
ιCS⁻¹∘ιTS (TS.doneTS l d)    = refl
ιBF⁻¹∘ιTS : {X : Set 0ℓ} (e₁ : TS.TSEv X) → ιBF⁻¹ (ιTS e₁) ≡ nothing
ιBF⁻¹∘ιTS (TS.sendTS l d)    = refl
ιBF⁻¹∘ιTS (TS.receiveTS l d) = refl
ιBF⁻¹∘ιTS (TS.apiTSev l d m) = refl
ιBF⁻¹∘ιTS (TS.doneTS l d)    = refl
ιKA⁻¹∘ιTS : {X : Set 0ℓ} (e₁ : TS.TSEv X) → ιKA⁻¹ (ιTS e₁) ≡ nothing
ιKA⁻¹∘ιTS (TS.sendTS l d)    = refl
ιKA⁻¹∘ιTS (TS.receiveTS l d) = refl
ιKA⁻¹∘ιTS (TS.apiTSev l d m) = refl
ιKA⁻¹∘ιTS (TS.doneTS l d)    = refl
ιLN⁻¹∘ιTS : {X : Set 0ℓ} (e₁ : TS.TSEv X) → ιLN⁻¹ (ιTS e₁) ≡ nothing
ιLN⁻¹∘ιTS (TS.sendTS l d)    = refl
ιLN⁻¹∘ιTS (TS.receiveTS l d) = refl
ιLN⁻¹∘ιTS (TS.apiTSev l d m) = refl
ιLN⁻¹∘ιTS (TS.doneTS l d)    = refl
ιLF⁻¹∘ιTS : {X : Set 0ℓ} (e₁ : TS.TSEv X) → ιLF⁻¹ (ιTS e₁) ≡ nothing
ιLF⁻¹∘ιTS (TS.sendTS l d)    = refl
ιLF⁻¹∘ιTS (TS.receiveTS l d) = refl
ιLF⁻¹∘ιTS (TS.apiTSev l d m) = refl
ιLF⁻¹∘ιTS (TS.doneTS l d)    = refl

-- the direction component of a TxSubmission source event
tsEvDir : {X : Set 0ℓ} → TS.TSEv X → Dir
tsEvDir (TS.sendTS l d)    = d
tsEvDir (TS.receiveTS l d) = d
tsEvDir (TS.apiTSev l d m) = d
tsEvDir (TS.doneTS l d)    = d

-- ιTS carries the source direction into the Net_Api event
tsApiDir : {X : Set 0ℓ} (e₁ : TS.TSEv X) → ApiHasDir (tsEvDir e₁) (ιTS e₁)
tsApiDir (TS.sendTS l d)    = ahIn
tsApiDir (TS.receiveTS l d) = ahOut
tsApiDir (TS.apiTSev l d m) = ahTS
tsApiDir (TS.doneTS l d)    = ahDone

decTSc-src-dir : (l : Link) (d : Dir) (pos : TScPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : TSProc}
  → decTSc-src l d pos TSL.─[ TSL.ev (TSL.evl (TSL.evLabel X e₁ a)) ]─► P′
  → tsEvDir e₁ ≡ d
-- head stInit : sends MsgTSInit (io) → tcSil stIdle
decTSc-src-dir l d (tcHead TS.stInit) {e₁ = TS.sendTS l' d'} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-dir l d (tcHead TS.stInit) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
decTSc-src-dir l d (tcHead TS.stInit) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
decTSc-src-dir l d (tcHead TS.stInit) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
-- head stIdle : receives a wire request → tcReqIdsB1 / tcReqIdsNB1 / tcReqTxs1
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds Blocking a r)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds NonBlocking a r)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxs ids)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit}        s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone}        s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-dir l d (tcHead TS.stIdle) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
-- head stTxIdsBlocking : fires apiTSev sendTSReplyTxIds / sendTSDone
decTSc-src-dir l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-dir l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSDone} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-dir l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}          s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
-- head stTxIdsNonBlocking : fires apiTSev sendTSReplyTxIds
decTSc-src-dir l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-dir l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSDone}                 s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}          s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-dir l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
-- head stTxs : fires apiTSev sendTSReplyTxs
decTSc-src-dir l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSReplyTxs} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSc-src-dir l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-dir l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSDone}                  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-dir l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-dir l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-dir l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-dir l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}           s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-dir l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-dir l d (tcHead TS.stTxs) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-dir l d (tcHead TS.stTxs) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-dir l d (tcHead TS.stTxs) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
-- head stDone : ret, no visible step
decTSc-src-dir l d (tcHead TS.stDone) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaf tcReqIdsB1 : fires apiTSev recvTSRequestTxIds (Blocking,a,r) → tcSil stTxIdsBlocking
decTSc-src-dir l d (tcReqIdsB1 a r) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxIds) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (Blocking , a , r)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-dir l d (tcReqIdsB1 a r) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
decTSc-src-dir l d (tcReqIdsB1 a r) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
decTSc-src-dir l d (tcReqIdsB1 a r) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
-- recv leaf tcReqIdsNB1 : fires apiTSev recvTSRequestTxIds (NonBlocking,a,r) → tcSil stTxIdsNonBlocking
decTSc-src-dir l d (tcReqIdsNB1 a r) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxIds) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (NonBlocking , a , r)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-dir l d (tcReqIdsNB1 a r) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
decTSc-src-dir l d (tcReqIdsNB1 a r) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
decTSc-src-dir l d (tcReqIdsNB1 a r) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
-- recv leaf tcReqTxs1 : fires apiTSev recvTSRequestTxs ids → tcSil stTxs
decTSc-src-dir l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxs) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec (λ _ _ → yes refl) val ids
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-dir l d (tcReqTxs1 ids) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
decTSc-src-dir l d (tcReqTxs1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
decTSc-src-dir l d (tcReqTxs1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
-- send leaf tcRepB1 : fires sendTS (MsgTSReplyTxIds ids) → tcSil stIdle
decTSc-src-dir l d (tcRepB1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-dir l d (tcRepB1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
decTSc-src-dir l d (tcRepB1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
decTSc-src-dir l d (tcRepB1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
-- send leaf tcDone1 : fires sendTS MsgTSDone → tcSil stDone
decTSc-src-dir l d tcDone1 {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-dir l d tcDone1 {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
decTSc-src-dir l d tcDone1 {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
decTSc-src-dir l d tcDone1 {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
-- send leaf tcRepNB1 : fires sendTS (MsgTSReplyTxIds ids) → tcSil stIdle
decTSc-src-dir l d (tcRepNB1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-dir l d (tcRepNB1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
decTSc-src-dir l d (tcRepNB1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
decTSc-src-dir l d (tcRepNB1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
-- send leaf tcRepTxs1 : fires sendTS (MsgTSReplyTxs txs) → tcSil stIdle
decTSc-src-dir l d (tcRepTxs1 txs) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSc-src-dir l d (tcRepTxs1 txs) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
decTSc-src-dir l d (tcRepTxs1 txs) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
decTSc-src-dir l d (tcRepTxs1 txs) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
-- loop re-entry : sil, no visible step
decTSc-src-dir l d (tcSil st) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decTSs-src-dir : (l : Link) (d : Dir) (pos : TSsPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : TSProc}
  → decTSs-src l d pos TSL.─[ TSL.ev (TSL.evl (TSL.evLabel X e₁ a)) ]─► P′
  → tsEvDir e₁ ≡ d
-- head stInit : receives MsgTSInit → tsSil stIdle
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSInit} s with step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-dir l d (tsHead TS.stInit) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
-- head stIdle : fires the three api pull requests
decTSs-src-dir l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-dir l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-dir l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-dir l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-dir l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-dir l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSDone}       s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-dir l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-dir l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-dir l d (tsHead TS.stIdle) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-dir l d (tsHead TS.stIdle) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-dir l d (tsHead TS.stIdle) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
-- head stTxIdsBlocking : receives MsgTSReplyTxIds (→ tsSil stIdle) / MsgTSDone (→ tsDone1)
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSDone} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
-- head stTxIdsNonBlocking : receives MsgTSReplyTxIds → tsSil stIdle
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-dir l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
-- head stTxs : receives MsgTSReplyTxs → tsSil stIdle
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxs txs)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-dir l d (tsHead TS.stTxs) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
-- head stDone : ret, no visible step
decTSs-src-dir l d (tsHead TS.stDone) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf tsDone1 : fires doneTS → tsSil stDone
decTSs-src-dir l d tsDone1 {e₁ = TS.doneTS l' d'} {a} s with step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s
... | offer with TS.TSEv-≟ (_ , TS.doneTS l d) (_ , TS.doneTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decTSs-src-dir l d tsDone1 {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
decTSs-src-dir l d tsDone1 {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
decTSs-src-dir l d tsDone1 {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
-- send leaf tsReqB1 : fires sendTS (MsgTSRequestTxIds Blocking a r) → tsSil stTxIdsBlocking
decTSs-src-dir l d (tsReqB1 (a , r)) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSs-src-dir l d (tsReqB1 (a , r)) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
decTSs-src-dir l d (tsReqB1 (a , r)) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
decTSs-src-dir l d (tsReqB1 (a , r)) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
-- send leaf tsReqNB1 : fires sendTS (MsgTSRequestTxIds NonBlocking a r) → tsSil stTxIdsNonBlocking
decTSs-src-dir l d (tsReqNB1 (a , r)) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSs-src-dir l d (tsReqNB1 (a , r)) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
decTSs-src-dir l d (tsReqNB1 (a , r)) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
decTSs-src-dir l d (tsReqNB1 (a , r)) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
-- send leaf tsReqTxs1 : fires sendTS (MsgTSRequestTxs ids) → tsSil stTxs
decTSs-src-dir l d (tsReqTxs1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decTSs-src-dir l d (tsReqTxs1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
decTSs-src-dir l d (tsReqTxs1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
decTSs-src-dir l d (tsReqTxs1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
-- loop re-entry : sil, no visible step
decTSs-src-dir l d (tsSil st) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- the direction a driven TS-client / TS-server step exposes on the Net_Api event
tsc-ev-dir : (l : Link) (d : Dir) (pos : TScPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decTSc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
tsc-ev-dir l d pos step with TSNO.renameMap-ev-reflect-ι {P = decTSc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιTS-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιTS e₁)) (decTSc-src-dir l d pos srcStep) (tsApiDir e₁))
tss-ev-dir : (l : Link) (d : Dir) (pos : TSsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decTSs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
tss-ev-dir l d pos step with TSNO.renameMap-ev-reflect-ι {P = decTSs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιTS-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιTS e₁)) (decTSs-src-dir l d pos srcStep) (tsApiDir e₁))

-- L2 (TS): the client (dir cl) and server (dir sv≠cl) never fire the SAME event
TSc-TSs-noBoth : (l : Link) (cl sv : Dir) → cl ≢ sv → (pc : TScPos) (ps : TSsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {Mc Ms : NetProc}
  → decTSc l cl pc ─[ ev (evl (evLabel X e₂ a)) ]─► Mc
  → decTSs l sv ps ─[ ev (evl (evLabel X e₂ a)) ]─► Ms → ⊥
TSc-TSs-noBoth l cl sv cl≢sv pc ps sc ss =
  cl≢sv (apiDir-inj (tsc-ev-dir l cl pc sc) (tss-ev-dir l sv ps ss))

-- concrete TS peers never fire a wrong-direction TS-image event
decTSc-dir-noOffer : (l : Link) (d : Dir) (pos : TScPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → tsEvDir e₁ ≢ d → ¬ IoOffers (decTSc l d pos) (ιTS e₁) a
decTSc-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (tsc-ev-dir l d pos step) (tsApiDir e₁)))
decTSs-dir-noOffer : (l : Link) (d : Dir) (pos : TSsPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → tsEvDir e₁ ≢ d → ¬ IoOffers (decTSs l d pos) (ιTS e₁) a
decTSs-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (tss-ev-dir l d pos step) (tsApiDir e₁)))

-- augmented TS-client / TS-server sim
simTSc′ : (l : Link) (d : Dir) (pos : TScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decTSc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ TS.TSEv X ] Σ[ pos′ ∈ TScPos ]
       (e ≡ ιTS e₁) × (tsEvDir e₁ ≡ d) × (M ≡ decTSc l d pos′)
       × (absTSc l d pos ─[ ev (evl (evLabel X e a)) ]─► absTSc l d pos′)
simTSc′ l d pos step with TSNO.renameMap-ev-reflect-ι {P = decTSc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decTSc-src-ev-inv l d pos srcStep | ιTS-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decTSc-src-dir l d pos srcStep ,
        trans Meq (cong RenTS.renameMap P′eq) , aStep
simTSs′ : (l : Link) (d : Dir) (pos : TSsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decTSs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ TS.TSEv X ] Σ[ pos′ ∈ TSsPos ]
       (e ≡ ιTS e₁) × (tsEvDir e₁ ≡ d) × (M ≡ decTSs l d pos′)
       × (absTSs l d pos ─[ ev (evl (evLabel X e a)) ]─► absTSs l d pos′)
simTSs′ l d pos step with TSNO.renameMap-ev-reflect-ι {P = decTSs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decTSs-src-ev-inv l d pos srcStep | ιTS-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decTSs-src-dir l d pos srcStep ,
        trans Meq (cong RenTS.renameMap P′eq) , aStep


------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER B — TxSubmission channel abstract-side non-offers.
-- Each foreign abstract table (CS/BF/KA/LN/LF) gives `nothing` at every
-- position for a TS-image event (own-channel-only edges); wrappers lift that
-- to `¬ IoOffers`.
------------------------------------------------------------------------

csCnxt-noTS : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → NS.csCnxt l d q (X , ιTS e₁) a ≡ nothing
csCnxt-noTS l d NS.ccIdle (TS.sendTS _ _) = refl
csCnxt-noTS l d NS.ccIdle (TS.receiveTS _ _) = refl
csCnxt-noTS l d NS.ccIdle (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d NS.ccIdle (TS.doneTS _ _) = refl
csCnxt-noTS l d NS.ccWreq (TS.sendTS _ _) = refl
csCnxt-noTS l d NS.ccWreq (TS.receiveTS _ _) = refl
csCnxt-noTS l d NS.ccWreq (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d NS.ccWreq (TS.doneTS _ _) = refl
csCnxt-noTS l d NS.ccAwait (TS.sendTS _ _) = refl
csCnxt-noTS l d NS.ccAwait (TS.receiveTS _ _) = refl
csCnxt-noTS l d NS.ccAwait (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d NS.ccAwait (TS.doneTS _ _) = refl
csCnxt-noTS l d (NS.ccWfi _) (TS.sendTS _ _) = refl
csCnxt-noTS l d (NS.ccWfi _) (TS.receiveTS _ _) = refl
csCnxt-noTS l d (NS.ccWfi _) (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d (NS.ccWfi _) (TS.doneTS _ _) = refl
csCnxt-noTS l d NS.ccInt (TS.sendTS _ _) = refl
csCnxt-noTS l d NS.ccInt (TS.receiveTS _ _) = refl
csCnxt-noTS l d NS.ccInt (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d NS.ccInt (TS.doneTS _ _) = refl
csCnxt-noTS l d NS.ccWdone (TS.sendTS _ _) = refl
csCnxt-noTS l d NS.ccWdone (TS.receiveTS _ _) = refl
csCnxt-noTS l d NS.ccWdone (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d NS.ccWdone (TS.doneTS _ _) = refl
csCnxt-noTS l d NS.ccMust (TS.sendTS _ _) = refl
csCnxt-noTS l d NS.ccMust (TS.receiveTS _ _) = refl
csCnxt-noTS l d NS.ccMust (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d NS.ccMust (TS.doneTS _ _) = refl
csCnxt-noTS l d (NS.ccArf _) (TS.sendTS _ _) = refl
csCnxt-noTS l d (NS.ccArf _) (TS.receiveTS _ _) = refl
csCnxt-noTS l d (NS.ccArf _) (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d (NS.ccArf _) (TS.doneTS _ _) = refl
csCnxt-noTS l d (NS.ccArb _) (TS.sendTS _ _) = refl
csCnxt-noTS l d (NS.ccArb _) (TS.receiveTS _ _) = refl
csCnxt-noTS l d (NS.ccArb _) (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d (NS.ccArb _) (TS.doneTS _ _) = refl
csCnxt-noTS l d (NS.ccAif _) (TS.sendTS _ _) = refl
csCnxt-noTS l d (NS.ccAif _) (TS.receiveTS _ _) = refl
csCnxt-noTS l d (NS.ccAif _) (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d (NS.ccAif _) (TS.doneTS _ _) = refl
csCnxt-noTS l d (NS.ccAin _) (TS.sendTS _ _) = refl
csCnxt-noTS l d (NS.ccAin _) (TS.receiveTS _ _) = refl
csCnxt-noTS l d (NS.ccAin _) (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d (NS.ccAin _) (TS.doneTS _ _) = refl
csCnxt-noTS l d NS.ccTerm (TS.sendTS _ _) = refl
csCnxt-noTS l d NS.ccTerm (TS.receiveTS _ _) = refl
csCnxt-noTS l d NS.ccTerm (TS.apiTSev _ _ _) = refl
csCnxt-noTS l d NS.ccTerm (TS.doneTS _ _) = refl

csSnxt-noTS : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → NS.csSnxt l d q (X , ιTS e₁) a ≡ nothing
csSnxt-noTS l d NS.csIdle (TS.sendTS _ _) = refl
csSnxt-noTS l d NS.csIdle (TS.receiveTS _ _) = refl
csSnxt-noTS l d NS.csIdle (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d NS.csIdle (TS.doneTS _ _) = refl
csSnxt-noTS l d NS.csAreq (TS.sendTS _ _) = refl
csSnxt-noTS l d NS.csAreq (TS.receiveTS _ _) = refl
csSnxt-noTS l d NS.csAreq (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d NS.csAreq (TS.doneTS _ _) = refl
csSnxt-noTS l d NS.csCanAwait (TS.sendTS _ _) = refl
csSnxt-noTS l d NS.csCanAwait (TS.receiveTS _ _) = refl
csSnxt-noTS l d NS.csCanAwait (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d NS.csCanAwait (TS.doneTS _ _) = refl
csSnxt-noTS l d (NS.csAfi _) (TS.sendTS _ _) = refl
csSnxt-noTS l d (NS.csAfi _) (TS.receiveTS _ _) = refl
csSnxt-noTS l d (NS.csAfi _) (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d (NS.csAfi _) (TS.doneTS _ _) = refl
csSnxt-noTS l d NS.csInt (TS.sendTS _ _) = refl
csSnxt-noTS l d NS.csInt (TS.receiveTS _ _) = refl
csSnxt-noTS l d NS.csInt (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d NS.csInt (TS.doneTS _ _) = refl
csSnxt-noTS l d NS.csDdone (TS.sendTS _ _) = refl
csSnxt-noTS l d NS.csDdone (TS.receiveTS _ _) = refl
csSnxt-noTS l d NS.csDdone (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d NS.csDdone (TS.doneTS _ _) = refl
csSnxt-noTS l d NS.csMust (TS.sendTS _ _) = refl
csSnxt-noTS l d NS.csMust (TS.receiveTS _ _) = refl
csSnxt-noTS l d NS.csMust (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d NS.csMust (TS.doneTS _ _) = refl
csSnxt-noTS l d (NS.csWrf _) (TS.sendTS _ _) = refl
csSnxt-noTS l d (NS.csWrf _) (TS.receiveTS _ _) = refl
csSnxt-noTS l d (NS.csWrf _) (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d (NS.csWrf _) (TS.doneTS _ _) = refl
csSnxt-noTS l d (NS.csWrb _) (TS.sendTS _ _) = refl
csSnxt-noTS l d (NS.csWrb _) (TS.receiveTS _ _) = refl
csSnxt-noTS l d (NS.csWrb _) (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d (NS.csWrb _) (TS.doneTS _ _) = refl
csSnxt-noTS l d NS.csWar (TS.sendTS _ _) = refl
csSnxt-noTS l d NS.csWar (TS.receiveTS _ _) = refl
csSnxt-noTS l d NS.csWar (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d NS.csWar (TS.doneTS _ _) = refl
csSnxt-noTS l d (NS.csWif _) (TS.sendTS _ _) = refl
csSnxt-noTS l d (NS.csWif _) (TS.receiveTS _ _) = refl
csSnxt-noTS l d (NS.csWif _) (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d (NS.csWif _) (TS.doneTS _ _) = refl
csSnxt-noTS l d (NS.csWin _) (TS.sendTS _ _) = refl
csSnxt-noTS l d (NS.csWin _) (TS.receiveTS _ _) = refl
csSnxt-noTS l d (NS.csWin _) (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d (NS.csWin _) (TS.doneTS _ _) = refl
csSnxt-noTS l d NS.csTerm (TS.sendTS _ _) = refl
csSnxt-noTS l d NS.csTerm (TS.receiveTS _ _) = refl
csSnxt-noTS l d NS.csTerm (TS.apiTSev _ _ _) = refl
csSnxt-noTS l d NS.csTerm (TS.doneTS _ _) = refl

bfCnxt-noTS : (l : Link) (d : Dir) (q : NS.BFcPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → NS.bfCnxt l d q (X , ιTS e₁) a ≡ nothing
bfCnxt-noTS l d NS.bcIdle (TS.sendTS _ _) = refl
bfCnxt-noTS l d NS.bcIdle (TS.receiveTS _ _) = refl
bfCnxt-noTS l d NS.bcIdle (TS.apiTSev _ _ _) = refl
bfCnxt-noTS l d NS.bcIdle (TS.doneTS _ _) = refl
bfCnxt-noTS l d (NS.bcWrr _) (TS.sendTS _ _) = refl
bfCnxt-noTS l d (NS.bcWrr _) (TS.receiveTS _ _) = refl
bfCnxt-noTS l d (NS.bcWrr _) (TS.apiTSev _ _ _) = refl
bfCnxt-noTS l d (NS.bcWrr _) (TS.doneTS _ _) = refl
bfCnxt-noTS l d NS.bcBusy (TS.sendTS _ _) = refl
bfCnxt-noTS l d NS.bcBusy (TS.receiveTS _ _) = refl
bfCnxt-noTS l d NS.bcBusy (TS.apiTSev _ _ _) = refl
bfCnxt-noTS l d NS.bcBusy (TS.doneTS _ _) = refl
bfCnxt-noTS l d NS.bcWcd (TS.sendTS _ _) = refl
bfCnxt-noTS l d NS.bcWcd (TS.receiveTS _ _) = refl
bfCnxt-noTS l d NS.bcWcd (TS.apiTSev _ _ _) = refl
bfCnxt-noTS l d NS.bcWcd (TS.doneTS _ _) = refl
bfCnxt-noTS l d NS.bcStream (TS.sendTS _ _) = refl
bfCnxt-noTS l d NS.bcStream (TS.receiveTS _ _) = refl
bfCnxt-noTS l d NS.bcStream (TS.apiTSev _ _ _) = refl
bfCnxt-noTS l d NS.bcStream (TS.doneTS _ _) = refl
bfCnxt-noTS l d (NS.bcAblk _) (TS.sendTS _ _) = refl
bfCnxt-noTS l d (NS.bcAblk _) (TS.receiveTS _ _) = refl
bfCnxt-noTS l d (NS.bcAblk _) (TS.apiTSev _ _ _) = refl
bfCnxt-noTS l d (NS.bcAblk _) (TS.doneTS _ _) = refl
bfCnxt-noTS l d NS.bcTerm (TS.sendTS _ _) = refl
bfCnxt-noTS l d NS.bcTerm (TS.receiveTS _ _) = refl
bfCnxt-noTS l d NS.bcTerm (TS.apiTSev _ _ _) = refl
bfCnxt-noTS l d NS.bcTerm (TS.doneTS _ _) = refl

bfSnxt-noTS : (l : Link) (d : Dir) (q : NS.BFsPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → NS.bfSnxt l d q (X , ιTS e₁) a ≡ nothing
bfSnxt-noTS l d NS.bsIdle (TS.sendTS _ _) = refl
bfSnxt-noTS l d NS.bsIdle (TS.receiveTS _ _) = refl
bfSnxt-noTS l d NS.bsIdle (TS.apiTSev _ _ _) = refl
bfSnxt-noTS l d NS.bsIdle (TS.doneTS _ _) = refl
bfSnxt-noTS l d (NS.bsAreq _) (TS.sendTS _ _) = refl
bfSnxt-noTS l d (NS.bsAreq _) (TS.receiveTS _ _) = refl
bfSnxt-noTS l d (NS.bsAreq _) (TS.apiTSev _ _ _) = refl
bfSnxt-noTS l d (NS.bsAreq _) (TS.doneTS _ _) = refl
bfSnxt-noTS l d NS.bsBusy (TS.sendTS _ _) = refl
bfSnxt-noTS l d NS.bsBusy (TS.receiveTS _ _) = refl
bfSnxt-noTS l d NS.bsBusy (TS.apiTSev _ _ _) = refl
bfSnxt-noTS l d NS.bsBusy (TS.doneTS _ _) = refl
bfSnxt-noTS l d NS.bsDdone (TS.sendTS _ _) = refl
bfSnxt-noTS l d NS.bsDdone (TS.receiveTS _ _) = refl
bfSnxt-noTS l d NS.bsDdone (TS.apiTSev _ _ _) = refl
bfSnxt-noTS l d NS.bsDdone (TS.doneTS _ _) = refl
bfSnxt-noTS l d NS.bsWsb (TS.sendTS _ _) = refl
bfSnxt-noTS l d NS.bsWsb (TS.receiveTS _ _) = refl
bfSnxt-noTS l d NS.bsWsb (TS.apiTSev _ _ _) = refl
bfSnxt-noTS l d NS.bsWsb (TS.doneTS _ _) = refl
bfSnxt-noTS l d NS.bsStream (TS.sendTS _ _) = refl
bfSnxt-noTS l d NS.bsStream (TS.receiveTS _ _) = refl
bfSnxt-noTS l d NS.bsStream (TS.apiTSev _ _ _) = refl
bfSnxt-noTS l d NS.bsStream (TS.doneTS _ _) = refl
bfSnxt-noTS l d NS.bsWnb (TS.sendTS _ _) = refl
bfSnxt-noTS l d NS.bsWnb (TS.receiveTS _ _) = refl
bfSnxt-noTS l d NS.bsWnb (TS.apiTSev _ _ _) = refl
bfSnxt-noTS l d NS.bsWnb (TS.doneTS _ _) = refl
bfSnxt-noTS l d (NS.bsWblk _) (TS.sendTS _ _) = refl
bfSnxt-noTS l d (NS.bsWblk _) (TS.receiveTS _ _) = refl
bfSnxt-noTS l d (NS.bsWblk _) (TS.apiTSev _ _ _) = refl
bfSnxt-noTS l d (NS.bsWblk _) (TS.doneTS _ _) = refl
bfSnxt-noTS l d NS.bsWbd (TS.sendTS _ _) = refl
bfSnxt-noTS l d NS.bsWbd (TS.receiveTS _ _) = refl
bfSnxt-noTS l d NS.bsWbd (TS.apiTSev _ _ _) = refl
bfSnxt-noTS l d NS.bsWbd (TS.doneTS _ _) = refl
bfSnxt-noTS l d NS.bsTerm (TS.sendTS _ _) = refl
bfSnxt-noTS l d NS.bsTerm (TS.receiveTS _ _) = refl
bfSnxt-noTS l d NS.bsTerm (TS.apiTSev _ _ _) = refl
bfSnxt-noTS l d NS.bsTerm (TS.doneTS _ _) = refl

kaCnxt-noTS : (l : Link) (d : Dir) (q : NS.KAcPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → NS.kaCnxt l d q (X , ιTS e₁) a ≡ nothing
kaCnxt-noTS l d NS.kcClient (TS.sendTS _ _) = refl
kaCnxt-noTS l d NS.kcClient (TS.receiveTS _ _) = refl
kaCnxt-noTS l d NS.kcClient (TS.apiTSev _ _ _) = refl
kaCnxt-noTS l d NS.kcClient (TS.doneTS _ _) = refl
kaCnxt-noTS l d (NS.kcWmsg _) (TS.sendTS _ _) = refl
kaCnxt-noTS l d (NS.kcWmsg _) (TS.receiveTS _ _) = refl
kaCnxt-noTS l d (NS.kcWmsg _) (TS.apiTSev _ _ _) = refl
kaCnxt-noTS l d (NS.kcWmsg _) (TS.doneTS _ _) = refl
kaCnxt-noTS l d (NS.kcAwait _) (TS.sendTS _ _) = refl
kaCnxt-noTS l d (NS.kcAwait _) (TS.receiveTS _ _) = refl
kaCnxt-noTS l d (NS.kcAwait _) (TS.apiTSev _ _ _) = refl
kaCnxt-noTS l d (NS.kcAwait _) (TS.doneTS _ _) = refl
kaCnxt-noTS l d NS.kcWdone (TS.sendTS _ _) = refl
kaCnxt-noTS l d NS.kcWdone (TS.receiveTS _ _) = refl
kaCnxt-noTS l d NS.kcWdone (TS.apiTSev _ _ _) = refl
kaCnxt-noTS l d NS.kcWdone (TS.doneTS _ _) = refl
kaCnxt-noTS l d (NS.kcErr _ _) (TS.sendTS _ _) = refl
kaCnxt-noTS l d (NS.kcErr _ _) (TS.receiveTS _ _) = refl
kaCnxt-noTS l d (NS.kcErr _ _) (TS.apiTSev _ _ _) = refl
kaCnxt-noTS l d (NS.kcErr _ _) (TS.doneTS _ _) = refl
kaCnxt-noTS l d NS.kcTerm (TS.sendTS _ _) = refl
kaCnxt-noTS l d NS.kcTerm (TS.receiveTS _ _) = refl
kaCnxt-noTS l d NS.kcTerm (TS.apiTSev _ _ _) = refl
kaCnxt-noTS l d NS.kcTerm (TS.doneTS _ _) = refl
kaCnxt-noTS l d NS.kcTermE (TS.sendTS _ _) = refl
kaCnxt-noTS l d NS.kcTermE (TS.receiveTS _ _) = refl
kaCnxt-noTS l d NS.kcTermE (TS.apiTSev _ _ _) = refl
kaCnxt-noTS l d NS.kcTermE (TS.doneTS _ _) = refl

kaSnxt-noTS : (l : Link) (d : Dir) (q : NS.KAsPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → NS.kaSnxt l d q (X , ιTS e₁) a ≡ nothing
kaSnxt-noTS l d NS.ksClient (TS.sendTS _ _) = refl
kaSnxt-noTS l d NS.ksClient (TS.receiveTS _ _) = refl
kaSnxt-noTS l d NS.ksClient (TS.apiTSev _ _ _) = refl
kaSnxt-noTS l d NS.ksClient (TS.doneTS _ _) = refl
kaSnxt-noTS l d (NS.ksRecv _) (TS.sendTS _ _) = refl
kaSnxt-noTS l d (NS.ksRecv _) (TS.receiveTS _ _) = refl
kaSnxt-noTS l d (NS.ksRecv _) (TS.apiTSev _ _ _) = refl
kaSnxt-noTS l d (NS.ksRecv _) (TS.doneTS _ _) = refl
kaSnxt-noTS l d (NS.ksResp _) (TS.sendTS _ _) = refl
kaSnxt-noTS l d (NS.ksResp _) (TS.receiveTS _ _) = refl
kaSnxt-noTS l d (NS.ksResp _) (TS.apiTSev _ _ _) = refl
kaSnxt-noTS l d (NS.ksResp _) (TS.doneTS _ _) = refl
kaSnxt-noTS l d NS.ksDdone (TS.sendTS _ _) = refl
kaSnxt-noTS l d NS.ksDdone (TS.receiveTS _ _) = refl
kaSnxt-noTS l d NS.ksDdone (TS.apiTSev _ _ _) = refl
kaSnxt-noTS l d NS.ksDdone (TS.doneTS _ _) = refl
kaSnxt-noTS l d NS.ksTerm (TS.sendTS _ _) = refl
kaSnxt-noTS l d NS.ksTerm (TS.receiveTS _ _) = refl
kaSnxt-noTS l d NS.ksTerm (TS.apiTSev _ _ _) = refl
kaSnxt-noTS l d NS.ksTerm (TS.doneTS _ _) = refl

lnCnxt-noTS : (l : Link) (d : Dir) (q : NS.LNcPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → NS.lnCnxt l d q (X , ιTS e₁) a ≡ nothing
lnCnxt-noTS l d NS.lncIdle (TS.sendTS _ _) = refl
lnCnxt-noTS l d NS.lncIdle (TS.receiveTS _ _) = refl
lnCnxt-noTS l d NS.lncIdle (TS.apiTSev _ _ _) = refl
lnCnxt-noTS l d NS.lncIdle (TS.doneTS _ _) = refl
lnCnxt-noTS l d NS.lncWreq (TS.sendTS _ _) = refl
lnCnxt-noTS l d NS.lncWreq (TS.receiveTS _ _) = refl
lnCnxt-noTS l d NS.lncWreq (TS.apiTSev _ _ _) = refl
lnCnxt-noTS l d NS.lncWreq (TS.doneTS _ _) = refl
lnCnxt-noTS l d NS.lncWdone (TS.sendTS _ _) = refl
lnCnxt-noTS l d NS.lncWdone (TS.receiveTS _ _) = refl
lnCnxt-noTS l d NS.lncWdone (TS.apiTSev _ _ _) = refl
lnCnxt-noTS l d NS.lncWdone (TS.doneTS _ _) = refl
lnCnxt-noTS l d NS.lncBusy (TS.sendTS _ _) = refl
lnCnxt-noTS l d NS.lncBusy (TS.receiveTS _ _) = refl
lnCnxt-noTS l d NS.lncBusy (TS.apiTSev _ _ _) = refl
lnCnxt-noTS l d NS.lncBusy (TS.doneTS _ _) = refl
lnCnxt-noTS l d (NS.lncRann _) (TS.sendTS _ _) = refl
lnCnxt-noTS l d (NS.lncRann _) (TS.receiveTS _ _) = refl
lnCnxt-noTS l d (NS.lncRann _) (TS.apiTSev _ _ _) = refl
lnCnxt-noTS l d (NS.lncRann _) (TS.doneTS _ _) = refl
lnCnxt-noTS l d (NS.lncRoff _) (TS.sendTS _ _) = refl
lnCnxt-noTS l d (NS.lncRoff _) (TS.receiveTS _ _) = refl
lnCnxt-noTS l d (NS.lncRoff _) (TS.apiTSev _ _ _) = refl
lnCnxt-noTS l d (NS.lncRoff _) (TS.doneTS _ _) = refl
lnCnxt-noTS l d (NS.lncRtxs _) (TS.sendTS _ _) = refl
lnCnxt-noTS l d (NS.lncRtxs _) (TS.receiveTS _ _) = refl
lnCnxt-noTS l d (NS.lncRtxs _) (TS.apiTSev _ _ _) = refl
lnCnxt-noTS l d (NS.lncRtxs _) (TS.doneTS _ _) = refl
lnCnxt-noTS l d (NS.lncRvot _) (TS.sendTS _ _) = refl
lnCnxt-noTS l d (NS.lncRvot _) (TS.receiveTS _ _) = refl
lnCnxt-noTS l d (NS.lncRvot _) (TS.apiTSev _ _ _) = refl
lnCnxt-noTS l d (NS.lncRvot _) (TS.doneTS _ _) = refl
lnCnxt-noTS l d NS.lncTerm (TS.sendTS _ _) = refl
lnCnxt-noTS l d NS.lncTerm (TS.receiveTS _ _) = refl
lnCnxt-noTS l d NS.lncTerm (TS.apiTSev _ _ _) = refl
lnCnxt-noTS l d NS.lncTerm (TS.doneTS _ _) = refl

lnSnxt-noTS : (l : Link) (d : Dir) (q : NS.LNsPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → NS.lnSnxt l d q (X , ιTS e₁) a ≡ nothing
lnSnxt-noTS l d NS.lnsIdle (TS.sendTS _ _) = refl
lnSnxt-noTS l d NS.lnsIdle (TS.receiveTS _ _) = refl
lnSnxt-noTS l d NS.lnsIdle (TS.apiTSev _ _ _) = refl
lnSnxt-noTS l d NS.lnsIdle (TS.doneTS _ _) = refl
lnSnxt-noTS l d NS.lnsBusy (TS.sendTS _ _) = refl
lnSnxt-noTS l d NS.lnsBusy (TS.receiveTS _ _) = refl
lnSnxt-noTS l d NS.lnsBusy (TS.apiTSev _ _ _) = refl
lnSnxt-noTS l d NS.lnsBusy (TS.doneTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWann _) (TS.sendTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWann _) (TS.receiveTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWann _) (TS.apiTSev _ _ _) = refl
lnSnxt-noTS l d (NS.lnsWann _) (TS.doneTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWoff _) (TS.sendTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWoff _) (TS.receiveTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWoff _) (TS.apiTSev _ _ _) = refl
lnSnxt-noTS l d (NS.lnsWoff _) (TS.doneTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWtxs _) (TS.sendTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWtxs _) (TS.receiveTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWtxs _) (TS.apiTSev _ _ _) = refl
lnSnxt-noTS l d (NS.lnsWtxs _) (TS.doneTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWvot _) (TS.sendTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWvot _) (TS.receiveTS _ _) = refl
lnSnxt-noTS l d (NS.lnsWvot _) (TS.apiTSev _ _ _) = refl
lnSnxt-noTS l d (NS.lnsWvot _) (TS.doneTS _ _) = refl
lnSnxt-noTS l d NS.lnsDone (TS.sendTS _ _) = refl
lnSnxt-noTS l d NS.lnsDone (TS.receiveTS _ _) = refl
lnSnxt-noTS l d NS.lnsDone (TS.apiTSev _ _ _) = refl
lnSnxt-noTS l d NS.lnsDone (TS.doneTS _ _) = refl
lnSnxt-noTS l d NS.lnsTerm (TS.sendTS _ _) = refl
lnSnxt-noTS l d NS.lnsTerm (TS.receiveTS _ _) = refl
lnSnxt-noTS l d NS.lnsTerm (TS.apiTSev _ _ _) = refl
lnSnxt-noTS l d NS.lnsTerm (TS.doneTS _ _) = refl

lfCnxt-noTS : (l : Link) (d : Dir) (q : NS.LFcPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → NS.lfCnxt l d q (X , ιTS e₁) a ≡ nothing
lfCnxt-noTS l d NS.lfcIdle (TS.sendTS _ _) = refl
lfCnxt-noTS l d NS.lfcIdle (TS.receiveTS _ _) = refl
lfCnxt-noTS l d NS.lfcIdle (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d NS.lfcIdle (TS.doneTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWblk _) (TS.sendTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWblk _) (TS.receiveTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWblk _) (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d (NS.lfcWblk _) (TS.doneTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWtxs _) (TS.sendTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWtxs _) (TS.receiveTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWtxs _) (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d (NS.lfcWtxs _) (TS.doneTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWvot _) (TS.sendTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWvot _) (TS.receiveTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWvot _) (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d (NS.lfcWvot _) (TS.doneTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWrng _) (TS.sendTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWrng _) (TS.receiveTS _ _) = refl
lfCnxt-noTS l d (NS.lfcWrng _) (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d (NS.lfcWrng _) (TS.doneTS _ _) = refl
lfCnxt-noTS l d NS.lfcWdone (TS.sendTS _ _) = refl
lfCnxt-noTS l d NS.lfcWdone (TS.receiveTS _ _) = refl
lfCnxt-noTS l d NS.lfcWdone (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d NS.lfcWdone (TS.doneTS _ _) = refl
lfCnxt-noTS l d NS.lfcBlk (TS.sendTS _ _) = refl
lfCnxt-noTS l d NS.lfcBlk (TS.receiveTS _ _) = refl
lfCnxt-noTS l d NS.lfcBlk (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d NS.lfcBlk (TS.doneTS _ _) = refl
lfCnxt-noTS l d NS.lfcBtx (TS.sendTS _ _) = refl
lfCnxt-noTS l d NS.lfcBtx (TS.receiveTS _ _) = refl
lfCnxt-noTS l d NS.lfcBtx (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d NS.lfcBtx (TS.doneTS _ _) = refl
lfCnxt-noTS l d NS.lfcVot (TS.sendTS _ _) = refl
lfCnxt-noTS l d NS.lfcVot (TS.receiveTS _ _) = refl
lfCnxt-noTS l d NS.lfcVot (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d NS.lfcVot (TS.doneTS _ _) = refl
lfCnxt-noTS l d NS.lfcRng (TS.sendTS _ _) = refl
lfCnxt-noTS l d NS.lfcRng (TS.receiveTS _ _) = refl
lfCnxt-noTS l d NS.lfcRng (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d NS.lfcRng (TS.doneTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRblk _) (TS.sendTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRblk _) (TS.receiveTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRblk _) (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d (NS.lfcRblk _) (TS.doneTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRbtx _) (TS.sendTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRbtx _) (TS.receiveTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRbtx _) (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d (NS.lfcRbtx _) (TS.doneTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRvot _) (TS.sendTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRvot _) (TS.receiveTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRvot _) (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d (NS.lfcRvot _) (TS.doneTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRnextRng _) (TS.sendTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRnextRng _) (TS.receiveTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRnextRng _) (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d (NS.lfcRnextRng _) (TS.doneTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRlastRng _) (TS.sendTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRlastRng _) (TS.receiveTS _ _) = refl
lfCnxt-noTS l d (NS.lfcRlastRng _) (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d (NS.lfcRlastRng _) (TS.doneTS _ _) = refl
lfCnxt-noTS l d NS.lfcTerm (TS.sendTS _ _) = refl
lfCnxt-noTS l d NS.lfcTerm (TS.receiveTS _ _) = refl
lfCnxt-noTS l d NS.lfcTerm (TS.apiTSev _ _ _) = refl
lfCnxt-noTS l d NS.lfcTerm (TS.doneTS _ _) = refl

lfSnxt-noTS : (l : Link) (d : Dir) (q : NS.LFsPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → NS.lfSnxt l d q (X , ιTS e₁) a ≡ nothing
lfSnxt-noTS l d NS.lfsIdle (TS.sendTS _ _) = refl
lfSnxt-noTS l d NS.lfsIdle (TS.receiveTS _ _) = refl
lfSnxt-noTS l d NS.lfsIdle (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d NS.lfsIdle (TS.doneTS _ _) = refl
lfSnxt-noTS l d NS.lfsBlk (TS.sendTS _ _) = refl
lfSnxt-noTS l d NS.lfsBlk (TS.receiveTS _ _) = refl
lfSnxt-noTS l d NS.lfsBlk (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d NS.lfsBlk (TS.doneTS _ _) = refl
lfSnxt-noTS l d NS.lfsBtx (TS.sendTS _ _) = refl
lfSnxt-noTS l d NS.lfsBtx (TS.receiveTS _ _) = refl
lfSnxt-noTS l d NS.lfsBtx (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d NS.lfsBtx (TS.doneTS _ _) = refl
lfSnxt-noTS l d NS.lfsVot (TS.sendTS _ _) = refl
lfSnxt-noTS l d NS.lfsVot (TS.receiveTS _ _) = refl
lfSnxt-noTS l d NS.lfsVot (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d NS.lfsVot (TS.doneTS _ _) = refl
lfSnxt-noTS l d NS.lfsRng (TS.sendTS _ _) = refl
lfSnxt-noTS l d NS.lfsRng (TS.receiveTS _ _) = refl
lfSnxt-noTS l d NS.lfsRng (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d NS.lfsRng (TS.doneTS _ _) = refl
lfSnxt-noTS l d NS.lfsDone (TS.sendTS _ _) = refl
lfSnxt-noTS l d NS.lfsDone (TS.receiveTS _ _) = refl
lfSnxt-noTS l d NS.lfsDone (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d NS.lfsDone (TS.doneTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWblk _) (TS.sendTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWblk _) (TS.receiveTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWblk _) (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d (NS.lfsWblk _) (TS.doneTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWtxs _) (TS.sendTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWtxs _) (TS.receiveTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWtxs _) (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d (NS.lfsWtxs _) (TS.doneTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWvot _) (TS.sendTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWvot _) (TS.receiveTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWvot _) (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d (NS.lfsWvot _) (TS.doneTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWnext _) (TS.sendTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWnext _) (TS.receiveTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWnext _) (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d (NS.lfsWnext _) (TS.doneTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWlast _) (TS.sendTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWlast _) (TS.receiveTS _ _) = refl
lfSnxt-noTS l d (NS.lfsWlast _) (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d (NS.lfsWlast _) (TS.doneTS _ _) = refl
lfSnxt-noTS l d NS.lfsTerm (TS.sendTS _ _) = refl
lfSnxt-noTS l d NS.lfsTerm (TS.receiveTS _ _) = refl
lfSnxt-noTS l d NS.lfsTerm (TS.apiTSev _ _ _) = refl
lfSnxt-noTS l d NS.lfsTerm (TS.doneTS _ _) = refl

absCSc-noTS : (l : Link) (d : Dir) (q : CScPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (absCSc l d q) (ιTS e₁) a
absCSc-noTS l d q e₁ {a} with NS.csCfin (coarsenCSc q) in fEq
... | true  = viewV→noOffer (absCSc l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSc l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιTS e₁} {a = a} fEq (csCnxt-noTS l d (coarsenCSc q) e₁ {a = a}))
absCSs-noTS : (l : Link) (d : Dir) (q : CSsPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (absCSs l d q) (ιTS e₁) a
absCSs-noTS l d q e₁ {a} with NS.csSfin (coarsenCSs q) in fEq
... | true  = viewV→noOffer (absCSs l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSs l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιTS e₁} {a = a} fEq (csSnxt-noTS l d (coarsenCSs q) e₁ {a = a}))
absBFc-noTS : (l : Link) (d : Dir) (q : BFcPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (absBFc l d q) (ιTS e₁) a
absBFc-noTS l d q e₁ {a} with NS.bfCfin (coarsenBFc q) in fEq
... | true  = viewV→noOffer (absBFc l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFc l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιTS e₁} {a = a} fEq (bfCnxt-noTS l d (coarsenBFc q) e₁ {a = a}))
absBFs-noTS : (l : Link) (d : Dir) (q : BFsPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (absBFs l d q) (ιTS e₁) a
absBFs-noTS l d q e₁ {a} with NS.bfSfin (coarsenBFs q) in fEq
... | true  = viewV→noOffer (absBFs l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFs l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιTS e₁} {a = a} fEq (bfSnxt-noTS l d (coarsenBFs q) e₁ {a = a}))
absKAc-noTS : (l : Link) (d : Dir) (q : KAcPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (absKAc l d q) (ιTS e₁) a
absKAc-noTS l d q e₁ {a} with NS.kaCfin (coarsenKAc q) in fEq
... | true  = viewV→noOffer (absKAc l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAc l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιTS e₁} {a = a} fEq (kaCnxt-noTS l d (coarsenKAc q) e₁ {a = a}))
absKAs-noTS : (l : Link) (d : Dir) (q : KAsPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (absKAs l d q) (ιTS e₁) a
absKAs-noTS l d q e₁ {a} with NS.kaSfin (coarsenKAs q) in fEq
... | true  = viewV→noOffer (absKAs l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAs l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιTS e₁} {a = a} fEq (kaSnxt-noTS l d (coarsenKAs q) e₁ {a = a}))
absLNc-noTS : (l : Link) (d : Dir) (q : LNcPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (absLNc l d q) (ιTS e₁) a
absLNc-noTS l d q e₁ {a} with NS.lnCfin (coarsenLNc q) in fEq
... | true  = viewV→noOffer (absLNc l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d })
                   (coarsenLNc q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNc l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d })
                   (coarsenLNc q) {e = ιTS e₁} {a = a} fEq (lnCnxt-noTS l d (coarsenLNc q) e₁ {a = a}))
absLNs-noTS : (l : Link) (d : Dir) (q : LNsPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (absLNs l d q) (ιTS e₁) a
absLNs-noTS l d q e₁ {a} with NS.lnSfin (coarsenLNs q) in fEq
... | true  = viewV→noOffer (absLNs l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d })
                   (coarsenLNs q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNs l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d })
                   (coarsenLNs q) {e = ιTS e₁} {a = a} fEq (lnSnxt-noTS l d (coarsenLNs q) e₁ {a = a}))
absLFc-noTS : (l : Link) (d : Dir) (q : LFcPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (absLFc l d q) (ιTS e₁) a
absLFc-noTS l d q e₁ {a} with NS.lfCfin (coarsenLFc q) in fEq
... | true  = viewV→noOffer (absLFc l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d })
                   (coarsenLFc q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFc l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d })
                   (coarsenLFc q) {e = ιTS e₁} {a = a} fEq (lfCnxt-noTS l d (coarsenLFc q) e₁ {a = a}))
absLFs-noTS : (l : Link) (d : Dir) (q : LFsPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (absLFs l d q) (ιTS e₁) a
absLFs-noTS l d q e₁ {a} with NS.lfSfin (coarsenLFs q) in fEq
... | true  = viewV→noOffer (absLFs l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d })
                   (coarsenLFs q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFs l d q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d })
                   (coarsenLFs q) {e = ιTS e₁} {a = a} fEq (lfSnxt-noTS l d (coarsenLFs q) e₁ {a = a}))

-- concrete CS/BF peers never fire ANY TS-image event (opposite protocol)
decCSc-noTSgen : (l : Link) (d : Dir) (pos : CScPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (decCSc l d pos) (ιTS e₁) a
decCSc-noTSgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSc-src l d pos) (ιCS⁻¹∘ιTS e₁)
decCSs-noTSgen : (l : Link) (d : Dir) (pos : CSsPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (decCSs l d pos) (ιTS e₁) a
decCSs-noTSgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSs-src l d pos) (ιCS⁻¹∘ιTS e₁)
decBFc-noTSgen : (l : Link) (d : Dir) (pos : BFcPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (decBFc l d pos) (ιTS e₁) a
decBFc-noTSgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFc-src l d pos) (ιBF⁻¹∘ιTS e₁)
decBFs-noTSgen : (l : Link) (d : Dir) (pos : BFsPos) {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (decBFs l d pos) (ιTS e₁) a
decBFs-noTSgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFs-src l d pos) (ιBF⁻¹∘ιTS e₁)

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER C1 — TxSubmission direction table-nothing lemmas
-- + same-role opposite-direction abstract non-offers + the two ⦀-tail
-- non-offers used by the bundle-TS-ev-inv evBoth refutations.
------------------------------------------------------------------------

tsCnxt-dir-no : (l : Link) (d : Dir) (q : NS.TScPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → tsEvDir e₁ ≢ d → NS.tsCnxt l d q (X , ιTS e₁) a ≡ nothing
tsCnxt-dir-no l d NS.tcInit (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d NS.tcInit (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcInit (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-dir-no l d NS.tcInit (TS.doneTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSInit} ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSDone} ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.sendTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-dir-no l d NS.tcIdle (TS.doneTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d (NS.tcAri (Blocking , a , r)) (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (Blocking , a , r)) (TS.sendTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (Blocking , a , r)) (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (Blocking , a , r)) (TS.doneTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d (NS.tcAri (NonBlocking , a , r)) (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (NonBlocking , a , r)) (TS.sendTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (NonBlocking , a , r)) (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcAri (NonBlocking , a , r)) (TS.doneTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d = refl
tsCnxt-dir-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsCnxt-dir-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsCnxt-dir-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-dir-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-dir-no l d (NS.tcArt _) (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-dir-no l d (NS.tcArt _) (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d = refl
tsCnxt-dir-no l d (NS.tcArt _) (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d (NS.tcArt _) (TS.sendTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcArt _) (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcArt _) (TS.doneTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsCnxt-dir-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSDone) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-dir-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-dir-no l d NS.tcBlk (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-dir-no l d NS.tcBlk (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d = refl
tsCnxt-dir-no l d NS.tcBlk (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsCnxt-dir-no l d NS.tcBlk (TS.sendTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcBlk (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcBlk (TS.doneTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsCnxt-dir-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsCnxt-dir-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-dir-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-dir-no l d NS.tcNbl (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-dir-no l d NS.tcNbl (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d = refl
tsCnxt-dir-no l d NS.tcNbl (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsCnxt-dir-no l d NS.tcNbl (TS.sendTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcNbl (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcNbl (TS.doneTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d = refl
tsCnxt-dir-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsCnxt-dir-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d = refl
tsCnxt-dir-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d = refl
tsCnxt-dir-no l d NS.tcTxs (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d = refl
tsCnxt-dir-no l d NS.tcTxs (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d = refl
tsCnxt-dir-no l d NS.tcTxs (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsCnxt-dir-no l d NS.tcTxs (TS.sendTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcTxs (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcTxs (TS.doneTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcWri _) (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d (NS.tcWri _) (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcWri _) (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-dir-no l d (NS.tcWri _) (TS.doneTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcWdone (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d NS.tcWdone (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcWdone (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-dir-no l d NS.tcWdone (TS.doneTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcWrt _) (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsCnxt-dir-no l d (NS.tcWrt _) (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-dir-no l d (NS.tcWrt _) (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-dir-no l d (NS.tcWrt _) (TS.doneTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcTerm (TS.sendTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcTerm (TS.receiveTS l′ d′) ¬d = refl
tsCnxt-dir-no l d NS.tcTerm (TS.apiTSev l′ d′ m) ¬d = refl
tsCnxt-dir-no l d NS.tcTerm (TS.doneTS l′ d′) ¬d = refl

tsSnxt-dir-no : (l : Link) (d : Dir) (q : NS.TSsPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → tsEvDir e₁ ≢ d → NS.tsSnxt l d q (X , ιTS e₁) a ≡ nothing
tsSnxt-dir-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSInit} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSDone} ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.sendTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-dir-no l d NS.tsInit (TS.doneTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSReplyTxIds) ¬d = refl
tsSnxt-dir-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSReplyTxs) ¬d = refl
tsSnxt-dir-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSDone) ¬d = refl
tsSnxt-dir-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSRequestTxIdsBlocking) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSRequestTxIdsPipelined) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d NS.tsIdle (TS.apiTSev l′ d′ sendTSRequestTxsPipelined) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d NS.tsIdle (TS.apiTSev l′ d′ recvTSRequestTxIds) ¬d = refl
tsSnxt-dir-no l d NS.tsIdle (TS.apiTSev l′ d′ recvTSRequestTxs) ¬d = refl
tsSnxt-dir-no l d NS.tsIdle (TS.sendTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsIdle (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsIdle (TS.doneTS l′ d′) ¬d = refl
tsSnxt-dir-no l d (NS.tsWib _) (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d (NS.tsWib _) (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-dir-no l d (NS.tsWib _) (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-dir-no l d (NS.tsWib _) (TS.doneTS l′ d′) ¬d = refl
tsSnxt-dir-no l d (NS.tsWin _) (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d (NS.tsWin _) (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-dir-no l d (NS.tsWin _) (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-dir-no l d (NS.tsWin _) (TS.doneTS l′ d′) ¬d = refl
tsSnxt-dir-no l d (NS.tsWrt _) (TS.sendTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d (NS.tsWrt _) (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-dir-no l d (NS.tsWrt _) (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-dir-no l d (NS.tsWrt _) (TS.doneTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSInit} ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSDone} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.sendTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-dir-no l d NS.tsBlk (TS.doneTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSInit} ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSDone} ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.sendTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-dir-no l d NS.tsNbl (TS.doneTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSInit} ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , txSubmission MsgTSDone} ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.receiveTS l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.sendTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-dir-no l d NS.tsTxs (TS.doneTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsDdone (TS.doneTS l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
tsSnxt-dir-no l d NS.tsDdone (TS.sendTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsDdone (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsDdone (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-dir-no l d NS.tsTerm (TS.sendTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsTerm (TS.receiveTS l′ d′) ¬d = refl
tsSnxt-dir-no l d NS.tsTerm (TS.apiTSev l′ d′ m) ¬d = refl
tsSnxt-dir-no l d NS.tsTerm (TS.doneTS l′ d′) ¬d = refl

-- absTSc-dir-noBoth / absTSs-dir-noBoth: the same-protocol OPPOSITE-role abstract
-- sibling (dir sv) does not fire the driven peer's wrong-direction TS event
absTSc-dir-noBoth : (l : Link) (sv : Dir) (q : TScPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → tsEvDir e₁ ≢ sv → ¬ IoOffers (absTSc l sv q) (ιTS e₁) a
absTSc-dir-noBoth l sv q e₁ {a} ¬d with NS.tsCfin (coarsenTSc q) in fEq
... | true  = viewV→noOffer (absTSc l sv q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l sv })
                   (coarsenTSc q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSc l sv q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l sv })
                   (coarsenTSc q) {e = ιTS e₁} {a = a} fEq (tsCnxt-dir-no l sv (coarsenTSc q) e₁ {a = a} ¬d))
absTSs-dir-noBoth : (l : Link) (sv : Dir) (q : TSsPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → tsEvDir e₁ ≢ sv → ¬ IoOffers (absTSs l sv q) (ιTS e₁) a
absTSs-dir-noBoth l sv q e₁ {a} ¬d with NS.tsSfin (coarsenTSs q) in fEq
... | true  = viewV→noOffer (absTSs l sv q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l sv })
                   (coarsenTSs q) {e = ιTS e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSs l sv q) {e = ιTS e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l sv })
                   (coarsenTSs q) {e = ιTS e₁} {a = a} fEq (tsSnxt-dir-no l sv (coarsenTSs q) e₁ {a = a} ¬d))

-- tail (LNc ⦀ LNs ⦀ LFc ⦀ LFs) offers no TS-image event (all inert, opposite protocol)
tsTail-lnc-noOffer : (l : Link) (cl sv : Dir) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X}
  → ¬ IoOffers (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))) (ιTS e₁) a
tsTail-lnc-noOffer l cl sv ip e₁ =
  SStep.⦀-noOffer (decLNc l cl (lnc ip)) _ (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιTS e₁))
    (SStep.⦀-noOffer (decLNs l sv (lns ip)) _ (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιTS e₁))
      (SStep.⦀-noOffer (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip))
        (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιTS e₁))
        (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιTS e₁))))

-- tail (decTSs ⦀ LNc ⦀ …) offers no TS-image event when tsEvDir e₁ ≢ sv (TS-client peel)
tsTail-tss-noOffer : (l : Link) (cl sv : Dir) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : TS.TSEv X) {a : X} → tsEvDir e₁ ≢ sv
  → ¬ IoOffers (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))) (ιTS e₁) a
tsTail-tss-noOffer l cl sv ip e₁ ¬sv =
  SStep.⦀-noOffer (decTSs l sv (tss ip)) _ (decTSs-dir-noOffer l sv (tss ip) e₁ ¬sv)
    (tsTail-lnc-noOffer l cl sv ip e₁)

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER C2 — the 12-peer bundle ev-inversion, TS channel
-- (driven-in-place TS peers at bundle positions #6 / #7, tracked by the
-- `tsc`/`tss` InertPos fields).  Re-verifies the M4 evBoth sidestep.
------------------------------------------------------------------------

-- TS-client advances: rebuild the abstract bundle step (dir cl, tsEvDir e₁≡cl)
absBundle-TSc-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {tsc′ : TScPos}
  → cl ≢ sv → tsEvDir e₁ ≡ cl
  → absTSc l cl (tsc ip) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► absTSc l cl tsc′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc qbs (record ip { tsc = tsc′ })
absBundle-TSc-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} {tsc′} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-R (absCSs l sv qcs) _
          (SStep.⦀-ev-R (absBFc l cl qbc) _
            (SStep.⦀-ev-R (absBFs l sv qbs) _
              (SStep.⦀-ev-L (absTSc l cl (tsc ip)) _ astep
                (⦀-viewV-nothing (absTSs l sv (tss ip)) _ (absTSs-dir-noBoth l sv (tss ip) e₁ ¬sv)
                  (SStep.⦀-noOffer (absLNc l cl (lnc ip)) _ (absLNc-noTS l cl (lnc ip) e₁)
                    (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noTS l sv (lns ip) e₁)
                      (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
                        (absLFc-noTS l cl (lfc ip) e₁) (absLFs-noTS l sv (lfs ip) e₁))))))
              (noOffer→viewV (absBFs l sv qbs) (absBFs-noTS l sv qbs e₁)))
            (noOffer→viewV (absBFc l cl qbc) (absBFc-noTS l cl qbc e₁)))
          (noOffer→viewV (absCSs l sv qcs) (absCSs-noTS l sv qcs e₁)))
        (noOffer→viewV (absCSc l cl qcc) (absCSc-noTS l cl qcc e₁)))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noTS l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noTS l cl (kac ip) e₁))
  where ¬sv : tsEvDir e₁ ≢ sv
        ¬sv q = cl≢sv (trans (sym eqd) q)

-- TS-server advances: rebuild the abstract bundle step (dir sv, tsEvDir e₁≡sv)
absBundle-TSs-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {tss′ : TSsPos}
  → cl ≢ sv → tsEvDir e₁ ≡ sv
  → absTSs l sv (tss ip) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► absTSs l sv tss′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc qbs (record ip { tss = tss′ })
absBundle-TSs-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} {tss′} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-R (absCSs l sv qcs) _
          (SStep.⦀-ev-R (absBFc l cl qbc) _
            (SStep.⦀-ev-R (absBFs l sv qbs) _
              (SStep.⦀-ev-R (absTSc l cl (tsc ip)) _
                (SStep.⦀-ev-L (absTSs l sv (tss ip)) _ astep
                  (⦀-viewV-nothing (absLNc l cl (lnc ip)) _ (absLNc-noTS l cl (lnc ip) e₁)
                    (SStep.⦀-noOffer (absLNs l sv (lns ip)) _ (absLNs-noTS l sv (lns ip) e₁)
                      (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
                        (absLFc-noTS l cl (lfc ip) e₁) (absLFs-noTS l sv (lfs ip) e₁)))))
                (noOffer→viewV (absTSc l cl (tsc ip)) (absTSc-dir-noBoth l cl (tsc ip) e₁ ¬cl)))
              (noOffer→viewV (absBFs l sv qbs) (absBFs-noTS l sv qbs e₁)))
            (noOffer→viewV (absBFc l cl qbc) (absBFc-noTS l cl qbc e₁)))
          (noOffer→viewV (absCSs l sv qcs) (absCSs-noTS l sv qcs e₁)))
        (noOffer→viewV (absCSc l cl qcc) (absCSc-noTS l cl qcc e₁)))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noTS l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noTS l cl (kac ip) e₁))
  where ¬cl : tsEvDir e₁ ≢ cl
        ¬cl q = cl≢sv (sym (trans (sym eqd) q))

-- which driven TS peer of the bundle fired the TS-image event (+ target + abstract step)
data BundleTSEvR (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : TS.TSEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  btscE : (tsc′ : TScPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc bfs (record ip { tsc = tsc′ })
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► absBundleG l cl sv csc css bfc bfs (record ip { tsc = tsc′ })
        → BundleTSEvR l cl sv csc css bfc bfs ip e₁ a Bd′
  btssE : (tss′ : TSsPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc bfs (record ip { tss = tss′ })
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► absBundleG l cl sv csc css bfc bfs (record ip { tss = tss′ })
        → BundleTSEvR l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a TS-client driven step into the bundle result (TS client is peer #6)
finishTSc-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decTSc l cl (tsc ip) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► P′
  → BundleTSEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
        ⦀ (P′ ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))))
finishTSc-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simTSc′ l cl (tsc ip) sM
... | _ , tsc′ , _ , _ , Meq , aStep0 =
      btscE tsc′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
               ⦀ (z ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))) Meq)
        (absBundle-TSc-ev l cl sv csc css bfc bfs ip {tsc′ = tsc′} cl≢sv
          (sym (apiDir-inj (tsc-ev-dir l cl (tsc ip) sM) (tsApiDir e₁))) aStep0)

-- fold a TS-server driven step into the bundle result (TS server is peer #7)
finishTSs-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decTSs l sv (tss ip) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► P′
  → BundleTSEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
        ⦀ (decTSc l cl (tsc ip) ⦀ (P′ ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))))
finishTSs-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simTSs′ l sv (tss ip) sM
... | _ , tss′ , _ , _ , Meq , aStep0 =
      btssE tss′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
               ⦀ (decTSc l cl (tsc ip) ⦀ (z ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))) Meq)
        (absBundle-TSs-ev l cl sv csc css bfc bfs ip {tss′ = tss′} cl≢sv
          (sym (apiDir-inj (tss-ev-dir l sv (tss ip) sM) (tsApiDir e₁))) aStep0)

-- 12-peer bundle ev-inversion (TS): peel each `⦀`, refute the ten siblings, invert the driven TS peer
bundle-TS-ev-inv : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► Bd′
  → BundleTSEvR l cl sv csc css bfc bfs ip e₁ a Bd′
bundle-TS-ev-inv l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...             | PEA.evL _ sM = finishTSc-ev l cl sv csc css bfc bfs ip cl≢sv sM
...             | PEA.evBoth _ sM sTail =
                    ⊥-elim (tsTail-tss-noOffer l cl sv ip e₁
                              (λ q → cl≢sv (trans (apiDir-inj (tsc-ev-dir l cl (tsc ip) sM) (tsApiDir e₁)) q))
                              (_ , sTail))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = finishTSs-ev l cl sv csc css bfc bfs ip cl≢sv sM
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



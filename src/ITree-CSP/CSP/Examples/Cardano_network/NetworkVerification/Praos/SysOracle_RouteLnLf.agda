{-# OPTIONS --guardedness #-}

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
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysDecode
  using ( SysState; med; nA; nB; nC; nD; ⟦_⟧ )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysMedium
  using ( decMed; decLink; decCopy; MedState; mkMed; phase; broken
        ; CopyPhase; empty; full; draining; NetProcN; vis-of )
open import CSP.Examples.Cardano_network.Network p Payload using ( Copy )
import CSP.Operators {E = Net Payload} (Net-≟ {Payload}) as OpN
open OpN using ( ⦀⋆; Skip; ∅ES )
import Semantics.LTS {E = Net Payload} {I = ExtI (Net Payload)} as LN
import CSP.Laws.Traces.TraceLawsParallelElim (Net-≟ {Payload}) as PEN
open import CSP.Laws.Traces.TraceLawsParallel (Net-≟ {Payload}) using ( fPar-er; fPar-sr; fPar-nn )
open import Data.List using ( List; []; _∷_; length; lookup; updateAt; map )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( decNodeA; decNodeB; decNodeC; decNodeD; bundleG; bundleA )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep
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
  using ( apiES; linkAB; linkAC; linkBD; linkCD; Block₃; b1; produce )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode as SN
import CSP.Examples.Cardano_network.NetworkVerification.Praos.NodeSpecs as NS
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
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( CScPos; csHead; csReqNext1; csFindInt1; csDone1
        ; csRF1; csRB1; csIF1; csINF1; csSil
        ; decCSc; decCSc-src )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
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
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
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
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
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
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( succVK; vis-ofK; KAProc )
import Semantics.LTS {E = KA.KAEv} {I = ExtI KA.KAEv} as KAL
open import CSP.Examples.Cardano_network.Net p using
  ( sendKAMsg; sendKADone; errCookie; recvKACookie )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgKeepAlive; MsgKeepAliveResponse; MsgKADone )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( succVT; vis-ofT; TSProc )
import Semantics.LTS {E = TS.TSEv} {I = ExtI TS.TSEv} as TSL
open import CSP.Examples.Cardano_network.Net p using
  ( sendTSReplyTxIds; sendTSReplyTxs; sendTSDone
  ; sendTSRequestTxIdsBlocking; sendTSRequestTxIdsPipelined; sendTSRequestTxsPipelined
  ; recvTSRequestTxIds; recvTSRequestTxs )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgTSInit; MsgTSRequestTxIds; MsgTSReplyTxIds; MsgTSRequestTxs; MsgTSReplyTxs; MsgTSDone )
open import Data.List.Properties using (≡-dec)
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( succVN; vis-ofN; LNProc )
import Semantics.LTS {E = LNp.LNEv} {I = ExtI LNp.LNEv} as LNL
open import CSP.Examples.Cardano_network.Net p using
  ( sendLNRequestNext; sendLNDone; sendLNBlockAnnouncement; sendLNBlockOffer
  ; sendLNBlockTxsOffer; sendLNVotesOffer; recvLNBlockAnnouncement
  ; recvLNBlockOffer; recvLNBlockTxsOffer; recvLNVotesOffer )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgLNRequestNext; MsgLNBlockAnnouncement; MsgLNBlockOffer
  ; MsgLNBlockTxsOffer; MsgLNVotesOffer; MsgLNDone )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
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
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep as SStep

module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_RouteLnLf where
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_RouteKaTs public

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER A — LN channel direction machinery.
------------------------------------------------------------------------
ιCS⁻¹∘ιLN : {X : Set 0ℓ} (e₁ : LNp.LNEv X) → ιCS⁻¹ (ιLN e₁) ≡ nothing
ιCS⁻¹∘ιLN (LNp.sendLN l d)    = refl
ιCS⁻¹∘ιLN (LNp.receiveLN l d) = refl
ιCS⁻¹∘ιLN (LNp.apiLNev l d m) = refl
ιCS⁻¹∘ιLN (LNp.doneLN l d)    = refl
ιBF⁻¹∘ιLN : {X : Set 0ℓ} (e₁ : LNp.LNEv X) → ιBF⁻¹ (ιLN e₁) ≡ nothing
ιBF⁻¹∘ιLN (LNp.sendLN l d)    = refl
ιBF⁻¹∘ιLN (LNp.receiveLN l d) = refl
ιBF⁻¹∘ιLN (LNp.apiLNev l d m) = refl
ιBF⁻¹∘ιLN (LNp.doneLN l d)    = refl
ιKA⁻¹∘ιLN : {X : Set 0ℓ} (e₁ : LNp.LNEv X) → ιKA⁻¹ (ιLN e₁) ≡ nothing
ιKA⁻¹∘ιLN (LNp.sendLN l d)    = refl
ιKA⁻¹∘ιLN (LNp.receiveLN l d) = refl
ιKA⁻¹∘ιLN (LNp.apiLNev l d m) = refl
ιKA⁻¹∘ιLN (LNp.doneLN l d)    = refl
ιTS⁻¹∘ιLN : {X : Set 0ℓ} (e₁ : LNp.LNEv X) → ιTS⁻¹ (ιLN e₁) ≡ nothing
ιTS⁻¹∘ιLN (LNp.sendLN l d)    = refl
ιTS⁻¹∘ιLN (LNp.receiveLN l d) = refl
ιTS⁻¹∘ιLN (LNp.apiLNev l d m) = refl
ιTS⁻¹∘ιLN (LNp.doneLN l d)    = refl
ιLF⁻¹∘ιLN : {X : Set 0ℓ} (e₁ : LNp.LNEv X) → ιLF⁻¹ (ιLN e₁) ≡ nothing
ιLF⁻¹∘ιLN (LNp.sendLN l d)    = refl
ιLF⁻¹∘ιLN (LNp.receiveLN l d) = refl
ιLF⁻¹∘ιLN (LNp.apiLNev l d m) = refl
ιLF⁻¹∘ιLN (LNp.doneLN l d)    = refl

lnEvDir : {X : Set 0ℓ} → LNp.LNEv X → Dir
lnEvDir (LNp.sendLN l d)    = d
lnEvDir (LNp.receiveLN l d) = d
lnEvDir (LNp.apiLNev l d m) = d
lnEvDir (LNp.doneLN l d)    = d
lnApiDir : {X : Set 0ℓ} (e₁ : LNp.LNEv X) → ApiHasDir (lnEvDir e₁) (ιLN e₁)
lnApiDir (LNp.sendLN l d)    = ahIn
lnApiDir (LNp.receiveLN l d) = ahOut
lnApiDir (LNp.apiLNev l d m) = ahLN
lnApiDir (LNp.doneLN l d)    = ahDone
decLNc-src-dir : (l : Link) (d : Dir) (pos : LNcPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {P′ : LNProc}
  → decLNc-src l d pos LNL.─[ LNL.ev (LNL.evl (LNL.evLabel X e₁ a)) ]─► P′
  → lnEvDir e₁ ≡ d
-- head stIdle : fires apiLNev sendLNRequestNext / sendLNDone
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNRequestNext} {a} s with step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNDone} {a} s with step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockTxsOffer}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNVotesOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockTxsOffer}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNVotesOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-dir l d (lncHead LNp.stIdle) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
-- head stBusy : receives one of four notifications
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockAnnouncement h)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockOffer q)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockTxsOffer q)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNVotesOffer vs)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNRequestNext} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNDone} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-dir l d (lncHead LNp.stBusy) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
-- head stDone : ret, no visible step
decLNc-src-dir l d (lncHead LNp.stDone) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaf lncRann1 : fires apiLNev recvLNBlockAnnouncement h → lncSil stIdle
decLNc-src-dir l d (lncRann1 h) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockAnnouncement) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ h
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-dir l d (lncRann1 h) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
decLNc-src-dir l d (lncRann1 h) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
decLNc-src-dir l d (lncRann1 h) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
-- recv leaf lncRoff1 : fires apiLNev recvLNBlockOffer q → lncSil stIdle
decLNc-src-dir l d (lncRoff1 q) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ q
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-dir l d (lncRoff1 q) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
decLNc-src-dir l d (lncRoff1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
decLNc-src-dir l d (lncRoff1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
-- recv leaf lncRtxs1 : fires apiLNev recvLNBlockTxsOffer q → lncSil stIdle
decLNc-src-dir l d (lncRtxs1 q) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockTxsOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ q
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-dir l d (lncRtxs1 q) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
decLNc-src-dir l d (lncRtxs1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
decLNc-src-dir l d (lncRtxs1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
-- recv leaf lncRvot1 : fires apiLNev recvLNVotesOffer vs → lncSil stIdle
decLNc-src-dir l d (lncRvot1 vs) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNVotesOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val vs
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-dir l d (lncRvot1 vs) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
decLNc-src-dir l d (lncRvot1 vs) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
decLNc-src-dir l d (lncRvot1 vs) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
-- send leaf lncReq1 : fires sendLN MsgLNRequestNext → lncSil stBusy
decLNc-src-dir l d lncReq1 {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-dir l d lncReq1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
decLNc-src-dir l d lncReq1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
decLNc-src-dir l d lncReq1 {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
-- send leaf lncDone1 : fires sendLN MsgLNDone → lncSil stDone
decLNc-src-dir l d lncDone1 {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNc-src-dir l d lncDone1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
decLNc-src-dir l d lncDone1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
decLNc-src-dir l d lncDone1 {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
-- loop re-entry : sil, no visible step
decLNc-src-dir l d (lncSil st) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decLNs-src-dir : (l : Link) (d : Dir) (pos : LNsPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {P′ : LNProc}
  → decLNs-src l d pos LNL.─[ LNL.ev (LNL.evl (LNL.evLabel X e₁ a)) ]─► P′
  → lnEvDir e₁ ≡ d
-- head stIdle : receives MsgLNRequestNext (→ lnsSil stBusy) / MsgLNDone (→ lnsDone1)
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNRequestNext} s with step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNDone} s with step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-dir l d (lnsHead LNp.stIdle) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
-- head stBusy : fires one of four api sends
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockAnnouncement} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockTxsOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNVotesOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNRequestNext} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNDone}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockOffer}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockTxsOffer} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNVotesOffer}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-dir l d (lnsHead LNp.stBusy) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
-- head stDone : ret, no visible step
decLNs-src-dir l d (lnsHead LNp.stDone) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf lnsDone1 : fires doneLN → lnsSil stDone
decLNs-src-dir l d lnsDone1 {e₁ = LNp.doneLN l' d'} {a} s with step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.doneLN l d) (_ , LNp.doneLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decLNs-src-dir l d lnsDone1 {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
decLNs-src-dir l d lnsDone1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
decLNs-src-dir l d lnsDone1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
-- send leaf lnsWann1 : fires sendLN (MsgLNBlockAnnouncement h) → lnsSil stIdle
decLNs-src-dir l d (lnsWann1 h) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-src-dir l d (lnsWann1 h) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
decLNs-src-dir l d (lnsWann1 h) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
decLNs-src-dir l d (lnsWann1 h) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
-- send leaf lnsWoff1 : fires sendLN (MsgLNBlockOffer q) → lnsSil stIdle
decLNs-src-dir l d (lnsWoff1 q) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-src-dir l d (lnsWoff1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
decLNs-src-dir l d (lnsWoff1 q) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
decLNs-src-dir l d (lnsWoff1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
-- send leaf lnsWtxs1 : fires sendLN (MsgLNBlockTxsOffer q) → lnsSil stIdle
decLNs-src-dir l d (lnsWtxs1 q) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-src-dir l d (lnsWtxs1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
decLNs-src-dir l d (lnsWtxs1 q) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
decLNs-src-dir l d (lnsWtxs1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
-- send leaf lnsWvot1 : fires sendLN (MsgLNVotesOffer vs) → lnsSil stIdle
decLNs-src-dir l d (lnsWvot1 vs) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLNs-src-dir l d (lnsWvot1 vs) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
decLNs-src-dir l d (lnsWvot1 vs) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
decLNs-src-dir l d (lnsWvot1 vs) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
-- loop re-entry : sil, no visible step
decLNs-src-dir l d (lnsSil st) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

lnc-ev-dir : (l : Link) (d : Dir) (pos : LNcPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decLNc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
lnc-ev-dir l d pos step with LNNO.renameMap-ev-reflect-ι {P = decLNc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιLN-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιLN e₁)) (decLNc-src-dir l d pos srcStep) (lnApiDir e₁))
lns-ev-dir : (l : Link) (d : Dir) (pos : LNsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decLNs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
lns-ev-dir l d pos step with LNNO.renameMap-ev-reflect-ι {P = decLNs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιLN-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιLN e₁)) (decLNs-src-dir l d pos srcStep) (lnApiDir e₁))

LNc-LNs-noBoth : (l : Link) (cl sv : Dir) → cl ≢ sv → (pc : LNcPos) (ps : LNsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {Mc Ms : NetProc}
  → decLNc l cl pc ─[ ev (evl (evLabel X e₂ a)) ]─► Mc
  → decLNs l sv ps ─[ ev (evl (evLabel X e₂ a)) ]─► Ms → ⊥
LNc-LNs-noBoth l cl sv cl≢sv pc ps sc ss =
  cl≢sv (apiDir-inj (lnc-ev-dir l cl pc sc) (lns-ev-dir l sv ps ss))

decLNc-dir-noOffer : (l : Link) (d : Dir) (pos : LNcPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → lnEvDir e₁ ≢ d → ¬ IoOffers (decLNc l d pos) (ιLN e₁) a
decLNc-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (lnc-ev-dir l d pos step) (lnApiDir e₁)))
decLNs-dir-noOffer : (l : Link) (d : Dir) (pos : LNsPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → lnEvDir e₁ ≢ d → ¬ IoOffers (decLNs l d pos) (ιLN e₁) a
decLNs-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (lns-ev-dir l d pos step) (lnApiDir e₁)))

simLNc′ : (l : Link) (d : Dir) (pos : LNcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decLNc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ LNp.LNEv X ] Σ[ pos′ ∈ LNcPos ]
       (e ≡ ιLN e₁) × (lnEvDir e₁ ≡ d) × (M ≡ decLNc l d pos′)
       × (absLNc l d pos ─[ ev (evl (evLabel X e a)) ]─► absLNc l d pos′)
simLNc′ l d pos step with LNNO.renameMap-ev-reflect-ι {P = decLNc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decLNc-src-ev-inv l d pos srcStep | ιLN-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decLNc-src-dir l d pos srcStep ,
        trans Meq (cong RenLN.renameMap P′eq) , aStep
simLNs′ : (l : Link) (d : Dir) (pos : LNsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decLNs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ LNp.LNEv X ] Σ[ pos′ ∈ LNsPos ]
       (e ≡ ιLN e₁) × (lnEvDir e₁ ≡ d) × (M ≡ decLNs l d pos′)
       × (absLNs l d pos ─[ ev (evl (evLabel X e a)) ]─► absLNs l d pos′)
simLNs′ l d pos step with LNNO.renameMap-ev-reflect-ι {P = decLNs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decLNs-src-ev-inv l d pos srcStep | ιLN-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decLNs-src-dir l d pos srcStep ,
        trans Meq (cong RenLN.renameMap P′eq) , aStep

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER B — LN channel abstract-side non-offers.
------------------------------------------------------------------------
csCnxt-noLN : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → NS.csCnxt l d q (X , ιLN e₁) a ≡ nothing
csCnxt-noLN l d NS.ccIdle (LNp.sendLN _ _) = refl
csCnxt-noLN l d NS.ccIdle (LNp.receiveLN _ _) = refl
csCnxt-noLN l d NS.ccIdle (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d NS.ccIdle (LNp.doneLN _ _) = refl
csCnxt-noLN l d NS.ccWreq (LNp.sendLN _ _) = refl
csCnxt-noLN l d NS.ccWreq (LNp.receiveLN _ _) = refl
csCnxt-noLN l d NS.ccWreq (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d NS.ccWreq (LNp.doneLN _ _) = refl
csCnxt-noLN l d NS.ccAwait (LNp.sendLN _ _) = refl
csCnxt-noLN l d NS.ccAwait (LNp.receiveLN _ _) = refl
csCnxt-noLN l d NS.ccAwait (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d NS.ccAwait (LNp.doneLN _ _) = refl
csCnxt-noLN l d (NS.ccWfi _) (LNp.sendLN _ _) = refl
csCnxt-noLN l d (NS.ccWfi _) (LNp.receiveLN _ _) = refl
csCnxt-noLN l d (NS.ccWfi _) (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d (NS.ccWfi _) (LNp.doneLN _ _) = refl
csCnxt-noLN l d NS.ccInt (LNp.sendLN _ _) = refl
csCnxt-noLN l d NS.ccInt (LNp.receiveLN _ _) = refl
csCnxt-noLN l d NS.ccInt (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d NS.ccInt (LNp.doneLN _ _) = refl
csCnxt-noLN l d NS.ccWdone (LNp.sendLN _ _) = refl
csCnxt-noLN l d NS.ccWdone (LNp.receiveLN _ _) = refl
csCnxt-noLN l d NS.ccWdone (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d NS.ccWdone (LNp.doneLN _ _) = refl
csCnxt-noLN l d NS.ccMust (LNp.sendLN _ _) = refl
csCnxt-noLN l d NS.ccMust (LNp.receiveLN _ _) = refl
csCnxt-noLN l d NS.ccMust (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d NS.ccMust (LNp.doneLN _ _) = refl
csCnxt-noLN l d (NS.ccArf _) (LNp.sendLN _ _) = refl
csCnxt-noLN l d (NS.ccArf _) (LNp.receiveLN _ _) = refl
csCnxt-noLN l d (NS.ccArf _) (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d (NS.ccArf _) (LNp.doneLN _ _) = refl
csCnxt-noLN l d (NS.ccArb _) (LNp.sendLN _ _) = refl
csCnxt-noLN l d (NS.ccArb _) (LNp.receiveLN _ _) = refl
csCnxt-noLN l d (NS.ccArb _) (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d (NS.ccArb _) (LNp.doneLN _ _) = refl
csCnxt-noLN l d (NS.ccAif _) (LNp.sendLN _ _) = refl
csCnxt-noLN l d (NS.ccAif _) (LNp.receiveLN _ _) = refl
csCnxt-noLN l d (NS.ccAif _) (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d (NS.ccAif _) (LNp.doneLN _ _) = refl
csCnxt-noLN l d (NS.ccAin _) (LNp.sendLN _ _) = refl
csCnxt-noLN l d (NS.ccAin _) (LNp.receiveLN _ _) = refl
csCnxt-noLN l d (NS.ccAin _) (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d (NS.ccAin _) (LNp.doneLN _ _) = refl
csCnxt-noLN l d NS.ccTerm (LNp.sendLN _ _) = refl
csCnxt-noLN l d NS.ccTerm (LNp.receiveLN _ _) = refl
csCnxt-noLN l d NS.ccTerm (LNp.apiLNev _ _ _) = refl
csCnxt-noLN l d NS.ccTerm (LNp.doneLN _ _) = refl
csSnxt-noLN : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → NS.csSnxt l d q (X , ιLN e₁) a ≡ nothing
csSnxt-noLN l d NS.csIdle (LNp.sendLN _ _) = refl
csSnxt-noLN l d NS.csIdle (LNp.receiveLN _ _) = refl
csSnxt-noLN l d NS.csIdle (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d NS.csIdle (LNp.doneLN _ _) = refl
csSnxt-noLN l d NS.csAreq (LNp.sendLN _ _) = refl
csSnxt-noLN l d NS.csAreq (LNp.receiveLN _ _) = refl
csSnxt-noLN l d NS.csAreq (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d NS.csAreq (LNp.doneLN _ _) = refl
csSnxt-noLN l d NS.csCanAwait (LNp.sendLN _ _) = refl
csSnxt-noLN l d NS.csCanAwait (LNp.receiveLN _ _) = refl
csSnxt-noLN l d NS.csCanAwait (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d NS.csCanAwait (LNp.doneLN _ _) = refl
csSnxt-noLN l d (NS.csAfi _) (LNp.sendLN _ _) = refl
csSnxt-noLN l d (NS.csAfi _) (LNp.receiveLN _ _) = refl
csSnxt-noLN l d (NS.csAfi _) (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d (NS.csAfi _) (LNp.doneLN _ _) = refl
csSnxt-noLN l d NS.csInt (LNp.sendLN _ _) = refl
csSnxt-noLN l d NS.csInt (LNp.receiveLN _ _) = refl
csSnxt-noLN l d NS.csInt (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d NS.csInt (LNp.doneLN _ _) = refl
csSnxt-noLN l d NS.csDdone (LNp.sendLN _ _) = refl
csSnxt-noLN l d NS.csDdone (LNp.receiveLN _ _) = refl
csSnxt-noLN l d NS.csDdone (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d NS.csDdone (LNp.doneLN _ _) = refl
csSnxt-noLN l d NS.csMust (LNp.sendLN _ _) = refl
csSnxt-noLN l d NS.csMust (LNp.receiveLN _ _) = refl
csSnxt-noLN l d NS.csMust (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d NS.csMust (LNp.doneLN _ _) = refl
csSnxt-noLN l d (NS.csWrf _) (LNp.sendLN _ _) = refl
csSnxt-noLN l d (NS.csWrf _) (LNp.receiveLN _ _) = refl
csSnxt-noLN l d (NS.csWrf _) (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d (NS.csWrf _) (LNp.doneLN _ _) = refl
csSnxt-noLN l d (NS.csWrb _) (LNp.sendLN _ _) = refl
csSnxt-noLN l d (NS.csWrb _) (LNp.receiveLN _ _) = refl
csSnxt-noLN l d (NS.csWrb _) (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d (NS.csWrb _) (LNp.doneLN _ _) = refl
csSnxt-noLN l d NS.csWar (LNp.sendLN _ _) = refl
csSnxt-noLN l d NS.csWar (LNp.receiveLN _ _) = refl
csSnxt-noLN l d NS.csWar (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d NS.csWar (LNp.doneLN _ _) = refl
csSnxt-noLN l d (NS.csWif _) (LNp.sendLN _ _) = refl
csSnxt-noLN l d (NS.csWif _) (LNp.receiveLN _ _) = refl
csSnxt-noLN l d (NS.csWif _) (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d (NS.csWif _) (LNp.doneLN _ _) = refl
csSnxt-noLN l d (NS.csWin _) (LNp.sendLN _ _) = refl
csSnxt-noLN l d (NS.csWin _) (LNp.receiveLN _ _) = refl
csSnxt-noLN l d (NS.csWin _) (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d (NS.csWin _) (LNp.doneLN _ _) = refl
csSnxt-noLN l d NS.csTerm (LNp.sendLN _ _) = refl
csSnxt-noLN l d NS.csTerm (LNp.receiveLN _ _) = refl
csSnxt-noLN l d NS.csTerm (LNp.apiLNev _ _ _) = refl
csSnxt-noLN l d NS.csTerm (LNp.doneLN _ _) = refl
bfCnxt-noLN : (l : Link) (d : Dir) (q : NS.BFcPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → NS.bfCnxt l d q (X , ιLN e₁) a ≡ nothing
bfCnxt-noLN l d NS.bcIdle (LNp.sendLN _ _) = refl
bfCnxt-noLN l d NS.bcIdle (LNp.receiveLN _ _) = refl
bfCnxt-noLN l d NS.bcIdle (LNp.apiLNev _ _ _) = refl
bfCnxt-noLN l d NS.bcIdle (LNp.doneLN _ _) = refl
bfCnxt-noLN l d (NS.bcWrr _) (LNp.sendLN _ _) = refl
bfCnxt-noLN l d (NS.bcWrr _) (LNp.receiveLN _ _) = refl
bfCnxt-noLN l d (NS.bcWrr _) (LNp.apiLNev _ _ _) = refl
bfCnxt-noLN l d (NS.bcWrr _) (LNp.doneLN _ _) = refl
bfCnxt-noLN l d NS.bcBusy (LNp.sendLN _ _) = refl
bfCnxt-noLN l d NS.bcBusy (LNp.receiveLN _ _) = refl
bfCnxt-noLN l d NS.bcBusy (LNp.apiLNev _ _ _) = refl
bfCnxt-noLN l d NS.bcBusy (LNp.doneLN _ _) = refl
bfCnxt-noLN l d NS.bcWcd (LNp.sendLN _ _) = refl
bfCnxt-noLN l d NS.bcWcd (LNp.receiveLN _ _) = refl
bfCnxt-noLN l d NS.bcWcd (LNp.apiLNev _ _ _) = refl
bfCnxt-noLN l d NS.bcWcd (LNp.doneLN _ _) = refl
bfCnxt-noLN l d NS.bcStream (LNp.sendLN _ _) = refl
bfCnxt-noLN l d NS.bcStream (LNp.receiveLN _ _) = refl
bfCnxt-noLN l d NS.bcStream (LNp.apiLNev _ _ _) = refl
bfCnxt-noLN l d NS.bcStream (LNp.doneLN _ _) = refl
bfCnxt-noLN l d (NS.bcAblk _) (LNp.sendLN _ _) = refl
bfCnxt-noLN l d (NS.bcAblk _) (LNp.receiveLN _ _) = refl
bfCnxt-noLN l d (NS.bcAblk _) (LNp.apiLNev _ _ _) = refl
bfCnxt-noLN l d (NS.bcAblk _) (LNp.doneLN _ _) = refl
bfCnxt-noLN l d NS.bcTerm (LNp.sendLN _ _) = refl
bfCnxt-noLN l d NS.bcTerm (LNp.receiveLN _ _) = refl
bfCnxt-noLN l d NS.bcTerm (LNp.apiLNev _ _ _) = refl
bfCnxt-noLN l d NS.bcTerm (LNp.doneLN _ _) = refl
bfSnxt-noLN : (l : Link) (d : Dir) (q : NS.BFsPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → NS.bfSnxt l d q (X , ιLN e₁) a ≡ nothing
bfSnxt-noLN l d NS.bsIdle (LNp.sendLN _ _) = refl
bfSnxt-noLN l d NS.bsIdle (LNp.receiveLN _ _) = refl
bfSnxt-noLN l d NS.bsIdle (LNp.apiLNev _ _ _) = refl
bfSnxt-noLN l d NS.bsIdle (LNp.doneLN _ _) = refl
bfSnxt-noLN l d (NS.bsAreq _) (LNp.sendLN _ _) = refl
bfSnxt-noLN l d (NS.bsAreq _) (LNp.receiveLN _ _) = refl
bfSnxt-noLN l d (NS.bsAreq _) (LNp.apiLNev _ _ _) = refl
bfSnxt-noLN l d (NS.bsAreq _) (LNp.doneLN _ _) = refl
bfSnxt-noLN l d NS.bsBusy (LNp.sendLN _ _) = refl
bfSnxt-noLN l d NS.bsBusy (LNp.receiveLN _ _) = refl
bfSnxt-noLN l d NS.bsBusy (LNp.apiLNev _ _ _) = refl
bfSnxt-noLN l d NS.bsBusy (LNp.doneLN _ _) = refl
bfSnxt-noLN l d NS.bsDdone (LNp.sendLN _ _) = refl
bfSnxt-noLN l d NS.bsDdone (LNp.receiveLN _ _) = refl
bfSnxt-noLN l d NS.bsDdone (LNp.apiLNev _ _ _) = refl
bfSnxt-noLN l d NS.bsDdone (LNp.doneLN _ _) = refl
bfSnxt-noLN l d NS.bsWsb (LNp.sendLN _ _) = refl
bfSnxt-noLN l d NS.bsWsb (LNp.receiveLN _ _) = refl
bfSnxt-noLN l d NS.bsWsb (LNp.apiLNev _ _ _) = refl
bfSnxt-noLN l d NS.bsWsb (LNp.doneLN _ _) = refl
bfSnxt-noLN l d NS.bsStream (LNp.sendLN _ _) = refl
bfSnxt-noLN l d NS.bsStream (LNp.receiveLN _ _) = refl
bfSnxt-noLN l d NS.bsStream (LNp.apiLNev _ _ _) = refl
bfSnxt-noLN l d NS.bsStream (LNp.doneLN _ _) = refl
bfSnxt-noLN l d NS.bsWnb (LNp.sendLN _ _) = refl
bfSnxt-noLN l d NS.bsWnb (LNp.receiveLN _ _) = refl
bfSnxt-noLN l d NS.bsWnb (LNp.apiLNev _ _ _) = refl
bfSnxt-noLN l d NS.bsWnb (LNp.doneLN _ _) = refl
bfSnxt-noLN l d (NS.bsWblk _) (LNp.sendLN _ _) = refl
bfSnxt-noLN l d (NS.bsWblk _) (LNp.receiveLN _ _) = refl
bfSnxt-noLN l d (NS.bsWblk _) (LNp.apiLNev _ _ _) = refl
bfSnxt-noLN l d (NS.bsWblk _) (LNp.doneLN _ _) = refl
bfSnxt-noLN l d NS.bsWbd (LNp.sendLN _ _) = refl
bfSnxt-noLN l d NS.bsWbd (LNp.receiveLN _ _) = refl
bfSnxt-noLN l d NS.bsWbd (LNp.apiLNev _ _ _) = refl
bfSnxt-noLN l d NS.bsWbd (LNp.doneLN _ _) = refl
bfSnxt-noLN l d NS.bsTerm (LNp.sendLN _ _) = refl
bfSnxt-noLN l d NS.bsTerm (LNp.receiveLN _ _) = refl
bfSnxt-noLN l d NS.bsTerm (LNp.apiLNev _ _ _) = refl
bfSnxt-noLN l d NS.bsTerm (LNp.doneLN _ _) = refl
kaCnxt-noLN : (l : Link) (d : Dir) (q : NS.KAcPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → NS.kaCnxt l d q (X , ιLN e₁) a ≡ nothing
kaCnxt-noLN l d NS.kcClient (LNp.sendLN _ _) = refl
kaCnxt-noLN l d NS.kcClient (LNp.receiveLN _ _) = refl
kaCnxt-noLN l d NS.kcClient (LNp.apiLNev _ _ _) = refl
kaCnxt-noLN l d NS.kcClient (LNp.doneLN _ _) = refl
kaCnxt-noLN l d (NS.kcWmsg _) (LNp.sendLN _ _) = refl
kaCnxt-noLN l d (NS.kcWmsg _) (LNp.receiveLN _ _) = refl
kaCnxt-noLN l d (NS.kcWmsg _) (LNp.apiLNev _ _ _) = refl
kaCnxt-noLN l d (NS.kcWmsg _) (LNp.doneLN _ _) = refl
kaCnxt-noLN l d (NS.kcAwait _) (LNp.sendLN _ _) = refl
kaCnxt-noLN l d (NS.kcAwait _) (LNp.receiveLN _ _) = refl
kaCnxt-noLN l d (NS.kcAwait _) (LNp.apiLNev _ _ _) = refl
kaCnxt-noLN l d (NS.kcAwait _) (LNp.doneLN _ _) = refl
kaCnxt-noLN l d NS.kcWdone (LNp.sendLN _ _) = refl
kaCnxt-noLN l d NS.kcWdone (LNp.receiveLN _ _) = refl
kaCnxt-noLN l d NS.kcWdone (LNp.apiLNev _ _ _) = refl
kaCnxt-noLN l d NS.kcWdone (LNp.doneLN _ _) = refl
kaCnxt-noLN l d (NS.kcErr _ _) (LNp.sendLN _ _) = refl
kaCnxt-noLN l d (NS.kcErr _ _) (LNp.receiveLN _ _) = refl
kaCnxt-noLN l d (NS.kcErr _ _) (LNp.apiLNev _ _ _) = refl
kaCnxt-noLN l d (NS.kcErr _ _) (LNp.doneLN _ _) = refl
kaCnxt-noLN l d NS.kcTerm (LNp.sendLN _ _) = refl
kaCnxt-noLN l d NS.kcTerm (LNp.receiveLN _ _) = refl
kaCnxt-noLN l d NS.kcTerm (LNp.apiLNev _ _ _) = refl
kaCnxt-noLN l d NS.kcTerm (LNp.doneLN _ _) = refl
kaCnxt-noLN l d NS.kcTermE (LNp.sendLN _ _) = refl
kaCnxt-noLN l d NS.kcTermE (LNp.receiveLN _ _) = refl
kaCnxt-noLN l d NS.kcTermE (LNp.apiLNev _ _ _) = refl
kaCnxt-noLN l d NS.kcTermE (LNp.doneLN _ _) = refl
kaSnxt-noLN : (l : Link) (d : Dir) (q : NS.KAsPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → NS.kaSnxt l d q (X , ιLN e₁) a ≡ nothing
kaSnxt-noLN l d NS.ksClient (LNp.sendLN _ _) = refl
kaSnxt-noLN l d NS.ksClient (LNp.receiveLN _ _) = refl
kaSnxt-noLN l d NS.ksClient (LNp.apiLNev _ _ _) = refl
kaSnxt-noLN l d NS.ksClient (LNp.doneLN _ _) = refl
kaSnxt-noLN l d (NS.ksRecv _) (LNp.sendLN _ _) = refl
kaSnxt-noLN l d (NS.ksRecv _) (LNp.receiveLN _ _) = refl
kaSnxt-noLN l d (NS.ksRecv _) (LNp.apiLNev _ _ _) = refl
kaSnxt-noLN l d (NS.ksRecv _) (LNp.doneLN _ _) = refl
kaSnxt-noLN l d (NS.ksResp _) (LNp.sendLN _ _) = refl
kaSnxt-noLN l d (NS.ksResp _) (LNp.receiveLN _ _) = refl
kaSnxt-noLN l d (NS.ksResp _) (LNp.apiLNev _ _ _) = refl
kaSnxt-noLN l d (NS.ksResp _) (LNp.doneLN _ _) = refl
kaSnxt-noLN l d NS.ksDdone (LNp.sendLN _ _) = refl
kaSnxt-noLN l d NS.ksDdone (LNp.receiveLN _ _) = refl
kaSnxt-noLN l d NS.ksDdone (LNp.apiLNev _ _ _) = refl
kaSnxt-noLN l d NS.ksDdone (LNp.doneLN _ _) = refl
kaSnxt-noLN l d NS.ksTerm (LNp.sendLN _ _) = refl
kaSnxt-noLN l d NS.ksTerm (LNp.receiveLN _ _) = refl
kaSnxt-noLN l d NS.ksTerm (LNp.apiLNev _ _ _) = refl
kaSnxt-noLN l d NS.ksTerm (LNp.doneLN _ _) = refl
tsCnxt-noLN : (l : Link) (d : Dir) (q : NS.TScPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → NS.tsCnxt l d q (X , ιLN e₁) a ≡ nothing
tsCnxt-noLN l d NS.tcInit (LNp.sendLN _ _) = refl
tsCnxt-noLN l d NS.tcInit (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d NS.tcInit (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d NS.tcInit (LNp.doneLN _ _) = refl
tsCnxt-noLN l d NS.tcIdle (LNp.sendLN _ _) = refl
tsCnxt-noLN l d NS.tcIdle (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d NS.tcIdle (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d NS.tcIdle (LNp.doneLN _ _) = refl
tsCnxt-noLN l d (NS.tcAri (Blocking , _ , _)) (LNp.sendLN _ _) = refl
tsCnxt-noLN l d (NS.tcAri (Blocking , _ , _)) (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d (NS.tcAri (Blocking , _ , _)) (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d (NS.tcAri (Blocking , _ , _)) (LNp.doneLN _ _) = refl
tsCnxt-noLN l d (NS.tcAri (NonBlocking , _ , _)) (LNp.sendLN _ _) = refl
tsCnxt-noLN l d (NS.tcAri (NonBlocking , _ , _)) (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d (NS.tcAri (NonBlocking , _ , _)) (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d (NS.tcAri (NonBlocking , _ , _)) (LNp.doneLN _ _) = refl
tsCnxt-noLN l d NS.tcBlk (LNp.sendLN _ _) = refl
tsCnxt-noLN l d NS.tcBlk (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d NS.tcBlk (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d NS.tcBlk (LNp.doneLN _ _) = refl
tsCnxt-noLN l d NS.tcNbl (LNp.sendLN _ _) = refl
tsCnxt-noLN l d NS.tcNbl (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d NS.tcNbl (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d NS.tcNbl (LNp.doneLN _ _) = refl
tsCnxt-noLN l d (NS.tcArt _) (LNp.sendLN _ _) = refl
tsCnxt-noLN l d (NS.tcArt _) (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d (NS.tcArt _) (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d (NS.tcArt _) (LNp.doneLN _ _) = refl
tsCnxt-noLN l d NS.tcTxs (LNp.sendLN _ _) = refl
tsCnxt-noLN l d NS.tcTxs (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d NS.tcTxs (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d NS.tcTxs (LNp.doneLN _ _) = refl
tsCnxt-noLN l d (NS.tcWri _) (LNp.sendLN _ _) = refl
tsCnxt-noLN l d (NS.tcWri _) (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d (NS.tcWri _) (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d (NS.tcWri _) (LNp.doneLN _ _) = refl
tsCnxt-noLN l d NS.tcWdone (LNp.sendLN _ _) = refl
tsCnxt-noLN l d NS.tcWdone (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d NS.tcWdone (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d NS.tcWdone (LNp.doneLN _ _) = refl
tsCnxt-noLN l d (NS.tcWrt _) (LNp.sendLN _ _) = refl
tsCnxt-noLN l d (NS.tcWrt _) (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d (NS.tcWrt _) (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d (NS.tcWrt _) (LNp.doneLN _ _) = refl
tsCnxt-noLN l d NS.tcTerm (LNp.sendLN _ _) = refl
tsCnxt-noLN l d NS.tcTerm (LNp.receiveLN _ _) = refl
tsCnxt-noLN l d NS.tcTerm (LNp.apiLNev _ _ _) = refl
tsCnxt-noLN l d NS.tcTerm (LNp.doneLN _ _) = refl
tsSnxt-noLN : (l : Link) (d : Dir) (q : NS.TSsPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → NS.tsSnxt l d q (X , ιLN e₁) a ≡ nothing
tsSnxt-noLN l d NS.tsInit (LNp.sendLN _ _) = refl
tsSnxt-noLN l d NS.tsInit (LNp.receiveLN _ _) = refl
tsSnxt-noLN l d NS.tsInit (LNp.apiLNev _ _ _) = refl
tsSnxt-noLN l d NS.tsInit (LNp.doneLN _ _) = refl
tsSnxt-noLN l d NS.tsIdle (LNp.sendLN _ _) = refl
tsSnxt-noLN l d NS.tsIdle (LNp.receiveLN _ _) = refl
tsSnxt-noLN l d NS.tsIdle (LNp.apiLNev _ _ _) = refl
tsSnxt-noLN l d NS.tsIdle (LNp.doneLN _ _) = refl
tsSnxt-noLN l d (NS.tsWib _) (LNp.sendLN _ _) = refl
tsSnxt-noLN l d (NS.tsWib _) (LNp.receiveLN _ _) = refl
tsSnxt-noLN l d (NS.tsWib _) (LNp.apiLNev _ _ _) = refl
tsSnxt-noLN l d (NS.tsWib _) (LNp.doneLN _ _) = refl
tsSnxt-noLN l d (NS.tsWin _) (LNp.sendLN _ _) = refl
tsSnxt-noLN l d (NS.tsWin _) (LNp.receiveLN _ _) = refl
tsSnxt-noLN l d (NS.tsWin _) (LNp.apiLNev _ _ _) = refl
tsSnxt-noLN l d (NS.tsWin _) (LNp.doneLN _ _) = refl
tsSnxt-noLN l d (NS.tsWrt _) (LNp.sendLN _ _) = refl
tsSnxt-noLN l d (NS.tsWrt _) (LNp.receiveLN _ _) = refl
tsSnxt-noLN l d (NS.tsWrt _) (LNp.apiLNev _ _ _) = refl
tsSnxt-noLN l d (NS.tsWrt _) (LNp.doneLN _ _) = refl
tsSnxt-noLN l d NS.tsBlk (LNp.sendLN _ _) = refl
tsSnxt-noLN l d NS.tsBlk (LNp.receiveLN _ _) = refl
tsSnxt-noLN l d NS.tsBlk (LNp.apiLNev _ _ _) = refl
tsSnxt-noLN l d NS.tsBlk (LNp.doneLN _ _) = refl
tsSnxt-noLN l d NS.tsNbl (LNp.sendLN _ _) = refl
tsSnxt-noLN l d NS.tsNbl (LNp.receiveLN _ _) = refl
tsSnxt-noLN l d NS.tsNbl (LNp.apiLNev _ _ _) = refl
tsSnxt-noLN l d NS.tsNbl (LNp.doneLN _ _) = refl
tsSnxt-noLN l d NS.tsTxs (LNp.sendLN _ _) = refl
tsSnxt-noLN l d NS.tsTxs (LNp.receiveLN _ _) = refl
tsSnxt-noLN l d NS.tsTxs (LNp.apiLNev _ _ _) = refl
tsSnxt-noLN l d NS.tsTxs (LNp.doneLN _ _) = refl
tsSnxt-noLN l d NS.tsDdone (LNp.sendLN _ _) = refl
tsSnxt-noLN l d NS.tsDdone (LNp.receiveLN _ _) = refl
tsSnxt-noLN l d NS.tsDdone (LNp.apiLNev _ _ _) = refl
tsSnxt-noLN l d NS.tsDdone (LNp.doneLN _ _) = refl
tsSnxt-noLN l d NS.tsTerm (LNp.sendLN _ _) = refl
tsSnxt-noLN l d NS.tsTerm (LNp.receiveLN _ _) = refl
tsSnxt-noLN l d NS.tsTerm (LNp.apiLNev _ _ _) = refl
tsSnxt-noLN l d NS.tsTerm (LNp.doneLN _ _) = refl
lfCnxt-noLN : (l : Link) (d : Dir) (q : NS.LFcPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → NS.lfCnxt l d q (X , ιLN e₁) a ≡ nothing
lfCnxt-noLN l d NS.lfcIdle (LNp.sendLN _ _) = refl
lfCnxt-noLN l d NS.lfcIdle (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d NS.lfcIdle (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d NS.lfcIdle (LNp.doneLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWblk _) (LNp.sendLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWblk _) (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWblk _) (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d (NS.lfcWblk _) (LNp.doneLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWtxs _) (LNp.sendLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWtxs _) (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWtxs _) (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d (NS.lfcWtxs _) (LNp.doneLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWvot _) (LNp.sendLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWvot _) (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWvot _) (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d (NS.lfcWvot _) (LNp.doneLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWrng _) (LNp.sendLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWrng _) (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d (NS.lfcWrng _) (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d (NS.lfcWrng _) (LNp.doneLN _ _) = refl
lfCnxt-noLN l d NS.lfcWdone (LNp.sendLN _ _) = refl
lfCnxt-noLN l d NS.lfcWdone (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d NS.lfcWdone (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d NS.lfcWdone (LNp.doneLN _ _) = refl
lfCnxt-noLN l d NS.lfcBlk (LNp.sendLN _ _) = refl
lfCnxt-noLN l d NS.lfcBlk (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d NS.lfcBlk (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d NS.lfcBlk (LNp.doneLN _ _) = refl
lfCnxt-noLN l d NS.lfcBtx (LNp.sendLN _ _) = refl
lfCnxt-noLN l d NS.lfcBtx (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d NS.lfcBtx (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d NS.lfcBtx (LNp.doneLN _ _) = refl
lfCnxt-noLN l d NS.lfcVot (LNp.sendLN _ _) = refl
lfCnxt-noLN l d NS.lfcVot (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d NS.lfcVot (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d NS.lfcVot (LNp.doneLN _ _) = refl
lfCnxt-noLN l d NS.lfcRng (LNp.sendLN _ _) = refl
lfCnxt-noLN l d NS.lfcRng (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d NS.lfcRng (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d NS.lfcRng (LNp.doneLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRblk _) (LNp.sendLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRblk _) (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRblk _) (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d (NS.lfcRblk _) (LNp.doneLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRbtx _) (LNp.sendLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRbtx _) (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRbtx _) (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d (NS.lfcRbtx _) (LNp.doneLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRvot _) (LNp.sendLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRvot _) (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRvot _) (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d (NS.lfcRvot _) (LNp.doneLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRnextRng _) (LNp.sendLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRnextRng _) (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRnextRng _) (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d (NS.lfcRnextRng _) (LNp.doneLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRlastRng _) (LNp.sendLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRlastRng _) (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d (NS.lfcRlastRng _) (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d (NS.lfcRlastRng _) (LNp.doneLN _ _) = refl
lfCnxt-noLN l d NS.lfcTerm (LNp.sendLN _ _) = refl
lfCnxt-noLN l d NS.lfcTerm (LNp.receiveLN _ _) = refl
lfCnxt-noLN l d NS.lfcTerm (LNp.apiLNev _ _ _) = refl
lfCnxt-noLN l d NS.lfcTerm (LNp.doneLN _ _) = refl
lfSnxt-noLN : (l : Link) (d : Dir) (q : NS.LFsPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → NS.lfSnxt l d q (X , ιLN e₁) a ≡ nothing
lfSnxt-noLN l d NS.lfsIdle (LNp.sendLN _ _) = refl
lfSnxt-noLN l d NS.lfsIdle (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d NS.lfsIdle (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d NS.lfsIdle (LNp.doneLN _ _) = refl
lfSnxt-noLN l d NS.lfsBlk (LNp.sendLN _ _) = refl
lfSnxt-noLN l d NS.lfsBlk (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d NS.lfsBlk (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d NS.lfsBlk (LNp.doneLN _ _) = refl
lfSnxt-noLN l d NS.lfsBtx (LNp.sendLN _ _) = refl
lfSnxt-noLN l d NS.lfsBtx (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d NS.lfsBtx (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d NS.lfsBtx (LNp.doneLN _ _) = refl
lfSnxt-noLN l d NS.lfsVot (LNp.sendLN _ _) = refl
lfSnxt-noLN l d NS.lfsVot (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d NS.lfsVot (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d NS.lfsVot (LNp.doneLN _ _) = refl
lfSnxt-noLN l d NS.lfsRng (LNp.sendLN _ _) = refl
lfSnxt-noLN l d NS.lfsRng (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d NS.lfsRng (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d NS.lfsRng (LNp.doneLN _ _) = refl
lfSnxt-noLN l d NS.lfsDone (LNp.sendLN _ _) = refl
lfSnxt-noLN l d NS.lfsDone (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d NS.lfsDone (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d NS.lfsDone (LNp.doneLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWblk _) (LNp.sendLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWblk _) (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWblk _) (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d (NS.lfsWblk _) (LNp.doneLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWtxs _) (LNp.sendLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWtxs _) (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWtxs _) (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d (NS.lfsWtxs _) (LNp.doneLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWvot _) (LNp.sendLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWvot _) (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWvot _) (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d (NS.lfsWvot _) (LNp.doneLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWnext _) (LNp.sendLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWnext _) (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWnext _) (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d (NS.lfsWnext _) (LNp.doneLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWlast _) (LNp.sendLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWlast _) (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d (NS.lfsWlast _) (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d (NS.lfsWlast _) (LNp.doneLN _ _) = refl
lfSnxt-noLN l d NS.lfsTerm (LNp.sendLN _ _) = refl
lfSnxt-noLN l d NS.lfsTerm (LNp.receiveLN _ _) = refl
lfSnxt-noLN l d NS.lfsTerm (LNp.apiLNev _ _ _) = refl
lfSnxt-noLN l d NS.lfsTerm (LNp.doneLN _ _) = refl
absCSc-noLN : (l : Link) (d : Dir) (q : CScPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (absCSc l d q) (ιLN e₁) a
absCSc-noLN l d q e₁ {a} with NS.csCfin (coarsenCSc q) in fEq
... | true  = viewV→noOffer (absCSc l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSc l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιLN e₁} {a = a} fEq (csCnxt-noLN l d (coarsenCSc q) e₁ {a = a}))
absCSs-noLN : (l : Link) (d : Dir) (q : CSsPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (absCSs l d q) (ιLN e₁) a
absCSs-noLN l d q e₁ {a} with NS.csSfin (coarsenCSs q) in fEq
... | true  = viewV→noOffer (absCSs l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSs l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιLN e₁} {a = a} fEq (csSnxt-noLN l d (coarsenCSs q) e₁ {a = a}))
absBFc-noLN : (l : Link) (d : Dir) (q : BFcPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (absBFc l d q) (ιLN e₁) a
absBFc-noLN l d q e₁ {a} with NS.bfCfin (coarsenBFc q) in fEq
... | true  = viewV→noOffer (absBFc l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFc l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιLN e₁} {a = a} fEq (bfCnxt-noLN l d (coarsenBFc q) e₁ {a = a}))
absBFs-noLN : (l : Link) (d : Dir) (q : BFsPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (absBFs l d q) (ιLN e₁) a
absBFs-noLN l d q e₁ {a} with NS.bfSfin (coarsenBFs q) in fEq
... | true  = viewV→noOffer (absBFs l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFs l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιLN e₁} {a = a} fEq (bfSnxt-noLN l d (coarsenBFs q) e₁ {a = a}))
absKAc-noLN : (l : Link) (d : Dir) (q : KAcPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (absKAc l d q) (ιLN e₁) a
absKAc-noLN l d q e₁ {a} with NS.kaCfin (coarsenKAc q) in fEq
... | true  = viewV→noOffer (absKAc l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAc l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιLN e₁} {a = a} fEq (kaCnxt-noLN l d (coarsenKAc q) e₁ {a = a}))
absKAs-noLN : (l : Link) (d : Dir) (q : KAsPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (absKAs l d q) (ιLN e₁) a
absKAs-noLN l d q e₁ {a} with NS.kaSfin (coarsenKAs q) in fEq
... | true  = viewV→noOffer (absKAs l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAs l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιLN e₁} {a = a} fEq (kaSnxt-noLN l d (coarsenKAs q) e₁ {a = a}))
absTSc-noLN : (l : Link) (d : Dir) (q : TScPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (absTSc l d q) (ιLN e₁) a
absTSc-noLN l d q e₁ {a} with NS.tsCfin (coarsenTSc q) in fEq
... | true  = viewV→noOffer (absTSc l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSc l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιLN e₁} {a = a} fEq (tsCnxt-noLN l d (coarsenTSc q) e₁ {a = a}))
absTSs-noLN : (l : Link) (d : Dir) (q : TSsPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (absTSs l d q) (ιLN e₁) a
absTSs-noLN l d q e₁ {a} with NS.tsSfin (coarsenTSs q) in fEq
... | true  = viewV→noOffer (absTSs l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSs l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιLN e₁} {a = a} fEq (tsSnxt-noLN l d (coarsenTSs q) e₁ {a = a}))
absLFc-noLN : (l : Link) (d : Dir) (q : LFcPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (absLFc l d q) (ιLN e₁) a
absLFc-noLN l d q e₁ {a} with NS.lfCfin (coarsenLFc q) in fEq
... | true  = viewV→noOffer (absLFc l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d })
                   (coarsenLFc q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFc l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d })
                   (coarsenLFc q) {e = ιLN e₁} {a = a} fEq (lfCnxt-noLN l d (coarsenLFc q) e₁ {a = a}))
absLFs-noLN : (l : Link) (d : Dir) (q : LFsPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (absLFs l d q) (ιLN e₁) a
absLFs-noLN l d q e₁ {a} with NS.lfSfin (coarsenLFs q) in fEq
... | true  = viewV→noOffer (absLFs l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d })
                   (coarsenLFs q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFs l d q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d })
                   (coarsenLFs q) {e = ιLN e₁} {a = a} fEq (lfSnxt-noLN l d (coarsenLFs q) e₁ {a = a}))
decCSc-noLNgen : (l : Link) (d : Dir) (pos : CScPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (decCSc l d pos) (ιLN e₁) a
decCSc-noLNgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSc-src l d pos) (ιCS⁻¹∘ιLN e₁)
decCSs-noLNgen : (l : Link) (d : Dir) (pos : CSsPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (decCSs l d pos) (ιLN e₁) a
decCSs-noLNgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSs-src l d pos) (ιCS⁻¹∘ιLN e₁)
decBFc-noLNgen : (l : Link) (d : Dir) (pos : BFcPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (decBFc l d pos) (ιLN e₁) a
decBFc-noLNgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFc-src l d pos) (ιBF⁻¹∘ιLN e₁)
decBFs-noLNgen : (l : Link) (d : Dir) (pos : BFsPos) {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (decBFs l d pos) (ιLN e₁) a
decBFs-noLNgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFs-src l d pos) (ιBF⁻¹∘ιLN e₁)

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER C1 — LN direction table-nothing lemmas.
------------------------------------------------------------------------

lnCnxt-dir-no : (l : Link) (d : Dir) (q : NS.LNcPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → lnEvDir e₁ ≢ d → NS.lnCnxt l d q (X , ιLN e₁) a ≡ nothing
lnCnxt-dir-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNDone) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-dir-no l d NS.lncIdle (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-dir-no l d NS.lncWreq (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d NS.lncWreq (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-dir-no l d NS.lncWreq (LNp.apiLNev l′ d′ m) ¬d = refl
lnCnxt-dir-no l d NS.lncWreq (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-dir-no l d NS.lncWdone (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d NS.lncWdone (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-dir-no l d NS.lncWdone (LNp.apiLNev l′ d′ m) ¬d = refl
lnCnxt-dir-no l d NS.lncWdone (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify MsgLNRequestNext} ¬d = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify MsgLNDone} ¬d = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.apiLNev l′ d′ m) ¬d = refl
lnCnxt-dir-no l d NS.lncBusy (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNDone) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRann _) (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNDone) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRoff _) (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNDone) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRtxs _) (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNDone) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-dir-no l d (NS.lncRvot _) (LNp.doneLN l′ d′) ¬d = refl
lnCnxt-dir-no l d NS.lncTerm (LNp.sendLN l′ d′) ¬d = refl
lnCnxt-dir-no l d NS.lncTerm (LNp.receiveLN l′ d′) ¬d = refl
lnCnxt-dir-no l d NS.lncTerm (LNp.apiLNev l′ d′ m) ¬d = refl
lnCnxt-dir-no l d NS.lncTerm (LNp.doneLN l′ d′) ¬d = refl

lnSnxt-dir-no : (l : Link) (d : Dir) (q : NS.LNsPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → lnEvDir e₁ ≢ d → NS.lnSnxt l d q (X , ιLN e₁) a ≡ nothing
lnSnxt-dir-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify MsgLNRequestNext} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} ¬d = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} ¬d = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} ¬d = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} ¬d = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosNotify MsgLNDone} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.receiveLN l′ d′) {a = _ , _ , _ , leiosFetch _} ¬d = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.sendLN l′ d′) ¬d = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-dir-no l d NS.lnsIdle (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNRequestNext) ¬d = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNDone) ¬d = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNBlockAnnouncement) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNBlockOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNBlockTxsOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.apiLNev l′ d′ sendLNVotesOffer) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.apiLNev l′ d′ recvLNBlockAnnouncement) ¬d = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.apiLNev l′ d′ recvLNBlockOffer) ¬d = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.apiLNev l′ d′ recvLNBlockTxsOffer) ¬d = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.apiLNev l′ d′ recvLNVotesOffer) ¬d = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.sendLN l′ d′) ¬d = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-dir-no l d NS.lnsBusy (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWann _) (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnSnxt-dir-no l d (NS.lnsWann _) (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWann _) (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWann _) (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWoff _) (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnSnxt-dir-no l d (NS.lnsWoff _) (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWoff _) (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWoff _) (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWtxs _) (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnSnxt-dir-no l d (NS.lnsWtxs _) (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWtxs _) (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWtxs _) (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWvot _) (LNp.sendLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnSnxt-dir-no l d (NS.lnsWvot _) (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWvot _) (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-dir-no l d (NS.lnsWvot _) (LNp.doneLN l′ d′) ¬d = refl
lnSnxt-dir-no l d NS.lnsDone (LNp.doneLN l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lnSnxt-dir-no l d NS.lnsDone (LNp.sendLN l′ d′) ¬d = refl
lnSnxt-dir-no l d NS.lnsDone (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-dir-no l d NS.lnsDone (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-dir-no l d NS.lnsTerm (LNp.sendLN l′ d′) ¬d = refl
lnSnxt-dir-no l d NS.lnsTerm (LNp.receiveLN l′ d′) ¬d = refl
lnSnxt-dir-no l d NS.lnsTerm (LNp.apiLNev l′ d′ m) ¬d = refl
lnSnxt-dir-no l d NS.lnsTerm (LNp.doneLN l′ d′) ¬d = refl

-- absLNc-dir-noBoth / absLNs-dir-noBoth: same-protocol opposite-role abstract non-offers
absLNc-dir-noBoth : (l : Link) (sv : Dir) (q : LNcPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → lnEvDir e₁ ≢ sv → ¬ IoOffers (absLNc l sv q) (ιLN e₁) a
absLNc-dir-noBoth l sv q e₁ {a} ¬d with NS.lnCfin (coarsenLNc q) in fEq
... | true  = viewV→noOffer (absLNc l sv q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l sv })
                   (coarsenLNc q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNc l sv q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l sv })
                   (coarsenLNc q) {e = ιLN e₁} {a = a} fEq (lnCnxt-dir-no l sv (coarsenLNc q) e₁ {a = a} ¬d))
absLNs-dir-noBoth : (l : Link) (sv : Dir) (q : LNsPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → lnEvDir e₁ ≢ sv → ¬ IoOffers (absLNs l sv q) (ιLN e₁) a
absLNs-dir-noBoth l sv q e₁ {a} ¬d with NS.lnSfin (coarsenLNs q) in fEq
... | true  = viewV→noOffer (absLNs l sv q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l sv })
                   (coarsenLNs q) {e = ιLN e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNs l sv q) {e = ιLN e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l sv })
                   (coarsenLNs q) {e = ιLN e₁} {a = a} fEq (lnSnxt-dir-no l sv (coarsenLNs q) e₁ {a = a} ¬d))

-- tail (LFc ⦀ LFs) offers no LN-image event (all inert, opposite protocol)
lnTail-lfc-noOffer : (l : Link) (cl sv : Dir) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X}
  → ¬ IoOffers (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)) (ιLN e₁) a
lnTail-lfc-noOffer l cl sv ip e₁ =
  SStep.⦀-noOffer (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip))
    (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιLN e₁))
    (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιLN e₁))

-- tail (decLNs ⦀ LFc ⦀ LFs) offers no LN-image event when lnEvDir e₁ ≢ sv (LN-client peel)
lnTail-lns-noOffer : (l : Link) (cl sv : Dir) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : LNp.LNEv X) {a : X} → lnEvDir e₁ ≢ sv
  → ¬ IoOffers (decLNs l sv (lns ip) ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))) (ιLN e₁) a
lnTail-lns-noOffer l cl sv ip e₁ ¬sv =
  SStep.⦀-noOffer (decLNs l sv (lns ip)) _ (decLNs-dir-noOffer l sv (lns ip) e₁ ¬sv)
    (lnTail-lfc-noOffer l cl sv ip e₁)

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER C2 — the 12-peer bundle ev-inversion, LN channel
-- (driven LN peers at bundle positions #8 / #9, tracked by lnc/lns fields).
------------------------------------------------------------------------

-- LN-client advances (dir cl, lnEvDir e₁≡cl)
absBundle-LNc-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {lnc′ : LNcPos}
  → cl ≢ sv → lnEvDir e₁ ≡ cl
  → absLNc l cl (lnc ip) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► absLNc l cl lnc′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc qbs (record ip { lnc = lnc′ })
absBundle-LNc-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} {lnc′} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-R (absCSs l sv qcs) _
          (SStep.⦀-ev-R (absBFc l cl qbc) _
            (SStep.⦀-ev-R (absBFs l sv qbs) _
              (SStep.⦀-ev-R (absTSc l cl (tsc ip)) _
                (SStep.⦀-ev-R (absTSs l sv (tss ip)) _
                  (SStep.⦀-ev-L (absLNc l cl (lnc ip)) _ astep
                    (⦀-viewV-nothing (absLNs l sv (lns ip)) _ (absLNs-dir-noBoth l sv (lns ip) e₁ ¬sv)
                      (SStep.⦀-noOffer (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip))
                        (absLFc-noLN l cl (lfc ip) e₁) (absLFs-noLN l sv (lfs ip) e₁))))
                  (noOffer→viewV (absTSs l sv (tss ip)) (absTSs-noLN l sv (tss ip) e₁)))
                (noOffer→viewV (absTSc l cl (tsc ip)) (absTSc-noLN l cl (tsc ip) e₁)))
              (noOffer→viewV (absBFs l sv qbs) (absBFs-noLN l sv qbs e₁)))
            (noOffer→viewV (absBFc l cl qbc) (absBFc-noLN l cl qbc e₁)))
          (noOffer→viewV (absCSs l sv qcs) (absCSs-noLN l sv qcs e₁)))
        (noOffer→viewV (absCSc l cl qcc) (absCSc-noLN l cl qcc e₁)))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noLN l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noLN l cl (kac ip) e₁))
  where ¬sv : lnEvDir e₁ ≢ sv
        ¬sv q = cl≢sv (trans (sym eqd) q)

-- LN-server advances (dir sv, lnEvDir e₁≡sv)
absBundle-LNs-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {lns′ : LNsPos}
  → cl ≢ sv → lnEvDir e₁ ≡ sv
  → absLNs l sv (lns ip) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► absLNs l sv lns′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc qbs (record ip { lns = lns′ })
absBundle-LNs-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} {lns′} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-R (absCSs l sv qcs) _
          (SStep.⦀-ev-R (absBFc l cl qbc) _
            (SStep.⦀-ev-R (absBFs l sv qbs) _
              (SStep.⦀-ev-R (absTSc l cl (tsc ip)) _
                (SStep.⦀-ev-R (absTSs l sv (tss ip)) _
                  (SStep.⦀-ev-R (absLNc l cl (lnc ip)) _
                    (SStep.⦀-ev-L (absLNs l sv (lns ip)) _ astep
                      (⦀-viewV-nothing (absLFc l cl (lfc ip)) _ (absLFc-noLN l cl (lfc ip) e₁)
                        (absLFs-noLN l sv (lfs ip) e₁)))
                    (noOffer→viewV (absLNc l cl (lnc ip)) (absLNc-dir-noBoth l cl (lnc ip) e₁ ¬cl)))
                  (noOffer→viewV (absTSs l sv (tss ip)) (absTSs-noLN l sv (tss ip) e₁)))
                (noOffer→viewV (absTSc l cl (tsc ip)) (absTSc-noLN l cl (tsc ip) e₁)))
              (noOffer→viewV (absBFs l sv qbs) (absBFs-noLN l sv qbs e₁)))
            (noOffer→viewV (absBFc l cl qbc) (absBFc-noLN l cl qbc e₁)))
          (noOffer→viewV (absCSs l sv qcs) (absCSs-noLN l sv qcs e₁)))
        (noOffer→viewV (absCSc l cl qcc) (absCSc-noLN l cl qcc e₁)))
      (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noLN l sv (kas ip) e₁)))
    (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noLN l cl (kac ip) e₁))
  where ¬cl : lnEvDir e₁ ≢ cl
        ¬cl q = cl≢sv (sym (trans (sym eqd) q))

-- which driven LN peer fired the LN-image event
data BundleLNEvR (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : LNp.LNEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  btlncE : (lnc′ : LNcPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc bfs (record ip { lnc = lnc′ })
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► absBundleG l cl sv csc css bfc bfs (record ip { lnc = lnc′ })
        → BundleLNEvR l cl sv csc css bfc bfs ip e₁ a Bd′
  btlnsE : (lns′ : LNsPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc bfs (record ip { lns = lns′ })
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► absBundleG l cl sv csc css bfc bfs (record ip { lns = lns′ })
        → BundleLNEvR l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a LN-client driven step into the bundle result (LN client is peer #8)
finishLNc-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decLNc l cl (lnc ip) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► P′
  → BundleLNEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
        ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (P′ ⦀ (decLNs l sv (lns ip)
        ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))))
finishLNc-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simLNc′ l cl (lnc ip) sM
... | _ , lnc′ , _ , _ , Meq , aStep0 =
      btlncE lnc′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
               ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (z ⦀ (decLNs l sv (lns ip)
               ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))) Meq)
        (absBundle-LNc-ev l cl sv csc css bfc bfs ip {lnc′ = lnc′} cl≢sv
          (sym (apiDir-inj (lnc-ev-dir l cl (lnc ip) sM) (lnApiDir e₁))) aStep0)

-- fold a LN-server driven step into the bundle result (LN server is peer #9)
finishLNs-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decLNs l sv (lns ip) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► P′
  → BundleLNEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
        ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (P′
        ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))))
finishLNs-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simLNs′ l sv (lns ip) sM
... | _ , lns′ , _ , _ , Meq , aStep0 =
      btlnsE lns′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
               ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (z
               ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))) Meq)
        (absBundle-LNs-ev l cl sv csc css bfc bfs ip {lns′ = lns′} cl≢sv
          (sym (apiDir-inj (lns-ev-dir l sv (lns ip) sM) (lnApiDir e₁))) aStep0)

-- 12-peer bundle ev-inversion (LN)
bundle-LN-ev-inv : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► Bd′
  → BundleLNEvR l cl sv csc css bfc bfs ip e₁ a Bd′
bundle-LN-ev-inv l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...                 | PEA.evL _ sM = finishLNc-ev l cl sv csc css bfc bfs ip cl≢sv sM
...                 | PEA.evBoth _ sM sTail =
                        ⊥-elim (lnTail-lns-noOffer l cl sv ip e₁
                                  (λ q → cl≢sv (trans (apiDir-inj (lnc-ev-dir l cl (lnc ip) sM) (lnApiDir e₁)) q))
                                  (_ , sTail))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = finishLNs-ev l cl sv csc css bfc bfs ip cl≢sv sM
...                   | PEA.evBoth _ sM sTail =
                          ⊥-elim (lnTail-lfc-noOffer l cl sv ip e₁ (_ , sTail))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM      = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιLN e₁) (_ , sM))
...                     | PEA.evBoth _ sM _ = ⊥-elim (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιLN e₁) (_ , sM))
...                     | PEA.evR _ qs     = ⊥-elim (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιLN e₁) (_ , qs))


------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER A — LF channel direction machinery.
------------------------------------------------------------------------
ιCS⁻¹∘ιLF : {X : Set 0ℓ} (e₁ : LFp.LFEv X) → ιCS⁻¹ (ιLF e₁) ≡ nothing
ιCS⁻¹∘ιLF (LFp.sendLF l d)    = refl
ιCS⁻¹∘ιLF (LFp.receiveLF l d) = refl
ιCS⁻¹∘ιLF (LFp.apiLFev l d m) = refl
ιCS⁻¹∘ιLF (LFp.doneLF l d)    = refl
ιBF⁻¹∘ιLF : {X : Set 0ℓ} (e₁ : LFp.LFEv X) → ιBF⁻¹ (ιLF e₁) ≡ nothing
ιBF⁻¹∘ιLF (LFp.sendLF l d)    = refl
ιBF⁻¹∘ιLF (LFp.receiveLF l d) = refl
ιBF⁻¹∘ιLF (LFp.apiLFev l d m) = refl
ιBF⁻¹∘ιLF (LFp.doneLF l d)    = refl
ιKA⁻¹∘ιLF : {X : Set 0ℓ} (e₁ : LFp.LFEv X) → ιKA⁻¹ (ιLF e₁) ≡ nothing
ιKA⁻¹∘ιLF (LFp.sendLF l d)    = refl
ιKA⁻¹∘ιLF (LFp.receiveLF l d) = refl
ιKA⁻¹∘ιLF (LFp.apiLFev l d m) = refl
ιKA⁻¹∘ιLF (LFp.doneLF l d)    = refl
ιTS⁻¹∘ιLF : {X : Set 0ℓ} (e₁ : LFp.LFEv X) → ιTS⁻¹ (ιLF e₁) ≡ nothing
ιTS⁻¹∘ιLF (LFp.sendLF l d)    = refl
ιTS⁻¹∘ιLF (LFp.receiveLF l d) = refl
ιTS⁻¹∘ιLF (LFp.apiLFev l d m) = refl
ιTS⁻¹∘ιLF (LFp.doneLF l d)    = refl
ιLN⁻¹∘ιLF : {X : Set 0ℓ} (e₁ : LFp.LFEv X) → ιLN⁻¹ (ιLF e₁) ≡ nothing
ιLN⁻¹∘ιLF (LFp.sendLF l d)    = refl
ιLN⁻¹∘ιLF (LFp.receiveLF l d) = refl
ιLN⁻¹∘ιLF (LFp.apiLFev l d m) = refl
ιLN⁻¹∘ιLF (LFp.doneLF l d)    = refl

lfEvDir : {X : Set 0ℓ} → LFp.LFEv X → Dir
lfEvDir (LFp.sendLF l d)    = d
lfEvDir (LFp.receiveLF l d) = d
lfEvDir (LFp.apiLFev l d m) = d
lfEvDir (LFp.doneLF l d)    = d
lfApiDir : {X : Set 0ℓ} (e₁ : LFp.LFEv X) → ApiHasDir (lfEvDir e₁) (ιLF e₁)
lfApiDir (LFp.sendLF l d)    = ahIn
lfApiDir (LFp.receiveLF l d) = ahOut
lfApiDir (LFp.apiLFev l d m) = ahLF
lfApiDir (LFp.doneLF l d)    = ahDone
-- SOURCE-side per-position ev inversion — LeiosFetch CLIENT
decLFc-src-dir : (l : Link) (d : Dir) (pos : LFcPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {P′ : LFProc}
  → decLFc-src l d pos LFL.─[ LFL.ev (LFL.evl (LFL.evLabel X e₁ a)) ]─► P′
  → lfEvDir e₁ ≡ d
-- head stIdle : five api requests
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFDone} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-dir l d (lfcHead LFp.stIdle) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
-- head stBlock / stBlockTxs / stVotes / stBlockRange : wire receives
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlock b)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlock) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxs ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVoteDelivery vs)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stVotes) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-dir l d (lfcHead LFp.stBlockRange) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
-- head stDone : ret
decLFc-src-dir l d (lfcHead LFp.stDone) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaves
decLFc-src-dir l d (lfcRblk1 b) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ b
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-dir l d (lfcRblk1 b) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-src-dir l d (lfcRblk1 b) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-src-dir l d (lfcRblk1 b) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-src-dir l d (lfcRbtx1 ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFBlockTxs) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val ts
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-dir l d (lfcRbtx1 ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-src-dir l d (lfcRbtx1 ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-src-dir l d (lfcRbtx1 ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-src-dir l d (lfcRvot1 vs) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFVoteDelivery) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val vs
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-dir l d (lfcRvot1 vs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-src-dir l d (lfcRvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-src-dir l d (lfcRvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-src-dir l d (lfcRnext1 b ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFRangeBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEqI.DecEq-× ⦄ val (b , ts)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-dir l d (lfcRnext1 b ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-src-dir l d (lfcRnext1 b ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-src-dir l d (lfcRnext1 b ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-src-dir l d (lfcRlast1 b ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFRangeBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEqI.DecEq-× ⦄ val (b , ts)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-dir l d (lfcRlast1 b ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
decLFc-src-dir l d (lfcRlast1 b ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
decLFc-src-dir l d (lfcRlast1 b ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
-- send leaves
decLFc-src-dir l d (lfcWblk1 pt) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-dir l d (lfcWblk1 pt) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-src-dir l d (lfcWblk1 pt) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-src-dir l d (lfcWblk1 pt) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-src-dir l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-dir l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-src-dir l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-src-dir l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-src-dir l d (lfcWvot1 vs) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-dir l d (lfcWvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-src-dir l d (lfcWvot1 vs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-src-dir l d (lfcWvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-src-dir l d (lfcWrng1 r) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-dir l d (lfcWrng1 r) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-src-dir l d (lfcWrng1 r) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-src-dir l d (lfcWrng1 r) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-src-dir l d lfcDone1 {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFc-src-dir l d lfcDone1 {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
decLFc-src-dir l d lfcDone1 {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
decLFc-src-dir l d lfcDone1 {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
-- loop re-entry
decLFc-src-dir l d (lfcSil st) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- SOURCE-side per-position ev inversion — LeiosFetch SERVER
decLFs-src-dir : (l : Link) (d : Dir) (pos : LFsPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {P′ : LFProc}
  → decLFs-src l d pos LFL.─[ LFL.ev (LFL.evl (LFL.evLabel X e₁ a)) ]─► P′
  → lfEvDir e₁ ≡ d
-- head stIdle : five wire requests (4 loops + done)
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRequest pt)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxsRequest pt bm)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVotesRequest vs)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRangeRequest r)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFDone)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-dir l d (lfsHead LFp.stIdle) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
-- head stBlock / stBlockTxs / stVotes / stBlockRange : api sends
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlock} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlock) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stVotes) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = refl
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-dir l d (lfsHead LFp.stBlockRange) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
-- head stDone : ret
decLFs-src-dir l d (lfsHead LFp.stDone) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf
decLFs-src-dir l d lfsDone1 {e₁ = LFp.doneLF l' d'} {a} s with step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s
... | offer with LFp.LFEv-≟ (_ , LFp.doneLF l d) (_ , LFp.doneLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = refl
decLFs-src-dir l d lfsDone1 {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
decLFs-src-dir l d lfsDone1 {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
decLFs-src-dir l d lfsDone1 {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
-- send leaves
decLFs-src-dir l d (lfsWblk1 b) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-src-dir l d (lfsWblk1 b) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-src-dir l d (lfsWblk1 b) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-src-dir l d (lfsWblk1 b) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-src-dir l d (lfsWtxs1 ts) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-src-dir l d (lfsWtxs1 ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-src-dir l d (lfsWtxs1 ts) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-src-dir l d (lfsWtxs1 ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-src-dir l d (lfsWvot1 vs) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-src-dir l d (lfsWvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-src-dir l d (lfsWvot1 vs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-src-dir l d (lfsWvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-src-dir l d (lfsWnext1 (b , ts)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-src-dir l d (lfsWnext1 (b , ts)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-src-dir l d (lfsWnext1 (b , ts)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-src-dir l d (lfsWnext1 (b , ts)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-src-dir l d (lfsWlast1 (b , ts)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = refl
decLFs-src-dir l d (lfsWlast1 (b , ts)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
decLFs-src-dir l d (lfsWlast1 (b , ts)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
decLFs-src-dir l d (lfsWlast1 (b , ts)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
-- loop re-entry
decLFs-src-dir l d (lfsSil st) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

lfc-ev-dir : (l : Link) (d : Dir) (pos : LFcPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decLFc l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
lfc-ev-dir l d pos step with LFNO.renameMap-ev-reflect-ι {P = decLFc-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιLF-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιLF e₁)) (decLFc-src-dir l d pos srcStep) (lfApiDir e₁))
lfs-ev-dir : (l : Link) (d : Dir) (pos : LFsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {M : NetProc}
  → decLFs l d pos ─[ ev (evl (evLabel X e₂ a)) ]─► M → ApiHasDir d e₂
lfs-ev-dir l d pos step with LFNO.renameMap-ev-reflect-ι {P = decLFs-src l d pos} step
... | e₁ , _ , iota , srcStep , _ =
      subst (λ z → ApiHasDir d z) (sym (ιLF-inv-shape iota))
        (subst (λ dd → ApiHasDir dd (ιLF e₁)) (decLFs-src-dir l d pos srcStep) (lfApiDir e₁))

LFc-LFs-noBoth : (l : Link) (cl sv : Dir) → cl ≢ sv → (pc : LFcPos) (ps : LFsPos)
    {X : Set 0ℓ} {e₂ : Net_Api Payload X} {a : X} {Mc Ms : NetProc}
  → decLFc l cl pc ─[ ev (evl (evLabel X e₂ a)) ]─► Mc
  → decLFs l sv ps ─[ ev (evl (evLabel X e₂ a)) ]─► Ms → ⊥
LFc-LFs-noBoth l cl sv cl≢sv pc ps sc ss =
  cl≢sv (apiDir-inj (lfc-ev-dir l cl pc sc) (lfs-ev-dir l sv ps ss))

decLFc-dir-noOffer : (l : Link) (d : Dir) (pos : LFcPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → lfEvDir e₁ ≢ d → ¬ IoOffers (decLFc l d pos) (ιLF e₁) a
decLFc-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (lfc-ev-dir l d pos step) (lfApiDir e₁)))
decLFs-dir-noOffer : (l : Link) (d : Dir) (pos : LFsPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → lfEvDir e₁ ≢ d → ¬ IoOffers (decLFs l d pos) (ιLF e₁) a
decLFs-dir-noOffer l d pos e₁ ¬d (M , step) = ¬d (sym (apiDir-inj (lfs-ev-dir l d pos step) (lfApiDir e₁)))

simLFc′ : (l : Link) (d : Dir) (pos : LFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decLFc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ LFp.LFEv X ] Σ[ pos′ ∈ LFcPos ]
       (e ≡ ιLF e₁) × (lfEvDir e₁ ≡ d) × (M ≡ decLFc l d pos′)
       × (absLFc l d pos ─[ ev (evl (evLabel X e a)) ]─► absLFc l d pos′)
simLFc′ l d pos step with LFNO.renameMap-ev-reflect-ι {P = decLFc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decLFc-src-ev-inv l d pos srcStep | ιLF-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decLFc-src-dir l d pos srcStep ,
        trans Meq (cong RenLF.renameMap P′eq) , aStep
simLFs′ : (l : Link) (d : Dir) (pos : LFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decLFs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ e₁ ∈ LFp.LFEv X ] Σ[ pos′ ∈ LFsPos ]
       (e ≡ ιLF e₁) × (lfEvDir e₁ ≡ d) × (M ≡ decLFs l d pos′)
       × (absLFs l d pos ─[ ev (evl (evLabel X e a)) ]─► absLFs l d pos′)
simLFs′ l d pos step with LFNO.renameMap-ev-reflect-ι {P = decLFs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decLFs-src-ev-inv l d pos srcStep | ιLF-inv-shape iota
...   | pos′ , P′eq , aStep | refl =
        e₁ , pos′ , refl , decLFs-src-dir l d pos srcStep ,
        trans Meq (cong RenLF.renameMap P′eq) , aStep

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER B — LF channel abstract-side non-offers.
------------------------------------------------------------------------
csCnxt-noLF : (l : Link) (d : Dir) (q : NS.CScPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → NS.csCnxt l d q (X , ιLF e₁) a ≡ nothing
csCnxt-noLF l d NS.ccIdle (LFp.sendLF _ _) = refl
csCnxt-noLF l d NS.ccIdle (LFp.receiveLF _ _) = refl
csCnxt-noLF l d NS.ccIdle (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d NS.ccIdle (LFp.doneLF _ _) = refl
csCnxt-noLF l d NS.ccWreq (LFp.sendLF _ _) = refl
csCnxt-noLF l d NS.ccWreq (LFp.receiveLF _ _) = refl
csCnxt-noLF l d NS.ccWreq (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d NS.ccWreq (LFp.doneLF _ _) = refl
csCnxt-noLF l d NS.ccAwait (LFp.sendLF _ _) = refl
csCnxt-noLF l d NS.ccAwait (LFp.receiveLF _ _) = refl
csCnxt-noLF l d NS.ccAwait (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d NS.ccAwait (LFp.doneLF _ _) = refl
csCnxt-noLF l d (NS.ccWfi _) (LFp.sendLF _ _) = refl
csCnxt-noLF l d (NS.ccWfi _) (LFp.receiveLF _ _) = refl
csCnxt-noLF l d (NS.ccWfi _) (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d (NS.ccWfi _) (LFp.doneLF _ _) = refl
csCnxt-noLF l d NS.ccInt (LFp.sendLF _ _) = refl
csCnxt-noLF l d NS.ccInt (LFp.receiveLF _ _) = refl
csCnxt-noLF l d NS.ccInt (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d NS.ccInt (LFp.doneLF _ _) = refl
csCnxt-noLF l d NS.ccWdone (LFp.sendLF _ _) = refl
csCnxt-noLF l d NS.ccWdone (LFp.receiveLF _ _) = refl
csCnxt-noLF l d NS.ccWdone (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d NS.ccWdone (LFp.doneLF _ _) = refl
csCnxt-noLF l d NS.ccMust (LFp.sendLF _ _) = refl
csCnxt-noLF l d NS.ccMust (LFp.receiveLF _ _) = refl
csCnxt-noLF l d NS.ccMust (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d NS.ccMust (LFp.doneLF _ _) = refl
csCnxt-noLF l d (NS.ccArf _) (LFp.sendLF _ _) = refl
csCnxt-noLF l d (NS.ccArf _) (LFp.receiveLF _ _) = refl
csCnxt-noLF l d (NS.ccArf _) (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d (NS.ccArf _) (LFp.doneLF _ _) = refl
csCnxt-noLF l d (NS.ccArb _) (LFp.sendLF _ _) = refl
csCnxt-noLF l d (NS.ccArb _) (LFp.receiveLF _ _) = refl
csCnxt-noLF l d (NS.ccArb _) (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d (NS.ccArb _) (LFp.doneLF _ _) = refl
csCnxt-noLF l d (NS.ccAif _) (LFp.sendLF _ _) = refl
csCnxt-noLF l d (NS.ccAif _) (LFp.receiveLF _ _) = refl
csCnxt-noLF l d (NS.ccAif _) (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d (NS.ccAif _) (LFp.doneLF _ _) = refl
csCnxt-noLF l d (NS.ccAin _) (LFp.sendLF _ _) = refl
csCnxt-noLF l d (NS.ccAin _) (LFp.receiveLF _ _) = refl
csCnxt-noLF l d (NS.ccAin _) (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d (NS.ccAin _) (LFp.doneLF _ _) = refl
csCnxt-noLF l d NS.ccTerm (LFp.sendLF _ _) = refl
csCnxt-noLF l d NS.ccTerm (LFp.receiveLF _ _) = refl
csCnxt-noLF l d NS.ccTerm (LFp.apiLFev _ _ _) = refl
csCnxt-noLF l d NS.ccTerm (LFp.doneLF _ _) = refl
csSnxt-noLF : (l : Link) (d : Dir) (q : NS.CSsPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → NS.csSnxt l d q (X , ιLF e₁) a ≡ nothing
csSnxt-noLF l d NS.csIdle (LFp.sendLF _ _) = refl
csSnxt-noLF l d NS.csIdle (LFp.receiveLF _ _) = refl
csSnxt-noLF l d NS.csIdle (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d NS.csIdle (LFp.doneLF _ _) = refl
csSnxt-noLF l d NS.csAreq (LFp.sendLF _ _) = refl
csSnxt-noLF l d NS.csAreq (LFp.receiveLF _ _) = refl
csSnxt-noLF l d NS.csAreq (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d NS.csAreq (LFp.doneLF _ _) = refl
csSnxt-noLF l d NS.csCanAwait (LFp.sendLF _ _) = refl
csSnxt-noLF l d NS.csCanAwait (LFp.receiveLF _ _) = refl
csSnxt-noLF l d NS.csCanAwait (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d NS.csCanAwait (LFp.doneLF _ _) = refl
csSnxt-noLF l d (NS.csAfi _) (LFp.sendLF _ _) = refl
csSnxt-noLF l d (NS.csAfi _) (LFp.receiveLF _ _) = refl
csSnxt-noLF l d (NS.csAfi _) (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d (NS.csAfi _) (LFp.doneLF _ _) = refl
csSnxt-noLF l d NS.csInt (LFp.sendLF _ _) = refl
csSnxt-noLF l d NS.csInt (LFp.receiveLF _ _) = refl
csSnxt-noLF l d NS.csInt (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d NS.csInt (LFp.doneLF _ _) = refl
csSnxt-noLF l d NS.csDdone (LFp.sendLF _ _) = refl
csSnxt-noLF l d NS.csDdone (LFp.receiveLF _ _) = refl
csSnxt-noLF l d NS.csDdone (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d NS.csDdone (LFp.doneLF _ _) = refl
csSnxt-noLF l d NS.csMust (LFp.sendLF _ _) = refl
csSnxt-noLF l d NS.csMust (LFp.receiveLF _ _) = refl
csSnxt-noLF l d NS.csMust (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d NS.csMust (LFp.doneLF _ _) = refl
csSnxt-noLF l d (NS.csWrf _) (LFp.sendLF _ _) = refl
csSnxt-noLF l d (NS.csWrf _) (LFp.receiveLF _ _) = refl
csSnxt-noLF l d (NS.csWrf _) (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d (NS.csWrf _) (LFp.doneLF _ _) = refl
csSnxt-noLF l d (NS.csWrb _) (LFp.sendLF _ _) = refl
csSnxt-noLF l d (NS.csWrb _) (LFp.receiveLF _ _) = refl
csSnxt-noLF l d (NS.csWrb _) (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d (NS.csWrb _) (LFp.doneLF _ _) = refl
csSnxt-noLF l d NS.csWar (LFp.sendLF _ _) = refl
csSnxt-noLF l d NS.csWar (LFp.receiveLF _ _) = refl
csSnxt-noLF l d NS.csWar (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d NS.csWar (LFp.doneLF _ _) = refl
csSnxt-noLF l d (NS.csWif _) (LFp.sendLF _ _) = refl
csSnxt-noLF l d (NS.csWif _) (LFp.receiveLF _ _) = refl
csSnxt-noLF l d (NS.csWif _) (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d (NS.csWif _) (LFp.doneLF _ _) = refl
csSnxt-noLF l d (NS.csWin _) (LFp.sendLF _ _) = refl
csSnxt-noLF l d (NS.csWin _) (LFp.receiveLF _ _) = refl
csSnxt-noLF l d (NS.csWin _) (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d (NS.csWin _) (LFp.doneLF _ _) = refl
csSnxt-noLF l d NS.csTerm (LFp.sendLF _ _) = refl
csSnxt-noLF l d NS.csTerm (LFp.receiveLF _ _) = refl
csSnxt-noLF l d NS.csTerm (LFp.apiLFev _ _ _) = refl
csSnxt-noLF l d NS.csTerm (LFp.doneLF _ _) = refl
bfCnxt-noLF : (l : Link) (d : Dir) (q : NS.BFcPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → NS.bfCnxt l d q (X , ιLF e₁) a ≡ nothing
bfCnxt-noLF l d NS.bcIdle (LFp.sendLF _ _) = refl
bfCnxt-noLF l d NS.bcIdle (LFp.receiveLF _ _) = refl
bfCnxt-noLF l d NS.bcIdle (LFp.apiLFev _ _ _) = refl
bfCnxt-noLF l d NS.bcIdle (LFp.doneLF _ _) = refl
bfCnxt-noLF l d (NS.bcWrr _) (LFp.sendLF _ _) = refl
bfCnxt-noLF l d (NS.bcWrr _) (LFp.receiveLF _ _) = refl
bfCnxt-noLF l d (NS.bcWrr _) (LFp.apiLFev _ _ _) = refl
bfCnxt-noLF l d (NS.bcWrr _) (LFp.doneLF _ _) = refl
bfCnxt-noLF l d NS.bcBusy (LFp.sendLF _ _) = refl
bfCnxt-noLF l d NS.bcBusy (LFp.receiveLF _ _) = refl
bfCnxt-noLF l d NS.bcBusy (LFp.apiLFev _ _ _) = refl
bfCnxt-noLF l d NS.bcBusy (LFp.doneLF _ _) = refl
bfCnxt-noLF l d NS.bcWcd (LFp.sendLF _ _) = refl
bfCnxt-noLF l d NS.bcWcd (LFp.receiveLF _ _) = refl
bfCnxt-noLF l d NS.bcWcd (LFp.apiLFev _ _ _) = refl
bfCnxt-noLF l d NS.bcWcd (LFp.doneLF _ _) = refl
bfCnxt-noLF l d NS.bcStream (LFp.sendLF _ _) = refl
bfCnxt-noLF l d NS.bcStream (LFp.receiveLF _ _) = refl
bfCnxt-noLF l d NS.bcStream (LFp.apiLFev _ _ _) = refl
bfCnxt-noLF l d NS.bcStream (LFp.doneLF _ _) = refl
bfCnxt-noLF l d (NS.bcAblk _) (LFp.sendLF _ _) = refl
bfCnxt-noLF l d (NS.bcAblk _) (LFp.receiveLF _ _) = refl
bfCnxt-noLF l d (NS.bcAblk _) (LFp.apiLFev _ _ _) = refl
bfCnxt-noLF l d (NS.bcAblk _) (LFp.doneLF _ _) = refl
bfCnxt-noLF l d NS.bcTerm (LFp.sendLF _ _) = refl
bfCnxt-noLF l d NS.bcTerm (LFp.receiveLF _ _) = refl
bfCnxt-noLF l d NS.bcTerm (LFp.apiLFev _ _ _) = refl
bfCnxt-noLF l d NS.bcTerm (LFp.doneLF _ _) = refl
bfSnxt-noLF : (l : Link) (d : Dir) (q : NS.BFsPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → NS.bfSnxt l d q (X , ιLF e₁) a ≡ nothing
bfSnxt-noLF l d NS.bsIdle (LFp.sendLF _ _) = refl
bfSnxt-noLF l d NS.bsIdle (LFp.receiveLF _ _) = refl
bfSnxt-noLF l d NS.bsIdle (LFp.apiLFev _ _ _) = refl
bfSnxt-noLF l d NS.bsIdle (LFp.doneLF _ _) = refl
bfSnxt-noLF l d (NS.bsAreq _) (LFp.sendLF _ _) = refl
bfSnxt-noLF l d (NS.bsAreq _) (LFp.receiveLF _ _) = refl
bfSnxt-noLF l d (NS.bsAreq _) (LFp.apiLFev _ _ _) = refl
bfSnxt-noLF l d (NS.bsAreq _) (LFp.doneLF _ _) = refl
bfSnxt-noLF l d NS.bsBusy (LFp.sendLF _ _) = refl
bfSnxt-noLF l d NS.bsBusy (LFp.receiveLF _ _) = refl
bfSnxt-noLF l d NS.bsBusy (LFp.apiLFev _ _ _) = refl
bfSnxt-noLF l d NS.bsBusy (LFp.doneLF _ _) = refl
bfSnxt-noLF l d NS.bsDdone (LFp.sendLF _ _) = refl
bfSnxt-noLF l d NS.bsDdone (LFp.receiveLF _ _) = refl
bfSnxt-noLF l d NS.bsDdone (LFp.apiLFev _ _ _) = refl
bfSnxt-noLF l d NS.bsDdone (LFp.doneLF _ _) = refl
bfSnxt-noLF l d NS.bsWsb (LFp.sendLF _ _) = refl
bfSnxt-noLF l d NS.bsWsb (LFp.receiveLF _ _) = refl
bfSnxt-noLF l d NS.bsWsb (LFp.apiLFev _ _ _) = refl
bfSnxt-noLF l d NS.bsWsb (LFp.doneLF _ _) = refl
bfSnxt-noLF l d NS.bsStream (LFp.sendLF _ _) = refl
bfSnxt-noLF l d NS.bsStream (LFp.receiveLF _ _) = refl
bfSnxt-noLF l d NS.bsStream (LFp.apiLFev _ _ _) = refl
bfSnxt-noLF l d NS.bsStream (LFp.doneLF _ _) = refl
bfSnxt-noLF l d NS.bsWnb (LFp.sendLF _ _) = refl
bfSnxt-noLF l d NS.bsWnb (LFp.receiveLF _ _) = refl
bfSnxt-noLF l d NS.bsWnb (LFp.apiLFev _ _ _) = refl
bfSnxt-noLF l d NS.bsWnb (LFp.doneLF _ _) = refl
bfSnxt-noLF l d (NS.bsWblk _) (LFp.sendLF _ _) = refl
bfSnxt-noLF l d (NS.bsWblk _) (LFp.receiveLF _ _) = refl
bfSnxt-noLF l d (NS.bsWblk _) (LFp.apiLFev _ _ _) = refl
bfSnxt-noLF l d (NS.bsWblk _) (LFp.doneLF _ _) = refl
bfSnxt-noLF l d NS.bsWbd (LFp.sendLF _ _) = refl
bfSnxt-noLF l d NS.bsWbd (LFp.receiveLF _ _) = refl
bfSnxt-noLF l d NS.bsWbd (LFp.apiLFev _ _ _) = refl
bfSnxt-noLF l d NS.bsWbd (LFp.doneLF _ _) = refl
bfSnxt-noLF l d NS.bsTerm (LFp.sendLF _ _) = refl
bfSnxt-noLF l d NS.bsTerm (LFp.receiveLF _ _) = refl
bfSnxt-noLF l d NS.bsTerm (LFp.apiLFev _ _ _) = refl
bfSnxt-noLF l d NS.bsTerm (LFp.doneLF _ _) = refl
kaCnxt-noLF : (l : Link) (d : Dir) (q : NS.KAcPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → NS.kaCnxt l d q (X , ιLF e₁) a ≡ nothing
kaCnxt-noLF l d NS.kcClient (LFp.sendLF _ _) = refl
kaCnxt-noLF l d NS.kcClient (LFp.receiveLF _ _) = refl
kaCnxt-noLF l d NS.kcClient (LFp.apiLFev _ _ _) = refl
kaCnxt-noLF l d NS.kcClient (LFp.doneLF _ _) = refl
kaCnxt-noLF l d (NS.kcWmsg _) (LFp.sendLF _ _) = refl
kaCnxt-noLF l d (NS.kcWmsg _) (LFp.receiveLF _ _) = refl
kaCnxt-noLF l d (NS.kcWmsg _) (LFp.apiLFev _ _ _) = refl
kaCnxt-noLF l d (NS.kcWmsg _) (LFp.doneLF _ _) = refl
kaCnxt-noLF l d (NS.kcAwait _) (LFp.sendLF _ _) = refl
kaCnxt-noLF l d (NS.kcAwait _) (LFp.receiveLF _ _) = refl
kaCnxt-noLF l d (NS.kcAwait _) (LFp.apiLFev _ _ _) = refl
kaCnxt-noLF l d (NS.kcAwait _) (LFp.doneLF _ _) = refl
kaCnxt-noLF l d NS.kcWdone (LFp.sendLF _ _) = refl
kaCnxt-noLF l d NS.kcWdone (LFp.receiveLF _ _) = refl
kaCnxt-noLF l d NS.kcWdone (LFp.apiLFev _ _ _) = refl
kaCnxt-noLF l d NS.kcWdone (LFp.doneLF _ _) = refl
kaCnxt-noLF l d (NS.kcErr _ _) (LFp.sendLF _ _) = refl
kaCnxt-noLF l d (NS.kcErr _ _) (LFp.receiveLF _ _) = refl
kaCnxt-noLF l d (NS.kcErr _ _) (LFp.apiLFev _ _ _) = refl
kaCnxt-noLF l d (NS.kcErr _ _) (LFp.doneLF _ _) = refl
kaCnxt-noLF l d NS.kcTerm (LFp.sendLF _ _) = refl
kaCnxt-noLF l d NS.kcTerm (LFp.receiveLF _ _) = refl
kaCnxt-noLF l d NS.kcTerm (LFp.apiLFev _ _ _) = refl
kaCnxt-noLF l d NS.kcTerm (LFp.doneLF _ _) = refl
kaCnxt-noLF l d NS.kcTermE (LFp.sendLF _ _) = refl
kaCnxt-noLF l d NS.kcTermE (LFp.receiveLF _ _) = refl
kaCnxt-noLF l d NS.kcTermE (LFp.apiLFev _ _ _) = refl
kaCnxt-noLF l d NS.kcTermE (LFp.doneLF _ _) = refl
kaSnxt-noLF : (l : Link) (d : Dir) (q : NS.KAsPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → NS.kaSnxt l d q (X , ιLF e₁) a ≡ nothing
kaSnxt-noLF l d NS.ksClient (LFp.sendLF _ _) = refl
kaSnxt-noLF l d NS.ksClient (LFp.receiveLF _ _) = refl
kaSnxt-noLF l d NS.ksClient (LFp.apiLFev _ _ _) = refl
kaSnxt-noLF l d NS.ksClient (LFp.doneLF _ _) = refl
kaSnxt-noLF l d (NS.ksRecv _) (LFp.sendLF _ _) = refl
kaSnxt-noLF l d (NS.ksRecv _) (LFp.receiveLF _ _) = refl
kaSnxt-noLF l d (NS.ksRecv _) (LFp.apiLFev _ _ _) = refl
kaSnxt-noLF l d (NS.ksRecv _) (LFp.doneLF _ _) = refl
kaSnxt-noLF l d (NS.ksResp _) (LFp.sendLF _ _) = refl
kaSnxt-noLF l d (NS.ksResp _) (LFp.receiveLF _ _) = refl
kaSnxt-noLF l d (NS.ksResp _) (LFp.apiLFev _ _ _) = refl
kaSnxt-noLF l d (NS.ksResp _) (LFp.doneLF _ _) = refl
kaSnxt-noLF l d NS.ksDdone (LFp.sendLF _ _) = refl
kaSnxt-noLF l d NS.ksDdone (LFp.receiveLF _ _) = refl
kaSnxt-noLF l d NS.ksDdone (LFp.apiLFev _ _ _) = refl
kaSnxt-noLF l d NS.ksDdone (LFp.doneLF _ _) = refl
kaSnxt-noLF l d NS.ksTerm (LFp.sendLF _ _) = refl
kaSnxt-noLF l d NS.ksTerm (LFp.receiveLF _ _) = refl
kaSnxt-noLF l d NS.ksTerm (LFp.apiLFev _ _ _) = refl
kaSnxt-noLF l d NS.ksTerm (LFp.doneLF _ _) = refl
tsCnxt-noLF : (l : Link) (d : Dir) (q : NS.TScPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → NS.tsCnxt l d q (X , ιLF e₁) a ≡ nothing
tsCnxt-noLF l d NS.tcInit (LFp.sendLF _ _) = refl
tsCnxt-noLF l d NS.tcInit (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d NS.tcInit (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d NS.tcInit (LFp.doneLF _ _) = refl
tsCnxt-noLF l d NS.tcIdle (LFp.sendLF _ _) = refl
tsCnxt-noLF l d NS.tcIdle (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d NS.tcIdle (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d NS.tcIdle (LFp.doneLF _ _) = refl
tsCnxt-noLF l d (NS.tcAri (Blocking , _ , _)) (LFp.sendLF _ _) = refl
tsCnxt-noLF l d (NS.tcAri (Blocking , _ , _)) (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d (NS.tcAri (Blocking , _ , _)) (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d (NS.tcAri (Blocking , _ , _)) (LFp.doneLF _ _) = refl
tsCnxt-noLF l d (NS.tcAri (NonBlocking , _ , _)) (LFp.sendLF _ _) = refl
tsCnxt-noLF l d (NS.tcAri (NonBlocking , _ , _)) (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d (NS.tcAri (NonBlocking , _ , _)) (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d (NS.tcAri (NonBlocking , _ , _)) (LFp.doneLF _ _) = refl
tsCnxt-noLF l d NS.tcBlk (LFp.sendLF _ _) = refl
tsCnxt-noLF l d NS.tcBlk (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d NS.tcBlk (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d NS.tcBlk (LFp.doneLF _ _) = refl
tsCnxt-noLF l d NS.tcNbl (LFp.sendLF _ _) = refl
tsCnxt-noLF l d NS.tcNbl (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d NS.tcNbl (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d NS.tcNbl (LFp.doneLF _ _) = refl
tsCnxt-noLF l d (NS.tcArt _) (LFp.sendLF _ _) = refl
tsCnxt-noLF l d (NS.tcArt _) (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d (NS.tcArt _) (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d (NS.tcArt _) (LFp.doneLF _ _) = refl
tsCnxt-noLF l d NS.tcTxs (LFp.sendLF _ _) = refl
tsCnxt-noLF l d NS.tcTxs (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d NS.tcTxs (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d NS.tcTxs (LFp.doneLF _ _) = refl
tsCnxt-noLF l d (NS.tcWri _) (LFp.sendLF _ _) = refl
tsCnxt-noLF l d (NS.tcWri _) (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d (NS.tcWri _) (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d (NS.tcWri _) (LFp.doneLF _ _) = refl
tsCnxt-noLF l d NS.tcWdone (LFp.sendLF _ _) = refl
tsCnxt-noLF l d NS.tcWdone (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d NS.tcWdone (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d NS.tcWdone (LFp.doneLF _ _) = refl
tsCnxt-noLF l d (NS.tcWrt _) (LFp.sendLF _ _) = refl
tsCnxt-noLF l d (NS.tcWrt _) (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d (NS.tcWrt _) (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d (NS.tcWrt _) (LFp.doneLF _ _) = refl
tsCnxt-noLF l d NS.tcTerm (LFp.sendLF _ _) = refl
tsCnxt-noLF l d NS.tcTerm (LFp.receiveLF _ _) = refl
tsCnxt-noLF l d NS.tcTerm (LFp.apiLFev _ _ _) = refl
tsCnxt-noLF l d NS.tcTerm (LFp.doneLF _ _) = refl
tsSnxt-noLF : (l : Link) (d : Dir) (q : NS.TSsPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → NS.tsSnxt l d q (X , ιLF e₁) a ≡ nothing
tsSnxt-noLF l d NS.tsInit (LFp.sendLF _ _) = refl
tsSnxt-noLF l d NS.tsInit (LFp.receiveLF _ _) = refl
tsSnxt-noLF l d NS.tsInit (LFp.apiLFev _ _ _) = refl
tsSnxt-noLF l d NS.tsInit (LFp.doneLF _ _) = refl
tsSnxt-noLF l d NS.tsIdle (LFp.sendLF _ _) = refl
tsSnxt-noLF l d NS.tsIdle (LFp.receiveLF _ _) = refl
tsSnxt-noLF l d NS.tsIdle (LFp.apiLFev _ _ _) = refl
tsSnxt-noLF l d NS.tsIdle (LFp.doneLF _ _) = refl
tsSnxt-noLF l d (NS.tsWib _) (LFp.sendLF _ _) = refl
tsSnxt-noLF l d (NS.tsWib _) (LFp.receiveLF _ _) = refl
tsSnxt-noLF l d (NS.tsWib _) (LFp.apiLFev _ _ _) = refl
tsSnxt-noLF l d (NS.tsWib _) (LFp.doneLF _ _) = refl
tsSnxt-noLF l d (NS.tsWin _) (LFp.sendLF _ _) = refl
tsSnxt-noLF l d (NS.tsWin _) (LFp.receiveLF _ _) = refl
tsSnxt-noLF l d (NS.tsWin _) (LFp.apiLFev _ _ _) = refl
tsSnxt-noLF l d (NS.tsWin _) (LFp.doneLF _ _) = refl
tsSnxt-noLF l d (NS.tsWrt _) (LFp.sendLF _ _) = refl
tsSnxt-noLF l d (NS.tsWrt _) (LFp.receiveLF _ _) = refl
tsSnxt-noLF l d (NS.tsWrt _) (LFp.apiLFev _ _ _) = refl
tsSnxt-noLF l d (NS.tsWrt _) (LFp.doneLF _ _) = refl
tsSnxt-noLF l d NS.tsBlk (LFp.sendLF _ _) = refl
tsSnxt-noLF l d NS.tsBlk (LFp.receiveLF _ _) = refl
tsSnxt-noLF l d NS.tsBlk (LFp.apiLFev _ _ _) = refl
tsSnxt-noLF l d NS.tsBlk (LFp.doneLF _ _) = refl
tsSnxt-noLF l d NS.tsNbl (LFp.sendLF _ _) = refl
tsSnxt-noLF l d NS.tsNbl (LFp.receiveLF _ _) = refl
tsSnxt-noLF l d NS.tsNbl (LFp.apiLFev _ _ _) = refl
tsSnxt-noLF l d NS.tsNbl (LFp.doneLF _ _) = refl
tsSnxt-noLF l d NS.tsTxs (LFp.sendLF _ _) = refl
tsSnxt-noLF l d NS.tsTxs (LFp.receiveLF _ _) = refl
tsSnxt-noLF l d NS.tsTxs (LFp.apiLFev _ _ _) = refl
tsSnxt-noLF l d NS.tsTxs (LFp.doneLF _ _) = refl
tsSnxt-noLF l d NS.tsDdone (LFp.sendLF _ _) = refl
tsSnxt-noLF l d NS.tsDdone (LFp.receiveLF _ _) = refl
tsSnxt-noLF l d NS.tsDdone (LFp.apiLFev _ _ _) = refl
tsSnxt-noLF l d NS.tsDdone (LFp.doneLF _ _) = refl
tsSnxt-noLF l d NS.tsTerm (LFp.sendLF _ _) = refl
tsSnxt-noLF l d NS.tsTerm (LFp.receiveLF _ _) = refl
tsSnxt-noLF l d NS.tsTerm (LFp.apiLFev _ _ _) = refl
tsSnxt-noLF l d NS.tsTerm (LFp.doneLF _ _) = refl
lnCnxt-noLF : (l : Link) (d : Dir) (q : NS.LNcPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → NS.lnCnxt l d q (X , ιLF e₁) a ≡ nothing
lnCnxt-noLF l d NS.lncIdle (LFp.sendLF _ _) = refl
lnCnxt-noLF l d NS.lncIdle (LFp.receiveLF _ _) = refl
lnCnxt-noLF l d NS.lncIdle (LFp.apiLFev _ _ _) = refl
lnCnxt-noLF l d NS.lncIdle (LFp.doneLF _ _) = refl
lnCnxt-noLF l d NS.lncWreq (LFp.sendLF _ _) = refl
lnCnxt-noLF l d NS.lncWreq (LFp.receiveLF _ _) = refl
lnCnxt-noLF l d NS.lncWreq (LFp.apiLFev _ _ _) = refl
lnCnxt-noLF l d NS.lncWreq (LFp.doneLF _ _) = refl
lnCnxt-noLF l d NS.lncWdone (LFp.sendLF _ _) = refl
lnCnxt-noLF l d NS.lncWdone (LFp.receiveLF _ _) = refl
lnCnxt-noLF l d NS.lncWdone (LFp.apiLFev _ _ _) = refl
lnCnxt-noLF l d NS.lncWdone (LFp.doneLF _ _) = refl
lnCnxt-noLF l d NS.lncBusy (LFp.sendLF _ _) = refl
lnCnxt-noLF l d NS.lncBusy (LFp.receiveLF _ _) = refl
lnCnxt-noLF l d NS.lncBusy (LFp.apiLFev _ _ _) = refl
lnCnxt-noLF l d NS.lncBusy (LFp.doneLF _ _) = refl
lnCnxt-noLF l d (NS.lncRann _) (LFp.sendLF _ _) = refl
lnCnxt-noLF l d (NS.lncRann _) (LFp.receiveLF _ _) = refl
lnCnxt-noLF l d (NS.lncRann _) (LFp.apiLFev _ _ _) = refl
lnCnxt-noLF l d (NS.lncRann _) (LFp.doneLF _ _) = refl
lnCnxt-noLF l d (NS.lncRoff _) (LFp.sendLF _ _) = refl
lnCnxt-noLF l d (NS.lncRoff _) (LFp.receiveLF _ _) = refl
lnCnxt-noLF l d (NS.lncRoff _) (LFp.apiLFev _ _ _) = refl
lnCnxt-noLF l d (NS.lncRoff _) (LFp.doneLF _ _) = refl
lnCnxt-noLF l d (NS.lncRtxs _) (LFp.sendLF _ _) = refl
lnCnxt-noLF l d (NS.lncRtxs _) (LFp.receiveLF _ _) = refl
lnCnxt-noLF l d (NS.lncRtxs _) (LFp.apiLFev _ _ _) = refl
lnCnxt-noLF l d (NS.lncRtxs _) (LFp.doneLF _ _) = refl
lnCnxt-noLF l d (NS.lncRvot _) (LFp.sendLF _ _) = refl
lnCnxt-noLF l d (NS.lncRvot _) (LFp.receiveLF _ _) = refl
lnCnxt-noLF l d (NS.lncRvot _) (LFp.apiLFev _ _ _) = refl
lnCnxt-noLF l d (NS.lncRvot _) (LFp.doneLF _ _) = refl
lnCnxt-noLF l d NS.lncTerm (LFp.sendLF _ _) = refl
lnCnxt-noLF l d NS.lncTerm (LFp.receiveLF _ _) = refl
lnCnxt-noLF l d NS.lncTerm (LFp.apiLFev _ _ _) = refl
lnCnxt-noLF l d NS.lncTerm (LFp.doneLF _ _) = refl
lnSnxt-noLF : (l : Link) (d : Dir) (q : NS.LNsPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → NS.lnSnxt l d q (X , ιLF e₁) a ≡ nothing
lnSnxt-noLF l d NS.lnsIdle (LFp.sendLF _ _) = refl
lnSnxt-noLF l d NS.lnsIdle (LFp.receiveLF _ _) = refl
lnSnxt-noLF l d NS.lnsIdle (LFp.apiLFev _ _ _) = refl
lnSnxt-noLF l d NS.lnsIdle (LFp.doneLF _ _) = refl
lnSnxt-noLF l d NS.lnsBusy (LFp.sendLF _ _) = refl
lnSnxt-noLF l d NS.lnsBusy (LFp.receiveLF _ _) = refl
lnSnxt-noLF l d NS.lnsBusy (LFp.apiLFev _ _ _) = refl
lnSnxt-noLF l d NS.lnsBusy (LFp.doneLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWann _) (LFp.sendLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWann _) (LFp.receiveLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWann _) (LFp.apiLFev _ _ _) = refl
lnSnxt-noLF l d (NS.lnsWann _) (LFp.doneLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWoff _) (LFp.sendLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWoff _) (LFp.receiveLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWoff _) (LFp.apiLFev _ _ _) = refl
lnSnxt-noLF l d (NS.lnsWoff _) (LFp.doneLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWtxs _) (LFp.sendLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWtxs _) (LFp.receiveLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWtxs _) (LFp.apiLFev _ _ _) = refl
lnSnxt-noLF l d (NS.lnsWtxs _) (LFp.doneLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWvot _) (LFp.sendLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWvot _) (LFp.receiveLF _ _) = refl
lnSnxt-noLF l d (NS.lnsWvot _) (LFp.apiLFev _ _ _) = refl
lnSnxt-noLF l d (NS.lnsWvot _) (LFp.doneLF _ _) = refl
lnSnxt-noLF l d NS.lnsDone (LFp.sendLF _ _) = refl
lnSnxt-noLF l d NS.lnsDone (LFp.receiveLF _ _) = refl
lnSnxt-noLF l d NS.lnsDone (LFp.apiLFev _ _ _) = refl
lnSnxt-noLF l d NS.lnsDone (LFp.doneLF _ _) = refl
lnSnxt-noLF l d NS.lnsTerm (LFp.sendLF _ _) = refl
lnSnxt-noLF l d NS.lnsTerm (LFp.receiveLF _ _) = refl
lnSnxt-noLF l d NS.lnsTerm (LFp.apiLFev _ _ _) = refl
lnSnxt-noLF l d NS.lnsTerm (LFp.doneLF _ _) = refl
absCSc-noLF : (l : Link) (d : Dir) (q : CScPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (absCSc l d q) (ιLF e₁) a
absCSc-noLF l d q e₁ {a} with NS.csCfin (coarsenCSc q) in fEq
... | true  = viewV→noOffer (absCSc l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSc l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csCfin ; nxt = NS.csCnxt l d })
                   (coarsenCSc q) {e = ιLF e₁} {a = a} fEq (csCnxt-noLF l d (coarsenCSc q) e₁ {a = a}))
absCSs-noLF : (l : Link) (d : Dir) (q : CSsPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (absCSs l d q) (ιLF e₁) a
absCSs-noLF l d q e₁ {a} with NS.csSfin (coarsenCSs q) in fEq
... | true  = viewV→noOffer (absCSs l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absCSs l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.csSfin ; nxt = NS.csSnxt l d })
                   (coarsenCSs q) {e = ιLF e₁} {a = a} fEq (csSnxt-noLF l d (coarsenCSs q) e₁ {a = a}))
absBFc-noLF : (l : Link) (d : Dir) (q : BFcPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (absBFc l d q) (ιLF e₁) a
absBFc-noLF l d q e₁ {a} with NS.bfCfin (coarsenBFc q) in fEq
... | true  = viewV→noOffer (absBFc l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFc l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d })
                   (coarsenBFc q) {e = ιLF e₁} {a = a} fEq (bfCnxt-noLF l d (coarsenBFc q) e₁ {a = a}))
absBFs-noLF : (l : Link) (d : Dir) (q : BFsPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (absBFs l d q) (ιLF e₁) a
absBFs-noLF l d q e₁ {a} with NS.bfSfin (coarsenBFs q) in fEq
... | true  = viewV→noOffer (absBFs l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absBFs l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d })
                   (coarsenBFs q) {e = ιLF e₁} {a = a} fEq (bfSnxt-noLF l d (coarsenBFs q) e₁ {a = a}))
absKAc-noLF : (l : Link) (d : Dir) (q : KAcPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (absKAc l d q) (ιLF e₁) a
absKAc-noLF l d q e₁ {a} with NS.kaCfin (coarsenKAc q) in fEq
... | true  = viewV→noOffer (absKAc l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAc l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d })
                   (coarsenKAc q) {e = ιLF e₁} {a = a} fEq (kaCnxt-noLF l d (coarsenKAc q) e₁ {a = a}))
absKAs-noLF : (l : Link) (d : Dir) (q : KAsPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (absKAs l d q) (ιLF e₁) a
absKAs-noLF l d q e₁ {a} with NS.kaSfin (coarsenKAs q) in fEq
... | true  = viewV→noOffer (absKAs l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absKAs l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d })
                   (coarsenKAs q) {e = ιLF e₁} {a = a} fEq (kaSnxt-noLF l d (coarsenKAs q) e₁ {a = a}))
absTSc-noLF : (l : Link) (d : Dir) (q : TScPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (absTSc l d q) (ιLF e₁) a
absTSc-noLF l d q e₁ {a} with NS.tsCfin (coarsenTSc q) in fEq
... | true  = viewV→noOffer (absTSc l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSc l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d })
                   (coarsenTSc q) {e = ιLF e₁} {a = a} fEq (tsCnxt-noLF l d (coarsenTSc q) e₁ {a = a}))
absTSs-noLF : (l : Link) (d : Dir) (q : TSsPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (absTSs l d q) (ιLF e₁) a
absTSs-noLF l d q e₁ {a} with NS.tsSfin (coarsenTSs q) in fEq
... | true  = viewV→noOffer (absTSs l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absTSs l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d })
                   (coarsenTSs q) {e = ιLF e₁} {a = a} fEq (tsSnxt-noLF l d (coarsenTSs q) e₁ {a = a}))
absLNc-noLF : (l : Link) (d : Dir) (q : LNcPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (absLNc l d q) (ιLF e₁) a
absLNc-noLF l d q e₁ {a} with NS.lnCfin (coarsenLNc q) in fEq
... | true  = viewV→noOffer (absLNc l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d })
                   (coarsenLNc q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNc l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d })
                   (coarsenLNc q) {e = ιLF e₁} {a = a} fEq (lnCnxt-noLF l d (coarsenLNc q) e₁ {a = a}))
absLNs-noLF : (l : Link) (d : Dir) (q : LNsPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (absLNs l d q) (ιLF e₁) a
absLNs-noLF l d q e₁ {a} with NS.lnSfin (coarsenLNs q) in fEq
... | true  = viewV→noOffer (absLNs l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d })
                   (coarsenLNs q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absLNs l d q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d })
                   (coarsenLNs q) {e = ιLF e₁} {a = a} fEq (lnSnxt-noLF l d (coarsenLNs q) e₁ {a = a}))
decCSc-noLFgen : (l : Link) (d : Dir) (pos : CScPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (decCSc l d pos) (ιLF e₁) a
decCSc-noLFgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSc-src l d pos) (ιCS⁻¹∘ιLF e₁)
decCSs-noLFgen : (l : Link) (d : Dir) (pos : CSsPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (decCSs l d pos) (ιLF e₁) a
decCSs-noLFgen l d pos e₁ = CSNOff.renameMap-noOffer-χ (decCSs-src l d pos) (ιCS⁻¹∘ιLF e₁)
decBFc-noLFgen : (l : Link) (d : Dir) (pos : BFcPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (decBFc l d pos) (ιLF e₁) a
decBFc-noLFgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFc-src l d pos) (ιBF⁻¹∘ιLF e₁)
decBFs-noLFgen : (l : Link) (d : Dir) (pos : BFsPos) {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → ¬ IoOffers (decBFs l d pos) (ιLF e₁) a
decBFs-noLFgen l d pos e₁ = BFNOff.renameMap-noOffer-χ (decBFs-src l d pos) (ιBF⁻¹∘ιLF e₁)

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER C1 — LF direction table-nothing lemmas.
------------------------------------------------------------------------

lfCnxt-dir-no : (l : Link) (d : Dir) (q : NS.LFcPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → lfEvDir e₁ ≢ d → NS.lfCnxt l d q (X , ιLF e₁) a ≡ nothing
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFDone) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcIdle (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWblk _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d (NS.lfcWblk _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWblk _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWblk _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWtxs _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d (NS.lfcWtxs _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWtxs _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWtxs _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWvot _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d (NS.lfcWvot _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWvot _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWvot _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWrng _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d (NS.lfcWrng _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWrng _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-dir-no l d (NS.lfcWrng _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcWdone (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d NS.lfcWdone (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcWdone (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-dir-no l d NS.lfcWdone (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch MsgLFDone} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-dir-no l d NS.lfcBlk (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch MsgLFDone} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-dir-no l d NS.lfcBtx (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch MsgLFDone} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-dir-no l d NS.lfcVot (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch MsgLFDone} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-dir-no l d NS.lfcRng (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ recvLFBlock) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRblk _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRbtx _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRvot _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRnextRng _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d (NS.lfcRlastRng _) (LFp.doneLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcTerm (LFp.sendLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcTerm (LFp.receiveLF l′ d′) ¬d = refl
lfCnxt-dir-no l d NS.lfcTerm (LFp.apiLFev l′ d′ m) ¬d = refl
lfCnxt-dir-no l d NS.lfcTerm (LFp.doneLF l′ d′) ¬d = refl

lfSnxt-dir-no : (l : Link) (d : Dir) (q : NS.LFsPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → lfEvDir e₁ ≢ d → NS.lfSnxt l d q (X , ιLF e₁) a ≡ nothing
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch MsgLFDone} ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , chainSync _} ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , blockFetch _} ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , txSubmission _} ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , keepAlive _} ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.receiveLF l′ d′) {a = _ , _ , _ , leiosNotify _} ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-dir-no l d NS.lfsIdle (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFBlock) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsBlk (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsBtx (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsVot (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFBlockRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFBlockTxsRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFVotesRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFBlockRangeRequest) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFDone) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFBlock) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFBlockTxs) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFVoteDelivery) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFNextBlockAndTxsInRange) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ sendLFLastBlockAndTxsInRange) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ recvLFBlock) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ recvLFBlockTxs) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ recvLFVoteDelivery) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.apiLFev l′ d′ recvLFRangeBlock) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsRng (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWblk _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d (NS.lfsWblk _) (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWblk _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWblk _) (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWtxs _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d (NS.lfsWtxs _) (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWtxs _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWtxs _) (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWvot _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d (NS.lfsWvot _) (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWvot _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWvot _) (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWnext _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d (NS.lfsWnext _) (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWnext _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWnext _) (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWlast _) (LFp.sendLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d (NS.lfsWlast _) (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWlast _) (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-dir-no l d (NS.lfsWlast _) (LFp.doneLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsDone (LFp.doneLF l′ d′) ¬d with l′ ≟ l | d′ ≟ d
... | yes refl | yes refl = ⊥-elim (¬d refl)
... | yes refl | no _ = refl
... | no _ | _ = refl
lfSnxt-dir-no l d NS.lfsDone (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsDone (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsDone (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-dir-no l d NS.lfsTerm (LFp.sendLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsTerm (LFp.receiveLF l′ d′) ¬d = refl
lfSnxt-dir-no l d NS.lfsTerm (LFp.apiLFev l′ d′ m) ¬d = refl
lfSnxt-dir-no l d NS.lfsTerm (LFp.doneLF l′ d′) ¬d = refl

-- absLFc-dir-noBoth / absLFs-dir-noBoth: same-protocol opposite-role abstract non-offers
absLFc-dir-noBoth : (l : Link) (sv : Dir) (q : LFcPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → lfEvDir e₁ ≢ sv → ¬ IoOffers (absLFc l sv q) (ιLF e₁) a
absLFc-dir-noBoth l sv q e₁ {a} ¬d with NS.lfCfin (coarsenLFc q) in fEq
... | true  = viewV→noOffer (absLFc l sv q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l sv })
                   (coarsenLFc q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFc l sv q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l sv })
                   (coarsenLFc q) {e = ιLF e₁} {a = a} fEq (lfCnxt-dir-no l sv (coarsenLFc q) e₁ {a = a} ¬d))
absLFs-dir-noBoth : (l : Link) (sv : Dir) (q : LFsPos)
    {X : Set 0ℓ} (e₁ : LFp.LFEv X) {a : X}
  → lfEvDir e₁ ≢ sv → ¬ IoOffers (absLFs l sv q) (ιLF e₁) a
absLFs-dir-noBoth l sv q e₁ {a} ¬d with NS.lfSfin (coarsenLFs q) in fEq
... | true  = viewV→noOffer (absLFs l sv q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-fin (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l sv })
                   (coarsenLFs q) {e = ιLF e₁} {a = a} fEq)
... | false = viewV→noOffer (absLFs l sv q) {e = ιLF e₁} {a = a}
                (tableSpec-viewV-noOffer (record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l sv })
                   (coarsenLFs q) {e = ιLF e₁} {a = a} fEq (lfSnxt-dir-no l sv (coarsenLFs q) e₁ {a = a} ¬d))

------------------------------------------------------------------------
-- ITEM-4 (io routing) LAYER C2 — the 12-peer bundle ev-inversion, LF channel
-- (driven LF peers at the innermost ⦀, positions #10 / #11; lfc/lfs fields).
------------------------------------------------------------------------

absBundle-LFc-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {lfc′ : LFcPos}
  → cl ≢ sv → lfEvDir e₁ ≡ cl
  → absLFc l cl (lfc ip) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► absLFc l cl lfc′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc qbs (record ip { lfc = lfc′ })
absBundle-LFc-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} {lfc′} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-R (absCSs l sv qcs) _
          (SStep.⦀-ev-R (absBFc l cl qbc) _
            (SStep.⦀-ev-R (absBFs l sv qbs) _
              (SStep.⦀-ev-R (absTSc l cl (tsc ip)) _
                (SStep.⦀-ev-R (absTSs l sv (tss ip)) _
                  (SStep.⦀-ev-R (absLNc l cl (lnc ip)) _
                    (SStep.⦀-ev-R (absLNs l sv (lns ip)) _
                      (SStep.⦀-ev-L (absLFc l cl (lfc ip)) _ astep
                        (noOffer→viewV (absLFs l sv (lfs ip)) (absLFs-dir-noBoth l sv (lfs ip) e₁ ¬sv)))
                    (noOffer→viewV (absLNs l sv (lns ip)) (absLNs-noLF l sv (lns ip) e₁)))
                  (noOffer→viewV (absLNc l cl (lnc ip)) (absLNc-noLF l cl (lnc ip) e₁)))
                (noOffer→viewV (absTSs l sv (tss ip)) (absTSs-noLF l sv (tss ip) e₁)))
              (noOffer→viewV (absTSc l cl (tsc ip)) (absTSc-noLF l cl (tsc ip) e₁)))
            (noOffer→viewV (absBFs l sv qbs) (absBFs-noLF l sv qbs e₁)))
          (noOffer→viewV (absBFc l cl qbc) (absBFc-noLF l cl qbc e₁)))
        (noOffer→viewV (absCSs l sv qcs) (absCSs-noLF l sv qcs e₁)))
      (noOffer→viewV (absCSc l cl qcc) (absCSc-noLF l cl qcc e₁)))
    (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noLF l sv (kas ip) e₁)))
  (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noLF l cl (kac ip) e₁))
  where ¬sv : lfEvDir e₁ ≢ sv
        ¬sv q = cl≢sv (trans (sym eqd) q)

absBundle-LFs-ev : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {lfs′ : LFsPos}
  → cl ≢ sv → lfEvDir e₁ ≡ sv
  → absLFs l sv (lfs ip) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► absLFs l sv lfs′
  → absBundleG l cl sv qcc qcs qbc qbs ip
      ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► absBundleG l cl sv qcc qcs qbc qbs (record ip { lfs = lfs′ })
absBundle-LFs-ev l cl sv qcc qcs qbc qbs ip {X} {e₁} {a} {lfs′} cl≢sv eqd astep =
  SStep.⦀-ev-R (absKAc l cl (kac ip)) _
    (SStep.⦀-ev-R (absKAs l sv (kas ip)) _
      (SStep.⦀-ev-R (absCSc l cl qcc) _
        (SStep.⦀-ev-R (absCSs l sv qcs) _
          (SStep.⦀-ev-R (absBFc l cl qbc) _
            (SStep.⦀-ev-R (absBFs l sv qbs) _
              (SStep.⦀-ev-R (absTSc l cl (tsc ip)) _
                (SStep.⦀-ev-R (absTSs l sv (tss ip)) _
                  (SStep.⦀-ev-R (absLNc l cl (lnc ip)) _
                    (SStep.⦀-ev-R (absLNs l sv (lns ip)) _
                      (SStep.⦀-ev-R (absLFc l cl (lfc ip)) _ astep
                        (noOffer→viewV (absLFc l cl (lfc ip)) (absLFc-dir-noBoth l cl (lfc ip) e₁ ¬cl)))
                    (noOffer→viewV (absLNs l sv (lns ip)) (absLNs-noLF l sv (lns ip) e₁)))
                  (noOffer→viewV (absLNc l cl (lnc ip)) (absLNc-noLF l cl (lnc ip) e₁)))
                (noOffer→viewV (absTSs l sv (tss ip)) (absTSs-noLF l sv (tss ip) e₁)))
              (noOffer→viewV (absTSc l cl (tsc ip)) (absTSc-noLF l cl (tsc ip) e₁)))
            (noOffer→viewV (absBFs l sv qbs) (absBFs-noLF l sv qbs e₁)))
          (noOffer→viewV (absBFc l cl qbc) (absBFc-noLF l cl qbc e₁)))
        (noOffer→viewV (absCSs l sv qcs) (absCSs-noLF l sv qcs e₁)))
      (noOffer→viewV (absCSc l cl qcc) (absCSc-noLF l cl qcc e₁)))
    (noOffer→viewV (absKAs l sv (kas ip)) (absKAs-noLF l sv (kas ip) e₁)))
  (noOffer→viewV (absKAc l cl (kac ip)) (absKAc-noLF l cl (kac ip) e₁))
  where ¬cl : lfEvDir e₁ ≢ cl
        ¬cl q = cl≢sv (sym (trans (sym eqd) q))

data BundleLFEvR (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : LFp.LFEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  btlfcE : (lfc′ : LFcPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc bfs (record ip { lfc = lfc′ })
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► absBundleG l cl sv csc css bfc bfs (record ip { lfc = lfc′ })
        → BundleLFEvR l cl sv csc css bfc bfs ip e₁ a Bd′
  btlfsE : (lfs′ : LFsPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc bfs (record ip { lfs = lfs′ })
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► absBundleG l cl sv csc css bfc bfs (record ip { lfs = lfs′ })
        → BundleLFEvR l cl sv csc css bfc bfs ip e₁ a Bd′

finishLFc-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decLFc l cl (lfc ip) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► P′
  → BundleLFEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip) ⦀ (P′ ⦀ (decLFs l sv (lfs ip)))))))))))))
finishLFc-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simLFc′ l cl (lfc ip) sM
... | _ , lfc′ , _ , _ , Meq , aStep0 =
      btlfcE lfc′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip) ⦀ (z ⦀ (decLFs l sv (lfs ip))))))))))))) Meq)
        (absBundle-LFc-ev l cl sv csc css bfc bfs ip {lfc′ = lfc′} cl≢sv
          (sym (apiDir-inj (lfc-ev-dir l cl (lfc ip) sM) (lfApiDir e₁))) aStep0)

finishLFs-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decLFs l sv (lfs ip) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► P′
  → BundleLFEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip) ⦀ (decLFc l cl (lfc ip) ⦀ (P′))))))))))))
finishLFs-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simLFs′ l sv (lfs ip) sM
... | _ , lfs′ , _ , _ , Meq , aStep0 =
      btlfsE lfs′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip) ⦀ (decLFc l cl (lfc ip) ⦀ (z)))))))))))) Meq)
        (absBundle-LFs-ev l cl sv csc css bfc bfs ip {lfs′ = lfs′} cl≢sv
          (sym (apiDir-inj (lfs-ev-dir l sv (lfs ip) sM) (lfApiDir e₁))) aStep0)

-- 12-peer bundle ev-inversion (LF)
bundle-LF-ev-inv : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► Bd′
  → BundleLFEvR l cl sv csc css bfc bfs ip e₁ a Bd′
bundle-LF-ev-inv l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.evSync () _ _
... | PEA.evL _ sM = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιLF e₁) (_ , sM))
... | PEA.evBoth _ sM _ = ⊥-elim (decKAc-noOffer l cl (kac ip) (ιKA⁻¹∘ιLF e₁) (_ , sM))
... | PEA.evR _ q1
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.evSync () _ _
...   | PEA.evL _ sM = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιLF e₁) (_ , sM))
...   | PEA.evBoth _ sM _ = ⊥-elim (decKAs-noOffer l sv (kas ip) (ιKA⁻¹∘ιLF e₁) (_ , sM))
...   | PEA.evR _ q2
      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.evSync () _ _
...     | PEA.evL _ sM = ⊥-elim (decCSc-noLFgen l cl csc e₁ (_ , sM))
...     | PEA.evBoth _ sM _ = ⊥-elim (decCSc-noLFgen l cl csc e₁ (_ , sM))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM = ⊥-elim (decCSs-noLFgen l sv css e₁ (_ , sM))
...       | PEA.evBoth _ sM _ = ⊥-elim (decCSs-noLFgen l sv css e₁ (_ , sM))
...       | PEA.evR _ q4
          with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.evSync () _ _
...         | PEA.evL _ sM = ⊥-elim (decBFc-noLFgen l cl bfc e₁ (_ , sM))
...         | PEA.evBoth _ sM _ = ⊥-elim (decBFc-noLFgen l cl bfc e₁ (_ , sM))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM = ⊥-elim (decBFs-noLFgen l sv bfs e₁ (_ , sM))
...           | PEA.evBoth _ sM _ = ⊥-elim (decBFs-noLFgen l sv bfs e₁ (_ , sM))
...           | PEA.evR _ q6
              with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.evSync () _ _
...             | PEA.evL _ sM = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιLF e₁) (_ , sM))
...             | PEA.evBoth _ sM _ = ⊥-elim (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιLF e₁) (_ , sM))
...             | PEA.evR _ q7
                with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.evSync () _ _
...               | PEA.evL _ sM = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιLF e₁) (_ , sM))
...               | PEA.evBoth _ sM _ = ⊥-elim (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιLF e₁) (_ , sM))
...               | PEA.evR _ q8
                  with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.evSync () _ _
...                 | PEA.evL _ sM = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιLF e₁) (_ , sM))
...                 | PEA.evBoth _ sM _ = ⊥-elim (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιLF e₁) (_ , sM))
...                 | PEA.evR _ q9
                    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.evSync () _ _
...                   | PEA.evL _ sM = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιLF e₁) (_ , sM))
...                   | PEA.evBoth _ sM _ = ⊥-elim (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιLF e₁) (_ , sM))
...                   | PEA.evR _ q10
                      with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip)) q10
...                     | PEA.evSync () _ _
...                     | PEA.evL _ sM = finishLFc-ev l cl sv csc css bfc bfs ip cl≢sv sM
...                     | PEA.evBoth _ sM sTail =
                          ⊥-elim (decLFs-dir-noOffer l sv (lfs ip) e₁
                            (λ q → cl≢sv (trans (apiDir-inj (lfc-ev-dir l cl (lfc ip) sM) (lfApiDir e₁)) q))
                            (_ , sTail))
...                     | PEA.evR _ qs = finishLFs-ev l cl sv csc css bfc bfs ip cl≢sv qs
------------------------------------------------------------------------
-- GAP-B L4 — the 12-peer bundle ev-inversion (DOWNWARD peel), CS side.
-- A visible CS-image event `ιCS e₁` of `bundleG` is fired by exactly ONE of
-- the two driven CS peers (client at cl / server at sv); the ten siblings are
-- refuted by NON-OFFER (inert KA/TS/LN/LF via the `ιX⁻¹∘ιCS` cross-preimages;
-- opposite-protocol BF via `decBF*-noCSgen`; the same-protocol opposite-role
-- driven peer via the direction leaf, cl ≢ sv).  Peels the 11 `⦀` with
-- `PEA.Par-ev-elim ∅ESa`; the abstract step is rebuilt by `absBundle-CS{c,s}-ev`.
------------------------------------------------------------------------

-- tail (decBFc ⦀ decBFs ⦀ TS ⦀ LN ⦀ LF) offers no CS-image event (all BF/inert)
csTail-bfc-noOffer : (l : Link) (cl sv : Dir) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X}
  → ¬ IoOffers (decBFc l cl bfc ⦀ (decBFs l sv bfs
       ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))) (ιCS e₁) a
csTail-bfc-noOffer l cl sv bfc bfs ip e₁ =
  SStep.⦀-noOffer (decBFc l cl bfc) _ (decBFc-noCSgen l cl bfc e₁)
    (SStep.⦀-noOffer (decBFs l sv bfs) _ (decBFs-noCSgen l sv bfs e₁)
      (SStep.⦀-noOffer (decTSc l cl (tsc ip)) _ (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιCS e₁))
        (SStep.⦀-noOffer (decTSs l sv (tss ip)) _ (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιCS e₁))
          (SStep.⦀-noOffer (decLNc l cl (lnc ip)) _ (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιCS e₁))
            (SStep.⦀-noOffer (decLNs l sv (lns ip)) _ (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιCS e₁))
              (SStep.⦀-noOffer (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip))
                (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιCS e₁))
                (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιCS e₁))))))))

-- tail (decCSs ⦀ decBFc ⦀ …) offers no CS-image event when csEvDir e₁ ≢ sv
csTail-css-noOffer : (l : Link) (cl sv : Dir) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : CS.CSEv X) {a : X} → csEvDir e₁ ≢ sv
  → ¬ IoOffers (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
       ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))) (ιCS e₁) a
csTail-css-noOffer l cl sv css bfc bfs ip e₁ ¬sv =
  SStep.⦀-noOffer (decCSs l sv css) _ (decCSs-dir-noOffer l sv css e₁ ¬sv)
    (csTail-bfc-noOffer l cl sv bfc bfs ip e₁)

-- which driven CS peer of the bundle fired the CS-image event (+ target + abstract step)
data BundleCSEvR (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : CS.CSEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  bcscE : (csc′ : CScPos)
        → Bd′ ≡ bundleG l cl sv csc′ css bfc bfs ip
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absBundleG l cl sv csc′ css bfc bfs ip
        → BundleCSEvR l cl sv csc css bfc bfs ip e₁ a Bd′
  bcssE : (css′ : CSsPos)
        → Bd′ ≡ bundleG l cl sv csc css′ bfc bfs ip
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absBundleG l cl sv csc css′ bfc bfs ip
        → BundleCSEvR l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a CS-client driven step into the bundle result (target index is the
-- exact `⦀`-nesting the peel refines `Bd′` to; abstract step via `absBundle-CSc-ev`)
finishCSc-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decCSc l cl csc ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► P′
  → BundleCSEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (P′
        ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
        ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))))
finishCSc-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simCSc′ l cl csc sM
... | _ , csc′ , _ , _ , Meq , aStep0 =
      bcscE csc′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (z
               ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
               ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))) Meq)
        (absBundle-CSc-ev l cl sv csc css bfc bfs ip {qcc′ = csc′} cl≢sv
          (sym (apiDir-inj (csc-ev-dir l cl csc sM) (csApiDir e₁))) aStep0)

-- fold a CS-server driven step into the bundle result
finishCSs-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decCSs l sv css ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► P′
  → BundleCSEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (P′
        ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
        ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))))
finishCSs-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simCSs′ l sv css sM
... | _ , css′ , _ , _ , Meq , aStep0 =
      bcssE css′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (z
               ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
               ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))) Meq)
        (absBundle-CSs-ev l cl sv csc css bfc bfs ip {qcs′ = css′} cl≢sv
          (sym (apiDir-inj (css-ev-dir l sv css sM) (csApiDir e₁))) aStep0)

-- 12-peer bundle ev-inversion (CS): peel each `⦀`, refute the ten siblings, invert the driven CS peer
bundle-CS-ev-inv : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► Bd′
  → BundleCSEvR l cl sv csc css bfc bfs ip e₁ a Bd′
bundle-CS-ev-inv l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...     | PEA.evL _ sM      = finishCSc-ev l cl sv csc css bfc bfs ip cl≢sv sM
...     | PEA.evBoth _ sM sTail =
            ⊥-elim (csTail-css-noOffer l cl sv css bfc bfs ip e₁
                      (λ q → cl≢sv (trans (apiDir-inj (csc-ev-dir l cl csc sM) (csApiDir e₁)) q))
                      (_ , sTail))
...     | PEA.evR _ q3
        with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.evSync () _ _
...       | PEA.evL _ sM      = finishCSs-ev l cl sv csc css bfc bfs ip cl≢sv sM
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

------------------------------------------------------------------------
-- GAP-B L4 — the 12-peer bundle ev-inversion (DOWNWARD peel), BF side.
-- Dual of the CS peel: a BF-image event `ιBF e₁` is fired by exactly one of
-- the two driven BF peers; the ten siblings are refuted (inert KA/TS/LN/LF via
-- the `ιX⁻¹∘ιBF` cross-preimages; opposite-protocol CS via `decCS*-noBFgen`;
-- the same-protocol opposite-role driven peer via the direction leaf, cl ≢ sv).
------------------------------------------------------------------------

-- tail (TS ⦀ LN ⦀ LF) offers no BF-image event (all inert)
bfTail-tsc-noOffer : (l : Link) (cl sv : Dir) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X}
  → ¬ IoOffers (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))) (ιBF e₁) a
bfTail-tsc-noOffer l cl sv ip e₁ =
  SStep.⦀-noOffer (decTSc l cl (tsc ip)) _ (decTSc-noOffer l cl (tsc ip) (ιTS⁻¹∘ιBF e₁))
    (SStep.⦀-noOffer (decTSs l sv (tss ip)) _ (decTSs-noOffer l sv (tss ip) (ιTS⁻¹∘ιBF e₁))
      (SStep.⦀-noOffer (decLNc l cl (lnc ip)) _ (decLNc-noOffer l cl (lnc ip) (ιLN⁻¹∘ιBF e₁))
        (SStep.⦀-noOffer (decLNs l sv (lns ip)) _ (decLNs-noOffer l sv (lns ip) (ιLN⁻¹∘ιBF e₁))
          (SStep.⦀-noOffer (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip))
            (decLFc-noOffer l cl (lfc ip) (ιLF⁻¹∘ιBF e₁))
            (decLFs-noOffer l sv (lfs ip) (ιLF⁻¹∘ιBF e₁))))))

-- tail (decBFs ⦀ TS ⦀ …) offers no BF-image event when bfEvDir e₁ ≢ sv
bfTail-bfs-noOffer : (l : Link) (cl sv : Dir) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} (e₁ : BF.BFEv X) {a : X} → bfEvDir e₁ ≢ sv
  → ¬ IoOffers (decBFs l sv bfs ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
       ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))) (ιBF e₁) a
bfTail-bfs-noOffer l cl sv bfs ip e₁ ¬sv =
  SStep.⦀-noOffer (decBFs l sv bfs) _ (decBFs-dir-noOffer l sv bfs e₁ ¬sv)
    (bfTail-tsc-noOffer l cl sv ip e₁)

-- which driven BF peer of the bundle fired the BF-image event (+ target + abstract step)
data BundleBFEvR (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} (e₁ : BF.BFEv X) (a : X) (Bd′ : NetProc) : Set₁ where
  bcbcE : (bfc′ : BFcPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc′ bfs ip
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBundleG l cl sv csc css bfc′ bfs ip
        → BundleBFEvR l cl sv csc css bfc bfs ip e₁ a Bd′
  bcbsE : (bfs′ : BFsPos)
        → Bd′ ≡ bundleG l cl sv csc css bfc bfs′ ip
        → absBundleG l cl sv csc css bfc bfs ip
            ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBundleG l cl sv csc css bfc bfs′ ip
        → BundleBFEvR l cl sv csc css bfc bfs ip e₁ a Bd′

-- fold a BF-client driven step into the bundle result
finishBFc-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decBFc l cl bfc ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → BundleBFEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (P′
        ⦀ (decBFs l sv bfs ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))))
finishBFc-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simBFc′ l cl bfc sM
... | _ , bfc′ , _ , _ , Meq , aStep0 =
      bcbcE bfc′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (z
               ⦀ (decBFs l sv bfs ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))) Meq)
        (absBundle-BFc-ev l cl sv csc css bfc bfs ip {qbc′ = bfc′} cl≢sv
          (sym (apiDir-inj (bfc-ev-dir l cl bfc sM) (bfApiDir e₁))) aStep0)

-- fold a BF-server driven step into the bundle result
finishBFs-ev : (l : Link) (cl sv : Dir) (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : NetProc} → cl ≢ sv
  → decBFs l sv bfs ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► P′
  → BundleBFEvR l cl sv csc css bfc bfs ip e₁ a
      (decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (P′
        ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
        ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))))
finishBFs-ev l cl sv csc css bfc bfs ip {X} {e₁} {a} cl≢sv sM with simBFs′ l sv bfs sM
... | _ , bfs′ , _ , _ , Meq , aStep0 =
      bcbsE bfs′
        (cong (λ z → decKAc l cl (kac ip) ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (z
               ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
               ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))) Meq)
        (absBundle-BFs-ev l cl sv csc css bfc bfs ip {qbs′ = bfs′} cl≢sv
          (sym (apiDir-inj (bfs-ev-dir l sv bfs sM) (bfApiDir e₁))) aStep0)

-- 12-peer bundle ev-inversion (BF): peel each `⦀`, refute the ten siblings, invert the driven BF peer
bundle-BF-ev-inv : (l : Link) (cl sv : Dir) → cl ≢ sv
     → (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► Bd′
  → BundleBFEvR l cl sv csc css bfc bfs ip e₁ a Bd′
bundle-BF-ev-inv l cl sv cl≢sv csc css bfc bfs ip {X} {e₁} {a} step
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
...         | PEA.evL _ sM      = finishBFc-ev l cl sv csc css bfc bfs ip cl≢sv sM
...         | PEA.evBoth _ sM sTail =
              ⊥-elim (bfTail-bfs-noOffer l cl sv bfs ip e₁
                        (λ q → cl≢sv (trans (apiDir-inj (bfc-ev-dir l cl bfc sM) (bfApiDir e₁)) q))
                        (_ , sTail))
...         | PEA.evR _ q5
            with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.evSync () _ _
...           | PEA.evL _ sM      = finishBFs-ev l cl sv csc css bfc bfs ip cl≢sv sM
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



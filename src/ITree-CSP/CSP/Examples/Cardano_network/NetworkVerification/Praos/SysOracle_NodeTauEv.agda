{-# OPTIONS --guardedness #-}

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv (blkA : Block₃) where

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
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA
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

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore blkA public

------------------------------------------------------------------------
-- STAGE-2 NODE-τ BACKBONE — the 12-peer bundle τ-inversion.  A τ of a
-- `bundleG l cl sv csc css bfc bfs ip` interleave is exactly ONE of the SIX
-- moving peers' loop re-entry sil (`…Sil st → …Head st`): the four DRIVEN
-- CS/BF peers OR the TxSubmission client/server (now tracked in `ip`); the six
-- frozen KA/LN/LF peers are τ-free (refuted).  Peels the 11 nested `⦀` with
-- `Par-τ-elim ∅ESa`, refuting the frozen peers and inverting the moving one.
------------------------------------------------------------------------

-- which moving peer of a bundle carried the τ (+ its loop state + target)
data BundleτR (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     (Bd′ : NetProc) : Set₁ where
  bcsc : (st : CS.CSState) → csc ≡ csSil st
       → Bd′ ≡ bundleG l cl sv (csHead st) css bfc bfs ip → BundleτR l cl sv csc css bfc bfs ip Bd′
  bcss : (st : CS.CSState) → css ≡ ssSil st
       → Bd′ ≡ bundleG l cl sv csc (ssHead st) bfc bfs ip → BundleτR l cl sv csc css bfc bfs ip Bd′
  bbfc : (st : BF.BFState) → bfc ≡ bcSil st
       → Bd′ ≡ bundleG l cl sv csc css (bcHead st) bfs ip → BundleτR l cl sv csc css bfc bfs ip Bd′
  bbfs : (st : BF.BFState) → bfs ≡ bsSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc (bsHead st) ip → BundleτR l cl sv csc css bfc bfs ip Bd′
  btsc : (st : TS.TSState) → tsc ip ≡ tcSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tcHead st) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  btss : (st : TS.TSState) → tss ip ≡ tsSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tsHead st) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  bkac : (st : KA.KAState) → kac ip ≡ kcSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kcHead st) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  bkas : (st : KA.KAState) → kas ip ≡ ksSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (ksHead st) (lnc ip) (lns ip) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  blnc : (st : LNp.LNState) → lnc ip ≡ lncSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lncHead st) (lns ip) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  blns : (st : LNp.LNState) → lns ip ≡ lnsSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lnsHead st) (lfc ip) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  blfc : (st : LFp.LFState) → lfc ip ≡ lfcSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfcHead st) (lfs ip)) → BundleτR l cl sv csc css bfc bfs ip Bd′
  blfs : (st : LFp.LFState) → lfs ip ≡ lfsSil st
       → Bd′ ≡ bundleG l cl sv csc css bfc bfs (mkInert (tsc ip) (tss ip) (kac ip) (kas ip) (lnc ip) (lns ip) (lfc ip) (lfsHead st)) → BundleτR l cl sv csc css bfc bfs ip Bd′

-- finisher for a KA-client peel (peer 1): M is the KA client at `kcHead st`
finishKAc : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ M : NetProc}
  → Bd′ ≡ (M ⦀ (decKAs l sv (kas ip) ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
              ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))))
  → (Σ[ st ∈ KA.KAState ] (kac ip ≡ kcSil st) × (M ≡ decKAc l cl (kcHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishKAc l cl sv csc css bfc bfs ip e1 (st , poseq , refl) = bkac st poseq e1

-- finisher for a KA-server peel (peer 2): M is the KA server at `ksHead st`
finishKAs : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1)
  → R1 ≡ (M ⦀ (decCSc l cl csc ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
              ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))))
  → (Σ[ st ∈ KA.KAState ] (kas ip ≡ ksSil st) × (M ≡ decKAs l sv (ksHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishKAs l cl sv csc css bfc bfs ip e1 e2 (st , poseq , refl) =
  bkas st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_) e2))

-- finisher for a CS-client peel: fold the three prefix eqs + the CS-client
-- inversion into a `bcsc` (the `refl` match on the target eq fixes the peer)
finishCSc : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (M ⦀ (decCSs l sv css ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
              ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))))
  → (Σ[ st ∈ CS.CSState ] (csc ≡ csSil st) × (M ≡ decCSc l cl (csHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishCSc l cl sv csc css bfc bfs ip e1 e2 e3 (st , poseq , refl) =
  bcsc st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_) e3))))

-- finisher for a CS-server peel
finishCSs : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3)
  → R3 ≡ (M ⦀ (decBFc l cl bfc ⦀ (decBFs l sv bfs
              ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))))
  → (Σ[ st ∈ CS.CSState ] (css ≡ ssSil st) × (M ≡ decCSs l sv (ssHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishCSs l cl sv csc css bfc bfs ip e1 e2 e3 e4 (st , poseq , refl) =
  bcss st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_)
                (trans e3 (cong (decCSc l cl csc ⦀_) e4))))))

-- finisher for a BF-client peel
finishBFc : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (M ⦀ (decBFs l sv bfs
              ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))))
  → (Σ[ st ∈ BF.BFState ] (bfc ≡ bcSil st) × (M ≡ decBFc l cl (bcHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishBFc l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 (st , poseq , refl) =
  bbfc st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_)
                (trans e3 (cong (decCSc l cl csc ⦀_)
                (trans e4 (cong (decCSs l sv css ⦀_) e5))))))))

-- finisher for a BF-server peel
finishBFs : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5)
  → R5 ≡ (M ⦀ (decTSc l cl (tsc ip) ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))))
  → (Σ[ st ∈ BF.BFState ] (bfs ≡ bsSil st) × (M ≡ decBFs l sv (bsHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishBFs l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 (st , poseq , refl) =
  bbfs st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_)
                (trans e3 (cong (decCSc l cl csc ⦀_)
                (trans e4 (cong (decCSs l sv css ⦀_)
                (trans e5 (cong (decBFc l cl bfc ⦀_) e6))))))))))

-- finisher for a TS-client peel (peer 7): M is the TS client at `tcHead st`
finishTSc : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 R6 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5) → R5 ≡ (decBFs l sv bfs ⦀ R6)
  → R6 ≡ (M ⦀ (decTSs l sv (tss ip) ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))))
  → (Σ[ st ∈ TS.TSState ] (tsc ip ≡ tcSil st) × (M ≡ decTSc l cl (tcHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishTSc l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 e7 (st , poseq , refl) =
  btsc st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_)
                (trans e3 (cong (decCSc l cl csc ⦀_)
                (trans e4 (cong (decCSs l sv css ⦀_)
                (trans e5 (cong (decBFc l cl bfc ⦀_)
                (trans e6 (cong (decBFs l sv bfs ⦀_) e7))))))))))))

-- finisher for a TS-server peel (peer 8): M is the TS server at `tsHead st`
finishTSs : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 R6 R7 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5) → R5 ≡ (decBFs l sv bfs ⦀ R6)
  → R6 ≡ (decTSc l cl (tsc ip) ⦀ R7)
  → R7 ≡ (M ⦀ (decLNc l cl (lnc ip) ⦀ (decLNs l sv (lns ip)
              ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))))
  → (Σ[ st ∈ TS.TSState ] (tss ip ≡ tsSil st) × (M ≡ decTSs l sv (tsHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishTSs l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 e7 e8 (st , poseq , refl) =
  btss st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_)
                (trans e2 (cong (decKAs l sv (kas ip) ⦀_)
                (trans e3 (cong (decCSc l cl csc ⦀_)
                (trans e4 (cong (decCSs l sv css ⦀_)
                (trans e5 (cong (decBFc l cl bfc ⦀_)
                (trans e6 (cong (decBFs l sv bfs ⦀_)
                (trans e7 (cong (decTSc l cl (tsc ip) ⦀_) e8))))))))))))))

-- finisher for a LeiosNotify-client peel (peer 9): M is the LN client at `lncHead st`
finishLNc : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 R6 R7 R8 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5) → R5 ≡ (decBFs l sv bfs ⦀ R6)
  → R6 ≡ (decTSc l cl (tsc ip) ⦀ R7) → R7 ≡ (decTSs l sv (tss ip) ⦀ R8)
  → R8 ≡ (M ⦀ (decLNs l sv (lns ip) ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip))))
  → (Σ[ st ∈ LNp.LNState ] (lnc ip ≡ lncSil st) × (M ≡ decLNc l cl (lncHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishLNc l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 e7 e8 e9 (st , poseq , refl) =
  blnc st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_) (trans e2 (cong (decKAs l sv (kas ip) ⦀_) (trans e3 (cong (decCSc l cl csc ⦀_) (trans e4 (cong (decCSs l sv css ⦀_) (trans e5 (cong (decBFc l cl bfc ⦀_) (trans e6 (cong (decBFs l sv bfs ⦀_) (trans e7 (cong (decTSc l cl (tsc ip) ⦀_) (trans e8 (cong (decTSs l sv (tss ip) ⦀_) e9))))))))))))))))

-- finisher for a LeiosNotify-server peel (peer 10): M is the LN server at `lnsHead st`
finishLNs : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 R6 R7 R8 R9 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5) → R5 ≡ (decBFs l sv bfs ⦀ R6)
  → R6 ≡ (decTSc l cl (tsc ip) ⦀ R7) → R7 ≡ (decTSs l sv (tss ip) ⦀ R8)
  → R8 ≡ (decLNc l cl (lnc ip) ⦀ R9)
  → R9 ≡ (M ⦀ (decLFc l cl (lfc ip) ⦀ decLFs l sv (lfs ip)))
  → (Σ[ st ∈ LNp.LNState ] (lns ip ≡ lnsSil st) × (M ≡ decLNs l sv (lnsHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishLNs l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 (st , poseq , refl) =
  blns st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_) (trans e2 (cong (decKAs l sv (kas ip) ⦀_) (trans e3 (cong (decCSc l cl csc ⦀_) (trans e4 (cong (decCSs l sv css ⦀_) (trans e5 (cong (decBFc l cl bfc ⦀_) (trans e6 (cong (decBFs l sv bfs ⦀_) (trans e7 (cong (decTSc l cl (tsc ip) ⦀_) (trans e8 (cong (decTSs l sv (tss ip) ⦀_) (trans e9 (cong (decLNc l cl (lnc ip) ⦀_) e10))))))))))))))))))

-- finisher for a LeiosFetch-client peel (peer 11): M is the LF client at `lfcHead st`
finishLFc : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5) → R5 ≡ (decBFs l sv bfs ⦀ R6)
  → R6 ≡ (decTSc l cl (tsc ip) ⦀ R7) → R7 ≡ (decTSs l sv (tss ip) ⦀ R8)
  → R8 ≡ (decLNc l cl (lnc ip) ⦀ R9) → R9 ≡ (decLNs l sv (lns ip) ⦀ R10)
  → R10 ≡ (M ⦀ decLFs l sv (lfs ip))
  → (Σ[ st ∈ LFp.LFState ] (lfc ip ≡ lfcSil st) × (M ≡ decLFc l cl (lfcHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishLFc l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 (st , poseq , refl) =
  blfc st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_) (trans e2 (cong (decKAs l sv (kas ip) ⦀_) (trans e3 (cong (decCSc l cl csc ⦀_) (trans e4 (cong (decCSs l sv css ⦀_) (trans e5 (cong (decBFc l cl bfc ⦀_) (trans e6 (cong (decBFs l sv bfs ⦀_) (trans e7 (cong (decTSc l cl (tsc ip) ⦀_) (trans e8 (cong (decTSs l sv (tss ip) ⦀_) (trans e9 (cong (decLNc l cl (lnc ip) ⦀_) (trans e10 (cong (decLNs l sv (lns ip) ⦀_) e11))))))))))))))))))))

-- finisher for a LeiosFetch-server peel (peer 12): M is the LF server at `lfsHead st`
finishLFs : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos)
     {Bd′ R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 M : NetProc}
  → Bd′ ≡ (decKAc l cl (kac ip) ⦀ R1) → R1 ≡ (decKAs l sv (kas ip) ⦀ R2)
  → R2 ≡ (decCSc l cl csc ⦀ R3) → R3 ≡ (decCSs l sv css ⦀ R4)
  → R4 ≡ (decBFc l cl bfc ⦀ R5) → R5 ≡ (decBFs l sv bfs ⦀ R6)
  → R6 ≡ (decTSc l cl (tsc ip) ⦀ R7) → R7 ≡ (decTSs l sv (tss ip) ⦀ R8)
  → R8 ≡ (decLNc l cl (lnc ip) ⦀ R9) → R9 ≡ (decLNs l sv (lns ip) ⦀ R10)
  → R10 ≡ (decLFc l cl (lfc ip) ⦀ M)
  → (Σ[ st ∈ LFp.LFState ] (lfs ip ≡ lfsSil st) × (M ≡ decLFs l sv (lfsHead st)))
  → BundleτR l cl sv csc css bfc bfs ip Bd′
finishLFs l cl sv csc css bfc bfs ip e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 (st , poseq , refl) =
  blfs st poseq (trans e1 (cong (decKAc l cl (kac ip) ⦀_) (trans e2 (cong (decKAs l sv (kas ip) ⦀_) (trans e3 (cong (decCSc l cl csc ⦀_) (trans e4 (cong (decCSs l sv css ⦀_) (trans e5 (cong (decBFc l cl bfc ⦀_) (trans e6 (cong (decBFs l sv bfs ⦀_) (trans e7 (cong (decTSc l cl (tsc ip) ⦀_) (trans e8 (cong (decTSs l sv (tss ip) ⦀_) (trans e9 (cong (decLNc l cl (lnc ip) ⦀_) (trans e10 (cong (decLNs l sv (lns ip) ⦀_) e11))))))))))))))))))))

-- 12-peer bundle τ-inversion (TOTAL): peel each `⦀`, refute the four frozen
-- KA peers, invert the eight moving CS/BF/TS/LN/LF peers
bundle-τ-inv : (l : Link) (cl sv : Dir)
     (csc : CScPos) (css : CSsPos) (bfc : BFcPos) (bfs : BFsPos) (ip : InertPos) {Bd′ : NetProc}
  → bundleG l cl sv csc css bfc bfs ip ─[ τ ]─► Bd′
  → BundleτR l cl sv csc css bfc bfs ip Bd′
bundle-τ-inv l cl sv csc css bfc bfs ip step
  with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decKAc l cl (kac ip)) _ step
... | PEA.τL _ cstep eq1 = finishKAc l cl sv csc css bfc bfs ip eq1 (decKAc-τ-inv l cl (kac ip) cstep)
... | PEA.τR _ q1 eq1
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decKAs l sv (kas ip)) _ q1
...   | PEA.τL _ cstep eq2 = finishKAs l cl sv csc css bfc bfs ip eq1 eq2 (decKAs-τ-inv l sv (kas ip) cstep)
...   | PEA.τR _ q2 eq2
      with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decCSc l cl csc) _ q2
...     | PEA.τL _ cstep eq3 = finishCSc l cl sv csc css bfc bfs ip eq1 eq2 eq3 (decCSc-τ-inv l cl csc cstep)
...     | PEA.τR _ q3 eq3
        with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decCSs l sv css) _ q3
...       | PEA.τL _ cstep eq4 = finishCSs l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 (decCSs-τ-inv l sv css cstep)
...       | PEA.τR _ q4 eq4
          with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decBFc l cl bfc) _ q4
...         | PEA.τL _ cstep eq5 = finishBFc l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 (decBFc-τ-inv l cl bfc cstep)
...         | PEA.τR _ q5 eq5
            with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decBFs l sv bfs) _ q5
...           | PEA.τL _ cstep eq6 = finishBFs l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 (decBFs-τ-inv l sv bfs cstep)
...           | PEA.τR _ q6 eq6
              with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decTSc l cl (tsc ip)) _ q6
...             | PEA.τL _ cstep eq7 = finishTSc l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 eq7 (decTSc-τ-inv l cl (tsc ip) cstep)
...             | PEA.τR _ q7 eq7
                with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decTSs l sv (tss ip)) _ q7
...               | PEA.τL _ cstep eq8 = finishTSs l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 (decTSs-τ-inv l sv (tss ip) cstep)
...               | PEA.τR _ q8 eq8
                  with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decLNc l cl (lnc ip)) _ q8
...                 | PEA.τL _ cstep eq9 = finishLNc l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 (decLNc-τ-inv l cl (lnc ip) cstep)
...                 | PEA.τR _ q9 eq9
                    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decLNs l sv (lns ip)) _ q9
...                   | PEA.τL _ cstep eq10 = finishLNs l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 (decLNs-τ-inv l sv (lns ip) cstep)
...                   | PEA.τR _ q10 eq10
                      with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decLFc l cl (lfc ip)) (decLFs l sv (lfs ip)) q10
...                     | PEA.τL _ cstep eq11 = finishLFc l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 eq11 (decLFc-τ-inv l cl (lfc ip) cstep)
...                     | PEA.τR _ cstep eq11 = finishLFs l cl sv csc css bfc bfs ip eq1 eq2 eq3 eq4 eq5 eq6 eq7 eq8 eq9 eq10 eq11 (decLFs-τ-inv l sv (lfs ip) cstep)


------------------------------------------------------------------------
-- STAGE-2 NODE τ-INVERSIONS.  A node `(bundle₁ ⦀ bundle₂) ∥⇘ apiES ⇙ driver`
-- τ is a BUNDLE τ (peel via `reflect-node-τ` → `Par-τ-elim ∅ESa` → the two
-- links → `bundle-τ-inv`); the DRIVER τ is refuted (produce/consume/relay are
-- τ-free prefix chains).  Each `finishX-{L,R}` folds the per-link `BundleτR`
-- into the node-state successor `nX′` (one peer advanced `…Sil st → …Head st`),
-- `refl`-defeq to `decNodeX` (`bundleA ≡ bundleG lo hi`).  `rewrite` on the peel
-- equalities collapses the target; the driven-peer target eq is matched `refl`.
------------------------------------------------------------------------

-- fold a link-AB bundle inversion into node A's successor
finishA-L : (na : SN.NodeStateA) {A′ Bd′ M1 : NetProc}
  → A′ ≡ (Bd′ ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
  → Bd′ ≡ (M1 ⦀ bundleA linkAC (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na))
  → BundleτR linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) M1
  → Σ[ na′ ∈ SN.NodeStateA ] (A′ ≡ decNodeA na′)
finishA-L na eq eqL (bcsc st _ refl) rewrite eqL =
  SN.mkNodeA (csHead st) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (bcss st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (ssHead st) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (bbfc st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (bcHead st) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (bbfs st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (bsHead st) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (btsc st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tcHead st) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (btss st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tsHead st) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (bkac st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kcHead st) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (bkas st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (ksHead st) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (blnc st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lncHead st) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (blns st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lnsHead st) (lfc (SN.NodeStateA.inert-AB na)) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (blfc st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfcHead st) (lfs (SN.NodeStateA.inert-AB na))) (SN.NodeStateA.inert-AC na) , eq
finishA-L na eq eqL (blfs st _ refl) rewrite eqL =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (mkInert (tsc (SN.NodeStateA.inert-AB na)) (tss (SN.NodeStateA.inert-AB na)) (kac (SN.NodeStateA.inert-AB na)) (kas (SN.NodeStateA.inert-AB na)) (lnc (SN.NodeStateA.inert-AB na)) (lns (SN.NodeStateA.inert-AB na)) (lfc (SN.NodeStateA.inert-AB na)) (lfsHead st)) (SN.NodeStateA.inert-AC na) , eq

-- fold a link-AC bundle inversion into node A's successor
finishA-R : (na : SN.NodeStateA) {A′ Bd′ M2 : NetProc}
  → A′ ≡ (Bd′ ∥⇘ apiES ⇙ (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na) ⦀ decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)))
  → Bd′ ≡ (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) ⦀ M2)
  → BundleτR linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) M2
  → Σ[ na′ ∈ SN.NodeStateA ] (A′ ≡ decNodeA na′)
finishA-R na eq eqR (bcsc st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (csHead st) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-R na eq eqR (bcss st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (ssHead st) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-R na eq eqR (bbfc st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (bcHead st) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-R na eq eqR (bbfs st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (bsHead st) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (SN.NodeStateA.inert-AC na) , eq
finishA-R na eq eqR (btsc st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tcHead st) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (btss st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tsHead st) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (bkac st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kcHead st) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (bkas st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (ksHead st) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (blnc st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lncHead st) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (blns st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lnsHead st) (lfc (SN.NodeStateA.inert-AC na)) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (blfc st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfcHead st) (lfs (SN.NodeStateA.inert-AC na))) , eq
finishA-R na eq eqR (blfs st _ refl) rewrite eqR =
  SN.mkNodeA (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.prod-AB na)
             (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.prod-AC na) (SN.NodeStateA.inert-AB na) (mkInert (tsc (SN.NodeStateA.inert-AC na)) (tss (SN.NodeStateA.inert-AC na)) (kac (SN.NodeStateA.inert-AC na)) (kas (SN.NodeStateA.inert-AC na)) (lnc (SN.NodeStateA.inert-AC na)) (lns (SN.NodeStateA.inert-AC na)) (lfc (SN.NodeStateA.inert-AC na)) (lfsHead st)) , eq

-- NODE-A τ-inversion
nodeA-τ-inv : (na : SN.NodeStateA) {A′ : NetProc}
  → decNodeA na ─[ τ ]─► A′ → Σ[ na′ ∈ SN.NodeStateA ] (A′ ≡ decNodeA na′)
nodeA-τ-inv na step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na))
           (decProd linkAC hi blkA (SN.NodeStateA.prod-AC na)) ds
...   | PEA.τL _ ps _ = ⊥-elim (decProd-no-τ linkAB hi blkA (SN.NodeStateA.prod-AB na) ps)
...   | PEA.τR _ qs _ = ⊥-elim (decProd-no-τ linkAC hi blkA (SN.NodeStateA.prod-AC na) qs)
nodeA-τ-inv na step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleA linkAB (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _ bs
...   | PEA.τL _ s1 eqL = finishA-L na eq eqL
          (bundle-τ-inv linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) s1)
...   | PEA.τR _ s2 eqR = finishA-R na eq eqR
          (bundle-τ-inv linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) s2)

-- fold a link-AB bundle inversion into node B's successor
finishB-L : (nb : SN.NodeStateB) {B′ Bd′ M1 : NetProc}
  → B′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
  → Bd′ ≡ (M1 ⦀ bundleG linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb))
  → BundleτR linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) M1
  → Σ[ nb′ ∈ SN.NodeStateB ] (B′ ≡ decNodeB nb′)
finishB-L nb eq eqL (bcsc st _ refl) rewrite eqL =
  SN.mkNodeB (csHead st) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (bcss st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (ssHead st) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (bbfc st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (bcHead st) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (bbfs st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (bsHead st)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (btsc st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tcHead st) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (btss st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tsHead st) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (bkac st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kcHead st) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (bkas st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (ksHead st) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (blnc st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lncHead st) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (blns st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lnsHead st) (lfc (SN.NodeStateB.inert-AB nb)) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (blfc st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfcHead st) (lfs (SN.NodeStateB.inert-AB nb))) (SN.NodeStateB.inert-BD nb) , eq
finishB-L nb eq eqL (blfs st _ refl) rewrite eqL =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (mkInert (tsc (SN.NodeStateB.inert-AB nb)) (tss (SN.NodeStateB.inert-AB nb)) (kac (SN.NodeStateB.inert-AB nb)) (kas (SN.NodeStateB.inert-AB nb)) (lnc (SN.NodeStateB.inert-AB nb)) (lns (SN.NodeStateB.inert-AB nb)) (lfc (SN.NodeStateB.inert-AB nb)) (lfsHead st)) (SN.NodeStateB.inert-BD nb) , eq

-- fold a link-BD bundle inversion into node B's successor
finishB-R : (nb : SN.NodeStateB) {B′ Bd′ M2 : NetProc}
  → B′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAB linkBD (SN.NodeStateB.cp-B nb))
  → Bd′ ≡ (bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) ⦀ M2)
  → BundleτR linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) M2
  → Σ[ nb′ ∈ SN.NodeStateB ] (B′ ≡ decNodeB nb′)
finishB-R nb eq eqR (bcsc st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (csHead st) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-R nb eq eqR (bcss st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (ssHead st) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-R nb eq eqR (bbfc st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (bcHead st) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-R nb eq eqR (bbfs st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (bsHead st) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (SN.NodeStateB.inert-BD nb) , eq
finishB-R nb eq eqR (btsc st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tcHead st) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (btss st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tsHead st) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (bkac st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kcHead st) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (bkas st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (ksHead st) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (blnc st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lncHead st) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (blns st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lnsHead st) (lfc (SN.NodeStateB.inert-BD nb)) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (blfc st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfcHead st) (lfs (SN.NodeStateB.inert-BD nb))) , eq
finishB-R nb eq eqR (blfs st _ refl) rewrite eqR =
  SN.mkNodeB (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb)
             (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.cp-B nb) (SN.NodeStateB.inert-AB nb) (mkInert (tsc (SN.NodeStateB.inert-BD nb)) (tss (SN.NodeStateB.inert-BD nb)) (kac (SN.NodeStateB.inert-BD nb)) (kas (SN.NodeStateB.inert-BD nb)) (lnc (SN.NodeStateB.inert-BD nb)) (lns (SN.NodeStateB.inert-BD nb)) (lfc (SN.NodeStateB.inert-BD nb)) (lfsHead st)) , eq

-- NODE-B τ-inversion
nodeB-τ-inv : (nb : SN.NodeStateB) {B′ : NetProc}
  → decNodeB nb ─[ τ ]─► B′ → Σ[ nb′ ∈ SN.NodeStateB ] (B′ ≡ decNodeB nb′)
nodeB-τ-inv nb step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _ = ⊥-elim (decCP-no-τ linkAB linkBD (SN.NodeStateB.cp-B nb) ds)
nodeB-τ-inv nb step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)) _ bs
...   | PEA.τL _ s1 eqL = finishB-L nb eq eqL
          (bundle-τ-inv linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) s1)
...   | PEA.τR _ s2 eqR = finishB-R nb eq eqR
          (bundle-τ-inv linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) s2)

-- fold a link-AC bundle inversion into node C's successor
finishC-L : (nc : SN.NodeStateC) {C′ Bd′ M1 : NetProc}
  → C′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
  → Bd′ ≡ (M1 ⦀ bundleG linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc))
  → BundleτR linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) M1
  → Σ[ nc′ ∈ SN.NodeStateC ] (C′ ≡ decNodeC nc′)
finishC-L nc eq eqL (bcsc st _ refl) rewrite eqL =
  SN.mkNodeC (csHead st) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (bcss st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (ssHead st) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (bbfc st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (bcHead st) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (bbfs st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (bsHead st)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (btsc st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tcHead st) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (btss st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tsHead st) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (bkac st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kcHead st) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (bkas st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (ksHead st) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (blnc st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lncHead st) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (blns st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lnsHead st) (lfc (SN.NodeStateC.inert-AC nc)) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (blfc st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfcHead st) (lfs (SN.NodeStateC.inert-AC nc))) (SN.NodeStateC.inert-CD nc) , eq
finishC-L nc eq eqL (blfs st _ refl) rewrite eqL =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (mkInert (tsc (SN.NodeStateC.inert-AC nc)) (tss (SN.NodeStateC.inert-AC nc)) (kac (SN.NodeStateC.inert-AC nc)) (kas (SN.NodeStateC.inert-AC nc)) (lnc (SN.NodeStateC.inert-AC nc)) (lns (SN.NodeStateC.inert-AC nc)) (lfc (SN.NodeStateC.inert-AC nc)) (lfsHead st)) (SN.NodeStateC.inert-CD nc) , eq

-- fold a link-CD bundle inversion into node C's successor
finishC-R : (nc : SN.NodeStateC) {C′ Bd′ M2 : NetProc}
  → C′ ≡ (Bd′ ∥⇘ apiES ⇙ decCP linkAC linkCD (SN.NodeStateC.cp-C nc))
  → Bd′ ≡ (bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) ⦀ M2)
  → BundleτR linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) M2
  → Σ[ nc′ ∈ SN.NodeStateC ] (C′ ≡ decNodeC nc′)
finishC-R nc eq eqR (bcsc st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (csHead st) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-R nc eq eqR (bcss st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (ssHead st) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-R nc eq eqR (bbfc st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (bcHead st) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-R nc eq eqR (bbfs st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (bsHead st) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (SN.NodeStateC.inert-CD nc) , eq
finishC-R nc eq eqR (btsc st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tcHead st) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (btss st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tsHead st) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (bkac st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kcHead st) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (bkas st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (ksHead st) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (blnc st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lncHead st) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (blns st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lnsHead st) (lfc (SN.NodeStateC.inert-CD nc)) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (blfc st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfcHead st) (lfs (SN.NodeStateC.inert-CD nc))) , eq
finishC-R nc eq eqR (blfs st _ refl) rewrite eqR =
  SN.mkNodeC (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc)
             (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.cp-C nc) (SN.NodeStateC.inert-AC nc) (mkInert (tsc (SN.NodeStateC.inert-CD nc)) (tss (SN.NodeStateC.inert-CD nc)) (kac (SN.NodeStateC.inert-CD nc)) (kas (SN.NodeStateC.inert-CD nc)) (lnc (SN.NodeStateC.inert-CD nc)) (lns (SN.NodeStateC.inert-CD nc)) (lfc (SN.NodeStateC.inert-CD nc)) (lfsHead st)) , eq

-- NODE-C τ-inversion
nodeC-τ-inv : (nc : SN.NodeStateC) {C′ : NetProc}
  → decNodeC nc ─[ τ ]─► C′ → Σ[ nc′ ∈ SN.NodeStateC ] (C′ ≡ decNodeC nc′)
nodeC-τ-inv nc step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _ = ⊥-elim (decCP-no-τ linkAC linkCD (SN.NodeStateC.cp-C nc) ds)
nodeC-τ-inv nc step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)) _ bs
...   | PEA.τL _ s1 eqL = finishC-L nc eq eqL
          (bundle-τ-inv linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) s1)
...   | PEA.τR _ s2 eqR = finishC-R nc eq eqR
          (bundle-τ-inv linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) s2)

-- fold a link-BD bundle inversion into node D's successor
finishD-L : (nd : SN.NodeStateD) {D′ Bd′ M1 : NetProc}
  → D′ ≡ (Bd′ ∥⇘ apiES ⇙ (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)))
  → Bd′ ≡ (M1 ⦀ bundleG linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd))
  → BundleτR linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) M1
  → Σ[ nd′ ∈ SN.NodeStateD ] (D′ ≡ decNodeD nd′)
finishD-L nd eq eqL (bcsc st _ refl) rewrite eqL =
  SN.mkNodeD (csHead st) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (bcss st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (ssHead st) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (bbfc st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (bcHead st) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (bbfs st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (bsHead st) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (btsc st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tcHead st) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (btss st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tsHead st) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (bkac st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kcHead st) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (bkas st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (ksHead st) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (blnc st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lncHead st) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (blns st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lnsHead st) (lfc (SN.NodeStateD.inert-BD nd)) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (blfc st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfcHead st) (lfs (SN.NodeStateD.inert-BD nd))) (SN.NodeStateD.inert-CD nd) , eq
finishD-L nd eq eqL (blfs st _ refl) rewrite eqL =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (mkInert (tsc (SN.NodeStateD.inert-BD nd)) (tss (SN.NodeStateD.inert-BD nd)) (kac (SN.NodeStateD.inert-BD nd)) (kas (SN.NodeStateD.inert-BD nd)) (lnc (SN.NodeStateD.inert-BD nd)) (lns (SN.NodeStateD.inert-BD nd)) (lfc (SN.NodeStateD.inert-BD nd)) (lfsHead st)) (SN.NodeStateD.inert-CD nd) , eq

-- fold a link-CD bundle inversion into node D's successor
finishD-R : (nd : SN.NodeStateD) {D′ Bd′ M2 : NetProc}
  → D′ ≡ (Bd′ ∥⇘ apiES ⇙ (decConsD linkBD (SN.NodeStateD.cons-BD nd) ⦀ decConsD linkCD (SN.NodeStateD.cons-CD nd)))
  → Bd′ ≡ (bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) ⦀ M2)
  → BundleτR linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) M2
  → Σ[ nd′ ∈ SN.NodeStateD ] (D′ ≡ decNodeD nd′)
finishD-R nd eq eqR (bcsc st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (csHead st) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-R nd eq eqR (bcss st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (ssHead st) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-R nd eq eqR (bbfc st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (bcHead st) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-R nd eq eqR (bbfs st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (bsHead st) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (SN.NodeStateD.inert-CD nd) , eq
finishD-R nd eq eqR (btsc st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tcHead st) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (btss st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tsHead st) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (bkac st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kcHead st) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (bkas st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (ksHead st) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (blnc st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lncHead st) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (blns st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lnsHead st) (lfc (SN.NodeStateD.inert-CD nd)) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (blfc st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfcHead st) (lfs (SN.NodeStateD.inert-CD nd))) , eq
finishD-R nd eq eqR (blfs st _ refl) rewrite eqR =
  SN.mkNodeD (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.cons-BD nd)
             (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.cons-CD nd) (SN.NodeStateD.inert-BD nd) (mkInert (tsc (SN.NodeStateD.inert-CD nd)) (tss (SN.NodeStateD.inert-CD nd)) (kac (SN.NodeStateD.inert-CD nd)) (kas (SN.NodeStateD.inert-CD nd)) (lnc (SN.NodeStateD.inert-CD nd)) (lns (SN.NodeStateD.inert-CD nd)) (lfc (SN.NodeStateD.inert-CD nd)) (lfsHead st)) , eq

-- NODE-D τ-inversion
nodeD-τ-inv : (nd : SN.NodeStateD) {D′ : NetProc}
  → decNodeD nd ─[ τ ]─► D′ → Σ[ nd′ ∈ SN.NodeStateD ] (D′ ≡ decNodeD nd′)
nodeD-τ-inv nd step with reflect-node-τ _ _ step
... | driverτ Dr′ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decConsD linkBD (SN.NodeStateD.cons-BD nd))
           (decConsD linkCD (SN.NodeStateD.cons-CD nd)) ds
...   | PEA.τL _ ps _ = ⊥-elim (decConsD-no-τ linkBD (SN.NodeStateD.cons-BD nd) ps)
...   | PEA.τR _ qs _ = ⊥-elim (decConsD-no-τ linkCD (SN.NodeStateD.cons-CD nd) qs)
nodeD-τ-inv nd step | bundleτ Bd′ bs eq
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (bundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)) _ bs
...   | PEA.τL _ s1 eqL = finishD-L nd eq eqL
          (bundle-τ-inv linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) s1)
...   | PEA.τR _ s2 eqR = finishD-R nd eq eqR
          (bundle-τ-inv linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) s2)


------------------------------------------------------------------------
-- GROUP 5a — ABSTRACT-SIDE τ-FREEDOM (the `otauB` `aτ-nds` vacuity).
--
-- The abstract nodes decode to `tableSpec` peer bundles + the SHARED τ-free
-- drivers.  Every `tableSpec T q` is either `ret tt` (`isFin T q ≡ true`) or a
-- stable `react (tMenu T q) (λ _ _ → nothing)` (`isFin T q ≡ false`) — NEVER a
-- `sil` and NEVER a react with a firing τ-branch — so it admits NO τ.  Peeling
-- the abstract node/bundle `⦀` stacks refutes every operand, mirroring the
-- concrete `nodeX-τ-inv` backbone but with all branches VACUOUS.
------------------------------------------------------------------------

-- force of a `tableSpec` peer at a TERMINAL position: `ret tt`
tsForce-ret : {Pos : Set} (T : NS.Table Pos) (q : Pos)
  → NS.Table.isFin T q ≡ true → PTree.force (tableSpec T q) ≡ ret tt
tsForce-ret T q eqf = cong (tsNode T q) eqf

-- force of a `tableSpec` peer at a NON-terminal position: a stable react whose
-- τ-branch is everywhere `nothing` (the `nxt`-table visible-offer react)
tsForce-react : {Pos : Set} (T : NS.Table Pos) (q : Pos)
  → NS.Table.isFin T q ≡ false
  → PTree.force (tableSpec T q) ≡ react (tMenu T q) (λ _ _ → nothing)
tsForce-react T q eqf = cong (tsNode T q) eqf

-- a `tableSpec` peer admits NO τ (τ-free: `ret` or stable react, per `isFin`)
tableSpec-no-τ : {Pos : Set} (T : NS.Table Pos) (q : Pos) {M : NetProc}
  → ¬ (tableSpec T q ─[ τ ]─► M)
tableSpec-no-τ T q step with NS.Table.isFin T q in eqf
... | true  = ret-no-τ   {P = tableSpec T q} (tsForce-ret T q eqf) step
... | false = react-no-τ {P = tableSpec T q} (tsForce-react T q eqf) (λ _ _ → refl) step

-- the abstract 8-peer bundle is τ-free (peel the 7 `⦀`, refute each tableSpec peer)
absBundleG-no-τ : (l : Link) (cl sv : Dir)
    (qcc : CScPos) (qcs : CSsPos) (qbc : BFcPos) (qbs : BFsPos) (ip : InertPos) {M : NetProc}
  → ¬ (absBundleG l cl sv qcc qcs qbc qbs ip ─[ τ ]─► M)
absBundleG-no-τ l cl sv qcc qcs qbc qbs ip step
  with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absKAc l cl (kac ip)) _ step
... | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
... | PEA.τR _ q1 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absKAs l sv (kas ip)) _ q1
...   | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...   | PEA.τR _ q2 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absCSc l cl qcc) _ q2
...     | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...     | PEA.τR _ q3 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absCSs l sv qcs) _ q3
...       | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...       | PEA.τR _ q4 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absBFc l cl qbc) _ q4
...         | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...         | PEA.τR _ q5 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absBFs l sv qbs) _ q5
...           | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...           | PEA.τR _ q6 _
                with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absTSc l cl (tsc ip)) _ q6
...             | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...             | PEA.τR _ q7 _
                  with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absTSs l sv (tss ip)) _ q7
...               | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...               | PEA.τR _ q8 _
                    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absLNc l cl (lnc ip)) _ q8
...                 | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...                 | PEA.τR _ q9 _
                      with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absLNs l sv (lns ip)) _ q9
...                   | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...                   | PEA.τR _ q10 _
                        with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absLFc l cl (lfc ip)) (absLFs l sv (lfs ip)) q10
...                     | PEA.τL _ ps _ = tableSpec-no-τ _ _ ps
...                     | PEA.τR _ qs _ = tableSpec-no-τ _ _ qs

-- NODE-A abstract τ-freedom (bundle refuted by `absBundleG-no-τ`, driver by `decProd-no-τ`)
absNodeA-no-τ : (na : SN.NodeStateA) {A′ : NetProc} → ¬ (absNodeA na ─[ τ ]─► A′)
absNodeA-no-τ na step with reflect-node-τ _ _ step
... | driverτ _ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decProd linkAB hi blkA (SN.NodeStateA.prod-AB na)) _ ds
...   | PEA.τL _ ps _ = decProd-no-τ linkAB hi blkA (SN.NodeStateA.prod-AB na) ps
...   | PEA.τR _ qs _ = decProd-no-τ linkAC hi blkA (SN.NodeStateA.prod-AC na) qs
absNodeA-no-τ na step | bundleτ _ bs _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na)
                       (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na)) _ bs
...   | PEA.τL _ s1 _ = absBundleG-no-τ linkAB lo hi (SN.NodeStateA.csC-AB na) (SN.NodeStateA.csS-AB na) (SN.NodeStateA.bfC-AB na) (SN.NodeStateA.bfS-AB na) (SN.NodeStateA.inert-AB na) s1
...   | PEA.τR _ s2 _ = absBundleG-no-τ linkAC lo hi (SN.NodeStateA.csC-AC na) (SN.NodeStateA.csS-AC na) (SN.NodeStateA.bfC-AC na) (SN.NodeStateA.bfS-AC na) (SN.NodeStateA.inert-AC na) s2

-- NODE-B abstract τ-freedom (single `decCP` driver)
absNodeB-no-τ : (nb : SN.NodeStateB) {B′ : NetProc} → ¬ (absNodeB nb ─[ τ ]─► B′)
absNodeB-no-τ nb step with reflect-node-τ _ _ step
... | driverτ _ ds _ = decCP-no-τ linkAB linkBD (SN.NodeStateB.cp-B nb) ds
absNodeB-no-τ nb step | bundleτ _ bs _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb)
                       (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb)) _ bs
...   | PEA.τL _ s1 _ = absBundleG-no-τ linkAB hi lo (SN.NodeStateB.csC-AB nb) (SN.NodeStateB.csS-AB nb) (SN.NodeStateB.bfC-AB nb) (SN.NodeStateB.bfS-AB nb) (SN.NodeStateB.inert-AB nb) s1
...   | PEA.τR _ s2 _ = absBundleG-no-τ linkBD lo hi (SN.NodeStateB.csC-BD nb) (SN.NodeStateB.csS-BD nb) (SN.NodeStateB.bfC-BD nb) (SN.NodeStateB.bfS-BD nb) (SN.NodeStateB.inert-BD nb) s2

-- NODE-C abstract τ-freedom (single `decCP` driver)
absNodeC-no-τ : (nc : SN.NodeStateC) {C′ : NetProc} → ¬ (absNodeC nc ─[ τ ]─► C′)
absNodeC-no-τ nc step with reflect-node-τ _ _ step
... | driverτ _ ds _ = decCP-no-τ linkAC linkCD (SN.NodeStateC.cp-C nc) ds
absNodeC-no-τ nc step | bundleτ _ bs _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc)
                       (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc)) _ bs
...   | PEA.τL _ s1 _ = absBundleG-no-τ linkAC hi lo (SN.NodeStateC.csC-AC nc) (SN.NodeStateC.csS-AC nc) (SN.NodeStateC.bfC-AC nc) (SN.NodeStateC.bfS-AC nc) (SN.NodeStateC.inert-AC nc) s1
...   | PEA.τR _ s2 _ = absBundleG-no-τ linkCD lo hi (SN.NodeStateC.csC-CD nc) (SN.NodeStateC.csS-CD nc) (SN.NodeStateC.bfC-CD nc) (SN.NodeStateC.bfS-CD nc) (SN.NodeStateC.inert-CD nc) s2

-- NODE-D abstract τ-freedom (two `decConsD` drivers)
absNodeD-no-τ : (nd : SN.NodeStateD) {D′ : NetProc} → ¬ (absNodeD nd ─[ τ ]─► D′)
absNodeD-no-τ nd step with reflect-node-τ _ _ step
... | driverτ _ ds _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (decConsD linkBD (SN.NodeStateD.cons-BD nd)) _ ds
...   | PEA.τL _ ps _ = decConsD-no-τ linkBD (SN.NodeStateD.cons-BD nd) ps
...   | PEA.τR _ qs _ = decConsD-no-τ linkCD (SN.NodeStateD.cons-CD nd) qs
absNodeD-no-τ nd step | bundleτ _ bs _
    with PEA.Par-τ-elim ∅ESa (λ _ _ → tt)
           (absBundleG linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd)
                       (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd)) _ bs
...   | PEA.τL _ s1 _ = absBundleG-no-τ linkBD hi lo (SN.NodeStateD.csC-BD nd) (SN.NodeStateD.csS-BD nd) (SN.NodeStateD.bfC-BD nd) (SN.NodeStateD.bfS-BD nd) (SN.NodeStateD.inert-BD nd) s1
...   | PEA.τR _ s2 _ = absBundleG-no-τ linkCD hi lo (SN.NodeStateD.csC-CD nd) (SN.NodeStateD.csS-CD nd) (SN.NodeStateD.bfC-CD nd) (SN.NodeStateD.bfS-CD nd) (SN.NodeStateD.inert-CD nd) s2

-- the whole abstract four-node `⦀` is τ-free (peel the 3 `⦀`, refute each node);
-- this is exactly the `aτ-nds` VACUITY the `otauB` assembly needs
absNodesOf-no-τ : (s : SysState) {M : NetProc} → ¬ (absNodesOf s ─[ τ ]─► M)
absNodesOf-no-τ s step with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absNodeA (nA s)) _ step
... | PEA.τL _ ps _ = absNodeA-no-τ (nA s) ps
... | PEA.τR _ q1 _ with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absNodeB (nB s)) _ q1
...   | PEA.τL _ ps _ = absNodeB-no-τ (nB s) ps
...   | PEA.τR _ q2 _
        with PEA.Par-τ-elim ∅ESa (λ _ _ → tt) (absNodeC (nC s)) (absNodeD (nD s)) q2
...     | PEA.τL _ ps _ = absNodeC-no-τ (nC s) ps
...     | PEA.τR _ qs _ = absNodeD-no-τ (nD s) qs

------------------------------------------------------------------------
-- GROUP 5b — ABSTRACT-SIDE ev INVERSION (the `oevB` peer leaf).
--
-- A `tableSpec T q` peer's visible offer map is `tMenu T q = tGo T ∘ nxt T q`,
-- so a visible step fires exactly one `nxt`-table edge: `nxt T q (e,a) ≡ just q′`
-- and the target is `tableSpec T q′`.  This is the table-driven positive
-- inversion the abstract driven peers (`absCSc`/`absCSs`/`absBFc`/`absBFs`) reuse.
------------------------------------------------------------------------

-- invert the `tGo`-image of a `nxt`-table lookup that yielded a `just` target
tGo-inv : {Pos : Set} (T : NS.Table Pos) (q : Pos)
    {A : Set 0ℓ} {e : Net_Api Payload A} {a : A} {M : NetProc}
  → tGo T (NS.Table.nxt T q (A , e) a) ≡ just M
  → Σ[ q′ ∈ Pos ] (NS.Table.nxt T q (A , e) a ≡ just q′) × (M ≡ tableSpec T q′)
tGo-inv T q {A} {e} {a} meq with NS.Table.nxt T q (A , e) a
... | just q′ = q′ , refl , sym (just-injective meq)
... | nothing with meq
...   | ()

-- `tableSpec` ev-inversion: a visible step of a `tableSpec` peer fires a unique
-- `nxt`-table edge, landing on that edge's target position (terminal `isFin`
-- position has no visible offer — a `ret` cannot `sVis`, refuted)
tableSpec-ev-inv : {Pos : Set} (T : NS.Table Pos) (q : Pos)
    {A : Set 0ℓ} {e : Net_Api Payload A} {a : A} {M : NetProc}
  → tableSpec T q ─[ ev (evl (evLabel A e a)) ]─► M
  → Σ[ q′ ∈ Pos ] (NS.Table.nxt T q (A , e) a ≡ just q′) × (M ≡ tableSpec T q′)
tableSpec-ev-inv T q step with NS.Table.isFin T q in eqf
... | true with ev-inv step
...   | v , τc , feq , veq with trans (sym feq) (tsForce-ret T q eqf)
...     | ()
tableSpec-ev-inv T q {A} {e} {a} step | false with ev-inv step
...   | v , τc , feq , veq with react-injective (trans (sym feq) (tsForce-react T q eqf))
...     | vEq , _ = tGo-inv T q (trans (sym (cong (λ w → w (A , e) a) vEq)) veq)

-- GAP-A forward direction: a `tableSpec` peer at a non-terminal position FIRES
-- the visible event of a `just`-valued `nxt` entry, landing on the table
-- successor (the constructor counterpart of `tableSpec-ev-inv`; the abstract
-- twin's step in the per-peer concrete↔abstract simulation)
tableSpec-ev-fwd : {Pos : Set} (T : NS.Table Pos) (q : Pos)
    {A : Set 0ℓ} {e : Net_Api Payload A} {a : A} {q′ : Pos}
  → NS.Table.isFin T q ≡ false
  → NS.Table.nxt T q (A , e) a ≡ just q′
  → tableSpec T q ─[ ev (evl (evLabel A e a)) ]─► tableSpec T q′
tableSpec-ev-fwd T q finEq nxtEq = sVis (tsForce-react T q finEq) (cong (tGo T) nxtEq)


------------------------------------------------------------------------
-- GROUP 1 (cell leaf) — copy-cell ev INVERSION.  A copy cell fires exactly
-- its phase's single visible offer: `empty ─[input l d id ? a]─► full a` and
-- `full x ─[output l d id ! x]─► draining x`; `draining` is a `sil` (no ev).
-- Mirrors `PerLink.Exp`'s proven `cp0-evL`/`cp1-evL` (identical `succV` cells),
-- at the Net-Payload alphabet `LN`.  The phase transition + target suffice for
-- the medium reconstruction (the delivered channel is fixed by the peel site).
------------------------------------------------------------------------

-- a `nothing ≡ just _` is absurd (level-polymorphic)
nothing-absurd : ∀ {a} {A : Set a} {x : A} → (nothing ≡ just x) → ⊥
nothing-absurd ()

-- the outcome of a copy-cell visible step: an input (empty→full a) or an
-- output (full x→draining x) firing, with the reconstructed target phase
data CopyEvR (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase) (M : NetProcN) : Set₁ where
  cevIn  : (x : Payload) → ph ≡ empty  → M ≡ decCopy l d id (full x)     → CopyEvR l d id ph M
  cevOut : (x : Payload) → ph ≡ full x → M ≡ decCopy l d id (draining x) → CopyEvR l d id ph M

-- `empty` (the `Copy` head) offers `input l d id ? x`, landing on `full x`
offer-empty : (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → vis-of (PTree.force (decCopy l d id empty)) (Payload , input l d id) x
    ≡ just (decCopy l d id (full x))
offer-empty l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl

-- `full x` offers `output l d id ! x`, landing on `draining x`
offer-full : (l : Link) (d : Dir) (id : IDs) (x : Payload)
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , output l d id) x
    ≡ just (decCopy l d id (draining x))
offer-full l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id
                          | ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id | ≟-yes-refl x = refl

-- read the offer map of a copy cell at the fired event (from an `sVis` step)
cell-view : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {A : Set 0ℓ} {e : Net Payload A} {a : A} {M : NetProcN}
  → decCopy l d id ph LN.─[ LN.ev (LN.evl (LN.evLabel A e a)) ]─► M
  → vis-of (PTree.force (decCopy l d id ph)) (A , e) a ≡ just M
cell-view l d id ph (LN.sVis eqf offer) = trans (cong (λ n → vis-of n _ _) eqf) offer

-- `empty` fires ONLY `input l d id` (any value), landing on `full a`; every
-- other channel / wrong instance offers `nothing` (refuted)
empty-evL : (l : Link) (d : Dir) (id : IDs)
    {A : Set 0ℓ} {e : Net Payload A} {a : A} {M : NetProcN}
  → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel A e a)) ]─► M
  → CopyEvR l d id empty M
empty-evL l d id {e = input l₀ d₀ id₀} {a} step with l₀ ≟ l | d₀ ≟ d | id₀ ≟ id
... | yes refl | yes refl | yes refl =
      cevIn a refl (just-injective (trans (sym (cell-view l d id empty step)) (offer-empty l d id a)))
... | no ¬p | _ | _ = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l₀ d₀ id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) with l₀ ≟ l
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
... | yes refl | no ¬p | _ = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l d₀ id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) rewrite ≟-yes-refl l with d₀ ≟ d
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
... | yes refl | yes refl | no ¬p = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l d id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) rewrite ≟-yes-refl l | ≟-yes-refl d with id₀ ≟ id
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
empty-evL l d id {e = output l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = sndmsg l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = rcvmsg l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = tx     l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = sndack l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = rcvack l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
empty-evL l d id {e = ack    l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)

-- `full x`'s force offers ONLY `output l d id ! x`; every other channel / wrong
-- instance / wrong value maps to `nothing` (the Output-prefix Cont guard)
full-menu-input  : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , input l₀ d₀ id₀) a′ ≡ nothing
full-menu-input  l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-sndmsg : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , sndmsg l₀ d₀ id₀) a′ ≡ nothing
full-menu-sndmsg l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-rcvmsg : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , rcvmsg l₀ d₀ id₀) a′ ≡ nothing
full-menu-rcvmsg l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-tx     : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , tx l₀ d₀ id₀) a′ ≡ nothing
full-menu-tx     l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-sndack : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : _} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (_ , sndack l₀ d₀ id₀) a′ ≡ nothing
full-menu-sndack l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-rcvack : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : _} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (_ , rcvack l₀ d₀ id₀) a′ ≡ nothing
full-menu-rcvack l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl
full-menu-ack    : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : _} {l₀ : Link} {d₀ : Dir} {id₀ : IDs}
  → vis-of (PTree.force (decCopy l d id (full x))) (_ , ack l₀ d₀ id₀) a′ ≡ nothing
full-menu-ack    l d id x rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id = refl

-- `output` at a DIFFERENT value a′ ≢ x: `full x` offers nothing
full-menu-output-val : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} → ¬ (a′ ≡ x)
  → vis-of (PTree.force (decCopy l d id (full x))) (Payload , output l d id) a′ ≡ nothing
full-menu-output-val l d id x {a′} a≢
  rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id
        | ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id with a′ ≟ x
... | yes p = ⊥-elim (a≢ p)
... | no  _ = refl

-- an `output` off the diagonal channel/instance: `full x` offers nothing
full-out-off : (l : Link) (d : Dir) (id : IDs) (x : Payload) {a′ : Payload} {l₀ : Link} {d₀ : Dir} {id₀ : IDs} {M : NetProcN}
  → ¬ ((Payload , output l₀ d₀ id₀) ≡ (Payload , output l d id))
  → decCopy l d id (full x) LN.─[ LN.ev (LN.evl (LN.evLabel Payload (output l₀ d₀ id₀) a′)) ]─► M → ⊥
full-out-off l d id x {a′} {l₀} {d₀} {id₀} ¬eq step with cell-view l d id (full x) step
... | v rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl id
      with Net-≟ (Payload , output l d id) (Payload , output l₀ d₀ id₀)
...   | no  _  = nothing-absurd v
...   | yes eq = ¬eq (sym eq)

-- `full x` fires ONLY `output l d id ! x`, landing on `draining x`
full-evL : (l : Link) (d : Dir) (id : IDs) (x : Payload)
    {A : Set 0ℓ} {e : Net Payload A} {a : A} {M : NetProcN}
  → decCopy l d id (full x) LN.─[ LN.ev (LN.evl (LN.evLabel A e a)) ]─► M
  → CopyEvR l d id (full x) M
full-evL l d id x {e = output l₀ d₀ id₀} {a} step with l₀ ≟ l | d₀ ≟ d | id₀ ≟ id | a ≟ x
... | yes refl | yes refl | yes refl | yes refl =
      cevOut x refl (just-injective (trans (sym (cell-view l d id (full x) step)) (offer-full l d id x)))
... | yes refl | yes refl | yes refl | no  a≢   =
      ⊥-elim (nothing-absurd (trans (sym (full-menu-output-val l d id x a≢)) (cell-view l d id (full x) step)))
... | no  ¬p   | _        | _        | _        = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
... | yes refl | no  ¬p   | _        | _        = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
... | yes refl | yes refl | no  ¬p   | _        = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
full-evL l d id x {e = input  l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-input  l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = sndmsg l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-sndmsg l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = rcvmsg l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-rcvmsg l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = tx     l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-tx     l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = sndack l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-sndack l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = rcvack l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-rcvack l d id x)) (cell-view l d id (full x) step)))
full-evL l d id x {e = ack    l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-ack    l d id x)) (cell-view l d id (full x) step)))

-- `draining x` is a `sil` (the drain loop-back), so it has NO visible step
draining-evL : (l : Link) (d : Dir) (id : IDs) (x : Payload)
    {A : Set 0ℓ} {e : Net Payload A} {a : A} {M : NetProcN}
  → decCopy l d id (draining x) LN.─[ LN.ev (LN.evl (LN.evLabel A e a)) ]─► M → ⊥
draining-evL l d id x (LN.sVis feq _) with trans (sym feq) (fdrain l d id x)
... | ()

-- per-cell ev inversion: a copy-cell visible step is an input (empty→full) or
-- an output (full→draining) firing, reconstructing the target phase
decCopy-ev-inv : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {A : Set 0ℓ} {e : Net Payload A} {a : A} {M : NetProcN}
  → decCopy l d id ph LN.─[ LN.ev (LN.evl (LN.evLabel A e a)) ]─► M
  → CopyEvR l d id ph M
decCopy-ev-inv l d id empty        step = empty-evL l d id step
decCopy-ev-inv l d id (full x)     step = full-evL  l d id x step
decCopy-ev-inv l d id (draining x) step = ⊥-elim (draining-evL l d id x step)

------------------------------------------------------------------------
-- GROUP 1 (channel-disjointness) — a copy cell fires ONLY its OWN (l,d,id)
-- channel.  `cell-key` extracts the fired event's channel identity (`input`
-- or `output` at exactly `(l,d,id)`); `cell-diff-noBoth` refutes the `evBoth`
-- case of the `⦀`-ev peel — two DISTINCT-key cells cannot fire the SAME event.
-- This is the one NEW non-mechanical piece the ev-lifts need (τ-side never has
-- an evBoth).  Distinct model keys `(l,d,id)` make the disjointness hold.
------------------------------------------------------------------------

-- the channel a copy-cell visible step fires: `input`/`output` at its OWN key
data CellChan (l : Link) (d : Dir) (id : IDs) : {X : Set 0ℓ} → Net Payload X → Set₁ where
  chIn  : CellChan l d id (input l d id)
  chOut : CellChan l d id (output l d id)

-- `empty` fires ONLY `input l d id` (the diagonal), refuting wrong keys/channels
cell-key-empty : (l : Link) (d : Dir) (id : IDs)
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {M : NetProcN}
  → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M → CellChan l d id e
cell-key-empty l d id {e = input l₀ d₀ id₀} {a} step with l₀ ≟ l | d₀ ≟ d | id₀ ≟ id
... | yes refl | yes refl | yes refl = chIn
... | no ¬p | _ | _ = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l₀ d₀ id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) with l₀ ≟ l
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
... | yes refl | no ¬p | _ = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l d₀ id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) rewrite ≟-yes-refl l with d₀ ≟ d
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
... | yes refl | yes refl | no ¬p = ⊥-elim (off step)
  where off : {W : NetProcN} → decCopy l d id empty LN.─[ LN.ev (LN.evl (LN.evLabel _ (input l d id₀) a)) ]─► W → ⊥
        off (LN.sVis refl offer) rewrite ≟-yes-refl l | ≟-yes-refl d with id₀ ≟ id
        ... | no _  = nothing-absurd offer
        ... | yes q = ⊥-elim (¬p q)
cell-key-empty l d id {e = output l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = sndmsg l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = rcvmsg l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = tx     l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = sndack l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = rcvack l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)
cell-key-empty l d id {e = ack    l₀ d₀ id₀} (LN.sVis refl offer) = ⊥-elim (nothing-absurd offer)

-- `full x` fires ONLY `output l d id` (the diagonal), refuting wrong keys/channels
cell-key-full : (l : Link) (d : Dir) (id : IDs) (x : Payload)
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {M : NetProcN}
  → decCopy l d id (full x) LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M → CellChan l d id e
cell-key-full l d id x {e = output l₀ d₀ id₀} {a} step with l₀ ≟ l | d₀ ≟ d | id₀ ≟ id
... | yes refl | yes refl | yes refl = chOut
... | no  ¬p   | _        | _        = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
... | yes refl | no  ¬p   | _        = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
... | yes refl | yes refl | no  ¬p   = ⊥-elim (full-out-off l d id x (λ { refl → ¬p refl }) step)
cell-key-full l d id x {e = input  l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-input  l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = sndmsg l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-sndmsg l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = rcvmsg l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-rcvmsg l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = tx     l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-tx     l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = sndack l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-sndack l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = rcvack l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-rcvack l d id x)) (cell-view l d id (full x) step)))
cell-key-full l d id x {e = ack    l₀ d₀ id₀} step = ⊥-elim (nothing-absurd (trans (sym (full-menu-ack    l d id x)) (cell-view l d id (full x) step)))

-- any copy-cell visible step fires the cell's own channel (draining has none)
cell-key : (l : Link) (d : Dir) (id : IDs) (ph : CopyPhase)
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {M : NetProcN}
  → decCopy l d id ph LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M → CellChan l d id e
cell-key l d id empty        step = cell-key-empty l d id step
cell-key l d id (full x)     step = cell-key-full  l d id x step
cell-key l d id (draining x) step = ⊥-elim (draining-evL l d id x step)

-- CHANNEL-DISJOINTNESS: two cells of the SAME link with DISTINCT `(d,id)` keys
-- cannot fire the SAME visible event (their channels are disjoint) — refutes the
-- `evBoth` case of a within-link `⦀⋆` peel.  Both `cell-key`s pin the SAME event
-- `e` to each cell's own key, forcing `(d,id) ≡ (d′,id′)`, contra the hypothesis.
cell-diff-noBoth : (l : Link) (d d′ : Dir) (id id′ : IDs) (ph ph′ : CopyPhase)
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {M M′ : NetProcN}
  → ¬ ((d , id) ≡ (d′ , id′))
  → decCopy l d  id  ph  LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M
  → decCopy l d′ id′ ph′ LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M′ → ⊥
cell-diff-noBoth l d d′ id id′ ph ph′ ¬eq s1 s2
  with cell-key l d id ph s1 | cell-key l d′ id′ ph′ s2
... | chIn  | chIn  = ¬eq refl
... | chOut | chOut = ¬eq refl

------------------------------------------------------------------------
-- GROUP 3 — DRIVER ev INVERSION.  The `decProd`/`decCons`/`decConsD`/`decCP`
-- drivers are NATIVE `Net_Api` prefix chains (no rename, no fold): each phase
-- forces to a single `Prefix`/`Output` react offering exactly ONE api event and
-- landing on the next phase.  A visible step therefore FIRES that api event and
-- advances the phase; the terminal (`ret`) phase has no visible step (refuted).
-- The producer driver `decProd` is done here (its phases are constant-tail
-- prefixes/outputs); it is REUSED by `decCP producing` and the `decConsD` tail.
------------------------------------------------------------------------

-- the Net_Api prefix/output step inversions (`⟶₀`-ev; generic in the channel)
import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload}) as PInv
open PInv using ( ⟶₀-ev-inv; Prefix-cont-fires )
-- the Net_Api prefix + output prefixes + their offer maps (the driver phases)
open Op using ( Prefix; Output; Output-cont )
open import Class.DecEq using ( DecEq )

-- a `ret`-forced tree has no visible (`evl`) step (only a `√`, ruled out here)
ret-no-ev : {R : Set} {r : R}
    {P M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → PTree.force P ≡ ret r → ¬ (P ─[ ev (evl (evLabel X e a)) ]─► M)
ret-no-ev feq (sVis feq′ _) with trans (sym feq′) feq
... | ()

-- an `Output` (`ce ! v ⟶ P`) visible step lands on its tail `P`.  `ce`/`v`/`P`
-- are IMPLICIT so the subject unifies at the PTree head; the offer-map `with`
-- is inlined HERE (where `ce`/`deqB`/`a` are variables, so `Output-cont` reduces
-- cleanly) rather than delegated — dodging the stuck-neutral unification block.
-- The `DecEq` instance is threaded EXPLICITLY (unified from the subject) to dodge
-- the ambiguous `DecEq-Header×Tip` instance search.  R-generic (⊤ producer /
-- Block₃ consumer chains both reuse it).
output-ev-inv : {R : Set} {B : Set 0ℓ} {deqB : DecEq B} {ce : Net_Api Payload B} {v : B}
    {P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
  → (Output ⦃ deqB ⦄ ce v P) ─[ ev (evl (evLabel X e a)) ]─► M → M ≡ P
output-ev-inv {R} {B} {deqB} {ce} {v} {P} {X} {e} {a} (sVis refl br)
    with Net_Api-≟ {Payload} (B , ce) (X , e)
... | no  ¬eq  = ⊥-elim (nothing-absurd br)
... | yes refl with _≟_ ⦃ deqB ⦄ a v
...   | yes _  = sym (just-injective br)
...   | no  _  = ⊥-elim (nothing-absurd br)

-- a `Prefix` (`ce ⟶ P`) visible step lands on `P x` for the fired value `x`
-- (non-`₀`: the continuation may DEPEND on the received value — the consumer
-- driver's `recvCSRollforward`/`recvBFBlock` data-carrying phases)
prefix-ev-inv : {R : Set} {A : Set 0ℓ} {ce : Net_Api Payload A}
    {P : A → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
  → (Prefix ce P) ─[ ev (evl (evLabel X e a)) ]─► M → Σ[ x ∈ A ] (M ≡ P x)
prefix-ev-inv (sVis refl br) with Prefix-cont-fires br
... | refl , x , t′≡ = x , t′≡

-- which producer phase a visible step lands on (always the successor phase)
data ProdEvR (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh) (M : NetProc) : Set₁ where
  peR : (pp′ : ProdPh) → M ≡ decProd l d blk pp′ → ProdEvR l d blk pp M

-- producer-driver ev inversion: pp0..pp6 fire their head api event and advance
-- to the next phase (pp0→pp1 … pp6→pp7); pp7 = Skip = ret has no visible step
decProd-ev-inv : (l : Link) (d : Dir) (blk : Block₃) (pp : ProdPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decProd l d blk pp ─[ ev (evl (evLabel X e a)) ]─► M → ProdEvR l d blk pp M
decProd-ev-inv l d blk pp0 step with ⟶₀-ev-inv step
... | _ , _ , refl = peR pp1 refl
decProd-ev-inv l d blk pp1 step with ⟶₀-ev-inv step
... | _ , _ , refl = peR pp2 refl
decProd-ev-inv l d blk pp2 step = peR pp3 (output-ev-inv step)
decProd-ev-inv l d blk pp3 step with ⟶₀-ev-inv step
... | _ , _ , refl = peR pp4 refl
decProd-ev-inv l d blk pp4 step = peR pp5 (output-ev-inv step)
decProd-ev-inv l d blk pp5 step = peR pp6 (output-ev-inv step)
decProd-ev-inv l d blk pp6 step = peR pp7 (output-ev-inv step)
decProd-ev-inv l d blk pp7 step with ⟶₀-ev-inv step
... | _ , _ , refl = peR pp8 refl
decProd-ev-inv l d blk pp8 step with ⟶₀-ev-inv step
... | _ , _ , refl = peR pp9 refl
decProd-ev-inv l d blk pp9 step = ⊥-elim (ret-no-ev {P = decProd l d blk pp9} refl step)

-- which consumer phase (+ the block carried onward) a visible step lands on.
-- The consumer chain THREADS a block (unlike the fixed-`blkA` producer): the
-- data-carrying phases cp1 (`recvCSRollforward`) / cp3 (`recvBFBlock`) update it
-- to the received value, so the result phase carries its own block `b′`.
data ConsEvR (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
     (M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃) : Set₁ where
  ceR : (b′ : Block₃) (cp′ : ConsPh)
      → M ≡ decCons l d b′ cp′ → ConsEvR l d b cp M

-- consumer-driver ev inversion: cp0..cp5 fire their head api event and advance
-- to the next phase (cp1/cp3 rebind the block to the received value — cp1 via
-- the named `consume-k` pattern-lambda that the refactor made shared, cp3 via
-- the inner `λ b′ →`); cp6 = `Ret b` has no visible step (refuted).
decCons-ev-inv : (l : Link) (d : Dir) (b : Block₃) (cp : ConsPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃}
  → decCons l d b cp ─[ ev (evl (evLabel X e a)) ]─► M → ConsEvR l d b cp M
decCons-ev-inv l d b cp0 step with ⟶₀-ev-inv step
... | _ , _ , refl = ceR b cp1 refl
decCons-ev-inv l d b cp1 step with prefix-ev-inv step
... | (header b′ , _) , refl = ceR b′ cp2 refl
decCons-ev-inv l d b cp2 step = ceR b cp3 (output-ev-inv step)
decCons-ev-inv l d b cp3 step with prefix-ev-inv step
... | b′ , refl = ceR b′ cp4 refl
decCons-ev-inv l d b cp4 step = ceR b cp5 (output-ev-inv step)
decCons-ev-inv l d b cp5 step with ⟶₀-ev-inv step
... | _ , _ , refl = ceR b cp6 refl
decCons-ev-inv l d b cp6 step = ⊥-elim (ret-no-ev {P = decCons l d b cp6} refl step)

------------------------------------------------------------------------
-- decConsD / decCP ev INVERSION (G3 handoff).  The node-D consume driver
-- `decConsD = decCons … >> Skip` and the relay driver `decCP consuming =
-- decCons … >>= produce` lift `decCons-ev-inv` through a bind; the relay's
-- `consuming cp6 → producing pp0` handoff uses the definitional `Ret >>= k`
-- reduction; `producing`/the produce leg REUSE `decProd-ev-inv`.
------------------------------------------------------------------------

-- single-step bind ev inversion: a visible step of `P >>= k`, when `P` forces
-- to a react node, FIRES `P`'s event and lands on `t >>= k` for `P`'s
-- derivative `t` (mirrors `bind-elim-aux`'s react-ev case: `bindV-elim` +
-- `react-injective` transport of the fired offer entry)
bind-ev-inv : {S : Set} (k : Block₃ → PTree (Net_Api Payload) (ExtI (Net_Api Payload)) S)
    (P : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃)
    {vp : (at : AnyTypes (Net_Api Payload)) → ContinueType at (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃))}
    {τcp : (i : AnyTypes (ExtI (Net_Api Payload))) → ContinueType i (Maybe (PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃))}
  → PTree.force P ≡ react vp τcp
  → {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
    {M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) S}
  → (P >>= k) ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ t ∈ PTree (Net_Api Payload) (ExtI (Net_Api Payload)) Block₃ ]
      (P ─[ ev (evl (evLabel X e a)) ]─► t) × (M ≡ t >>= k)
bind-ev-inv k P {vp} {τcp} feq (sVis {at = at} {a = a} eqf br)
  with bindV-elim k (react vp τcp)
         (subst (λ g → g at a ≡ just _)
                (sym (proj₁ (react-injective (trans (sym (fBind-react k P feq)) eqf)))) br)
... | t , vv , refl = t , sVis feq vv , refl

-- which phase (+ carried block) a visible step of node-D's `decCons … >> Skip`
-- lands on (the carried block `b′` threads through as in `ConsEvR`)
data ConsDEvR (l : Link) (cph : ConsDPh) (M : NetProc) : Set₁ where
  cdR : (b′ : Block₃) (cp′ : ConsPh) → M ≡ decConsD l (consD b′ cp′) → ConsDEvR l cph M

-- node-D consume-driver ev inversion: fire the consume event through the
-- `>> Skip` bind (`bind-ev-inv`), advance the phase (`decCons-ev-inv`); cp6 =
-- `Ret blkA >> Skip` forces (via `>>=`-on-ret) to `Skip = ret`, so no visible step.
decConsD-ev-inv : (l : Link) (cph : ConsDPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decConsD l cph ─[ ev (evl (evLabel X e a)) ]─► M → ConsDEvR l cph M
decConsD-ev-inv l (consD b cp0) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp0) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp0 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp1) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp1) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp1 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp2) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp2) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp2 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp3) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp3) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp3 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp4) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp4) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp4 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp5) step with bind-ev-inv (λ _ → Op.Skip) (decCons l hi b cp5) refl step
... | _ , sc , refl with decCons-ev-inv l hi b cp5 sc
...   | ceR b′ cp′ refl = cdR b′ cp′ refl
decConsD-ev-inv l (consD b cp6) step = ⊥-elim (ret-no-ev {P = decConsD l (consD b cp6)} refl step)

-- which phase a visible step of a relay `consume l₁ hi >>= produce l₂ hi` lands
-- on: still consuming (+ carried block), or — past the bind-ret boundary —
-- producing (the produce leg, reusing `decProd`).
data CPEvR (l₁ l₂ : Link) (ph : CPPh) (M : NetProc) : Set₁ where
  cpR-cons : (b′ : Block₃) (cp′ : ConsPh)
           → M ≡ decCP l₁ l₂ (consuming b′ cp′) → CPEvR l₁ l₂ ph M
  cpR-prod : (b′ : Block₃) (pp′ : ProdPh)
           → M ≡ decCP l₁ l₂ (producing b′ pp′) → CPEvR l₁ l₂ ph M

-- transport a step across a force-equality (a step only inspects `PTree.force`);
-- used to view the bind-ret boundary `decCP … (consuming cp6)` as `decProd … pp0`
-- (they are force-equal by the `Ret blkA >>= k` reduction, but not convertible as
-- neutral copattern terms without unfolding the `with` head)
step-fcong : {R : Set} {P Q M : PTree (Net_Api Payload) (ExtI (Net_Api Payload)) R}
    {l : Label R}
  → PTree.force P ≡ PTree.force Q → P ─[ l ]─► M → Q ─[ l ]─► M
step-fcong fe (sRet feq)    = sRet (trans (sym fe) feq)
step-fcong fe (sSil feq)    = sSil (trans (sym fe) feq)
step-fcong fe (sVis feq br) = sVis (trans (sym fe) feq) br
step-fcong fe (sTau feq br) = sTau (trans (sym fe) feq) br

-- relay-driver ev inversion: consuming cp0..cp5 advance the consume phase (via
-- the `>>= produce` bind); consuming cp6 = `Ret blkA >>= produce l₂ hi` reduces
-- (via `>>=`-on-ret) to `decProd l₂ hi pp0`, so the fired event is produce's
-- first (the `consuming cp6 → producing pp0` handoff, made explicit through
-- `step-fcong refl`); producing pp delegates to `decProd-ev-inv`.
decCP-ev-inv : (l₁ l₂ : Link) (ph : CPPh)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCP l₁ l₂ ph ─[ ev (evl (evLabel X e a)) ]─► M → CPEvR l₁ l₂ ph M
decCP-ev-inv l₁ l₂ (consuming b cp0) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp0) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp0 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp1) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp1) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp1 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp2) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp2) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp2 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp3) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp3) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp3 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp4) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp4) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp4 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp5) step
  with bind-ev-inv (λ b → produce l₂ hi b) (decCons l₁ hi b cp5) refl step
... | _ , sc , refl with decCons-ev-inv l₁ hi b cp5 sc
...   | ceR b′ cp′ refl = cpR-cons b′ cp′ refl
decCP-ev-inv l₁ l₂ (consuming b cp6) step
  with decProd-ev-inv l₂ hi b pp0 (step-fcong refl step)
... | peR pp′ refl = cpR-prod b pp′ refl
decCP-ev-inv l₁ l₂ (producing b pp) step with decProd-ev-inv l₂ hi b pp step
... | peR pp′ refl = cpR-prod b pp′ refl

------------------------------------------------------------------------
-- GROUP 1 (medium-ev lift) — mirror the committed `medium-τ-inv` chain, but
-- for VISIBLE io steps.  A hidden io (`input`/`output`, `break ∉ ioES`) of the
-- medium is one cell firing: `⦀Fin-ev-inv` peels the four-link interleave to
-- one link (evBoth refuted by link-level channel disjointness), `△-ev-elim`
-- discards the `break` operand (io ≠ break), `renameMap-ev-reflect` reflects to
-- the source fold, `⦀⋆-ev-inv` peels one cell (evBoth refuted by the committed
-- `cell-diff-noBoth`), and `decCopy-ev-inv` flips that cell (empty→full input /
-- full→draining output).  The peels are noBoth-parameterised (generic); the
-- disjointness witnesses are supplied concretely.
------------------------------------------------------------------------

-- a native Net-Payload `ret` has no visible step (the `⦀⋆ []` = `Skip` tail)
retN-no-ev : {Rr : Set} {r : Rr} {P M : PTree (Net Payload) (ExtI (Net Payload)) Rr}
    {X : Set 0ℓ} {e : Net Payload X} {a : X}
  → PTree.force P ≡ ret r → ¬ (P LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M)
retN-no-ev feq (LN.sVis feq′ _) with trans (sym feq′) feq
... | ()

-- `⦀⋆` list ev-peel (generic, noBoth-parameterised): a visible step of `⦀⋆ Ps`
-- fires exactly one cell's offer (evSync impossible under `∅ES`; evBoth refuted
-- by the `noBoth` disjointness), returning position + operand step + updated fold
⦀⋆-ev-inv : (Ps : List NetProcN)
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {M : NetProcN}
  → ((i j : Fin (length Ps)) → i ≢ j → {Mi Mj : NetProcN}
       → lookup Ps i LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mi
       → lookup Ps j LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mj → ⊥)
  → ⦀⋆ Ps LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M
  → Σ[ k ∈ Fin (length Ps) ] Σ[ Mk ∈ NetProcN ]
       (lookup Ps k LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mk)
       × (M ≡ ⦀⋆ (updateAt Ps k (λ _ → Mk)))
⦀⋆-ev-inv []       nb step = ⊥-elim (retN-no-ev {P = Skip} refl step)
⦀⋆-ev-inv (P ∷ Ps) nb step with PEN.Par-ev-elim ∅ES (λ _ _ → tt) P (⦀⋆ Ps) step
... | PEN.evSync mem _ _ = ⊥-elim mem
... | PEN.evL _ ps = fzero , _ , ps , refl
... | PEN.evR _ qs
      with ⦀⋆-ev-inv Ps (λ i j i≢j → nb (fsuc i) (fsuc j) (λ p → i≢j (suc-injective p))) qs
...   | k , Mk , lstep , meq = fsuc k , Mk , lstep , cong (P OpN.⦀_) meq
⦀⋆-ev-inv (P ∷ Ps) nb step | PEN.evBoth _ ps qs
      with ⦀⋆-ev-inv Ps (λ i j i≢j → nb (fsuc i) (fsuc j) (λ p → i≢j (suc-injective p))) qs
...   | k , _ , lstep , _ = ⊥-elim (nb fzero (fsuc k) (λ ()) ps lstep)

-- `⦀Fin` link ev-peel (generic, noBoth-parameterised): a visible step of
-- `⦀Fin n f` fires one link's offer (evSync impossible; evBoth refuted by the
-- `noBoth` link disjointness); mirrors `⦀Fin-τ-inv`
⦀Fin-ev-inv : (n : ℕ) (f : Fin n → NetProc)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ((i j : Fin n) → i ≢ j → {Mi Mj : NetProc}
       → f i ─[ ev (evl (evLabel X e a)) ]─► Mi
       → f j ─[ ev (evl (evLabel X e a)) ]─► Mj → ⊥)
  → ⦀Fin n f ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ i ∈ Fin n ] Σ[ Mi ∈ NetProc ]
       (f i ─[ ev (evl (evLabel X e a)) ]─► Mi) × (M ≡ ⦀Fin n (finUpd f i Mi))
⦀Fin-ev-inv zero f nb step = ⊥-elim (ret-no-ev {P = ⦀Fin zero f} refl step)
⦀Fin-ev-inv (suc n) f nb step
    with PEA.Par-ev-elim ∅ESa (λ _ _ → tt) (f fzero) (⦀Fin n (λ i → f (fsuc i))) step
... | PEA.evSync mem _ _ = ⊥-elim mem
... | PEA.evL _ ps = fzero , _ , ps , refl
... | PEA.evR _ qs
      with ⦀Fin-ev-inv n (λ i → f (fsuc i))
             (λ i j i≢j → nb (fsuc i) (fsuc j) (λ p → i≢j (suc-injective p))) qs
...   | i , Mi , istep , meq = fsuc i , Mi , istep , cong (f fzero ⦀_) meq
⦀Fin-ev-inv (suc n) f nb step | PEA.evBoth _ ps qs
      with ⦀Fin-ev-inv n (λ i → f (fsuc i))
             (λ i j i≢j → nb (fsuc i) (fsuc j) (λ p → i≢j (suc-injective p))) qs
...   | i , _ , istep , _ = ⊥-elim (nb fzero (fsuc i) (λ ()) ps istep)

-- the link component a source copy-fold visible step fires: `input`/`output`
-- at exactly link `l` (all cells of the link share `l`)
data CellChanL (l : Link) : {X : Set 0ℓ} → Net Payload X → Set₁ where
  clIn  : {d : Dir} {id : IDs} → CellChanL l (input l d id)
  clOut : {d : Dir} {id : IDs} → CellChanL l (output l d id)

-- a cell's own channel identity lifts to the link's channel identity
cellChan→L : (l : Link) (d : Dir) (id : IDs) {X : Set 0ℓ} {e : Net Payload X}
  → CellChan l d id e → CellChanL l e
cellChan→L l d id chIn  = clIn
cellChan→L l d id chOut = clOut

-- `fold-key`: any visible step of a copy fold `⦀⋆ (map cf cfg)` fires a channel
-- at link `l` (cf is passed as a variable so the recursion keeps ONE cell fn;
-- `cfk` extracts each cell's link channel).  evSync impossible; evL/evBoth read
-- the head cell, evR recurses
fold-key : (l : Link) (cf : Dir × IDs → NetProcN)
    (cfk : (di : Dir × IDs) {X : Set 0ℓ} {e : Net Payload X} {a : X} {M : NetProcN}
           → cf di LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► M → CellChanL l e)
    (cfg : List (Dir × IDs))
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {P′ : NetProcN}
  → ⦀⋆ (map cf cfg) LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► P′
  → CellChanL l e
fold-key l cf cfk []        step = ⊥-elim (retN-no-ev {P = Skip} refl step)
fold-key l cf cfk (di ∷ tl) step
    with PEN.Par-ev-elim ∅ES (λ _ _ → tt) (cf di) (⦀⋆ (map cf tl)) step
... | PEN.evSync mem _ _ = ⊥-elim mem
... | PEN.evL _ ps       = cfk di ps
... | PEN.evR _ qs       = fold-key l cf cfk tl qs
... | PEN.evBoth _ ps _  = cfk di ps

-- the Net_Api link component a broken/unbroken link fires under an io step
data ApiLinkChan (l : Link) : {X : Set 0ℓ} → Net_Api Payload X → Set₁ where
  alIn  : {d : Dir} {id : IDs} → ApiLinkChan l (input l d id)
  alOut : {d : Dir} {id : IDs} → ApiLinkChan l (output l d id)

-- two links firing the SAME io event must be the same link (the event's link
-- component is pinned by each; `input`/`output` cross-cases are index-impossible)
apiLinkChan-inj : {X : Set 0ℓ} {e : Net_Api Payload X} (l l′ : Link)
  → ApiLinkChan l e → ApiLinkChan l′ e → l ≡ l′
apiLinkChan-inj l l′ alIn  alIn  = refl
apiLinkChan-inj l l′ alOut alOut = refl

-- LINK-level channel key: an io step of a link fires an `input`/`output` at
-- exactly that link `l`.  Broken (`Skip = ret`) has no visible step; unbroken
-- peels `△` (break refuses io), reflects the rename (recovering the ι-preimage),
-- and reads the source fold's channel — pinning the link component to `l`
link-io-chan : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → decLink l ph b ─[ ev (evl (evLabel X e a)) ]─► M
  → ApiLinkChan l e
link-io-chan l ph true iomem step = ⊥-elim (ret-no-ev {P = decLink l ph true} refl step)
link-io-chan l ph false {e = input l₂ d₂ id₂} iomem step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (MedNO.force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , _
        with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , _
          with just-injective iota
...       | refl
            with fold-key l (λ { (d , id) → decCopy l d id (ph d id) })
                          (λ { (d , id) s → cellChan→L l d id (cell-key l d id (ph d id) s) })
                          (linkConfig l) srcStep
...         | clIn = alIn
link-io-chan l ph false {e = output l₂ d₂ id₂} iomem step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (MedNO.force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , _
        with MedNO.renameMap-ev-reflect-ι leftStep
...     | e₁ , Q′ , iota , srcStep , _
          with just-injective iota
...       | refl
            with fold-key l (λ { (d , id) → decCopy l d id (ph d id) })
                          (λ { (d , id) s → cellChan→L l d id (cell-key l d id (ph d id) s) })
                          (linkConfig l) srcStep
...         | clOut = alOut
link-io-chan l ph false {e = sndmsg l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = rcvmsg l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = tx     l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = sndack l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = rcvack l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = ack    l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = done   l₀ d₀ id₀} iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiCS  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiBF  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiTS  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiKA  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiLN  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = apiLF  l₀ d₀ m}   iomem step = ⊥-elim iomem
link-io-chan l ph false {e = break  l₀}        iomem step = ⊥-elim iomem

-- LINK DISJOINTNESS (the `⦀Fin`-ev evBoth refutation): distinct links cannot
-- fire the SAME io event (their io channels carry distinct link components)
link-io-diff : (m : MedState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → ioES .mem (X , e) a
  → (i j : Link) → i ≢ j → {Mi Mj : NetProc}
  → decLink i (phase m i) (broken m i) ─[ ev (evl (evLabel X e a)) ]─► Mi
  → decLink j (phase m j) (broken m j) ─[ ev (evl (evLabel X e a)) ]─► Mj → ⊥
link-io-diff m iomem i j i≢j si sj =
  i≢j (apiLinkChan-inj i j (link-io-chan i (phase m i) (broken m i) iomem si)
                           (link-io-chan j (phase m j) (broken m j) iomem sj))

-- CELL DISJOINTNESS (the `⦀⋆`-ev evBoth refutation for a link's cell list):
-- distinct cell positions of the concrete `uniformCfg` fold cannot fire the
-- SAME event (distinct `(d,id)` keys ⇒ disjoint channels).  64 concrete cases:
-- diagonal absurd by `i≢j refl`, off-diagonal via the committed `cell-diff-noBoth`.
cell-noBoth : (l : Link) (ph : Dir → IDs → CopyPhase)
    {X : Set 0ℓ} {e : Net Payload X} {a : X}
    (i j : Fin (length (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))))
  → i ≢ j → {Mi Mj : NetProcN}
  → lookup (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) i LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mi
  → lookup (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) j LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mj → ⊥
cell-noBoth l ph fzero fzero i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph fzero (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_KeepAlive (ph lo N2N_KeepAlive) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l lo lo N2N_KeepAlive N2N_ChainSync (ph lo N2N_KeepAlive) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_ChainSync (ph lo N2N_KeepAlive) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l lo lo N2N_KeepAlive N2N_BlockFetch (ph lo N2N_KeepAlive) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_BlockFetch (ph lo N2N_KeepAlive) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_KeepAlive N2N_TxSubmission (ph lo N2N_KeepAlive) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_TxSubmission (ph lo N2N_KeepAlive) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_KeepAlive (ph hi N2N_KeepAlive) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc fzero) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_ChainSync (ph hi N2N_KeepAlive) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l hi hi N2N_KeepAlive N2N_ChainSync (ph hi N2N_KeepAlive) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_BlockFetch (ph hi N2N_KeepAlive) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_KeepAlive N2N_BlockFetch (ph hi N2N_KeepAlive) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_TxSubmission (ph hi N2N_KeepAlive) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_KeepAlive N2N_TxSubmission (ph hi N2N_KeepAlive) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) fzero i≢j si sj = cell-diff-noBoth l lo lo N2N_ChainSync N2N_KeepAlive (ph lo N2N_ChainSync) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_KeepAlive (ph lo N2N_ChainSync) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_ChainSync (ph lo N2N_ChainSync) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l lo lo N2N_ChainSync N2N_BlockFetch (ph lo N2N_ChainSync) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_BlockFetch (ph lo N2N_ChainSync) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_ChainSync N2N_TxSubmission (ph lo N2N_ChainSync) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_TxSubmission (ph lo N2N_ChainSync) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_KeepAlive (ph hi N2N_ChainSync) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l hi hi N2N_ChainSync N2N_KeepAlive (ph hi N2N_ChainSync) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_ChainSync (ph hi N2N_ChainSync) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_BlockFetch (ph hi N2N_ChainSync) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_ChainSync N2N_BlockFetch (ph hi N2N_ChainSync) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_TxSubmission (ph hi N2N_ChainSync) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_ChainSync N2N_TxSubmission (ph hi N2N_ChainSync) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) fzero i≢j si sj = cell-diff-noBoth l lo lo N2N_BlockFetch N2N_KeepAlive (ph lo N2N_BlockFetch) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_KeepAlive (ph lo N2N_BlockFetch) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l lo lo N2N_BlockFetch N2N_ChainSync (ph lo N2N_BlockFetch) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_ChainSync (ph lo N2N_BlockFetch) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_BlockFetch (ph lo N2N_BlockFetch) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_BlockFetch N2N_TxSubmission (ph lo N2N_BlockFetch) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_TxSubmission (ph lo N2N_BlockFetch) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_KeepAlive (ph hi N2N_BlockFetch) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l hi hi N2N_BlockFetch N2N_KeepAlive (ph hi N2N_BlockFetch) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_ChainSync (ph hi N2N_BlockFetch) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l hi hi N2N_BlockFetch N2N_ChainSync (ph hi N2N_BlockFetch) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_BlockFetch (ph hi N2N_BlockFetch) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_TxSubmission (ph hi N2N_BlockFetch) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_BlockFetch N2N_TxSubmission (ph hi N2N_BlockFetch) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) fzero i≢j si sj = cell-diff-noBoth l lo lo N2N_TxSubmission N2N_KeepAlive (ph lo N2N_TxSubmission) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_KeepAlive (ph lo N2N_TxSubmission) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l lo lo N2N_TxSubmission N2N_ChainSync (ph lo N2N_TxSubmission) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_ChainSync (ph lo N2N_TxSubmission) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l lo lo N2N_TxSubmission N2N_BlockFetch (ph lo N2N_TxSubmission) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_BlockFetch (ph lo N2N_TxSubmission) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_TxSubmission (ph lo N2N_TxSubmission) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_KeepAlive (ph hi N2N_TxSubmission) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l hi hi N2N_TxSubmission N2N_KeepAlive (ph hi N2N_TxSubmission) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_ChainSync (ph hi N2N_TxSubmission) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l hi hi N2N_TxSubmission N2N_ChainSync (ph hi N2N_TxSubmission) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_BlockFetch (ph hi N2N_TxSubmission) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_TxSubmission N2N_BlockFetch (ph hi N2N_TxSubmission) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_TxSubmission (ph hi N2N_TxSubmission) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_KeepAlive N2N_LeiosNotify (ph lo N2N_KeepAlive) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_LeiosNotify (ph lo N2N_KeepAlive) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_KeepAlive N2N_LeiosFetch (ph lo N2N_KeepAlive) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph fzero (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_KeepAlive N2N_LeiosFetch (ph lo N2N_KeepAlive) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_LeiosNotify (ph hi N2N_KeepAlive) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_KeepAlive N2N_LeiosNotify (ph hi N2N_KeepAlive) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_KeepAlive N2N_LeiosFetch (ph hi N2N_KeepAlive) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_KeepAlive N2N_LeiosFetch (ph hi N2N_KeepAlive) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_ChainSync N2N_LeiosNotify (ph lo N2N_ChainSync) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_LeiosNotify (ph lo N2N_ChainSync) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_ChainSync N2N_LeiosFetch (ph lo N2N_ChainSync) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_ChainSync N2N_LeiosFetch (ph lo N2N_ChainSync) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_LeiosNotify (ph hi N2N_ChainSync) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_ChainSync N2N_LeiosNotify (ph hi N2N_ChainSync) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_ChainSync N2N_LeiosFetch (ph hi N2N_ChainSync) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_ChainSync N2N_LeiosFetch (ph hi N2N_ChainSync) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_BlockFetch N2N_LeiosNotify (ph lo N2N_BlockFetch) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_LeiosNotify (ph lo N2N_BlockFetch) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_BlockFetch N2N_LeiosFetch (ph lo N2N_BlockFetch) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_BlockFetch N2N_LeiosFetch (ph lo N2N_BlockFetch) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_LeiosNotify (ph hi N2N_BlockFetch) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_BlockFetch N2N_LeiosNotify (ph hi N2N_BlockFetch) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_BlockFetch N2N_LeiosFetch (ph hi N2N_BlockFetch) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_BlockFetch N2N_LeiosFetch (ph hi N2N_BlockFetch) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_TxSubmission N2N_LeiosNotify (ph lo N2N_TxSubmission) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_LeiosNotify (ph lo N2N_TxSubmission) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_TxSubmission N2N_LeiosFetch (ph lo N2N_TxSubmission) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_TxSubmission N2N_LeiosFetch (ph lo N2N_TxSubmission) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_LeiosNotify (ph hi N2N_TxSubmission) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_TxSubmission N2N_LeiosNotify (ph hi N2N_TxSubmission) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_TxSubmission N2N_LeiosFetch (ph hi N2N_TxSubmission) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_TxSubmission N2N_LeiosFetch (ph hi N2N_TxSubmission) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) fzero i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosNotify N2N_KeepAlive (ph lo N2N_LeiosNotify) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_KeepAlive (ph lo N2N_LeiosNotify) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosNotify N2N_ChainSync (ph lo N2N_LeiosNotify) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_ChainSync (ph lo N2N_LeiosNotify) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosNotify N2N_BlockFetch (ph lo N2N_LeiosNotify) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_BlockFetch (ph lo N2N_LeiosNotify) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosNotify N2N_TxSubmission (ph lo N2N_LeiosNotify) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_TxSubmission (ph lo N2N_LeiosNotify) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_LeiosNotify (ph lo N2N_LeiosNotify) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosNotify N2N_LeiosFetch (ph lo N2N_LeiosNotify) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosNotify N2N_LeiosFetch (ph lo N2N_LeiosNotify) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_KeepAlive (ph hi N2N_LeiosNotify) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosNotify N2N_KeepAlive (ph hi N2N_LeiosNotify) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_ChainSync (ph hi N2N_LeiosNotify) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosNotify N2N_ChainSync (ph hi N2N_LeiosNotify) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_BlockFetch (ph hi N2N_LeiosNotify) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosNotify N2N_BlockFetch (ph hi N2N_LeiosNotify) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_TxSubmission (ph hi N2N_LeiosNotify) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosNotify N2N_TxSubmission (ph hi N2N_LeiosNotify) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_LeiosNotify (ph hi N2N_LeiosNotify) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosNotify N2N_LeiosFetch (ph hi N2N_LeiosNotify) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosNotify N2N_LeiosFetch (ph hi N2N_LeiosNotify) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) fzero i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosFetch N2N_KeepAlive (ph lo N2N_LeiosFetch) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_KeepAlive (ph lo N2N_LeiosFetch) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosFetch N2N_ChainSync (ph lo N2N_LeiosFetch) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_ChainSync (ph lo N2N_LeiosFetch) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosFetch N2N_BlockFetch (ph lo N2N_LeiosFetch) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_BlockFetch (ph lo N2N_LeiosFetch) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosFetch N2N_TxSubmission (ph lo N2N_LeiosFetch) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_TxSubmission (ph lo N2N_LeiosFetch) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l lo lo N2N_LeiosFetch N2N_LeiosNotify (ph lo N2N_LeiosFetch) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_LeiosNotify (ph lo N2N_LeiosFetch) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = ⊥-elim (i≢j refl)
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = cell-diff-noBoth l lo hi N2N_LeiosFetch N2N_LeiosFetch (ph lo N2N_LeiosFetch) (ph hi N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) fzero i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_KeepAlive (ph hi N2N_LeiosFetch) (ph lo N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc fzero) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosFetch N2N_KeepAlive (ph hi N2N_LeiosFetch) (ph hi N2N_KeepAlive) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc fzero)) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_ChainSync (ph hi N2N_LeiosFetch) (ph lo N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc fzero))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosFetch N2N_ChainSync (ph hi N2N_LeiosFetch) (ph hi N2N_ChainSync) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_BlockFetch (ph hi N2N_LeiosFetch) (ph lo N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosFetch N2N_BlockFetch (ph hi N2N_LeiosFetch) (ph hi N2N_BlockFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_TxSubmission (ph hi N2N_LeiosFetch) (ph lo N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosFetch N2N_TxSubmission (ph hi N2N_LeiosFetch) (ph hi N2N_TxSubmission) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_LeiosNotify (ph hi N2N_LeiosFetch) (ph lo N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) i≢j si sj = cell-diff-noBoth l hi hi N2N_LeiosFetch N2N_LeiosNotify (ph hi N2N_LeiosFetch) (ph hi N2N_LeiosNotify) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) i≢j si sj = cell-diff-noBoth l hi lo N2N_LeiosFetch N2N_LeiosFetch (ph hi N2N_LeiosFetch) (ph lo N2N_LeiosFetch) (λ ()) si sj
cell-noBoth l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) i≢j si sj = ⊥-elim (i≢j refl)

-- set one cell `(d₀,id₀)` of a link's phase function to a new phase `np`
setCell : (Dir → IDs → CopyPhase) → Dir → IDs → CopyPhase → (Dir → IDs → CopyPhase)
setCell g d₀ id₀ np d id with d ≟ d₀ | id ≟ id₀
... | no  _ | _     = g d id
... | yes _ | no  _ = g d id
... | yes _ | yes _ = np

-- per-position cell FLIP: at concrete cell index `k` the cell `(dₖ,idₖ)` fired
-- (empty→full x input / full x→draining x output); the positional `updateAt`
-- equals the key-set `map` (distinct keys ⇒ each cell equality holds by `refl`)
cellFlipEv : (l : Link) (ph : Dir → IDs → CopyPhase)
    (k : Fin (length (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))))
    {X : Set 0ℓ} {e : Net Payload X} {a : X} {Mk : NetProcN}
  → lookup (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k LN.─[ LN.ev (LN.evl (LN.evLabel X e a)) ]─► Mk
  → Σ[ d₀ ∈ Dir ] Σ[ id₀ ∈ IDs ] Σ[ np ∈ CopyPhase ]
       (updateAt (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l)) k (λ _ → Mk)
          ≡ map (λ { (d , id) → decCopy l d id (setCell ph d₀ id₀ np d id) }) (linkConfig l))
cellFlipEv l ph fzero cs with decCopy-ev-inv l lo N2N_KeepAlive (ph lo N2N_KeepAlive) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_KeepAlive , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_KeepAlive , draining x , refl
cellFlipEv l ph (fsuc fzero) cs with decCopy-ev-inv l hi N2N_KeepAlive (ph hi N2N_KeepAlive) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_KeepAlive , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_KeepAlive , draining x , refl
cellFlipEv l ph (fsuc (fsuc fzero)) cs with decCopy-ev-inv l lo N2N_ChainSync (ph lo N2N_ChainSync) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_ChainSync , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_ChainSync , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc fzero))) cs with decCopy-ev-inv l hi N2N_ChainSync (ph hi N2N_ChainSync) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_ChainSync , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_ChainSync , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc fzero)))) cs with decCopy-ev-inv l lo N2N_BlockFetch (ph lo N2N_BlockFetch) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_BlockFetch , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_BlockFetch , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) cs with decCopy-ev-inv l hi N2N_BlockFetch (ph hi N2N_BlockFetch) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_BlockFetch , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_BlockFetch , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) cs with decCopy-ev-inv l lo N2N_TxSubmission (ph lo N2N_TxSubmission) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_TxSubmission , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_TxSubmission , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) cs with decCopy-ev-inv l hi N2N_TxSubmission (ph hi N2N_TxSubmission) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_TxSubmission , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_TxSubmission , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) cs with decCopy-ev-inv l lo N2N_LeiosNotify (ph lo N2N_LeiosNotify) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_LeiosNotify , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_LeiosNotify , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) cs with decCopy-ev-inv l hi N2N_LeiosNotify (ph hi N2N_LeiosNotify) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_LeiosNotify , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_LeiosNotify , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) cs with decCopy-ev-inv l lo N2N_LeiosFetch (ph lo N2N_LeiosFetch) cs
... | cevIn  x _ Mkeq rewrite Mkeq = lo , N2N_LeiosFetch , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = lo , N2N_LeiosFetch , draining x , refl
cellFlipEv l ph (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) cs with decCopy-ev-inv l hi N2N_LeiosFetch (ph hi N2N_LeiosFetch) cs
... | cevIn  x _ Mkeq rewrite Mkeq = hi , N2N_LeiosFetch , full x , refl
... | cevOut x _ Mkeq rewrite Mkeq = hi , N2N_LeiosFetch , draining x , refl

-- LINK ev-inversion: an io step of an unbroken link is one cell firing; the
-- target is the same link with that cell's phase advanced (empty→full input /
-- full→draining output).  Mirrors `decLink-τ-inv`: `△-ev-elim` (break refuses
-- io) → `renameMap-ev-reflect` → `⦀⋆-ev-inv` (evBoth via `cell-noBoth`) →
-- `cellFlipEv` (the fired cell's phase set).  Broken (`Skip`) has no visible step.
decLink-ev-inv : (l : Link) (ph : Dir → IDs → CopyPhase) (b : Bool)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → decLink l ph b ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ ph′ ∈ (Dir → IDs → CopyPhase) ] (b ≡ false) × (M ≡ decLink l ph′ false)
decLink-ev-inv l ph true iomem step = ⊥-elim (ret-no-ev {P = decLink l ph true} refl step)
decLink-ev-inv l ph false {e = input l₂ d₂ id₂} iomem step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (MedNO.force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , Meq
        with MedNO.renameMap-ev-reflect leftStep
...     | e₁ , Q′ , srcStep , P′eq
          with ⦀⋆-ev-inv (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))
                         (cell-noBoth l ph) srcStep
...       | k , Mk , cellStep , Q′eq
            with cellFlipEv l ph k cellStep
...         | d₀ , id₀ , np , listEq =
              setCell ph d₀ id₀ np , refl ,
              trans Meq
                (trans (cong (λ z → z △ (break l ⟶₀ Op.Skip)) P′eq)
                  (trans (cong (λ z → renameMap z △ (break l ⟶₀ Op.Skip)) Q′eq)
                         (cong (λ z → renameMap (⦀⋆ z) △ (break l ⟶₀ Op.Skip)) listEq)))
decLink-ev-inv l ph false {e = output l₂ d₂ id₂} iomem step
    with fold-react l ph
... | mkReactF V T feq
      with △-ev-elim (MedNO.force-renameMap-react
                       {P = ⦀⋆ (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))} feq)
                     refl refl step
...   | P′ , leftStep , Meq
        with MedNO.renameMap-ev-reflect leftStep
...     | e₁ , Q′ , srcStep , P′eq
          with ⦀⋆-ev-inv (map (λ { (d , id) → decCopy l d id (ph d id) }) (linkConfig l))
                         (cell-noBoth l ph) srcStep
...       | k , Mk , cellStep , Q′eq
            with cellFlipEv l ph k cellStep
...         | d₀ , id₀ , np , listEq =
              setCell ph d₀ id₀ np , refl ,
              trans Meq
                (trans (cong (λ z → z △ (break l ⟶₀ Op.Skip)) P′eq)
                  (trans (cong (λ z → renameMap z △ (break l ⟶₀ Op.Skip)) Q′eq)
                         (cong (λ z → renameMap (⦀⋆ z) △ (break l ⟶₀ Op.Skip)) listEq)))
decLink-ev-inv l ph false {e = sndmsg l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = rcvmsg l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = tx     l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = sndack l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = rcvack l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = ack    l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = done   l₀ d₀ id₀} iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiCS  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiBF  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiTS  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiKA  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiLN  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = apiLF  l₀ d₀ m}   iomem step = ⊥-elim iomem
decLink-ev-inv l ph false {e = break  l₀}        iomem step = ⊥-elim iomem

-- MEDIUM ev-inversion (io delivery): `⦀Fin-ev-inv` peels the four-link
-- interleave to one link `i` (evBoth refuted by `link-io-diff`); `decLink-ev-inv`
-- advances that link's fired cell.  Reconstructs the `MedState` successor via the
-- committed `phase-upd`/`recon-decMed` bridge (mirrors `medium-τ-inv`).  Scoped
-- to hidden io (`break ∉ ioES`), matching the `cτ-io` classifier that supplies it.
medium-ev-inv : (m : MedState) {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → ioES .mem (X , e) a
  → decMed m ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ m′ ∈ MedState ] (M ≡ decMed m′)
medium-ev-inv m iomem step
    with ⦀Fin-ev-inv numLinks (λ l → decLink l (phase m l) (broken m l)) (link-io-diff m iomem) step
... | i , Mi , linkStep , Meq
      with decLink-ev-inv i (phase m i) (broken m i) iomem linkStep
...   | ph′ , brEq , MiEq =
        mkMed (phase-upd (phase m) i ph′) (broken m) ,
        trans Meq
          (trans (cong (λ z → ⦀Fin numLinks
                    (finUpd (λ l → decLink l (phase m l) (broken m l)) i z))
                    (trans MiEq (cong (decLink i ph′) (sym brEq))))
                 (recon-decMed m i ph′))


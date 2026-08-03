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

module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_PeerEvIo where
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_PeerEvCSBF public

------------------------------------------------------------------------
-- G2 (io) — KeepAlive CLIENT / SERVER visible-event inversions.
-- KA carries io (`sendKA`/`receiveKA` → input/output) + api (`apiKAev`) +
-- `doneKA`.  Same infra as CS/BF (`succVK`/`step-target-KA`).  ONE asymmetry
-- vs the CS/BF twins: the client `errCookie` leaf (`kcErr1`) fires DIRECTLY to
-- a `Ret (inj₂ _)` terminal (`kcTermE1`), coarsening to the abstract `kcTermE`
-- (every other peer terminates through a state head → `kcTerm`).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode
  using ( succVK; vis-ofK; KAProc )
import Semantics.LTS {E = KA.KAEv} {I = ExtI KA.KAEv} as KAL
open import CSP.Examples.Cardano_network.Net p using
  ( sendKAMsg; sendKADone; errCookie; recvKACookie )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgKeepAlive; MsgKeepAliveResponse; MsgKADone )

-- NOTE (Cookie = ⊤ under `p`): `decCookie = λ _ _ → yes refl`, so any `cq ≟ cr`
-- is DEFINITIONALLY `yes refl`.  Hence the client's `errCookie` mismatch branch
-- (`kcErr1 cq cr ne`, `ne : ¬ (cq ≡ cr)`) is VACUOUS — `ne refl : ⊥` — and the
-- keepalive-response always routes to `kcSil stClient` (no `cq ≟ cr` split).

-- KA iter-force offer: `succVK q at a` is exactly the offered continuation
succVK-just : (q : KAProc) (at : AnyTypes KA.KAEv) (a : proj₁ at) {P′ : KAProc}
  → vis-ofK (PTree.force q) at a ≡ just P′ → succVK q at a ≡ P′
succVK-just q at a eq with vis-ofK (PTree.force q) at a
succVK-just q at a refl | just t = refl
succVK-just q at a ()   | nothing

-- KA: a visible source step lands on `succVK q (X , e) a`
succVK-inv : (q : KAProc) {X : Set 0ℓ} {e : KA.KAEv X} {a : X} {P′ : KAProc}
  → q KAL.─[ KAL.ev (KAL.evl (KAL.evLabel X e a)) ]─► P′
  → P′ ≡ succVK q (X , e) a
succVK-inv q {X} {e} {a} step with KAL.ev-inv step
... | v , τc , feq , veq =
      sym (succVK-just q (X , e) a (trans (cong (λ n → vis-ofK n (X , e) a) feq) veq))

-- KA: the fired offer entry at a KNOWN force (`refl` head / `h*` mid)
step-target-KA : (q : KAProc)
    {V : (at : AnyTypes KA.KAEv) → ContinueType at (Maybe KAProc)}
    {T : (i : AnyTypes (ExtI KA.KAEv)) → ContinueType i (Maybe KAProc)}
    {X : Set 0ℓ} {e : KA.KAEv X} {a : X} {P′ : KAProc}
  → PTree.force q ≡ react V T
  → q KAL.─[ KAL.ev (KAL.evl (KAL.evLabel X e a)) ]─► P′
  → V (X , e) a ≡ just P′
step-target-KA q {V} {T} {X} {e} {a} feq step with KAL.ev-inv step
... | v , τc , feq′ , veq with react-injective (trans (sym feq) feq′)
...   | Veq , _ = trans (cong (λ w → w (X , e) a) Veq) veq

-- a renamed Net_Api event whose ι-preimage is a KA source event is the ι-image
ιKA-inv-shape : {X : Set 0ℓ} {e₂ : Net_Api Payload X} {e₁ : KA.KAEv X}
  → ιKA⁻¹ e₂ ≡ just e₁ → e₂ ≡ ιKA e₁
ιKA-inv-shape {e₂ = input  _ _ N2N_ChainSync}    ()
ιKA-inv-shape {e₂ = input  _ _ N2N_BlockFetch}   ()
ιKA-inv-shape {e₂ = input  _ _ N2N_TxSubmission} ()
ιKA-inv-shape {e₂ = input  _ _ N2N_KeepAlive}    refl = refl
ιKA-inv-shape {e₂ = input  _ _ N2N_LeiosNotify}  ()
ιKA-inv-shape {e₂ = input  _ _ N2N_LeiosFetch}   ()
ιKA-inv-shape {e₂ = output _ _ N2N_ChainSync}    ()
ιKA-inv-shape {e₂ = output _ _ N2N_BlockFetch}   ()
ιKA-inv-shape {e₂ = output _ _ N2N_TxSubmission} ()
ιKA-inv-shape {e₂ = output _ _ N2N_KeepAlive}    refl = refl
ιKA-inv-shape {e₂ = output _ _ N2N_LeiosNotify}  ()
ιKA-inv-shape {e₂ = output _ _ N2N_LeiosFetch}   ()
ιKA-inv-shape {e₂ = done   _ _ N2N_ChainSync}    ()
ιKA-inv-shape {e₂ = done   _ _ N2N_BlockFetch}   ()
ιKA-inv-shape {e₂ = done   _ _ N2N_TxSubmission} ()
ιKA-inv-shape {e₂ = done   _ _ N2N_KeepAlive}    refl = refl
ιKA-inv-shape {e₂ = done   _ _ N2N_LeiosNotify}  ()
ιKA-inv-shape {e₂ = done   _ _ N2N_LeiosFetch}   ()
ιKA-inv-shape {e₂ = apiKA  _ _ _} refl = refl
ιKA-inv-shape {e₂ = apiCS  _ _ _} ()
ιKA-inv-shape {e₂ = apiBF  _ _ _} ()
ιKA-inv-shape {e₂ = apiTS  _ _ _} ()
ιKA-inv-shape {e₂ = apiLN  _ _ _} ()
ιKA-inv-shape {e₂ = apiLF  _ _ _} ()
ιKA-inv-shape {e₂ = sndmsg _ _ _} ()
ιKA-inv-shape {e₂ = rcvmsg _ _ _} ()
ιKA-inv-shape {e₂ = tx     _ _ _} ()
ιKA-inv-shape {e₂ = sndack _ _ _} ()
ιKA-inv-shape {e₂ = rcvack _ _ _} ()
ιKA-inv-shape {e₂ = ack    _ _ _} ()
ιKA-inv-shape {e₂ = break  _}     ()

-- package a `kaCnxt`/`kaSnxt` agreement into the abstract KA step
aKAc : (l : Link) (d : Dir) (pos pos′ : KAcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.kaCfin (coarsenKAc pos) ≡ false
  → NS.kaCnxt l d (coarsenKAc pos) (X , e) a ≡ just (coarsenKAc pos′)
  → absKAc l d pos ─[ ev (evl (evLabel X e a)) ]─► absKAc l d pos′
aKAc l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenKAc pos) finEq ceq
aKAs : (l : Link) (d : Dir) (pos pos′ : KAsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.kaSfin (coarsenKAs pos) ≡ false
  → NS.kaSnxt l d (coarsenKAs pos) (X , e) a ≡ just (coarsenKAs pos′)
  → absKAs l d pos ─[ ev (evl (evLabel X e a)) ]─► absKAs l d pos′
aKAs l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenKAs pos) finEq ceq

-- per-firing `coarsen ∘ nxt` commutations (CLIENT)
ceqKA-c-sendMsg : ∀ {c} (l : Link) (d : Dir)
  → NS.kaCnxt l d NS.kcClient (_ , apiKA l d sendKAMsg) c ≡ just (NS.kcWmsg c)
ceqKA-c-sendMsg l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqKA-c-sendDone : ∀ {a} (l : Link) (d : Dir)
  → NS.kaCnxt l d NS.kcClient (_ , apiKA l d sendKADone) a ≡ just NS.kcWdone
ceqKA-c-sendDone l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
-- keepalive-response always continues the loop (cq ≟ cr ≡ yes under Cookie = ⊤)
ceqKA-c-respEq : ∀ {t0 md ln} (l : Link) (d : Dir) (cq cr : Cookie)
  → NS.kaCnxt l d (NS.kcAwait cq) (_ , output l d N2N_KeepAlive)
      (t0 , md , ln , keepAlive (MsgKeepAliveResponse cr)) ≡ just NS.kcClient
ceqKA-c-respEq l d cq cr rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqKA-c-wmsg : (l : Link) (d : Dir) (c : Cookie)
  → NS.kaCnxt l d (NS.kcWmsg c) (_ , input l d N2N_KeepAlive)
      (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) ≡ just (NS.kcAwait c)
ceqKA-c-wmsg l d c rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) = refl
ceqKA-c-wdone : (l : Link) (d : Dir)
  → NS.kaCnxt l d NS.kcWdone (_ , input l d N2N_KeepAlive)
      (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) ≡ just NS.kcTerm
ceqKA-c-wdone l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) = refl

-- per-firing `coarsen ∘ nxt` commutations (SERVER)
ceqKA-s-recv : ∀ {t0 md ln} (l : Link) (d : Dir) (c : Cookie)
  → NS.kaSnxt l d NS.ksClient (_ , output l d N2N_KeepAlive)
      (t0 , md , ln , keepAlive (MsgKeepAlive c)) ≡ just (NS.ksRecv c)
ceqKA-s-recv l d c rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqKA-s-ddone : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.kaSnxt l d NS.ksClient (_ , output l d N2N_KeepAlive)
      (t0 , md , ln , keepAlive MsgKADone) ≡ just NS.ksDdone
ceqKA-s-ddone l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqKA-s-srecv : (l : Link) (d : Dir) (c : Cookie)
  → NS.kaSnxt l d (NS.ksRecv c) (_ , apiKA l d recvKACookie) c ≡ just (NS.ksResp c)
ceqKA-s-srecv l d c rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqKA-s-sddone : ∀ {a} (l : Link) (d : Dir)
  → NS.kaSnxt l d NS.ksDdone (_ , done l d N2N_KeepAlive) a ≡ just NS.ksTerm
ceqKA-s-sddone l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqKA-s-sresp : (l : Link) (d : Dir) (c : Cookie)
  → NS.kaSnxt l d (NS.ksResp c) (_ , input l d N2N_KeepAlive)
      (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) ≡ just NS.ksClient
ceqKA-s-sresp l d c rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl

-- receive-firing bridges (unstick the `l≟l|d≟d`(+cookie) guards of the head)
brKrespEq : (l : Link) (d : Dir) (cq cr : Cookie) (t0 : _) (md : _) (ln : _)
  → succVK (decKAc-src l d (kcHead (KA.stServer cq))) (_ , KA.receiveKA l d)
           (t0 , md , ln , keepAlive (MsgKeepAliveResponse cr)) ≡ decKAc-src l d (kcSil KA.stClient)
brKrespEq l d cq cr t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brKsRecv : (l : Link) (d : Dir) (c : Cookie) (t0 : _) (md : _) (ln : _)
  → succVK (decKAs-src l d (ksHead KA.stClient)) (_ , KA.receiveKA l d)
           (t0 , md , ln , keepAlive (MsgKeepAlive c)) ≡ decKAs-src l d (ksRecv1 c)
brKsRecv l d c t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brKsDone : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVK (decKAs-src l d (ksHead KA.stClient)) (_ , KA.receiveKA l d)
           (t0 , md , ln , keepAlive MsgKADone) ≡ decKAs-src l d ksDdone1
brKsDone l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- SOURCE-side per-position ev inversion — KeepAlive CLIENT
decKAc-src-ev-inv : (l : Link) (d : Dir) (pos : KAcPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : KAProc}
  → decKAc-src l d pos KAL.─[ KAL.ev (KAL.evl (KAL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ KAcPos ] (P′ ≡ decKAc-src l d pos′)
      × (absKAc l d pos ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► absKAc l d pos′)
-- head stClient : fires apiKAev sendKAMsg / sendKADone
decKAc-src-ev-inv l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' sendKAMsg} {a} s with step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = kcReq1 a , succVK-inv (decKAc-src l d (kcHead KA.stClient)) s , aKAc l d (kcHead KA.stClient) (kcReq1 a) refl (ceqKA-c-sendMsg l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decKAc-src-ev-inv l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' sendKADone} {a} s with step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = kcDone1 , succVK-inv (decKAc-src l d (kcHead KA.stClient)) s , aKAc l d (kcHead KA.stClient) kcDone1 refl (ceqKA-c-sendDone l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decKAc-src-ev-inv l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' errCookie}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-ev-inv l d (kcHead KA.stClient) {e₁ = KA.apiKAev l' d' recvKACookie} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-ev-inv l d (kcHead KA.stClient) {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-ev-inv l d (kcHead KA.stClient) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
decKAc-src-ev-inv l d (kcHead KA.stClient) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead KA.stClient)) refl s))
-- head stServer cq : fires receiveKA MsgKeepAliveResponse cr (cq≡cr → loop / cq≢cr → errCookie leaf)
decKAc-src-ev-inv l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAliveResponse cr)} s with step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = kcSil KA.stClient , trans (succVK-inv (decKAc-src l d (kcHead (KA.stServer cq))) s) (brKrespEq l d cq cr t0 md ln) , aKAc l d (kcHead (KA.stServer cq)) (kcSil KA.stClient) refl (ceqKA-c-respEq {t0} {md} {ln} l d cq cr)
decKAc-src-ev-inv l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAlive c)} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-ev-inv l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive MsgKADone}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-ev-inv l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-ev-inv l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-ev-inv l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-ev-inv l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-ev-inv l d (kcHead (KA.stServer cq)) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-ev-inv l d (kcHead (KA.stServer cq)) {e₁ = KA.sendKA l' d'}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-ev-inv l d (kcHead (KA.stServer cq)) {e₁ = KA.apiKAev l' d' m}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
decKAc-src-ev-inv l d (kcHead (KA.stServer cq)) {e₁ = KA.doneKA l' d'}      s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcHead (KA.stServer cq))) refl s))
-- head stDone : ret, no visible step
decKAc-src-ev-inv l d (kcHead KA.stDone) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- errCookie leaf : VACUOUS under Cookie = ⊤ (ne : ¬ (cq ≡ cr) but cq ≡ cr by η)
decKAc-src-ev-inv l d (kcErr1 cq cr ne) s = ⊥-elim (ne refl)
-- send leaf kcReq1 c : fires sendKA (MsgKeepAlive c) → kcSil (stServer c)
decKAc-src-ev-inv l d (kcReq1 c) {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = kcSil (KA.stServer c) , sym (just-injective offer) , aKAc l d (kcReq1 c) (kcSil (KA.stServer c)) refl (ceqKA-c-wmsg l d c)
decKAc-src-ev-inv l d (kcReq1 c) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
decKAc-src-ev-inv l d (kcReq1 c) {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
decKAc-src-ev-inv l d (kcReq1 c) {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d (kcReq1 c)) (hkcReq1 l d c) s))
-- send leaf kcDone1 : fires sendKA MsgKADone → kcSil stDone
decKAc-src-ev-inv l d kcDone1 {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive MsgKADone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = kcSil KA.stDone , sym (just-injective offer) , aKAc l d kcDone1 (kcSil KA.stDone) refl (ceqKA-c-wdone l d)
decKAc-src-ev-inv l d kcDone1 {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
decKAc-src-ev-inv l d kcDone1 {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
decKAc-src-ev-inv l d kcDone1 {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAc-src l d kcDone1) (hkcDone1 l d) s))
-- loop re-entry / errCookie terminal : sil / ret, no visible step
decKAc-src-ev-inv l d (kcSil st) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
decKAc-src-ev-inv l d kcTermE1 s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- SOURCE-side per-position ev inversion — KeepAlive SERVER
decKAs-src-ev-inv : (l : Link) (d : Dir) (pos : KAsPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {P′ : KAProc}
  → decKAs-src l d pos KAL.─[ KAL.ev (KAL.evl (KAL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ KAsPos ] (P′ ≡ decKAs-src l d pos′)
      × (absKAs l d pos ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► absKAs l d pos′)
-- head stClient : receives MsgKeepAlive c (→ ksRecv1 c) / MsgKADone (→ ksDdone1)
decKAs-src-ev-inv l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAlive c)} s with step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = ksRecv1 c , trans (succVK-inv (decKAs-src l d (ksHead KA.stClient)) s) (brKsRecv l d c t0 md ln) , aKAs l d (ksHead KA.stClient) (ksRecv1 c) refl (ceqKA-s-recv {t0} {md} {ln} l d c)
decKAs-src-ev-inv l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive MsgKADone} s with step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = ksDdone1 , trans (succVK-inv (decKAs-src l d (ksHead KA.stClient)) s) (brKsDone l d t0 md ln) , aKAs l d (ksHead KA.stClient) ksDdone1 refl (ceqKA-s-ddone {t0} {md} {ln} l d)
decKAs-src-ev-inv l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAliveResponse c)} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-ev-inv l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-ev-inv l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-ev-inv l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-ev-inv l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-ev-inv l d (ksHead KA.stClient) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-ev-inv l d (ksHead KA.stClient) {e₁ = KA.sendKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-ev-inv l d (ksHead KA.stClient) {e₁ = KA.apiKAev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
decKAs-src-ev-inv l d (ksHead KA.stClient) {e₁ = KA.doneKA l' d'}     s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead KA.stClient)) refl s))
-- head stServer c : sends the response → ksSil stClient
decKAs-src-ev-inv l d (ksHead (KA.stServer c)) {e₁ = KA.sendKA l' d'} {a} s with step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s
... | offer with KA.KAEv-≟ (_ , KA.sendKA l d) (_ , KA.sendKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ksSil KA.stClient , sym (just-injective offer) , aKAs l d (ksHead (KA.stServer c)) (ksSil KA.stClient) refl (ceqKA-s-sresp l d c)
decKAs-src-ev-inv l d (ksHead (KA.stServer c)) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
decKAs-src-ev-inv l d (ksHead (KA.stServer c)) {e₁ = KA.apiKAev l' d' m} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
decKAs-src-ev-inv l d (ksHead (KA.stServer c)) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksHead (KA.stServer c))) refl s))
-- head stDone : ret, no visible step
decKAs-src-ev-inv l d (ksHead KA.stDone) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaf ksRecv1 c : fires apiKAev recvKACookie c → ksSil (stServer c)
decKAs-src-ev-inv l d (ksRecv1 c) {e₁ = KA.apiKAev l' d' m} {a} s with step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s
... | offer with KA.KAEv-≟ (_ , KA.apiKAev l d recvKACookie) (_ , KA.apiKAev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = ksSil (KA.stServer c) , sym (just-injective offer) , aKAs l d (ksRecv1 c) (ksSil (KA.stServer c)) refl (ceqKA-s-srecv l d c)
decKAs-src-ev-inv l d (ksRecv1 c) {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
decKAs-src-ev-inv l d (ksRecv1 c) {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
decKAs-src-ev-inv l d (ksRecv1 c) {e₁ = KA.doneKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d (ksRecv1 c)) (hksRecv1 l d c) s))
-- done leaf ksDdone1 : fires doneKA → ksSil stDone
decKAs-src-ev-inv l d ksDdone1 {e₁ = KA.doneKA l' d'} {a} s with step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s
... | offer with KA.KAEv-≟ (_ , KA.doneKA l d) (_ , KA.doneKA l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = ksSil KA.stDone , sym (just-injective offer) , aKAs l d ksDdone1 (ksSil KA.stDone) refl (ceqKA-s-sddone l d)
decKAs-src-ev-inv l d ksDdone1 {e₁ = KA.sendKA l' d'}    s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
decKAs-src-ev-inv l d ksDdone1 {e₁ = KA.receiveKA l' d'} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
decKAs-src-ev-inv l d ksDdone1 {e₁ = KA.apiKAev l' d' m} s = ⊥-elim (nothing-absurd (step-target-KA (decKAs-src l d ksDdone1) (hksDdone1 l d) s))
-- loop re-entry : sil, no visible step
decKAs-src-ev-inv l d (ksSil st) s with KAL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

------------------------------------------------------------------------
-- G2 (io) — TxSubmission CLIENT / SERVER visible-event inversions.
-- TS carries io (`sendTS`/`receiveTS` → input/output) + api (`apiTSev`) +
-- `doneTS`.  Same infra as CS/BF/KA (`succVT`/`step-target-TS`).  Value
-- carriers are NON-trivial here (List Txid / List Tx / BlockingStyle×ℕ×ℕ),
-- so mid-leaf firings split on the offered value (unlike the ⊤-carrier KA).
------------------------------------------------------------------------

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

-- TS iter-force offer: `succVT q at a` is exactly the offered continuation
succVT-just : (q : TSProc) (at : AnyTypes TS.TSEv) (a : proj₁ at) {P′ : TSProc}
  → vis-ofT (PTree.force q) at a ≡ just P′ → succVT q at a ≡ P′
succVT-just q at a eq with vis-ofT (PTree.force q) at a
succVT-just q at a refl | just t = refl
succVT-just q at a ()   | nothing

-- TS: a visible source step lands on `succVT q (X , e) a`
succVT-inv : (q : TSProc) {X : Set 0ℓ} {e : TS.TSEv X} {a : X} {P′ : TSProc}
  → q TSL.─[ TSL.ev (TSL.evl (TSL.evLabel X e a)) ]─► P′
  → P′ ≡ succVT q (X , e) a
succVT-inv q {X} {e} {a} step with TSL.ev-inv step
... | v , τc , feq , veq =
      sym (succVT-just q (X , e) a (trans (cong (λ n → vis-ofT n (X , e) a) feq) veq))

-- TS: the fired offer entry at a KNOWN force (`refl` head / `h*` mid)
step-target-TS : (q : TSProc)
    {V : (at : AnyTypes TS.TSEv) → ContinueType at (Maybe TSProc)}
    {T : (i : AnyTypes (ExtI TS.TSEv)) → ContinueType i (Maybe TSProc)}
    {X : Set 0ℓ} {e : TS.TSEv X} {a : X} {P′ : TSProc}
  → PTree.force q ≡ react V T
  → q TSL.─[ TSL.ev (TSL.evl (TSL.evLabel X e a)) ]─► P′
  → V (X , e) a ≡ just P′
step-target-TS q {V} {T} {X} {e} {a} feq step with TSL.ev-inv step
... | v , τc , feq′ , veq with react-injective (trans (sym feq) feq′)
...   | Veq , _ = trans (cong (λ w → w (X , e) a) Veq) veq

-- a renamed Net_Api event whose ι-preimage is a TS source event is the ι-image
ιTS-inv-shape : {X : Set 0ℓ} {e₂ : Net_Api Payload X} {e₁ : TS.TSEv X}
  → ιTS⁻¹ e₂ ≡ just e₁ → e₂ ≡ ιTS e₁
ιTS-inv-shape {e₂ = input  _ _ N2N_ChainSync}    ()
ιTS-inv-shape {e₂ = input  _ _ N2N_BlockFetch}   ()
ιTS-inv-shape {e₂ = input  _ _ N2N_TxSubmission} refl = refl
ιTS-inv-shape {e₂ = input  _ _ N2N_KeepAlive}    ()
ιTS-inv-shape {e₂ = input  _ _ N2N_LeiosNotify}  ()
ιTS-inv-shape {e₂ = input  _ _ N2N_LeiosFetch}   ()
ιTS-inv-shape {e₂ = output _ _ N2N_ChainSync}    ()
ιTS-inv-shape {e₂ = output _ _ N2N_BlockFetch}   ()
ιTS-inv-shape {e₂ = output _ _ N2N_TxSubmission} refl = refl
ιTS-inv-shape {e₂ = output _ _ N2N_KeepAlive}    ()
ιTS-inv-shape {e₂ = output _ _ N2N_LeiosNotify}  ()
ιTS-inv-shape {e₂ = output _ _ N2N_LeiosFetch}   ()
ιTS-inv-shape {e₂ = done   _ _ N2N_ChainSync}    ()
ιTS-inv-shape {e₂ = done   _ _ N2N_BlockFetch}   ()
ιTS-inv-shape {e₂ = done   _ _ N2N_TxSubmission} refl = refl
ιTS-inv-shape {e₂ = done   _ _ N2N_KeepAlive}    ()
ιTS-inv-shape {e₂ = done   _ _ N2N_LeiosNotify}  ()
ιTS-inv-shape {e₂ = done   _ _ N2N_LeiosFetch}   ()
ιTS-inv-shape {e₂ = apiTS  _ _ _} refl = refl
ιTS-inv-shape {e₂ = apiCS  _ _ _} ()
ιTS-inv-shape {e₂ = apiBF  _ _ _} ()
ιTS-inv-shape {e₂ = apiKA  _ _ _} ()
ιTS-inv-shape {e₂ = apiLN  _ _ _} ()
ιTS-inv-shape {e₂ = apiLF  _ _ _} ()
ιTS-inv-shape {e₂ = sndmsg _ _ _} ()
ιTS-inv-shape {e₂ = rcvmsg _ _ _} ()
ιTS-inv-shape {e₂ = tx     _ _ _} ()
ιTS-inv-shape {e₂ = sndack _ _ _} ()
ιTS-inv-shape {e₂ = rcvack _ _ _} ()
ιTS-inv-shape {e₂ = ack    _ _ _} ()
ιTS-inv-shape {e₂ = break  _}     ()

-- package a `tsCnxt`/`tsSnxt` agreement into the abstract TS step
aTSc : (l : Link) (d : Dir) (pos pos′ : TScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.tsCfin (coarsenTSc pos) ≡ false
  → NS.tsCnxt l d (coarsenTSc pos) (X , e) a ≡ just (coarsenTSc pos′)
  → absTSc l d pos ─[ ev (evl (evLabel X e a)) ]─► absTSc l d pos′
aTSc l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenTSc pos) finEq ceq
aTSs : (l : Link) (d : Dir) (pos pos′ : TSsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.tsSfin (coarsenTSs pos) ≡ false
  → NS.tsSnxt l d (coarsenTSs pos) (X , e) a ≡ just (coarsenTSs pos′)
  → absTSs l d pos ─[ ev (evl (evLabel X e a)) ]─► absTSs l d pos′
aTSs l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenTSs pos) finEq ceq

-- per-firing `coarsen ∘ nxt` commutations (CLIENT)
ceqTS-c-init : (l : Link) (d : Dir)
  → NS.tsCnxt l d NS.tcInit (_ , input l d N2N_TxSubmission)
      (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) ≡ just NS.tcIdle
ceqTS-c-init l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) = refl
ceqTS-c-idleB : ∀ {t0 md ln} (l : Link) (d : Dir) (a r : ℕ)
  → NS.tsCnxt l d NS.tcIdle (_ , output l d N2N_TxSubmission)
      (t0 , md , ln , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ just (NS.tcAri (Blocking , a , r))
ceqTS-c-idleB l d a r rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-c-idleNB : ∀ {t0 md ln} (l : Link) (d : Dir) (a r : ℕ)
  → NS.tsCnxt l d NS.tcIdle (_ , output l d N2N_TxSubmission)
      (t0 , md , ln , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ just (NS.tcAri (NonBlocking , a , r))
ceqTS-c-idleNB l d a r rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-c-idleTxs : ∀ {t0 md ln} (l : Link) (d : Dir) (ids : _)
  → NS.tsCnxt l d NS.tcIdle (_ , output l d N2N_TxSubmission)
      (t0 , md , ln , txSubmission (MsgTSRequestTxs ids)) ≡ just (NS.tcArt ids)
ceqTS-c-idleTxs l d ids rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-c-blkReply : ∀ {ids} (l : Link) (d : Dir)
  → NS.tsCnxt l d NS.tcBlk (_ , apiTS l d sendTSReplyTxIds) ids ≡ just (NS.tcWri ids)
ceqTS-c-blkReply l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-c-blkDone : ∀ {a} (l : Link) (d : Dir)
  → NS.tsCnxt l d NS.tcBlk (_ , apiTS l d sendTSDone) a ≡ just NS.tcWdone
ceqTS-c-blkDone l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-c-nblReply : ∀ {ids} (l : Link) (d : Dir)
  → NS.tsCnxt l d NS.tcNbl (_ , apiTS l d sendTSReplyTxIds) ids ≡ just (NS.tcWri ids)
ceqTS-c-nblReply l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-c-txsReply : ∀ {txs} (l : Link) (d : Dir)
  → NS.tsCnxt l d NS.tcTxs (_ , apiTS l d sendTSReplyTxs) txs ≡ just (NS.tcWrt txs)
ceqTS-c-txsReply l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-c-ariB : (l : Link) (d : Dir) (a r : ℕ)
  → NS.tsCnxt l d (NS.tcAri (Blocking , a , r)) (_ , apiTS l d recvTSRequestTxIds)
      (Blocking , a , r) ≡ just NS.tcBlk
ceqTS-c-ariB l d a r rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl (Blocking , a , r) = refl
ceqTS-c-ariNB : (l : Link) (d : Dir) (a r : ℕ)
  → NS.tsCnxt l d (NS.tcAri (NonBlocking , a , r)) (_ , apiTS l d recvTSRequestTxIds)
      (NonBlocking , a , r) ≡ just NS.tcNbl
ceqTS-c-ariNB l d a r rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl (NonBlocking , a , r) = refl
ceqTS-c-art : (l : Link) (d : Dir) (ids : _)
  → NS.tsCnxt l d (NS.tcArt ids) (_ , apiTS l d recvTSRequestTxs) ids ≡ just NS.tcTxs
ceqTS-c-art l d ids rewrite ≟-yes-refl l | ≟-yes-refl d with ≡-dec (λ _ _ → yes refl) ids ids
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)
ceqTS-c-wri : (l : Link) (d : Dir) (ids : _)
  → NS.tsCnxt l d (NS.tcWri ids) (_ , input l d N2N_TxSubmission)
      (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just NS.tcIdle
ceqTS-c-wri l d ids rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
ceqTS-c-wdone : (l : Link) (d : Dir)
  → NS.tsCnxt l d NS.tcWdone (_ , input l d N2N_TxSubmission)
      (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) ≡ just NS.tcTerm
ceqTS-c-wdone l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) = refl
ceqTS-c-wrt : (l : Link) (d : Dir) (txs : _)
  → NS.tsCnxt l d (NS.tcWrt txs) (_ , input l d N2N_TxSubmission)
      (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) ≡ just NS.tcIdle
ceqTS-c-wrt l d txs rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) = refl

-- per-firing `coarsen ∘ nxt` commutations (SERVER)
ceqTS-s-init : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.tsSnxt l d NS.tsInit (_ , output l d N2N_TxSubmission)
      (t0 , md , ln , txSubmission MsgTSInit) ≡ just NS.tsIdle
ceqTS-s-init l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-s-reqB : ∀ {ar} (l : Link) (d : Dir)
  → NS.tsSnxt l d NS.tsIdle (_ , apiTS l d sendTSRequestTxIdsBlocking) ar ≡ just (NS.tsWib ar)
ceqTS-s-reqB l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-s-reqNB : ∀ {ar} (l : Link) (d : Dir)
  → NS.tsSnxt l d NS.tsIdle (_ , apiTS l d sendTSRequestTxIdsPipelined) ar ≡ just (NS.tsWin ar)
ceqTS-s-reqNB l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-s-reqTxs : ∀ {ids} (l : Link) (d : Dir)
  → NS.tsSnxt l d NS.tsIdle (_ , apiTS l d sendTSRequestTxsPipelined) ids ≡ just (NS.tsWrt ids)
ceqTS-s-reqTxs l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-s-blkReply : ∀ {t0 md ln} (l : Link) (d : Dir) (ids : _)
  → NS.tsSnxt l d NS.tsBlk (_ , output l d N2N_TxSubmission)
      (t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)) ≡ just NS.tsIdle
ceqTS-s-blkReply l d ids rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-s-blkDone : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.tsSnxt l d NS.tsBlk (_ , output l d N2N_TxSubmission)
      (t0 , md , ln , txSubmission MsgTSDone) ≡ just NS.tsDdone
ceqTS-s-blkDone l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-s-nblReply : ∀ {t0 md ln} (l : Link) (d : Dir) (ids : _)
  → NS.tsSnxt l d NS.tsNbl (_ , output l d N2N_TxSubmission)
      (t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)) ≡ just NS.tsIdle
ceqTS-s-nblReply l d ids rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-s-txsReply : ∀ {t0 md ln} (l : Link) (d : Dir) (txs : _)
  → NS.tsSnxt l d NS.tsTxs (_ , output l d N2N_TxSubmission)
      (t0 , md , ln , txSubmission (MsgTSReplyTxs txs)) ≡ just NS.tsIdle
ceqTS-s-txsReply l d txs rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-s-ddone : ∀ {a} (l : Link) (d : Dir)
  → NS.tsSnxt l d NS.tsDdone (_ , done l d N2N_TxSubmission) a ≡ just NS.tsTerm
ceqTS-s-ddone l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqTS-s-wib : (l : Link) (d : Dir) (a r : ℕ)
  → NS.tsSnxt l d (NS.tsWib (a , r)) (_ , input l d N2N_TxSubmission)
      (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ just NS.tsBlk
ceqTS-s-wib l d a r rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) = refl
ceqTS-s-win : (l : Link) (d : Dir) (a r : ℕ)
  → NS.tsSnxt l d (NS.tsWin (a , r)) (_ , input l d N2N_TxSubmission)
      (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ just NS.tsNbl
ceqTS-s-win l d a r rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) = refl
ceqTS-s-wrt : (l : Link) (d : Dir) (ids : _)
  → NS.tsSnxt l d (NS.tsWrt ids) (_ , input l d N2N_TxSubmission)
      (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) ≡ just NS.tsTxs
ceqTS-s-wrt l d ids rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) = refl

-- receive-firing bridges (unstick the head `l≟l|d≟d`, prefix irrelevant) — CLIENT
brTIdleB : (l : Link) (d : Dir) (a r : ℕ) (t0 : _) (md : _) (ln : _)
  → succVT (decTSc-src l d (tcHead TS.stIdle)) (_ , TS.receiveTS l d)
      (t0 , md , ln , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ decTSc-src l d (tcReqIdsB1 a r)
brTIdleB l d a r t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brTIdleNB : (l : Link) (d : Dir) (a r : ℕ) (t0 : _) (md : _) (ln : _)
  → succVT (decTSc-src l d (tcHead TS.stIdle)) (_ , TS.receiveTS l d)
      (t0 , md , ln , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ decTSc-src l d (tcReqIdsNB1 a r)
brTIdleNB l d a r t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brTIdleTxs : (l : Link) (d : Dir) (ids : _) (t0 : _) (md : _) (ln : _)
  → succVT (decTSc-src l d (tcHead TS.stIdle)) (_ , TS.receiveTS l d)
      (t0 , md , ln , txSubmission (MsgTSRequestTxs ids)) ≡ decTSc-src l d (tcReqTxs1 ids)
brTIdleTxs l d ids t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- receive-firing bridges — SERVER
brTsInit : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVT (decTSs-src l d (tsHead TS.stInit)) (_ , TS.receiveTS l d)
      (t0 , md , ln , txSubmission MsgTSInit) ≡ decTSs-src l d (tsSil TS.stIdle)
brTsInit l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brTsBlkReply : (l : Link) (d : Dir) (ids : _) (t0 : _) (md : _) (ln : _)
  → succVT (decTSs-src l d (tsHead TS.stTxIdsBlocking)) (_ , TS.receiveTS l d)
      (t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)) ≡ decTSs-src l d (tsSil TS.stIdle)
brTsBlkReply l d ids t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brTsBlkDone : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVT (decTSs-src l d (tsHead TS.stTxIdsBlocking)) (_ , TS.receiveTS l d)
      (t0 , md , ln , txSubmission MsgTSDone) ≡ decTSs-src l d tsDone1
brTsBlkDone l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brTsNblReply : (l : Link) (d : Dir) (ids : _) (t0 : _) (md : _) (ln : _)
  → succVT (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) (_ , TS.receiveTS l d)
      (t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)) ≡ decTSs-src l d (tsSil TS.stIdle)
brTsNblReply l d ids t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brTsTxsReply : (l : Link) (d : Dir) (txs : _) (t0 : _) (md : _) (ln : _)
  → succVT (decTSs-src l d (tsHead TS.stTxs)) (_ , TS.receiveTS l d)
      (t0 , md , ln , txSubmission (MsgTSReplyTxs txs)) ≡ decTSs-src l d (tsSil TS.stIdle)
brTsTxsReply l d txs t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- SOURCE-side per-position ev inversion — TxSubmission CLIENT
decTSc-src-ev-inv : (l : Link) (d : Dir) (pos : TScPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : TSProc}
  → decTSc-src l d pos TSL.─[ TSL.ev (TSL.evl (TSL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ TScPos ] (P′ ≡ decTSc-src l d pos′)
      × (absTSc l d pos ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► absTSc l d pos′)
-- head stInit : sends MsgTSInit (io) → tcSil stIdle
decTSc-src-ev-inv l d (tcHead TS.stInit) {e₁ = TS.sendTS l' d'} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tcSil TS.stIdle , sym (just-injective offer) , aTSc l d (tcHead TS.stInit) (tcSil TS.stIdle) refl (ceqTS-c-init l d)
decTSc-src-ev-inv l d (tcHead TS.stInit) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stInit) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stInit) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stInit)) refl s))
-- head stIdle : receives a wire request → tcReqIdsB1 / tcReqIdsNB1 / tcReqTxs1
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds Blocking a r)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tcReqIdsB1 a r , trans (succVT-inv (decTSc-src l d (tcHead TS.stIdle)) s) (brTIdleB l d a r t0 md ln) , aTSc l d (tcHead TS.stIdle) (tcReqIdsB1 a r) refl (ceqTS-c-idleB {t0} {md} {ln} l d a r)
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds NonBlocking a r)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tcReqIdsNB1 a r , trans (succVT-inv (decTSc-src l d (tcHead TS.stIdle)) s) (brTIdleNB l d a r t0 md ln) , aTSc l d (tcHead TS.stIdle) (tcReqIdsNB1 a r) refl (ceqTS-c-idleNB {t0} {md} {ln} l d a r)
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxs ids)} s with step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tcReqTxs1 ids , trans (succVT-inv (decTSc-src l d (tcHead TS.stIdle)) s) (brTIdleTxs l d ids t0 md ln) , aTSc l d (tcHead TS.stIdle) (tcReqTxs1 ids) refl (ceqTS-c-idleTxs {t0} {md} {ln} l d ids)
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit}        s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone}        s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stIdle) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stIdle)) refl s))
-- head stTxIdsBlocking : fires apiTSev sendTSReplyTxIds / sendTSDone
decTSc-src-ev-inv l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tcRepB1 a , succVT-inv (decTSc-src l d (tcHead TS.stTxIdsBlocking)) s , aTSc l d (tcHead TS.stTxIdsBlocking) (tcRepB1 a) refl (ceqTS-c-blkReply l d)
decTSc-src-ev-inv l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSDone} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tcDone1 , succVT-inv (decTSc-src l d (tcHead TS.stTxIdsBlocking)) s , aTSc l d (tcHead TS.stTxIdsBlocking) tcDone1 refl (ceqTS-c-blkDone l d)
decTSc-src-ev-inv l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}          s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsBlocking)) refl s))
-- head stTxIdsNonBlocking : fires apiTSev sendTSReplyTxIds
decTSc-src-ev-inv l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tcRepNB1 a , succVT-inv (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) s , aTSc l d (tcHead TS.stTxIdsNonBlocking) (tcRepNB1 a) refl (ceqTS-c-nblReply l d)
decTSc-src-ev-inv l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSDone}                 s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}          s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxIdsNonBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)) refl s))
-- head stTxs : fires apiTSev sendTSReplyTxs
decTSc-src-ev-inv l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSReplyTxs} {a} s with step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tcRepTxs1 a , succVT-inv (decTSc-src l d (tcHead TS.stTxs)) s , aTSc l d (tcHead TS.stTxs) (tcRepTxs1 a) refl (ceqTS-c-txsReply l d)
decTSc-src-ev-inv l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds}            s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSDone}                  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds}           s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxs) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}             s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxs) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxs) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
decTSc-src-ev-inv l d (tcHead TS.stTxs) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcHead TS.stTxs)) refl s))
-- head stDone : ret, no visible step
decTSc-src-ev-inv l d (tcHead TS.stDone) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaf tcReqIdsB1 : fires apiTSev recvTSRequestTxIds (Blocking,a,r) → tcSil stTxIdsBlocking
decTSc-src-ev-inv l d (tcReqIdsB1 a r) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxIds) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (Blocking , a , r)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tcSil TS.stTxIdsBlocking , sym (just-injective offer) , aTSc l d (tcReqIdsB1 a r) (tcSil TS.stTxIdsBlocking) refl (ceqTS-c-ariB l d a r)
decTSc-src-ev-inv l d (tcReqIdsB1 a r) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
decTSc-src-ev-inv l d (tcReqIdsB1 a r) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
decTSc-src-ev-inv l d (tcReqIdsB1 a r) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsB1 a r)) (htcReqIdsB1 l d a r) s))
-- recv leaf tcReqIdsNB1 : fires apiTSev recvTSRequestTxIds (NonBlocking,a,r) → tcSil stTxIdsNonBlocking
decTSc-src-ev-inv l d (tcReqIdsNB1 a r) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxIds) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (NonBlocking , a , r)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tcSil TS.stTxIdsNonBlocking , sym (just-injective offer) , aTSc l d (tcReqIdsNB1 a r) (tcSil TS.stTxIdsNonBlocking) refl (ceqTS-c-ariNB l d a r)
decTSc-src-ev-inv l d (tcReqIdsNB1 a r) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
decTSc-src-ev-inv l d (tcReqIdsNB1 a r) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
decTSc-src-ev-inv l d (tcReqIdsNB1 a r) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqIdsNB1 a r)) (htcReqIdsNB1 l d a r) s))
-- recv leaf tcReqTxs1 : fires apiTSev recvTSRequestTxs ids → tcSil stTxs
decTSc-src-ev-inv l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' m} {a = val} s with step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.apiTSev l d recvTSRequestTxs) (_ , TS.apiTSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec (λ _ _ → yes refl) val ids
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tcSil TS.stTxs , sym (just-injective offer) , aTSc l d (tcReqTxs1 ids) (tcSil TS.stTxs) refl (ceqTS-c-art l d ids)
decTSc-src-ev-inv l d (tcReqTxs1 ids) {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
decTSc-src-ev-inv l d (tcReqTxs1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
decTSc-src-ev-inv l d (tcReqTxs1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcReqTxs1 ids)) (htcReqTxs1 l d ids) s))
-- send leaf tcRepB1 : fires sendTS (MsgTSReplyTxIds ids) → tcSil stIdle
decTSc-src-ev-inv l d (tcRepB1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tcSil TS.stIdle , sym (just-injective offer) , aTSc l d (tcRepB1 ids) (tcSil TS.stIdle) refl (ceqTS-c-wri l d ids)
decTSc-src-ev-inv l d (tcRepB1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
decTSc-src-ev-inv l d (tcRepB1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
decTSc-src-ev-inv l d (tcRepB1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepB1 ids)) (htcRepB1 l d ids) s))
-- send leaf tcDone1 : fires sendTS MsgTSDone → tcSil stDone
decTSc-src-ev-inv l d tcDone1 {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tcSil TS.stDone , sym (just-injective offer) , aTSc l d tcDone1 (tcSil TS.stDone) refl (ceqTS-c-wdone l d)
decTSc-src-ev-inv l d tcDone1 {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
decTSc-src-ev-inv l d tcDone1 {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
decTSc-src-ev-inv l d tcDone1 {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d tcDone1) (htcDone1 l d) s))
-- send leaf tcRepNB1 : fires sendTS (MsgTSReplyTxIds ids) → tcSil stIdle
decTSc-src-ev-inv l d (tcRepNB1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tcSil TS.stIdle , sym (just-injective offer) , aTSc l d (tcRepNB1 ids) (tcSil TS.stIdle) refl (ceqTS-c-wri l d ids)
decTSc-src-ev-inv l d (tcRepNB1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
decTSc-src-ev-inv l d (tcRepNB1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
decTSc-src-ev-inv l d (tcRepNB1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepNB1 ids)) (htcRepNB1 l d ids) s))
-- send leaf tcRepTxs1 : fires sendTS (MsgTSReplyTxs txs) → tcSil stIdle
decTSc-src-ev-inv l d (tcRepTxs1 txs) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tcSil TS.stIdle , sym (just-injective offer) , aTSc l d (tcRepTxs1 txs) (tcSil TS.stIdle) refl (ceqTS-c-wrt l d txs)
decTSc-src-ev-inv l d (tcRepTxs1 txs) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
decTSc-src-ev-inv l d (tcRepTxs1 txs) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
decTSc-src-ev-inv l d (tcRepTxs1 txs) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSc-src l d (tcRepTxs1 txs)) (htcRepTxs1 l d txs) s))
-- loop re-entry : sil, no visible step
decTSc-src-ev-inv l d (tcSil st) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- SOURCE-side per-position ev inversion — TxSubmission SERVER
decTSs-src-ev-inv : (l : Link) (d : Dir) (pos : TSsPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {P′ : TSProc}
  → decTSs-src l d pos TSL.─[ TSL.ev (TSL.evl (TSL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ TSsPos ] (P′ ≡ decTSs-src l d pos′)
      × (absTSs l d pos ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► absTSs l d pos′)
-- head stInit : receives MsgTSInit → tsSil stIdle
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSInit} s with step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tsSil TS.stIdle , trans (succVT-inv (decTSs-src l d (tsHead TS.stInit)) s) (brTsInit l d t0 md ln) , aTSs l d (tsHead TS.stInit) (tsSil TS.stIdle) refl (ceqTS-s-init {t0} {md} {ln} l d)
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stInit) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stInit)) refl s))
-- head stIdle : fires the three api pull requests
decTSs-src-ev-inv l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tsReqB1 a , succVT-inv (decTSs-src l d (tsHead TS.stIdle)) s , aTSs l d (tsHead TS.stIdle) (tsReqB1 a) refl (ceqTS-s-reqB l d)
decTSs-src-ev-inv l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tsReqNB1 a , succVT-inv (decTSs-src l d (tsHead TS.stIdle)) s , aTSs l d (tsHead TS.stIdle) (tsReqNB1 a) refl (ceqTS-s-reqNB l d)
decTSs-src-ev-inv l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined} {a} s with step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tsReqTxs1 a , succVT-inv (decTSs-src l d (tsHead TS.stIdle)) s , aTSs l d (tsHead TS.stIdle) (tsReqTxs1 a) refl (ceqTS-s-reqTxs l d)
decTSs-src-ev-inv l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSReplyTxs}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' sendTSDone}       s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stIdle) {e₁ = TS.apiTSev l' d' recvTSRequestTxs}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stIdle) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stIdle) {e₁ = TS.receiveTS l' d'}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stIdle) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stIdle)) refl s))
-- head stTxIdsBlocking : receives MsgTSReplyTxIds (→ tsSil stIdle) / MsgTSDone (→ tsDone1)
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tsSil TS.stIdle , trans (succVT-inv (decTSs-src l d (tsHead TS.stTxIdsBlocking)) s) (brTsBlkReply l d ids t0 md ln) , aTSs l d (tsHead TS.stTxIdsBlocking) (tsSil TS.stIdle) refl (ceqTS-s-blkReply {t0} {md} {ln} l d ids)
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSDone} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tsDone1 , trans (succVT-inv (decTSs-src l d (tsHead TS.stTxIdsBlocking)) s) (brTsBlkDone l d t0 md ln) , aTSs l d (tsHead TS.stTxIdsBlocking) tsDone1 refl (ceqTS-s-blkDone {t0} {md} {ln} l d)
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsBlocking)) refl s))
-- head stTxIdsNonBlocking : receives MsgTSReplyTxIds → tsSil stIdle
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tsSil TS.stIdle , trans (succVT-inv (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) s) (brTsNblReply l d ids t0 md ln) , aTSs l d (tsHead TS.stTxIdsNonBlocking) (tsSil TS.stIdle) refl (ceqTS-s-nblReply {t0} {md} {ln} l d ids)
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxIdsNonBlocking) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)) refl s))
-- head stTxs : receives MsgTSReplyTxs → tsSil stIdle
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxs txs)} s with step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = tsSil TS.stIdle , trans (succVT-inv (decTSs-src l d (tsHead TS.stTxs)) s) (brTsTxsReply l d txs t0 md ln) , aTSs l d (tsHead TS.stTxs) (tsSil TS.stIdle) refl (ceqTS-s-txsReply {t0} {md} {ln} l d txs)
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x}   s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.sendTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.apiTSev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
decTSs-src-ev-inv l d (tsHead TS.stTxs) {e₁ = TS.doneTS l' d'}     s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsHead TS.stTxs)) refl s))
-- head stDone : ret, no visible step
decTSs-src-ev-inv l d (tsHead TS.stDone) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf tsDone1 : fires doneTS → tsSil stDone
decTSs-src-ev-inv l d tsDone1 {e₁ = TS.doneTS l' d'} {a} s with step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s
... | offer with TS.TSEv-≟ (_ , TS.doneTS l d) (_ , TS.doneTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = tsSil TS.stDone , sym (just-injective offer) , aTSs l d tsDone1 (tsSil TS.stDone) refl (ceqTS-s-ddone l d)
decTSs-src-ev-inv l d tsDone1 {e₁ = TS.sendTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
decTSs-src-ev-inv l d tsDone1 {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
decTSs-src-ev-inv l d tsDone1 {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d tsDone1) (htsDone1 l d) s))
-- send leaf tsReqB1 : fires sendTS (MsgTSRequestTxIds Blocking a r) → tsSil stTxIdsBlocking
decTSs-src-ev-inv l d (tsReqB1 (a , r)) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tsSil TS.stTxIdsBlocking , sym (just-injective offer) , aTSs l d (tsReqB1 (a , r)) (tsSil TS.stTxIdsBlocking) refl (ceqTS-s-wib l d a r)
decTSs-src-ev-inv l d (tsReqB1 (a , r)) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
decTSs-src-ev-inv l d (tsReqB1 (a , r)) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
decTSs-src-ev-inv l d (tsReqB1 (a , r)) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqB1 (a , r))) (htsReqB1 l d (a , r)) s))
-- send leaf tsReqNB1 : fires sendTS (MsgTSRequestTxIds NonBlocking a r) → tsSil stTxIdsNonBlocking
decTSs-src-ev-inv l d (tsReqNB1 (a , r)) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tsSil TS.stTxIdsNonBlocking , sym (just-injective offer) , aTSs l d (tsReqNB1 (a , r)) (tsSil TS.stTxIdsNonBlocking) refl (ceqTS-s-win l d a r)
decTSs-src-ev-inv l d (tsReqNB1 (a , r)) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
decTSs-src-ev-inv l d (tsReqNB1 (a , r)) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
decTSs-src-ev-inv l d (tsReqNB1 (a , r)) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqNB1 (a , r))) (htsReqNB1 l d (a , r)) s))
-- send leaf tsReqTxs1 : fires sendTS (MsgTSRequestTxs ids) → tsSil stTxs
decTSs-src-ev-inv l d (tsReqTxs1 ids) {e₁ = TS.sendTS l' d'} {a = val} s with step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s
... | offer with TS.TSEv-≟ (_ , TS.sendTS l d) (_ , TS.sendTS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = tsSil TS.stTxs , sym (just-injective offer) , aTSs l d (tsReqTxs1 ids) (tsSil TS.stTxs) refl (ceqTS-s-wrt l d ids)
decTSs-src-ev-inv l d (tsReqTxs1 ids) {e₁ = TS.receiveTS l' d'} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
decTSs-src-ev-inv l d (tsReqTxs1 ids) {e₁ = TS.apiTSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
decTSs-src-ev-inv l d (tsReqTxs1 ids) {e₁ = TS.doneTS l' d'}    s = ⊥-elim (nothing-absurd (step-target-TS (decTSs-src l d (tsReqTxs1 ids)) (htsReqTxs1 l d ids) s))
-- loop re-entry : sil, no visible step
decTSs-src-ev-inv l d (tsSil st) s with TSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

------------------------------------------------------------------------
-- G2 (io) — LeiosNotify CLIENT / SERVER visible-event inversions.
-- LN carries io (`sendLN`/`receiveLN` → input/output) + api (`apiLNev`) +
-- `doneLN`.  Same infra as CS/BF/KA/TS.  Value carriers: Header / Point (Block₃-
-- based) split like CS `(h,t)`; `List Vote` is a bare list → explicit `≡-dec`.
------------------------------------------------------------------------

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

-- LN iter-force offer: `succVN q at a` is exactly the offered continuation
succVN-just : (q : LNProc) (at : AnyTypes LNp.LNEv) (a : proj₁ at) {P′ : LNProc}
  → vis-ofN (PTree.force q) at a ≡ just P′ → succVN q at a ≡ P′
succVN-just q at a eq with vis-ofN (PTree.force q) at a
succVN-just q at a refl | just t = refl
succVN-just q at a ()   | nothing

-- LN: a visible source step lands on `succVN q (X , e) a`
succVN-inv : (q : LNProc) {X : Set 0ℓ} {e : LNp.LNEv X} {a : X} {P′ : LNProc}
  → q LNL.─[ LNL.ev (LNL.evl (LNL.evLabel X e a)) ]─► P′
  → P′ ≡ succVN q (X , e) a
succVN-inv q {X} {e} {a} step with LNL.ev-inv step
... | v , τc , feq , veq =
      sym (succVN-just q (X , e) a (trans (cong (λ n → vis-ofN n (X , e) a) feq) veq))

-- LN: the fired offer entry at a KNOWN force (`refl` head / `h*` mid)
step-target-LN : (q : LNProc)
    {V : (at : AnyTypes LNp.LNEv) → ContinueType at (Maybe LNProc)}
    {T : (i : AnyTypes (ExtI LNp.LNEv)) → ContinueType i (Maybe LNProc)}
    {X : Set 0ℓ} {e : LNp.LNEv X} {a : X} {P′ : LNProc}
  → PTree.force q ≡ react V T
  → q LNL.─[ LNL.ev (LNL.evl (LNL.evLabel X e a)) ]─► P′
  → V (X , e) a ≡ just P′
step-target-LN q {V} {T} {X} {e} {a} feq step with LNL.ev-inv step
... | v , τc , feq′ , veq with react-injective (trans (sym feq) feq′)
...   | Veq , _ = trans (cong (λ w → w (X , e) a) Veq) veq

-- a renamed Net_Api event whose ι-preimage is an LN source event is the ι-image
ιLN-inv-shape : {X : Set 0ℓ} {e₂ : Net_Api Payload X} {e₁ : LNp.LNEv X}
  → ιLN⁻¹ e₂ ≡ just e₁ → e₂ ≡ ιLN e₁
ιLN-inv-shape {e₂ = input  _ _ N2N_ChainSync}    ()
ιLN-inv-shape {e₂ = input  _ _ N2N_BlockFetch}   ()
ιLN-inv-shape {e₂ = input  _ _ N2N_TxSubmission} ()
ιLN-inv-shape {e₂ = input  _ _ N2N_KeepAlive}    ()
ιLN-inv-shape {e₂ = input  _ _ N2N_LeiosNotify}  refl = refl
ιLN-inv-shape {e₂ = input  _ _ N2N_LeiosFetch}   ()
ιLN-inv-shape {e₂ = output _ _ N2N_ChainSync}    ()
ιLN-inv-shape {e₂ = output _ _ N2N_BlockFetch}   ()
ιLN-inv-shape {e₂ = output _ _ N2N_TxSubmission} ()
ιLN-inv-shape {e₂ = output _ _ N2N_KeepAlive}    ()
ιLN-inv-shape {e₂ = output _ _ N2N_LeiosNotify}  refl = refl
ιLN-inv-shape {e₂ = output _ _ N2N_LeiosFetch}   ()
ιLN-inv-shape {e₂ = done   _ _ N2N_ChainSync}    ()
ιLN-inv-shape {e₂ = done   _ _ N2N_BlockFetch}   ()
ιLN-inv-shape {e₂ = done   _ _ N2N_TxSubmission} ()
ιLN-inv-shape {e₂ = done   _ _ N2N_KeepAlive}    ()
ιLN-inv-shape {e₂ = done   _ _ N2N_LeiosNotify}  refl = refl
ιLN-inv-shape {e₂ = done   _ _ N2N_LeiosFetch}   ()
ιLN-inv-shape {e₂ = apiLN  _ _ _} refl = refl
ιLN-inv-shape {e₂ = apiCS  _ _ _} ()
ιLN-inv-shape {e₂ = apiBF  _ _ _} ()
ιLN-inv-shape {e₂ = apiKA  _ _ _} ()
ιLN-inv-shape {e₂ = apiTS  _ _ _} ()
ιLN-inv-shape {e₂ = apiLF  _ _ _} ()
ιLN-inv-shape {e₂ = sndmsg _ _ _} ()
ιLN-inv-shape {e₂ = rcvmsg _ _ _} ()
ιLN-inv-shape {e₂ = tx     _ _ _} ()
ιLN-inv-shape {e₂ = sndack _ _ _} ()
ιLN-inv-shape {e₂ = rcvack _ _ _} ()
ιLN-inv-shape {e₂ = ack    _ _ _} ()
ιLN-inv-shape {e₂ = break  _}     ()

-- package a `lnCnxt`/`lnSnxt` agreement into the abstract LN step
aLNc : (l : Link) (d : Dir) (pos pos′ : LNcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.lnCfin (coarsenLNc pos) ≡ false
  → NS.lnCnxt l d (coarsenLNc pos) (X , e) a ≡ just (coarsenLNc pos′)
  → absLNc l d pos ─[ ev (evl (evLabel X e a)) ]─► absLNc l d pos′
aLNc l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenLNc pos) finEq ceq
aLNs : (l : Link) (d : Dir) (pos pos′ : LNsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.lnSfin (coarsenLNs pos) ≡ false
  → NS.lnSnxt l d (coarsenLNs pos) (X , e) a ≡ just (coarsenLNs pos′)
  → absLNs l d pos ─[ ev (evl (evLabel X e a)) ]─► absLNs l d pos′
aLNs l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenLNs pos) finEq ceq

-- per-firing `coarsen ∘ nxt` commutations (CLIENT)
ceqLN-c-req : ∀ {a} (l : Link) (d : Dir)
  → NS.lnCnxt l d NS.lncIdle (_ , apiLN l d sendLNRequestNext) a ≡ just NS.lncWreq
ceqLN-c-req l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-c-done : ∀ {a} (l : Link) (d : Dir)
  → NS.lnCnxt l d NS.lncIdle (_ , apiLN l d sendLNDone) a ≡ just NS.lncWdone
ceqLN-c-done l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-c-busyAnn : ∀ {t0 md ln} (l : Link) (d : Dir) (h : Header)
  → NS.lnCnxt l d NS.lncBusy (_ , output l d N2N_LeiosNotify)
      (t0 , md , ln , leiosNotify (MsgLNBlockAnnouncement h)) ≡ just (NS.lncRann h)
ceqLN-c-busyAnn l d h rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-c-busyOff : ∀ {t0 md ln} (l : Link) (d : Dir) (q : _)
  → NS.lnCnxt l d NS.lncBusy (_ , output l d N2N_LeiosNotify)
      (t0 , md , ln , leiosNotify (MsgLNBlockOffer q)) ≡ just (NS.lncRoff q)
ceqLN-c-busyOff l d q rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-c-busyTxs : ∀ {t0 md ln} (l : Link) (d : Dir) (q : _)
  → NS.lnCnxt l d NS.lncBusy (_ , output l d N2N_LeiosNotify)
      (t0 , md , ln , leiosNotify (MsgLNBlockTxsOffer q)) ≡ just (NS.lncRtxs q)
ceqLN-c-busyTxs l d q rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-c-busyVot : ∀ {t0 md ln} (l : Link) (d : Dir) (vs : List Vote)
  → NS.lnCnxt l d NS.lncBusy (_ , output l d N2N_LeiosNotify)
      (t0 , md , ln , leiosNotify (MsgLNVotesOffer vs)) ≡ just (NS.lncRvot vs)
ceqLN-c-busyVot l d vs rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-c-rann : (l : Link) (d : Dir) (h : Header)
  → NS.lnCnxt l d (NS.lncRann h) (_ , apiLN l d recvLNBlockAnnouncement) h ≡ just NS.lncIdle
ceqLN-c-rann l d h rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl h = refl
ceqLN-c-roff : (l : Link) (d : Dir) (q : _)
  → NS.lnCnxt l d (NS.lncRoff q) (_ , apiLN l d recvLNBlockOffer) q ≡ just NS.lncIdle
ceqLN-c-roff l d q rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl q = refl
ceqLN-c-rtxs : (l : Link) (d : Dir) (q : _)
  → NS.lnCnxt l d (NS.lncRtxs q) (_ , apiLN l d recvLNBlockTxsOffer) q ≡ just NS.lncIdle
ceqLN-c-rtxs l d q rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl q = refl
ceqLN-c-rvot : (l : Link) (d : Dir) (vs : List Vote)
  → NS.lnCnxt l d (NS.lncRvot vs) (_ , apiLN l d recvLNVotesOffer) vs ≡ just NS.lncIdle
ceqLN-c-rvot l d vs rewrite ≟-yes-refl l | ≟-yes-refl d with ≡-dec _≟_ vs vs
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)
ceqLN-c-wreq : (l : Link) (d : Dir)
  → NS.lnCnxt l d NS.lncWreq (_ , input l d N2N_LeiosNotify)
      (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) ≡ just NS.lncBusy
ceqLN-c-wreq l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) = refl
ceqLN-c-wdone : (l : Link) (d : Dir)
  → NS.lnCnxt l d NS.lncWdone (_ , input l d N2N_LeiosNotify)
      (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) ≡ just NS.lncTerm
ceqLN-c-wdone l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) = refl

-- per-firing `coarsen ∘ nxt` commutations (SERVER)
ceqLN-s-idleReq : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.lnSnxt l d NS.lnsIdle (_ , output l d N2N_LeiosNotify)
      (t0 , md , ln , leiosNotify MsgLNRequestNext) ≡ just NS.lnsBusy
ceqLN-s-idleReq l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-s-idleDone : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.lnSnxt l d NS.lnsIdle (_ , output l d N2N_LeiosNotify)
      (t0 , md , ln , leiosNotify MsgLNDone) ≡ just NS.lnsDone
ceqLN-s-idleDone l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-s-busyAnn : ∀ {h} (l : Link) (d : Dir)
  → NS.lnSnxt l d NS.lnsBusy (_ , apiLN l d sendLNBlockAnnouncement) h ≡ just (NS.lnsWann h)
ceqLN-s-busyAnn l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-s-busyOff : ∀ {q} (l : Link) (d : Dir)
  → NS.lnSnxt l d NS.lnsBusy (_ , apiLN l d sendLNBlockOffer) q ≡ just (NS.lnsWoff q)
ceqLN-s-busyOff l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-s-busyTxs : ∀ {q} (l : Link) (d : Dir)
  → NS.lnSnxt l d NS.lnsBusy (_ , apiLN l d sendLNBlockTxsOffer) q ≡ just (NS.lnsWtxs q)
ceqLN-s-busyTxs l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-s-busyVot : ∀ {vs} (l : Link) (d : Dir)
  → NS.lnSnxt l d NS.lnsBusy (_ , apiLN l d sendLNVotesOffer) vs ≡ just (NS.lnsWvot vs)
ceqLN-s-busyVot l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLN-s-wann : (l : Link) (d : Dir) (h : Header)
  → NS.lnSnxt l d (NS.lnsWann h) (_ , input l d N2N_LeiosNotify)
      (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) ≡ just NS.lnsIdle
ceqLN-s-wann l d h rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) = refl
ceqLN-s-woff : (l : Link) (d : Dir) (q : _)
  → NS.lnSnxt l d (NS.lnsWoff q) (_ , input l d N2N_LeiosNotify)
      (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) ≡ just NS.lnsIdle
ceqLN-s-woff l d q rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) = refl
ceqLN-s-wtxs : (l : Link) (d : Dir) (q : _)
  → NS.lnSnxt l d (NS.lnsWtxs q) (_ , input l d N2N_LeiosNotify)
      (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) ≡ just NS.lnsIdle
ceqLN-s-wtxs l d q rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) = refl
ceqLN-s-wvot : (l : Link) (d : Dir) (vs : List Vote)
  → NS.lnSnxt l d (NS.lnsWvot vs) (_ , input l d N2N_LeiosNotify)
      (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) ≡ just NS.lnsIdle
ceqLN-s-wvot l d vs rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) = refl
ceqLN-s-ddone : ∀ {a} (l : Link) (d : Dir)
  → NS.lnSnxt l d NS.lnsDone (_ , done l d N2N_LeiosNotify) a ≡ just NS.lnsTerm
ceqLN-s-ddone l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- receive-firing bridges (unstick the head `l≟l|d≟d`, prefix irrelevant) — CLIENT
brLNBusyAnn : (l : Link) (d : Dir) (h : Header) (t0 : _) (md : _) (ln : _)
  → succVN (decLNc-src l d (lncHead LNp.stBusy)) (_ , LNp.receiveLN l d)
      (t0 , md , ln , leiosNotify (MsgLNBlockAnnouncement h)) ≡ decLNc-src l d (lncRann1 h)
brLNBusyAnn l d h t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brLNBusyOff : (l : Link) (d : Dir) (q : _) (t0 : _) (md : _) (ln : _)
  → succVN (decLNc-src l d (lncHead LNp.stBusy)) (_ , LNp.receiveLN l d)
      (t0 , md , ln , leiosNotify (MsgLNBlockOffer q)) ≡ decLNc-src l d (lncRoff1 q)
brLNBusyOff l d q t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brLNBusyTxs : (l : Link) (d : Dir) (q : _) (t0 : _) (md : _) (ln : _)
  → succVN (decLNc-src l d (lncHead LNp.stBusy)) (_ , LNp.receiveLN l d)
      (t0 , md , ln , leiosNotify (MsgLNBlockTxsOffer q)) ≡ decLNc-src l d (lncRtxs1 q)
brLNBusyTxs l d q t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brLNBusyVot : (l : Link) (d : Dir) (vs : _) (t0 : _) (md : _) (ln : _)
  → succVN (decLNc-src l d (lncHead LNp.stBusy)) (_ , LNp.receiveLN l d)
      (t0 , md , ln , leiosNotify (MsgLNVotesOffer vs)) ≡ decLNc-src l d (lncRvot1 vs)
brLNBusyVot l d vs t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- receive-firing bridges — SERVER
brLNsIdleReq : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVN (decLNs-src l d (lnsHead LNp.stIdle)) (_ , LNp.receiveLN l d)
      (t0 , md , ln , leiosNotify MsgLNRequestNext) ≡ decLNs-src l d (lnsSil LNp.stBusy)
brLNsIdleReq l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brLNsIdleDone : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVN (decLNs-src l d (lnsHead LNp.stIdle)) (_ , LNp.receiveLN l d)
      (t0 , md , ln , leiosNotify MsgLNDone) ≡ decLNs-src l d lnsDone1
brLNsIdleDone l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- SOURCE-side per-position ev inversion — LeiosNotify CLIENT
decLNc-src-ev-inv : (l : Link) (d : Dir) (pos : LNcPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {P′ : LNProc}
  → decLNc-src l d pos LNL.─[ LNL.ev (LNL.evl (LNL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ LNcPos ] (P′ ≡ decLNc-src l d pos′)
      × (absLNc l d pos ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► absLNc l d pos′)
-- head stIdle : fires apiLNev sendLNRequestNext / sendLNDone
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNRequestNext} {a} s with step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lncReq1 , succVN-inv (decLNc-src l d (lncHead LNp.stIdle)) s , aLNc l d (lncHead LNp.stIdle) lncReq1 refl (ceqLN-c-req l d)
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNDone} {a} s with step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lncDone1 , succVN-inv (decLNc-src l d (lncHead LNp.stIdle)) s , aLNc l d (lncHead LNp.stIdle) lncDone1 refl (ceqLN-c-done l d)
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNBlockTxsOffer}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' sendLNVotesOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNBlockTxsOffer}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' recvLNVotesOffer}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stIdle) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stIdle)) refl s))
-- head stBusy : receives one of four notifications
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockAnnouncement h)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lncRann1 h , trans (succVN-inv (decLNc-src l d (lncHead LNp.stBusy)) s) (brLNBusyAnn l d h t0 md ln) , aLNc l d (lncHead LNp.stBusy) (lncRann1 h) refl (ceqLN-c-busyAnn {t0} {md} {ln} l d h)
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockOffer q)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lncRoff1 q , trans (succVN-inv (decLNc-src l d (lncHead LNp.stBusy)) s) (brLNBusyOff l d q t0 md ln) , aLNc l d (lncHead LNp.stBusy) (lncRoff1 q) refl (ceqLN-c-busyOff {t0} {md} {ln} l d q)
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockTxsOffer q)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lncRtxs1 q , trans (succVN-inv (decLNc-src l d (lncHead LNp.stBusy)) s) (brLNBusyTxs l d q t0 md ln) , aLNc l d (lncHead LNp.stBusy) (lncRtxs1 q) refl (ceqLN-c-busyTxs {t0} {md} {ln} l d q)
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNVotesOffer vs)} s with step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lncRvot1 vs , trans (succVN-inv (decLNc-src l d (lncHead LNp.stBusy)) s) (brLNBusyVot l d vs t0 md ln) , aLNc l d (lncHead LNp.stBusy) (lncRvot1 vs) refl (ceqLN-c-busyVot {t0} {md} {ln} l d vs)
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNRequestNext} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNDone} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
decLNc-src-ev-inv l d (lncHead LNp.stBusy) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncHead LNp.stBusy)) refl s))
-- head stDone : ret, no visible step
decLNc-src-ev-inv l d (lncHead LNp.stDone) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaf lncRann1 : fires apiLNev recvLNBlockAnnouncement h → lncSil stIdle
decLNc-src-ev-inv l d (lncRann1 h) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockAnnouncement) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ h
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lncSil LNp.stIdle , sym (just-injective offer) , aLNc l d (lncRann1 h) (lncSil LNp.stIdle) refl (ceqLN-c-rann l d h)
decLNc-src-ev-inv l d (lncRann1 h) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
decLNc-src-ev-inv l d (lncRann1 h) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
decLNc-src-ev-inv l d (lncRann1 h) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRann1 h)) (hlncRann1 l d h) s))
-- recv leaf lncRoff1 : fires apiLNev recvLNBlockOffer q → lncSil stIdle
decLNc-src-ev-inv l d (lncRoff1 q) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ q
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lncSil LNp.stIdle , sym (just-injective offer) , aLNc l d (lncRoff1 q) (lncSil LNp.stIdle) refl (ceqLN-c-roff l d q)
decLNc-src-ev-inv l d (lncRoff1 q) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
decLNc-src-ev-inv l d (lncRoff1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
decLNc-src-ev-inv l d (lncRoff1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRoff1 q)) (hlncRoff1 l d q) s))
-- recv leaf lncRtxs1 : fires apiLNev recvLNBlockTxsOffer q → lncSil stIdle
decLNc-src-ev-inv l d (lncRtxs1 q) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNBlockTxsOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ q
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lncSil LNp.stIdle , sym (just-injective offer) , aLNc l d (lncRtxs1 q) (lncSil LNp.stIdle) refl (ceqLN-c-rtxs l d q)
decLNc-src-ev-inv l d (lncRtxs1 q) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
decLNc-src-ev-inv l d (lncRtxs1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
decLNc-src-ev-inv l d (lncRtxs1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRtxs1 q)) (hlncRtxs1 l d q) s))
-- recv leaf lncRvot1 : fires apiLNev recvLNVotesOffer vs → lncSil stIdle
decLNc-src-ev-inv l d (lncRvot1 vs) {e₁ = LNp.apiLNev l' d' m} {a = val} s with step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s
... | offer with LNp.LNEv-≟ (_ , LNp.apiLNev l d recvLNVotesOffer) (_ , LNp.apiLNev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val vs
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lncSil LNp.stIdle , sym (just-injective offer) , aLNc l d (lncRvot1 vs) (lncSil LNp.stIdle) refl (ceqLN-c-rvot l d vs)
decLNc-src-ev-inv l d (lncRvot1 vs) {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
decLNc-src-ev-inv l d (lncRvot1 vs) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
decLNc-src-ev-inv l d (lncRvot1 vs) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d (lncRvot1 vs)) (hlncRvot1 l d vs) s))
-- send leaf lncReq1 : fires sendLN MsgLNRequestNext → lncSil stBusy
decLNc-src-ev-inv l d lncReq1 {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lncSil LNp.stBusy , sym (just-injective offer) , aLNc l d lncReq1 (lncSil LNp.stBusy) refl (ceqLN-c-wreq l d)
decLNc-src-ev-inv l d lncReq1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
decLNc-src-ev-inv l d lncReq1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
decLNc-src-ev-inv l d lncReq1 {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncReq1) (hlncReq1 l d) s))
-- send leaf lncDone1 : fires sendLN MsgLNDone → lncSil stDone
decLNc-src-ev-inv l d lncDone1 {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lncSil LNp.stDone , sym (just-injective offer) , aLNc l d lncDone1 (lncSil LNp.stDone) refl (ceqLN-c-wdone l d)
decLNc-src-ev-inv l d lncDone1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
decLNc-src-ev-inv l d lncDone1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
decLNc-src-ev-inv l d lncDone1 {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNc-src l d lncDone1) (hlncDone1 l d) s))
-- loop re-entry : sil, no visible step
decLNc-src-ev-inv l d (lncSil st) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- SOURCE-side per-position ev inversion — LeiosNotify SERVER
decLNs-src-ev-inv : (l : Link) (d : Dir) (pos : LNsPos)
    {X : Set 0ℓ} {e₁ : LNp.LNEv X} {a : X} {P′ : LNProc}
  → decLNs-src l d pos LNL.─[ LNL.ev (LNL.evl (LNL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ LNsPos ] (P′ ≡ decLNs-src l d pos′)
      × (absLNs l d pos ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► absLNs l d pos′)
-- head stIdle : receives MsgLNRequestNext (→ lnsSil stBusy) / MsgLNDone (→ lnsDone1)
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNRequestNext} s with step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lnsSil LNp.stBusy , trans (succVN-inv (decLNs-src l d (lnsHead LNp.stIdle)) s) (brLNsIdleReq l d t0 md ln) , aLNs l d (lnsHead LNp.stIdle) (lnsSil LNp.stBusy) refl (ceqLN-s-idleReq {t0} {md} {ln} l d)
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNDone} s with step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lnsDone1 , trans (succVN-inv (decLNs-src l d (lnsHead LNp.stIdle)) s) (brLNsIdleDone l d t0 md ln) , aLNs l d (lnsHead LNp.stIdle) lnsDone1 refl (ceqLN-s-idleDone {t0} {md} {ln} l d)
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.apiLNev l' d' m}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stIdle) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stIdle)) refl s))
-- head stBusy : fires one of four api sends
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockAnnouncement} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lnsWann1 a , succVN-inv (decLNs-src l d (lnsHead LNp.stBusy)) s , aLNs l d (lnsHead LNp.stBusy) (lnsWann1 a) refl (ceqLN-s-busyAnn l d)
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lnsWoff1 a , succVN-inv (decLNs-src l d (lnsHead LNp.stBusy)) s , aLNs l d (lnsHead LNp.stBusy) (lnsWoff1 a) refl (ceqLN-s-busyOff l d)
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNBlockTxsOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lnsWtxs1 a , succVN-inv (decLNs-src l d (lnsHead LNp.stBusy)) s , aLNs l d (lnsHead LNp.stBusy) (lnsWtxs1 a) refl (ceqLN-s-busyTxs l d)
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNVotesOffer} {a} s with step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lnsWvot1 a , succVN-inv (decLNs-src l d (lnsHead LNp.stBusy)) s , aLNs l d (lnsHead LNp.stBusy) (lnsWvot1 a) refl (ceqLN-s-busyVot l d)
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNRequestNext} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' sendLNDone}        s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockAnnouncement} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockOffer}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNBlockTxsOffer} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.apiLNev l' d' recvLNVotesOffer}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.sendLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.receiveLN l' d'}  s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
decLNs-src-ev-inv l d (lnsHead LNp.stBusy) {e₁ = LNp.doneLN l' d'}     s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsHead LNp.stBusy)) refl s))
-- head stDone : ret, no visible step
decLNs-src-ev-inv l d (lnsHead LNp.stDone) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf lnsDone1 : fires doneLN → lnsSil stDone
decLNs-src-ev-inv l d lnsDone1 {e₁ = LNp.doneLN l' d'} {a} s with step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s
... | offer with LNp.LNEv-≟ (_ , LNp.doneLN l d) (_ , LNp.doneLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = lnsSil LNp.stDone , sym (just-injective offer) , aLNs l d lnsDone1 (lnsSil LNp.stDone) refl (ceqLN-s-ddone l d)
decLNs-src-ev-inv l d lnsDone1 {e₁ = LNp.sendLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
decLNs-src-ev-inv l d lnsDone1 {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
decLNs-src-ev-inv l d lnsDone1 {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d lnsDone1) (hlnsDone1 l d) s))
-- send leaf lnsWann1 : fires sendLN (MsgLNBlockAnnouncement h) → lnsSil stIdle
decLNs-src-ev-inv l d (lnsWann1 h) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lnsSil LNp.stIdle , sym (just-injective offer) , aLNs l d (lnsWann1 h) (lnsSil LNp.stIdle) refl (ceqLN-s-wann l d h)
decLNs-src-ev-inv l d (lnsWann1 h) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
decLNs-src-ev-inv l d (lnsWann1 h) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
decLNs-src-ev-inv l d (lnsWann1 h) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWann1 h)) (hlnsWann1 l d h) s))
-- send leaf lnsWoff1 : fires sendLN (MsgLNBlockOffer q) → lnsSil stIdle
decLNs-src-ev-inv l d (lnsWoff1 q) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lnsSil LNp.stIdle , sym (just-injective offer) , aLNs l d (lnsWoff1 q) (lnsSil LNp.stIdle) refl (ceqLN-s-woff l d q)
decLNs-src-ev-inv l d (lnsWoff1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
decLNs-src-ev-inv l d (lnsWoff1 q) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
decLNs-src-ev-inv l d (lnsWoff1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWoff1 q)) (hlnsWoff1 l d q) s))
-- send leaf lnsWtxs1 : fires sendLN (MsgLNBlockTxsOffer q) → lnsSil stIdle
decLNs-src-ev-inv l d (lnsWtxs1 q) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lnsSil LNp.stIdle , sym (just-injective offer) , aLNs l d (lnsWtxs1 q) (lnsSil LNp.stIdle) refl (ceqLN-s-wtxs l d q)
decLNs-src-ev-inv l d (lnsWtxs1 q) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
decLNs-src-ev-inv l d (lnsWtxs1 q) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
decLNs-src-ev-inv l d (lnsWtxs1 q) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWtxs1 q)) (hlnsWtxs1 l d q) s))
-- send leaf lnsWvot1 : fires sendLN (MsgLNVotesOffer vs) → lnsSil stIdle
decLNs-src-ev-inv l d (lnsWvot1 vs) {e₁ = LNp.sendLN l' d'} {a = val} s with step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s
... | offer with LNp.LNEv-≟ (_ , LNp.sendLN l d) (_ , LNp.sendLN l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lnsSil LNp.stIdle , sym (just-injective offer) , aLNs l d (lnsWvot1 vs) (lnsSil LNp.stIdle) refl (ceqLN-s-wvot l d vs)
decLNs-src-ev-inv l d (lnsWvot1 vs) {e₁ = LNp.receiveLN l' d'} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
decLNs-src-ev-inv l d (lnsWvot1 vs) {e₁ = LNp.apiLNev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
decLNs-src-ev-inv l d (lnsWvot1 vs) {e₁ = LNp.doneLN l' d'}    s = ⊥-elim (nothing-absurd (step-target-LN (decLNs-src l d (lnsWvot1 vs)) (hlnsWvot1 l d vs) s))
-- loop re-entry : sil, no visible step
decLNs-src-ev-inv l d (lnsSil st) s with LNL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

------------------------------------------------------------------------
-- G2 (io) — LeiosFetch CLIENT / SERVER visible-event inversions.
-- LF carries io (`sendLF`/`receiveLF` → input/output) + api (`apiLFev`) +
-- `doneLF`.  Richest peer (6 states, 14 api tags).  Value carriers: Block
-- (single) splits like CS; `List Tx`/`List VoteBlob` bare lists via explicit
-- `≡-dec`; `Block × List Tx` products via the pinned `DecEqI.DecEq-×`.
------------------------------------------------------------------------

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

-- LF iter-force offer: `succVF q at a` is exactly the offered continuation
succVF-just : (q : LFProc) (at : AnyTypes LFp.LFEv) (a : proj₁ at) {P′ : LFProc}
  → vis-ofF (PTree.force q) at a ≡ just P′ → succVF q at a ≡ P′
succVF-just q at a eq with vis-ofF (PTree.force q) at a
succVF-just q at a refl | just t = refl
succVF-just q at a ()   | nothing

-- LF: a visible source step lands on `succVF q (X , e) a`
succVF-inv : (q : LFProc) {X : Set 0ℓ} {e : LFp.LFEv X} {a : X} {P′ : LFProc}
  → q LFL.─[ LFL.ev (LFL.evl (LFL.evLabel X e a)) ]─► P′
  → P′ ≡ succVF q (X , e) a
succVF-inv q {X} {e} {a} step with LFL.ev-inv step
... | v , τc , feq , veq =
      sym (succVF-just q (X , e) a (trans (cong (λ n → vis-ofF n (X , e) a) feq) veq))

-- LF: the fired offer entry at a KNOWN force
step-target-LF : (q : LFProc)
    {V : (at : AnyTypes LFp.LFEv) → ContinueType at (Maybe LFProc)}
    {T : (i : AnyTypes (ExtI LFp.LFEv)) → ContinueType i (Maybe LFProc)}
    {X : Set 0ℓ} {e : LFp.LFEv X} {a : X} {P′ : LFProc}
  → PTree.force q ≡ react V T
  → q LFL.─[ LFL.ev (LFL.evl (LFL.evLabel X e a)) ]─► P′
  → V (X , e) a ≡ just P′
step-target-LF q {V} {T} {X} {e} {a} feq step with LFL.ev-inv step
... | v , τc , feq′ , veq with react-injective (trans (sym feq) feq′)
...   | Veq , _ = trans (cong (λ w → w (X , e) a) Veq) veq

-- a renamed Net_Api event whose ι-preimage is an LF source event is the ι-image
ιLF-inv-shape : {X : Set 0ℓ} {e₂ : Net_Api Payload X} {e₁ : LFp.LFEv X}
  → ιLF⁻¹ e₂ ≡ just e₁ → e₂ ≡ ιLF e₁
ιLF-inv-shape {e₂ = input  _ _ N2N_ChainSync}    ()
ιLF-inv-shape {e₂ = input  _ _ N2N_BlockFetch}   ()
ιLF-inv-shape {e₂ = input  _ _ N2N_TxSubmission} ()
ιLF-inv-shape {e₂ = input  _ _ N2N_KeepAlive}    ()
ιLF-inv-shape {e₂ = input  _ _ N2N_LeiosNotify}  ()
ιLF-inv-shape {e₂ = input  _ _ N2N_LeiosFetch}   refl = refl
ιLF-inv-shape {e₂ = output _ _ N2N_ChainSync}    ()
ιLF-inv-shape {e₂ = output _ _ N2N_BlockFetch}   ()
ιLF-inv-shape {e₂ = output _ _ N2N_TxSubmission} ()
ιLF-inv-shape {e₂ = output _ _ N2N_KeepAlive}    ()
ιLF-inv-shape {e₂ = output _ _ N2N_LeiosNotify}  ()
ιLF-inv-shape {e₂ = output _ _ N2N_LeiosFetch}   refl = refl
ιLF-inv-shape {e₂ = done   _ _ N2N_ChainSync}    ()
ιLF-inv-shape {e₂ = done   _ _ N2N_BlockFetch}   ()
ιLF-inv-shape {e₂ = done   _ _ N2N_TxSubmission} ()
ιLF-inv-shape {e₂ = done   _ _ N2N_KeepAlive}    ()
ιLF-inv-shape {e₂ = done   _ _ N2N_LeiosNotify}  ()
ιLF-inv-shape {e₂ = done   _ _ N2N_LeiosFetch}   refl = refl
ιLF-inv-shape {e₂ = apiLF  _ _ _} refl = refl
ιLF-inv-shape {e₂ = apiCS  _ _ _} ()
ιLF-inv-shape {e₂ = apiBF  _ _ _} ()
ιLF-inv-shape {e₂ = apiKA  _ _ _} ()
ιLF-inv-shape {e₂ = apiTS  _ _ _} ()
ιLF-inv-shape {e₂ = apiLN  _ _ _} ()
ιLF-inv-shape {e₂ = sndmsg _ _ _} ()
ιLF-inv-shape {e₂ = rcvmsg _ _ _} ()
ιLF-inv-shape {e₂ = tx     _ _ _} ()
ιLF-inv-shape {e₂ = sndack _ _ _} ()
ιLF-inv-shape {e₂ = rcvack _ _ _} ()
ιLF-inv-shape {e₂ = ack    _ _ _} ()
ιLF-inv-shape {e₂ = break  _}     ()

-- package a `lfCnxt`/`lfSnxt` agreement into the abstract LF step
aLFc : (l : Link) (d : Dir) (pos pos′ : LFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.lfCfin (coarsenLFc pos) ≡ false
  → NS.lfCnxt l d (coarsenLFc pos) (X , e) a ≡ just (coarsenLFc pos′)
  → absLFc l d pos ─[ ev (evl (evLabel X e a)) ]─► absLFc l d pos′
aLFc l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenLFc pos) finEq ceq
aLFs : (l : Link) (d : Dir) (pos pos′ : LFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.lfSfin (coarsenLFs pos) ≡ false
  → NS.lfSnxt l d (coarsenLFs pos) (X , e) a ≡ just (coarsenLFs pos′)
  → absLFs l d pos ─[ ev (evl (evLabel X e a)) ]─► absLFs l d pos′
aLFs l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenLFs pos) finEq ceq

-- per-firing coarsen∘nxt commutations (CLIENT)
ceqLF-c-reqBlk : ∀ {a} (l : Link) (d : Dir)
  → NS.lfCnxt l d NS.lfcIdle (_ , apiLF l d sendLFBlockRequest) a ≡ just (NS.lfcWblk a)
ceqLF-c-reqBlk l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-c-reqTxs : ∀ {a} (l : Link) (d : Dir)
  → NS.lfCnxt l d NS.lfcIdle (_ , apiLF l d sendLFBlockTxsRequest) a ≡ just (NS.lfcWtxs a)
ceqLF-c-reqTxs l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-c-reqVot : ∀ {a} (l : Link) (d : Dir)
  → NS.lfCnxt l d NS.lfcIdle (_ , apiLF l d sendLFVotesRequest) a ≡ just (NS.lfcWvot a)
ceqLF-c-reqVot l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-c-reqRng : ∀ {a} (l : Link) (d : Dir)
  → NS.lfCnxt l d NS.lfcIdle (_ , apiLF l d sendLFBlockRangeRequest) a ≡ just (NS.lfcWrng a)
ceqLF-c-reqRng l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-c-reqDone : ∀ {a} (l : Link) (d : Dir)
  → NS.lfCnxt l d NS.lfcIdle (_ , apiLF l d sendLFDone) a ≡ just (NS.lfcWdone)
ceqLF-c-reqDone l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-c-blkRecv : ∀ {t0 md ln} (l : Link) (d : Dir) (b : _)
  → NS.lfCnxt l d NS.lfcBlk (_ , output l d N2N_LeiosFetch)
      (t0 , md , ln , leiosFetch (MsgLFBlock b)) ≡ just (NS.lfcRblk b)
ceqLF-c-blkRecv l d b rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-c-btxRecv : ∀ {t0 md ln} (l : Link) (d : Dir) (ts : _)
  → NS.lfCnxt l d NS.lfcBtx (_ , output l d N2N_LeiosFetch)
      (t0 , md , ln , leiosFetch (MsgLFBlockTxs ts)) ≡ just (NS.lfcRbtx ts)
ceqLF-c-btxRecv l d ts rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-c-votRecv : ∀ {t0 md ln} (l : Link) (d : Dir) (vs : _)
  → NS.lfCnxt l d NS.lfcVot (_ , output l d N2N_LeiosFetch)
      (t0 , md , ln , leiosFetch (MsgLFVoteDelivery vs)) ≡ just (NS.lfcRvot vs)
ceqLF-c-votRecv l d vs rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-c-rngNext : ∀ {t0 md ln} (l : Link) (d : Dir) (b : _) (ts : _)
  → NS.lfCnxt l d NS.lfcRng (_ , output l d N2N_LeiosFetch)
      (t0 , md , ln , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ just (NS.lfcRnextRng (b , ts))
ceqLF-c-rngNext l d b ts rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-c-rngLast : ∀ {t0 md ln} (l : Link) (d : Dir) (b : _) (ts : _)
  → NS.lfCnxt l d NS.lfcRng (_ , output l d N2N_LeiosFetch)
      (t0 , md , ln , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ just (NS.lfcRlastRng (b , ts))
ceqLF-c-rngLast l d b ts rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-c-rblk : (l : Link) (d : Dir) (b : _)
  → NS.lfCnxt l d (NS.lfcRblk b) (_ , apiLF l d recvLFBlock) b ≡ just NS.lfcIdle
ceqLF-c-rblk l d b rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl b = refl
ceqLF-c-rbtx : (l : Link) (d : Dir) (ts : _)
  → NS.lfCnxt l d (NS.lfcRbtx ts) (_ , apiLF l d recvLFBlockTxs) ts ≡ just NS.lfcIdle
ceqLF-c-rbtx l d ts rewrite ≟-yes-refl l | ≟-yes-refl d with ≡-dec _≟_ ts ts
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)
ceqLF-c-rvot : (l : Link) (d : Dir) (vs : _)
  → NS.lfCnxt l d (NS.lfcRvot vs) (_ , apiLF l d recvLFVoteDelivery) vs ≡ just NS.lfcIdle
ceqLF-c-rvot l d vs rewrite ≟-yes-refl l | ≟-yes-refl d with ≡-dec _≟_ vs vs
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)
ceqLF-c-rnext : (l : Link) (d : Dir) (b : _) (ts : _)
  → NS.lfCnxt l d (NS.lfcRnextRng (b , ts)) (_ , apiLF l d recvLFRangeBlock) (b , ts) ≡ just NS.lfcRng
ceqLF-c-rnext l d b ts rewrite ≟-yes-refl l | ≟-yes-refl d with _≟_ ⦃ DecEqI.DecEq-× ⦄ (b , ts) (b , ts)
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)
ceqLF-c-rlast : (l : Link) (d : Dir) (b : _) (ts : _)
  → NS.lfCnxt l d (NS.lfcRlastRng (b , ts)) (_ , apiLF l d recvLFRangeBlock) (b , ts) ≡ just NS.lfcIdle
ceqLF-c-rlast l d b ts rewrite ≟-yes-refl l | ≟-yes-refl d with _≟_ ⦃ DecEqI.DecEq-× ⦄ (b , ts) (b , ts)
... | yes _  = refl
... | no ¬p = ⊥-elim (¬p refl)
ceqLF-c-wblk : (l : Link) (d : Dir) (pt : _)
  → NS.lfCnxt l d (NS.lfcWblk pt) (_ , input l d N2N_LeiosFetch)
      (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) ≡ just NS.lfcBlk
ceqLF-c-wblk l d pt rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) = refl
ceqLF-c-wtxs : (l : Link) (d : Dir) (pt : _) (bm : _)
  → NS.lfCnxt l d (NS.lfcWtxs (pt , bm)) (_ , input l d N2N_LeiosFetch)
      (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ just NS.lfcBtx
ceqLF-c-wtxs l d pt bm rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) = refl
ceqLF-c-wvot : (l : Link) (d : Dir) (vs : _)
  → NS.lfCnxt l d (NS.lfcWvot vs) (_ , input l d N2N_LeiosFetch)
      (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) ≡ just NS.lfcVot
ceqLF-c-wvot l d vs rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) = refl
ceqLF-c-wrng : (l : Link) (d : Dir) (r : _)
  → NS.lfCnxt l d (NS.lfcWrng r) (_ , input l d N2N_LeiosFetch)
      (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) ≡ just NS.lfcRng
ceqLF-c-wrng l d r rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) = refl
ceqLF-c-wdone : (l : Link) (d : Dir)
  → NS.lfCnxt l d (NS.lfcWdone) (_ , input l d N2N_LeiosFetch)
      (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFDone)) ≡ just NS.lfcTerm
ceqLF-c-wdone l d  rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFDone)) = refl
-- per-firing coarsen∘nxt commutations (SERVER)
ceqLF-s-reqBlk : ∀ {t0 md ln} (l : Link) (d : Dir) (pt : _)
  → NS.lfSnxt l d NS.lfsIdle (_ , output l d N2N_LeiosFetch)
      (t0 , md , ln , leiosFetch (MsgLFBlockRequest pt)) ≡ just NS.lfsBlk
ceqLF-s-reqBlk l d pt with l ≟ l | d ≟ d
... | yes refl | yes refl = refl
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes _    | no ¬p    = ⊥-elim (¬p refl)
ceqLF-s-reqTxs : ∀ {t0 md ln} (l : Link) (d : Dir) (pt : _) (bm : _)
  → NS.lfSnxt l d NS.lfsIdle (_ , output l d N2N_LeiosFetch)
      (t0 , md , ln , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ just NS.lfsBtx
ceqLF-s-reqTxs l d pt bm with l ≟ l | d ≟ d
... | yes refl | yes refl = refl
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes _    | no ¬p    = ⊥-elim (¬p refl)
ceqLF-s-reqVot : ∀ {t0 md ln} (l : Link) (d : Dir) (vs : _)
  → NS.lfSnxt l d NS.lfsIdle (_ , output l d N2N_LeiosFetch)
      (t0 , md , ln , leiosFetch (MsgLFVotesRequest vs)) ≡ just NS.lfsVot
ceqLF-s-reqVot l d vs with l ≟ l | d ≟ d
... | yes refl | yes refl = refl
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes _    | no ¬p    = ⊥-elim (¬p refl)
ceqLF-s-reqRng : ∀ {t0 md ln} (l : Link) (d : Dir) (r : _)
  → NS.lfSnxt l d NS.lfsIdle (_ , output l d N2N_LeiosFetch)
      (t0 , md , ln , leiosFetch (MsgLFBlockRangeRequest r)) ≡ just NS.lfsRng
ceqLF-s-reqRng l d r with l ≟ l | d ≟ d
... | yes refl | yes refl = refl
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes _    | no ¬p    = ⊥-elim (¬p refl)
ceqLF-s-reqDone : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.lfSnxt l d NS.lfsIdle (_ , output l d N2N_LeiosFetch)
      (t0 , md , ln , leiosFetch (MsgLFDone)) ≡ just NS.lfsDone
ceqLF-s-reqDone l d with l ≟ l | d ≟ d
... | yes refl | yes refl = refl
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes _    | no ¬p    = ⊥-elim (¬p refl)
ceqLF-s-blk : ∀ {a} (l : Link) (d : Dir)
  → NS.lfSnxt l d NS.lfsBlk (_ , apiLF l d sendLFBlock) a ≡ just (NS.lfsWblk a)
ceqLF-s-blk l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-s-btx : ∀ {a} (l : Link) (d : Dir)
  → NS.lfSnxt l d NS.lfsBtx (_ , apiLF l d sendLFBlockTxs) a ≡ just (NS.lfsWtxs a)
ceqLF-s-btx l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-s-vot : ∀ {a} (l : Link) (d : Dir)
  → NS.lfSnxt l d NS.lfsVot (_ , apiLF l d sendLFVoteDelivery) a ≡ just (NS.lfsWvot a)
ceqLF-s-vot l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-s-next : ∀ {a} (l : Link) (d : Dir)
  → NS.lfSnxt l d NS.lfsRng (_ , apiLF l d sendLFNextBlockAndTxsInRange) a ≡ just (NS.lfsWnext a)
ceqLF-s-next l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-s-last : ∀ {a} (l : Link) (d : Dir)
  → NS.lfSnxt l d NS.lfsRng (_ , apiLF l d sendLFLastBlockAndTxsInRange) a ≡ just (NS.lfsWlast a)
ceqLF-s-last l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqLF-s-wblk : (l : Link) (d : Dir) (b : _)
  → NS.lfSnxt l d (NS.lfsWblk b) (_ , input l d N2N_LeiosFetch)
      (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) ≡ just NS.lfsIdle
ceqLF-s-wblk l d b rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) = refl
ceqLF-s-wtxs : (l : Link) (d : Dir) (ts : _)
  → NS.lfSnxt l d (NS.lfsWtxs ts) (_ , input l d N2N_LeiosFetch)
      (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) ≡ just NS.lfsIdle
ceqLF-s-wtxs l d ts rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) = refl
ceqLF-s-wvot : (l : Link) (d : Dir) (vs : _)
  → NS.lfSnxt l d (NS.lfsWvot vs) (_ , input l d N2N_LeiosFetch)
      (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) ≡ just NS.lfsIdle
ceqLF-s-wvot l d vs rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) = refl
ceqLF-s-wnext : (l : Link) (d : Dir) (b : _) (ts : _)
  → NS.lfSnxt l d (NS.lfsWnext (b , ts)) (_ , input l d N2N_LeiosFetch)
      (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ just NS.lfsRng
ceqLF-s-wnext l d b ts rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) = refl
ceqLF-s-wlast : (l : Link) (d : Dir) (b : _) (ts : _)
  → NS.lfSnxt l d (NS.lfsWlast (b , ts)) (_ , input l d N2N_LeiosFetch)
      (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ just NS.lfsIdle
ceqLF-s-wlast l d b ts rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) = refl
ceqLF-s-ddone : ∀ {a} (l : Link) (d : Dir)
  → NS.lfSnxt l d NS.lfsDone (_ , done l d N2N_LeiosFetch) a ≡ just NS.lfsTerm
ceqLF-s-ddone l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
-- receive-firing bridges — CLIENT
brLFBlk : (l : Link) (d : Dir) (b : _) (t0 : _) (md : _) (ln : _)
  → succVF (decLFc-src l d (lfcHead LFp.stBlock)) (_ , LFp.receiveLF l d)
      (t0 , md , ln , leiosFetch (MsgLFBlock b)) ≡ decLFc-src l d (lfcRblk1 b)
brLFBlk l d b t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brLFBtx : (l : Link) (d : Dir) (ts : _) (t0 : _) (md : _) (ln : _)
  → succVF (decLFc-src l d (lfcHead LFp.stBlockTxs)) (_ , LFp.receiveLF l d)
      (t0 , md , ln , leiosFetch (MsgLFBlockTxs ts)) ≡ decLFc-src l d (lfcRbtx1 ts)
brLFBtx l d ts t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brLFVot : (l : Link) (d : Dir) (vs : _) (t0 : _) (md : _) (ln : _)
  → succVF (decLFc-src l d (lfcHead LFp.stVotes)) (_ , LFp.receiveLF l d)
      (t0 , md , ln , leiosFetch (MsgLFVoteDelivery vs)) ≡ decLFc-src l d (lfcRvot1 vs)
brLFVot l d vs t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brLFNext : (l : Link) (d : Dir) (b : _) (ts : _) (t0 : _) (md : _) (ln : _)
  → succVF (decLFc-src l d (lfcHead LFp.stBlockRange)) (_ , LFp.receiveLF l d)
      (t0 , md , ln , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ decLFc-src l d (lfcRnext1 b ts)
brLFNext l d b ts t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brLFLast : (l : Link) (d : Dir) (b : _) (ts : _) (t0 : _) (md : _) (ln : _)
  → succVF (decLFc-src l d (lfcHead LFp.stBlockRange)) (_ , LFp.receiveLF l d)
      (t0 , md , ln , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ decLFc-src l d (lfcRlast1 b ts)
brLFLast l d b ts t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
-- receive-firing bridges — SERVER
brLFsReqBlk : (l : Link) (d : Dir) (pt : _) (t0 : _) (md : _) (ln : _)
  → succVF (decLFs-src l d (lfsHead LFp.stIdle)) (_ , LFp.receiveLF l d)
      (t0 , md , ln , leiosFetch (MsgLFBlockRequest pt)) ≡ decLFs-src l d (lfsSil LFp.stBlock)
brLFsReqBlk l d pt t0 md ln with l ≟ l | d ≟ d
... | yes refl | yes refl = refl
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes _    | no ¬p    = ⊥-elim (¬p refl)
brLFsReqTxs : (l : Link) (d : Dir) (pt : _) (bm : _) (t0 : _) (md : _) (ln : _)
  → succVF (decLFs-src l d (lfsHead LFp.stIdle)) (_ , LFp.receiveLF l d)
      (t0 , md , ln , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ decLFs-src l d (lfsSil LFp.stBlockTxs)
brLFsReqTxs l d pt bm t0 md ln with l ≟ l | d ≟ d
... | yes refl | yes refl = refl
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes _    | no ¬p    = ⊥-elim (¬p refl)
brLFsReqVot : (l : Link) (d : Dir) (vs : _) (t0 : _) (md : _) (ln : _)
  → succVF (decLFs-src l d (lfsHead LFp.stIdle)) (_ , LFp.receiveLF l d)
      (t0 , md , ln , leiosFetch (MsgLFVotesRequest vs)) ≡ decLFs-src l d (lfsSil LFp.stVotes)
brLFsReqVot l d vs t0 md ln with l ≟ l | d ≟ d
... | yes refl | yes refl = refl
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes _    | no ¬p    = ⊥-elim (¬p refl)
brLFsReqRng : (l : Link) (d : Dir) (r : _) (t0 : _) (md : _) (ln : _)
  → succVF (decLFs-src l d (lfsHead LFp.stIdle)) (_ , LFp.receiveLF l d)
      (t0 , md , ln , leiosFetch (MsgLFBlockRangeRequest r)) ≡ decLFs-src l d (lfsSil LFp.stBlockRange)
brLFsReqRng l d r t0 md ln with l ≟ l | d ≟ d
... | yes refl | yes refl = refl
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes _    | no ¬p    = ⊥-elim (¬p refl)
brLFsReqDone : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVF (decLFs-src l d (lfsHead LFp.stIdle)) (_ , LFp.receiveLF l d)
      (t0 , md , ln , leiosFetch (MsgLFDone)) ≡ decLFs-src l d (lfsDone1)
brLFsReqDone l d t0 md ln with l ≟ l | d ≟ d
... | yes refl | yes refl = refl
... | no ¬p    | _        = ⊥-elim (¬p refl)
... | yes _    | no ¬p    = ⊥-elim (¬p refl)
-- SOURCE-side per-position ev inversion — LeiosFetch CLIENT
decLFc-src-ev-inv : (l : Link) (d : Dir) (pos : LFcPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {P′ : LFProc}
  → decLFc-src l d pos LFL.─[ LFL.ev (LFL.evl (LFL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ LFcPos ] (P′ ≡ decLFc-src l d pos′)
      × (absLFc l d pos ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► absLFc l d pos′)
-- head stIdle : five api requests
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfcWblk1 a , succVF-inv (decLFc-src l d (lfcHead LFp.stIdle)) s , aLFc l d (lfcHead LFp.stIdle) (lfcWblk1 a) refl (ceqLF-c-reqBlk l d)
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfcWtxs1 a , succVF-inv (decLFc-src l d (lfcHead LFp.stIdle)) s , aLFc l d (lfcHead LFp.stIdle) (lfcWtxs1 a) refl (ceqLF-c-reqTxs l d)
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfcWvot1 a , succVF-inv (decLFc-src l d (lfcHead LFp.stIdle)) s , aLFc l d (lfcHead LFp.stIdle) (lfcWvot1 a) refl (ceqLF-c-reqVot l d)
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfcWrng1 a , succVF-inv (decLFc-src l d (lfcHead LFp.stIdle)) s , aLFc l d (lfcHead LFp.stIdle) (lfcWrng1 a) refl (ceqLF-c-reqRng l d)
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFDone} {a} s with step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfcDone1 , succVF-inv (decLFc-src l d (lfcHead LFp.stIdle)) s , aLFc l d (lfcHead LFp.stIdle) (lfcDone1) refl (ceqLF-c-reqDone l d)
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stIdle) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stIdle)) refl s))
-- head stBlock / stBlockTxs / stVotes / stBlockRange : wire receives
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlock b)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfcRblk1 b , trans (succVF-inv (decLFc-src l d (lfcHead LFp.stBlock)) s) (brLFBlk l d b t0 md ln) , aLFc l d (lfcHead LFp.stBlock) (lfcRblk1 b) refl (ceqLF-c-blkRecv {t0} {md} {ln} l d b)
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlock) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlock)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxs ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfcRbtx1 ts , trans (succVF-inv (decLFc-src l d (lfcHead LFp.stBlockTxs)) s) (brLFBtx l d ts t0 md ln) , aLFc l d (lfcHead LFp.stBlockTxs) (lfcRbtx1 ts) refl (ceqLF-c-btxRecv {t0} {md} {ln} l d ts)
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockTxs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockTxs)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVoteDelivery vs)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfcRvot1 vs , trans (succVF-inv (decLFc-src l d (lfcHead LFp.stVotes)) s) (brLFVot l d vs t0 md ln) , aLFc l d (lfcHead LFp.stVotes) (lfcRvot1 vs) refl (ceqLF-c-votRecv {t0} {md} {ln} l d vs)
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stVotes) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stVotes)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfcRnext1 b ts , trans (succVF-inv (decLFc-src l d (lfcHead LFp.stBlockRange)) s) (brLFNext l d b ts t0 md ln) , aLFc l d (lfcHead LFp.stBlockRange) (lfcRnext1 b ts) refl (ceqLF-c-rngNext {t0} {md} {ln} l d b ts)
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)} s with step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfcRlast1 b ts , trans (succVF-inv (decLFc-src l d (lfcHead LFp.stBlockRange)) s) (brLFLast l d b ts t0 md ln) , aLFc l d (lfcHead LFp.stBlockRange) (lfcRlast1 b ts) refl (ceqLF-c-rngLast {t0} {md} {ln} l d b ts)
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFDone)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
decLFc-src-ev-inv l d (lfcHead LFp.stBlockRange) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcHead LFp.stBlockRange)) refl s))
-- head stDone : ret
decLFc-src-ev-inv l d (lfcHead LFp.stDone) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- recv leaves
decLFc-src-ev-inv l d (lfcRblk1 b) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ b
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfcSil LFp.stIdle , sym (just-injective offer) , aLFc l d (lfcRblk1 b) (lfcSil LFp.stIdle) refl (ceqLF-c-rblk l d b)
decLFc-src-ev-inv l d (lfcRblk1 b) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-src-ev-inv l d (lfcRblk1 b) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-src-ev-inv l d (lfcRblk1 b) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRblk1 b)) (hlfcRblk1 l d b) s))
decLFc-src-ev-inv l d (lfcRbtx1 ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFBlockTxs) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val ts
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfcSil LFp.stIdle , sym (just-injective offer) , aLFc l d (lfcRbtx1 ts) (lfcSil LFp.stIdle) refl (ceqLF-c-rbtx l d ts)
decLFc-src-ev-inv l d (lfcRbtx1 ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-src-ev-inv l d (lfcRbtx1 ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-src-ev-inv l d (lfcRbtx1 ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRbtx1 ts)) (hlfcRbtx1 l d ts) s))
decLFc-src-ev-inv l d (lfcRvot1 vs) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFVoteDelivery) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with ≡-dec _≟_ val vs
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfcSil LFp.stIdle , sym (just-injective offer) , aLFc l d (lfcRvot1 vs) (lfcSil LFp.stIdle) refl (ceqLF-c-rvot l d vs)
decLFc-src-ev-inv l d (lfcRvot1 vs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-src-ev-inv l d (lfcRvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-src-ev-inv l d (lfcRvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRvot1 vs)) (hlfcRvot1 l d vs) s))
decLFc-src-ev-inv l d (lfcRnext1 b ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFRangeBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEqI.DecEq-× ⦄ val (b , ts)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfcSil LFp.stBlockRange , sym (just-injective offer) , aLFc l d (lfcRnext1 b ts) (lfcSil LFp.stBlockRange) refl (ceqLF-c-rnext l d b ts)
decLFc-src-ev-inv l d (lfcRnext1 b ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-src-ev-inv l d (lfcRnext1 b ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-src-ev-inv l d (lfcRnext1 b ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRnext1 b ts)) (hlfcRnext1 l d b ts) s))
decLFc-src-ev-inv l d (lfcRlast1 b ts) {e₁ = LFp.apiLFev l' d' m} {a = val} s with step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.apiLFev l d recvLFRangeBlock) (_ , LFp.apiLFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEqI.DecEq-× ⦄ val (b , ts)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfcSil LFp.stIdle , sym (just-injective offer) , aLFc l d (lfcRlast1 b ts) (lfcSil LFp.stIdle) refl (ceqLF-c-rlast l d b ts)
decLFc-src-ev-inv l d (lfcRlast1 b ts) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
decLFc-src-ev-inv l d (lfcRlast1 b ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
decLFc-src-ev-inv l d (lfcRlast1 b ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcRlast1 b ts)) (hlfcRlast1 l d b ts) s))
-- send leaves
decLFc-src-ev-inv l d (lfcWblk1 pt) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfcSil LFp.stBlock , sym (just-injective offer) , aLFc l d (lfcWblk1 pt) (lfcSil LFp.stBlock) refl (ceqLF-c-wblk l d pt)
decLFc-src-ev-inv l d (lfcWblk1 pt) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-src-ev-inv l d (lfcWblk1 pt) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-src-ev-inv l d (lfcWblk1 pt) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWblk1 pt)) (hlfcWblk1 l d pt) s))
decLFc-src-ev-inv l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfcSil LFp.stBlockTxs , sym (just-injective offer) , aLFc l d (lfcWtxs1 (pt , bm)) (lfcSil LFp.stBlockTxs) refl (ceqLF-c-wtxs l d pt bm)
decLFc-src-ev-inv l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-src-ev-inv l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-src-ev-inv l d (lfcWtxs1 (pt , bm)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWtxs1 (pt , bm))) (hlfcWtxs1 l d (pt , bm)) s))
decLFc-src-ev-inv l d (lfcWvot1 vs) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfcSil LFp.stVotes , sym (just-injective offer) , aLFc l d (lfcWvot1 vs) (lfcSil LFp.stVotes) refl (ceqLF-c-wvot l d vs)
decLFc-src-ev-inv l d (lfcWvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-src-ev-inv l d (lfcWvot1 vs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-src-ev-inv l d (lfcWvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWvot1 vs)) (hlfcWvot1 l d vs) s))
decLFc-src-ev-inv l d (lfcWrng1 r) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfcSil LFp.stBlockRange , sym (just-injective offer) , aLFc l d (lfcWrng1 r) (lfcSil LFp.stBlockRange) refl (ceqLF-c-wrng l d r)
decLFc-src-ev-inv l d (lfcWrng1 r) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-src-ev-inv l d (lfcWrng1 r) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-src-ev-inv l d (lfcWrng1 r) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d (lfcWrng1 r)) (hlfcWrng1 l d r) s))
decLFc-src-ev-inv l d lfcDone1 {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfcSil LFp.stDone , sym (just-injective offer) , aLFc l d lfcDone1 (lfcSil LFp.stDone) refl (ceqLF-c-wdone l d)
decLFc-src-ev-inv l d lfcDone1 {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
decLFc-src-ev-inv l d lfcDone1 {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
decLFc-src-ev-inv l d lfcDone1 {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFc-src l d lfcDone1) (hlfcDone1 l d) s))
-- loop re-entry
decLFc-src-ev-inv l d (lfcSil st) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- SOURCE-side per-position ev inversion — LeiosFetch SERVER
decLFs-src-ev-inv : (l : Link) (d : Dir) (pos : LFsPos)
    {X : Set 0ℓ} {e₁ : LFp.LFEv X} {a : X} {P′ : LFProc}
  → decLFs-src l d pos LFL.─[ LFL.ev (LFL.evl (LFL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ LFsPos ] (P′ ≡ decLFs-src l d pos′)
      × (absLFs l d pos ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► absLFs l d pos′)
-- head stIdle : five wire requests (4 loops + done)
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRequest pt)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfsSil LFp.stBlock , trans (succVF-inv (decLFs-src l d (lfsHead LFp.stIdle)) s) (brLFsReqBlk l d pt t0 md ln) , aLFs l d (lfsHead LFp.stIdle) (lfsSil LFp.stBlock) refl (ceqLF-s-reqBlk {t0} {md} {ln} l d pt)
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxsRequest pt bm)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfsSil LFp.stBlockTxs , trans (succVF-inv (decLFs-src l d (lfsHead LFp.stIdle)) s) (brLFsReqTxs l d pt bm t0 md ln) , aLFs l d (lfsHead LFp.stIdle) (lfsSil LFp.stBlockTxs) refl (ceqLF-s-reqTxs {t0} {md} {ln} l d pt bm)
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVotesRequest vs)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfsSil LFp.stVotes , trans (succVF-inv (decLFs-src l d (lfsHead LFp.stIdle)) s) (brLFsReqVot l d vs t0 md ln) , aLFs l d (lfsHead LFp.stIdle) (lfsSil LFp.stVotes) refl (ceqLF-s-reqVot {t0} {md} {ln} l d vs)
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRangeRequest r)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfsSil LFp.stBlockRange , trans (succVF-inv (decLFs-src l d (lfsHead LFp.stIdle)) s) (brLFsReqRng l d r t0 md ln) , aLFs l d (lfsHead LFp.stIdle) (lfsSil LFp.stBlockRange) refl (ceqLF-s-reqRng {t0} {md} {ln} l d r)
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFDone)} s with step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfsDone1 , trans (succVF-inv (decLFs-src l d (lfsHead LFp.stIdle)) s) (brLFsReqDone l d t0 md ln) , aLFs l d (lfsHead LFp.stIdle) (lfsDone1) refl (ceqLF-s-reqDone {t0} {md} {ln} l d)
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , chainSync x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stIdle) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stIdle)) refl s))
-- head stBlock / stBlockTxs / stVotes / stBlockRange : api sends
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlock} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfsWblk1 a , succVF-inv (decLFs-src l d (lfsHead LFp.stBlock)) s , aLFs l d (lfsHead LFp.stBlock) (lfsWblk1 a) refl (ceqLF-s-blk l d)
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlock) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlock)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfsWtxs1 a , succVF-inv (decLFs-src l d (lfsHead LFp.stBlockTxs)) s , aLFs l d (lfsHead LFp.stBlockTxs) (lfsWtxs1 a) refl (ceqLF-s-btx l d)
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockTxs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockTxs)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfsWvot1 a , succVF-inv (decLFs-src l d (lfsHead LFp.stVotes)) s , aLFs l d (lfsHead LFp.stVotes) (lfsWvot1 a) refl (ceqLF-s-vot l d)
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stVotes) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stVotes)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFNextBlockAndTxsInRange} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfsWnext1 a , succVF-inv (decLFs-src l d (lfsHead LFp.stBlockRange)) s , aLFs l d (lfsHead LFp.stBlockRange) (lfsWnext1 a) refl (ceqLF-s-next l d)
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFLastBlockAndTxsInRange} {a} s with step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl | yes refl = lfsWlast1 a , succVF-inv (decLFs-src l d (lfsHead LFp.stBlockRange)) s , aLFs l d (lfsHead LFp.stBlockRange) (lfsWlast1 a) refl (ceqLF-s-last l d)
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockTxsRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFVotesRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockRangeRequest} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFDone} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' sendLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFBlockTxs} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFVoteDelivery} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.apiLFev l' d' recvLFRangeBlock} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
decLFs-src-ev-inv l d (lfsHead LFp.stBlockRange) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsHead LFp.stBlockRange)) refl s))
-- head stDone : ret
decLFs-src-ev-inv l d (lfsHead LFp.stDone) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- done leaf
decLFs-src-ev-inv l d lfsDone1 {e₁ = LFp.doneLF l' d'} {a} s with step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s
... | offer with LFp.LFEv-≟ (_ , LFp.doneLF l d) (_ , LFp.doneLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = lfsSil LFp.stDone , sym (just-injective offer) , aLFs l d lfsDone1 (lfsSil LFp.stDone) refl (ceqLF-s-ddone l d)
decLFs-src-ev-inv l d lfsDone1 {e₁ = LFp.sendLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
decLFs-src-ev-inv l d lfsDone1 {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
decLFs-src-ev-inv l d lfsDone1 {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d lfsDone1) (hlfsDone1 l d) s))
-- send leaves
decLFs-src-ev-inv l d (lfsWblk1 b) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfsSil LFp.stIdle , sym (just-injective offer) , aLFs l d (lfsWblk1 b) (lfsSil LFp.stIdle) refl (ceqLF-s-wblk l d b)
decLFs-src-ev-inv l d (lfsWblk1 b) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-src-ev-inv l d (lfsWblk1 b) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-src-ev-inv l d (lfsWblk1 b) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWblk1 b)) (hlfsWblk1 l d b) s))
decLFs-src-ev-inv l d (lfsWtxs1 ts) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfsSil LFp.stIdle , sym (just-injective offer) , aLFs l d (lfsWtxs1 ts) (lfsSil LFp.stIdle) refl (ceqLF-s-wtxs l d ts)
decLFs-src-ev-inv l d (lfsWtxs1 ts) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-src-ev-inv l d (lfsWtxs1 ts) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-src-ev-inv l d (lfsWtxs1 ts) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWtxs1 ts)) (hlfsWtxs1 l d ts) s))
decLFs-src-ev-inv l d (lfsWvot1 vs) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfsSil LFp.stIdle , sym (just-injective offer) , aLFs l d (lfsWvot1 vs) (lfsSil LFp.stIdle) refl (ceqLF-s-wvot l d vs)
decLFs-src-ev-inv l d (lfsWvot1 vs) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-src-ev-inv l d (lfsWvot1 vs) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-src-ev-inv l d (lfsWvot1 vs) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWvot1 vs)) (hlfsWvot1 l d vs) s))
decLFs-src-ev-inv l d (lfsWnext1 (b , ts)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfsSil LFp.stBlockRange , sym (just-injective offer) , aLFs l d (lfsWnext1 (b , ts)) (lfsSil LFp.stBlockRange) refl (ceqLF-s-wnext l d b ts)
decLFs-src-ev-inv l d (lfsWnext1 (b , ts)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-src-ev-inv l d (lfsWnext1 (b , ts)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-src-ev-inv l d (lfsWnext1 (b , ts)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWnext1 (b , ts))) (hlfsWnext1 l d (b , ts)) s))
decLFs-src-ev-inv l d (lfsWlast1 (b , ts)) {e₁ = LFp.sendLF l' d'} {a = val} s with step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s
... | offer with LFp.LFEv-≟ (_ , LFp.sendLF l d) (_ , LFp.sendLF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with val ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = lfsSil LFp.stIdle , sym (just-injective offer) , aLFs l d (lfsWlast1 (b , ts)) (lfsSil LFp.stIdle) refl (ceqLF-s-wlast l d b ts)
decLFs-src-ev-inv l d (lfsWlast1 (b , ts)) {e₁ = LFp.receiveLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
decLFs-src-ev-inv l d (lfsWlast1 (b , ts)) {e₁ = LFp.apiLFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
decLFs-src-ev-inv l d (lfsWlast1 (b , ts)) {e₁ = LFp.doneLF l' d'} s = ⊥-elim (nothing-absurd (step-target-LF (decLFs-src l d (lfsWlast1 (b , ts))) (hlfsWlast1 l d (b , ts)) s))
-- loop re-entry
decLFs-src-ev-inv l d (lfsSil st) s with LFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()


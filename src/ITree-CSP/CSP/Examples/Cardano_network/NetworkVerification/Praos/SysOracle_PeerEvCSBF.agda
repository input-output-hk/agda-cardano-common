{-# OPTIONS --guardedness #-}

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_PeerEvCSBF (blkA : Block₃) where

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
import CSP.Laws.Traces.PrefixInversion (Net_Api-≟ {Payload}) as PInv
open PInv using ( ⟶₀-ev-inv; Prefix-cont-fires )
open Op using ( Prefix; Output; Output-cont )
open import Class.DecEq using ( DecEq )

open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA public

------------------------------------------------------------------------
-- G2 — PER-PEER VISIBLE-EVENT INVERSIONS (`dec{peer}-ev-inv`).
--
-- Foundation: the ITER-FORCE OFFER lemma.  A source-alphabet visible step of
-- a peer's react node (a loop `iter` head or a `succVC` mid derivative) lands
-- on the node's OFFERED continuation `succVC q at a` (the very expression the
-- fine mid positions are DEFINED by).  `step-target-*` reads off the offer
-- map at the fired event (via the manifest / `f*`-supplied force equality) so
-- non-firing events are refuted by `nothing-absurd`.
------------------------------------------------------------------------

open SN
  using ( succVC; vis-ofC; CSProc; succVB; vis-ofB; BFProc )

-- the source-alphabet LTS instances (same module applications the peer
-- `renameMap-ev-reflect` reflects into, so their step types are convertible)
import Semantics.LTS {E = CS.CSEv} {I = ExtI CS.CSEv} as CSL
import Semantics.LTS {E = BF.BFEv} {I = ExtI BF.BFEv} as BFL

-- CS iter-force offer: `succVC q at a` is exactly the offered continuation
succVC-just : (q : CSProc) (at : AnyTypes CS.CSEv) (a : proj₁ at) {P′ : CSProc}
  → vis-ofC (PTree.force q) at a ≡ just P′ → succVC q at a ≡ P′
succVC-just q at a eq with vis-ofC (PTree.force q) at a
succVC-just q at a refl | just t = refl
succVC-just q at a ()   | nothing

-- CS: a visible source step lands on `succVC q (X , e) a`
succVC-inv : (q : CSProc) {X : Set 0ℓ} {e : CS.CSEv X} {a : X} {P′ : CSProc}
  → q CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e a)) ]─► P′
  → P′ ≡ succVC q (X , e) a
succVC-inv q {X} {e} {a} step with CSL.ev-inv step
... | v , τc , feq , veq =
      sym (succVC-just q (X , e) a (trans (cong (λ n → vis-ofC n (X , e) a) feq) veq))

-- CS: the fired offer entry at a KNOWN force (`refl` for a head / `f*` for a
-- mid); refutes a non-firing event via the reduced (`nothing`) offer map
step-target-CS : (q : CSProc)
    {V : (at : AnyTypes CS.CSEv) → ContinueType at (Maybe CSProc)}
    {T : (i : AnyTypes (ExtI CS.CSEv)) → ContinueType i (Maybe CSProc)}
    {X : Set 0ℓ} {e : CS.CSEv X} {a : X} {P′ : CSProc}
  → PTree.force q ≡ react V T
  → q CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e a)) ]─► P′
  → V (X , e) a ≡ just P′
step-target-CS q {V} {T} {X} {e} {a} feq step with CSL.ev-inv step
... | v , τc , feq′ , veq with react-injective (trans (sym feq) feq′)
...   | Veq , _ = trans (cong (λ w → w (X , e) a) Veq) veq

-- BF iter-force offer
succVB-just : (q : BFProc) (at : AnyTypes BF.BFEv) (a : proj₁ at) {P′ : BFProc}
  → vis-ofB (PTree.force q) at a ≡ just P′ → succVB q at a ≡ P′
succVB-just q at a eq with vis-ofB (PTree.force q) at a
succVB-just q at a refl | just t = refl
succVB-just q at a ()   | nothing

-- BF: a visible source step lands on `succVB q (X , e) a`
succVB-inv : (q : BFProc) {X : Set 0ℓ} {e : BF.BFEv X} {a : X} {P′ : BFProc}
  → q BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e a)) ]─► P′
  → P′ ≡ succVB q (X , e) a
succVB-inv q {X} {e} {a} step with BFL.ev-inv step
... | v , τc , feq , veq =
      sym (succVB-just q (X , e) a (trans (cong (λ n → vis-ofB n (X , e) a) feq) veq))

-- BF: the fired offer entry at a known force
step-target-BF : (q : BFProc)
    {V : (at : AnyTypes BF.BFEv) → ContinueType at (Maybe BFProc)}
    {T : (i : AnyTypes (ExtI BF.BFEv)) → ContinueType i (Maybe BFProc)}
    {X : Set 0ℓ} {e : BF.BFEv X} {a : X} {P′ : BFProc}
  → PTree.force q ≡ react V T
  → q BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e a)) ]─► P′
  → V (X , e) a ≡ just P′
step-target-BF q {V} {T} {X} {e} {a} feq step with BFL.ev-inv step
... | v , τc , feq′ , veq with react-injective (trans (sym feq) feq′)
...   | Veq , _ = trans (cong (λ w → w (X , e) a) Veq) veq

------------------------------------------------------------------------

------------------------------------------------------------------------
-- G2 — ChainSync CLIENT visible-event inversion (`decCSc-ev-inv`).
------------------------------------------------------------------------

-- extra event/payload constructors + value DecEq for the per-position menus
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

instance
  DecEqO-H×T : DecEq (Header × Tip)
  DecEqO-H×T = DecEqI.DecEq-×
  DecEqO-P×T : DecEq (Point × Tip)
  DecEqO-P×T = DecEqI.DecEq-×

-- reduction bridges: the receiveCS-head firing lands on a mid position whose
-- own definition is a `succVC` STUCK on `l ≟ l`; `≟-yes-refl` unsticks both
-- sides (the head-value's first 3 components are wildcarded by `clientStep`)
brRF : (l : Link) (d : Dir) (h : Header) (t : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stCanAwait)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSRollForward h t)) ≡ decCSc-src l d (csRF1 h t)
brRF l d h t t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brRB : (l : Link) (d : Dir) (pt : Point) (tp : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stCanAwait)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSRollBackward pt tp)) ≡ decCSc-src l d (csRB1 pt tp)
brRB l d pt tp t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brAw : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stCanAwait)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync MsgCSAwaitReply) ≡ decCSc-src l d (csSil CS.stMustReply)
brAw l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brRF-MR : (l : Link) (d : Dir) (h : Header) (t : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stMustReply)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSRollForward h t)) ≡ decCSc-src l d (csRF1 h t)
brRF-MR l d h t t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brRB-MR : (l : Link) (d : Dir) (pt : Point) (tp : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stMustReply)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSRollBackward pt tp)) ≡ decCSc-src l d (csRB1 pt tp)
brRB-MR l d pt tp t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brIF : (l : Link) (d : Dir) (pt : Point) (tp : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stIntersect)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)) ≡ decCSc-src l d (csIF1 pt tp)
brIF l d pt tp t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brINF : (l : Link) (d : Dir) (tp : Tip) (t0 : _) (md : _) (ln : _)
     → succVC (decCSc-src l d (csHead CS.stIntersect)) (_ , CS.receiveCS l d)
              (t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)) ≡ decCSc-src l d (csINF1 tp)
brINF l d tp t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl

------------------------------------------------------------------------
-- GAP-A (ChainSync CLIENT) — per-peer concrete↔abstract simulation.  The
-- abstract twin `absCSc l d pos = tableSpec (…csCnxt…) (coarsenCSc pos)` fires
-- the SAME visible `(e,a)` to the coarsened successor.  `ιCS-inv-shape` pins
-- the renamed event's ι-image shape; each `ceqCSc*` witnesses that the abstract
-- `csCnxt` edge agrees with the coarsening (coarsen ∘ nxt COMMUTES), and `aCSc`
-- packages the agreement into the abstract `tableSpec` step.
------------------------------------------------------------------------

-- a renamed Net_Api event whose ι-preimage is a CS source event `e₁` is exactly
-- the ι-image `ιCS e₁` (recover `e₂ ≡ ιCS e₁` by casing the Net_Api channel)
ιCS-inv-shape : {X : Set 0ℓ} {e₂ : Net_Api Payload X} {e₁ : CS.CSEv X}
  → ιCS⁻¹ e₂ ≡ just e₁ → e₂ ≡ ιCS e₁
ιCS-inv-shape {e₂ = input  _ _ N2N_ChainSync}    refl = refl
ιCS-inv-shape {e₂ = input  _ _ N2N_BlockFetch}   ()
ιCS-inv-shape {e₂ = input  _ _ N2N_TxSubmission} ()
ιCS-inv-shape {e₂ = input  _ _ N2N_KeepAlive}    ()
ιCS-inv-shape {e₂ = input  _ _ N2N_LeiosNotify}  ()
ιCS-inv-shape {e₂ = input  _ _ N2N_LeiosFetch}   ()
ιCS-inv-shape {e₂ = output _ _ N2N_ChainSync}    refl = refl
ιCS-inv-shape {e₂ = output _ _ N2N_BlockFetch}   ()
ιCS-inv-shape {e₂ = output _ _ N2N_TxSubmission} ()
ιCS-inv-shape {e₂ = output _ _ N2N_KeepAlive}    ()
ιCS-inv-shape {e₂ = output _ _ N2N_LeiosNotify}  ()
ιCS-inv-shape {e₂ = output _ _ N2N_LeiosFetch}   ()
ιCS-inv-shape {e₂ = done   _ _ N2N_ChainSync}    refl = refl
ιCS-inv-shape {e₂ = done   _ _ N2N_BlockFetch}   ()
ιCS-inv-shape {e₂ = done   _ _ N2N_TxSubmission} ()
ιCS-inv-shape {e₂ = done   _ _ N2N_KeepAlive}    ()
ιCS-inv-shape {e₂ = done   _ _ N2N_LeiosNotify}  ()
ιCS-inv-shape {e₂ = done   _ _ N2N_LeiosFetch}   ()
ιCS-inv-shape {e₂ = apiCS  _ _ _} refl = refl
ιCS-inv-shape {e₂ = sndmsg _ _ _} ()
ιCS-inv-shape {e₂ = rcvmsg _ _ _} ()
ιCS-inv-shape {e₂ = tx     _ _ _} ()
ιCS-inv-shape {e₂ = sndack _ _ _} ()
ιCS-inv-shape {e₂ = rcvack _ _ _} ()
ιCS-inv-shape {e₂ = ack    _ _ _} ()
ιCS-inv-shape {e₂ = apiBF  _ _ _} ()
ιCS-inv-shape {e₂ = apiTS  _ _ _} ()
ιCS-inv-shape {e₂ = apiKA  _ _ _} ()
ιCS-inv-shape {e₂ = apiLN  _ _ _} ()
ιCS-inv-shape {e₂ = apiLF  _ _ _} ()
ιCS-inv-shape {e₂ = break  _}     ()

-- package a `csCnxt` agreement into the abstract CS-client step (the abstract
-- peer is at a non-terminal coarsened position, so it offers the `nxt` react)
aCSc : (l : Link) (d : Dir) (pos pos′ : CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.csCfin (coarsenCSc pos) ≡ false
  → NS.csCnxt l d (coarsenCSc pos) (X , e) a ≡ just (coarsenCSc pos′)
  → absCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSc l d pos′
aCSc l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenCSc pos) finEq ceq

-- per-firing `coarsen ∘ nxt` commutations (each: the abstract `csCnxt` fires the
-- SAME renamed event to the coarsened successor; `refl` after the `l/d`(+value)
-- `≟`-guards are unstuck)
ceqCSc01 : ∀ {a} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccIdle (_ , apiCS l d sendCSRequestNext) a ≡ just NS.ccWreq
ceqCSc01 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc02 : ∀ {ps} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccIdle (_ , apiCS l d sendCSFindIntersect) ps ≡ just (NS.ccWfi ps)
ceqCSc02 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc03 : ∀ {a} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccIdle (_ , apiCS l d sendCSDone) a ≡ just NS.ccWdone
ceqCSc03 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc04 : ∀ {t0 md ln} {h : Header} {t : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccAwait (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSRollForward h t)) ≡ just (NS.ccArf (h , t))
ceqCSc04 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc05 : ∀ {t0 md ln} {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccAwait (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSRollBackward pt tp)) ≡ just (NS.ccArb (pt , tp))
ceqCSc05 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc06 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccAwait (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync MsgCSAwaitReply) ≡ just NS.ccMust
ceqCSc06 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc07 : ∀ {t0 md ln} {h : Header} {t : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccMust (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSRollForward h t)) ≡ just (NS.ccArf (h , t))
ceqCSc07 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc08 : ∀ {t0 md ln} {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccMust (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSRollBackward pt tp)) ≡ just (NS.ccArb (pt , tp))
ceqCSc08 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc09 : ∀ {t0 md ln} {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccInt (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)) ≡ just (NS.ccAif (pt , tp))
ceqCSc09 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc10 : ∀ {t0 md ln} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccInt (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)) ≡ just (NS.ccAin tp)
ceqCSc10 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSc11 : (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccWreq (_ , input l d N2N_ChainSync)
      (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ≡ just NS.ccAwait
ceqCSc11 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) = refl
ceqCSc12 : ∀ {ps} (l : Link) (d : Dir)
  → NS.csCnxt l d (NS.ccWfi ps) (_ , input l d N2N_ChainSync)
      (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) ≡ just NS.ccInt
ceqCSc12 {ps} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) = refl
ceqCSc13 : (l : Link) (d : Dir)
  → NS.csCnxt l d NS.ccWdone (_ , input l d N2N_ChainSync)
      (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ≡ just NS.ccTerm
ceqCSc13 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) = refl
ceqCSc15 : ∀ {h : Header} {t : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d (NS.ccArf (h , t)) (_ , apiCS l d recvCSRollforward) (h , t) ≡ just NS.ccIdle
ceqCSc15 {h} {t} l d rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl (h , t) = refl
ceqCSc16 : ∀ {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d (NS.ccArb (pt , tp)) (_ , apiCS l d recvCSRollback) (pt , tp) ≡ just NS.ccIdle
ceqCSc16 {pt} {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl (pt , tp) = refl
ceqCSc17 : ∀ {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d (NS.ccAif (pt , tp)) (_ , apiCS l d recvCSIntersectFound) (pt , tp) ≡ just NS.ccIdle
ceqCSc17 {pt} {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl (pt , tp) = refl
ceqCSc18 : ∀ {tp : Tip} (l : Link) (d : Dir)
  → NS.csCnxt l d (NS.ccAin tp) (_ , apiCS l d recvCSIntersectNotFound) tp ≡ just NS.ccIdle
ceqCSc18 {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl tp = refl

-- SOURCE-side per-position ev inversion: a visible source step of a fine CS
-- client position lands on a representable fine position, AND the abstract
-- twin fires the same (renamed) event to the coarsened successor.
decCSc-src-ev-inv : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSc-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ CScPos ] (P′ ≡ decCSc-src l d pos′)
      × (absCSc l d pos ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absCSc l d pos′)
-- head stIdle : fires apiCSev sendCSRequestNext / FindIntersect / Done
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRequestNext} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csReqNext1 , succVC-inv (decCSc-src l d (csHead CS.stIdle)) s , aCSc l d (csHead CS.stIdle) csReqNext1 refl (ceqCSc01 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} {a} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csFindInt1 a , succVC-inv (decCSc-src l d (csHead CS.stIdle)) s , aCSc l d (csHead CS.stIdle) (csFindInt1 a) refl (ceqCSc02 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSDone} s with step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csDone1 , succVC-inv (decCSc-src l d (csHead CS.stIdle)) s , aCSc l d (csHead CS.stIdle) csDone1 refl (ceqCSc03 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollForward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSRollBackward}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollforward}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSRollback}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIdle)) refl s))
-- head stCanAwait : fires receiveCS RollForward / RollBackward / AwaitReply
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRF1 h t , trans (succVC-inv (decCSc-src l d (csHead CS.stCanAwait)) s) (brRF l d h t t0 md ln) , aCSc l d (csHead CS.stCanAwait) (csRF1 h t) refl (ceqCSc04 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRB1 pt tp , trans (succVC-inv (decCSc-src l d (csHead CS.stCanAwait)) s) (brRB l d pt tp t0 md ln) , aCSc l d (csHead CS.stCanAwait) (csRB1 pt tp) refl (ceqCSc05 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSAwaitReply} s with step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csSil CS.stMustReply , trans (succVC-inv (decCSc-src l d (csHead CS.stCanAwait)) s) (brAw l d t0 md ln) , aCSc l d (csHead CS.stCanAwait) (csSil CS.stMustReply) refl (ceqCSc06 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' m}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
decCSc-src-ev-inv l d (csHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stCanAwait)) refl s))
-- head stMustReply : fires receiveCS RollForward / RollBackward
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRF1 h t , trans (succVC-inv (decCSc-src l d (csHead CS.stMustReply)) s) (brRF-MR l d h t t0 md ln) , aCSc l d (csHead CS.stMustReply) (csRF1 h t) refl (ceqCSc07 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRB1 pt tp , trans (succVC-inv (decCSc-src l d (csHead CS.stMustReply)) s) (brRB-MR l d pt tp t0 md ln) , aCSc l d (csHead CS.stMustReply) (csRB1 pt tp) refl (ceqCSc08 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}          s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}                 s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
decCSc-src-ev-inv l d (csHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stMustReply)) refl s))
-- head stIntersect : fires receiveCS IntersectFound / IntersectNotFound
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csIF1 pt tp , trans (succVC-inv (decCSc-src l d (csHead CS.stIntersect)) s) (brIF l d pt tp t0 md ln) , aCSc l d (csHead CS.stIntersect) (csIF1 pt tp) refl (ceqCSc09 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)} s with step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csINF1 tp , trans (succVC-inv (decCSc-src l d (csHead CS.stIntersect)) s) (brINF l d tp t0 md ln) , aCSc l d (csHead CS.stIntersect) (csINF1 tp) refl (ceqCSc10 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect ps)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
decCSc-src-ev-inv l d (csHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSc-src-ev-inv l d (csHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid csReqNext1 : fires sendCS payload → csSil stCanAwait
decCSc-src-ev-inv l d csReqNext1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stCanAwait , sym (just-injective offer) , aCSc l d csReqNext1 (csSil CS.stCanAwait) refl (ceqCSc11 l d)
decCSc-src-ev-inv l d csReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-ev-inv l d csReqNext1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
decCSc-src-ev-inv l d csReqNext1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csReqNext1) (fReqNext1 l d) s))
-- mid csFindInt1 ps : fires sendCS payload → csSil stIntersect
decCSc-src-ev-inv l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stIntersect , sym (just-injective offer) , aCSc l d (csFindInt1 ps) (csSil CS.stIntersect) refl (ceqCSc12 l d)
decCSc-src-ev-inv l d (csFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-ev-inv l d (csFindInt1 ps) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
decCSc-src-ev-inv l d (csFindInt1 ps) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csFindInt1 ps)) (fFindInt1 l d ps) s))
-- mid csDone1 : fires sendCS payload → csSil stDone (client has no node-local done)
decCSc-src-ev-inv l d csDone1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stDone , sym (just-injective offer) , aCSc l d csDone1 (csSil CS.stDone) refl (ceqCSc13 l d)
decCSc-src-ev-inv l d csDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-ev-inv l d csDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
decCSc-src-ev-inv l d csDone1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d csDone1) (fDone1 l d) s))
-- mid csRF1 : fires apiCSev recvCSRollforward (h,t) → csSil stIdle
decCSc-src-ev-inv l d (csRF1 h t) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollforward) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (h , t)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stIdle , sym (just-injective offer) , aCSc l d (csRF1 h t) (csSil CS.stIdle) refl (ceqCSc15 l d)
decCSc-src-ev-inv l d (csRF1 h t) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-ev-inv l d (csRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
decCSc-src-ev-inv l d (csRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRF1 h t)) (fRF1 l d h t) s))
-- mid csRB1 : fires apiCSev recvCSRollback (pt,tp) → csSil stIdle
decCSc-src-ev-inv l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSRollback) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stIdle , sym (just-injective offer) , aCSc l d (csRB1 pt tp) (csSil CS.stIdle) refl (ceqCSc16 l d)
decCSc-src-ev-inv l d (csRB1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-ev-inv l d (csRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
decCSc-src-ev-inv l d (csRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csRB1 pt tp)) (fRB1 l d pt tp) s))
-- mid csIF1 : fires apiCSev recvCSIntersectFound (pt,tp) → csSil stIdle
decCSc-src-ev-inv l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (pt , tp)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stIdle , sym (just-injective offer) , aCSc l d (csIF1 pt tp) (csSil CS.stIdle) refl (ceqCSc17 l d)
decCSc-src-ev-inv l d (csIF1 pt tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-ev-inv l d (csIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
decCSc-src-ev-inv l d (csIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csIF1 pt tp)) (fIF1 l d pt tp) s))
-- mid csINF1 : fires apiCSev recvCSIntersectNotFound tp → csSil stIdle
decCSc-src-ev-inv l d (csINF1 tp) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d recvCSIntersectNotFound) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ tp
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = csSil CS.stIdle , sym (just-injective offer) , aCSc l d (csINF1 tp) (csSil CS.stIdle) refl (ceqCSc18 l d)
decCSc-src-ev-inv l d (csINF1 tp) {e₁ = CS.sendCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-ev-inv l d (csINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
decCSc-src-ev-inv l d (csINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSc-src l d (csINF1 tp)) (fINF1 l d tp) s))
-- loop re-entry csSil : forces to `sil`, no visible step
decCSc-src-ev-inv l d (csSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- GAP-A (ChainSync CLIENT) per-peer simulation: reflect the renamed step to the
-- source FSM (keeping the ι-preimage), invert the source offer for the concrete
-- successor + the abstract twin's matching step, re-rename the concrete target,
-- and transport the abstract step onto the actual renamed event `e₂ ≡ ιCS e₁`.
simCSc : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ pos′ ∈ CScPos ] (M ≡ decCSc l d pos′)
      × (absCSc l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSc l d pos′)
simCSc l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decCSc-src-ev-inv l d pos srcStep | ιCS-inv-shape iota
...   | pos′ , P′eq , aStep | refl = pos′ , trans Meq (cong RenCS.renameMap P′eq) , aStep

------------------------------------------------------------------------
-- G2 — ChainSync SERVER visible-event inversion (`decCSs-ev-inv`).
-- Dual of the client: `ssHead stIdle` RECEIVES on the wire; the other heads
-- SEND via api.  Same infra (succVC-inv / step-target-CS / RenCS / CSNO).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.Base using ( FromResponder )
open import Data.List using ( List )

-- server-stIdle receive-firing bridges (target the mid positions, whose defs
-- are `succVC` stuck on `l ≟ l`; the received value's first 3 are wildcarded)
brSReq : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
       → succVC (decCSs-src l d (ssHead CS.stIdle)) (_ , CS.receiveCS l d)
                (t0 , md , ln , chainSync MsgCSRequestNext) ≡ decCSs-src l d ssReqNext1
brSReq l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brSFI : (l : Link) (d : Dir) (ps : List Point) (t0 : _) (md : _) (ln : _)
      → succVC (decCSs-src l d (ssHead CS.stIdle)) (_ , CS.receiveCS l d)
               (t0 , md , ln , chainSync (MsgCSFindIntersect ps)) ≡ decCSs-src l d (ssFindInt1 ps)
brSFI l d ps t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brSDN : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
      → succVC (decCSs-src l d (ssHead CS.stIdle)) (_ , CS.receiveCS l d)
               (t0 , md , ln , chainSync MsgCSDone) ≡ decCSs-src l d ssDone1
brSDN l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
-- server stMustReply reaches ssRF1/ssRB1 (defined via stCanAwait): bridge the state
brSRF-MR : (l : Link) (d : Dir) (a : Header × Tip)
  → succVC (decCSs-src l d (ssHead CS.stMustReply)) (_ , CS.apiCSev l d sendCSRollForward) a ≡ decCSs-src l d (ssRF1 (proj₁ a) (proj₂ a))
brSRF-MR l d a rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brSRB-MR : (l : Link) (d : Dir) (a : Point × Tip)
  → succVC (decCSs-src l d (ssHead CS.stMustReply)) (_ , CS.apiCSev l d sendCSRollBackward) a ≡ decCSs-src l d (ssRB1 (proj₁ a) (proj₂ a))
brSRB-MR l d a rewrite ≟-yes-refl l | ≟-yes-refl d = refl

------------------------------------------------------------------------
-- GAP-A (ChainSync SERVER) — per-peer concrete↔abstract simulation.  Dual of
-- the client: the abstract `csSnxt` table drives `absCSs l d pos`; `aCSs`
-- packages each `coarsen ∘ nxt` agreement (`ceqCSs*`) into the abstract step.
------------------------------------------------------------------------

-- package a `csSnxt` agreement into the abstract CS-server step
aCSs : (l : Link) (d : Dir) (pos pos′ : CSsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.csSfin (coarsenCSs pos) ≡ false
  → NS.csSnxt l d (coarsenCSs pos) (X , e) a ≡ just (coarsenCSs pos′)
  → absCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSs l d pos′
aCSs l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenCSs pos) finEq ceq

-- per-firing `coarsen ∘ nxt` commutations for the CS server
ceqCSs01 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csIdle (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync MsgCSRequestNext) ≡ just NS.csAreq
ceqCSs01 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs02 : ∀ {t0 md ln} {ps} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csIdle (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync (MsgCSFindIntersect ps)) ≡ just (NS.csAfi ps)
ceqCSs02 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs03 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csIdle (_ , output l d N2N_ChainSync)
      (t0 , md , ln , chainSync MsgCSDone) ≡ just NS.csDdone
ceqCSs03 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs04 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csCanAwait (_ , apiCS l d sendCSRollForward) a ≡ just (NS.csWrf a)
ceqCSs04 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs05 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csCanAwait (_ , apiCS l d sendCSRollBackward) a ≡ just (NS.csWrb a)
ceqCSs05 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs06 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csCanAwait (_ , apiCS l d sendCSAwaitReply) a ≡ just NS.csWar
ceqCSs06 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs07 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csMust (_ , apiCS l d sendCSRollForward) a ≡ just (NS.csWrf a)
ceqCSs07 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs08 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csMust (_ , apiCS l d sendCSRollBackward) a ≡ just (NS.csWrb a)
ceqCSs08 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs09 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csInt (_ , apiCS l d sendCSIntersectFound) a ≡ just (NS.csWif a)
ceqCSs09 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs10 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csInt (_ , apiCS l d sendCSIntersectNotFound) a ≡ just (NS.csWin a)
ceqCSs10 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs11 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csAreq (_ , apiCS l d reqCSRequestNext) a ≡ just NS.csCanAwait
ceqCSs11 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs12 : ∀ {ps} (l : Link) (d : Dir)
  → NS.csSnxt l d (NS.csAfi ps) (_ , apiCS l d reqCSFindIntersect) ps ≡ just NS.csInt
ceqCSs12 {ps} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl ⦃ DecEqI.DecEq-List ⦃ DecEq-Point ⦄ ⦄ ps = refl
ceqCSs13 : ∀ {a} (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csDdone (_ , done l d N2N_ChainSync) a ≡ just NS.csTerm
ceqCSs13 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqCSs14 : ∀ {h : Header} {t : Tip} (l : Link) (d : Dir)
  → NS.csSnxt l d (NS.csWrf (h , t)) (_ , input l d N2N_ChainSync)
      (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just NS.csIdle
ceqCSs14 {h} {t} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) = refl
ceqCSs15 : ∀ {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csSnxt l d (NS.csWrb (pt , tp)) (_ , input l d N2N_ChainSync)
      (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ≡ just NS.csIdle
ceqCSs15 {pt} {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) = refl
ceqCSs16 : (l : Link) (d : Dir)
  → NS.csSnxt l d NS.csWar (_ , input l d N2N_ChainSync)
      (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) ≡ just NS.csMust
ceqCSs16 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) = refl
ceqCSs17 : ∀ {pt : Point} {tp : Tip} (l : Link) (d : Dir)
  → NS.csSnxt l d (NS.csWif (pt , tp)) (_ , input l d N2N_ChainSync)
      (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) ≡ just NS.csIdle
ceqCSs17 {pt} {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) = refl
ceqCSs18 : ∀ {tp : Tip} (l : Link) (d : Dir)
  → NS.csSnxt l d (NS.csWin tp) (_ , input l d N2N_ChainSync)
      (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) ≡ just NS.csIdle
ceqCSs18 {tp} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) = refl

-- SOURCE-side per-position ev inversion for the CS server (+ the abstract twin's
-- matching step to the coarsened successor).
decCSs-src-ev-inv : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {P′ : CSProc}
  → decCSs-src l d pos CSL.─[ CSL.ev (CSL.evl (CSL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ CSsPos ] (P′ ≡ decCSs-src l d pos′)
      × (absCSs l d pos ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► absCSs l d pos′)
-- head stIdle : receives RequestNext / FindIntersect / Done on the wire
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSRequestNext} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssReqNext1 , trans (succVC-inv (decCSs-src l d (ssHead CS.stIdle)) s) (brSReq l d t0 md ln) , aCSs l d (ssHead CS.stIdle) ssReqNext1 refl (ceqCSs01 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSFindIntersect ps)} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssFindInt1 ps , trans (succVC-inv (decCSs-src l d (ssHead CS.stIdle)) s) (brSFI l d ps t0 md ln) , aCSs l d (ssHead CS.stIdle) (ssFindInt1 ps) refl (ceqCSs02 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSDone} s with step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssDone1 , trans (succVC-inv (decCSs-src l d (ssHead CS.stIdle)) s) (brSDN l d t0 md ln) , aCSs l d (ssHead CS.stIdle) ssDone1 refl (ceqCSs03 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward p t)}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound p t)}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound t)} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIdle) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIdle)) refl s))
-- head stCanAwait : sends RollForward / RollBackward / AwaitReply via api
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRF1 (proj₁ a) (proj₂ a) , succVC-inv (decCSs-src l d (ssHead CS.stCanAwait)) s , aCSs l d (ssHead CS.stCanAwait) (ssRF1 (proj₁ a) (proj₂ a)) refl (ceqCSs04 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRB1 (proj₁ a) (proj₂ a) , succVC-inv (decCSs-src l d (ssHead CS.stCanAwait)) s , aCSs l d (ssHead CS.stCanAwait) (ssRB1 (proj₁ a) (proj₂ a)) refl (ceqCSs05 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} s with step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssAw1 , succVC-inv (decCSs-src l d (ssHead CS.stCanAwait)) s , aCSs l d (ssHead CS.stCanAwait) ssAw1 refl (ceqCSs06 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stCanAwait) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stCanAwait)) refl s))
-- head stMustReply : sends RollForward / RollBackward via api
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRF1 (proj₁ a) (proj₂ a) , trans (succVC-inv (decCSs-src l d (ssHead CS.stMustReply)) s) (brSRF-MR l d a) , aCSs l d (ssHead CS.stMustReply) (ssRF1 (proj₁ a) (proj₂ a)) refl (ceqCSs07 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRB1 (proj₁ a) (proj₂ a) , trans (succVC-inv (decCSs-src l d (ssHead CS.stMustReply)) s) (brSRB-MR l d a) , aCSs l d (ssHead CS.stMustReply) (ssRB1 (proj₁ a) (proj₂ a)) refl (ceqCSs08 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSRequestNext}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSDone}               s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollforward}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSRollback}           s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSRequestNext}         s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}       s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stMustReply) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stMustReply)) refl s))
-- head stIntersect : sends IntersectFound / IntersectNotFound via api
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssIF1 (proj₁ a) (proj₂ a) , succVC-inv (decCSs-src l d (ssHead CS.stIntersect)) s , aCSs l d (ssHead CS.stIntersect) (ssIF1 (proj₁ a) (proj₂ a)) refl (ceqCSs09 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} {a} s with step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssINF1 a , succVC-inv (decCSs-src l d (ssHead CS.stIntersect)) s , aCSs l d (ssHead CS.stIntersect) (ssINF1 a) refl (ceqCSs10 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRequestNext}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSFindIntersect}   s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSDone}            s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSAwaitReply}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollForward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' sendCSRollBackward}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollforward}     s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSRollback}        s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectFound}  s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSRequestNext}      s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.apiCSev l' d' reqCSFindIntersect}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
decCSs-src-ev-inv l d (ssHead CS.stIntersect) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssHead CS.stIntersect)) refl s))
-- head stDone : `ret`, no visible step
decCSs-src-ev-inv l d (ssHead CS.stDone) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid ssReqNext1 : fires api reqCSRequestNext (Prefix₀) → ssSil stCanAwait
decCSs-src-ev-inv l d ssReqNext1 {e₁ = CS.apiCSev l' d' m} s with step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSRequestNext) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = ssSil CS.stCanAwait , sym (just-injective offer) , aCSs l d ssReqNext1 (ssSil CS.stCanAwait) refl (ceqCSs11 l d)
decCSs-src-ev-inv l d ssReqNext1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-ev-inv l d ssReqNext1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
decCSs-src-ev-inv l d ssReqNext1 {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssReqNext1) (gReqNext1 l d) s))
-- mid ssFindInt1 ps : fires api reqCSFindIntersect ps (Output) → ssSil stIntersect
decCSs-src-ev-inv l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' m} {a} s with step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s
... | offer with CS.CSEv-≟ (_ , CS.apiCSev l d reqCSFindIntersect) (_ , CS.apiCSev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ CS.DecEq-ListPoint ⦄ a ps
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stIntersect , sym (just-injective offer) , aCSs l d (ssFindInt1 ps) (ssSil CS.stIntersect) refl (ceqCSs12 l d)
decCSs-src-ev-inv l d (ssFindInt1 ps) {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-ev-inv l d (ssFindInt1 ps) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
decCSs-src-ev-inv l d (ssFindInt1 ps) {e₁ = CS.doneCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssFindInt1 ps)) (gFindInt1 l d ps) s))
-- mid ssDone1 : fires doneCS (Prefix₀) → ssSil stDone
decCSs-src-ev-inv l d ssDone1 {e₁ = CS.doneCS l' d'} s with step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.doneCS l d) (_ , CS.doneCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = ssSil CS.stDone , sym (just-injective offer) , aCSs l d ssDone1 (ssSil CS.stDone) refl (ceqCSs13 l d)
decCSs-src-ev-inv l d ssDone1 {e₁ = CS.sendCS l' d'}    s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-ev-inv l d ssDone1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
decCSs-src-ev-inv l d ssDone1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssDone1) (gDone1 l d) s))
-- mid ssRF1 : fires sendCS payload → ssSil stIdle
decCSs-src-ev-inv l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stIdle , sym (just-injective offer) , aCSs l d (ssRF1 h t) (ssSil CS.stIdle) refl (ceqCSs14 l d)
decCSs-src-ev-inv l d (ssRF1 h t) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-ev-inv l d (ssRF1 h t) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
decCSs-src-ev-inv l d (ssRF1 h t) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRF1 h t)) (gRF1 l d h t) s))
-- mid ssRB1 : fires sendCS payload → ssSil stIdle
decCSs-src-ev-inv l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stIdle , sym (just-injective offer) , aCSs l d (ssRB1 pt tp) (ssSil CS.stIdle) refl (ceqCSs15 l d)
decCSs-src-ev-inv l d (ssRB1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-ev-inv l d (ssRB1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
decCSs-src-ev-inv l d (ssRB1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssRB1 pt tp)) (gRB1 l d pt tp) s))
-- mid ssAw1 : fires sendCS payload → ssSil stMustReply
decCSs-src-ev-inv l d ssAw1 {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stMustReply , sym (just-injective offer) , aCSs l d ssAw1 (ssSil CS.stMustReply) refl (ceqCSs16 l d)
decCSs-src-ev-inv l d ssAw1 {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-ev-inv l d ssAw1 {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
decCSs-src-ev-inv l d ssAw1 {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d ssAw1) (gAw1 l d) s))
-- mid ssIF1 : fires sendCS payload → ssSil stIdle
decCSs-src-ev-inv l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stIdle , sym (just-injective offer) , aCSs l d (ssIF1 pt tp) (ssSil CS.stIdle) refl (ceqCSs17 l d)
decCSs-src-ev-inv l d (ssIF1 pt tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-ev-inv l d (ssIF1 pt tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
decCSs-src-ev-inv l d (ssIF1 pt tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssIF1 pt tp)) (gIF1 l d pt tp) s))
-- mid ssINF1 : fires sendCS payload → ssSil stIdle
decCSs-src-ev-inv l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} {a} s with step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s
... | offer with CS.CSEv-≟ (_ , CS.sendCS l d) (_ , CS.sendCS l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = ssSil CS.stIdle , sym (just-injective offer) , aCSs l d (ssINF1 tp) (ssSil CS.stIdle) refl (ceqCSs18 l d)
decCSs-src-ev-inv l d (ssINF1 tp) {e₁ = CS.receiveCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-ev-inv l d (ssINF1 tp) {e₁ = CS.apiCSev l' d' m} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
decCSs-src-ev-inv l d (ssINF1 tp) {e₁ = CS.doneCS l' d'} s = ⊥-elim (nothing-absurd (step-target-CS (decCSs-src l d (ssINF1 tp)) (gINF1 l d tp) s))
-- loop re-entry ssSil : forces to `sil`, no visible step
decCSs-src-ev-inv l d (ssSil st) s with CSL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- GAP-A (ChainSync SERVER) per-peer simulation.
simCSs : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ pos′ ∈ CSsPos ] (M ≡ decCSs l d pos′)
      × (absCSs l d pos ─[ ev (evl (evLabel X e a)) ]─► absCSs l d pos′)
simCSs l d pos step with CSNO.renameMap-ev-reflect-ι {P = decCSs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decCSs-src-ev-inv l d pos srcStep | ιCS-inv-shape iota
...   | pos′ , P′eq , aStep | refl = pos′ , trans Meq (cong RenCS.renameMap P′eq) , aStep

------------------------------------------------------------------------
-- G2 — BlockFetch CLIENT / SERVER visible-event inversions.
-- Same recipe over the BF alphabet (succVB-inv / step-target-BF / BFNO).
------------------------------------------------------------------------

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

-- BFc receive-firing bridges (stBusy / stStreaming heads → mid / sil positions)
brBcStart : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVB (decBFc-src l d (bcHead BF.stBusy)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch MsgStartBatch) ≡ decBFc-src l d (bcSil BF.stStreaming)
brBcStart l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brBcNoBlk : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVB (decBFc-src l d (bcHead BF.stBusy)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch MsgNoBlocks) ≡ decBFc-src l d (bcSil BF.stIdle)
brBcNoBlk l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brBcBlk : (l : Link) (d : Dir) (b : Block) (t0 : _) (md : _) (ln : _)
  → succVB (decBFc-src l d (bcHead BF.stStreaming)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch (MsgBlock b)) ≡ decBFc-src l d (bcBlk1 b)
brBcBlk l d b t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brBcBatch : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVB (decBFc-src l d (bcHead BF.stStreaming)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch MsgBatchDone) ≡ decBFc-src l d (bcSil BF.stIdle)
brBcBatch l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
-- BFs receive-firing bridges (stIdle head → mid positions)
brBsReq : (l : Link) (d : Dir) (r : ChainRange) (t0 : _) (md : _) (ln : _)
  → succVB (decBFs-src l d (bsHead BF.stIdle)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch (MsgRequestRange r)) ≡ decBFs-src l d (bsReq1 r)
brBsReq l d r t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl
brBsDone : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → succVB (decBFs-src l d (bsHead BF.stIdle)) (_ , BF.receiveBF l d)
           (t0 , md , ln , blockFetch MsgClientDone) ≡ decBFs-src l d bsDone1
brBsDone l d t0 md ln rewrite ≟-yes-refl l | ≟-yes-refl d = refl

------------------------------------------------------------------------
-- GAP-A (BlockFetch CLIENT / SERVER) — per-peer concrete↔abstract simulation.
-- `ιBF-inv-shape` pins the renamed event's ι-image; `aBFc`/`aBFs` package each
-- `coarsen ∘ nxt` agreement (`ceqBFc*`/`ceqBFs*`) into the abstract step.
------------------------------------------------------------------------

-- a renamed Net_Api event whose ι-preimage is a BF source event is its ι-image
ιBF-inv-shape : {X : Set 0ℓ} {e₂ : Net_Api Payload X} {e₁ : BF.BFEv X}
  → ιBF⁻¹ e₂ ≡ just e₁ → e₂ ≡ ιBF e₁
ιBF-inv-shape {e₂ = input  _ _ N2N_BlockFetch}   refl = refl
ιBF-inv-shape {e₂ = input  _ _ N2N_ChainSync}    ()
ιBF-inv-shape {e₂ = input  _ _ N2N_TxSubmission} ()
ιBF-inv-shape {e₂ = input  _ _ N2N_KeepAlive}    ()
ιBF-inv-shape {e₂ = input  _ _ N2N_LeiosNotify}  ()
ιBF-inv-shape {e₂ = input  _ _ N2N_LeiosFetch}   ()
ιBF-inv-shape {e₂ = output _ _ N2N_BlockFetch}   refl = refl
ιBF-inv-shape {e₂ = output _ _ N2N_ChainSync}    ()
ιBF-inv-shape {e₂ = output _ _ N2N_TxSubmission} ()
ιBF-inv-shape {e₂ = output _ _ N2N_KeepAlive}    ()
ιBF-inv-shape {e₂ = output _ _ N2N_LeiosNotify}  ()
ιBF-inv-shape {e₂ = output _ _ N2N_LeiosFetch}   ()
ιBF-inv-shape {e₂ = done   _ _ N2N_BlockFetch}   refl = refl
ιBF-inv-shape {e₂ = done   _ _ N2N_ChainSync}    ()
ιBF-inv-shape {e₂ = done   _ _ N2N_TxSubmission} ()
ιBF-inv-shape {e₂ = done   _ _ N2N_KeepAlive}    ()
ιBF-inv-shape {e₂ = done   _ _ N2N_LeiosNotify}  ()
ιBF-inv-shape {e₂ = done   _ _ N2N_LeiosFetch}   ()
ιBF-inv-shape {e₂ = apiBF  _ _ _} refl = refl
ιBF-inv-shape {e₂ = sndmsg _ _ _} ()
ιBF-inv-shape {e₂ = rcvmsg _ _ _} ()
ιBF-inv-shape {e₂ = tx     _ _ _} ()
ιBF-inv-shape {e₂ = sndack _ _ _} ()
ιBF-inv-shape {e₂ = rcvack _ _ _} ()
ιBF-inv-shape {e₂ = ack    _ _ _} ()
ιBF-inv-shape {e₂ = apiCS  _ _ _} ()
ιBF-inv-shape {e₂ = apiTS  _ _ _} ()
ιBF-inv-shape {e₂ = apiKA  _ _ _} ()
ιBF-inv-shape {e₂ = apiLN  _ _ _} ()
ιBF-inv-shape {e₂ = apiLF  _ _ _} ()
ιBF-inv-shape {e₂ = break  _}     ()

-- package a `bfCnxt` agreement into the abstract BF-client step
aBFc : (l : Link) (d : Dir) (pos pos′ : BFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.bfCfin (coarsenBFc pos) ≡ false
  → NS.bfCnxt l d (coarsenBFc pos) (X , e) a ≡ just (coarsenBFc pos′)
  → absBFc l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFc l d pos′
aBFc l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenBFc pos) finEq ceq

-- per-firing `coarsen ∘ nxt` commutations for the BF client
ceqBFc01 : ∀ {r} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcIdle (_ , apiBF l d sendBFRequestRange) r ≡ just (NS.bcWrr r)
ceqBFc01 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc02 : ∀ {a} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcIdle (_ , apiBF l d sendBFClientDone) a ≡ just NS.bcWcd
ceqBFc02 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc03 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcBusy (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch MsgStartBatch) ≡ just NS.bcStream
ceqBFc03 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc04 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcBusy (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch MsgNoBlocks) ≡ just NS.bcIdle
ceqBFc04 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc05 : ∀ {t0 md ln} {b : Block} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcStream (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch (MsgBlock b)) ≡ just (NS.bcAblk b)
ceqBFc05 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc06 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcStream (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch MsgBatchDone) ≡ just NS.bcIdle
ceqBFc06 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFc07 : ∀ {r} (l : Link) (d : Dir)
  → NS.bfCnxt l d (NS.bcWrr r) (_ , input l d N2N_BlockFetch)
      (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ≡ just NS.bcBusy
ceqBFc07 {r} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) = refl
ceqBFc08 : (l : Link) (d : Dir)
  → NS.bfCnxt l d NS.bcWcd (_ , input l d N2N_BlockFetch)
      (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ≡ just NS.bcTerm
ceqBFc08 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) = refl
ceqBFc10 : ∀ {b : Block} (l : Link) (d : Dir)
  → NS.bfCnxt l d (NS.bcAblk b) (_ , apiBF l d recvBFBlock) b ≡ just NS.bcStream
ceqBFc10 {b} l d rewrite ≟-yes-refl l | ≟-yes-refl d | ≟-yes-refl ⦃ decBlock ⦄ b = refl

-- SOURCE-side per-position ev inversion for the BF client (+ abstract twin step).
decBFc-src-ev-inv : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFc-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ BFcPos ] (P′ ≡ decBFc-src l d pos′)
      × (absBFc l d pos ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBFc l d pos′)
-- head stIdle : sends RequestRange / ClientDone via api
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFRequestRange} {a} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcReq1 a , succVB-inv (decBFc-src l d (bcHead BF.stIdle)) s , aBFc l d (bcHead BF.stIdle) (bcReq1 a) refl (ceqBFc01 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFClientDone} s with step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcDone1 , succVB-inv (decBFc-src l d (bcHead BF.stIdle)) s , aBFc l d (bcHead BF.stIdle) bcDone1 refl (ceqBFc02 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' sendBFBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' recvBFBlock}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.apiBFev l' d' reqBFRange}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stIdle)) refl s))
-- head stBusy : receives StartBatch / NoBlocks (both go straight to a re-entry sil)
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgStartBatch} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stStreaming , trans (succVB-inv (decBFc-src l d (bcHead BF.stBusy)) s) (brBcStart l d t0 md ln) , aBFc l d (bcHead BF.stBusy) (bcSil BF.stStreaming) refl (ceqBFc03 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgNoBlocks} s with step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stIdle , trans (succVB-inv (decBFc-src l d (bcHead BF.stBusy)) s) (brBcNoBlk l d t0 md ln) , aBFc l d (bcHead BF.stBusy) (bcSil BF.stIdle) refl (ceqBFc04 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}      s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stBusy)) refl s))
-- head stStreaming : receives Block (→ bcBlk1) / BatchDone (→ re-entry sil)
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgBlock b)} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcBlk1 b , trans (succVB-inv (decBFc-src l d (bcHead BF.stStreaming)) s) (brBcBlk l d b t0 md ln) , aBFc l d (bcHead BF.stStreaming) (bcBlk1 b) refl (ceqBFc05 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgBatchDone} s with step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stIdle , trans (succVB-inv (decBFc-src l d (bcHead BF.stStreaming)) s) (brBcBatch l d t0 md ln) , aBFc l d (bcHead BF.stStreaming) (bcSil BF.stIdle) refl (ceqBFc06 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone}       s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
decBFc-src-ev-inv l d (bcHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcHead BF.stStreaming)) refl s))
-- head stDone : `ret`, no visible step
decBFc-src-ev-inv l d (bcHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bcReq1 r : fires sendBF payload → bcSil stBusy
decBFc-src-ev-inv l d (bcReq1 r) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bcSil BF.stBusy , sym (just-injective offer) , aBFc l d (bcReq1 r) (bcSil BF.stBusy) refl (ceqBFc07 l d)
decBFc-src-ev-inv l d (bcReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-ev-inv l d (bcReq1 r) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
decBFc-src-ev-inv l d (bcReq1 r) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcReq1 r)) (hReq1 l d r) s))
-- mid bcDone1 : fires sendBF payload → bcSil stDone (client has no node-local done)
decBFc-src-ev-inv l d bcDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bcSil BF.stDone , sym (just-injective offer) , aBFc l d bcDone1 (bcSil BF.stDone) refl (ceqBFc08 l d)
decBFc-src-ev-inv l d bcDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-ev-inv l d bcDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
decBFc-src-ev-inv l d bcDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d bcDone1) (hcDone1 l d) s))
-- mid bcBlk1 b : fires apiBFev recvBFBlock b → bcSil stStreaming
decBFc-src-ev-inv l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d recvBFBlock) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ decBlock ⦄ a b
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bcSil BF.stStreaming , sym (just-injective offer) , aBFc l d (bcBlk1 b) (bcSil BF.stStreaming) refl (ceqBFc10 l d)
decBFc-src-ev-inv l d (bcBlk1 b) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-ev-inv l d (bcBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
decBFc-src-ev-inv l d (bcBlk1 b) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFc-src l d (bcBlk1 b)) (hBlk1 l d b) s))
-- loop re-entry bcSil : forces to `sil`, no visible step
decBFc-src-ev-inv l d (bcSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- GAP-A (BlockFetch CLIENT) per-peer simulation.
simBFc : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFc l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ pos′ ∈ BFcPos ] (M ≡ decBFc l d pos′)
      × (absBFc l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFc l d pos′)
simBFc l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFc-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decBFc-src-ev-inv l d pos srcStep | ιBF-inv-shape iota
...   | pos′ , P′eq , aStep | refl = pos′ , trans Meq (cong RenBF.renameMap P′eq) , aStep

-- package a `bfSnxt` agreement into the abstract BF-server step
aBFs : (l : Link) (d : Dir) (pos pos′ : BFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X}
  → NS.bfSfin (coarsenBFs pos) ≡ false
  → NS.bfSnxt l d (coarsenBFs pos) (X , e) a ≡ just (coarsenBFs pos′)
  → absBFs l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFs l d pos′
aBFs l d pos pos′ finEq ceq = tableSpec-ev-fwd _ (coarsenBFs pos) finEq ceq

-- per-firing `coarsen ∘ nxt` commutations for the BF server
ceqBFs01 : ∀ {t0 md ln} {r} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsIdle (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch (MsgRequestRange r)) ≡ just (NS.bsAreq r)
ceqBFs01 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs02 : ∀ {t0 md ln} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsIdle (_ , output l d N2N_BlockFetch)
      (t0 , md , ln , blockFetch MsgClientDone) ≡ just NS.bsDdone
ceqBFs02 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs03 : ∀ {a} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsBusy (_ , apiBF l d sendBFStartBatch) a ≡ just NS.bsWsb
ceqBFs03 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs04 : ∀ {a} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsBusy (_ , apiBF l d sendBFNoBlocks) a ≡ just NS.bsWnb
ceqBFs04 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs05 : ∀ {b : Block} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsStream (_ , apiBF l d sendBFBlock) b ≡ just (NS.bsWblk b)
ceqBFs05 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs06 : ∀ {a} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsStream (_ , apiBF l d sendBFBatchDone) a ≡ just NS.bsWbd
ceqBFs06 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs07 : ∀ {r} (l : Link) (d : Dir)
  → NS.bfSnxt l d (NS.bsAreq r) (_ , apiBF l d reqBFRange) r ≡ just NS.bsBusy
ceqBFs07 {r} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl ⦃ DecEq-ChainRange ⦄ r = refl
ceqBFs08 : ∀ {a} (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsDdone (_ , done l d N2N_BlockFetch) a ≡ just NS.bsTerm
ceqBFs08 l d rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ceqBFs09 : (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsWsb (_ , input l d N2N_BlockFetch)
      (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ≡ just NS.bsStream
ceqBFs09 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) = refl
ceqBFs10 : (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsWnb (_ , input l d N2N_BlockFetch)
      (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ≡ just NS.bsIdle
ceqBFs10 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) = refl
ceqBFs11 : ∀ {b : Block} (l : Link) (d : Dir)
  → NS.bfSnxt l d (NS.bsWblk b) (_ , input l d N2N_BlockFetch)
      (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ≡ just NS.bsStream
ceqBFs11 {b} l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) = refl
ceqBFs12 : (l : Link) (d : Dir)
  → NS.bfSnxt l d NS.bsWbd (_ , input l d N2N_BlockFetch)
      (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ≡ just NS.bsIdle
ceqBFs12 l d rewrite ≟-yes-refl l | ≟-yes-refl d
  | ≟-yes-refl (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) = refl

-- SOURCE-side per-position ev inversion for the BF server (+ abstract twin step).
decBFs-src-ev-inv : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {P′ : BFProc}
  → decBFs-src l d pos BFL.─[ BFL.ev (BFL.evl (BFL.evLabel X e₁ a)) ]─► P′
  → Σ[ pos′ ∈ BFsPos ] (P′ ≡ decBFs-src l d pos′)
      × (absBFs l d pos ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► absBFs l d pos′)
-- head stIdle : receives RequestRange (→ bsReq1) / ClientDone (→ bsDone1)
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgRequestRange r)} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsReq1 r , trans (succVB-inv (decBFs-src l d (bsHead BF.stIdle)) s) (brBsReq l d r t0 md ln) , aBFs l d (bsHead BF.stIdle) (bsReq1 r) refl (ceqBFs01 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgClientDone} s with step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsDone1 , trans (succVB-inv (decBFs-src l d (bsHead BF.stIdle)) s) (brBsDone l d t0 md ln) , aBFs l d (bsHead BF.stIdle) bsDone1 refl (ceqBFs02 {t0} {md} {ln} l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync x}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission x} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify x}  s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch x}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stIdle) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stIdle)) refl s))
-- head stBusy : sends StartBatch (→ bsStart1) / NoBlocks (→ bsNoBlk1) via api
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFStartBatch} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsStart1 , succVB-inv (decBFs-src l d (bsHead BF.stBusy)) s , aBFs l d (bsHead BF.stBusy) bsStart1 refl (ceqBFs03 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFNoBlocks} s with step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsNoBlk1 , succVB-inv (decBFs-src l d (bsHead BF.stBusy)) s , aBFs l d (bsHead BF.stBusy) bsNoBlk1 refl (ceqBFs04 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' sendBFBatchDone}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stBusy) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stBusy)) refl s))
-- head stStreaming : sends Block (→ bsBlk1) / BatchDone (→ bsBatchDone1) via api
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBlock} {a} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsBlk1 a , succVB-inv (decBFs-src l d (bsHead BF.stStreaming)) s , aBFs l d (bsHead BF.stStreaming) (bsBlk1 a) refl (ceqBFs05 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFBatchDone} s with step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s
... | offer with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsBatchDone1 , succVB-inv (decBFs-src l d (bsHead BF.stStreaming)) s , aBFs l d (bsHead BF.stStreaming) bsBatchDone1 refl (ceqBFs06 l d)
...   | no  _    | _        = ⊥-elim (nothing-absurd offer)
...   | yes refl | no  _    = ⊥-elim (nothing-absurd offer)
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFRequestRange} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFClientDone}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFStartBatch}   s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' sendBFNoBlocks}     s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' recvBFBlock}        s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.apiBFev l' d' reqBFRange}         s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
decBFs-src-ev-inv l d (bsHead BF.stStreaming) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsHead BF.stStreaming)) refl s))
-- head stDone : `ret`
decBFs-src-ev-inv l d (bsHead BF.stDone) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()
-- mid bsReq1 r : fires api reqBFRange r (Output) → bsSil stBusy
decBFs-src-ev-inv l d (bsReq1 r) {e₁ = BF.apiBFev l' d' m} {a} s with step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s
... | offer with BF.BFEv-≟ (_ , BF.apiBFev l d reqBFRange) (_ , BF.apiBFev l' d' m)
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with _≟_ ⦃ DecEq-ChainRange ⦄ a r
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bsSil BF.stBusy , sym (just-injective offer) , aBFs l d (bsReq1 r) (bsSil BF.stBusy) refl (ceqBFs07 l d)
decBFs-src-ev-inv l d (bsReq1 r) {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-ev-inv l d (bsReq1 r) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
decBFs-src-ev-inv l d (bsReq1 r) {e₁ = BF.doneBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsReq1 r)) (kReq1 l d r) s))
-- mid bsDone1 : fires doneBF (Prefix₀) → bsSil stDone
decBFs-src-ev-inv l d bsDone1 {e₁ = BF.doneBF l' d'} s with step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.doneBF l d) (_ , BF.doneBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl = bsSil BF.stDone , sym (just-injective offer) , aBFs l d bsDone1 (bsSil BF.stDone) refl (ceqBFs08 l d)
decBFs-src-ev-inv l d bsDone1 {e₁ = BF.sendBF l' d'}    s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-ev-inv l d bsDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
decBFs-src-ev-inv l d bsDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsDone1) (ksDone1 l d) s))
-- mid bsStart1 : fires sendBF payload → bsSil stStreaming
decBFs-src-ev-inv l d bsStart1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bsSil BF.stStreaming , sym (just-injective offer) , aBFs l d bsStart1 (bsSil BF.stStreaming) refl (ceqBFs09 l d)
decBFs-src-ev-inv l d bsStart1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-ev-inv l d bsStart1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
decBFs-src-ev-inv l d bsStart1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsStart1) (kStart1 l d) s))
-- mid bsNoBlk1 : fires sendBF payload → bsSil stIdle
decBFs-src-ev-inv l d bsNoBlk1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bsSil BF.stIdle , sym (just-injective offer) , aBFs l d bsNoBlk1 (bsSil BF.stIdle) refl (ceqBFs10 l d)
decBFs-src-ev-inv l d bsNoBlk1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-ev-inv l d bsNoBlk1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
decBFs-src-ev-inv l d bsNoBlk1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsNoBlk1) (kNoBlk1 l d) s))
-- mid bsBlk1 b : fires sendBF payload → bsSil stStreaming
decBFs-src-ev-inv l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bsSil BF.stStreaming , sym (just-injective offer) , aBFs l d (bsBlk1 b) (bsSil BF.stStreaming) refl (ceqBFs11 l d)
decBFs-src-ev-inv l d (bsBlk1 b) {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-ev-inv l d (bsBlk1 b) {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
decBFs-src-ev-inv l d (bsBlk1 b) {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d (bsBlk1 b)) (kBlk1 l d b) s))
-- mid bsBatchDone1 : fires sendBF payload → bsSil stIdle
decBFs-src-ev-inv l d bsBatchDone1 {e₁ = BF.sendBF l' d'} {a} s with step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s
... | offer with BF.BFEv-≟ (_ , BF.sendBF l d) (_ , BF.sendBF l' d')
...   | no  _    = ⊥-elim (nothing-absurd offer)
...   | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | no  _    = ⊥-elim (nothing-absurd offer)
...     | yes refl = bsSil BF.stIdle , sym (just-injective offer) , aBFs l d bsBatchDone1 (bsSil BF.stIdle) refl (ceqBFs12 l d)
decBFs-src-ev-inv l d bsBatchDone1 {e₁ = BF.receiveBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-ev-inv l d bsBatchDone1 {e₁ = BF.apiBFev l' d' m} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
decBFs-src-ev-inv l d bsBatchDone1 {e₁ = BF.doneBF l' d'} s = ⊥-elim (nothing-absurd (step-target-BF (decBFs-src l d bsBatchDone1) (kBatchDone1 l d) s))
-- loop re-entry bsSil : forces to `sil`, no visible step
decBFs-src-ev-inv l d (bsSil st) s with BFL.ev-inv s
... | v , τc , feq , _ with feq
...   | ()

-- GAP-A (BlockFetch SERVER) per-peer simulation.
simBFs : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e : Net_Api Payload X} {a : X} {M : NetProc}
  → decBFs l d pos ─[ ev (evl (evLabel X e a)) ]─► M
  → Σ[ pos′ ∈ BFsPos ] (M ≡ decBFs l d pos′)
      × (absBFs l d pos ─[ ev (evl (evLabel X e a)) ]─► absBFs l d pos′)
simBFs l d pos step with BFNO.renameMap-ev-reflect-ι {P = decBFs-src l d pos} step
... | e₁ , P′ , iota , srcStep , Meq
      with decBFs-src-ev-inv l d pos srcStep | ιBF-inv-shape iota
...   | pos′ , P′eq , aStep | refl = pos′ , trans Meq (cong RenBF.renameMap P′eq) , aStep


{-# OPTIONS --guardedness #-}

------------------------------------------------------------------------
-- Praos Phase-2 R2 — io-peel layer, PART 5 (BACKWARD production leaves).
--
-- STEP 1 (this commit): `renameMap-ev-fwd` — transport a peer-LOCAL visible
-- fire FORWARD through `renameMap` (the MIRROR of `renameMap-ev-reflect`,
-- SysOracle_TauCore:384).  Since `decCSc = RenCS.renameMap ∘ decCSc-src`
-- (SysNode:707) and only the REVERSE existed, the forward emitter is the
-- atomic prerequisite for every backward `nodeX-ev-*-abs` production leaf.
-- Built GENERIC over the alphabet injection `ι` (parametrised module
-- `RenFwd`), so all 6 peers reuse the one lemma.
--
-- Re-exports PART 4 (`open import SysIoLink4 public`) so downstream consumers
-- import only SysIoLink5 (keeps SysIoLink4 frozen; cheap `.agdai` load).
------------------------------------------------------------------------

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( Block₃ )
module CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink5 (blkA : Block₃) where

open import Level using (0ℓ; Level)
open import Data.Maybe using (Maybe; just; nothing)
open import Data.Product using (Σ; Σ-syntax; _×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Process_Trees using ( PTree; ExtI; AnyTypes; ContinueType; react )

-- re-export PART 4 (node-τ abstract collapse) so downstream imports SysIoLink5
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysIoLink4 blkA public

open import CSP.Examples.Cardano_network.FourNode.FourNodeDiamond using ( p )
open import CSP.Examples.Cardano_network.Net p using ( Net_Api )
open import CSP.Examples.Cardano_network.Data p using ( Payload )

open import Semantics.LTS {E = Net_Api Payload} {I = ExtI (Net_Api Payload)}
  using ( _─[_]─►_; ev; evl; evLabel; sVis; τ; sSil )

------------------------------------------------------------------------
-- STEP 2 preamble — imports + LTS/rename instances for the CONCRETE offer
-- builders (`csc-fire-*`) and the CS/BF backward production leaves.
------------------------------------------------------------------------
import Data.Unit as U
import Class.DecEq.Instances as DecEqI
open import Data.Fin using ( Fin; zero; suc )
open import CSP.Examples.Cardano_network.Base using ( Dir; lo; hi; FromInitiator; FromResponder )
open import CSP.Examples.Cardano_network.Params using ( Params )
open Params p using ( time₀; length₀; Block; decBlock; decVoteBlob )
open import CSP.Examples.Cardano_network.Net p using
  ( Link; sendCSRequestNext; sendCSFindIntersect; sendCSDone
  ; recvCSRollforward; recvCSRollback; recvCSIntersectFound; recvCSIntersectNotFound )
open import CSP.Examples.Cardano_network.Data p using
  ( chainSync; Header; Tip; Point
  ; MsgCSRollForward; MsgCSRollBackward; MsgCSAwaitReply
  ; MsgCSIntersectFound; MsgCSIntersectNotFound
  ; MsgCSRequestNext; MsgCSFindIntersect; MsgCSDone
  ; DecEq-Payload; DecEq-Header; DecEq-Tip; DecEq-Point )
import CSP.Examples.Cardano_network.ChainSync p as CS
open import CSP.Examples.Cardano_network.NetworkPar p using
  ( ιCS; ιCS⁻¹; ιCS-linv )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysNode blkA as MSysNode
open MSysNode using
  ( CScPos; csHead; csReqNext1; csFindInt1; csDone1
  ; csRF1; csRB1; csIF1; csINF1; csSil
  ; decCSc-src; vis-ofC; decCSc
  ; CSsPos; ssHead; ssReqNext1; ssFindInt1; ssDone1
  ; ssRF1; ssRB1; ssAw1; ssIF1; ssINF1; ssSil
  ; decCSs-src; decCSs )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_TauCore blkA using
  ( ≟-yes-refl )

-- the CS SOURCE-alphabet LTS (same instance the peer `renameMap` reflects into)
import Semantics.LTS {E = CS.CSEv} {I = ExtI CS.CSEv} as CSL

------------------------------------------------------------------------
-- STEP 2 (CS-CLIENT backward production leaf) — extra imports for the
-- abstract-side inversion (`tableSpec-ev-inv`), the coarse table + edge
-- commutations (`ceqCSc*`), the weak run wrapper, and the closers.
------------------------------------------------------------------------
open import Data.Empty using ( ⊥-elim )
open import Relation.Nullary using ( yes; no )
open import Data.Maybe.Properties using ( just-injective )
open import Class.DecEq using ( _≟_ )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.NodeSpecs blkA as NS
open NS using ( tableSpec )
import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysStep blkA as MSysStep
open MSysStep using
  ( NetProc; absCSc; coarsenCSc; coarsenCScSt; decCSc-sil-step
  ; absCSs; coarsenCSs; coarsenCSsSt; decCSs-sil-step )
open import CSP.Examples.Cardano_network.NetworkVerification.Praos.SysOracle_NodeTauEv blkA using
  ( tableSpec-ev-inv; nothing-absurd )
open import Semantics.WeakBisim {E = Net_Api Payload} {I = ExtI (Net_Api Payload)} using
  ( _═[_]═►_; wev; τ*-refl; τ*-step )
-- extra ApiCSTag constructors (the non-firing tags at `ccIdle`/api positions)
open import CSP.Examples.Cardano_network.Net p using
  ( sendCSAwaitReply; sendCSRollForward; sendCSRollBackward
  ; sendCSIntersectFound; sendCSIntersectNotFound
  ; reqCSRequestNext; reqCSFindIntersect )
-- extra Payload body constructors (the non-ChainSync wire payloads)
open import CSP.Examples.Cardano_network.Data p using
  ( keepAlive; blockFetch; txSubmission; leiosNotify; leiosFetch
  ; MsgTSInit; MsgTSRequestTxIds; MsgTSReplyTxIds; MsgTSRequestTxs; MsgTSReplyTxs; MsgTSDone
  ; MsgLNRequestNext; MsgLNBlockAnnouncement; MsgLNBlockOffer; MsgLNBlockTxsOffer; MsgLNVotesOffer; MsgLNDone
  ; MsgLFBlockRequest; MsgLFBlockTxsRequest; MsgLFVotesRequest; MsgLFBlockRangeRequest; MsgLFDone
  ; MsgLFBlock; MsgLFBlockTxs; MsgLFVoteDelivery; MsgLFNextBlockAndTxsInRange; MsgLFLastBlockAndTxsInRange
  ; DecEq-Tx )

------------------------------------------------------------------------
-- STEP 2 (BF client + server) — BlockFetch alphabet + model imports.
------------------------------------------------------------------------
import CSP.Examples.Cardano_network.BlockFetch p as BF
open import CSP.Examples.Cardano_network.NetworkPar p using
  ( ιBF; ιBF⁻¹; ιBF-linv )
open import CSP.Examples.Cardano_network.Net p using
  ( sendBFRequestRange; sendBFClientDone; sendBFStartBatch; sendBFNoBlocks
  ; sendBFBlock; sendBFBatchDone; recvBFBlock; reqBFRange )
open import CSP.Examples.Cardano_network.Data p using
  ( ChainRange; DecEq-ChainRange
  ; MsgRequestRange; MsgClientDone; MsgStartBatch; MsgNoBlocks
  ; MsgBlock; MsgBatchDone )
open MSysNode using
  ( BFcPos; bcHead; bcReq1; bcDone1; bcBlk1; bcSil
  ; BFsPos; bsHead; bsReq1; bsDone1; bsStart1; bsNoBlk1; bsBlk1; bsBatchDone1; bsSil
  ; decBFc-src; decBFs-src; decBFc; decBFs; vis-ofB )
open MSysStep using
  ( absBFc; absBFs; coarsenBFc; coarsenBFs; decBFc-sil-step; decBFs-sil-step )
-- the BF SOURCE-alphabet LTS
import Semantics.LTS {E = BF.BFEv} {I = ExtI BF.BFEv} as BFL

------------------------------------------------------------------------
-- INERT PEER: KeepAlive (KA) client + server — alphabet + model imports.
------------------------------------------------------------------------
import CSP.Examples.Cardano_network.KeepAlive p as KA
open import CSP.Examples.Cardano_network.NetworkPar p using
  ( ιKA; ιKA⁻¹; ιKA-linv )
open import CSP.Examples.Cardano_network.Net p using
  ( sendKAMsg; sendKADone; recvKACookie; errCookie )
open import CSP.Examples.Cardano_network.Data p using
  ( MsgKeepAlive; MsgKeepAliveResponse; MsgKADone )
open MSysNode using
  ( KAcPos; kcHead; kcErr1; kcReq1; kcDone1; kcSil; kcTermE1
  ; KAsPos; ksHead; ksRecv1; ksDdone1; ksSil
  ; decKAc-src; decKAs-src; decKAc; decKAs; vis-ofK )
open MSysStep using
  ( absKAc; absKAs; coarsenKAc; coarsenKAs )
-- the KA SOURCE-alphabet LTS
import Semantics.LTS {E = KA.KAEv} {I = ExtI KA.KAEv} as KAL

------------------------------------------------------------------------
-- INERT PEER: TxSubmission (TS) client + server — alphabet + model imports.
-- Role-INVERTED (server sends Request*, client sends Reply*); value carriers
-- BlockingStyle×ℕ×ℕ / List Txid / List Tx are NON-trivial (unlike KA's ⊤).
------------------------------------------------------------------------
import CSP.Examples.Cardano_network.TxSubmission p as TS
open import CSP.Examples.Cardano_network.NetworkPar p using
  ( ιTS; ιTS⁻¹; ιTS-linv )
open import CSP.Examples.Cardano_network.Net p using
  ( sendTSReplyTxIds; sendTSReplyTxs; sendTSDone
  ; sendTSRequestTxIdsBlocking; sendTSRequestTxIdsPipelined; sendTSRequestTxsPipelined
  ; recvTSRequestTxIds; recvTSRequestTxs )
open import CSP.Examples.Cardano_network.Base using
  ( BlockingStyle; Blocking; NonBlocking )
open import Data.Nat using ( ℕ )
open import Data.List using ( List )
open MSysNode using
  ( TScPos; tcHead; tcReqIdsB1; tcReqIdsNB1; tcReqTxs1; tcRepB1; tcDone1; tcRepNB1; tcRepTxs1; tcSil
  ; TSsPos; tsHead; tsDone1; tsReqB1; tsReqNB1; tsReqTxs1; tsSil
  ; decTSc-src; decTSs-src; decTSc; decTSs; vis-ofT )
open MSysStep using
  ( absTSc; absTSs; coarsenTSc; coarsenTSs )
-- the TS SOURCE-alphabet LTS
import Semantics.LTS {E = TS.TSEv} {I = ExtI TS.TSEv} as TSL

------------------------------------------------------------------------
-- INERT PEER: LeiosNotify (LN) client + server — alphabet + model imports.
-- Value carriers Header / Point (Block₃-based, plain `≟`) + List Vote
-- (bare list → the source's named `DecEq-ListVote`, mirroring the table).
------------------------------------------------------------------------
import CSP.Examples.Cardano_network.LeiosNotify p as LN
open import CSP.Examples.Cardano_network.NetworkPar p using
  ( ιLN; ιLN⁻¹; ιLN-linv )
open import CSP.Examples.Cardano_network.Net p using
  ( sendLNRequestNext; sendLNDone; sendLNBlockAnnouncement; sendLNBlockOffer
  ; sendLNBlockTxsOffer; sendLNVotesOffer; recvLNBlockAnnouncement
  ; recvLNBlockOffer; recvLNBlockTxsOffer; recvLNVotesOffer )
open MSysNode using
  ( LNcPos; lncHead; lncRann1; lncRoff1; lncRtxs1; lncRvot1; lncReq1; lncDone1; lncSil
  ; LNsPos; lnsHead; lnsDone1; lnsWann1; lnsWoff1; lnsWtxs1; lnsWvot1; lnsSil
  ; decLNc-src; decLNs-src; decLNc; decLNs; vis-ofN )
open MSysStep using
  ( absLNc; absLNs; coarsenLNc; coarsenLNs )
-- the LN SOURCE-alphabet LTS
import Semantics.LTS {E = LN.LNEv} {I = ExtI LN.LNEv} as LNL

------------------------------------------------------------------------
-- INERT PEER: LeiosFetch (LF) client + server — alphabet + model imports.
-- LAST inert peer; hardest: 6 states, 11 client + 8 server positions,
-- value carriers Block / List Tx / List VoteBlob / Block×List Tx / Point /
-- Point×LFBitmap / ChainRange / List Vote.  LF has NO named List instance —
-- the api-emit mid List gates use `DecEqI.DecEq-List` directly.
------------------------------------------------------------------------
import CSP.Examples.Cardano_network.LeiosFetch p as LF
open import CSP.Examples.Cardano_network.NetworkPar p using
  ( ιLF; ιLF⁻¹; ιLF-linv )
open import CSP.Examples.Cardano_network.Net p using
  ( sendLFBlockRequest; sendLFBlockTxsRequest; sendLFVotesRequest
  ; sendLFBlockRangeRequest; sendLFDone; sendLFBlock; sendLFBlockTxs
  ; sendLFVoteDelivery; sendLFNextBlockAndTxsInRange; sendLFLastBlockAndTxsInRange
  ; recvLFBlock; recvLFBlockTxs; recvLFVoteDelivery; recvLFRangeBlock )
open MSysNode using
  ( LFcPos; lfcHead; lfcRblk1; lfcRbtx1; lfcRvot1; lfcRnext1; lfcRlast1
  ; lfcWblk1; lfcWtxs1; lfcWvot1; lfcWrng1; lfcDone1; lfcSil
  ; LFsPos; lfsHead; lfsDone1; lfsWblk1; lfsWtxs1; lfsWvot1; lfsWnext1; lfsWlast1; lfsSil
  ; decLFc-src; decLFs-src; decLFc; decLFs; vis-ofF )
open MSysStep using
  ( absLFc; absLFs; coarsenLFc; coarsenLFs )
-- the LF SOURCE-alphabet LTS
import Semantics.LTS {E = LF.LFEv} {I = ExtI LF.LFEv} as LFL

------------------------------------------------------------------------
-- Generic `renameMap` FORWARD visible transport, parametrised over an
-- alphabet injection `ι : E₁ → Net_Api Payload` (instantiated at ιCS / ιBF
-- / … per peer kind — the exact mirror of `RenTC` in SysOracle_TauCore).
------------------------------------------------------------------------
module RenFwd {ℓe₁ : Level} {E₁ : Set 0ℓ → Set ℓe₁}
  (ι      : ∀ {A} → E₁ A → Net_Api Payload A)
  (ι⁻¹    : ∀ {A} → Net_Api Payload A → Maybe (E₁ A))
  (ι-linv : ∀ {A} (e : E₁ A) → ι⁻¹ (ι e) ≡ just e)
  where
  open import CSP.Rename {E₁ = E₁} {E₂ = Net_Api Payload} ι ι⁻¹ ι-linv
    using ( renameMap; extBranch; extBwd; invRel; invPreimg; ι-vis-inv
          ; rnFan; rnCollect )
  import Semantics.LTS {E = E₁} {I = ExtI E₁} as L₁

  -- force of a renamed react (identical to RenTC's; re-derived to stay
  -- self-contained — a single definitional unfolding under `P .force`)
  force-renameMap-react : {Rr : Set} {P : PTree E₁ (ExtI E₁) Rr}
      {vP  : (at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr))}
      {τcP : (i : AnyTypes (ExtI E₁)) → ContinueType i (Maybe (PTree E₁ (ExtI E₁) Rr))}
    → PTree.force P ≡ react vP τcP
    → PTree.force (renameMap P) ≡
        react (λ bt b → rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
                              (rnCollect vP (invPreimg ι-vis-inv bt b)))
              (extBranch (invRel ι-vis-inv) (invPreimg ι-vis-inv) τcP)
  force-renameMap-react {P = P} eq with PTree.force P | eq
  ... | react vP τcP | refl = refl

  -- the renamed VISIBLE-offer at target `(X , ι e₁)` FIRES to `renameMap P′`:
  -- `rewrite ι-linv` collapses `ι-vis-inv`'s `ι⁻¹ (ι e₁)` to `just e₁`, so
  -- `invPreimg` reduces to the singleton `[((X,e₁),b,refl)]`; `rewrite vpe`
  -- collapses `rnCollect vP [_]` to `[P′]`; and
  -- `rnFan _ _ [P′] = just (P′ ⟦ … ⟧) = just (renameMap P′)` definitionally.
  rn-vis-fwd : {Rr : Set}
      (vP : (at : AnyTypes E₁) → ContinueType at (Maybe (PTree E₁ (ExtI E₁) Rr)))
      {X : Set 0ℓ} (e₁ : E₁ X) (b : X) {P′ : PTree E₁ (ExtI E₁) Rr}
    → vP (X , e₁) b ≡ just P′
    → rnFan (invRel ι-vis-inv) (invPreimg ι-vis-inv)
            (rnCollect vP (invPreimg ι-vis-inv (X , ι e₁) b)) ≡ just (renameMap P′)
  rn-vis-fwd vP e₁ b vpe rewrite ι-linv e₁ | vpe = refl

  -- FORWARD renamed visible step (the atomic backward-production brick): a
  -- SOURCE fire `P ─[ev e₁ b]─► P′` lifts to `renameMap P ─[ev (ι e₁) b]─►
  -- renameMap P′`.  MIRROR of `renameMap-ev-reflect` (SysOracle_TauCore:384).
  renameMap-ev-fwd : {Rr : Set} {P P′ : PTree E₁ (ExtI E₁) Rr} {X : Set 0ℓ}
      {e₁ : E₁ X} {b : X}
    → P L₁.─[ L₁.ev (L₁.evl (L₁.evLabel X e₁ b)) ]─► P′
    → renameMap P ─[ ev (evl (evLabel X (ι e₁) b)) ]─► renameMap P′
  renameMap-ev-fwd {P = P} {e₁ = e₁} {b = b} step with L₁.ev-inv step
  ... | vP , τcP , eqP , vpe =
        sVis (force-renameMap-react {P = P} eqP) (rn-vis-fwd vP e₁ b vpe)

-- FORWARD renamed-fire emitter at the ChainSync alphabet: `renameMap-ev-fwd`
-- specialised to `ιCS` — lifts a CS source fire to the concrete `decCSc` peer.
module RFCS = RenFwd {E₁ = CS.CSEv} ιCS ιCS⁻¹ ιCS-linv

-- FORWARD renamed-fire emitter at the BlockFetch alphabet (ιBF instance)
module RFBF = RenFwd {E₁ = BF.BFEv} ιBF ιBF⁻¹ ιBF-linv

-- FORWARD renamed-fire emitter at the KeepAlive alphabet (ιKA instance)
module RFKA = RenFwd {E₁ = KA.KAEv} ιKA ιKA⁻¹ ιKA-linv

-- FORWARD renamed-fire emitter at the TxSubmission alphabet (ιTS instance)
module RFTS = RenFwd {E₁ = TS.TSEv} ιTS ιTS⁻¹ ιTS-linv

-- FORWARD renamed-fire emitter at the LeiosNotify alphabet (ιLN instance)
module RFLN = RenFwd {E₁ = LN.LNEv} ιLN ιLN⁻¹ ιLN-linv

-- FORWARD renamed-fire emitter at the LeiosFetch alphabet (ιLF instance)
module RFLF = RenFwd {E₁ = LF.LFEv} ιLF ιLF⁻¹ ιLF-linv

------------------------------------------------------------------------
-- STEP 2 (CS-CLIENT concrete offer builders) — the PRODUCTION-direction
-- mirror of `decCSc-src-ev-inv`'s per-firing `succVC` reductions (the
-- `ceqCSc*`/`br*` twins).  Each `csc-fire-*` emits the SOURCE-alphabet
-- visible fire `decCSc-src l d pos ─[ev e₁ a]─► decCSc-src l d pos′`, ready
-- to lift through `RFCS.renameMap-ev-fwd` onto the concrete `decCSc` peer.
------------------------------------------------------------------------

-- head stIdle → csReqNext1 (fires apiCSev sendCSRequestNext)
csc-fire-reqNext : (l : Link) (d : Dir)
  → decCSc-src l d (csHead CS.stIdle)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d sendCSRequestNext) U.tt)) ]─►
    decCSc-src l d csReqNext1
csc-fire-reqNext l d = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src l d (csHead CS.stIdle)))
          (_ , CS.apiCSev l d sendCSRequestNext) U.tt ≡ just (decCSc-src l d csReqNext1)
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stCanAwait → csRF1 h t (fires receiveCS with a RollForward payload)
csc-fire-rf-CA : (l : Link) (d : Dir) (h : Header) (t : Tip) (t0 : _) (md : _) (ln : _)
  → decCSc-src l d (csHead CS.stCanAwait)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.receiveCS l d)
               (t0 , md , ln , chainSync (MsgCSRollForward h t)))) ]─►
    decCSc-src l d (csRF1 h t)
csc-fire-rf-CA l d h t t0 md ln = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src l d (csHead CS.stCanAwait)))
          (_ , CS.receiveCS l d) (t0 , md , ln , chainSync (MsgCSRollForward h t))
          ≡ just (decCSc-src l d (csRF1 h t))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stIdle → csFindInt1 ps (fires apiCSev sendCSFindIntersect)
csc-fire-findInt : (l : Link) (d : Dir) (ps : _)
  → decCSc-src l d (csHead CS.stIdle)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d sendCSFindIntersect) ps)) ]─►
    decCSc-src l d (csFindInt1 ps)
csc-fire-findInt l d ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src l d (csHead CS.stIdle)))
          (_ , CS.apiCSev l d sendCSFindIntersect) ps ≡ just (decCSc-src l d (csFindInt1 ps))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stIdle → csDone1 (fires apiCSev sendCSDone)
csc-fire-sendDone : (l : Link) (d : Dir)
  → decCSc-src l d (csHead CS.stIdle)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d sendCSDone) U.tt)) ]─►
    decCSc-src l d csDone1
csc-fire-sendDone l d = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src l d (csHead CS.stIdle)))
          (_ , CS.apiCSev l d sendCSDone) U.tt ≡ just (decCSc-src l d csDone1)
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stCanAwait → csRB1 pt tp (fires receiveCS with a RollBackward payload)
csc-fire-rb-CA : (l : Link) (d : Dir) (pt : Point) (tp : Tip) (t0 : _) (md : _) (ln : _)
  → decCSc-src l d (csHead CS.stCanAwait)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.receiveCS l d)
               (t0 , md , ln , chainSync (MsgCSRollBackward pt tp)))) ]─►
    decCSc-src l d (csRB1 pt tp)
csc-fire-rb-CA l d pt tp t0 md ln = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src l d (csHead CS.stCanAwait)))
          (_ , CS.receiveCS l d) (t0 , md , ln , chainSync (MsgCSRollBackward pt tp))
          ≡ just (decCSc-src l d (csRB1 pt tp))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stCanAwait → csSil stMustReply (fires receiveCS with AwaitReply)
csc-fire-aw-CA : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decCSc-src l d (csHead CS.stCanAwait)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.receiveCS l d)
               (t0 , md , ln , chainSync MsgCSAwaitReply))) ]─►
    decCSc-src l d (csSil CS.stMustReply)
csc-fire-aw-CA l d t0 md ln = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src l d (csHead CS.stCanAwait)))
          (_ , CS.receiveCS l d) (t0 , md , ln , chainSync MsgCSAwaitReply)
          ≡ just (decCSc-src l d (csSil CS.stMustReply))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stMustReply → csRF1 h t (fires receiveCS with a RollForward payload)
csc-fire-rf-MR : (l : Link) (d : Dir) (h : Header) (t : Tip) (t0 : _) (md : _) (ln : _)
  → decCSc-src l d (csHead CS.stMustReply)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.receiveCS l d)
               (t0 , md , ln , chainSync (MsgCSRollForward h t)))) ]─►
    decCSc-src l d (csRF1 h t)
csc-fire-rf-MR l d h t t0 md ln = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src l d (csHead CS.stMustReply)))
          (_ , CS.receiveCS l d) (t0 , md , ln , chainSync (MsgCSRollForward h t))
          ≡ just (decCSc-src l d (csRF1 h t))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stMustReply → csRB1 pt tp (fires receiveCS with a RollBackward payload)
csc-fire-rb-MR : (l : Link) (d : Dir) (pt : Point) (tp : Tip) (t0 : _) (md : _) (ln : _)
  → decCSc-src l d (csHead CS.stMustReply)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.receiveCS l d)
               (t0 , md , ln , chainSync (MsgCSRollBackward pt tp)))) ]─►
    decCSc-src l d (csRB1 pt tp)
csc-fire-rb-MR l d pt tp t0 md ln = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src l d (csHead CS.stMustReply)))
          (_ , CS.receiveCS l d) (t0 , md , ln , chainSync (MsgCSRollBackward pt tp))
          ≡ just (decCSc-src l d (csRB1 pt tp))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stIntersect → csIF1 pt tp (fires receiveCS with an IntersectFound payload)
csc-fire-if : (l : Link) (d : Dir) (pt : Point) (tp : Tip) (t0 : _) (md : _) (ln : _)
  → decCSc-src l d (csHead CS.stIntersect)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.receiveCS l d)
               (t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)))) ]─►
    decCSc-src l d (csIF1 pt tp)
csc-fire-if l d pt tp t0 md ln = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src l d (csHead CS.stIntersect)))
          (_ , CS.receiveCS l d) (t0 , md , ln , chainSync (MsgCSIntersectFound pt tp))
          ≡ just (decCSc-src l d (csIF1 pt tp))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stIntersect → csINF1 tp (fires receiveCS with an IntersectNotFound payload)
csc-fire-inf : (l : Link) (d : Dir) (tp : Tip) (t0 : _) (md : _) (ln : _)
  → decCSc-src l d (csHead CS.stIntersect)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.receiveCS l d)
               (t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)))) ]─►
    decCSc-src l d (csINF1 tp)
csc-fire-inf l d tp t0 md ln = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src l d (csHead CS.stIntersect)))
          (_ , CS.receiveCS l d) (t0 , md , ln , chainSync (MsgCSIntersectNotFound tp))
          ≡ just (decCSc-src l d (csINF1 tp))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- MID-BUILDERS-BEGIN
------------------------------------------------------------------------
-- STEP 2 (CS-CLIENT MID offer builders) — the 7 mid-position fires.
-- Fin-enum fix (M1): pattern-match l,d into concrete Fin/Dir literals so
-- the succVC head-api gate AND the exposed output/api-node gate reduce
-- definitionally; the remaining payload/value `≟` is closed by
-- `rewrite ≟-yes-refl {A = …} <a>` (typed so DecEq resolves to the peer's).
------------------------------------------------------------------------

csc-fire-reqNext1 : (l : Link) (d : Dir)
  → decCSc-src l d csReqNext1
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.sendCS l d) (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext))) ]─►
    decCSc-src l d (csSil CS.stCanAwait)
csc-fire-reqNext1 (zero) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) lo csReqNext1))
          (_ , CS.sendCS (zero) lo) (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ≡ just (decCSc-src (zero) lo (csSil CS.stCanAwait))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) = refl
csc-fire-reqNext1 (zero) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) hi csReqNext1))
          (_ , CS.sendCS (zero) hi) (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ≡ just (decCSc-src (zero) hi (csSil CS.stCanAwait))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) = refl
csc-fire-reqNext1 (suc zero) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) lo csReqNext1))
          (_ , CS.sendCS (suc zero) lo) (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ≡ just (decCSc-src (suc zero) lo (csSil CS.stCanAwait))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) = refl
csc-fire-reqNext1 (suc zero) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) hi csReqNext1))
          (_ , CS.sendCS (suc zero) hi) (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ≡ just (decCSc-src (suc zero) hi (csSil CS.stCanAwait))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) = refl
csc-fire-reqNext1 (suc (suc zero)) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) lo csReqNext1))
          (_ , CS.sendCS (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ≡ just (decCSc-src (suc (suc zero)) lo (csSil CS.stCanAwait))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) = refl
csc-fire-reqNext1 (suc (suc zero)) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) hi csReqNext1))
          (_ , CS.sendCS (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ≡ just (decCSc-src (suc (suc zero)) hi (csSil CS.stCanAwait))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) = refl
csc-fire-reqNext1 (suc (suc (suc zero))) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) lo csReqNext1))
          (_ , CS.sendCS (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ≡ just (decCSc-src (suc (suc (suc zero))) lo (csSil CS.stCanAwait))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) = refl
csc-fire-reqNext1 (suc (suc (suc zero))) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) hi csReqNext1))
          (_ , CS.sendCS (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) ≡ just (decCSc-src (suc (suc (suc zero))) hi (csSil CS.stCanAwait))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext) = refl

csc-fire-findInt1 : (l : Link) (d : Dir) (ps : _)
  → decCSc-src l d (csFindInt1 ps)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.sendCS l d) (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)))) ]─►
    decCSc-src l d (csSil CS.stIntersect)
csc-fire-findInt1 (zero) lo ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) lo (csFindInt1 ps)))
          (_ , CS.sendCS (zero) lo) (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) ≡ just (decCSc-src (zero) lo (csSil CS.stIntersect))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) = refl
csc-fire-findInt1 (zero) hi ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) hi (csFindInt1 ps)))
          (_ , CS.sendCS (zero) hi) (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) ≡ just (decCSc-src (zero) hi (csSil CS.stIntersect))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) = refl
csc-fire-findInt1 (suc zero) lo ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) lo (csFindInt1 ps)))
          (_ , CS.sendCS (suc zero) lo) (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) ≡ just (decCSc-src (suc zero) lo (csSil CS.stIntersect))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) = refl
csc-fire-findInt1 (suc zero) hi ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) hi (csFindInt1 ps)))
          (_ , CS.sendCS (suc zero) hi) (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) ≡ just (decCSc-src (suc zero) hi (csSil CS.stIntersect))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) = refl
csc-fire-findInt1 (suc (suc zero)) lo ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) lo (csFindInt1 ps)))
          (_ , CS.sendCS (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) ≡ just (decCSc-src (suc (suc zero)) lo (csSil CS.stIntersect))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) = refl
csc-fire-findInt1 (suc (suc zero)) hi ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) hi (csFindInt1 ps)))
          (_ , CS.sendCS (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) ≡ just (decCSc-src (suc (suc zero)) hi (csSil CS.stIntersect))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) = refl
csc-fire-findInt1 (suc (suc (suc zero))) lo ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) lo (csFindInt1 ps)))
          (_ , CS.sendCS (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) ≡ just (decCSc-src (suc (suc (suc zero))) lo (csSil CS.stIntersect))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) = refl
csc-fire-findInt1 (suc (suc (suc zero))) hi ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) hi (csFindInt1 ps)))
          (_ , CS.sendCS (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) ≡ just (decCSc-src (suc (suc (suc zero))) hi (csSil CS.stIntersect))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps)) = refl

csc-fire-done1 : (l : Link) (d : Dir)
  → decCSc-src l d csDone1
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.sendCS l d) (time₀ , FromInitiator , length₀ , chainSync MsgCSDone))) ]─►
    decCSc-src l d (csSil CS.stDone)
csc-fire-done1 (zero) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) lo csDone1))
          (_ , CS.sendCS (zero) lo) (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ≡ just (decCSc-src (zero) lo (csSil CS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) = refl
csc-fire-done1 (zero) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) hi csDone1))
          (_ , CS.sendCS (zero) hi) (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ≡ just (decCSc-src (zero) hi (csSil CS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) = refl
csc-fire-done1 (suc zero) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) lo csDone1))
          (_ , CS.sendCS (suc zero) lo) (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ≡ just (decCSc-src (suc zero) lo (csSil CS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) = refl
csc-fire-done1 (suc zero) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) hi csDone1))
          (_ , CS.sendCS (suc zero) hi) (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ≡ just (decCSc-src (suc zero) hi (csSil CS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) = refl
csc-fire-done1 (suc (suc zero)) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) lo csDone1))
          (_ , CS.sendCS (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ≡ just (decCSc-src (suc (suc zero)) lo (csSil CS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) = refl
csc-fire-done1 (suc (suc zero)) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) hi csDone1))
          (_ , CS.sendCS (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ≡ just (decCSc-src (suc (suc zero)) hi (csSil CS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) = refl
csc-fire-done1 (suc (suc (suc zero))) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) lo csDone1))
          (_ , CS.sendCS (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ≡ just (decCSc-src (suc (suc (suc zero))) lo (csSil CS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) = refl
csc-fire-done1 (suc (suc (suc zero))) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) hi csDone1))
          (_ , CS.sendCS (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) ≡ just (decCSc-src (suc (suc (suc zero))) hi (csSil CS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , chainSync MsgCSDone) = refl

csc-fire-rf1 : (l : Link) (d : Dir) (h : Header) (t : Tip)
  → decCSc-src l d (csRF1 h t)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d recvCSRollforward) (h , t))) ]─►
    decCSc-src l d (csSil CS.stIdle)
csc-fire-rf1 (zero) lo h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) lo (csRF1 h t)))
          (_ , CS.apiCSev (zero) lo recvCSRollforward) (h , t) ≡ just (decCSc-src (zero) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Header × Tip)} (h , t) = refl
csc-fire-rf1 (zero) hi h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) hi (csRF1 h t)))
          (_ , CS.apiCSev (zero) hi recvCSRollforward) (h , t) ≡ just (decCSc-src (zero) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Header × Tip)} (h , t) = refl
csc-fire-rf1 (suc zero) lo h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) lo (csRF1 h t)))
          (_ , CS.apiCSev (suc zero) lo recvCSRollforward) (h , t) ≡ just (decCSc-src (suc zero) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Header × Tip)} (h , t) = refl
csc-fire-rf1 (suc zero) hi h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) hi (csRF1 h t)))
          (_ , CS.apiCSev (suc zero) hi recvCSRollforward) (h , t) ≡ just (decCSc-src (suc zero) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Header × Tip)} (h , t) = refl
csc-fire-rf1 (suc (suc zero)) lo h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) lo (csRF1 h t)))
          (_ , CS.apiCSev (suc (suc zero)) lo recvCSRollforward) (h , t) ≡ just (decCSc-src (suc (suc zero)) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Header × Tip)} (h , t) = refl
csc-fire-rf1 (suc (suc zero)) hi h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) hi (csRF1 h t)))
          (_ , CS.apiCSev (suc (suc zero)) hi recvCSRollforward) (h , t) ≡ just (decCSc-src (suc (suc zero)) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Header × Tip)} (h , t) = refl
csc-fire-rf1 (suc (suc (suc zero))) lo h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) lo (csRF1 h t)))
          (_ , CS.apiCSev (suc (suc (suc zero))) lo recvCSRollforward) (h , t) ≡ just (decCSc-src (suc (suc (suc zero))) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Header × Tip)} (h , t) = refl
csc-fire-rf1 (suc (suc (suc zero))) hi h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) hi (csRF1 h t)))
          (_ , CS.apiCSev (suc (suc (suc zero))) hi recvCSRollforward) (h , t) ≡ just (decCSc-src (suc (suc (suc zero))) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Header × Tip)} (h , t) = refl

csc-fire-rb1 : (l : Link) (d : Dir) (pt : Point) (tp : Tip)
  → decCSc-src l d (csRB1 pt tp)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d recvCSRollback) (pt , tp))) ]─►
    decCSc-src l d (csSil CS.stIdle)
csc-fire-rb1 (zero) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) lo (csRB1 pt tp)))
          (_ , CS.apiCSev (zero) lo recvCSRollback) (pt , tp) ≡ just (decCSc-src (zero) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-rb1 (zero) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) hi (csRB1 pt tp)))
          (_ , CS.apiCSev (zero) hi recvCSRollback) (pt , tp) ≡ just (decCSc-src (zero) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-rb1 (suc zero) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) lo (csRB1 pt tp)))
          (_ , CS.apiCSev (suc zero) lo recvCSRollback) (pt , tp) ≡ just (decCSc-src (suc zero) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-rb1 (suc zero) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) hi (csRB1 pt tp)))
          (_ , CS.apiCSev (suc zero) hi recvCSRollback) (pt , tp) ≡ just (decCSc-src (suc zero) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-rb1 (suc (suc zero)) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) lo (csRB1 pt tp)))
          (_ , CS.apiCSev (suc (suc zero)) lo recvCSRollback) (pt , tp) ≡ just (decCSc-src (suc (suc zero)) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-rb1 (suc (suc zero)) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) hi (csRB1 pt tp)))
          (_ , CS.apiCSev (suc (suc zero)) hi recvCSRollback) (pt , tp) ≡ just (decCSc-src (suc (suc zero)) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-rb1 (suc (suc (suc zero))) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) lo (csRB1 pt tp)))
          (_ , CS.apiCSev (suc (suc (suc zero))) lo recvCSRollback) (pt , tp) ≡ just (decCSc-src (suc (suc (suc zero))) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-rb1 (suc (suc (suc zero))) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) hi (csRB1 pt tp)))
          (_ , CS.apiCSev (suc (suc (suc zero))) hi recvCSRollback) (pt , tp) ≡ just (decCSc-src (suc (suc (suc zero))) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl

csc-fire-if1 : (l : Link) (d : Dir) (pt : Point) (tp : Tip)
  → decCSc-src l d (csIF1 pt tp)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d recvCSIntersectFound) (pt , tp))) ]─►
    decCSc-src l d (csSil CS.stIdle)
csc-fire-if1 (zero) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) lo (csIF1 pt tp)))
          (_ , CS.apiCSev (zero) lo recvCSIntersectFound) (pt , tp) ≡ just (decCSc-src (zero) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-if1 (zero) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) hi (csIF1 pt tp)))
          (_ , CS.apiCSev (zero) hi recvCSIntersectFound) (pt , tp) ≡ just (decCSc-src (zero) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-if1 (suc zero) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) lo (csIF1 pt tp)))
          (_ , CS.apiCSev (suc zero) lo recvCSIntersectFound) (pt , tp) ≡ just (decCSc-src (suc zero) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-if1 (suc zero) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) hi (csIF1 pt tp)))
          (_ , CS.apiCSev (suc zero) hi recvCSIntersectFound) (pt , tp) ≡ just (decCSc-src (suc zero) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-if1 (suc (suc zero)) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) lo (csIF1 pt tp)))
          (_ , CS.apiCSev (suc (suc zero)) lo recvCSIntersectFound) (pt , tp) ≡ just (decCSc-src (suc (suc zero)) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-if1 (suc (suc zero)) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) hi (csIF1 pt tp)))
          (_ , CS.apiCSev (suc (suc zero)) hi recvCSIntersectFound) (pt , tp) ≡ just (decCSc-src (suc (suc zero)) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-if1 (suc (suc (suc zero))) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) lo (csIF1 pt tp)))
          (_ , CS.apiCSev (suc (suc (suc zero))) lo recvCSIntersectFound) (pt , tp) ≡ just (decCSc-src (suc (suc (suc zero))) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl
csc-fire-if1 (suc (suc (suc zero))) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) hi (csIF1 pt tp)))
          (_ , CS.apiCSev (suc (suc (suc zero))) hi recvCSIntersectFound) (pt , tp) ≡ just (decCSc-src (suc (suc (suc zero))) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = (Point × Tip)} (pt , tp) = refl

csc-fire-inf1 : (l : Link) (d : Dir) (tp : Tip)
  → decCSc-src l d (csINF1 tp)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d recvCSIntersectNotFound) tp)) ]─►
    decCSc-src l d (csSil CS.stIdle)
csc-fire-inf1 (zero) lo tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) lo (csINF1 tp)))
          (_ , CS.apiCSev (zero) lo recvCSIntersectNotFound) tp ≡ just (decCSc-src (zero) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Tip} tp = refl
csc-fire-inf1 (zero) hi tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (zero) hi (csINF1 tp)))
          (_ , CS.apiCSev (zero) hi recvCSIntersectNotFound) tp ≡ just (decCSc-src (zero) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Tip} tp = refl
csc-fire-inf1 (suc zero) lo tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) lo (csINF1 tp)))
          (_ , CS.apiCSev (suc zero) lo recvCSIntersectNotFound) tp ≡ just (decCSc-src (suc zero) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Tip} tp = refl
csc-fire-inf1 (suc zero) hi tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc zero) hi (csINF1 tp)))
          (_ , CS.apiCSev (suc zero) hi recvCSIntersectNotFound) tp ≡ just (decCSc-src (suc zero) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Tip} tp = refl
csc-fire-inf1 (suc (suc zero)) lo tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) lo (csINF1 tp)))
          (_ , CS.apiCSev (suc (suc zero)) lo recvCSIntersectNotFound) tp ≡ just (decCSc-src (suc (suc zero)) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Tip} tp = refl
csc-fire-inf1 (suc (suc zero)) hi tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc zero)) hi (csINF1 tp)))
          (_ , CS.apiCSev (suc (suc zero)) hi recvCSIntersectNotFound) tp ≡ just (decCSc-src (suc (suc zero)) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Tip} tp = refl
csc-fire-inf1 (suc (suc (suc zero))) lo tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) lo (csINF1 tp)))
          (_ , CS.apiCSev (suc (suc (suc zero))) lo recvCSIntersectNotFound) tp ≡ just (decCSc-src (suc (suc (suc zero))) lo (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Tip} tp = refl
csc-fire-inf1 (suc (suc (suc zero))) hi tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSc-src (suc (suc (suc zero))) hi (csINF1 tp)))
          (_ , CS.apiCSev (suc (suc (suc zero))) hi recvCSIntersectNotFound) tp ≡ just (decCSc-src (suc (suc (suc zero))) hi (csSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Tip} tp = refl
-- MID-BUILDERS-END


-- CSC-LEAF-BEGIN
------------------------------------------------------------------------
-- STEP 2 (CS-CLIENT backward production leaf `decCSc-ev-prod-abs`).
-- `Tcsc` = the abstract CS-client table (the `absCSc` table); `mkMcsc`
-- closes `M ≡ absCSc l d pos′` from the `tableSpec-ev-inv` `Meq` and the
-- coarse-position equality `q′ ≡ coarsenCSc pos′`.
------------------------------------------------------------------------

-- the abstract CS-client `nxt`-table (identical to the record inside `absCSc`)
Tcsc : Link → Dir → NS.Table NS.CScPos
Tcsc l d = record { isFin = NS.csCfin ; nxt = NS.csCnxt l d }

-- close `M ≡ absCSc l d pos′` (rewrite the coarse successor to `coarsenCSc pos′`)
mkMcsc : (l : Link) (d : Dir) (pos′ : CScPos) {q′ : NS.CScPos} {M : NetProc}
  → M ≡ tableSpec (Tcsc l d) q′ → q′ ≡ coarsenCSc pos′ → M ≡ absCSc l d pos′
mkMcsc l d pos′ Meq qeq = trans Meq (cong (tableSpec (Tcsc l d)) qeq)

------------------------------------------------------------------------
-- `csc-hstep` — the STRONG concrete fire from a head state, shared by the
-- leaf's `csHead st` (0-τ) and `csSil st` (1-τ) clauses.  Enumerates the
-- firing source event `e₁`; every non-firing `e₁` is refuted via the
-- inverted coarse edge (`csCnxt … ≡ nothing`, `nothing-absurd`).
------------------------------------------------------------------------
csc-hstep : (l : Link) (d : Dir) (st : CS.CSState)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → absCSc l d (csHead st) ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → Σ[ pos′ ∈ CScPos ] (decCSc l d (csHead st) ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► decCSc l d pos′)
      × (M ≡ absCSc l d pos′)

-- stIdle (ccIdle): fires apiCSev sendCSRequestNext / FindIntersect / Done
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' sendCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csReqNext1 , RFCS.renameMap-ev-fwd (csc-fire-reqNext l d) , mkMcsc l d (csReqNext1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' sendCSFindIntersect} {a = ps} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csFindInt1 ps , RFCS.renameMap-ev-fwd (csc-fire-findInt l d ps) , mkMcsc l d (csFindInt1 ps) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' sendCSDone} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csDone1 , RFCS.renameMap-ev-fwd (csc-fire-sendDone l d) , mkMcsc l d (csDone1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' sendCSAwaitReply} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' sendCSRollForward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' sendCSRollBackward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' sendCSIntersectFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' recvCSRollforward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' recvCSRollback} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' recvCSIntersectFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' reqCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' reqCSFindIntersect} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIdle {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stCanAwait (ccAwait): fires receiveCS (output) payloads
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRF1 h t , RFCS.renameMap-ev-fwd (csc-fire-rf-CA l d h t t0 md ln) , mkMcsc l d (csRF1 h t) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRB1 pt tp , RFCS.renameMap-ev-fwd (csc-fire-rb-CA l d pt tp t0 md ln) , mkMcsc l d (csRB1 pt tp) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSAwaitReply} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csSil CS.stMustReply , RFCS.renameMap-ev-fwd (csc-fire-aw-CA l d t0 md ln) , mkMcsc l d (csSil CS.stMustReply) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stCanAwait {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stMustReply (ccMust): fires receiveCS (output) payloads
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollForward h t)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRF1 h t , RFCS.renameMap-ev-fwd (csc-fire-rf-MR l d h t t0 md ln) , mkMcsc l d (csRF1 h t) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSRollBackward pt tp)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csRB1 pt tp , RFCS.renameMap-ev-fwd (csc-fire-rb-MR l d pt tp t0 md ln) , mkMcsc l d (csRB1 pt tp) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound _ _)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound _)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stMustReply {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stIntersect (ccInt): fires receiveCS (output) payloads
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectFound pt tp)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csIF1 pt tp , RFCS.renameMap-ev-fwd (csc-fire-if l d pt tp t0 md ln) , mkMcsc l d (csIF1 pt tp) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSIntersectNotFound tp)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = csINF1 tp , RFCS.renameMap-ev-fwd (csc-fire-inf l d tp t0 md ln) , mkMcsc l d (csINF1 tp) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward _ _)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward _ _)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSFindIntersect _)} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSDone} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch _} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
csc-hstep l d CS.stIntersect {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stDone (ccTerm): terminal — no visible offer; every event refuted
csc-hstep l d CS.stDone step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csHead CS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- CSC-HSTEP-END


-- CSC-LEAF-BODY-BEGIN
------------------------------------------------------------------------
-- `decCSc-ev-prod-abs` — the CS-CLIENT backward production leaf: an
-- abstract visible fire of `absCSc l d pos` is matched by a WEAK concrete
-- run of `decCSc l d pos` (head/mid: 0-τ; `csSil`: 1-τ loop-reentry
-- prefix), landing on the same abstract position.  Firing mids gate
-- link/dir then the value via nested `with` (outer l/d fall-throughs as
-- full clauses), mirroring the committed `csCnxt-io-role` inversion tree.
------------------------------------------------------------------------
decCSc-ev-prod-abs : (l : Link) (d : Dir) (pos : CScPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → absCSc l d pos ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → Σ[ pos′ ∈ CScPos ] (decCSc l d pos ═[ ev (evl (evLabel X (ιCS e₁) a)) ]═► decCSc l d pos′)
      × (M ≡ absCSc l d pos′)

-- head state: strong fire (0 τ), delegated to `csc-hstep`
decCSc-ev-prod-abs l d (csHead st) step with csc-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
-- loop-reentry sil: 1 τ (`decCSc-sil-step`) then the head fire
decCSc-ev-prod-abs l d (csSil st) step with csc-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decCSc-sil-step l d st) τ*-refl) f τ*-refl , m

-- csReqNext1: fires CS.sendCS l' d'
decCSc-ev-prod-abs l d (csReqNext1) {e₁ = CS.sendCS l' d'} {a} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csReqNext1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSRequestNext)
...     | yes refl = csSil CS.stCanAwait , wev τ*-refl (RFCS.renameMap-ev-fwd (csc-fire-reqNext1 l d)) τ*-refl , mkMcsc l d (csSil CS.stCanAwait) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csReqNext1) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csReqNext1) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csReqNext1) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csReqNext1) {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csReqNext1) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- csFindInt1 ps: fires CS.sendCS l' d'
decCSc-ev-prod-abs l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} {a} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csFindInt1 ps)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync (MsgCSFindIntersect ps))
...     | yes refl = csSil CS.stIntersect , wev τ*-refl (RFCS.renameMap-ev-fwd (csc-fire-findInt1 l d ps)) τ*-refl , mkMcsc l d (csSil CS.stIntersect) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csFindInt1 ps) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csFindInt1 ps) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csFindInt1 ps) {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csFindInt1 ps) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- csDone1: fires CS.sendCS l' d'
decCSc-ev-prod-abs l d (csDone1) {e₁ = CS.sendCS l' d'} {a} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csDone1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , chainSync MsgCSDone)
...     | yes refl = csSil CS.stDone , wev τ*-refl (RFCS.renameMap-ev-fwd (csc-fire-done1 l d)) τ*-refl , mkMcsc l d (csSil CS.stDone) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csDone1) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csDone1) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csDone1) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csDone1) {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csDone1) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- csRF1 h t: fires CS.apiCSev l' d' recvCSRollforward
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' recvCSRollforward} {a} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (h , t)
...     | yes refl = csSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (csc-fire-rf1 l d h t)) τ*-refl , mkMcsc l d (csSil CS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' recvCSRollforward} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' recvCSRollforward} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' sendCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' sendCSDone} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' sendCSRollForward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' sendCSRollBackward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' recvCSRollback} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' recvCSIntersectFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' reqCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.apiCSev l' d' reqCSFindIntersect} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRF1 h t) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- csRB1 pt tp: fires CS.apiCSev l' d' recvCSRollback
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' recvCSRollback} {a} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (pt , tp)
...     | yes refl = csSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (csc-fire-rb1 l d pt tp)) τ*-refl , mkMcsc l d (csSil CS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' recvCSRollback} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' recvCSRollback} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' sendCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' sendCSDone} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' sendCSRollForward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' sendCSRollBackward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' recvCSRollforward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' recvCSIntersectFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' reqCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.apiCSev l' d' reqCSFindIntersect} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csRB1 pt tp) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- csIF1 pt tp: fires CS.apiCSev l' d' recvCSIntersectFound
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' recvCSIntersectFound} {a} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (pt , tp)
...     | yes refl = csSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (csc-fire-if1 l d pt tp)) τ*-refl , mkMcsc l d (csSil CS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' recvCSIntersectFound} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' recvCSIntersectFound} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' sendCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' sendCSDone} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' sendCSRollForward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' sendCSRollBackward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' recvCSRollforward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' recvCSRollback} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' reqCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.apiCSev l' d' reqCSFindIntersect} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csIF1 pt tp) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- csINF1 tp: fires CS.apiCSev l' d' recvCSIntersectNotFound
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} {a} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (tp)
...     | yes refl = csSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (csc-fire-inf1 l d tp)) τ*-refl , mkMcsc l d (csSil CS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' sendCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' sendCSDone} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' sendCSRollForward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' sendCSRollBackward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' recvCSRollforward} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' recvCSRollback} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' recvCSIntersectFound} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' reqCSRequestNext} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.apiCSev l' d' reqCSFindIntersect} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSc-ev-prod-abs l d (csINF1 tp) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcsc l d) (coarsenCSc (csINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- CSC-LEAF-BODY-END




-- CSS-FIRE-BEGIN
------------------------------------------------------------------------
-- STEP 2 (CS-SERVER concrete offer builders).  Role-swapped mirror of
-- the CS-client `csc-fire-*`: `ssHead stIdle` RECEIVES on the wire
-- (receiveCS), the other heads SEND via api; the 8 mids emit the
-- api-notify / wire-send / done leaves (FromResponder payloads).
------------------------------------------------------------------------

-- the abstract CS-server `nxt`-table (identical to the record inside `absCSs`)
Tcss : Link → Dir → NS.Table NS.CSsPos
Tcss l d = record { isFin = NS.csSfin ; nxt = NS.csSnxt l d }

-- close `M ≡ absCSs l d pos′` (rewrite the coarse successor to `coarsenCSs pos′`)
mkMcss : (l : Link) (d : Dir) (pos′ : CSsPos) {q′ : NS.CSsPos} {M : NetProc}
  → M ≡ tableSpec (Tcss l d) q′ → q′ ≡ coarsenCSs pos′ → M ≡ absCSs l d pos′
mkMcss l d pos′ Meq qeq = trans Meq (cong (tableSpec (Tcss l d)) qeq)

css-fire-reqNext : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decCSs-src l d (ssHead CS.stIdle)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.receiveCS l d) (t0 , md , ln , chainSync MsgCSRequestNext))) ]─►
    decCSs-src l d (ssReqNext1)
css-fire-reqNext l d t0 md ln = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src l d (ssHead CS.stIdle)))
          (_ , CS.receiveCS l d) (t0 , md , ln , chainSync MsgCSRequestNext) ≡ just (decCSs-src l d (ssReqNext1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

css-fire-findInt : (l : Link) (d : Dir) (ps : _) (t0 : _) (md : _) (ln : _)
  → decCSs-src l d (ssHead CS.stIdle)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.receiveCS l d) (t0 , md , ln , chainSync (MsgCSFindIntersect ps)))) ]─►
    decCSs-src l d (ssFindInt1 ps)
css-fire-findInt l d ps t0 md ln = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src l d (ssHead CS.stIdle)))
          (_ , CS.receiveCS l d) (t0 , md , ln , chainSync (MsgCSFindIntersect ps)) ≡ just (decCSs-src l d (ssFindInt1 ps))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

css-fire-done : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decCSs-src l d (ssHead CS.stIdle)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.receiveCS l d) (t0 , md , ln , chainSync MsgCSDone))) ]─►
    decCSs-src l d (ssDone1)
css-fire-done l d t0 md ln = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src l d (ssHead CS.stIdle)))
          (_ , CS.receiveCS l d) (t0 , md , ln , chainSync MsgCSDone) ≡ just (decCSs-src l d (ssDone1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

css-fire-rf-CA : (l : Link) (d : Dir) (h : Header) (t : Tip)
  → decCSs-src l d (ssHead CS.stCanAwait)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d sendCSRollForward) (h , t))) ]─►
    decCSs-src l d (ssRF1 h t)
css-fire-rf-CA l d h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src l d (ssHead CS.stCanAwait)))
          (_ , CS.apiCSev l d sendCSRollForward) (h , t) ≡ just (decCSs-src l d (ssRF1 h t))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

css-fire-rb-CA : (l : Link) (d : Dir) (pt : Point) (tp : Tip)
  → decCSs-src l d (ssHead CS.stCanAwait)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d sendCSRollBackward) (pt , tp))) ]─►
    decCSs-src l d (ssRB1 pt tp)
css-fire-rb-CA l d pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src l d (ssHead CS.stCanAwait)))
          (_ , CS.apiCSev l d sendCSRollBackward) (pt , tp) ≡ just (decCSs-src l d (ssRB1 pt tp))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

css-fire-aw-CA : (l : Link) (d : Dir)
  → decCSs-src l d (ssHead CS.stCanAwait)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d sendCSAwaitReply) U.tt)) ]─►
    decCSs-src l d (ssAw1)
css-fire-aw-CA l d  = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src l d (ssHead CS.stCanAwait)))
          (_ , CS.apiCSev l d sendCSAwaitReply) U.tt ≡ just (decCSs-src l d (ssAw1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

css-fire-rf-MR : (l : Link) (d : Dir) (h : Header) (t : Tip)
  → decCSs-src l d (ssHead CS.stMustReply)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d sendCSRollForward) (h , t))) ]─►
    decCSs-src l d (ssRF1 h t)
css-fire-rf-MR l d h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src l d (ssHead CS.stMustReply)))
          (_ , CS.apiCSev l d sendCSRollForward) (h , t) ≡ just (decCSs-src l d (ssRF1 h t))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

css-fire-rb-MR : (l : Link) (d : Dir) (pt : Point) (tp : Tip)
  → decCSs-src l d (ssHead CS.stMustReply)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d sendCSRollBackward) (pt , tp))) ]─►
    decCSs-src l d (ssRB1 pt tp)
css-fire-rb-MR l d pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src l d (ssHead CS.stMustReply)))
          (_ , CS.apiCSev l d sendCSRollBackward) (pt , tp) ≡ just (decCSs-src l d (ssRB1 pt tp))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

css-fire-if : (l : Link) (d : Dir) (pt : Point) (tp : Tip)
  → decCSs-src l d (ssHead CS.stIntersect)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d sendCSIntersectFound) (pt , tp))) ]─►
    decCSs-src l d (ssIF1 pt tp)
css-fire-if l d pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src l d (ssHead CS.stIntersect)))
          (_ , CS.apiCSev l d sendCSIntersectFound) (pt , tp) ≡ just (decCSs-src l d (ssIF1 pt tp))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

css-fire-inf : (l : Link) (d : Dir) (tp : Tip)
  → decCSs-src l d (ssHead CS.stIntersect)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d sendCSIntersectNotFound) tp)) ]─►
    decCSs-src l d (ssINF1 tp)
css-fire-inf l d tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src l d (ssHead CS.stIntersect)))
          (_ , CS.apiCSev l d sendCSIntersectNotFound) tp ≡ just (decCSs-src l d (ssINF1 tp))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

css-fire-reqNext1 : (l : Link) (d : Dir)
  → decCSs-src l d (ssReqNext1)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d reqCSRequestNext) U.tt)) ]─►
    decCSs-src l d (ssSil CS.stCanAwait)
css-fire-reqNext1 (zero) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) lo (ssReqNext1)))
          (_ , CS.apiCSev (zero) lo reqCSRequestNext) U.tt ≡ just (decCSs-src (zero) lo (ssSil CS.stCanAwait))
    o = refl
css-fire-reqNext1 (zero) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) hi (ssReqNext1)))
          (_ , CS.apiCSev (zero) hi reqCSRequestNext) U.tt ≡ just (decCSs-src (zero) hi (ssSil CS.stCanAwait))
    o = refl
css-fire-reqNext1 (suc zero) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) lo (ssReqNext1)))
          (_ , CS.apiCSev (suc zero) lo reqCSRequestNext) U.tt ≡ just (decCSs-src (suc zero) lo (ssSil CS.stCanAwait))
    o = refl
css-fire-reqNext1 (suc zero) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) hi (ssReqNext1)))
          (_ , CS.apiCSev (suc zero) hi reqCSRequestNext) U.tt ≡ just (decCSs-src (suc zero) hi (ssSil CS.stCanAwait))
    o = refl
css-fire-reqNext1 (suc (suc zero)) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) lo (ssReqNext1)))
          (_ , CS.apiCSev (suc (suc zero)) lo reqCSRequestNext) U.tt ≡ just (decCSs-src (suc (suc zero)) lo (ssSil CS.stCanAwait))
    o = refl
css-fire-reqNext1 (suc (suc zero)) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) hi (ssReqNext1)))
          (_ , CS.apiCSev (suc (suc zero)) hi reqCSRequestNext) U.tt ≡ just (decCSs-src (suc (suc zero)) hi (ssSil CS.stCanAwait))
    o = refl
css-fire-reqNext1 (suc (suc (suc zero))) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) lo (ssReqNext1)))
          (_ , CS.apiCSev (suc (suc (suc zero))) lo reqCSRequestNext) U.tt ≡ just (decCSs-src (suc (suc (suc zero))) lo (ssSil CS.stCanAwait))
    o = refl
css-fire-reqNext1 (suc (suc (suc zero))) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) hi (ssReqNext1)))
          (_ , CS.apiCSev (suc (suc (suc zero))) hi reqCSRequestNext) U.tt ≡ just (decCSs-src (suc (suc (suc zero))) hi (ssSil CS.stCanAwait))
    o = refl

css-fire-findInt1 : (l : Link) (d : Dir) (ps : _)
  → decCSs-src l d (ssFindInt1 ps)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.apiCSev l d reqCSFindIntersect) ps)) ]─►
    decCSs-src l d (ssSil CS.stIntersect)
css-fire-findInt1 (zero) lo ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) lo (ssFindInt1 ps)))
          (_ , CS.apiCSev (zero) lo reqCSFindIntersect) ps ≡ just (decCSs-src (zero) lo (ssSil CS.stIntersect))
    o rewrite ≟-yes-refl ⦃ CS.DecEq-ListPoint ⦄ ps = refl
css-fire-findInt1 (zero) hi ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) hi (ssFindInt1 ps)))
          (_ , CS.apiCSev (zero) hi reqCSFindIntersect) ps ≡ just (decCSs-src (zero) hi (ssSil CS.stIntersect))
    o rewrite ≟-yes-refl ⦃ CS.DecEq-ListPoint ⦄ ps = refl
css-fire-findInt1 (suc zero) lo ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) lo (ssFindInt1 ps)))
          (_ , CS.apiCSev (suc zero) lo reqCSFindIntersect) ps ≡ just (decCSs-src (suc zero) lo (ssSil CS.stIntersect))
    o rewrite ≟-yes-refl ⦃ CS.DecEq-ListPoint ⦄ ps = refl
css-fire-findInt1 (suc zero) hi ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) hi (ssFindInt1 ps)))
          (_ , CS.apiCSev (suc zero) hi reqCSFindIntersect) ps ≡ just (decCSs-src (suc zero) hi (ssSil CS.stIntersect))
    o rewrite ≟-yes-refl ⦃ CS.DecEq-ListPoint ⦄ ps = refl
css-fire-findInt1 (suc (suc zero)) lo ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) lo (ssFindInt1 ps)))
          (_ , CS.apiCSev (suc (suc zero)) lo reqCSFindIntersect) ps ≡ just (decCSs-src (suc (suc zero)) lo (ssSil CS.stIntersect))
    o rewrite ≟-yes-refl ⦃ CS.DecEq-ListPoint ⦄ ps = refl
css-fire-findInt1 (suc (suc zero)) hi ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) hi (ssFindInt1 ps)))
          (_ , CS.apiCSev (suc (suc zero)) hi reqCSFindIntersect) ps ≡ just (decCSs-src (suc (suc zero)) hi (ssSil CS.stIntersect))
    o rewrite ≟-yes-refl ⦃ CS.DecEq-ListPoint ⦄ ps = refl
css-fire-findInt1 (suc (suc (suc zero))) lo ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) lo (ssFindInt1 ps)))
          (_ , CS.apiCSev (suc (suc (suc zero))) lo reqCSFindIntersect) ps ≡ just (decCSs-src (suc (suc (suc zero))) lo (ssSil CS.stIntersect))
    o rewrite ≟-yes-refl ⦃ CS.DecEq-ListPoint ⦄ ps = refl
css-fire-findInt1 (suc (suc (suc zero))) hi ps = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) hi (ssFindInt1 ps)))
          (_ , CS.apiCSev (suc (suc (suc zero))) hi reqCSFindIntersect) ps ≡ just (decCSs-src (suc (suc (suc zero))) hi (ssSil CS.stIntersect))
    o rewrite ≟-yes-refl ⦃ CS.DecEq-ListPoint ⦄ ps = refl

css-fire-done1 : (l : Link) (d : Dir)
  → decCSs-src l d (ssDone1)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.doneCS l d) U.tt)) ]─►
    decCSs-src l d (ssSil CS.stDone)
css-fire-done1 (zero) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) lo (ssDone1)))
          (_ , CS.doneCS (zero) lo) U.tt ≡ just (decCSs-src (zero) lo (ssSil CS.stDone))
    o = refl
css-fire-done1 (zero) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) hi (ssDone1)))
          (_ , CS.doneCS (zero) hi) U.tt ≡ just (decCSs-src (zero) hi (ssSil CS.stDone))
    o = refl
css-fire-done1 (suc zero) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) lo (ssDone1)))
          (_ , CS.doneCS (suc zero) lo) U.tt ≡ just (decCSs-src (suc zero) lo (ssSil CS.stDone))
    o = refl
css-fire-done1 (suc zero) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) hi (ssDone1)))
          (_ , CS.doneCS (suc zero) hi) U.tt ≡ just (decCSs-src (suc zero) hi (ssSil CS.stDone))
    o = refl
css-fire-done1 (suc (suc zero)) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) lo (ssDone1)))
          (_ , CS.doneCS (suc (suc zero)) lo) U.tt ≡ just (decCSs-src (suc (suc zero)) lo (ssSil CS.stDone))
    o = refl
css-fire-done1 (suc (suc zero)) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) hi (ssDone1)))
          (_ , CS.doneCS (suc (suc zero)) hi) U.tt ≡ just (decCSs-src (suc (suc zero)) hi (ssSil CS.stDone))
    o = refl
css-fire-done1 (suc (suc (suc zero))) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) lo (ssDone1)))
          (_ , CS.doneCS (suc (suc (suc zero))) lo) U.tt ≡ just (decCSs-src (suc (suc (suc zero))) lo (ssSil CS.stDone))
    o = refl
css-fire-done1 (suc (suc (suc zero))) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) hi (ssDone1)))
          (_ , CS.doneCS (suc (suc (suc zero))) hi) U.tt ≡ just (decCSs-src (suc (suc (suc zero))) hi (ssSil CS.stDone))
    o = refl

css-fire-rf1 : (l : Link) (d : Dir) (h : Header) (t : Tip)
  → decCSs-src l d (ssRF1 h t)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.sendCS l d) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)))) ]─►
    decCSs-src l d (ssSil CS.stIdle)
css-fire-rf1 (zero) lo h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) lo (ssRF1 h t)))
          (_ , CS.sendCS (zero) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just (decCSs-src (zero) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) = refl
css-fire-rf1 (zero) hi h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) hi (ssRF1 h t)))
          (_ , CS.sendCS (zero) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just (decCSs-src (zero) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) = refl
css-fire-rf1 (suc zero) lo h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) lo (ssRF1 h t)))
          (_ , CS.sendCS (suc zero) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just (decCSs-src (suc zero) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) = refl
css-fire-rf1 (suc zero) hi h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) hi (ssRF1 h t)))
          (_ , CS.sendCS (suc zero) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just (decCSs-src (suc zero) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) = refl
css-fire-rf1 (suc (suc zero)) lo h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) lo (ssRF1 h t)))
          (_ , CS.sendCS (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just (decCSs-src (suc (suc zero)) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) = refl
css-fire-rf1 (suc (suc zero)) hi h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) hi (ssRF1 h t)))
          (_ , CS.sendCS (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just (decCSs-src (suc (suc zero)) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) = refl
css-fire-rf1 (suc (suc (suc zero))) lo h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) lo (ssRF1 h t)))
          (_ , CS.sendCS (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just (decCSs-src (suc (suc (suc zero))) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) = refl
css-fire-rf1 (suc (suc (suc zero))) hi h t = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) hi (ssRF1 h t)))
          (_ , CS.sendCS (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) ≡ just (decCSs-src (suc (suc (suc zero))) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t)) = refl

css-fire-rb1 : (l : Link) (d : Dir) (pt : Point) (tp : Tip)
  → decCSs-src l d (ssRB1 pt tp)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.sendCS l d) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)))) ]─►
    decCSs-src l d (ssSil CS.stIdle)
css-fire-rb1 (zero) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) lo (ssRB1 pt tp)))
          (_ , CS.sendCS (zero) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ≡ just (decCSs-src (zero) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) = refl
css-fire-rb1 (zero) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) hi (ssRB1 pt tp)))
          (_ , CS.sendCS (zero) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ≡ just (decCSs-src (zero) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) = refl
css-fire-rb1 (suc zero) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) lo (ssRB1 pt tp)))
          (_ , CS.sendCS (suc zero) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ≡ just (decCSs-src (suc zero) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) = refl
css-fire-rb1 (suc zero) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) hi (ssRB1 pt tp)))
          (_ , CS.sendCS (suc zero) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ≡ just (decCSs-src (suc zero) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) = refl
css-fire-rb1 (suc (suc zero)) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) lo (ssRB1 pt tp)))
          (_ , CS.sendCS (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ≡ just (decCSs-src (suc (suc zero)) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) = refl
css-fire-rb1 (suc (suc zero)) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) hi (ssRB1 pt tp)))
          (_ , CS.sendCS (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ≡ just (decCSs-src (suc (suc zero)) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) = refl
css-fire-rb1 (suc (suc (suc zero))) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) lo (ssRB1 pt tp)))
          (_ , CS.sendCS (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ≡ just (decCSs-src (suc (suc (suc zero))) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) = refl
css-fire-rb1 (suc (suc (suc zero))) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) hi (ssRB1 pt tp)))
          (_ , CS.sendCS (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) ≡ just (decCSs-src (suc (suc (suc zero))) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp)) = refl

css-fire-aw1 : (l : Link) (d : Dir)
  → decCSs-src l d (ssAw1)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.sendCS l d) (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply))) ]─►
    decCSs-src l d (ssSil CS.stMustReply)
css-fire-aw1 (zero) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) lo (ssAw1)))
          (_ , CS.sendCS (zero) lo) (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) ≡ just (decCSs-src (zero) lo (ssSil CS.stMustReply))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) = refl
css-fire-aw1 (zero) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) hi (ssAw1)))
          (_ , CS.sendCS (zero) hi) (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) ≡ just (decCSs-src (zero) hi (ssSil CS.stMustReply))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) = refl
css-fire-aw1 (suc zero) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) lo (ssAw1)))
          (_ , CS.sendCS (suc zero) lo) (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) ≡ just (decCSs-src (suc zero) lo (ssSil CS.stMustReply))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) = refl
css-fire-aw1 (suc zero) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) hi (ssAw1)))
          (_ , CS.sendCS (suc zero) hi) (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) ≡ just (decCSs-src (suc zero) hi (ssSil CS.stMustReply))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) = refl
css-fire-aw1 (suc (suc zero)) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) lo (ssAw1)))
          (_ , CS.sendCS (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) ≡ just (decCSs-src (suc (suc zero)) lo (ssSil CS.stMustReply))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) = refl
css-fire-aw1 (suc (suc zero)) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) hi (ssAw1)))
          (_ , CS.sendCS (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) ≡ just (decCSs-src (suc (suc zero)) hi (ssSil CS.stMustReply))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) = refl
css-fire-aw1 (suc (suc (suc zero))) lo = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) lo (ssAw1)))
          (_ , CS.sendCS (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) ≡ just (decCSs-src (suc (suc (suc zero))) lo (ssSil CS.stMustReply))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) = refl
css-fire-aw1 (suc (suc (suc zero))) hi = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) hi (ssAw1)))
          (_ , CS.sendCS (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) ≡ just (decCSs-src (suc (suc (suc zero))) hi (ssSil CS.stMustReply))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply) = refl

css-fire-if1 : (l : Link) (d : Dir) (pt : Point) (tp : Tip)
  → decCSs-src l d (ssIF1 pt tp)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.sendCS l d) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)))) ]─►
    decCSs-src l d (ssSil CS.stIdle)
css-fire-if1 (zero) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) lo (ssIF1 pt tp)))
          (_ , CS.sendCS (zero) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) ≡ just (decCSs-src (zero) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) = refl
css-fire-if1 (zero) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) hi (ssIF1 pt tp)))
          (_ , CS.sendCS (zero) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) ≡ just (decCSs-src (zero) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) = refl
css-fire-if1 (suc zero) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) lo (ssIF1 pt tp)))
          (_ , CS.sendCS (suc zero) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) ≡ just (decCSs-src (suc zero) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) = refl
css-fire-if1 (suc zero) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) hi (ssIF1 pt tp)))
          (_ , CS.sendCS (suc zero) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) ≡ just (decCSs-src (suc zero) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) = refl
css-fire-if1 (suc (suc zero)) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) lo (ssIF1 pt tp)))
          (_ , CS.sendCS (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) ≡ just (decCSs-src (suc (suc zero)) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) = refl
css-fire-if1 (suc (suc zero)) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) hi (ssIF1 pt tp)))
          (_ , CS.sendCS (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) ≡ just (decCSs-src (suc (suc zero)) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) = refl
css-fire-if1 (suc (suc (suc zero))) lo pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) lo (ssIF1 pt tp)))
          (_ , CS.sendCS (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) ≡ just (decCSs-src (suc (suc (suc zero))) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) = refl
css-fire-if1 (suc (suc (suc zero))) hi pt tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) hi (ssIF1 pt tp)))
          (_ , CS.sendCS (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) ≡ just (decCSs-src (suc (suc (suc zero))) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp)) = refl

css-fire-inf1 : (l : Link) (d : Dir) (tp : Tip)
  → decCSs-src l d (ssINF1 tp)
      CSL.─[ CSL.ev (CSL.evl (CSL.evLabel _ (CS.sendCS l d) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)))) ]─►
    decCSs-src l d (ssSil CS.stIdle)
css-fire-inf1 (zero) lo tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) lo (ssINF1 tp)))
          (_ , CS.sendCS (zero) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) ≡ just (decCSs-src (zero) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) = refl
css-fire-inf1 (zero) hi tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (zero) hi (ssINF1 tp)))
          (_ , CS.sendCS (zero) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) ≡ just (decCSs-src (zero) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) = refl
css-fire-inf1 (suc zero) lo tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) lo (ssINF1 tp)))
          (_ , CS.sendCS (suc zero) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) ≡ just (decCSs-src (suc zero) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) = refl
css-fire-inf1 (suc zero) hi tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc zero) hi (ssINF1 tp)))
          (_ , CS.sendCS (suc zero) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) ≡ just (decCSs-src (suc zero) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) = refl
css-fire-inf1 (suc (suc zero)) lo tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) lo (ssINF1 tp)))
          (_ , CS.sendCS (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) ≡ just (decCSs-src (suc (suc zero)) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) = refl
css-fire-inf1 (suc (suc zero)) hi tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc zero)) hi (ssINF1 tp)))
          (_ , CS.sendCS (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) ≡ just (decCSs-src (suc (suc zero)) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) = refl
css-fire-inf1 (suc (suc (suc zero))) lo tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) lo (ssINF1 tp)))
          (_ , CS.sendCS (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) ≡ just (decCSs-src (suc (suc (suc zero))) lo (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) = refl
css-fire-inf1 (suc (suc (suc zero))) hi tp = CSL.sVis refl o
  where
    o : vis-ofC (PTree.force (decCSs-src (suc (suc (suc zero))) hi (ssINF1 tp)))
          (_ , CS.sendCS (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) ≡ just (decCSs-src (suc (suc (suc zero))) hi (ssSil CS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp)) = refl

-- CSS-FIRE-END


-- CSS-HSTEP-BEGIN
------------------------------------------------------------------------
-- `css-hstep` — CS-SERVER head-state STRONG-fire helper (role-swapped
-- mirror of `csc-hstep`): `ssHead stIdle` RECEIVES on the wire; the
-- other heads SEND via api (so they enumerate all 14 `ApiCSTag`).
------------------------------------------------------------------------
css-hstep : (l : Link) (d : Dir) (st : CS.CSState)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → absCSs l d (ssHead st) ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → Σ[ pos′ ∈ CSsPos ] (decCSs l d (ssHead st) ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► decCSs l d pos′)
      × (M ≡ absCSs l d pos′)

-- stIdle (csIdle): receives RequestNext / FindIntersect / Done on the wire
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSRequestNext} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssReqNext1 , RFCS.renameMap-ev-fwd (css-fire-reqNext l d t0 md ln) , mkMcss l d (ssReqNext1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync (MsgCSFindIntersect ps)} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssFindInt1 ps , RFCS.renameMap-ev-fwd (css-fire-findInt l d ps t0 md ln) , mkMcss l d (ssFindInt1 ps) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = t0 , md , ln , chainSync MsgCSDone} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssDone1 , RFCS.renameMap-ev-fwd (css-fire-done l d t0 md ln) , mkMcss l d (ssDone1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync MsgCSAwaitReply} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollForward h t)} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSRollBackward pt tp)} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectFound pt tp)} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , chainSync (MsgCSIntersectNotFound tp)} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , keepAlive _} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , blockFetch _} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , txSubmission _} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosNotify _} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.receiveCS l' d'} {a = _ , _ , _ , leiosFetch _} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIdle {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stCanAwait (api send): enumerate all 14 ApiCSTag
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' sendCSRequestNext} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' sendCSFindIntersect} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' sendCSDone} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' sendCSAwaitReply} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssAw1 , RFCS.renameMap-ev-fwd (css-fire-aw-CA l d) , mkMcss l d (ssAw1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRF1 (proj₁ a) (proj₂ a) , RFCS.renameMap-ev-fwd (css-fire-rf-CA l d (proj₁ a) (proj₂ a)) , mkMcss l d (ssRF1 (proj₁ a) (proj₂ a)) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRB1 (proj₁ a) (proj₂ a) , RFCS.renameMap-ev-fwd (css-fire-rb-CA l d (proj₁ a) (proj₂ a)) , mkMcss l d (ssRB1 (proj₁ a) (proj₂ a)) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' sendCSIntersectFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' recvCSRollforward} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' recvCSRollback} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' recvCSIntersectFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' reqCSRequestNext} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.apiCSev l' d' reqCSFindIntersect} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stCanAwait {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stCanAwait)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stMustReply (api send): enumerate all 14 ApiCSTag
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' sendCSRequestNext} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' sendCSFindIntersect} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' sendCSDone} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' sendCSAwaitReply} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' sendCSRollForward} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRF1 (proj₁ a) (proj₂ a) , RFCS.renameMap-ev-fwd (css-fire-rf-MR l d (proj₁ a) (proj₂ a)) , mkMcss l d (ssRF1 (proj₁ a) (proj₂ a)) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' sendCSRollBackward} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssRB1 (proj₁ a) (proj₂ a) , RFCS.renameMap-ev-fwd (css-fire-rb-MR l d (proj₁ a) (proj₂ a)) , mkMcss l d (ssRB1 (proj₁ a) (proj₂ a)) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' sendCSIntersectFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' recvCSRollforward} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' recvCSRollback} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' recvCSIntersectFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' reqCSRequestNext} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.apiCSev l' d' reqCSFindIntersect} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stMustReply {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stMustReply)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stIntersect (api send): enumerate all 14 ApiCSTag
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' sendCSRequestNext} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' sendCSFindIntersect} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' sendCSDone} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' sendCSAwaitReply} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' sendCSRollForward} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' sendCSRollBackward} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' sendCSIntersectFound} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssIF1 (proj₁ a) (proj₂ a) , RFCS.renameMap-ev-fwd (css-fire-if l d (proj₁ a) (proj₂ a)) , mkMcss l d (ssIF1 (proj₁ a) (proj₂ a)) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssINF1 a , RFCS.renameMap-ev-fwd (css-fire-inf l d a) , mkMcss l d (ssINF1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' recvCSRollforward} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' recvCSRollback} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' recvCSIntersectFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' reqCSRequestNext} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.apiCSev l' d' reqCSFindIntersect} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
css-hstep l d CS.stIntersect {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stIntersect)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stDone (csTerm): terminal — no visible offer
css-hstep l d CS.stDone step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssHead CS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- CSS-HSTEP-END


-- CSS-LEAF-BODY-BEGIN
------------------------------------------------------------------------
-- `decCSs-ev-prod-abs` — the CS-SERVER backward production leaf (mirror
-- of `decCSc-ev-prod-abs`): head/sil delegate to `css-hstep` (0-τ / 1-τ);
-- the 8 mids inline-enumerate the firing event.  api-notify mids
-- (ssReqNext1/ssFindInt1) enumerate 14 tags; done/wire-send mids use
-- 1-clause refutes for the non-firing event ctors.
------------------------------------------------------------------------
decCSs-ev-prod-abs : (l : Link) (d : Dir) (pos : CSsPos)
    {X : Set 0ℓ} {e₁ : CS.CSEv X} {a : X} {M : NetProc}
  → absCSs l d pos ─[ ev (evl (evLabel X (ιCS e₁) a)) ]─► M
  → Σ[ pos′ ∈ CSsPos ] (decCSs l d pos ═[ ev (evl (evLabel X (ιCS e₁) a)) ]═► decCSs l d pos′)
      × (M ≡ absCSs l d pos′)

-- head state: strong fire (0 τ), delegated to `css-hstep`
decCSs-ev-prod-abs l d (ssHead st) step with css-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
-- loop-reentry sil: 1 τ (`decCSs-sil-step`) then the head fire
decCSs-ev-prod-abs l d (ssSil st) step with css-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decCSs-sil-step l d st) τ*-refl) f τ*-refl , m

-- ssReqNext1: fires apiCSev reqCSRequestNext (⊤)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' sendCSRequestNext} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' sendCSDone} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' sendCSRollForward} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' sendCSRollBackward} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' recvCSRollforward} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' recvCSRollback} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' recvCSIntersectFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' reqCSRequestNext} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssSil CS.stCanAwait , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-reqNext1 l d)) τ*-refl , mkMcss l d (ssSil CS.stCanAwait) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.apiCSev l' d' reqCSFindIntersect} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssReqNext1) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssReqNext1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssFindInt1 ps: fires apiCSev reqCSFindIntersect ps (List Point gate)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' sendCSRequestNext} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' sendCSFindIntersect} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' sendCSDone} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' sendCSAwaitReply} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' sendCSRollForward} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' sendCSRollBackward} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' sendCSIntersectFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' sendCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' recvCSRollforward} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' recvCSRollback} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' recvCSIntersectFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' recvCSIntersectNotFound} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' reqCSRequestNext} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' reqCSFindIntersect} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ CS.DecEq-ListPoint ⦄ a ps
...     | yes refl = ssSil CS.stIntersect , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-findInt1 l d ps)) τ*-refl , mkMcss l d (ssSil CS.stIntersect) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' reqCSFindIntersect} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.apiCSev l' d' reqCSFindIntersect} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssFindInt1 ps) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssFindInt1 ps)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssDone1: fires doneCS (⊤) → ssSil stDone
decCSs-ev-prod-abs l d ssDone1 {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssDone1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ssSil CS.stDone , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-done1 l d)) τ*-refl , mkMcss l d (ssSil CS.stDone) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d ssDone1 {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d ssDone1 {e₁ = CS.sendCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d ssDone1 {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssRF1 h t: fires sendCS (RollForward, FromResponder)
decCSs-ev-prod-abs l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRF1 h t)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollForward h t))
...     | yes refl = ssSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-rf1 l d h t)) τ*-refl , mkMcss l d (ssSil CS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssRF1 h t) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssRF1 h t) {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssRF1 h t) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssRF1 h t) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRF1 h t)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssRB1 pt tp: fires sendCS (RollBackward)
decCSs-ev-prod-abs l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRB1 pt tp)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSRollBackward pt tp))
...     | yes refl = ssSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-rb1 l d pt tp)) τ*-refl , mkMcss l d (ssSil CS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssRB1 pt tp) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssRB1 pt tp) {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssRB1 pt tp) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssRB1 pt tp) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssRB1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssAw1: fires sendCS (AwaitReply) → stMustReply
decCSs-ev-prod-abs l d (ssAw1) {e₁ = CS.sendCS l' d'} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssAw1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync MsgCSAwaitReply)
...     | yes refl = ssSil CS.stMustReply , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-aw1 l d)) τ*-refl , mkMcss l d (ssSil CS.stMustReply) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssAw1) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssAw1) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssAw1) {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssAw1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssAw1) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssAw1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssAw1) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssAw1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssIF1 pt tp: fires sendCS (IntersectFound)
decCSs-ev-prod-abs l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssIF1 pt tp)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectFound pt tp))
...     | yes refl = ssSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-if1 l d pt tp)) τ*-refl , mkMcss l d (ssSil CS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssIF1 pt tp) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssIF1 pt tp) {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssIF1 pt tp) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssIF1 pt tp) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssIF1 pt tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ssINF1 tp: fires sendCS (IntersectNotFound)
decCSs-ev-prod-abs l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} {a} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssINF1 tp)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , chainSync (MsgCSIntersectNotFound tp))
...     | yes refl = ssSil CS.stIdle , wev τ*-refl (RFCS.renameMap-ev-fwd (css-fire-inf1 l d tp)) τ*-refl , mkMcss l d (ssSil CS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssINF1 tp) {e₁ = CS.sendCS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssINF1 tp) {e₁ = CS.apiCSev l' d' m} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssINF1 tp) {e₁ = CS.receiveCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decCSs-ev-prod-abs l d (ssINF1 tp) {e₁ = CS.doneCS l' d'} step
  with tableSpec-ev-inv (Tcss l d) (coarsenCSs (ssINF1 tp)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- CSS-LEAF-BODY-END


-- BFC-FIRE-BEGIN
------------------------------------------------------------------------
-- STEP 2 (BF-CLIENT).  `bcHead stIdle` api-SENDS; stBusy/stStreaming
-- RECEIVE on the wire.  Concrete offer builders, hstep, leaf.
------------------------------------------------------------------------
Tbfc : Link → Dir → NS.Table NS.BFcPos
Tbfc l d = record { isFin = NS.bfCfin ; nxt = NS.bfCnxt l d }
mkMbfc : (l : Link) (d : Dir) (pos′ : BFcPos) {q′ : NS.BFcPos} {M : NetProc}
  → M ≡ tableSpec (Tbfc l d) q′ → q′ ≡ coarsenBFc pos′ → M ≡ absBFc l d pos′
mkMbfc l d pos′ Meq qeq = trans Meq (cong (tableSpec (Tbfc l d)) qeq)

bfc-fire-req : (l : Link) (d : Dir) (r : ChainRange)
  → decBFc-src l d (bcHead BF.stIdle)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.apiBFev l d sendBFRequestRange) r)) ]─►
    decBFc-src l d (bcReq1 r)
bfc-fire-req l d r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src l d (bcHead BF.stIdle)))
          (_ , BF.apiBFev l d sendBFRequestRange) r ≡ just (decBFc-src l d (bcReq1 r))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfc-fire-cdone : (l : Link) (d : Dir)
  → decBFc-src l d (bcHead BF.stIdle)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.apiBFev l d sendBFClientDone) U.tt)) ]─►
    decBFc-src l d (bcDone1)
bfc-fire-cdone l d  = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src l d (bcHead BF.stIdle)))
          (_ , BF.apiBFev l d sendBFClientDone) U.tt ≡ just (decBFc-src l d (bcDone1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfc-fire-start : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decBFc-src l d (bcHead BF.stBusy)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.receiveBF l d) (t0 , md , ln , blockFetch MsgStartBatch))) ]─►
    decBFc-src l d (bcSil BF.stStreaming)
bfc-fire-start l d t0 md ln = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src l d (bcHead BF.stBusy)))
          (_ , BF.receiveBF l d) (t0 , md , ln , blockFetch MsgStartBatch) ≡ just (decBFc-src l d (bcSil BF.stStreaming))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfc-fire-noblk : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decBFc-src l d (bcHead BF.stBusy)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.receiveBF l d) (t0 , md , ln , blockFetch MsgNoBlocks))) ]─►
    decBFc-src l d (bcSil BF.stIdle)
bfc-fire-noblk l d t0 md ln = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src l d (bcHead BF.stBusy)))
          (_ , BF.receiveBF l d) (t0 , md , ln , blockFetch MsgNoBlocks) ≡ just (decBFc-src l d (bcSil BF.stIdle))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfc-fire-blk : (l : Link) (d : Dir) (b : Block) (t0 : _) (md : _) (ln : _)
  → decBFc-src l d (bcHead BF.stStreaming)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.receiveBF l d) (t0 , md , ln , blockFetch (MsgBlock b)))) ]─►
    decBFc-src l d (bcBlk1 b)
bfc-fire-blk l d b t0 md ln = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src l d (bcHead BF.stStreaming)))
          (_ , BF.receiveBF l d) (t0 , md , ln , blockFetch (MsgBlock b)) ≡ just (decBFc-src l d (bcBlk1 b))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfc-fire-batch : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decBFc-src l d (bcHead BF.stStreaming)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.receiveBF l d) (t0 , md , ln , blockFetch MsgBatchDone))) ]─►
    decBFc-src l d (bcSil BF.stIdle)
bfc-fire-batch l d t0 md ln = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src l d (bcHead BF.stStreaming)))
          (_ , BF.receiveBF l d) (t0 , md , ln , blockFetch MsgBatchDone) ≡ just (decBFc-src l d (bcSil BF.stIdle))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfc-fire-req1 : (l : Link) (d : Dir) (r : ChainRange)
  → decBFc-src l d (bcReq1 r)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.sendBF l d) (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)))) ]─►
    decBFc-src l d (bcSil BF.stBusy)
bfc-fire-req1 (zero) lo r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (zero) lo (bcReq1 r)))
          (_ , BF.sendBF (zero) lo) (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ≡ just (decBFc-src (zero) lo (bcSil BF.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) = refl
bfc-fire-req1 (zero) hi r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (zero) hi (bcReq1 r)))
          (_ , BF.sendBF (zero) hi) (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ≡ just (decBFc-src (zero) hi (bcSil BF.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) = refl
bfc-fire-req1 (suc zero) lo r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc zero) lo (bcReq1 r)))
          (_ , BF.sendBF (suc zero) lo) (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ≡ just (decBFc-src (suc zero) lo (bcSil BF.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) = refl
bfc-fire-req1 (suc zero) hi r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc zero) hi (bcReq1 r)))
          (_ , BF.sendBF (suc zero) hi) (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ≡ just (decBFc-src (suc zero) hi (bcSil BF.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) = refl
bfc-fire-req1 (suc (suc zero)) lo r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc zero)) lo (bcReq1 r)))
          (_ , BF.sendBF (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ≡ just (decBFc-src (suc (suc zero)) lo (bcSil BF.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) = refl
bfc-fire-req1 (suc (suc zero)) hi r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc zero)) hi (bcReq1 r)))
          (_ , BF.sendBF (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ≡ just (decBFc-src (suc (suc zero)) hi (bcSil BF.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) = refl
bfc-fire-req1 (suc (suc (suc zero))) lo r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc (suc zero))) lo (bcReq1 r)))
          (_ , BF.sendBF (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ≡ just (decBFc-src (suc (suc (suc zero))) lo (bcSil BF.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) = refl
bfc-fire-req1 (suc (suc (suc zero))) hi r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc (suc zero))) hi (bcReq1 r)))
          (_ , BF.sendBF (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) ≡ just (decBFc-src (suc (suc (suc zero))) hi (bcSil BF.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r)) = refl

bfc-fire-cdone1 : (l : Link) (d : Dir)
  → decBFc-src l d (bcDone1)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.sendBF l d) (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone))) ]─►
    decBFc-src l d (bcSil BF.stDone)
bfc-fire-cdone1 (zero) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (zero) lo (bcDone1)))
          (_ , BF.sendBF (zero) lo) (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ≡ just (decBFc-src (zero) lo (bcSil BF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) = refl
bfc-fire-cdone1 (zero) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (zero) hi (bcDone1)))
          (_ , BF.sendBF (zero) hi) (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ≡ just (decBFc-src (zero) hi (bcSil BF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) = refl
bfc-fire-cdone1 (suc zero) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc zero) lo (bcDone1)))
          (_ , BF.sendBF (suc zero) lo) (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ≡ just (decBFc-src (suc zero) lo (bcSil BF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) = refl
bfc-fire-cdone1 (suc zero) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc zero) hi (bcDone1)))
          (_ , BF.sendBF (suc zero) hi) (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ≡ just (decBFc-src (suc zero) hi (bcSil BF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) = refl
bfc-fire-cdone1 (suc (suc zero)) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc zero)) lo (bcDone1)))
          (_ , BF.sendBF (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ≡ just (decBFc-src (suc (suc zero)) lo (bcSil BF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) = refl
bfc-fire-cdone1 (suc (suc zero)) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc zero)) hi (bcDone1)))
          (_ , BF.sendBF (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ≡ just (decBFc-src (suc (suc zero)) hi (bcSil BF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) = refl
bfc-fire-cdone1 (suc (suc (suc zero))) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc (suc zero))) lo (bcDone1)))
          (_ , BF.sendBF (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ≡ just (decBFc-src (suc (suc (suc zero))) lo (bcSil BF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) = refl
bfc-fire-cdone1 (suc (suc (suc zero))) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc (suc zero))) hi (bcDone1)))
          (_ , BF.sendBF (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) ≡ just (decBFc-src (suc (suc (suc zero))) hi (bcSil BF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone) = refl

bfc-fire-blk1 : (l : Link) (d : Dir) (b : Block)
  → decBFc-src l d (bcBlk1 b)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.apiBFev l d recvBFBlock) b)) ]─►
    decBFc-src l d (bcSil BF.stStreaming)
bfc-fire-blk1 (zero) lo b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (zero) lo (bcBlk1 b)))
          (_ , BF.apiBFev (zero) lo recvBFBlock) b ≡ just (decBFc-src (zero) lo (bcSil BF.stStreaming))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
bfc-fire-blk1 (zero) hi b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (zero) hi (bcBlk1 b)))
          (_ , BF.apiBFev (zero) hi recvBFBlock) b ≡ just (decBFc-src (zero) hi (bcSil BF.stStreaming))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
bfc-fire-blk1 (suc zero) lo b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc zero) lo (bcBlk1 b)))
          (_ , BF.apiBFev (suc zero) lo recvBFBlock) b ≡ just (decBFc-src (suc zero) lo (bcSil BF.stStreaming))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
bfc-fire-blk1 (suc zero) hi b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc zero) hi (bcBlk1 b)))
          (_ , BF.apiBFev (suc zero) hi recvBFBlock) b ≡ just (decBFc-src (suc zero) hi (bcSil BF.stStreaming))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
bfc-fire-blk1 (suc (suc zero)) lo b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc zero)) lo (bcBlk1 b)))
          (_ , BF.apiBFev (suc (suc zero)) lo recvBFBlock) b ≡ just (decBFc-src (suc (suc zero)) lo (bcSil BF.stStreaming))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
bfc-fire-blk1 (suc (suc zero)) hi b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc zero)) hi (bcBlk1 b)))
          (_ , BF.apiBFev (suc (suc zero)) hi recvBFBlock) b ≡ just (decBFc-src (suc (suc zero)) hi (bcSil BF.stStreaming))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
bfc-fire-blk1 (suc (suc (suc zero))) lo b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc (suc zero))) lo (bcBlk1 b)))
          (_ , BF.apiBFev (suc (suc (suc zero))) lo recvBFBlock) b ≡ just (decBFc-src (suc (suc (suc zero))) lo (bcSil BF.stStreaming))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
bfc-fire-blk1 (suc (suc (suc zero))) hi b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFc-src (suc (suc (suc zero))) hi (bcBlk1 b)))
          (_ , BF.apiBFev (suc (suc (suc zero))) hi recvBFBlock) b ≡ just (decBFc-src (suc (suc (suc zero))) hi (bcSil BF.stStreaming))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl

-- BFC-FIRE-END


-- BFC-HSTEP-BEGIN
bfc-hstep : (l : Link) (d : Dir) (st : BF.BFState)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → absBFc l d (bcHead st) ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M
  → Σ[ pos′ ∈ BFcPos ] (decBFc l d (bcHead st) ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► decBFc l d pos′)
      × (M ≡ absBFc l d pos′)

-- stIdle (bcIdle): api sends — enumerate 8 ApiBFTag
bfc-hstep l d BF.stIdle {e₁ = BF.apiBFev l' d' sendBFRequestRange} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcReq1 a , RFBF.renameMap-ev-fwd (bfc-fire-req l d a) , mkMbfc l d (bcReq1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stIdle {e₁ = BF.apiBFev l' d' sendBFClientDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcDone1 , RFBF.renameMap-ev-fwd (bfc-fire-cdone l d) , mkMbfc l d (bcDone1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stIdle {e₁ = BF.apiBFev l' d' sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stIdle {e₁ = BF.apiBFev l' d' sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stIdle {e₁ = BF.apiBFev l' d' sendBFBlock} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stIdle {e₁ = BF.apiBFev l' d' sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stIdle {e₁ = BF.apiBFev l' d' recvBFBlock} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stIdle {e₁ = BF.apiBFev l' d' reqBFRange} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stIdle {e₁ = BF.sendBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stIdle {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stBusy: receives on the wire (receiveBF)
bfc-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgStartBatch} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stStreaming , RFBF.renameMap-ev-fwd (bfc-fire-start l d t0 md ln) , mkMbfc l d (bcSil BF.stStreaming) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgNoBlocks} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stIdle , RFBF.renameMap-ev-fwd (bfc-fire-noblk l d t0 md ln) , mkMbfc l d (bcSil BF.stIdle) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.sendBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.apiBFev l' d' m} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stBusy {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stStreaming: receives on the wire (receiveBF)
bfc-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgBlock b)} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcBlk1 b , RFBF.renameMap-ev-fwd (bfc-fire-blk l d b t0 md ln) , mkMbfc l d (bcBlk1 b) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgBatchDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bcSil BF.stIdle , RFBF.renameMap-ev-fwd (bfc-fire-batch l d t0 md ln) , mkMbfc l d (bcSil BF.stIdle) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgRequestRange r)} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgClientDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch _} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.sendBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.apiBFev l' d' m} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfc-hstep l d BF.stStreaming {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stDone (bcTerm): terminal
bfc-hstep l d BF.stDone step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- BFC-HSTEP-END


-- BFC-LEAF-BEGIN
decBFc-ev-prod-abs : (l : Link) (d : Dir) (pos : BFcPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → absBFc l d pos ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M
  → Σ[ pos′ ∈ BFcPos ] (decBFc l d pos ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFc l d pos′)
      × (M ≡ absBFc l d pos′)

decBFc-ev-prod-abs l d (bcHead st) step with bfc-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
decBFc-ev-prod-abs l d (bcSil st) step with bfc-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decBFc-sil-step l d st) τ*-refl) f τ*-refl , m

-- bcReq1 r: fires sendBF (RequestRange)
decBFc-ev-prod-abs l d (bcReq1 r) {e₁ = BF.sendBF l' d'} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch (MsgRequestRange r))
...     | yes refl = bcSil BF.stBusy , wev τ*-refl (RFBF.renameMap-ev-fwd (bfc-fire-req1 l d r)) τ*-refl , mkMbfc l d (bcSil BF.stBusy) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcReq1 r) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcReq1 r) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcReq1 r) {e₁ = BF.apiBFev l' d' m} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcReq1 r) {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcReq1 r) {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bcDone1: fires sendBF (ClientDone)
decBFc-ev-prod-abs l d (bcDone1) {e₁ = BF.sendBF l' d'} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcDone1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , blockFetch MsgClientDone)
...     | yes refl = bcSil BF.stDone , wev τ*-refl (RFBF.renameMap-ev-fwd (bfc-fire-cdone1 l d)) τ*-refl , mkMbfc l d (bcSil BF.stDone) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcDone1) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcDone1) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcDone1) {e₁ = BF.apiBFev l' d' m} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcDone1) {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcDone1) {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bcBlk1 b: fires apiBFev recvBFBlock (Block gate) → bcSil stStreaming
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' sendBFRequestRange} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' sendBFClientDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' sendBFBlock} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' recvBFBlock} {a} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ decBlock ⦄ a b
...     | yes refl = bcSil BF.stStreaming , wev τ*-refl (RFBF.renameMap-ev-fwd (bfc-fire-blk1 l d b)) τ*-refl , mkMbfc l d (bcSil BF.stStreaming) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' recvBFBlock} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' recvBFBlock} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.apiBFev l' d' reqBFRange} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.sendBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFc-ev-prod-abs l d (bcBlk1 b) {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfc l d) (coarsenBFc (bcBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- BFC-LEAF-END


-- BFS-FIRE-BEGIN
------------------------------------------------------------------------
-- STEP 2 (BF-SERVER).  `bsHead stIdle` RECEIVES on the wire;
-- stBusy/stStreaming api-SEND (enumerate 8 ApiBFTag).
------------------------------------------------------------------------
Tbfs : Link → Dir → NS.Table NS.BFsPos
Tbfs l d = record { isFin = NS.bfSfin ; nxt = NS.bfSnxt l d }
mkMbfs : (l : Link) (d : Dir) (pos′ : BFsPos) {q′ : NS.BFsPos} {M : NetProc}
  → M ≡ tableSpec (Tbfs l d) q′ → q′ ≡ coarsenBFs pos′ → M ≡ absBFs l d pos′
mkMbfs l d pos′ Meq qeq = trans Meq (cong (tableSpec (Tbfs l d)) qeq)

bfs-fire-req : (l : Link) (d : Dir) (r : ChainRange) (t0 : _) (md : _) (ln : _)
  → decBFs-src l d (bsHead BF.stIdle)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.receiveBF l d) (t0 , md , ln , blockFetch (MsgRequestRange r)))) ]─►
    decBFs-src l d (bsReq1 r)
bfs-fire-req l d r t0 md ln = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src l d (bsHead BF.stIdle)))
          (_ , BF.receiveBF l d) (t0 , md , ln , blockFetch (MsgRequestRange r)) ≡ just (decBFs-src l d (bsReq1 r))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfs-fire-cdone : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decBFs-src l d (bsHead BF.stIdle)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.receiveBF l d) (t0 , md , ln , blockFetch MsgClientDone))) ]─►
    decBFs-src l d (bsDone1)
bfs-fire-cdone l d t0 md ln = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src l d (bsHead BF.stIdle)))
          (_ , BF.receiveBF l d) (t0 , md , ln , blockFetch MsgClientDone) ≡ just (decBFs-src l d (bsDone1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfs-fire-start : (l : Link) (d : Dir)
  → decBFs-src l d (bsHead BF.stBusy)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.apiBFev l d sendBFStartBatch) U.tt)) ]─►
    decBFs-src l d (bsStart1)
bfs-fire-start l d  = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src l d (bsHead BF.stBusy)))
          (_ , BF.apiBFev l d sendBFStartBatch) U.tt ≡ just (decBFs-src l d (bsStart1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfs-fire-noblk : (l : Link) (d : Dir)
  → decBFs-src l d (bsHead BF.stBusy)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.apiBFev l d sendBFNoBlocks) U.tt)) ]─►
    decBFs-src l d (bsNoBlk1)
bfs-fire-noblk l d  = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src l d (bsHead BF.stBusy)))
          (_ , BF.apiBFev l d sendBFNoBlocks) U.tt ≡ just (decBFs-src l d (bsNoBlk1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfs-fire-blk : (l : Link) (d : Dir) (b : Block)
  → decBFs-src l d (bsHead BF.stStreaming)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.apiBFev l d sendBFBlock) b)) ]─►
    decBFs-src l d (bsBlk1 b)
bfs-fire-blk l d b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src l d (bsHead BF.stStreaming)))
          (_ , BF.apiBFev l d sendBFBlock) b ≡ just (decBFs-src l d (bsBlk1 b))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfs-fire-batch : (l : Link) (d : Dir)
  → decBFs-src l d (bsHead BF.stStreaming)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.apiBFev l d sendBFBatchDone) U.tt)) ]─►
    decBFs-src l d (bsBatchDone1)
bfs-fire-batch l d  = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src l d (bsHead BF.stStreaming)))
          (_ , BF.apiBFev l d sendBFBatchDone) U.tt ≡ just (decBFs-src l d (bsBatchDone1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

bfs-fire-req1 : (l : Link) (d : Dir) (r : ChainRange)
  → decBFs-src l d (bsReq1 r)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.apiBFev l d reqBFRange) r)) ]─►
    decBFs-src l d (bsSil BF.stBusy)
bfs-fire-req1 (zero) lo r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) lo (bsReq1 r)))
          (_ , BF.apiBFev (zero) lo reqBFRange) r ≡ just (decBFs-src (zero) lo (bsSil BF.stBusy))
    o rewrite ≟-yes-refl ⦃ DecEq-ChainRange ⦄ r = refl
bfs-fire-req1 (zero) hi r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) hi (bsReq1 r)))
          (_ , BF.apiBFev (zero) hi reqBFRange) r ≡ just (decBFs-src (zero) hi (bsSil BF.stBusy))
    o rewrite ≟-yes-refl ⦃ DecEq-ChainRange ⦄ r = refl
bfs-fire-req1 (suc zero) lo r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) lo (bsReq1 r)))
          (_ , BF.apiBFev (suc zero) lo reqBFRange) r ≡ just (decBFs-src (suc zero) lo (bsSil BF.stBusy))
    o rewrite ≟-yes-refl ⦃ DecEq-ChainRange ⦄ r = refl
bfs-fire-req1 (suc zero) hi r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) hi (bsReq1 r)))
          (_ , BF.apiBFev (suc zero) hi reqBFRange) r ≡ just (decBFs-src (suc zero) hi (bsSil BF.stBusy))
    o rewrite ≟-yes-refl ⦃ DecEq-ChainRange ⦄ r = refl
bfs-fire-req1 (suc (suc zero)) lo r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) lo (bsReq1 r)))
          (_ , BF.apiBFev (suc (suc zero)) lo reqBFRange) r ≡ just (decBFs-src (suc (suc zero)) lo (bsSil BF.stBusy))
    o rewrite ≟-yes-refl ⦃ DecEq-ChainRange ⦄ r = refl
bfs-fire-req1 (suc (suc zero)) hi r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) hi (bsReq1 r)))
          (_ , BF.apiBFev (suc (suc zero)) hi reqBFRange) r ≡ just (decBFs-src (suc (suc zero)) hi (bsSil BF.stBusy))
    o rewrite ≟-yes-refl ⦃ DecEq-ChainRange ⦄ r = refl
bfs-fire-req1 (suc (suc (suc zero))) lo r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) lo (bsReq1 r)))
          (_ , BF.apiBFev (suc (suc (suc zero))) lo reqBFRange) r ≡ just (decBFs-src (suc (suc (suc zero))) lo (bsSil BF.stBusy))
    o rewrite ≟-yes-refl ⦃ DecEq-ChainRange ⦄ r = refl
bfs-fire-req1 (suc (suc (suc zero))) hi r = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) hi (bsReq1 r)))
          (_ , BF.apiBFev (suc (suc (suc zero))) hi reqBFRange) r ≡ just (decBFs-src (suc (suc (suc zero))) hi (bsSil BF.stBusy))
    o rewrite ≟-yes-refl ⦃ DecEq-ChainRange ⦄ r = refl

bfs-fire-done1 : (l : Link) (d : Dir)
  → decBFs-src l d (bsDone1)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.doneBF l d) U.tt)) ]─►
    decBFs-src l d (bsSil BF.stDone)
bfs-fire-done1 (zero) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) lo (bsDone1)))
          (_ , BF.doneBF (zero) lo) U.tt ≡ just (decBFs-src (zero) lo (bsSil BF.stDone))
    o = refl
bfs-fire-done1 (zero) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) hi (bsDone1)))
          (_ , BF.doneBF (zero) hi) U.tt ≡ just (decBFs-src (zero) hi (bsSil BF.stDone))
    o = refl
bfs-fire-done1 (suc zero) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) lo (bsDone1)))
          (_ , BF.doneBF (suc zero) lo) U.tt ≡ just (decBFs-src (suc zero) lo (bsSil BF.stDone))
    o = refl
bfs-fire-done1 (suc zero) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) hi (bsDone1)))
          (_ , BF.doneBF (suc zero) hi) U.tt ≡ just (decBFs-src (suc zero) hi (bsSil BF.stDone))
    o = refl
bfs-fire-done1 (suc (suc zero)) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) lo (bsDone1)))
          (_ , BF.doneBF (suc (suc zero)) lo) U.tt ≡ just (decBFs-src (suc (suc zero)) lo (bsSil BF.stDone))
    o = refl
bfs-fire-done1 (suc (suc zero)) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) hi (bsDone1)))
          (_ , BF.doneBF (suc (suc zero)) hi) U.tt ≡ just (decBFs-src (suc (suc zero)) hi (bsSil BF.stDone))
    o = refl
bfs-fire-done1 (suc (suc (suc zero))) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) lo (bsDone1)))
          (_ , BF.doneBF (suc (suc (suc zero))) lo) U.tt ≡ just (decBFs-src (suc (suc (suc zero))) lo (bsSil BF.stDone))
    o = refl
bfs-fire-done1 (suc (suc (suc zero))) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) hi (bsDone1)))
          (_ , BF.doneBF (suc (suc (suc zero))) hi) U.tt ≡ just (decBFs-src (suc (suc (suc zero))) hi (bsSil BF.stDone))
    o = refl

bfs-fire-start1 : (l : Link) (d : Dir)
  → decBFs-src l d (bsStart1)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.sendBF l d) (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch))) ]─►
    decBFs-src l d (bsSil BF.stStreaming)
bfs-fire-start1 (zero) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) lo (bsStart1)))
          (_ , BF.sendBF (zero) lo) (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ≡ just (decBFs-src (zero) lo (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) = refl
bfs-fire-start1 (zero) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) hi (bsStart1)))
          (_ , BF.sendBF (zero) hi) (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ≡ just (decBFs-src (zero) hi (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) = refl
bfs-fire-start1 (suc zero) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) lo (bsStart1)))
          (_ , BF.sendBF (suc zero) lo) (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ≡ just (decBFs-src (suc zero) lo (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) = refl
bfs-fire-start1 (suc zero) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) hi (bsStart1)))
          (_ , BF.sendBF (suc zero) hi) (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ≡ just (decBFs-src (suc zero) hi (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) = refl
bfs-fire-start1 (suc (suc zero)) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) lo (bsStart1)))
          (_ , BF.sendBF (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ≡ just (decBFs-src (suc (suc zero)) lo (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) = refl
bfs-fire-start1 (suc (suc zero)) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) hi (bsStart1)))
          (_ , BF.sendBF (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ≡ just (decBFs-src (suc (suc zero)) hi (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) = refl
bfs-fire-start1 (suc (suc (suc zero))) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) lo (bsStart1)))
          (_ , BF.sendBF (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ≡ just (decBFs-src (suc (suc (suc zero))) lo (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) = refl
bfs-fire-start1 (suc (suc (suc zero))) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) hi (bsStart1)))
          (_ , BF.sendBF (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) ≡ just (decBFs-src (suc (suc (suc zero))) hi (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch) = refl

bfs-fire-noblk1 : (l : Link) (d : Dir)
  → decBFs-src l d (bsNoBlk1)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.sendBF l d) (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks))) ]─►
    decBFs-src l d (bsSil BF.stIdle)
bfs-fire-noblk1 (zero) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) lo (bsNoBlk1)))
          (_ , BF.sendBF (zero) lo) (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ≡ just (decBFs-src (zero) lo (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) = refl
bfs-fire-noblk1 (zero) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) hi (bsNoBlk1)))
          (_ , BF.sendBF (zero) hi) (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ≡ just (decBFs-src (zero) hi (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) = refl
bfs-fire-noblk1 (suc zero) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) lo (bsNoBlk1)))
          (_ , BF.sendBF (suc zero) lo) (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ≡ just (decBFs-src (suc zero) lo (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) = refl
bfs-fire-noblk1 (suc zero) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) hi (bsNoBlk1)))
          (_ , BF.sendBF (suc zero) hi) (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ≡ just (decBFs-src (suc zero) hi (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) = refl
bfs-fire-noblk1 (suc (suc zero)) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) lo (bsNoBlk1)))
          (_ , BF.sendBF (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ≡ just (decBFs-src (suc (suc zero)) lo (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) = refl
bfs-fire-noblk1 (suc (suc zero)) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) hi (bsNoBlk1)))
          (_ , BF.sendBF (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ≡ just (decBFs-src (suc (suc zero)) hi (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) = refl
bfs-fire-noblk1 (suc (suc (suc zero))) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) lo (bsNoBlk1)))
          (_ , BF.sendBF (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ≡ just (decBFs-src (suc (suc (suc zero))) lo (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) = refl
bfs-fire-noblk1 (suc (suc (suc zero))) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) hi (bsNoBlk1)))
          (_ , BF.sendBF (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) ≡ just (decBFs-src (suc (suc (suc zero))) hi (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks) = refl

bfs-fire-blk1 : (l : Link) (d : Dir) (b : Block)
  → decBFs-src l d (bsBlk1 b)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.sendBF l d) (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)))) ]─►
    decBFs-src l d (bsSil BF.stStreaming)
bfs-fire-blk1 (zero) lo b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) lo (bsBlk1 b)))
          (_ , BF.sendBF (zero) lo) (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ≡ just (decBFs-src (zero) lo (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) = refl
bfs-fire-blk1 (zero) hi b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) hi (bsBlk1 b)))
          (_ , BF.sendBF (zero) hi) (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ≡ just (decBFs-src (zero) hi (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) = refl
bfs-fire-blk1 (suc zero) lo b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) lo (bsBlk1 b)))
          (_ , BF.sendBF (suc zero) lo) (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ≡ just (decBFs-src (suc zero) lo (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) = refl
bfs-fire-blk1 (suc zero) hi b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) hi (bsBlk1 b)))
          (_ , BF.sendBF (suc zero) hi) (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ≡ just (decBFs-src (suc zero) hi (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) = refl
bfs-fire-blk1 (suc (suc zero)) lo b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) lo (bsBlk1 b)))
          (_ , BF.sendBF (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ≡ just (decBFs-src (suc (suc zero)) lo (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) = refl
bfs-fire-blk1 (suc (suc zero)) hi b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) hi (bsBlk1 b)))
          (_ , BF.sendBF (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ≡ just (decBFs-src (suc (suc zero)) hi (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) = refl
bfs-fire-blk1 (suc (suc (suc zero))) lo b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) lo (bsBlk1 b)))
          (_ , BF.sendBF (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ≡ just (decBFs-src (suc (suc (suc zero))) lo (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) = refl
bfs-fire-blk1 (suc (suc (suc zero))) hi b = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) hi (bsBlk1 b)))
          (_ , BF.sendBF (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) ≡ just (decBFs-src (suc (suc (suc zero))) hi (bsSil BF.stStreaming))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b)) = refl

bfs-fire-batch1 : (l : Link) (d : Dir)
  → decBFs-src l d (bsBatchDone1)
      BFL.─[ BFL.ev (BFL.evl (BFL.evLabel _ (BF.sendBF l d) (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone))) ]─►
    decBFs-src l d (bsSil BF.stIdle)
bfs-fire-batch1 (zero) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) lo (bsBatchDone1)))
          (_ , BF.sendBF (zero) lo) (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ≡ just (decBFs-src (zero) lo (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) = refl
bfs-fire-batch1 (zero) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (zero) hi (bsBatchDone1)))
          (_ , BF.sendBF (zero) hi) (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ≡ just (decBFs-src (zero) hi (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) = refl
bfs-fire-batch1 (suc zero) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) lo (bsBatchDone1)))
          (_ , BF.sendBF (suc zero) lo) (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ≡ just (decBFs-src (suc zero) lo (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) = refl
bfs-fire-batch1 (suc zero) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc zero) hi (bsBatchDone1)))
          (_ , BF.sendBF (suc zero) hi) (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ≡ just (decBFs-src (suc zero) hi (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) = refl
bfs-fire-batch1 (suc (suc zero)) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) lo (bsBatchDone1)))
          (_ , BF.sendBF (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ≡ just (decBFs-src (suc (suc zero)) lo (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) = refl
bfs-fire-batch1 (suc (suc zero)) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc zero)) hi (bsBatchDone1)))
          (_ , BF.sendBF (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ≡ just (decBFs-src (suc (suc zero)) hi (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) = refl
bfs-fire-batch1 (suc (suc (suc zero))) lo = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) lo (bsBatchDone1)))
          (_ , BF.sendBF (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ≡ just (decBFs-src (suc (suc (suc zero))) lo (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) = refl
bfs-fire-batch1 (suc (suc (suc zero))) hi = BFL.sVis refl o
  where
    o : vis-ofB (PTree.force (decBFs-src (suc (suc (suc zero))) hi (bsBatchDone1)))
          (_ , BF.sendBF (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) ≡ just (decBFs-src (suc (suc (suc zero))) hi (bsSil BF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone) = refl

-- BFS-FIRE-END


-- BFS-HSTEP-BEGIN
bfs-hstep : (l : Link) (d : Dir) (st : BF.BFState)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → absBFs l d (bsHead st) ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M
  → Σ[ pos′ ∈ BFsPos ] (decBFs l d (bsHead st) ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► decBFs l d pos′)
      × (M ≡ absBFs l d pos′)

-- stIdle (bsIdle): receives RequestRange / ClientDone on the wire
bfs-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch (MsgRequestRange r)} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsReq1 r , RFBF.renameMap-ev-fwd (bfs-fire-req l d r t0 md ln) , mkMbfs l d (bsReq1 r) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = t0 , md , ln , blockFetch MsgClientDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsDone1 , RFBF.renameMap-ev-fwd (bfs-fire-cdone l d t0 md ln) , mkMbfs l d (bsDone1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgStartBatch} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgNoBlocks} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch (MsgBlock b)} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , blockFetch MsgBatchDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , keepAlive _} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , chainSync _} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , txSubmission _} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosNotify _} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.receiveBF l' d'} {a = _ , _ , _ , leiosFetch _} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.sendBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.apiBFev l' d' m} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stIdle {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stBusy: api sends — enumerate 8 ApiBFTag
bfs-hstep l d BF.stBusy {e₁ = BF.apiBFev l' d' sendBFRequestRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stBusy {e₁ = BF.apiBFev l' d' sendBFClientDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stBusy {e₁ = BF.apiBFev l' d' sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsStart1 , RFBF.renameMap-ev-fwd (bfs-fire-start l d) , mkMbfs l d (bsStart1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stBusy {e₁ = BF.apiBFev l' d' sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsNoBlk1 , RFBF.renameMap-ev-fwd (bfs-fire-noblk l d) , mkMbfs l d (bsNoBlk1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stBusy {e₁ = BF.apiBFev l' d' sendBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stBusy {e₁ = BF.apiBFev l' d' sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stBusy {e₁ = BF.apiBFev l' d' recvBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stBusy {e₁ = BF.apiBFev l' d' reqBFRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stBusy {e₁ = BF.sendBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stBusy {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stBusy {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stStreaming: api sends — enumerate 8 ApiBFTag
bfs-hstep l d BF.stStreaming {e₁ = BF.apiBFev l' d' sendBFRequestRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stStreaming {e₁ = BF.apiBFev l' d' sendBFClientDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stStreaming {e₁ = BF.apiBFev l' d' sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stStreaming {e₁ = BF.apiBFev l' d' sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stStreaming {e₁ = BF.apiBFev l' d' sendBFBlock} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsBlk1 a , RFBF.renameMap-ev-fwd (bfs-fire-blk l d a) , mkMbfs l d (bsBlk1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stStreaming {e₁ = BF.apiBFev l' d' sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsBatchDone1 , RFBF.renameMap-ev-fwd (bfs-fire-batch l d) , mkMbfs l d (bsBatchDone1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stStreaming {e₁ = BF.apiBFev l' d' recvBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stStreaming {e₁ = BF.apiBFev l' d' reqBFRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stStreaming {e₁ = BF.sendBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stStreaming {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
bfs-hstep l d BF.stStreaming {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stStreaming)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- stDone (bsTerm): terminal
bfs-hstep l d BF.stDone step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsHead BF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- BFS-HSTEP-END


-- BFS-LEAF-BEGIN
decBFs-ev-prod-abs : (l : Link) (d : Dir) (pos : BFsPos)
    {X : Set 0ℓ} {e₁ : BF.BFEv X} {a : X} {M : NetProc}
  → absBFs l d pos ─[ ev (evl (evLabel X (ιBF e₁) a)) ]─► M
  → Σ[ pos′ ∈ BFsPos ] (decBFs l d pos ═[ ev (evl (evLabel X (ιBF e₁) a)) ]═► decBFs l d pos′)
      × (M ≡ absBFs l d pos′)

decBFs-ev-prod-abs l d (bsHead st) step with bfs-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
decBFs-ev-prod-abs l d (bsSil st) step with bfs-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decBFs-sil-step l d st) τ*-refl) f τ*-refl , m

-- bsReq1 r: fires apiBFev reqBFRange (ChainRange gate) → bsSil stBusy
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.apiBFev l' d' sendBFRequestRange} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.apiBFev l' d' sendBFClientDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.apiBFev l' d' sendBFStartBatch} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.apiBFev l' d' sendBFNoBlocks} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.apiBFev l' d' sendBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.apiBFev l' d' sendBFBatchDone} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.apiBFev l' d' recvBFBlock} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.apiBFev l' d' reqBFRange} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ DecEq-ChainRange ⦄ a r
...     | yes refl = bsSil BF.stBusy , wev τ*-refl (RFBF.renameMap-ev-fwd (bfs-fire-req1 l d r)) τ*-refl , mkMbfs l d (bsSil BF.stBusy) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.apiBFev l' d' reqBFRange} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.apiBFev l' d' reqBFRange} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.sendBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsReq1 r) {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsReq1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bsDone1: fires doneBF (⊤) → bsSil stDone
decBFs-ev-prod-abs l d bsDone1 {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsDone1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = bsSil BF.stDone , wev τ*-refl (RFBF.renameMap-ev-fwd (bfs-fire-done1 l d)) τ*-refl , mkMbfs l d (bsSil BF.stDone) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d bsDone1 {e₁ = BF.apiBFev l' d' m} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d bsDone1 {e₁ = BF.sendBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d bsDone1 {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bsStart1: fires sendBF (StartBatch)
decBFs-ev-prod-abs l d (bsStart1) {e₁ = BF.sendBF l' d'} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsStart1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgStartBatch)
...     | yes refl = bsSil BF.stStreaming , wev τ*-refl (RFBF.renameMap-ev-fwd (bfs-fire-start1 l d)) τ*-refl , mkMbfs l d (bsSil BF.stStreaming) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsStart1) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsStart1) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsStart1) {e₁ = BF.apiBFev l' d' m} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsStart1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsStart1) {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsStart1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsStart1) {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsStart1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bsNoBlk1: fires sendBF (NoBlocks)
decBFs-ev-prod-abs l d (bsNoBlk1) {e₁ = BF.sendBF l' d'} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsNoBlk1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgNoBlocks)
...     | yes refl = bsSil BF.stIdle , wev τ*-refl (RFBF.renameMap-ev-fwd (bfs-fire-noblk1 l d)) τ*-refl , mkMbfs l d (bsSil BF.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsNoBlk1) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsNoBlk1) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsNoBlk1) {e₁ = BF.apiBFev l' d' m} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsNoBlk1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsNoBlk1) {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsNoBlk1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsNoBlk1) {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsNoBlk1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bsBlk1 b: fires sendBF (Block)
decBFs-ev-prod-abs l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch (MsgBlock b))
...     | yes refl = bsSil BF.stStreaming , wev τ*-refl (RFBF.renameMap-ev-fwd (bfs-fire-blk1 l d b)) τ*-refl , mkMbfs l d (bsSil BF.stStreaming) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsBlk1 b) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsBlk1 b) {e₁ = BF.apiBFev l' d' m} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsBlk1 b) {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsBlk1 b) {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBlk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- bsBatchDone1: fires sendBF (BatchDone)
decBFs-ev-prod-abs l d (bsBatchDone1) {e₁ = BF.sendBF l' d'} {a} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBatchDone1)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , blockFetch MsgBatchDone)
...     | yes refl = bsSil BF.stIdle , wev τ*-refl (RFBF.renameMap-ev-fwd (bfs-fire-batch1 l d)) τ*-refl , mkMbfs l d (bsSil BF.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsBatchDone1) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsBatchDone1) {e₁ = BF.sendBF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsBatchDone1) {e₁ = BF.apiBFev l' d' m} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBatchDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsBatchDone1) {e₁ = BF.receiveBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBatchDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decBFs-ev-prod-abs l d (bsBatchDone1) {e₁ = BF.doneBF l' d'} step
  with tableSpec-ev-inv (Tbfs l d) (coarsenBFs (bsBatchDone1)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- BFS-LEAF-END

-- KA-SECTION-BEGIN
------------------------------------------------------------------------
-- INERT PEER KeepAlive (KA) — backward production leaves.  Cookie = ⊤ in
-- `p`, so every KA value gate reduces definitionally (`decEq⊤ = yes refl`);
-- the only value the leaf must split on is the wire-send payload (via the
-- baked `DecEq-Payload`).  KA has NO `decKAc/decKAs-sil-step` in SysStep, so
-- they are defined here.  Mirrors the committed CS/BF driven-peer leaves.
------------------------------------------------------------------------

-- KA-client loop re-entry sil → loop head (concrete peer τ)
decKAc-sil-step : (l : Link) (d : Dir) (st : KA.KAState)
  → decKAc l d (kcSil st) ─[ τ ]─► decKAc l d (kcHead st)
decKAc-sil-step l d st = sSil refl

-- KA-server loop re-entry sil → loop head (concrete peer τ)
decKAs-sil-step : (l : Link) (d : Dir) (st : KA.KAState)
  → decKAs l d (ksSil st) ─[ τ ]─► decKAs l d (ksHead st)
decKAs-sil-step l d st = sSil refl

-- head stClient → kcReq1 c (fires apiKAev sendKAMsg, value c : Cookie)
kac-fire-req : (l : Link) (d : Dir) (c : _)
  → decKAc-src l d (kcHead KA.stClient)
      KAL.─[ KAL.ev (KAL.evl (KAL.evLabel _ (KA.apiKAev l d sendKAMsg) c)) ]─►
    decKAc-src l d (kcReq1 c)
kac-fire-req l d c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src l d (kcHead KA.stClient)))
          (_ , KA.apiKAev l d sendKAMsg) c ≡ just (decKAc-src l d (kcReq1 c))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stClient → kcDone1 (fires apiKAev sendKADone, ⊤)
kac-fire-done : (l : Link) (d : Dir)
  → decKAc-src l d (kcHead KA.stClient)
      KAL.─[ KAL.ev (KAL.evl (KAL.evLabel _ (KA.apiKAev l d sendKADone) U.tt)) ]─►
    decKAc-src l d kcDone1
kac-fire-done l d = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src l d (kcHead KA.stClient)))
          (_ , KA.apiKAev l d sendKADone) U.tt ≡ just (decKAc-src l d kcDone1)
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stServer cq → kcSil stClient (fires receiveKA, response payload cr)
kac-fire-resp : (l : Link) (d : Dir) (cq cr : _) (t0 : _) (md : _) (ln : _)
  → decKAc-src l d (kcHead (KA.stServer cq))
      KAL.─[ KAL.ev (KAL.evl (KAL.evLabel _ (KA.receiveKA l d)
               (t0 , md , ln , keepAlive (MsgKeepAliveResponse cr)))) ]─►
    decKAc-src l d (kcSil KA.stClient)
kac-fire-resp l d cq cr t0 md ln = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src l d (kcHead (KA.stServer cq))))
          (_ , KA.receiveKA l d) (t0 , md , ln , keepAlive (MsgKeepAliveResponse cr))
          ≡ just (decKAc-src l d (kcSil KA.stClient))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- MID kcReq1 c → kcSil (stServer c) (fires sendKA, payload MsgKeepAlive c) — Fin-enum
kac-fire-req1 : (l : Link) (d : Dir) (c : _)
  → decKAc-src l d (kcReq1 c)
      KAL.─[ KAL.ev (KAL.evl (KAL.evLabel _ (KA.sendKA l d) (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)))) ]─►
    decKAc-src l d (kcSil (KA.stServer c))
kac-fire-req1 (zero) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (zero) lo (kcReq1 c)))
          (_ , KA.sendKA (zero) lo) (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) ≡ just (decKAc-src (zero) lo (kcSil (KA.stServer c)))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) = refl
kac-fire-req1 (zero) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (zero) hi (kcReq1 c)))
          (_ , KA.sendKA (zero) hi) (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) ≡ just (decKAc-src (zero) hi (kcSil (KA.stServer c)))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) = refl
kac-fire-req1 (suc zero) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc zero) lo (kcReq1 c)))
          (_ , KA.sendKA (suc zero) lo) (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) ≡ just (decKAc-src (suc zero) lo (kcSil (KA.stServer c)))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) = refl
kac-fire-req1 (suc zero) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc zero) hi (kcReq1 c)))
          (_ , KA.sendKA (suc zero) hi) (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) ≡ just (decKAc-src (suc zero) hi (kcSil (KA.stServer c)))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) = refl
kac-fire-req1 (suc (suc zero)) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc (suc zero)) lo (kcReq1 c)))
          (_ , KA.sendKA (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) ≡ just (decKAc-src (suc (suc zero)) lo (kcSil (KA.stServer c)))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) = refl
kac-fire-req1 (suc (suc zero)) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc (suc zero)) hi (kcReq1 c)))
          (_ , KA.sendKA (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) ≡ just (decKAc-src (suc (suc zero)) hi (kcSil (KA.stServer c)))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) = refl
kac-fire-req1 (suc (suc (suc zero))) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc (suc (suc zero))) lo (kcReq1 c)))
          (_ , KA.sendKA (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) ≡ just (decKAc-src (suc (suc (suc zero))) lo (kcSil (KA.stServer c)))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) = refl
kac-fire-req1 (suc (suc (suc zero))) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc (suc (suc zero))) hi (kcReq1 c)))
          (_ , KA.sendKA (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) ≡ just (decKAc-src (suc (suc (suc zero))) hi (kcSil (KA.stServer c)))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c)) = refl

-- MID kcDone1 → kcSil stDone (fires sendKA, payload MsgKADone) — Fin-enum
kac-fire-done1 : (l : Link) (d : Dir)
  → decKAc-src l d kcDone1
      KAL.─[ KAL.ev (KAL.evl (KAL.evLabel _ (KA.sendKA l d) (time₀ , FromInitiator , length₀ , keepAlive MsgKADone))) ]─►
    decKAc-src l d (kcSil KA.stDone)
kac-fire-done1 (zero) lo = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (zero) lo (kcDone1)))
          (_ , KA.sendKA (zero) lo) (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) ≡ just (decKAc-src (zero) lo (kcSil KA.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) = refl
kac-fire-done1 (zero) hi = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (zero) hi (kcDone1)))
          (_ , KA.sendKA (zero) hi) (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) ≡ just (decKAc-src (zero) hi (kcSil KA.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) = refl
kac-fire-done1 (suc zero) lo = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc zero) lo (kcDone1)))
          (_ , KA.sendKA (suc zero) lo) (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) ≡ just (decKAc-src (suc zero) lo (kcSil KA.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) = refl
kac-fire-done1 (suc zero) hi = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc zero) hi (kcDone1)))
          (_ , KA.sendKA (suc zero) hi) (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) ≡ just (decKAc-src (suc zero) hi (kcSil KA.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) = refl
kac-fire-done1 (suc (suc zero)) lo = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc (suc zero)) lo (kcDone1)))
          (_ , KA.sendKA (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) ≡ just (decKAc-src (suc (suc zero)) lo (kcSil KA.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) = refl
kac-fire-done1 (suc (suc zero)) hi = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc (suc zero)) hi (kcDone1)))
          (_ , KA.sendKA (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) ≡ just (decKAc-src (suc (suc zero)) hi (kcSil KA.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) = refl
kac-fire-done1 (suc (suc (suc zero))) lo = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc (suc (suc zero))) lo (kcDone1)))
          (_ , KA.sendKA (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) ≡ just (decKAc-src (suc (suc (suc zero))) lo (kcSil KA.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) = refl
kac-fire-done1 (suc (suc (suc zero))) hi = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAc-src (suc (suc (suc zero))) hi (kcDone1)))
          (_ , KA.sendKA (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) ≡ just (decKAc-src (suc (suc (suc zero))) hi (kcSil KA.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , keepAlive MsgKADone) = refl

-- head stClient → ksRecv1 c (fires receiveKA, payload MsgKeepAlive c)
kas-fire-recv : (l : Link) (d : Dir) (c : _) (t0 : _) (md : _) (ln : _)
  → decKAs-src l d (ksHead KA.stClient)
      KAL.─[ KAL.ev (KAL.evl (KAL.evLabel _ (KA.receiveKA l d)
               (t0 , md , ln , keepAlive (MsgKeepAlive c)))) ]─►
    decKAs-src l d (ksRecv1 c)
kas-fire-recv l d c t0 md ln = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src l d (ksHead KA.stClient)))
          (_ , KA.receiveKA l d) (t0 , md , ln , keepAlive (MsgKeepAlive c))
          ≡ just (decKAs-src l d (ksRecv1 c))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stClient → ksDdone1 (fires receiveKA, payload MsgKADone)
kas-fire-ddone : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decKAs-src l d (ksHead KA.stClient)
      KAL.─[ KAL.ev (KAL.evl (KAL.evLabel _ (KA.receiveKA l d)
               (t0 , md , ln , keepAlive MsgKADone))) ]─►
    decKAs-src l d ksDdone1
kas-fire-ddone l d t0 md ln = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src l d (ksHead KA.stClient)))
          (_ , KA.receiveKA l d) (t0 , md , ln , keepAlive MsgKADone)
          ≡ just (decKAs-src l d ksDdone1)
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- head stServer c → ksSil stClient (fires sendKA, response payload c) — Fin-enum
kas-fire-sresp : (l : Link) (d : Dir) (c : _)
  → decKAs-src l d (ksHead (KA.stServer c))
      KAL.─[ KAL.ev (KAL.evl (KAL.evLabel _ (KA.sendKA l d) (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)))) ]─►
    decKAs-src l d (ksSil KA.stClient)
kas-fire-sresp (zero) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (zero) lo (ksHead (KA.stServer c))))
          (_ , KA.sendKA (zero) lo) (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) ≡ just (decKAs-src (zero) lo (ksSil KA.stClient))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
kas-fire-sresp (zero) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (zero) hi (ksHead (KA.stServer c))))
          (_ , KA.sendKA (zero) hi) (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) ≡ just (decKAs-src (zero) hi (ksSil KA.stClient))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
kas-fire-sresp (suc zero) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc zero) lo (ksHead (KA.stServer c))))
          (_ , KA.sendKA (suc zero) lo) (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) ≡ just (decKAs-src (suc zero) lo (ksSil KA.stClient))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
kas-fire-sresp (suc zero) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc zero) hi (ksHead (KA.stServer c))))
          (_ , KA.sendKA (suc zero) hi) (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) ≡ just (decKAs-src (suc zero) hi (ksSil KA.stClient))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
kas-fire-sresp (suc (suc zero)) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc zero)) lo (ksHead (KA.stServer c))))
          (_ , KA.sendKA (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) ≡ just (decKAs-src (suc (suc zero)) lo (ksSil KA.stClient))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
kas-fire-sresp (suc (suc zero)) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc zero)) hi (ksHead (KA.stServer c))))
          (_ , KA.sendKA (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) ≡ just (decKAs-src (suc (suc zero)) hi (ksSil KA.stClient))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
kas-fire-sresp (suc (suc (suc zero))) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc (suc zero))) lo (ksHead (KA.stServer c))))
          (_ , KA.sendKA (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) ≡ just (decKAs-src (suc (suc (suc zero))) lo (ksSil KA.stClient))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl
kas-fire-sresp (suc (suc (suc zero))) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc (suc zero))) hi (ksHead (KA.stServer c))))
          (_ , KA.sendKA (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) ≡ just (decKAs-src (suc (suc (suc zero))) hi (ksSil KA.stClient))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c)) = refl

-- MID ksRecv1 c → ksSil (stServer c) (fires apiKAev recvKACookie, ⊤) — Fin-enum
kas-fire-srecv : (l : Link) (d : Dir) (c : _)
  → decKAs-src l d (ksRecv1 c)
      KAL.─[ KAL.ev (KAL.evl (KAL.evLabel _ (KA.apiKAev l d recvKACookie) c)) ]─►
    decKAs-src l d (ksSil (KA.stServer c))
kas-fire-srecv (zero) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (zero) lo (ksRecv1 c)))
          (_ , KA.apiKAev (zero) lo recvKACookie) c ≡ just (decKAs-src (zero) lo (ksSil (KA.stServer c)))
    o = refl
kas-fire-srecv (zero) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (zero) hi (ksRecv1 c)))
          (_ , KA.apiKAev (zero) hi recvKACookie) c ≡ just (decKAs-src (zero) hi (ksSil (KA.stServer c)))
    o = refl
kas-fire-srecv (suc zero) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc zero) lo (ksRecv1 c)))
          (_ , KA.apiKAev (suc zero) lo recvKACookie) c ≡ just (decKAs-src (suc zero) lo (ksSil (KA.stServer c)))
    o = refl
kas-fire-srecv (suc zero) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc zero) hi (ksRecv1 c)))
          (_ , KA.apiKAev (suc zero) hi recvKACookie) c ≡ just (decKAs-src (suc zero) hi (ksSil (KA.stServer c)))
    o = refl
kas-fire-srecv (suc (suc zero)) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc zero)) lo (ksRecv1 c)))
          (_ , KA.apiKAev (suc (suc zero)) lo recvKACookie) c ≡ just (decKAs-src (suc (suc zero)) lo (ksSil (KA.stServer c)))
    o = refl
kas-fire-srecv (suc (suc zero)) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc zero)) hi (ksRecv1 c)))
          (_ , KA.apiKAev (suc (suc zero)) hi recvKACookie) c ≡ just (decKAs-src (suc (suc zero)) hi (ksSil (KA.stServer c)))
    o = refl
kas-fire-srecv (suc (suc (suc zero))) lo c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc (suc zero))) lo (ksRecv1 c)))
          (_ , KA.apiKAev (suc (suc (suc zero))) lo recvKACookie) c ≡ just (decKAs-src (suc (suc (suc zero))) lo (ksSil (KA.stServer c)))
    o = refl
kas-fire-srecv (suc (suc (suc zero))) hi c = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc (suc zero))) hi (ksRecv1 c)))
          (_ , KA.apiKAev (suc (suc (suc zero))) hi recvKACookie) c ≡ just (decKAs-src (suc (suc (suc zero))) hi (ksSil (KA.stServer c)))
    o = refl

-- MID ksDdone1 → ksSil stDone (fires doneKA, ⊤) — Fin-enum
kas-fire-sddone : (l : Link) (d : Dir)
  → decKAs-src l d ksDdone1
      KAL.─[ KAL.ev (KAL.evl (KAL.evLabel _ (KA.doneKA l d) U.tt)) ]─►
    decKAs-src l d (ksSil KA.stDone)
kas-fire-sddone (zero) lo = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (zero) lo ksDdone1))
          (_ , KA.doneKA (zero) lo) U.tt ≡ just (decKAs-src (zero) lo (ksSil KA.stDone))
    o = refl
kas-fire-sddone (zero) hi = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (zero) hi ksDdone1))
          (_ , KA.doneKA (zero) hi) U.tt ≡ just (decKAs-src (zero) hi (ksSil KA.stDone))
    o = refl
kas-fire-sddone (suc zero) lo = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc zero) lo ksDdone1))
          (_ , KA.doneKA (suc zero) lo) U.tt ≡ just (decKAs-src (suc zero) lo (ksSil KA.stDone))
    o = refl
kas-fire-sddone (suc zero) hi = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc zero) hi ksDdone1))
          (_ , KA.doneKA (suc zero) hi) U.tt ≡ just (decKAs-src (suc zero) hi (ksSil KA.stDone))
    o = refl
kas-fire-sddone (suc (suc zero)) lo = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc zero)) lo ksDdone1))
          (_ , KA.doneKA (suc (suc zero)) lo) U.tt ≡ just (decKAs-src (suc (suc zero)) lo (ksSil KA.stDone))
    o = refl
kas-fire-sddone (suc (suc zero)) hi = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc zero)) hi ksDdone1))
          (_ , KA.doneKA (suc (suc zero)) hi) U.tt ≡ just (decKAs-src (suc (suc zero)) hi (ksSil KA.stDone))
    o = refl
kas-fire-sddone (suc (suc (suc zero))) lo = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc (suc zero))) lo ksDdone1))
          (_ , KA.doneKA (suc (suc (suc zero))) lo) U.tt ≡ just (decKAs-src (suc (suc (suc zero))) lo (ksSil KA.stDone))
    o = refl
kas-fire-sddone (suc (suc (suc zero))) hi = KAL.sVis refl o
  where
    o : vis-ofK (PTree.force (decKAs-src (suc (suc (suc zero))) hi ksDdone1))
          (_ , KA.doneKA (suc (suc (suc zero))) hi) U.tt ≡ just (decKAs-src (suc (suc (suc zero))) hi (ksSil KA.stDone))
    o = refl

------------------------------------------------------------------------
-- KA-CLIENT backward production leaf.
------------------------------------------------------------------------
Tkac : Link → Dir → NS.Table NS.KAcPos
Tkac l d = record { isFin = NS.kaCfin ; nxt = NS.kaCnxt l d }

mkMkac : (l : Link) (d : Dir) (pos′ : KAcPos) {q′ : NS.KAcPos} {M : NetProc}
  → M ≡ tableSpec (Tkac l d) q′ → q′ ≡ coarsenKAc pos′ → M ≡ absKAc l d pos′
mkMkac l d pos′ Meq qeq = trans Meq (cong (tableSpec (Tkac l d)) qeq)

-- STRONG concrete head fire, shared by the leaf's kcHead (0-τ) and kcSil (1-τ).
kac-hstep : (l : Link) (d : Dir) (st : KA.KAState)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → absKAc l d (kcHead st) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M
  → Σ[ pos′ ∈ KAcPos ] (decKAc l d (kcHead st) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► decKAc l d pos′)
      × (M ≡ absKAc l d pos′)
kac-hstep l d KA.stClient {e₁ = KA.apiKAev l' d' sendKAMsg} {a} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stClient)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = kcReq1 a , RFKA.renameMap-ev-fwd (kac-fire-req l d a) , mkMkac l d (kcReq1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
kac-hstep l d KA.stClient {e₁ = KA.apiKAev l' d' sendKADone} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stClient)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = kcDone1 , RFKA.renameMap-ev-fwd (kac-fire-done l d) , mkMkac l d (kcDone1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
kac-hstep l d KA.stClient {e₁ = KA.apiKAev l' d' errCookie} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d KA.stClient {e₁ = KA.apiKAev l' d' recvKACookie} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d KA.stClient {e₁ = KA.sendKA l' d'} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d KA.stClient {e₁ = KA.receiveKA l' d'} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d KA.stClient {e₁ = KA.doneKA l' d'} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- stServer cq (kcAwait cq): fires receiveKA response payload
kac-hstep l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAliveResponse cr)} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = kcSil KA.stClient , RFKA.renameMap-ev-fwd (kac-fire-resp l d cq cr t0 md ln) , mkMkac l d (kcSil KA.stClient) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
kac-hstep l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAlive c)} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive MsgKADone} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d (KA.stServer cq) {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d (KA.stServer cq) {e₁ = KA.sendKA l' d'} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d (KA.stServer cq) {e₁ = KA.apiKAev l' d' m} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kac-hstep l d (KA.stServer cq) {e₁ = KA.doneKA l' d'} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead (KA.stServer cq))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- stDone (kcTerm): terminal, no offer
kac-hstep l d KA.stDone step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcHead KA.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- the CS-CLIENT-style leaf assembly (heads 0-τ, kcSil 1-τ, mids value-gated).
decKAc-ev-prod-abs : (l : Link) (d : Dir) (pos : KAcPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → absKAc l d pos ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M
  → Σ[ pos′ ∈ KAcPos ] (decKAc l d pos ═[ ev (evl (evLabel X (ιKA e₁) a)) ]═► decKAc l d pos′)
      × (M ≡ absKAc l d pos′)
decKAc-ev-prod-abs l d (kcHead st) step with kac-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
decKAc-ev-prod-abs l d (kcSil st) step with kac-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decKAc-sil-step l d st) τ*-refl) f τ*-refl , m
decKAc-ev-prod-abs l d (kcErr1 cq cr ne) step = ⊥-elim (ne refl)

-- kcReq1 c: fires KA.sendKA (payload MsgKeepAlive c)
decKAc-ev-prod-abs l d (kcReq1 c) {e₁ = KA.sendKA l' d'} {a} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcReq1 c)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive (MsgKeepAlive c))
...     | yes refl = kcSil (KA.stServer c) , wev τ*-refl (RFKA.renameMap-ev-fwd (kac-fire-req1 l d c)) τ*-refl , mkMkac l d (kcSil (KA.stServer c)) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-prod-abs l d (kcReq1 c) {e₁ = KA.sendKA l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-prod-abs l d (kcReq1 c) {e₁ = KA.sendKA l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-prod-abs l d (kcReq1 c) {e₁ = KA.receiveKA l' d'} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcReq1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAc-ev-prod-abs l d (kcReq1 c) {e₁ = KA.apiKAev l' d' m} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcReq1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAc-ev-prod-abs l d (kcReq1 c) {e₁ = KA.doneKA l' d'} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc (kcReq1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- kcDone1: fires KA.sendKA (payload MsgKADone)
decKAc-ev-prod-abs l d kcDone1 {e₁ = KA.sendKA l' d'} {a} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc kcDone1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , keepAlive MsgKADone)
...     | yes refl = kcSil KA.stDone , wev τ*-refl (RFKA.renameMap-ev-fwd (kac-fire-done1 l d)) τ*-refl , mkMkac l d (kcSil KA.stDone) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-prod-abs l d kcDone1 {e₁ = KA.sendKA l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-prod-abs l d kcDone1 {e₁ = KA.sendKA l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decKAc-ev-prod-abs l d kcDone1 {e₁ = KA.receiveKA l' d'} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc kcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAc-ev-prod-abs l d kcDone1 {e₁ = KA.apiKAev l' d' m} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc kcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAc-ev-prod-abs l d kcDone1 {e₁ = KA.doneKA l' d'} step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc kcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- kcTermE1: terminal (√ after errCookie), no offer
decKAc-ev-prod-abs l d kcTermE1 step
  with tableSpec-ev-inv (Tkac l d) (coarsenKAc kcTermE1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

------------------------------------------------------------------------
-- KA-SERVER backward production leaf.
------------------------------------------------------------------------
Tkas : Link → Dir → NS.Table NS.KAsPos
Tkas l d = record { isFin = NS.kaSfin ; nxt = NS.kaSnxt l d }

mkMkas : (l : Link) (d : Dir) (pos′ : KAsPos) {q′ : NS.KAsPos} {M : NetProc}
  → M ≡ tableSpec (Tkas l d) q′ → q′ ≡ coarsenKAs pos′ → M ≡ absKAs l d pos′
mkMkas l d pos′ Meq qeq = trans Meq (cong (tableSpec (Tkas l d)) qeq)

kas-hstep : (l : Link) (d : Dir) (st : KA.KAState)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → absKAs l d (ksHead st) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M
  → Σ[ pos′ ∈ KAsPos ] (decKAs l d (ksHead st) ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► decKAs l d pos′)
      × (M ≡ absKAs l d pos′)
-- ksHead stClient (ksClient): receives MsgKeepAlive c (→ksRecv1 c) / MsgKADone (→ksDdone1)
kas-hstep l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive (MsgKeepAlive c)} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ksRecv1 c , RFKA.renameMap-ev-fwd (kas-fire-recv l d c t0 md ln) , mkMkas l d (ksRecv1 c) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
kas-hstep l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = t0 , md , ln , keepAlive MsgKADone} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ksDdone1 , RFKA.renameMap-ev-fwd (kas-fire-ddone l d t0 md ln) , mkMkas l d ksDdone1 Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
kas-hstep l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , keepAlive (MsgKeepAliveResponse c)} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , txSubmission x} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep l d KA.stClient {e₁ = KA.receiveKA l' d'} {a = _ , _ , _ , leiosFetch x} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep l d KA.stClient {e₁ = KA.sendKA l' d'} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep l d KA.stClient {e₁ = KA.apiKAev l' d' m} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep l d KA.stClient {e₁ = KA.doneKA l' d'} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stClient)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- ksHead (stServer c) (ksResp c): sends response payload → ksSil stClient
kas-hstep l d (KA.stServer c) {e₁ = KA.sendKA l' d'} {a} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead (KA.stServer c))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , keepAlive (MsgKeepAliveResponse c))
...     | yes refl = ksSil KA.stClient , RFKA.renameMap-ev-fwd (kas-fire-sresp l d c) , mkMkas l d (ksSil KA.stClient) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
kas-hstep l d (KA.stServer c) {e₁ = KA.sendKA l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
kas-hstep l d (KA.stServer c) {e₁ = KA.sendKA l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
kas-hstep l d (KA.stServer c) {e₁ = KA.receiveKA l' d'} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead (KA.stServer c))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep l d (KA.stServer c) {e₁ = KA.apiKAev l' d' m} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead (KA.stServer c))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
kas-hstep l d (KA.stServer c) {e₁ = KA.doneKA l' d'} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead (KA.stServer c))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- ksHead stDone (ksTerm): terminal, no offer
kas-hstep l d KA.stDone step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksHead KA.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

decKAs-ev-prod-abs : (l : Link) (d : Dir) (pos : KAsPos)
    {X : Set 0ℓ} {e₁ : KA.KAEv X} {a : X} {M : NetProc}
  → absKAs l d pos ─[ ev (evl (evLabel X (ιKA e₁) a)) ]─► M
  → Σ[ pos′ ∈ KAsPos ] (decKAs l d pos ═[ ev (evl (evLabel X (ιKA e₁) a)) ]═► decKAs l d pos′)
      × (M ≡ absKAs l d pos′)
decKAs-ev-prod-abs l d (ksHead st) step with kas-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
decKAs-ev-prod-abs l d (ksSil st) step with kas-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decKAs-sil-step l d st) τ*-refl) f τ*-refl , m

-- ksRecv1 c: fires apiKAev recvKACookie (⊤ value) → ksSil (stServer c)
decKAs-ev-prod-abs l d (ksRecv1 c) {e₁ = KA.apiKAev l' d' recvKACookie} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksRecv1 c)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ksSil (KA.stServer c) , wev τ*-refl (RFKA.renameMap-ev-fwd (kas-fire-srecv l d c)) τ*-refl , mkMkas l d (ksSil (KA.stServer c)) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
decKAs-ev-prod-abs l d (ksRecv1 c) {e₁ = KA.apiKAev l' d' sendKAMsg} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksRecv1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAs-ev-prod-abs l d (ksRecv1 c) {e₁ = KA.apiKAev l' d' sendKADone} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksRecv1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAs-ev-prod-abs l d (ksRecv1 c) {e₁ = KA.apiKAev l' d' errCookie} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksRecv1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAs-ev-prod-abs l d (ksRecv1 c) {e₁ = KA.sendKA l' d'} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksRecv1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAs-ev-prod-abs l d (ksRecv1 c) {e₁ = KA.receiveKA l' d'} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksRecv1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAs-ev-prod-abs l d (ksRecv1 c) {e₁ = KA.doneKA l' d'} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs (ksRecv1 c)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

-- ksDdone1: fires doneKA (⊤) → ksSil stDone
decKAs-ev-prod-abs l d ksDdone1 {e₁ = KA.doneKA l' d'} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs ksDdone1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = ksSil KA.stDone , wev τ*-refl (RFKA.renameMap-ev-fwd (kas-fire-sddone l d)) τ*-refl , mkMkas l d (ksSil KA.stDone) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
decKAs-ev-prod-abs l d ksDdone1 {e₁ = KA.sendKA l' d'} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs ksDdone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAs-ev-prod-abs l d ksDdone1 {e₁ = KA.receiveKA l' d'} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs ksDdone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decKAs-ev-prod-abs l d ksDdone1 {e₁ = KA.apiKAev l' d' m} step
  with tableSpec-ev-inv (Tkas l d) (coarsenKAs ksDdone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- KA-SECTION-END

-- TS-SECTION-BEGIN
------------------------------------------------------------------------
-- INERT PEER TxSubmission (TS) — backward production leaves (role-inverted).
-- KA has no sil-steps in SysStep; likewise TS — defined here.
------------------------------------------------------------------------
decTSc-sil-step : (l : Link) (d : Dir) (st : TS.TSState)
  → decTSc l d (tcSil st) ─[ τ ]─► decTSc l d (tcHead st)
decTSc-sil-step l d st = sSil refl
decTSs-sil-step : (l : Link) (d : Dir) (st : TS.TSState)
  → decTSs l d (tsSil st) ─[ τ ]─► decTSs l d (tsHead st)
decTSs-sil-step l d st = sSil refl

-- CLIENT head wire-send tcInit → tcSil stIdle (sendTS MsgTSInit) — Fin-enum
tc-fire-init : (l : Link) (d : Dir)
  → decTSc-src l d (tcHead TS.stInit)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.sendTS l d) (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit))) ]─►
    decTSc-src l d (tcSil TS.stIdle)
tc-fire-init (zero) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) lo (tcHead TS.stInit)))
          (_ , TS.sendTS (zero) lo) (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) ≡ just (decTSc-src (zero) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) = refl
tc-fire-init (zero) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) hi (tcHead TS.stInit)))
          (_ , TS.sendTS (zero) hi) (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) ≡ just (decTSc-src (zero) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) = refl
tc-fire-init (suc zero) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) lo (tcHead TS.stInit)))
          (_ , TS.sendTS (suc zero) lo) (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) ≡ just (decTSc-src (suc zero) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) = refl
tc-fire-init (suc zero) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) hi (tcHead TS.stInit)))
          (_ , TS.sendTS (suc zero) hi) (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) ≡ just (decTSc-src (suc zero) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) = refl
tc-fire-init (suc (suc zero)) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) lo (tcHead TS.stInit)))
          (_ , TS.sendTS (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) ≡ just (decTSc-src (suc (suc zero)) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) = refl
tc-fire-init (suc (suc zero)) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) hi (tcHead TS.stInit)))
          (_ , TS.sendTS (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) ≡ just (decTSc-src (suc (suc zero)) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) = refl
tc-fire-init (suc (suc (suc zero))) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) lo (tcHead TS.stInit)))
          (_ , TS.sendTS (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) ≡ just (decTSc-src (suc (suc (suc zero))) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) = refl
tc-fire-init (suc (suc (suc zero))) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) hi (tcHead TS.stInit)))
          (_ , TS.sendTS (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) ≡ just (decTSc-src (suc (suc (suc zero))) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit) = refl

-- CLIENT head receives (stIdle) — l,d gated
tc-fire-reqB : (l : Link) (d : Dir) (aa rr : ℕ) (t0 : _) (md : _) (ln : _)
  → decTSc-src l d (tcHead TS.stIdle)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSRequestTxIds Blocking aa rr)))) ]─►
    decTSc-src l d (tcReqIdsB1 aa rr)
tc-fire-reqB l d aa rr t0 md ln = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src l d (tcHead TS.stIdle)))
          (_ , TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSRequestTxIds Blocking aa rr)) ≡ just (decTSc-src l d (tcReqIdsB1 aa rr))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
tc-fire-reqNB : (l : Link) (d : Dir) (aa rr : ℕ) (t0 : _) (md : _) (ln : _)
  → decTSc-src l d (tcHead TS.stIdle)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSRequestTxIds NonBlocking aa rr)))) ]─►
    decTSc-src l d (tcReqIdsNB1 aa rr)
tc-fire-reqNB l d aa rr t0 md ln = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src l d (tcHead TS.stIdle)))
          (_ , TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSRequestTxIds NonBlocking aa rr)) ≡ just (decTSc-src l d (tcReqIdsNB1 aa rr))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
tc-fire-reqTxs : (l : Link) (d : Dir) (ids : _) (t0 : _) (md : _) (ln : _)
  → decTSc-src l d (tcHead TS.stIdle)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSRequestTxs ids)))) ]─►
    decTSc-src l d (tcReqTxs1 ids)
tc-fire-reqTxs l d ids t0 md ln = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src l d (tcHead TS.stIdle)))
          (_ , TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSRequestTxs ids)) ≡ just (decTSc-src l d (tcReqTxs1 ids))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- CLIENT head api-sends — l,d gated (pchoice, value bound)
tc-fire-repB : (l : Link) (d : Dir) (ids : _)
  → decTSc-src l d (tcHead TS.stTxIdsBlocking)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.apiTSev l d sendTSReplyTxIds) ids)) ]─►
    decTSc-src l d (tcRepB1 ids)
tc-fire-repB l d ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src l d (tcHead TS.stTxIdsBlocking)))
          (_ , TS.apiTSev l d sendTSReplyTxIds) ids ≡ just (decTSc-src l d (tcRepB1 ids))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
tc-fire-cdone : (l : Link) (d : Dir)
  → decTSc-src l d (tcHead TS.stTxIdsBlocking)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.apiTSev l d sendTSDone) U.tt)) ]─►
    decTSc-src l d tcDone1
tc-fire-cdone l d = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src l d (tcHead TS.stTxIdsBlocking)))
          (_ , TS.apiTSev l d sendTSDone) U.tt ≡ just (decTSc-src l d (tcDone1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
tc-fire-repNB : (l : Link) (d : Dir) (ids : _)
  → decTSc-src l d (tcHead TS.stTxIdsNonBlocking)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.apiTSev l d sendTSReplyTxIds) ids)) ]─►
    decTSc-src l d (tcRepNB1 ids)
tc-fire-repNB l d ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src l d (tcHead TS.stTxIdsNonBlocking)))
          (_ , TS.apiTSev l d sendTSReplyTxIds) ids ≡ just (decTSc-src l d (tcRepNB1 ids))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
tc-fire-repTxs : (l : Link) (d : Dir) (txs : _)
  → decTSc-src l d (tcHead TS.stTxs)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.apiTSev l d sendTSReplyTxs) txs)) ]─►
    decTSc-src l d (tcRepTxs1 txs)
tc-fire-repTxs l d txs = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src l d (tcHead TS.stTxs)))
          (_ , TS.apiTSev l d sendTSReplyTxs) txs ≡ just (decTSc-src l d (tcRepTxs1 txs))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- CLIENT api-emit mids — Fin-enum + value gate (source-baked instance)
tc-fire-ari1B : (l : Link) (d : Dir) (aa rr : ℕ)
  → decTSc-src l d (tcReqIdsB1 aa rr)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.apiTSev l d recvTSRequestTxIds) (Blocking , aa , rr))) ]─►
    decTSc-src l d (tcSil TS.stTxIdsBlocking)
tc-fire-ari1B (zero) lo aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) lo (tcReqIdsB1 aa rr)))
          (_ , TS.apiTSev (zero) lo recvTSRequestTxIds) (Blocking , aa , rr) ≡ just (decTSc-src (zero) lo (tcSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (Blocking , aa , rr) = refl
tc-fire-ari1B (zero) hi aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) hi (tcReqIdsB1 aa rr)))
          (_ , TS.apiTSev (zero) hi recvTSRequestTxIds) (Blocking , aa , rr) ≡ just (decTSc-src (zero) hi (tcSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (Blocking , aa , rr) = refl
tc-fire-ari1B (suc zero) lo aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) lo (tcReqIdsB1 aa rr)))
          (_ , TS.apiTSev (suc zero) lo recvTSRequestTxIds) (Blocking , aa , rr) ≡ just (decTSc-src (suc zero) lo (tcSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (Blocking , aa , rr) = refl
tc-fire-ari1B (suc zero) hi aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) hi (tcReqIdsB1 aa rr)))
          (_ , TS.apiTSev (suc zero) hi recvTSRequestTxIds) (Blocking , aa , rr) ≡ just (decTSc-src (suc zero) hi (tcSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (Blocking , aa , rr) = refl
tc-fire-ari1B (suc (suc zero)) lo aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) lo (tcReqIdsB1 aa rr)))
          (_ , TS.apiTSev (suc (suc zero)) lo recvTSRequestTxIds) (Blocking , aa , rr) ≡ just (decTSc-src (suc (suc zero)) lo (tcSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (Blocking , aa , rr) = refl
tc-fire-ari1B (suc (suc zero)) hi aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) hi (tcReqIdsB1 aa rr)))
          (_ , TS.apiTSev (suc (suc zero)) hi recvTSRequestTxIds) (Blocking , aa , rr) ≡ just (decTSc-src (suc (suc zero)) hi (tcSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (Blocking , aa , rr) = refl
tc-fire-ari1B (suc (suc (suc zero))) lo aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) lo (tcReqIdsB1 aa rr)))
          (_ , TS.apiTSev (suc (suc (suc zero))) lo recvTSRequestTxIds) (Blocking , aa , rr) ≡ just (decTSc-src (suc (suc (suc zero))) lo (tcSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (Blocking , aa , rr) = refl
tc-fire-ari1B (suc (suc (suc zero))) hi aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) hi (tcReqIdsB1 aa rr)))
          (_ , TS.apiTSev (suc (suc (suc zero))) hi recvTSRequestTxIds) (Blocking , aa , rr) ≡ just (decTSc-src (suc (suc (suc zero))) hi (tcSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (Blocking , aa , rr) = refl
tc-fire-ari1NB : (l : Link) (d : Dir) (aa rr : ℕ)
  → decTSc-src l d (tcReqIdsNB1 aa rr)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.apiTSev l d recvTSRequestTxIds) (NonBlocking , aa , rr))) ]─►
    decTSc-src l d (tcSil TS.stTxIdsNonBlocking)
tc-fire-ari1NB (zero) lo aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) lo (tcReqIdsNB1 aa rr)))
          (_ , TS.apiTSev (zero) lo recvTSRequestTxIds) (NonBlocking , aa , rr) ≡ just (decTSc-src (zero) lo (tcSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (NonBlocking , aa , rr) = refl
tc-fire-ari1NB (zero) hi aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) hi (tcReqIdsNB1 aa rr)))
          (_ , TS.apiTSev (zero) hi recvTSRequestTxIds) (NonBlocking , aa , rr) ≡ just (decTSc-src (zero) hi (tcSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (NonBlocking , aa , rr) = refl
tc-fire-ari1NB (suc zero) lo aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) lo (tcReqIdsNB1 aa rr)))
          (_ , TS.apiTSev (suc zero) lo recvTSRequestTxIds) (NonBlocking , aa , rr) ≡ just (decTSc-src (suc zero) lo (tcSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (NonBlocking , aa , rr) = refl
tc-fire-ari1NB (suc zero) hi aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) hi (tcReqIdsNB1 aa rr)))
          (_ , TS.apiTSev (suc zero) hi recvTSRequestTxIds) (NonBlocking , aa , rr) ≡ just (decTSc-src (suc zero) hi (tcSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (NonBlocking , aa , rr) = refl
tc-fire-ari1NB (suc (suc zero)) lo aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) lo (tcReqIdsNB1 aa rr)))
          (_ , TS.apiTSev (suc (suc zero)) lo recvTSRequestTxIds) (NonBlocking , aa , rr) ≡ just (decTSc-src (suc (suc zero)) lo (tcSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (NonBlocking , aa , rr) = refl
tc-fire-ari1NB (suc (suc zero)) hi aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) hi (tcReqIdsNB1 aa rr)))
          (_ , TS.apiTSev (suc (suc zero)) hi recvTSRequestTxIds) (NonBlocking , aa , rr) ≡ just (decTSc-src (suc (suc zero)) hi (tcSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (NonBlocking , aa , rr) = refl
tc-fire-ari1NB (suc (suc (suc zero))) lo aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) lo (tcReqIdsNB1 aa rr)))
          (_ , TS.apiTSev (suc (suc (suc zero))) lo recvTSRequestTxIds) (NonBlocking , aa , rr) ≡ just (decTSc-src (suc (suc (suc zero))) lo (tcSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (NonBlocking , aa , rr) = refl
tc-fire-ari1NB (suc (suc (suc zero))) hi aa rr = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) hi (tcReqIdsNB1 aa rr)))
          (_ , TS.apiTSev (suc (suc (suc zero))) hi recvTSRequestTxIds) (NonBlocking , aa , rr) ≡ just (decTSc-src (suc (suc (suc zero))) hi (tcSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ (NonBlocking , aa , rr) = refl
tc-fire-art1 : (l : Link) (d : Dir) (ids : _)
  → decTSc-src l d (tcReqTxs1 ids)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.apiTSev l d recvTSRequestTxs) ids)) ]─►
    decTSc-src l d (tcSil TS.stTxs)
tc-fire-art1 (zero) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) lo (tcReqTxs1 ids)))
          (_ , TS.apiTSev (zero) lo recvTSRequestTxs) ids ≡ just (decTSc-src (zero) lo (tcSil TS.stTxs))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-ListTxid ⦄ ids = refl
tc-fire-art1 (zero) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) hi (tcReqTxs1 ids)))
          (_ , TS.apiTSev (zero) hi recvTSRequestTxs) ids ≡ just (decTSc-src (zero) hi (tcSil TS.stTxs))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-ListTxid ⦄ ids = refl
tc-fire-art1 (suc zero) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) lo (tcReqTxs1 ids)))
          (_ , TS.apiTSev (suc zero) lo recvTSRequestTxs) ids ≡ just (decTSc-src (suc zero) lo (tcSil TS.stTxs))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-ListTxid ⦄ ids = refl
tc-fire-art1 (suc zero) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) hi (tcReqTxs1 ids)))
          (_ , TS.apiTSev (suc zero) hi recvTSRequestTxs) ids ≡ just (decTSc-src (suc zero) hi (tcSil TS.stTxs))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-ListTxid ⦄ ids = refl
tc-fire-art1 (suc (suc zero)) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) lo (tcReqTxs1 ids)))
          (_ , TS.apiTSev (suc (suc zero)) lo recvTSRequestTxs) ids ≡ just (decTSc-src (suc (suc zero)) lo (tcSil TS.stTxs))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-ListTxid ⦄ ids = refl
tc-fire-art1 (suc (suc zero)) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) hi (tcReqTxs1 ids)))
          (_ , TS.apiTSev (suc (suc zero)) hi recvTSRequestTxs) ids ≡ just (decTSc-src (suc (suc zero)) hi (tcSil TS.stTxs))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-ListTxid ⦄ ids = refl
tc-fire-art1 (suc (suc (suc zero))) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) lo (tcReqTxs1 ids)))
          (_ , TS.apiTSev (suc (suc (suc zero))) lo recvTSRequestTxs) ids ≡ just (decTSc-src (suc (suc (suc zero))) lo (tcSil TS.stTxs))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-ListTxid ⦄ ids = refl
tc-fire-art1 (suc (suc (suc zero))) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) hi (tcReqTxs1 ids)))
          (_ , TS.apiTSev (suc (suc (suc zero))) hi recvTSRequestTxs) ids ≡ just (decTSc-src (suc (suc (suc zero))) hi (tcSil TS.stTxs))
    o rewrite ≟-yes-refl ⦃ TS.DecEq-ListTxid ⦄ ids = refl

-- CLIENT wire-send mids — Fin-enum + Payload gate
tc-fire-wri1B : (l : Link) (d : Dir) (ids : _)
  → decTSc-src l d (tcRepB1 ids)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.sendTS l d) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)))) ]─►
    decTSc-src l d (tcSil TS.stIdle)
tc-fire-wri1B (zero) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) lo (tcRepB1 ids)))
          (_ , TS.sendTS (zero) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (zero) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1B (zero) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) hi (tcRepB1 ids)))
          (_ , TS.sendTS (zero) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (zero) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1B (suc zero) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) lo (tcRepB1 ids)))
          (_ , TS.sendTS (suc zero) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc zero) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1B (suc zero) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) hi (tcRepB1 ids)))
          (_ , TS.sendTS (suc zero) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc zero) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1B (suc (suc zero)) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) lo (tcRepB1 ids)))
          (_ , TS.sendTS (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc (suc zero)) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1B (suc (suc zero)) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) hi (tcRepB1 ids)))
          (_ , TS.sendTS (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc (suc zero)) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1B (suc (suc (suc zero))) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) lo (tcRepB1 ids)))
          (_ , TS.sendTS (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc (suc (suc zero))) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1B (suc (suc (suc zero))) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) hi (tcRepB1 ids)))
          (_ , TS.sendTS (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc (suc (suc zero))) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wdone1 : (l : Link) (d : Dir)
  → decTSc-src l d (tcDone1)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.sendTS l d) (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone))) ]─►
    decTSc-src l d (tcSil TS.stDone)
tc-fire-wdone1 (zero) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) lo (tcDone1)))
          (_ , TS.sendTS (zero) lo) (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) ≡ just (decTSc-src (zero) lo (tcSil TS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) = refl
tc-fire-wdone1 (zero) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) hi (tcDone1)))
          (_ , TS.sendTS (zero) hi) (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) ≡ just (decTSc-src (zero) hi (tcSil TS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) = refl
tc-fire-wdone1 (suc zero) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) lo (tcDone1)))
          (_ , TS.sendTS (suc zero) lo) (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) ≡ just (decTSc-src (suc zero) lo (tcSil TS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) = refl
tc-fire-wdone1 (suc zero) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) hi (tcDone1)))
          (_ , TS.sendTS (suc zero) hi) (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) ≡ just (decTSc-src (suc zero) hi (tcSil TS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) = refl
tc-fire-wdone1 (suc (suc zero)) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) lo (tcDone1)))
          (_ , TS.sendTS (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) ≡ just (decTSc-src (suc (suc zero)) lo (tcSil TS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) = refl
tc-fire-wdone1 (suc (suc zero)) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) hi (tcDone1)))
          (_ , TS.sendTS (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) ≡ just (decTSc-src (suc (suc zero)) hi (tcSil TS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) = refl
tc-fire-wdone1 (suc (suc (suc zero))) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) lo (tcDone1)))
          (_ , TS.sendTS (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) ≡ just (decTSc-src (suc (suc (suc zero))) lo (tcSil TS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) = refl
tc-fire-wdone1 (suc (suc (suc zero))) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) hi (tcDone1)))
          (_ , TS.sendTS (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) ≡ just (decTSc-src (suc (suc (suc zero))) hi (tcSil TS.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone) = refl
tc-fire-wri1NB : (l : Link) (d : Dir) (ids : _)
  → decTSc-src l d (tcRepNB1 ids)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.sendTS l d) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)))) ]─►
    decTSc-src l d (tcSil TS.stIdle)
tc-fire-wri1NB (zero) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) lo (tcRepNB1 ids)))
          (_ , TS.sendTS (zero) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (zero) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1NB (zero) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) hi (tcRepNB1 ids)))
          (_ , TS.sendTS (zero) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (zero) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1NB (suc zero) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) lo (tcRepNB1 ids)))
          (_ , TS.sendTS (suc zero) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc zero) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1NB (suc zero) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) hi (tcRepNB1 ids)))
          (_ , TS.sendTS (suc zero) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc zero) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1NB (suc (suc zero)) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) lo (tcRepNB1 ids)))
          (_ , TS.sendTS (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc (suc zero)) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1NB (suc (suc zero)) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) hi (tcRepNB1 ids)))
          (_ , TS.sendTS (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc (suc zero)) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1NB (suc (suc (suc zero))) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) lo (tcRepNB1 ids)))
          (_ , TS.sendTS (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc (suc (suc zero))) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wri1NB (suc (suc (suc zero))) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) hi (tcRepNB1 ids)))
          (_ , TS.sendTS (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSc-src (suc (suc (suc zero))) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids)) = refl
tc-fire-wrt1 : (l : Link) (d : Dir) (txs : _)
  → decTSc-src l d (tcRepTxs1 txs)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.sendTS l d) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)))) ]─►
    decTSc-src l d (tcSil TS.stIdle)
tc-fire-wrt1 (zero) lo txs = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) lo (tcRepTxs1 txs)))
          (_ , TS.sendTS (zero) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) ≡ just (decTSc-src (zero) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) = refl
tc-fire-wrt1 (zero) hi txs = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (zero) hi (tcRepTxs1 txs)))
          (_ , TS.sendTS (zero) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) ≡ just (decTSc-src (zero) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) = refl
tc-fire-wrt1 (suc zero) lo txs = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) lo (tcRepTxs1 txs)))
          (_ , TS.sendTS (suc zero) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) ≡ just (decTSc-src (suc zero) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) = refl
tc-fire-wrt1 (suc zero) hi txs = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc zero) hi (tcRepTxs1 txs)))
          (_ , TS.sendTS (suc zero) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) ≡ just (decTSc-src (suc zero) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) = refl
tc-fire-wrt1 (suc (suc zero)) lo txs = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) lo (tcRepTxs1 txs)))
          (_ , TS.sendTS (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) ≡ just (decTSc-src (suc (suc zero)) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) = refl
tc-fire-wrt1 (suc (suc zero)) hi txs = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc zero)) hi (tcRepTxs1 txs)))
          (_ , TS.sendTS (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) ≡ just (decTSc-src (suc (suc zero)) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) = refl
tc-fire-wrt1 (suc (suc (suc zero))) lo txs = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) lo (tcRepTxs1 txs)))
          (_ , TS.sendTS (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) ≡ just (decTSc-src (suc (suc (suc zero))) lo (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) = refl
tc-fire-wrt1 (suc (suc (suc zero))) hi txs = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSc-src (suc (suc (suc zero))) hi (tcRepTxs1 txs)))
          (_ , TS.sendTS (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) ≡ just (decTSc-src (suc (suc (suc zero))) hi (tcSil TS.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs)) = refl

-- SERVER head receive (stInit) → tsSil stIdle — l,d gated
ts-fire-init : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decTSs-src l d (tsHead TS.stInit)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.receiveTS l d) (t0 , md , ln , txSubmission MsgTSInit))) ]─►
    decTSs-src l d (tsSil TS.stIdle)
ts-fire-init l d t0 md ln = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src l d (tsHead TS.stInit)))
          (_ , TS.receiveTS l d) (t0 , md , ln , txSubmission MsgTSInit) ≡ just (decTSs-src l d (tsSil TS.stIdle))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- SERVER head api-sends (stIdle) — l,d gated
ts-fire-reqB : (l : Link) (d : Dir) (ar : _)
  → decTSs-src l d (tsHead TS.stIdle)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.apiTSev l d sendTSRequestTxIdsBlocking) ar)) ]─►
    decTSs-src l d (tsReqB1 ar)
ts-fire-reqB l d ar = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src l d (tsHead TS.stIdle)))
          (_ , TS.apiTSev l d sendTSRequestTxIdsBlocking) ar ≡ just (decTSs-src l d (tsReqB1 ar))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ts-fire-reqNB : (l : Link) (d : Dir) (ar : _)
  → decTSs-src l d (tsHead TS.stIdle)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.apiTSev l d sendTSRequestTxIdsPipelined) ar)) ]─►
    decTSs-src l d (tsReqNB1 ar)
ts-fire-reqNB l d ar = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src l d (tsHead TS.stIdle)))
          (_ , TS.apiTSev l d sendTSRequestTxIdsPipelined) ar ≡ just (decTSs-src l d (tsReqNB1 ar))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ts-fire-reqTxs : (l : Link) (d : Dir) (ids : _)
  → decTSs-src l d (tsHead TS.stIdle)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.apiTSev l d sendTSRequestTxsPipelined) ids)) ]─►
    decTSs-src l d (tsReqTxs1 ids)
ts-fire-reqTxs l d ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src l d (tsHead TS.stIdle)))
          (_ , TS.apiTSev l d sendTSRequestTxsPipelined) ids ≡ just (decTSs-src l d (tsReqTxs1 ids))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- SERVER head receives (stTxIdsBlocking/NonBlocking/Txs) — l,d gated
ts-fire-blkReply : (l : Link) (d : Dir) (ids : _) (t0 : _) (md : _) (ln : _)
  → decTSs-src l d (tsHead TS.stTxIdsBlocking)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)))) ]─►
    decTSs-src l d (tsSil TS.stIdle)
ts-fire-blkReply l d ids t0 md ln = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src l d (tsHead TS.stTxIdsBlocking)))
          (_ , TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSs-src l d (tsSil TS.stIdle))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ts-fire-blkDone : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decTSs-src l d (tsHead TS.stTxIdsBlocking)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.receiveTS l d) (t0 , md , ln , txSubmission MsgTSDone))) ]─►
    decTSs-src l d tsDone1
ts-fire-blkDone l d t0 md ln = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src l d (tsHead TS.stTxIdsBlocking)))
          (_ , TS.receiveTS l d) (t0 , md , ln , txSubmission MsgTSDone) ≡ just (decTSs-src l d (tsDone1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ts-fire-nblReply : (l : Link) (d : Dir) (ids : _) (t0 : _) (md : _) (ln : _)
  → decTSs-src l d (tsHead TS.stTxIdsNonBlocking)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)))) ]─►
    decTSs-src l d (tsSil TS.stIdle)
ts-fire-nblReply l d ids t0 md ln = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src l d (tsHead TS.stTxIdsNonBlocking)))
          (_ , TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)) ≡ just (decTSs-src l d (tsSil TS.stIdle))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
ts-fire-txsReply : (l : Link) (d : Dir) (txs : _) (t0 : _) (md : _) (ln : _)
  → decTSs-src l d (tsHead TS.stTxs)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSReplyTxs txs)))) ]─►
    decTSs-src l d (tsSil TS.stIdle)
ts-fire-txsReply l d txs t0 md ln = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src l d (tsHead TS.stTxs)))
          (_ , TS.receiveTS l d) (t0 , md , ln , txSubmission (MsgTSReplyTxs txs)) ≡ just (decTSs-src l d (tsSil TS.stIdle))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- SERVER done mid tsDone1 → tsSil stDone (doneTS, ⊤) — Fin-enum
ts-fire-sddone : (l : Link) (d : Dir)
  → decTSs-src l d tsDone1
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.doneTS l d) U.tt)) ]─►
    decTSs-src l d (tsSil TS.stDone)
ts-fire-sddone (zero) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (zero) lo tsDone1))
          (_ , TS.doneTS (zero) lo) U.tt ≡ just (decTSs-src (zero) lo (tsSil TS.stDone))
    o = refl
ts-fire-sddone (zero) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (zero) hi tsDone1))
          (_ , TS.doneTS (zero) hi) U.tt ≡ just (decTSs-src (zero) hi (tsSil TS.stDone))
    o = refl
ts-fire-sddone (suc zero) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc zero) lo tsDone1))
          (_ , TS.doneTS (suc zero) lo) U.tt ≡ just (decTSs-src (suc zero) lo (tsSil TS.stDone))
    o = refl
ts-fire-sddone (suc zero) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc zero) hi tsDone1))
          (_ , TS.doneTS (suc zero) hi) U.tt ≡ just (decTSs-src (suc zero) hi (tsSil TS.stDone))
    o = refl
ts-fire-sddone (suc (suc zero)) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc zero)) lo tsDone1))
          (_ , TS.doneTS (suc (suc zero)) lo) U.tt ≡ just (decTSs-src (suc (suc zero)) lo (tsSil TS.stDone))
    o = refl
ts-fire-sddone (suc (suc zero)) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc zero)) hi tsDone1))
          (_ , TS.doneTS (suc (suc zero)) hi) U.tt ≡ just (decTSs-src (suc (suc zero)) hi (tsSil TS.stDone))
    o = refl
ts-fire-sddone (suc (suc (suc zero))) lo = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc (suc zero))) lo tsDone1))
          (_ , TS.doneTS (suc (suc (suc zero))) lo) U.tt ≡ just (decTSs-src (suc (suc (suc zero))) lo (tsSil TS.stDone))
    o = refl
ts-fire-sddone (suc (suc (suc zero))) hi = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc (suc zero))) hi tsDone1))
          (_ , TS.doneTS (suc (suc (suc zero))) hi) U.tt ≡ just (decTSs-src (suc (suc (suc zero))) hi (tsSil TS.stDone))
    o = refl

-- SERVER wire-send mids — Fin-enum + Payload gate
ts-fire-wib1 : (l : Link) (d : Dir) (a r : ℕ)
  → decTSs-src l d (tsReqB1 (a , r))
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.sendTS l d) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)))) ]─►
    decTSs-src l d (tsSil TS.stTxIdsBlocking)
ts-fire-wib1 (zero) lo a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (zero) lo (tsReqB1 (a , r))))
          (_ , TS.sendTS (zero) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ just (decTSs-src (zero) lo (tsSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) = refl
ts-fire-wib1 (zero) hi a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (zero) hi (tsReqB1 (a , r))))
          (_ , TS.sendTS (zero) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ just (decTSs-src (zero) hi (tsSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) = refl
ts-fire-wib1 (suc zero) lo a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc zero) lo (tsReqB1 (a , r))))
          (_ , TS.sendTS (suc zero) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ just (decTSs-src (suc zero) lo (tsSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) = refl
ts-fire-wib1 (suc zero) hi a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc zero) hi (tsReqB1 (a , r))))
          (_ , TS.sendTS (suc zero) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ just (decTSs-src (suc zero) hi (tsSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) = refl
ts-fire-wib1 (suc (suc zero)) lo a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc zero)) lo (tsReqB1 (a , r))))
          (_ , TS.sendTS (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ just (decTSs-src (suc (suc zero)) lo (tsSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) = refl
ts-fire-wib1 (suc (suc zero)) hi a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc zero)) hi (tsReqB1 (a , r))))
          (_ , TS.sendTS (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ just (decTSs-src (suc (suc zero)) hi (tsSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) = refl
ts-fire-wib1 (suc (suc (suc zero))) lo a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc (suc zero))) lo (tsReqB1 (a , r))))
          (_ , TS.sendTS (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ just (decTSs-src (suc (suc (suc zero))) lo (tsSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) = refl
ts-fire-wib1 (suc (suc (suc zero))) hi a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc (suc zero))) hi (tsReqB1 (a , r))))
          (_ , TS.sendTS (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) ≡ just (decTSs-src (suc (suc (suc zero))) hi (tsSil TS.stTxIdsBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking a r)) = refl
ts-fire-win1 : (l : Link) (d : Dir) (a r : ℕ)
  → decTSs-src l d (tsReqNB1 (a , r))
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.sendTS l d) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)))) ]─►
    decTSs-src l d (tsSil TS.stTxIdsNonBlocking)
ts-fire-win1 (zero) lo a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (zero) lo (tsReqNB1 (a , r))))
          (_ , TS.sendTS (zero) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ just (decTSs-src (zero) lo (tsSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) = refl
ts-fire-win1 (zero) hi a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (zero) hi (tsReqNB1 (a , r))))
          (_ , TS.sendTS (zero) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ just (decTSs-src (zero) hi (tsSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) = refl
ts-fire-win1 (suc zero) lo a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc zero) lo (tsReqNB1 (a , r))))
          (_ , TS.sendTS (suc zero) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ just (decTSs-src (suc zero) lo (tsSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) = refl
ts-fire-win1 (suc zero) hi a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc zero) hi (tsReqNB1 (a , r))))
          (_ , TS.sendTS (suc zero) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ just (decTSs-src (suc zero) hi (tsSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) = refl
ts-fire-win1 (suc (suc zero)) lo a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc zero)) lo (tsReqNB1 (a , r))))
          (_ , TS.sendTS (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ just (decTSs-src (suc (suc zero)) lo (tsSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) = refl
ts-fire-win1 (suc (suc zero)) hi a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc zero)) hi (tsReqNB1 (a , r))))
          (_ , TS.sendTS (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ just (decTSs-src (suc (suc zero)) hi (tsSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) = refl
ts-fire-win1 (suc (suc (suc zero))) lo a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc (suc zero))) lo (tsReqNB1 (a , r))))
          (_ , TS.sendTS (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ just (decTSs-src (suc (suc (suc zero))) lo (tsSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) = refl
ts-fire-win1 (suc (suc (suc zero))) hi a r = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc (suc zero))) hi (tsReqNB1 (a , r))))
          (_ , TS.sendTS (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) ≡ just (decTSs-src (suc (suc (suc zero))) hi (tsSil TS.stTxIdsNonBlocking))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking a r)) = refl
ts-fire-wrt1 : (l : Link) (d : Dir) (ids : _)
  → decTSs-src l d (tsReqTxs1 ids)
      TSL.─[ TSL.ev (TSL.evl (TSL.evLabel _ (TS.sendTS l d) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)))) ]─►
    decTSs-src l d (tsSil TS.stTxs)
ts-fire-wrt1 (zero) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (zero) lo (tsReqTxs1 ids)))
          (_ , TS.sendTS (zero) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) ≡ just (decTSs-src (zero) lo (tsSil TS.stTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) = refl
ts-fire-wrt1 (zero) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (zero) hi (tsReqTxs1 ids)))
          (_ , TS.sendTS (zero) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) ≡ just (decTSs-src (zero) hi (tsSil TS.stTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) = refl
ts-fire-wrt1 (suc zero) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc zero) lo (tsReqTxs1 ids)))
          (_ , TS.sendTS (suc zero) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) ≡ just (decTSs-src (suc zero) lo (tsSil TS.stTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) = refl
ts-fire-wrt1 (suc zero) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc zero) hi (tsReqTxs1 ids)))
          (_ , TS.sendTS (suc zero) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) ≡ just (decTSs-src (suc zero) hi (tsSil TS.stTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) = refl
ts-fire-wrt1 (suc (suc zero)) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc zero)) lo (tsReqTxs1 ids)))
          (_ , TS.sendTS (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) ≡ just (decTSs-src (suc (suc zero)) lo (tsSil TS.stTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) = refl
ts-fire-wrt1 (suc (suc zero)) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc zero)) hi (tsReqTxs1 ids)))
          (_ , TS.sendTS (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) ≡ just (decTSs-src (suc (suc zero)) hi (tsSil TS.stTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) = refl
ts-fire-wrt1 (suc (suc (suc zero))) lo ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc (suc zero))) lo (tsReqTxs1 ids)))
          (_ , TS.sendTS (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) ≡ just (decTSs-src (suc (suc (suc zero))) lo (tsSil TS.stTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) = refl
ts-fire-wrt1 (suc (suc (suc zero))) hi ids = TSL.sVis refl o
  where
    o : vis-ofT (PTree.force (decTSs-src (suc (suc (suc zero))) hi (tsReqTxs1 ids)))
          (_ , TS.sendTS (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) ≡ just (decTSs-src (suc (suc (suc zero))) hi (tsSil TS.stTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids)) = refl

------------------------------------------------------------------------
-- TS-CLIENT backward production leaf.
------------------------------------------------------------------------
Ttsc : Link → Dir → NS.Table NS.TScPos
Ttsc l d = record { isFin = NS.tsCfin ; nxt = NS.tsCnxt l d }
mkMtsc : (l : Link) (d : Dir) (pos′ : TScPos) {q′ : NS.TScPos} {M : NetProc}
  → M ≡ tableSpec (Ttsc l d) q′ → q′ ≡ coarsenTSc pos′ → M ≡ absTSc l d pos′
mkMtsc l d pos′ Meq qeq = trans Meq (cong (tableSpec (Ttsc l d)) qeq)

tc-hstep : (l : Link) (d : Dir) (st : TS.TSState)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → absTSc l d (tcHead st) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M
  → Σ[ pos′ ∈ TScPos ] (decTSc l d (tcHead st) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► decTSc l d pos′)
      × (M ≡ absTSc l d pos′)
tc-hstep l d TS.stInit {e₁ = TS.sendTS l' d'} {a} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stInit)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSInit)
...     | yes refl = tcSil TS.stIdle , RFTS.renameMap-ev-fwd (tc-fire-init l d) , mkMtsc l d (tcSil TS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stInit {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stInit {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stInit {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stInit {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- stIdle: receives wire requests
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds Blocking aa rr)} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tcReqIdsB1 aa rr , RFTS.renameMap-ev-fwd (tc-fire-reqB l d aa rr t0 md ln) , mkMtsc l d (tcReqIdsB1 aa rr) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxIds NonBlocking aa rr)} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tcReqIdsNB1 aa rr , RFTS.renameMap-ev-fwd (tc-fire-reqNB l d aa rr t0 md ln) , mkMtsc l d (tcReqIdsNB1 aa rr) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSRequestTxs ids)} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tcReqTxs1 ids , RFTS.renameMap-ev-fwd (tc-fire-reqTxs l d ids t0 md ln) , mkMtsc l d (tcReqTxs1 ids) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stIdle {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsBlocking {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} {a} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tcRepB1 a , RFTS.renameMap-ev-fwd (tc-fire-repB l d a) , mkMtsc l d (tcRepB1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsBlocking {e₁ = TS.apiTSev l' d' sendTSDone} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tcDone1 , RFTS.renameMap-ev-fwd (tc-fire-cdone l d) , mkMtsc l d (tcDone1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsBlocking {e₁ = TS.apiTSev l' d' sendTSReplyTxs} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsBlocking {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsBlocking {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsBlocking {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsBlocking {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsBlocking {e₁ = TS.apiTSev l' d' recvTSRequestTxs} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsBlocking {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsBlocking {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} {a} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tcRepNB1 a , RFTS.renameMap-ev-fwd (tc-fire-repNB l d a) , mkMtsc l d (tcRepNB1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.apiTSev l' d' sendTSReplyTxs} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.apiTSev l' d' sendTSDone} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.apiTSev l' d' recvTSRequestTxs} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxs {e₁ = TS.apiTSev l' d' sendTSReplyTxs} {a} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tcRepTxs1 a , RFTS.renameMap-ev-fwd (tc-fire-repTxs l d a) , mkMtsc l d (tcRepTxs1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxs {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxs {e₁ = TS.apiTSev l' d' sendTSDone} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxs {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxs {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxs {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxs {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxs {e₁ = TS.apiTSev l' d' recvTSRequestTxs} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxs {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stTxs {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
tc-hstep l d TS.stDone step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcHead TS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

decTSc-ev-prod-abs : (l : Link) (d : Dir) (pos : TScPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → absTSc l d pos ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M
  → Σ[ pos′ ∈ TScPos ] (decTSc l d pos ═[ ev (evl (evLabel X (ιTS e₁) a)) ]═► decTSc l d pos′)
      × (M ≡ absTSc l d pos′)
decTSc-ev-prod-abs l d (tcHead st) step with tc-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
decTSc-ev-prod-abs l d (tcSil st) step with tc-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decTSc-sil-step l d st) τ*-refl) f τ*-refl , m
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} {a} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ a (Blocking , aa , rr)
...     | yes refl = tcSil TS.stTxIdsBlocking , wev τ*-refl (RFTS.renameMap-ev-fwd (tc-fire-ari1B l d aa rr)) τ*-refl , mkMtsc l d (tcSil TS.stTxIdsBlocking) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSReplyTxs} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSDone} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.apiTSev l' d' recvTSRequestTxs} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsB1 aa rr) {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} {a} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ TS.DecEq-BS×ℕ×ℕ ⦄ a (NonBlocking , aa , rr)
...     | yes refl = tcSil TS.stTxIdsNonBlocking , wev τ*-refl (RFTS.renameMap-ev-fwd (tc-fire-ari1NB l d aa rr)) τ*-refl , mkMtsc l d (tcSil TS.stTxIdsNonBlocking) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSReplyTxs} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSDone} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.apiTSev l' d' recvTSRequestTxs} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqIdsNB1 aa rr) {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqIdsNB1 aa rr)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' recvTSRequestTxs} {a} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ TS.DecEq-ListTxid ⦄ a ids
...     | yes refl = tcSil TS.stTxs , wev τ*-refl (RFTS.renameMap-ev-fwd (tc-fire-art1 l d ids)) τ*-refl , mkMtsc l d (tcSil TS.stTxs) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' recvTSRequestTxs} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' recvTSRequestTxs} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' sendTSReplyTxs} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' sendTSDone} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcReqTxs1 ids) {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepB1 ids) {e₁ = TS.sendTS l' d'} {a} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepB1 ids)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | yes refl = tcSil TS.stIdle , wev τ*-refl (RFTS.renameMap-ev-fwd (tc-fire-wri1B l d ids)) τ*-refl , mkMtsc l d (tcSil TS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepB1 ids) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepB1 ids) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepB1 ids) {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepB1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepB1 ids) {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepB1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepB1 ids) {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepB1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d tcDone1 {e₁ = TS.sendTS l' d'} {a} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc tcDone1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission MsgTSDone)
...     | yes refl = tcSil TS.stDone , wev τ*-refl (RFTS.renameMap-ev-fwd (tc-fire-wdone1 l d)) τ*-refl , mkMtsc l d (tcSil TS.stDone) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d tcDone1 {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d tcDone1 {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d tcDone1 {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc tcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d tcDone1 {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc tcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d tcDone1 {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc tcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepNB1 ids) {e₁ = TS.sendTS l' d'} {a} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepNB1 ids)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxIds ids))
...     | yes refl = tcSil TS.stIdle , wev τ*-refl (RFTS.renameMap-ev-fwd (tc-fire-wri1NB l d ids)) τ*-refl , mkMtsc l d (tcSil TS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepNB1 ids) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepNB1 ids) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepNB1 ids) {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepNB1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepNB1 ids) {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepNB1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepNB1 ids) {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepNB1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepTxs1 txs) {e₁ = TS.sendTS l' d'} {a} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepTxs1 txs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , txSubmission (MsgTSReplyTxs txs))
...     | yes refl = tcSil TS.stIdle , wev τ*-refl (RFTS.renameMap-ev-fwd (tc-fire-wrt1 l d txs)) τ*-refl , mkMtsc l d (tcSil TS.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepTxs1 txs) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepTxs1 txs) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepTxs1 txs) {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepTxs1 txs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepTxs1 txs) {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepTxs1 txs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSc-ev-prod-abs l d (tcRepTxs1 txs) {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttsc l d) (coarsenTSc (tcRepTxs1 txs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

------------------------------------------------------------------------
-- TS-SERVER backward production leaf.
------------------------------------------------------------------------
Ttss : Link → Dir → NS.Table NS.TSsPos
Ttss l d = record { isFin = NS.tsSfin ; nxt = NS.tsSnxt l d }
mkMtss : (l : Link) (d : Dir) (pos′ : TSsPos) {q′ : NS.TSsPos} {M : NetProc}
  → M ≡ tableSpec (Ttss l d) q′ → q′ ≡ coarsenTSs pos′ → M ≡ absTSs l d pos′
mkMtss l d pos′ Meq qeq = trans Meq (cong (tableSpec (Ttss l d)) qeq)

ts-hstep : (l : Link) (d : Dir) (st : TS.TSState)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → absTSs l d (tsHead st) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M
  → Σ[ pos′ ∈ TSsPos ] (decTSs l d (tsHead st) ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► decTSs l d pos′)
      × (M ≡ absTSs l d pos′)
ts-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSInit} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsSil TS.stIdle , RFTS.renameMap-ev-fwd (ts-fire-init l d t0 md ln) , mkMtss l d (tsSil TS.stIdle) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stInit {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stInit)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stIdle {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsBlocking} {a} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsReqB1 a , RFTS.renameMap-ev-fwd (ts-fire-reqB l d a) , mkMtss l d (tsReqB1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stIdle {e₁ = TS.apiTSev l' d' sendTSRequestTxIdsPipelined} {a} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsReqNB1 a , RFTS.renameMap-ev-fwd (ts-fire-reqNB l d a) , mkMtss l d (tsReqNB1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stIdle {e₁ = TS.apiTSev l' d' sendTSRequestTxsPipelined} {a} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsReqTxs1 a , RFTS.renameMap-ev-fwd (ts-fire-reqTxs l d a) , mkMtss l d (tsReqTxs1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stIdle {e₁ = TS.apiTSev l' d' sendTSReplyTxIds} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stIdle {e₁ = TS.apiTSev l' d' sendTSReplyTxs} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stIdle {e₁ = TS.apiTSev l' d' sendTSDone} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stIdle {e₁ = TS.apiTSev l' d' recvTSRequestTxIds} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stIdle {e₁ = TS.apiTSev l' d' recvTSRequestTxs} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stIdle {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stIdle {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stIdle {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsSil TS.stIdle , RFTS.renameMap-ev-fwd (ts-fire-blkReply l d ids t0 md ln) , mkMtss l d (tsSil TS.stIdle) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission MsgTSDone} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsDone1 , RFTS.renameMap-ev-fwd (ts-fire-blkDone l d t0 md ln) , mkMtss l d tsDone1 Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsBlocking {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxIds ids)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsSil TS.stIdle , RFTS.renameMap-ev-fwd (ts-fire-nblReply l d ids t0 md ln) , mkMtss l d (tsSil TS.stIdle) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxs _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxIdsNonBlocking {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxIdsNonBlocking)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = t0 , md , ln , txSubmission (MsgTSReplyTxs txs)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsSil TS.stIdle , RFTS.renameMap-ev-fwd (ts-fire-txsReply l d txs t0 md ln) , mkMtss l d (tsSil TS.stIdle) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSInit} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxIds _ _ _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSRequestTxs _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission (MsgTSReplyTxIds _)} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , txSubmission MsgTSDone} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.receiveTS l' d'} {a = _ , _ , _ , leiosFetch x} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stTxs {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
ts-hstep l d TS.stDone step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsHead TS.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

decTSs-ev-prod-abs : (l : Link) (d : Dir) (pos : TSsPos)
    {X : Set 0ℓ} {e₁ : TS.TSEv X} {a : X} {M : NetProc}
  → absTSs l d pos ─[ ev (evl (evLabel X (ιTS e₁) a)) ]─► M
  → Σ[ pos′ ∈ TSsPos ] (decTSs l d pos ═[ ev (evl (evLabel X (ιTS e₁) a)) ]═► decTSs l d pos′)
      × (M ≡ absTSs l d pos′)
decTSs-ev-prod-abs l d (tsHead st) step with ts-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
decTSs-ev-prod-abs l d (tsSil st) step with ts-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decTSs-sil-step l d st) τ*-refl) f τ*-refl , m
decTSs-ev-prod-abs l d tsDone1 {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs tsDone1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = tsSil TS.stDone , wev τ*-refl (RFTS.renameMap-ev-fwd (ts-fire-sddone l d)) τ*-refl , mkMtss l d (tsSil TS.stDone) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d tsDone1 {e₁ = TS.sendTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs tsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d tsDone1 {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs tsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d tsDone1 {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs tsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqB1 (aa , rr)) {e₁ = TS.sendTS l' d'} {a} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqB1 (aa , rr))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds Blocking aa rr))
...     | yes refl = tsSil TS.stTxIdsBlocking , wev τ*-refl (RFTS.renameMap-ev-fwd (ts-fire-wib1 l d aa rr)) τ*-refl , mkMtss l d (tsSil TS.stTxIdsBlocking) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqB1 (aa , rr)) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqB1 (aa , rr)) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqB1 (aa , rr)) {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqB1 (aa , rr))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqB1 (aa , rr)) {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqB1 (aa , rr))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqB1 (aa , rr)) {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqB1 (aa , rr))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqNB1 (aa , rr)) {e₁ = TS.sendTS l' d'} {a} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqNB1 (aa , rr))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxIds NonBlocking aa rr))
...     | yes refl = tsSil TS.stTxIdsNonBlocking , wev τ*-refl (RFTS.renameMap-ev-fwd (ts-fire-win1 l d aa rr)) τ*-refl , mkMtss l d (tsSil TS.stTxIdsNonBlocking) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqNB1 (aa , rr)) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqNB1 (aa , rr)) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqNB1 (aa , rr)) {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqNB1 (aa , rr))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqNB1 (aa , rr)) {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqNB1 (aa , rr))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqNB1 (aa , rr)) {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqNB1 (aa , rr))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqTxs1 ids) {e₁ = TS.sendTS l' d'} {a} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqTxs1 ids)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , txSubmission (MsgTSRequestTxs ids))
...     | yes refl = tsSil TS.stTxs , wev τ*-refl (RFTS.renameMap-ev-fwd (ts-fire-wrt1 l d ids)) τ*-refl , mkMtss l d (tsSil TS.stTxs) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqTxs1 ids) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqTxs1 ids) {e₁ = TS.sendTS l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqTxs1 ids) {e₁ = TS.receiveTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqTxs1 ids) {e₁ = TS.apiTSev l' d' m} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decTSs-ev-prod-abs l d (tsReqTxs1 ids) {e₁ = TS.doneTS l' d'} step
  with tableSpec-ev-inv (Ttss l d) (coarsenTSs (tsReqTxs1 ids)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- TS-SECTION-END

-- LN-SECTION-BEGIN
------------------------------------------------------------------------
-- INERT PEER LeiosNotify (LN) — backward production leaves.
------------------------------------------------------------------------
decLNc-sil-step : (l : Link) (d : Dir) (st : LN.LNState)
  → decLNc l d (lncSil st) ─[ τ ]─► decLNc l d (lncHead st)
decLNc-sil-step l d st = sSil refl
decLNs-sil-step : (l : Link) (d : Dir) (st : LN.LNState)
  → decLNs l d (lnsSil st) ─[ τ ]─► decLNs l d (lnsHead st)
decLNs-sil-step l d st = sSil refl

-- CLIENT head api-sends (stIdle) — l,d gated
lnc-fire-req : (l : Link) (d : Dir)
  → decLNc-src l d (lncHead LN.stIdle)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.apiLNev l d sendLNRequestNext) U.tt)) ]─►
    decLNc-src l d lncReq1
lnc-fire-req l d = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src l d (lncHead LN.stIdle)))
          (_ , LN.apiLNev l d sendLNRequestNext) U.tt ≡ just (decLNc-src l d (lncReq1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lnc-fire-cdone : (l : Link) (d : Dir)
  → decLNc-src l d (lncHead LN.stIdle)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.apiLNev l d sendLNDone) U.tt)) ]─►
    decLNc-src l d lncDone1
lnc-fire-cdone l d = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src l d (lncHead LN.stIdle)))
          (_ , LN.apiLNev l d sendLNDone) U.tt ≡ just (decLNc-src l d (lncDone1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- CLIENT head receives (stBusy) — l,d gated
lnc-fire-rann : (l : Link) (d : Dir) (h : _) (t0 : _) (md : _) (ln : _)
  → decLNc-src l d (lncHead LN.stBusy)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.receiveLN l d) (t0 , md , ln , leiosNotify (MsgLNBlockAnnouncement h)))) ]─►
    decLNc-src l d (lncRann1 h)
lnc-fire-rann l d h t0 md ln = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src l d (lncHead LN.stBusy)))
          (_ , LN.receiveLN l d) (t0 , md , ln , leiosNotify (MsgLNBlockAnnouncement h)) ≡ just (decLNc-src l d (lncRann1 h))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lnc-fire-roff : (l : Link) (d : Dir) (q : _) (t0 : _) (md : _) (ln : _)
  → decLNc-src l d (lncHead LN.stBusy)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.receiveLN l d) (t0 , md , ln , leiosNotify (MsgLNBlockOffer q)))) ]─►
    decLNc-src l d (lncRoff1 q)
lnc-fire-roff l d q t0 md ln = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src l d (lncHead LN.stBusy)))
          (_ , LN.receiveLN l d) (t0 , md , ln , leiosNotify (MsgLNBlockOffer q)) ≡ just (decLNc-src l d (lncRoff1 q))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lnc-fire-rtxs : (l : Link) (d : Dir) (q : _) (t0 : _) (md : _) (ln : _)
  → decLNc-src l d (lncHead LN.stBusy)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.receiveLN l d) (t0 , md , ln , leiosNotify (MsgLNBlockTxsOffer q)))) ]─►
    decLNc-src l d (lncRtxs1 q)
lnc-fire-rtxs l d q t0 md ln = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src l d (lncHead LN.stBusy)))
          (_ , LN.receiveLN l d) (t0 , md , ln , leiosNotify (MsgLNBlockTxsOffer q)) ≡ just (decLNc-src l d (lncRtxs1 q))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lnc-fire-rvot : (l : Link) (d : Dir) (vs : _) (t0 : _) (md : _) (ln : _)
  → decLNc-src l d (lncHead LN.stBusy)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.receiveLN l d) (t0 , md , ln , leiosNotify (MsgLNVotesOffer vs)))) ]─►
    decLNc-src l d (lncRvot1 vs)
lnc-fire-rvot l d vs t0 md ln = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src l d (lncHead LN.stBusy)))
          (_ , LN.receiveLN l d) (t0 , md , ln , leiosNotify (MsgLNVotesOffer vs)) ≡ just (decLNc-src l d (lncRvot1 vs))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- CLIENT api-emit mids — Fin-enum + value gate
lnc-fire-rann1 : (l : Link) (d : Dir) (h : _)
  → decLNc-src l d (lncRann1 h)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.apiLNev l d recvLNBlockAnnouncement) h)) ]─►
    decLNc-src l d (lncSil LN.stIdle)
lnc-fire-rann1 (zero) lo h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) lo (lncRann1 h)))
          (_ , LN.apiLNev (zero) lo recvLNBlockAnnouncement) h ≡ just (decLNc-src (zero) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Header} h = refl
lnc-fire-rann1 (zero) hi h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) hi (lncRann1 h)))
          (_ , LN.apiLNev (zero) hi recvLNBlockAnnouncement) h ≡ just (decLNc-src (zero) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Header} h = refl
lnc-fire-rann1 (suc zero) lo h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) lo (lncRann1 h)))
          (_ , LN.apiLNev (suc zero) lo recvLNBlockAnnouncement) h ≡ just (decLNc-src (suc zero) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Header} h = refl
lnc-fire-rann1 (suc zero) hi h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) hi (lncRann1 h)))
          (_ , LN.apiLNev (suc zero) hi recvLNBlockAnnouncement) h ≡ just (decLNc-src (suc zero) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Header} h = refl
lnc-fire-rann1 (suc (suc zero)) lo h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) lo (lncRann1 h)))
          (_ , LN.apiLNev (suc (suc zero)) lo recvLNBlockAnnouncement) h ≡ just (decLNc-src (suc (suc zero)) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Header} h = refl
lnc-fire-rann1 (suc (suc zero)) hi h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) hi (lncRann1 h)))
          (_ , LN.apiLNev (suc (suc zero)) hi recvLNBlockAnnouncement) h ≡ just (decLNc-src (suc (suc zero)) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Header} h = refl
lnc-fire-rann1 (suc (suc (suc zero))) lo h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) lo (lncRann1 h)))
          (_ , LN.apiLNev (suc (suc (suc zero))) lo recvLNBlockAnnouncement) h ≡ just (decLNc-src (suc (suc (suc zero))) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Header} h = refl
lnc-fire-rann1 (suc (suc (suc zero))) hi h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) hi (lncRann1 h)))
          (_ , LN.apiLNev (suc (suc (suc zero))) hi recvLNBlockAnnouncement) h ≡ just (decLNc-src (suc (suc (suc zero))) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Header} h = refl
lnc-fire-roff1 : (l : Link) (d : Dir) (q : _)
  → decLNc-src l d (lncRoff1 q)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.apiLNev l d recvLNBlockOffer) q)) ]─►
    decLNc-src l d (lncSil LN.stIdle)
lnc-fire-roff1 (zero) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) lo (lncRoff1 q)))
          (_ , LN.apiLNev (zero) lo recvLNBlockOffer) q ≡ just (decLNc-src (zero) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-roff1 (zero) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) hi (lncRoff1 q)))
          (_ , LN.apiLNev (zero) hi recvLNBlockOffer) q ≡ just (decLNc-src (zero) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-roff1 (suc zero) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) lo (lncRoff1 q)))
          (_ , LN.apiLNev (suc zero) lo recvLNBlockOffer) q ≡ just (decLNc-src (suc zero) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-roff1 (suc zero) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) hi (lncRoff1 q)))
          (_ , LN.apiLNev (suc zero) hi recvLNBlockOffer) q ≡ just (decLNc-src (suc zero) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-roff1 (suc (suc zero)) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) lo (lncRoff1 q)))
          (_ , LN.apiLNev (suc (suc zero)) lo recvLNBlockOffer) q ≡ just (decLNc-src (suc (suc zero)) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-roff1 (suc (suc zero)) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) hi (lncRoff1 q)))
          (_ , LN.apiLNev (suc (suc zero)) hi recvLNBlockOffer) q ≡ just (decLNc-src (suc (suc zero)) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-roff1 (suc (suc (suc zero))) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) lo (lncRoff1 q)))
          (_ , LN.apiLNev (suc (suc (suc zero))) lo recvLNBlockOffer) q ≡ just (decLNc-src (suc (suc (suc zero))) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-roff1 (suc (suc (suc zero))) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) hi (lncRoff1 q)))
          (_ , LN.apiLNev (suc (suc (suc zero))) hi recvLNBlockOffer) q ≡ just (decLNc-src (suc (suc (suc zero))) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-rtxs1 : (l : Link) (d : Dir) (q : _)
  → decLNc-src l d (lncRtxs1 q)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.apiLNev l d recvLNBlockTxsOffer) q)) ]─►
    decLNc-src l d (lncSil LN.stIdle)
lnc-fire-rtxs1 (zero) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) lo (lncRtxs1 q)))
          (_ , LN.apiLNev (zero) lo recvLNBlockTxsOffer) q ≡ just (decLNc-src (zero) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-rtxs1 (zero) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) hi (lncRtxs1 q)))
          (_ , LN.apiLNev (zero) hi recvLNBlockTxsOffer) q ≡ just (decLNc-src (zero) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-rtxs1 (suc zero) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) lo (lncRtxs1 q)))
          (_ , LN.apiLNev (suc zero) lo recvLNBlockTxsOffer) q ≡ just (decLNc-src (suc zero) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-rtxs1 (suc zero) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) hi (lncRtxs1 q)))
          (_ , LN.apiLNev (suc zero) hi recvLNBlockTxsOffer) q ≡ just (decLNc-src (suc zero) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-rtxs1 (suc (suc zero)) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) lo (lncRtxs1 q)))
          (_ , LN.apiLNev (suc (suc zero)) lo recvLNBlockTxsOffer) q ≡ just (decLNc-src (suc (suc zero)) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-rtxs1 (suc (suc zero)) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) hi (lncRtxs1 q)))
          (_ , LN.apiLNev (suc (suc zero)) hi recvLNBlockTxsOffer) q ≡ just (decLNc-src (suc (suc zero)) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-rtxs1 (suc (suc (suc zero))) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) lo (lncRtxs1 q)))
          (_ , LN.apiLNev (suc (suc (suc zero))) lo recvLNBlockTxsOffer) q ≡ just (decLNc-src (suc (suc (suc zero))) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-rtxs1 (suc (suc (suc zero))) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) hi (lncRtxs1 q)))
          (_ , LN.apiLNev (suc (suc (suc zero))) hi recvLNBlockTxsOffer) q ≡ just (decLNc-src (suc (suc (suc zero))) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Point} q = refl
lnc-fire-rvot1 : (l : Link) (d : Dir) (vs : _)
  → decLNc-src l d (lncRvot1 vs)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.apiLNev l d recvLNVotesOffer) vs)) ]─►
    decLNc-src l d (lncSil LN.stIdle)
lnc-fire-rvot1 (zero) lo vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) lo (lncRvot1 vs)))
          (_ , LN.apiLNev (zero) lo recvLNVotesOffer) vs ≡ just (decLNc-src (zero) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl ⦃ LN.DecEq-ListVote ⦄ vs = refl
lnc-fire-rvot1 (zero) hi vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) hi (lncRvot1 vs)))
          (_ , LN.apiLNev (zero) hi recvLNVotesOffer) vs ≡ just (decLNc-src (zero) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl ⦃ LN.DecEq-ListVote ⦄ vs = refl
lnc-fire-rvot1 (suc zero) lo vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) lo (lncRvot1 vs)))
          (_ , LN.apiLNev (suc zero) lo recvLNVotesOffer) vs ≡ just (decLNc-src (suc zero) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl ⦃ LN.DecEq-ListVote ⦄ vs = refl
lnc-fire-rvot1 (suc zero) hi vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) hi (lncRvot1 vs)))
          (_ , LN.apiLNev (suc zero) hi recvLNVotesOffer) vs ≡ just (decLNc-src (suc zero) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl ⦃ LN.DecEq-ListVote ⦄ vs = refl
lnc-fire-rvot1 (suc (suc zero)) lo vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) lo (lncRvot1 vs)))
          (_ , LN.apiLNev (suc (suc zero)) lo recvLNVotesOffer) vs ≡ just (decLNc-src (suc (suc zero)) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl ⦃ LN.DecEq-ListVote ⦄ vs = refl
lnc-fire-rvot1 (suc (suc zero)) hi vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) hi (lncRvot1 vs)))
          (_ , LN.apiLNev (suc (suc zero)) hi recvLNVotesOffer) vs ≡ just (decLNc-src (suc (suc zero)) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl ⦃ LN.DecEq-ListVote ⦄ vs = refl
lnc-fire-rvot1 (suc (suc (suc zero))) lo vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) lo (lncRvot1 vs)))
          (_ , LN.apiLNev (suc (suc (suc zero))) lo recvLNVotesOffer) vs ≡ just (decLNc-src (suc (suc (suc zero))) lo (lncSil LN.stIdle))
    o rewrite ≟-yes-refl ⦃ LN.DecEq-ListVote ⦄ vs = refl
lnc-fire-rvot1 (suc (suc (suc zero))) hi vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) hi (lncRvot1 vs)))
          (_ , LN.apiLNev (suc (suc (suc zero))) hi recvLNVotesOffer) vs ≡ just (decLNc-src (suc (suc (suc zero))) hi (lncSil LN.stIdle))
    o rewrite ≟-yes-refl ⦃ LN.DecEq-ListVote ⦄ vs = refl

-- CLIENT wire-send mids — Fin-enum + Payload gate
lnc-fire-wreq1 : (l : Link) (d : Dir)
  → decLNc-src l d lncReq1
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.sendLN l d) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext))) ]─►
    decLNc-src l d (lncSil LN.stBusy)
lnc-fire-wreq1 (zero) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) lo (lncReq1)))
          (_ , LN.sendLN (zero) lo) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) ≡ just (decLNc-src (zero) lo (lncSil LN.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) = refl
lnc-fire-wreq1 (zero) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) hi (lncReq1)))
          (_ , LN.sendLN (zero) hi) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) ≡ just (decLNc-src (zero) hi (lncSil LN.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) = refl
lnc-fire-wreq1 (suc zero) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) lo (lncReq1)))
          (_ , LN.sendLN (suc zero) lo) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) ≡ just (decLNc-src (suc zero) lo (lncSil LN.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) = refl
lnc-fire-wreq1 (suc zero) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) hi (lncReq1)))
          (_ , LN.sendLN (suc zero) hi) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) ≡ just (decLNc-src (suc zero) hi (lncSil LN.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) = refl
lnc-fire-wreq1 (suc (suc zero)) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) lo (lncReq1)))
          (_ , LN.sendLN (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) ≡ just (decLNc-src (suc (suc zero)) lo (lncSil LN.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) = refl
lnc-fire-wreq1 (suc (suc zero)) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) hi (lncReq1)))
          (_ , LN.sendLN (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) ≡ just (decLNc-src (suc (suc zero)) hi (lncSil LN.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) = refl
lnc-fire-wreq1 (suc (suc (suc zero))) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) lo (lncReq1)))
          (_ , LN.sendLN (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) ≡ just (decLNc-src (suc (suc (suc zero))) lo (lncSil LN.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) = refl
lnc-fire-wreq1 (suc (suc (suc zero))) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) hi (lncReq1)))
          (_ , LN.sendLN (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) ≡ just (decLNc-src (suc (suc (suc zero))) hi (lncSil LN.stBusy))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext) = refl
lnc-fire-wdone1 : (l : Link) (d : Dir)
  → decLNc-src l d lncDone1
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.sendLN l d) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone))) ]─►
    decLNc-src l d (lncSil LN.stDone)
lnc-fire-wdone1 (zero) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) lo (lncDone1)))
          (_ , LN.sendLN (zero) lo) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) ≡ just (decLNc-src (zero) lo (lncSil LN.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) = refl
lnc-fire-wdone1 (zero) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (zero) hi (lncDone1)))
          (_ , LN.sendLN (zero) hi) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) ≡ just (decLNc-src (zero) hi (lncSil LN.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) = refl
lnc-fire-wdone1 (suc zero) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) lo (lncDone1)))
          (_ , LN.sendLN (suc zero) lo) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) ≡ just (decLNc-src (suc zero) lo (lncSil LN.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) = refl
lnc-fire-wdone1 (suc zero) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc zero) hi (lncDone1)))
          (_ , LN.sendLN (suc zero) hi) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) ≡ just (decLNc-src (suc zero) hi (lncSil LN.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) = refl
lnc-fire-wdone1 (suc (suc zero)) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) lo (lncDone1)))
          (_ , LN.sendLN (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) ≡ just (decLNc-src (suc (suc zero)) lo (lncSil LN.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) = refl
lnc-fire-wdone1 (suc (suc zero)) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc zero)) hi (lncDone1)))
          (_ , LN.sendLN (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) ≡ just (decLNc-src (suc (suc zero)) hi (lncSil LN.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) = refl
lnc-fire-wdone1 (suc (suc (suc zero))) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) lo (lncDone1)))
          (_ , LN.sendLN (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) ≡ just (decLNc-src (suc (suc (suc zero))) lo (lncSil LN.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) = refl
lnc-fire-wdone1 (suc (suc (suc zero))) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNc-src (suc (suc (suc zero))) hi (lncDone1)))
          (_ , LN.sendLN (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) ≡ just (decLNc-src (suc (suc (suc zero))) hi (lncSil LN.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone) = refl

-- SERVER head receives (stIdle) — l,d gated
lns-fire-idleReq : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decLNs-src l d (lnsHead LN.stIdle)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.receiveLN l d) (t0 , md , ln , leiosNotify MsgLNRequestNext))) ]─►
    decLNs-src l d (lnsSil LN.stBusy)
lns-fire-idleReq l d t0 md ln = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src l d (lnsHead LN.stIdle)))
          (_ , LN.receiveLN l d) (t0 , md , ln , leiosNotify MsgLNRequestNext) ≡ just (decLNs-src l d (lnsSil LN.stBusy))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lns-fire-idleDone : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decLNs-src l d (lnsHead LN.stIdle)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.receiveLN l d) (t0 , md , ln , leiosNotify MsgLNDone))) ]─►
    decLNs-src l d (lnsDone1)
lns-fire-idleDone l d t0 md ln = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src l d (lnsHead LN.stIdle)))
          (_ , LN.receiveLN l d) (t0 , md , ln , leiosNotify MsgLNDone) ≡ just (decLNs-src l d (lnsDone1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- SERVER head api-sends (stBusy) — l,d gated
lns-fire-wann : (l : Link) (d : Dir) (a : _)
  → decLNs-src l d (lnsHead LN.stBusy)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.apiLNev l d sendLNBlockAnnouncement) a)) ]─►
    decLNs-src l d (lnsWann1 a)
lns-fire-wann l d a = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src l d (lnsHead LN.stBusy)))
          (_ , LN.apiLNev l d sendLNBlockAnnouncement) a ≡ just (decLNs-src l d (lnsWann1 a))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lns-fire-woff : (l : Link) (d : Dir) (a : _)
  → decLNs-src l d (lnsHead LN.stBusy)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.apiLNev l d sendLNBlockOffer) a)) ]─►
    decLNs-src l d (lnsWoff1 a)
lns-fire-woff l d a = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src l d (lnsHead LN.stBusy)))
          (_ , LN.apiLNev l d sendLNBlockOffer) a ≡ just (decLNs-src l d (lnsWoff1 a))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lns-fire-wtxs : (l : Link) (d : Dir) (a : _)
  → decLNs-src l d (lnsHead LN.stBusy)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.apiLNev l d sendLNBlockTxsOffer) a)) ]─►
    decLNs-src l d (lnsWtxs1 a)
lns-fire-wtxs l d a = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src l d (lnsHead LN.stBusy)))
          (_ , LN.apiLNev l d sendLNBlockTxsOffer) a ≡ just (decLNs-src l d (lnsWtxs1 a))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lns-fire-wvot : (l : Link) (d : Dir) (a : _)
  → decLNs-src l d (lnsHead LN.stBusy)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.apiLNev l d sendLNVotesOffer) a)) ]─►
    decLNs-src l d (lnsWvot1 a)
lns-fire-wvot l d a = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src l d (lnsHead LN.stBusy)))
          (_ , LN.apiLNev l d sendLNVotesOffer) a ≡ just (decLNs-src l d (lnsWvot1 a))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- SERVER done mid lnsDone1 → lnsSil stDone (doneLN, ⊤) — Fin-enum
lns-fire-sddone : (l : Link) (d : Dir)
  → decLNs-src l d lnsDone1
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.doneLN l d) U.tt)) ]─►
    decLNs-src l d (lnsSil LN.stDone)
lns-fire-sddone (zero) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (zero) lo lnsDone1))
          (_ , LN.doneLN (zero) lo) U.tt ≡ just (decLNs-src (zero) lo (lnsSil LN.stDone))
    o = refl
lns-fire-sddone (zero) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (zero) hi lnsDone1))
          (_ , LN.doneLN (zero) hi) U.tt ≡ just (decLNs-src (zero) hi (lnsSil LN.stDone))
    o = refl
lns-fire-sddone (suc zero) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc zero) lo lnsDone1))
          (_ , LN.doneLN (suc zero) lo) U.tt ≡ just (decLNs-src (suc zero) lo (lnsSil LN.stDone))
    o = refl
lns-fire-sddone (suc zero) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc zero) hi lnsDone1))
          (_ , LN.doneLN (suc zero) hi) U.tt ≡ just (decLNs-src (suc zero) hi (lnsSil LN.stDone))
    o = refl
lns-fire-sddone (suc (suc zero)) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc zero)) lo lnsDone1))
          (_ , LN.doneLN (suc (suc zero)) lo) U.tt ≡ just (decLNs-src (suc (suc zero)) lo (lnsSil LN.stDone))
    o = refl
lns-fire-sddone (suc (suc zero)) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc zero)) hi lnsDone1))
          (_ , LN.doneLN (suc (suc zero)) hi) U.tt ≡ just (decLNs-src (suc (suc zero)) hi (lnsSil LN.stDone))
    o = refl
lns-fire-sddone (suc (suc (suc zero))) lo = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc (suc zero))) lo lnsDone1))
          (_ , LN.doneLN (suc (suc (suc zero))) lo) U.tt ≡ just (decLNs-src (suc (suc (suc zero))) lo (lnsSil LN.stDone))
    o = refl
lns-fire-sddone (suc (suc (suc zero))) hi = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc (suc zero))) hi lnsDone1))
          (_ , LN.doneLN (suc (suc (suc zero))) hi) U.tt ≡ just (decLNs-src (suc (suc (suc zero))) hi (lnsSil LN.stDone))
    o = refl

-- SERVER wire-send mids — Fin-enum + Payload gate
lns-fire-wann1 : (l : Link) (d : Dir) (h : _)
  → decLNs-src l d (lnsWann1 h)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.sendLN l d) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)))) ]─►
    decLNs-src l d (lnsSil LN.stIdle)
lns-fire-wann1 (zero) lo h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (zero) lo (lnsWann1 h)))
          (_ , LN.sendLN (zero) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) ≡ just (decLNs-src (zero) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) = refl
lns-fire-wann1 (zero) hi h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (zero) hi (lnsWann1 h)))
          (_ , LN.sendLN (zero) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) ≡ just (decLNs-src (zero) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) = refl
lns-fire-wann1 (suc zero) lo h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc zero) lo (lnsWann1 h)))
          (_ , LN.sendLN (suc zero) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) ≡ just (decLNs-src (suc zero) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) = refl
lns-fire-wann1 (suc zero) hi h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc zero) hi (lnsWann1 h)))
          (_ , LN.sendLN (suc zero) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) ≡ just (decLNs-src (suc zero) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) = refl
lns-fire-wann1 (suc (suc zero)) lo h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc zero)) lo (lnsWann1 h)))
          (_ , LN.sendLN (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) ≡ just (decLNs-src (suc (suc zero)) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) = refl
lns-fire-wann1 (suc (suc zero)) hi h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc zero)) hi (lnsWann1 h)))
          (_ , LN.sendLN (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) ≡ just (decLNs-src (suc (suc zero)) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) = refl
lns-fire-wann1 (suc (suc (suc zero))) lo h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc (suc zero))) lo (lnsWann1 h)))
          (_ , LN.sendLN (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) ≡ just (decLNs-src (suc (suc (suc zero))) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) = refl
lns-fire-wann1 (suc (suc (suc zero))) hi h = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc (suc zero))) hi (lnsWann1 h)))
          (_ , LN.sendLN (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) ≡ just (decLNs-src (suc (suc (suc zero))) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h)) = refl
lns-fire-woff1 : (l : Link) (d : Dir) (q : _)
  → decLNs-src l d (lnsWoff1 q)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.sendLN l d) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)))) ]─►
    decLNs-src l d (lnsSil LN.stIdle)
lns-fire-woff1 (zero) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (zero) lo (lnsWoff1 q)))
          (_ , LN.sendLN (zero) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) ≡ just (decLNs-src (zero) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) = refl
lns-fire-woff1 (zero) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (zero) hi (lnsWoff1 q)))
          (_ , LN.sendLN (zero) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) ≡ just (decLNs-src (zero) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) = refl
lns-fire-woff1 (suc zero) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc zero) lo (lnsWoff1 q)))
          (_ , LN.sendLN (suc zero) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) ≡ just (decLNs-src (suc zero) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) = refl
lns-fire-woff1 (suc zero) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc zero) hi (lnsWoff1 q)))
          (_ , LN.sendLN (suc zero) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) ≡ just (decLNs-src (suc zero) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) = refl
lns-fire-woff1 (suc (suc zero)) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc zero)) lo (lnsWoff1 q)))
          (_ , LN.sendLN (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) ≡ just (decLNs-src (suc (suc zero)) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) = refl
lns-fire-woff1 (suc (suc zero)) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc zero)) hi (lnsWoff1 q)))
          (_ , LN.sendLN (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) ≡ just (decLNs-src (suc (suc zero)) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) = refl
lns-fire-woff1 (suc (suc (suc zero))) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc (suc zero))) lo (lnsWoff1 q)))
          (_ , LN.sendLN (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) ≡ just (decLNs-src (suc (suc (suc zero))) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) = refl
lns-fire-woff1 (suc (suc (suc zero))) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc (suc zero))) hi (lnsWoff1 q)))
          (_ , LN.sendLN (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) ≡ just (decLNs-src (suc (suc (suc zero))) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q)) = refl
lns-fire-wtxs1 : (l : Link) (d : Dir) (q : _)
  → decLNs-src l d (lnsWtxs1 q)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.sendLN l d) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)))) ]─►
    decLNs-src l d (lnsSil LN.stIdle)
lns-fire-wtxs1 (zero) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (zero) lo (lnsWtxs1 q)))
          (_ , LN.sendLN (zero) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) ≡ just (decLNs-src (zero) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) = refl
lns-fire-wtxs1 (zero) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (zero) hi (lnsWtxs1 q)))
          (_ , LN.sendLN (zero) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) ≡ just (decLNs-src (zero) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) = refl
lns-fire-wtxs1 (suc zero) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc zero) lo (lnsWtxs1 q)))
          (_ , LN.sendLN (suc zero) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) ≡ just (decLNs-src (suc zero) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) = refl
lns-fire-wtxs1 (suc zero) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc zero) hi (lnsWtxs1 q)))
          (_ , LN.sendLN (suc zero) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) ≡ just (decLNs-src (suc zero) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) = refl
lns-fire-wtxs1 (suc (suc zero)) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc zero)) lo (lnsWtxs1 q)))
          (_ , LN.sendLN (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) ≡ just (decLNs-src (suc (suc zero)) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) = refl
lns-fire-wtxs1 (suc (suc zero)) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc zero)) hi (lnsWtxs1 q)))
          (_ , LN.sendLN (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) ≡ just (decLNs-src (suc (suc zero)) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) = refl
lns-fire-wtxs1 (suc (suc (suc zero))) lo q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc (suc zero))) lo (lnsWtxs1 q)))
          (_ , LN.sendLN (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) ≡ just (decLNs-src (suc (suc (suc zero))) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) = refl
lns-fire-wtxs1 (suc (suc (suc zero))) hi q = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc (suc zero))) hi (lnsWtxs1 q)))
          (_ , LN.sendLN (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) ≡ just (decLNs-src (suc (suc (suc zero))) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q)) = refl
lns-fire-wvot1 : (l : Link) (d : Dir) (vs : _)
  → decLNs-src l d (lnsWvot1 vs)
      LNL.─[ LNL.ev (LNL.evl (LNL.evLabel _ (LN.sendLN l d) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)))) ]─►
    decLNs-src l d (lnsSil LN.stIdle)
lns-fire-wvot1 (zero) lo vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (zero) lo (lnsWvot1 vs)))
          (_ , LN.sendLN (zero) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) ≡ just (decLNs-src (zero) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) = refl
lns-fire-wvot1 (zero) hi vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (zero) hi (lnsWvot1 vs)))
          (_ , LN.sendLN (zero) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) ≡ just (decLNs-src (zero) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) = refl
lns-fire-wvot1 (suc zero) lo vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc zero) lo (lnsWvot1 vs)))
          (_ , LN.sendLN (suc zero) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) ≡ just (decLNs-src (suc zero) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) = refl
lns-fire-wvot1 (suc zero) hi vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc zero) hi (lnsWvot1 vs)))
          (_ , LN.sendLN (suc zero) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) ≡ just (decLNs-src (suc zero) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) = refl
lns-fire-wvot1 (suc (suc zero)) lo vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc zero)) lo (lnsWvot1 vs)))
          (_ , LN.sendLN (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) ≡ just (decLNs-src (suc (suc zero)) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) = refl
lns-fire-wvot1 (suc (suc zero)) hi vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc zero)) hi (lnsWvot1 vs)))
          (_ , LN.sendLN (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) ≡ just (decLNs-src (suc (suc zero)) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) = refl
lns-fire-wvot1 (suc (suc (suc zero))) lo vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc (suc zero))) lo (lnsWvot1 vs)))
          (_ , LN.sendLN (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) ≡ just (decLNs-src (suc (suc (suc zero))) lo (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) = refl
lns-fire-wvot1 (suc (suc (suc zero))) hi vs = LNL.sVis refl o
  where
    o : vis-ofN (PTree.force (decLNs-src (suc (suc (suc zero))) hi (lnsWvot1 vs)))
          (_ , LN.sendLN (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) ≡ just (decLNs-src (suc (suc (suc zero))) hi (lnsSil LN.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs)) = refl

------------------------------------------------------------------------
-- LN-CLIENT backward production leaf.
------------------------------------------------------------------------
Tlnc : Link → Dir → NS.Table NS.LNcPos
Tlnc l d = record { isFin = NS.lnCfin ; nxt = NS.lnCnxt l d }
mkMlnc : (l : Link) (d : Dir) (pos′ : LNcPos) {q′ : NS.LNcPos} {M : NetProc}
  → M ≡ tableSpec (Tlnc l d) q′ → q′ ≡ coarsenLNc pos′ → M ≡ absLNc l d pos′
mkMlnc l d pos′ Meq qeq = trans Meq (cong (tableSpec (Tlnc l d)) qeq)

lnc-hstep : (l : Link) (d : Dir) (st : LN.LNState)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {M : NetProc}
  → absLNc l d (lncHead st) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M
  → Σ[ pos′ ∈ LNcPos ] (decLNc l d (lncHead st) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► decLNc l d pos′)
      × (M ≡ absLNc l d pos′)
lnc-hstep l d LN.stIdle {e₁ = LN.apiLNev l' d' sendLNRequestNext} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lncReq1 , RFLN.renameMap-ev-fwd (lnc-fire-req l d) , mkMlnc l d (lncReq1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.apiLNev l' d' sendLNDone} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lncDone1 , RFLN.renameMap-ev-fwd (lnc-fire-cdone l d) , mkMlnc l d (lncDone1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.apiLNev l' d' sendLNBlockAnnouncement} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.apiLNev l' d' sendLNBlockOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.apiLNev l' d' sendLNBlockTxsOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.apiLNev l' d' sendLNVotesOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.apiLNev l' d' recvLNBlockAnnouncement} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.apiLNev l' d' recvLNBlockOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.apiLNev l' d' recvLNBlockTxsOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.apiLNev l' d' recvLNVotesOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.sendLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stIdle {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockAnnouncement h)} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lncRann1 h , RFLN.renameMap-ev-fwd (lnc-fire-rann l d h t0 md ln) , mkMlnc l d (lncRann1 h) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockOffer q)} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lncRoff1 q , RFLN.renameMap-ev-fwd (lnc-fire-roff l d q t0 md ln) , mkMlnc l d (lncRoff1 q) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNBlockTxsOffer q)} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lncRtxs1 q , RFLN.renameMap-ev-fwd (lnc-fire-rtxs l d q t0 md ln) , mkMlnc l d (lncRtxs1 q) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify (MsgLNVotesOffer vs)} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lncRvot1 vs , RFLN.renameMap-ev-fwd (lnc-fire-rvot l d vs t0 md ln) , mkMlnc l d (lncRvot1 vs) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNRequestNext} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify MsgLNDone} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.sendLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.apiLNev l' d' m} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stBusy {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lnc-hstep l d LN.stDone step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncHead LN.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

decLNc-ev-prod-abs : (l : Link) (d : Dir) (pos : LNcPos)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {M : NetProc}
  → absLNc l d pos ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M
  → Σ[ pos′ ∈ LNcPos ] (decLNc l d pos ═[ ev (evl (evLabel X (ιLN e₁) a)) ]═► decLNc l d pos′)
      × (M ≡ absLNc l d pos′)
decLNc-ev-prod-abs l d (lncHead st) step with lnc-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
decLNc-ev-prod-abs l d (lncSil st) step with lnc-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decLNc-sil-step l d st) τ*-refl) f τ*-refl , m
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' recvLNBlockAnnouncement} {a} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ h
...     | yes refl = lncSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lnc-fire-rann1 l d h)) τ*-refl , mkMlnc l d (lncSil LN.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' recvLNBlockAnnouncement} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' recvLNBlockAnnouncement} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' sendLNRequestNext} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' sendLNDone} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' sendLNBlockAnnouncement} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' sendLNBlockOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' sendLNBlockTxsOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' sendLNVotesOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' recvLNBlockOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' recvLNBlockTxsOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.apiLNev l' d' recvLNVotesOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.sendLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRann1 h) {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' recvLNBlockOffer} {a} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ q
...     | yes refl = lncSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lnc-fire-roff1 l d q)) τ*-refl , mkMlnc l d (lncSil LN.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' recvLNBlockOffer} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' recvLNBlockOffer} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' sendLNRequestNext} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' sendLNDone} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' sendLNBlockAnnouncement} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' sendLNBlockOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' sendLNBlockTxsOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' sendLNVotesOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' recvLNBlockAnnouncement} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' recvLNBlockTxsOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.apiLNev l' d' recvLNVotesOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.sendLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRoff1 q) {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' recvLNBlockTxsOffer} {a} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ q
...     | yes refl = lncSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lnc-fire-rtxs1 l d q)) τ*-refl , mkMlnc l d (lncSil LN.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' recvLNBlockTxsOffer} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' recvLNBlockTxsOffer} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' sendLNRequestNext} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' sendLNDone} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' sendLNBlockAnnouncement} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' sendLNBlockOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' sendLNBlockTxsOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' sendLNVotesOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' recvLNBlockAnnouncement} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' recvLNBlockOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.apiLNev l' d' recvLNVotesOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.sendLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRtxs1 q) {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' recvLNVotesOffer} {a} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ LN.DecEq-ListVote ⦄ a vs
...     | yes refl = lncSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lnc-fire-rvot1 l d vs)) τ*-refl , mkMlnc l d (lncSil LN.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' recvLNVotesOffer} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' recvLNVotesOffer} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' sendLNRequestNext} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' sendLNDone} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' sendLNBlockAnnouncement} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' sendLNBlockOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' sendLNBlockTxsOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' sendLNVotesOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' recvLNBlockAnnouncement} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' recvLNBlockOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.apiLNev l' d' recvLNBlockTxsOffer} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.sendLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d (lncRvot1 vs) {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc (lncRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncReq1 {e₁ = LN.sendLN l' d'} {a} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncReq1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNRequestNext)
...     | yes refl = lncSil LN.stBusy , wev τ*-refl (RFLN.renameMap-ev-fwd (lnc-fire-wreq1 l d)) τ*-refl , mkMlnc l d (lncSil LN.stBusy) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncReq1 {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncReq1 {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncReq1 {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncReq1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncReq1 {e₁ = LN.apiLNev l' d' m} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncReq1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncReq1 {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncReq1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncDone1 {e₁ = LN.sendLN l' d'} {a} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncDone1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosNotify MsgLNDone)
...     | yes refl = lncSil LN.stDone , wev τ*-refl (RFLN.renameMap-ev-fwd (lnc-fire-wdone1 l d)) τ*-refl , mkMlnc l d (lncSil LN.stDone) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncDone1 {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncDone1 {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncDone1 {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncDone1 {e₁ = LN.apiLNev l' d' m} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNc-ev-prod-abs l d lncDone1 {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlnc l d) (coarsenLNc lncDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

------------------------------------------------------------------------
-- LN-SERVER backward production leaf.
------------------------------------------------------------------------
Tlns : Link → Dir → NS.Table NS.LNsPos
Tlns l d = record { isFin = NS.lnSfin ; nxt = NS.lnSnxt l d }
mkMlns : (l : Link) (d : Dir) (pos′ : LNsPos) {q′ : NS.LNsPos} {M : NetProc}
  → M ≡ tableSpec (Tlns l d) q′ → q′ ≡ coarsenLNs pos′ → M ≡ absLNs l d pos′
mkMlns l d pos′ Meq qeq = trans Meq (cong (tableSpec (Tlns l d)) qeq)

lns-hstep : (l : Link) (d : Dir) (st : LN.LNState)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {M : NetProc}
  → absLNs l d (lnsHead st) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M
  → Σ[ pos′ ∈ LNsPos ] (decLNs l d (lnsHead st) ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► decLNs l d pos′)
      × (M ≡ absLNs l d pos′)
lns-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNRequestNext} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lnsSil LN.stBusy , RFLN.renameMap-ev-fwd (lns-fire-idleReq l d t0 md ln) , mkMlns l d (lnsSil LN.stBusy) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = t0 , md , ln , leiosNotify MsgLNDone} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lnsDone1 , RFLN.renameMap-ev-fwd (lns-fire-idleDone l d t0 md ln) , mkMlns l d (lnsDone1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockAnnouncement _)} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockOffer _)} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNBlockTxsOffer _)} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosNotify (MsgLNVotesOffer _)} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , txSubmission x} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.receiveLN l' d'} {a = _ , _ , _ , leiosFetch x} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.sendLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.apiLNev l' d' m} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stIdle {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.apiLNev l' d' sendLNBlockAnnouncement} {a} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lnsWann1 a , RFLN.renameMap-ev-fwd (lns-fire-wann l d a) , mkMlns l d (lnsWann1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.apiLNev l' d' sendLNBlockOffer} {a} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lnsWoff1 a , RFLN.renameMap-ev-fwd (lns-fire-woff l d a) , mkMlns l d (lnsWoff1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.apiLNev l' d' sendLNBlockTxsOffer} {a} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lnsWtxs1 a , RFLN.renameMap-ev-fwd (lns-fire-wtxs l d a) , mkMlns l d (lnsWtxs1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.apiLNev l' d' sendLNVotesOffer} {a} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lnsWvot1 a , RFLN.renameMap-ev-fwd (lns-fire-wvot l d a) , mkMlns l d (lnsWvot1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.apiLNev l' d' sendLNRequestNext} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.apiLNev l' d' sendLNDone} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.apiLNev l' d' recvLNBlockAnnouncement} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.apiLNev l' d' recvLNBlockOffer} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.apiLNev l' d' recvLNBlockTxsOffer} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.apiLNev l' d' recvLNVotesOffer} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.sendLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stBusy {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stBusy)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lns-hstep l d LN.stDone step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsHead LN.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

decLNs-ev-prod-abs : (l : Link) (d : Dir) (pos : LNsPos)
    {X : Set 0ℓ} {e₁ : LN.LNEv X} {a : X} {M : NetProc}
  → absLNs l d pos ─[ ev (evl (evLabel X (ιLN e₁) a)) ]─► M
  → Σ[ pos′ ∈ LNsPos ] (decLNs l d pos ═[ ev (evl (evLabel X (ιLN e₁) a)) ]═► decLNs l d pos′)
      × (M ≡ absLNs l d pos′)
decLNs-ev-prod-abs l d (lnsHead st) step with lns-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
decLNs-ev-prod-abs l d (lnsSil st) step with lns-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decLNs-sil-step l d st) τ*-refl) f τ*-refl , m
decLNs-ev-prod-abs l d lnsDone1 {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs lnsDone1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lnsSil LN.stDone , wev τ*-refl (RFLN.renameMap-ev-fwd (lns-fire-sddone l d)) τ*-refl , mkMlns l d (lnsSil LN.stDone) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d lnsDone1 {e₁ = LN.sendLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs lnsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d lnsDone1 {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs lnsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d lnsDone1 {e₁ = LN.apiLNev l' d' m} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs lnsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWann1 h) {e₁ = LN.sendLN l' d'} {a} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWann1 h)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockAnnouncement h))
...     | yes refl = lnsSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lns-fire-wann1 l d h)) τ*-refl , mkMlns l d (lnsSil LN.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWann1 h) {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWann1 h) {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWann1 h) {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWann1 h) {e₁ = LN.apiLNev l' d' m} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWann1 h) {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWann1 h)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWoff1 q) {e₁ = LN.sendLN l' d'} {a} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWoff1 q)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockOffer q))
...     | yes refl = lnsSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lns-fire-woff1 l d q)) τ*-refl , mkMlns l d (lnsSil LN.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWoff1 q) {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWoff1 q) {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWoff1 q) {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWoff1 q) {e₁ = LN.apiLNev l' d' m} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWoff1 q) {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWoff1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWtxs1 q) {e₁ = LN.sendLN l' d'} {a} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWtxs1 q)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNBlockTxsOffer q))
...     | yes refl = lnsSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lns-fire-wtxs1 l d q)) τ*-refl , mkMlns l d (lnsSil LN.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWtxs1 q) {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWtxs1 q) {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWtxs1 q) {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWtxs1 q) {e₁ = LN.apiLNev l' d' m} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWtxs1 q) {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWtxs1 q)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWvot1 vs) {e₁ = LN.sendLN l' d'} {a} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWvot1 vs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosNotify (MsgLNVotesOffer vs))
...     | yes refl = lnsSil LN.stIdle , wev τ*-refl (RFLN.renameMap-ev-fwd (lns-fire-wvot1 l d vs)) τ*-refl , mkMlns l d (lnsSil LN.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWvot1 vs) {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWvot1 vs) {e₁ = LN.sendLN l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWvot1 vs) {e₁ = LN.receiveLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWvot1 vs) {e₁ = LN.apiLNev l' d' m} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLNs-ev-prod-abs l d (lnsWvot1 vs) {e₁ = LN.doneLN l' d'} step
  with tableSpec-ev-inv (Tlns l d) (coarsenLNs (lnsWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- LN-SECTION-END

-- LF-SECTION-BEGIN
------------------------------------------------------------------------
-- INERT PEER LeiosFetch (LF) — backward production leaves.
------------------------------------------------------------------------
decLFc-sil-step : (l : Link) (d : Dir) (st : LF.LFState)
  → decLFc l d (lfcSil st) ─[ τ ]─► decLFc l d (lfcHead st)
decLFc-sil-step l d st = sSil refl
decLFs-sil-step : (l : Link) (d : Dir) (st : LF.LFState)
  → decLFs l d (lfsSil st) ─[ τ ]─► decLFs l d (lfsHead st)
decLFs-sil-step l d st = sSil refl

-- CLIENT head api-sends (stIdle) — l,d gated, value carried (not gated)
lfc-fire-blkreq : (l : Link) (d : Dir) (pt : _)
  → decLFc-src l d (lfcHead LF.stIdle)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d sendLFBlockRequest) pt)) ]─►
    decLFc-src l d (lfcWblk1 pt)
lfc-fire-blkreq l d pt = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src l d (lfcHead LF.stIdle)))
          (_ , LF.apiLFev l d sendLFBlockRequest) pt ≡ just (decLFc-src l d (lfcWblk1 pt))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfc-fire-txsreq : (l : Link) (d : Dir) (pb : _)
  → decLFc-src l d (lfcHead LF.stIdle)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d sendLFBlockTxsRequest) pb)) ]─►
    decLFc-src l d (lfcWtxs1 pb)
lfc-fire-txsreq l d pb = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src l d (lfcHead LF.stIdle)))
          (_ , LF.apiLFev l d sendLFBlockTxsRequest) pb ≡ just (decLFc-src l d (lfcWtxs1 pb))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfc-fire-votreq : (l : Link) (d : Dir) (vs : _)
  → decLFc-src l d (lfcHead LF.stIdle)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d sendLFVotesRequest) vs)) ]─►
    decLFc-src l d (lfcWvot1 vs)
lfc-fire-votreq l d vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src l d (lfcHead LF.stIdle)))
          (_ , LF.apiLFev l d sendLFVotesRequest) vs ≡ just (decLFc-src l d (lfcWvot1 vs))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfc-fire-rngreq : (l : Link) (d : Dir) (r : _)
  → decLFc-src l d (lfcHead LF.stIdle)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d sendLFBlockRangeRequest) r)) ]─►
    decLFc-src l d (lfcWrng1 r)
lfc-fire-rngreq l d r = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src l d (lfcHead LF.stIdle)))
          (_ , LF.apiLFev l d sendLFBlockRangeRequest) r ≡ just (decLFc-src l d (lfcWrng1 r))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfc-fire-cdone : (l : Link) (d : Dir)
  → decLFc-src l d (lfcHead LF.stIdle)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d sendLFDone) U.tt)) ]─►
    decLFc-src l d (lfcDone1)
lfc-fire-cdone l d = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src l d (lfcHead LF.stIdle)))
          (_ , LF.apiLFev l d sendLFDone) U.tt ≡ just (decLFc-src l d (lfcDone1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- CLIENT head receives (stBlock/stBlockTxs/stVotes/stBlockRange) — l,d gated
lfc-fire-rblk : (l : Link) (d : Dir) (b : _) (t0 : _) (md : _) (ln : _)
  → decLFc-src l d (lfcHead LF.stBlock)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFBlock b)))) ]─►
    decLFc-src l d (lfcRblk1 b)
lfc-fire-rblk l d b t0 md ln = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src l d (lfcHead LF.stBlock)))
          (_ , LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFBlock b)) ≡ just (decLFc-src l d (lfcRblk1 b))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfc-fire-rbtx : (l : Link) (d : Dir) (ts : _) (t0 : _) (md : _) (ln : _)
  → decLFc-src l d (lfcHead LF.stBlockTxs)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFBlockTxs ts)))) ]─►
    decLFc-src l d (lfcRbtx1 ts)
lfc-fire-rbtx l d ts t0 md ln = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src l d (lfcHead LF.stBlockTxs)))
          (_ , LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFBlockTxs ts)) ≡ just (decLFc-src l d (lfcRbtx1 ts))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfc-fire-rvot : (l : Link) (d : Dir) (vs : _) (t0 : _) (md : _) (ln : _)
  → decLFc-src l d (lfcHead LF.stVotes)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFVoteDelivery vs)))) ]─►
    decLFc-src l d (lfcRvot1 vs)
lfc-fire-rvot l d vs t0 md ln = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src l d (lfcHead LF.stVotes)))
          (_ , LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFVoteDelivery vs)) ≡ just (decLFc-src l d (lfcRvot1 vs))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfc-fire-rnext : (l : Link) (d : Dir) (b : _) (ts : _) (t0 : _) (md : _) (ln : _)
  → decLFc-src l d (lfcHead LF.stBlockRange)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)))) ]─►
    decLFc-src l d (lfcRnext1 b ts)
lfc-fire-rnext l d b ts t0 md ln = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src l d (lfcHead LF.stBlockRange)))
          (_ , LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ just (decLFc-src l d (lfcRnext1 b ts))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfc-fire-rlast : (l : Link) (d : Dir) (b : _) (ts : _) (t0 : _) (md : _) (ln : _)
  → decLFc-src l d (lfcHead LF.stBlockRange)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)))) ]─►
    decLFc-src l d (lfcRlast1 b ts)
lfc-fire-rlast l d b ts t0 md ln = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src l d (lfcHead LF.stBlockRange)))
          (_ , LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ just (decLFc-src l d (lfcRlast1 b ts))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- CLIENT api-emit mids — Fin-enum + value gate
lfc-fire-rblk1 : (l : Link) (d : Dir) (b : _)
  → decLFc-src l d (lfcRblk1 b)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d recvLFBlock) b)) ]─►
    decLFc-src l d (lfcSil LF.stIdle)
lfc-fire-rblk1 (zero) lo b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) lo (lfcRblk1 b)))
          (_ , LF.apiLFev (zero) lo recvLFBlock) b ≡ just (decLFc-src (zero) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
lfc-fire-rblk1 (zero) hi b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) hi (lfcRblk1 b)))
          (_ , LF.apiLFev (zero) hi recvLFBlock) b ≡ just (decLFc-src (zero) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
lfc-fire-rblk1 (suc zero) lo b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) lo (lfcRblk1 b)))
          (_ , LF.apiLFev (suc zero) lo recvLFBlock) b ≡ just (decLFc-src (suc zero) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
lfc-fire-rblk1 (suc zero) hi b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) hi (lfcRblk1 b)))
          (_ , LF.apiLFev (suc zero) hi recvLFBlock) b ≡ just (decLFc-src (suc zero) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
lfc-fire-rblk1 (suc (suc zero)) lo b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) lo (lfcRblk1 b)))
          (_ , LF.apiLFev (suc (suc zero)) lo recvLFBlock) b ≡ just (decLFc-src (suc (suc zero)) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
lfc-fire-rblk1 (suc (suc zero)) hi b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) hi (lfcRblk1 b)))
          (_ , LF.apiLFev (suc (suc zero)) hi recvLFBlock) b ≡ just (decLFc-src (suc (suc zero)) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
lfc-fire-rblk1 (suc (suc (suc zero))) lo b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) lo (lfcRblk1 b)))
          (_ , LF.apiLFev (suc (suc (suc zero))) lo recvLFBlock) b ≡ just (decLFc-src (suc (suc (suc zero))) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
lfc-fire-rblk1 (suc (suc (suc zero))) hi b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) hi (lfcRblk1 b)))
          (_ , LF.apiLFev (suc (suc (suc zero))) hi recvLFBlock) b ≡ just (decLFc-src (suc (suc (suc zero))) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ decBlock ⦄ b = refl
lfc-fire-rbtx1 : (l : Link) (d : Dir) (ts : _)
  → decLFc-src l d (lfcRbtx1 ts)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d recvLFBlockTxs) ts)) ]─►
    decLFc-src l d (lfcSil LF.stIdle)
lfc-fire-rbtx1 (zero) lo ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) lo (lfcRbtx1 ts)))
          (_ , LF.apiLFev (zero) lo recvLFBlockTxs) ts ≡ just (decLFc-src (zero) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ ts = refl
lfc-fire-rbtx1 (zero) hi ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) hi (lfcRbtx1 ts)))
          (_ , LF.apiLFev (zero) hi recvLFBlockTxs) ts ≡ just (decLFc-src (zero) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ ts = refl
lfc-fire-rbtx1 (suc zero) lo ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) lo (lfcRbtx1 ts)))
          (_ , LF.apiLFev (suc zero) lo recvLFBlockTxs) ts ≡ just (decLFc-src (suc zero) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ ts = refl
lfc-fire-rbtx1 (suc zero) hi ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) hi (lfcRbtx1 ts)))
          (_ , LF.apiLFev (suc zero) hi recvLFBlockTxs) ts ≡ just (decLFc-src (suc zero) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ ts = refl
lfc-fire-rbtx1 (suc (suc zero)) lo ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) lo (lfcRbtx1 ts)))
          (_ , LF.apiLFev (suc (suc zero)) lo recvLFBlockTxs) ts ≡ just (decLFc-src (suc (suc zero)) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ ts = refl
lfc-fire-rbtx1 (suc (suc zero)) hi ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) hi (lfcRbtx1 ts)))
          (_ , LF.apiLFev (suc (suc zero)) hi recvLFBlockTxs) ts ≡ just (decLFc-src (suc (suc zero)) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ ts = refl
lfc-fire-rbtx1 (suc (suc (suc zero))) lo ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) lo (lfcRbtx1 ts)))
          (_ , LF.apiLFev (suc (suc (suc zero))) lo recvLFBlockTxs) ts ≡ just (decLFc-src (suc (suc (suc zero))) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ ts = refl
lfc-fire-rbtx1 (suc (suc (suc zero))) hi ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) hi (lfcRbtx1 ts)))
          (_ , LF.apiLFev (suc (suc (suc zero))) hi recvLFBlockTxs) ts ≡ just (decLFc-src (suc (suc (suc zero))) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ ts = refl
lfc-fire-rvot1 : (l : Link) (d : Dir) (vs : _)
  → decLFc-src l d (lfcRvot1 vs)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d recvLFVoteDelivery) vs)) ]─►
    decLFc-src l d (lfcSil LF.stIdle)
lfc-fire-rvot1 (zero) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) lo (lfcRvot1 vs)))
          (_ , LF.apiLFev (zero) lo recvLFVoteDelivery) vs ≡ just (decLFc-src (zero) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ vs = refl
lfc-fire-rvot1 (zero) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) hi (lfcRvot1 vs)))
          (_ , LF.apiLFev (zero) hi recvLFVoteDelivery) vs ≡ just (decLFc-src (zero) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ vs = refl
lfc-fire-rvot1 (suc zero) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) lo (lfcRvot1 vs)))
          (_ , LF.apiLFev (suc zero) lo recvLFVoteDelivery) vs ≡ just (decLFc-src (suc zero) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ vs = refl
lfc-fire-rvot1 (suc zero) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) hi (lfcRvot1 vs)))
          (_ , LF.apiLFev (suc zero) hi recvLFVoteDelivery) vs ≡ just (decLFc-src (suc zero) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ vs = refl
lfc-fire-rvot1 (suc (suc zero)) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) lo (lfcRvot1 vs)))
          (_ , LF.apiLFev (suc (suc zero)) lo recvLFVoteDelivery) vs ≡ just (decLFc-src (suc (suc zero)) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ vs = refl
lfc-fire-rvot1 (suc (suc zero)) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) hi (lfcRvot1 vs)))
          (_ , LF.apiLFev (suc (suc zero)) hi recvLFVoteDelivery) vs ≡ just (decLFc-src (suc (suc zero)) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ vs = refl
lfc-fire-rvot1 (suc (suc (suc zero))) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) lo (lfcRvot1 vs)))
          (_ , LF.apiLFev (suc (suc (suc zero))) lo recvLFVoteDelivery) vs ≡ just (decLFc-src (suc (suc (suc zero))) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ vs = refl
lfc-fire-rvot1 (suc (suc (suc zero))) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) hi (lfcRvot1 vs)))
          (_ , LF.apiLFev (suc (suc (suc zero))) hi recvLFVoteDelivery) vs ≡ just (decLFc-src (suc (suc (suc zero))) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ DecEqI.DecEq-List ⦄ vs = refl
lfc-fire-rnext1 : (l : Link) (d : Dir) (b : _) (ts : _)
  → decLFc-src l d (lfcRnext1 b ts)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d recvLFRangeBlock) (b , ts))) ]─►
    decLFc-src l d (lfcSil LF.stBlockRange)
lfc-fire-rnext1 (zero) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) lo (lfcRnext1 b ts)))
          (_ , LF.apiLFev (zero) lo recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (zero) lo (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rnext1 (zero) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) hi (lfcRnext1 b ts)))
          (_ , LF.apiLFev (zero) hi recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (zero) hi (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rnext1 (suc zero) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) lo (lfcRnext1 b ts)))
          (_ , LF.apiLFev (suc zero) lo recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc zero) lo (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rnext1 (suc zero) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) hi (lfcRnext1 b ts)))
          (_ , LF.apiLFev (suc zero) hi recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc zero) hi (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rnext1 (suc (suc zero)) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) lo (lfcRnext1 b ts)))
          (_ , LF.apiLFev (suc (suc zero)) lo recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc (suc zero)) lo (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rnext1 (suc (suc zero)) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) hi (lfcRnext1 b ts)))
          (_ , LF.apiLFev (suc (suc zero)) hi recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc (suc zero)) hi (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rnext1 (suc (suc (suc zero))) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) lo (lfcRnext1 b ts)))
          (_ , LF.apiLFev (suc (suc (suc zero))) lo recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc (suc (suc zero))) lo (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rnext1 (suc (suc (suc zero))) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) hi (lfcRnext1 b ts)))
          (_ , LF.apiLFev (suc (suc (suc zero))) hi recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc (suc (suc zero))) hi (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rlast1 : (l : Link) (d : Dir) (b : _) (ts : _)
  → decLFc-src l d (lfcRlast1 b ts)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d recvLFRangeBlock) (b , ts))) ]─►
    decLFc-src l d (lfcSil LF.stIdle)
lfc-fire-rlast1 (zero) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) lo (lfcRlast1 b ts)))
          (_ , LF.apiLFev (zero) lo recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (zero) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rlast1 (zero) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) hi (lfcRlast1 b ts)))
          (_ , LF.apiLFev (zero) hi recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (zero) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rlast1 (suc zero) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) lo (lfcRlast1 b ts)))
          (_ , LF.apiLFev (suc zero) lo recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc zero) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rlast1 (suc zero) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) hi (lfcRlast1 b ts)))
          (_ , LF.apiLFev (suc zero) hi recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc zero) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rlast1 (suc (suc zero)) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) lo (lfcRlast1 b ts)))
          (_ , LF.apiLFev (suc (suc zero)) lo recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc (suc zero)) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rlast1 (suc (suc zero)) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) hi (lfcRlast1 b ts)))
          (_ , LF.apiLFev (suc (suc zero)) hi recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc (suc zero)) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rlast1 (suc (suc (suc zero))) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) lo (lfcRlast1 b ts)))
          (_ , LF.apiLFev (suc (suc (suc zero))) lo recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc (suc (suc zero))) lo (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl
lfc-fire-rlast1 (suc (suc (suc zero))) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) hi (lfcRlast1 b ts)))
          (_ , LF.apiLFev (suc (suc (suc zero))) hi recvLFRangeBlock) (b , ts) ≡ just (decLFc-src (suc (suc (suc zero))) hi (lfcSil LF.stIdle))
    o rewrite ≟-yes-refl ⦃ NS.DecEq-Block×ListTx ⦄ (b , ts) = refl

-- CLIENT wire-send mids — Fin-enum + Payload gate (FromInitiator)
lfc-fire-wblk1 : (l : Link) (d : Dir) (pt : _)
  → decLFc-src l d (lfcWblk1 pt)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.sendLF l d) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)))) ]─►
    decLFc-src l d (lfcSil LF.stBlock)
lfc-fire-wblk1 (zero) lo pt = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) lo (lfcWblk1 pt)))
          (_ , LF.sendLF (zero) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) ≡ just (decLFc-src (zero) lo (lfcSil LF.stBlock))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) = refl
lfc-fire-wblk1 (zero) hi pt = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) hi (lfcWblk1 pt)))
          (_ , LF.sendLF (zero) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) ≡ just (decLFc-src (zero) hi (lfcSil LF.stBlock))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) = refl
lfc-fire-wblk1 (suc zero) lo pt = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) lo (lfcWblk1 pt)))
          (_ , LF.sendLF (suc zero) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) ≡ just (decLFc-src (suc zero) lo (lfcSil LF.stBlock))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) = refl
lfc-fire-wblk1 (suc zero) hi pt = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) hi (lfcWblk1 pt)))
          (_ , LF.sendLF (suc zero) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) ≡ just (decLFc-src (suc zero) hi (lfcSil LF.stBlock))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) = refl
lfc-fire-wblk1 (suc (suc zero)) lo pt = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) lo (lfcWblk1 pt)))
          (_ , LF.sendLF (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) ≡ just (decLFc-src (suc (suc zero)) lo (lfcSil LF.stBlock))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) = refl
lfc-fire-wblk1 (suc (suc zero)) hi pt = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) hi (lfcWblk1 pt)))
          (_ , LF.sendLF (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) ≡ just (decLFc-src (suc (suc zero)) hi (lfcSil LF.stBlock))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) = refl
lfc-fire-wblk1 (suc (suc (suc zero))) lo pt = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) lo (lfcWblk1 pt)))
          (_ , LF.sendLF (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) ≡ just (decLFc-src (suc (suc (suc zero))) lo (lfcSil LF.stBlock))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) = refl
lfc-fire-wblk1 (suc (suc (suc zero))) hi pt = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) hi (lfcWblk1 pt)))
          (_ , LF.sendLF (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) ≡ just (decLFc-src (suc (suc (suc zero))) hi (lfcSil LF.stBlock))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt)) = refl
lfc-fire-wtxs1 : (l : Link) (d : Dir) (pt : _) (bm : _)
  → decLFc-src l d (lfcWtxs1 (pt , bm))
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.sendLF l d) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)))) ]─►
    decLFc-src l d (lfcSil LF.stBlockTxs)
lfc-fire-wtxs1 (zero) lo pt bm = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) lo (lfcWtxs1 (pt , bm))))
          (_ , LF.sendLF (zero) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ just (decLFc-src (zero) lo (lfcSil LF.stBlockTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) = refl
lfc-fire-wtxs1 (zero) hi pt bm = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) hi (lfcWtxs1 (pt , bm))))
          (_ , LF.sendLF (zero) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ just (decLFc-src (zero) hi (lfcSil LF.stBlockTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) = refl
lfc-fire-wtxs1 (suc zero) lo pt bm = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) lo (lfcWtxs1 (pt , bm))))
          (_ , LF.sendLF (suc zero) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ just (decLFc-src (suc zero) lo (lfcSil LF.stBlockTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) = refl
lfc-fire-wtxs1 (suc zero) hi pt bm = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) hi (lfcWtxs1 (pt , bm))))
          (_ , LF.sendLF (suc zero) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ just (decLFc-src (suc zero) hi (lfcSil LF.stBlockTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) = refl
lfc-fire-wtxs1 (suc (suc zero)) lo pt bm = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) lo (lfcWtxs1 (pt , bm))))
          (_ , LF.sendLF (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ just (decLFc-src (suc (suc zero)) lo (lfcSil LF.stBlockTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) = refl
lfc-fire-wtxs1 (suc (suc zero)) hi pt bm = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) hi (lfcWtxs1 (pt , bm))))
          (_ , LF.sendLF (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ just (decLFc-src (suc (suc zero)) hi (lfcSil LF.stBlockTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) = refl
lfc-fire-wtxs1 (suc (suc (suc zero))) lo pt bm = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) lo (lfcWtxs1 (pt , bm))))
          (_ , LF.sendLF (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ just (decLFc-src (suc (suc (suc zero))) lo (lfcSil LF.stBlockTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) = refl
lfc-fire-wtxs1 (suc (suc (suc zero))) hi pt bm = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) hi (lfcWtxs1 (pt , bm))))
          (_ , LF.sendLF (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ just (decLFc-src (suc (suc (suc zero))) hi (lfcSil LF.stBlockTxs))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm)) = refl
lfc-fire-wvot1 : (l : Link) (d : Dir) (vs : _)
  → decLFc-src l d (lfcWvot1 vs)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.sendLF l d) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)))) ]─►
    decLFc-src l d (lfcSil LF.stVotes)
lfc-fire-wvot1 (zero) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) lo (lfcWvot1 vs)))
          (_ , LF.sendLF (zero) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) ≡ just (decLFc-src (zero) lo (lfcSil LF.stVotes))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) = refl
lfc-fire-wvot1 (zero) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) hi (lfcWvot1 vs)))
          (_ , LF.sendLF (zero) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) ≡ just (decLFc-src (zero) hi (lfcSil LF.stVotes))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) = refl
lfc-fire-wvot1 (suc zero) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) lo (lfcWvot1 vs)))
          (_ , LF.sendLF (suc zero) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) ≡ just (decLFc-src (suc zero) lo (lfcSil LF.stVotes))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) = refl
lfc-fire-wvot1 (suc zero) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) hi (lfcWvot1 vs)))
          (_ , LF.sendLF (suc zero) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) ≡ just (decLFc-src (suc zero) hi (lfcSil LF.stVotes))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) = refl
lfc-fire-wvot1 (suc (suc zero)) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) lo (lfcWvot1 vs)))
          (_ , LF.sendLF (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) ≡ just (decLFc-src (suc (suc zero)) lo (lfcSil LF.stVotes))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) = refl
lfc-fire-wvot1 (suc (suc zero)) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) hi (lfcWvot1 vs)))
          (_ , LF.sendLF (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) ≡ just (decLFc-src (suc (suc zero)) hi (lfcSil LF.stVotes))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) = refl
lfc-fire-wvot1 (suc (suc (suc zero))) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) lo (lfcWvot1 vs)))
          (_ , LF.sendLF (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) ≡ just (decLFc-src (suc (suc (suc zero))) lo (lfcSil LF.stVotes))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) = refl
lfc-fire-wvot1 (suc (suc (suc zero))) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) hi (lfcWvot1 vs)))
          (_ , LF.sendLF (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) ≡ just (decLFc-src (suc (suc (suc zero))) hi (lfcSil LF.stVotes))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs)) = refl
lfc-fire-wrng1 : (l : Link) (d : Dir) (r : _)
  → decLFc-src l d (lfcWrng1 r)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.sendLF l d) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)))) ]─►
    decLFc-src l d (lfcSil LF.stBlockRange)
lfc-fire-wrng1 (zero) lo r = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) lo (lfcWrng1 r)))
          (_ , LF.sendLF (zero) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) ≡ just (decLFc-src (zero) lo (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) = refl
lfc-fire-wrng1 (zero) hi r = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) hi (lfcWrng1 r)))
          (_ , LF.sendLF (zero) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) ≡ just (decLFc-src (zero) hi (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) = refl
lfc-fire-wrng1 (suc zero) lo r = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) lo (lfcWrng1 r)))
          (_ , LF.sendLF (suc zero) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) ≡ just (decLFc-src (suc zero) lo (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) = refl
lfc-fire-wrng1 (suc zero) hi r = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) hi (lfcWrng1 r)))
          (_ , LF.sendLF (suc zero) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) ≡ just (decLFc-src (suc zero) hi (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) = refl
lfc-fire-wrng1 (suc (suc zero)) lo r = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) lo (lfcWrng1 r)))
          (_ , LF.sendLF (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) ≡ just (decLFc-src (suc (suc zero)) lo (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) = refl
lfc-fire-wrng1 (suc (suc zero)) hi r = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) hi (lfcWrng1 r)))
          (_ , LF.sendLF (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) ≡ just (decLFc-src (suc (suc zero)) hi (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) = refl
lfc-fire-wrng1 (suc (suc (suc zero))) lo r = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) lo (lfcWrng1 r)))
          (_ , LF.sendLF (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) ≡ just (decLFc-src (suc (suc (suc zero))) lo (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) = refl
lfc-fire-wrng1 (suc (suc (suc zero))) hi r = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) hi (lfcWrng1 r)))
          (_ , LF.sendLF (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) ≡ just (decLFc-src (suc (suc (suc zero))) hi (lfcSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r)) = refl
lfc-fire-wdone1 : (l : Link) (d : Dir)
  → decLFc-src l d (lfcDone1)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.sendLF l d) (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone))) ]─►
    decLFc-src l d (lfcSil LF.stDone)
lfc-fire-wdone1 (zero) lo = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) lo (lfcDone1)))
          (_ , LF.sendLF (zero) lo) (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) ≡ just (decLFc-src (zero) lo (lfcSil LF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) = refl
lfc-fire-wdone1 (zero) hi = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (zero) hi (lfcDone1)))
          (_ , LF.sendLF (zero) hi) (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) ≡ just (decLFc-src (zero) hi (lfcSil LF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) = refl
lfc-fire-wdone1 (suc zero) lo = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) lo (lfcDone1)))
          (_ , LF.sendLF (suc zero) lo) (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) ≡ just (decLFc-src (suc zero) lo (lfcSil LF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) = refl
lfc-fire-wdone1 (suc zero) hi = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc zero) hi (lfcDone1)))
          (_ , LF.sendLF (suc zero) hi) (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) ≡ just (decLFc-src (suc zero) hi (lfcSil LF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) = refl
lfc-fire-wdone1 (suc (suc zero)) lo = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) lo (lfcDone1)))
          (_ , LF.sendLF (suc (suc zero)) lo) (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) ≡ just (decLFc-src (suc (suc zero)) lo (lfcSil LF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) = refl
lfc-fire-wdone1 (suc (suc zero)) hi = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc zero)) hi (lfcDone1)))
          (_ , LF.sendLF (suc (suc zero)) hi) (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) ≡ just (decLFc-src (suc (suc zero)) hi (lfcSil LF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) = refl
lfc-fire-wdone1 (suc (suc (suc zero))) lo = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) lo (lfcDone1)))
          (_ , LF.sendLF (suc (suc (suc zero))) lo) (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) ≡ just (decLFc-src (suc (suc (suc zero))) lo (lfcSil LF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) = refl
lfc-fire-wdone1 (suc (suc (suc zero))) hi = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFc-src (suc (suc (suc zero))) hi (lfcDone1)))
          (_ , LF.sendLF (suc (suc (suc zero))) hi) (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) ≡ just (decLFc-src (suc (suc (suc zero))) hi (lfcSil LF.stDone))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone) = refl

-- SERVER head receives (stIdle) — l,d gated (request value carried, discarded)
lfs-fire-ireq-blk : (l : Link) (d : Dir) (pt : _) (t0 : _) (md : _) (ln : _)
  → decLFs-src l d (lfsHead LF.stIdle)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFBlockRequest pt)))) ]─►
    decLFs-src l d (lfsSil LF.stBlock)
lfs-fire-ireq-blk l d pt t0 md ln = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src l d (lfsHead LF.stIdle)))
          (_ , LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFBlockRequest pt)) ≡ just (decLFs-src l d (lfsSil LF.stBlock))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfs-fire-ireq-txs : (l : Link) (d : Dir) (pt : _) (bm : _) (t0 : _) (md : _) (ln : _)
  → decLFs-src l d (lfsHead LF.stIdle)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFBlockTxsRequest pt bm)))) ]─►
    decLFs-src l d (lfsSil LF.stBlockTxs)
lfs-fire-ireq-txs l d pt bm t0 md ln = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src l d (lfsHead LF.stIdle)))
          (_ , LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFBlockTxsRequest pt bm)) ≡ just (decLFs-src l d (lfsSil LF.stBlockTxs))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfs-fire-ireq-vot : (l : Link) (d : Dir) (vs : _) (t0 : _) (md : _) (ln : _)
  → decLFs-src l d (lfsHead LF.stIdle)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFVotesRequest vs)))) ]─►
    decLFs-src l d (lfsSil LF.stVotes)
lfs-fire-ireq-vot l d vs t0 md ln = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src l d (lfsHead LF.stIdle)))
          (_ , LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFVotesRequest vs)) ≡ just (decLFs-src l d (lfsSil LF.stVotes))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfs-fire-ireq-rng : (l : Link) (d : Dir) (r : _) (t0 : _) (md : _) (ln : _)
  → decLFs-src l d (lfsHead LF.stIdle)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFBlockRangeRequest r)))) ]─►
    decLFs-src l d (lfsSil LF.stBlockRange)
lfs-fire-ireq-rng l d r t0 md ln = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src l d (lfsHead LF.stIdle)))
          (_ , LF.receiveLF l d) (t0 , md , ln , leiosFetch (MsgLFBlockRangeRequest r)) ≡ just (decLFs-src l d (lfsSil LF.stBlockRange))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfs-fire-idone : (l : Link) (d : Dir) (t0 : _) (md : _) (ln : _)
  → decLFs-src l d (lfsHead LF.stIdle)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.receiveLF l d) (t0 , md , ln , leiosFetch MsgLFDone))) ]─►
    decLFs-src l d (lfsDone1)
lfs-fire-idone l d t0 md ln = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src l d (lfsHead LF.stIdle)))
          (_ , LF.receiveLF l d) (t0 , md , ln , leiosFetch MsgLFDone) ≡ just (decLFs-src l d (lfsDone1))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- SERVER head api-sends (stBlock/stBlockTxs/stVotes/stBlockRange) — l,d gated, value carried
lfs-fire-sblk : (l : Link) (d : Dir) (a : _)
  → decLFs-src l d (lfsHead LF.stBlock)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d sendLFBlock) a)) ]─►
    decLFs-src l d (lfsWblk1 a)
lfs-fire-sblk l d a = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src l d (lfsHead LF.stBlock)))
          (_ , LF.apiLFev l d sendLFBlock) a ≡ just (decLFs-src l d (lfsWblk1 a))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfs-fire-stxs : (l : Link) (d : Dir) (a : _)
  → decLFs-src l d (lfsHead LF.stBlockTxs)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d sendLFBlockTxs) a)) ]─►
    decLFs-src l d (lfsWtxs1 a)
lfs-fire-stxs l d a = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src l d (lfsHead LF.stBlockTxs)))
          (_ , LF.apiLFev l d sendLFBlockTxs) a ≡ just (decLFs-src l d (lfsWtxs1 a))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfs-fire-svot : (l : Link) (d : Dir) (a : _)
  → decLFs-src l d (lfsHead LF.stVotes)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d sendLFVoteDelivery) a)) ]─►
    decLFs-src l d (lfsWvot1 a)
lfs-fire-svot l d a = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src l d (lfsHead LF.stVotes)))
          (_ , LF.apiLFev l d sendLFVoteDelivery) a ≡ just (decLFs-src l d (lfsWvot1 a))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfs-fire-snext : (l : Link) (d : Dir) (a : _)
  → decLFs-src l d (lfsHead LF.stBlockRange)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d sendLFNextBlockAndTxsInRange) a)) ]─►
    decLFs-src l d (lfsWnext1 a)
lfs-fire-snext l d a = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src l d (lfsHead LF.stBlockRange)))
          (_ , LF.apiLFev l d sendLFNextBlockAndTxsInRange) a ≡ just (decLFs-src l d (lfsWnext1 a))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl
lfs-fire-slast : (l : Link) (d : Dir) (a : _)
  → decLFs-src l d (lfsHead LF.stBlockRange)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.apiLFev l d sendLFLastBlockAndTxsInRange) a)) ]─►
    decLFs-src l d (lfsWlast1 a)
lfs-fire-slast l d a = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src l d (lfsHead LF.stBlockRange)))
          (_ , LF.apiLFev l d sendLFLastBlockAndTxsInRange) a ≡ just (decLFs-src l d (lfsWlast1 a))
    o rewrite ≟-yes-refl l | ≟-yes-refl d = refl

-- SERVER done mid lfsDone1 → lfsSil stDone (doneLF, ⊤) — Fin-enum
lfs-fire-sddone : (l : Link) (d : Dir)
  → decLFs-src l d lfsDone1
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.doneLF l d) U.tt)) ]─►
    decLFs-src l d (lfsSil LF.stDone)
lfs-fire-sddone (zero) lo = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) lo lfsDone1))
          (_ , LF.doneLF (zero) lo) U.tt ≡ just (decLFs-src (zero) lo (lfsSil LF.stDone))
    o = refl
lfs-fire-sddone (zero) hi = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) hi lfsDone1))
          (_ , LF.doneLF (zero) hi) U.tt ≡ just (decLFs-src (zero) hi (lfsSil LF.stDone))
    o = refl
lfs-fire-sddone (suc zero) lo = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) lo lfsDone1))
          (_ , LF.doneLF (suc zero) lo) U.tt ≡ just (decLFs-src (suc zero) lo (lfsSil LF.stDone))
    o = refl
lfs-fire-sddone (suc zero) hi = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) hi lfsDone1))
          (_ , LF.doneLF (suc zero) hi) U.tt ≡ just (decLFs-src (suc zero) hi (lfsSil LF.stDone))
    o = refl
lfs-fire-sddone (suc (suc zero)) lo = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) lo lfsDone1))
          (_ , LF.doneLF (suc (suc zero)) lo) U.tt ≡ just (decLFs-src (suc (suc zero)) lo (lfsSil LF.stDone))
    o = refl
lfs-fire-sddone (suc (suc zero)) hi = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) hi lfsDone1))
          (_ , LF.doneLF (suc (suc zero)) hi) U.tt ≡ just (decLFs-src (suc (suc zero)) hi (lfsSil LF.stDone))
    o = refl
lfs-fire-sddone (suc (suc (suc zero))) lo = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) lo lfsDone1))
          (_ , LF.doneLF (suc (suc (suc zero))) lo) U.tt ≡ just (decLFs-src (suc (suc (suc zero))) lo (lfsSil LF.stDone))
    o = refl
lfs-fire-sddone (suc (suc (suc zero))) hi = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) hi lfsDone1))
          (_ , LF.doneLF (suc (suc (suc zero))) hi) U.tt ≡ just (decLFs-src (suc (suc (suc zero))) hi (lfsSil LF.stDone))
    o = refl

-- SERVER wire-send mids — Fin-enum + Payload gate (FromResponder)
lfs-fire-wblk1 : (l : Link) (d : Dir) (b : _)
  → decLFs-src l d (lfsWblk1 b)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.sendLF l d) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)))) ]─►
    decLFs-src l d (lfsSil LF.stIdle)
lfs-fire-wblk1 (zero) lo b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) lo (lfsWblk1 b)))
          (_ , LF.sendLF (zero) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) ≡ just (decLFs-src (zero) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) = refl
lfs-fire-wblk1 (zero) hi b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) hi (lfsWblk1 b)))
          (_ , LF.sendLF (zero) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) ≡ just (decLFs-src (zero) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) = refl
lfs-fire-wblk1 (suc zero) lo b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) lo (lfsWblk1 b)))
          (_ , LF.sendLF (suc zero) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) ≡ just (decLFs-src (suc zero) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) = refl
lfs-fire-wblk1 (suc zero) hi b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) hi (lfsWblk1 b)))
          (_ , LF.sendLF (suc zero) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) ≡ just (decLFs-src (suc zero) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) = refl
lfs-fire-wblk1 (suc (suc zero)) lo b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) lo (lfsWblk1 b)))
          (_ , LF.sendLF (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) ≡ just (decLFs-src (suc (suc zero)) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) = refl
lfs-fire-wblk1 (suc (suc zero)) hi b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) hi (lfsWblk1 b)))
          (_ , LF.sendLF (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) ≡ just (decLFs-src (suc (suc zero)) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) = refl
lfs-fire-wblk1 (suc (suc (suc zero))) lo b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) lo (lfsWblk1 b)))
          (_ , LF.sendLF (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) ≡ just (decLFs-src (suc (suc (suc zero))) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) = refl
lfs-fire-wblk1 (suc (suc (suc zero))) hi b = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) hi (lfsWblk1 b)))
          (_ , LF.sendLF (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) ≡ just (decLFs-src (suc (suc (suc zero))) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b)) = refl
lfs-fire-wtxs1 : (l : Link) (d : Dir) (ts : _)
  → decLFs-src l d (lfsWtxs1 ts)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.sendLF l d) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)))) ]─►
    decLFs-src l d (lfsSil LF.stIdle)
lfs-fire-wtxs1 (zero) lo ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) lo (lfsWtxs1 ts)))
          (_ , LF.sendLF (zero) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) ≡ just (decLFs-src (zero) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) = refl
lfs-fire-wtxs1 (zero) hi ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) hi (lfsWtxs1 ts)))
          (_ , LF.sendLF (zero) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) ≡ just (decLFs-src (zero) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) = refl
lfs-fire-wtxs1 (suc zero) lo ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) lo (lfsWtxs1 ts)))
          (_ , LF.sendLF (suc zero) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) ≡ just (decLFs-src (suc zero) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) = refl
lfs-fire-wtxs1 (suc zero) hi ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) hi (lfsWtxs1 ts)))
          (_ , LF.sendLF (suc zero) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) ≡ just (decLFs-src (suc zero) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) = refl
lfs-fire-wtxs1 (suc (suc zero)) lo ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) lo (lfsWtxs1 ts)))
          (_ , LF.sendLF (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) ≡ just (decLFs-src (suc (suc zero)) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) = refl
lfs-fire-wtxs1 (suc (suc zero)) hi ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) hi (lfsWtxs1 ts)))
          (_ , LF.sendLF (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) ≡ just (decLFs-src (suc (suc zero)) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) = refl
lfs-fire-wtxs1 (suc (suc (suc zero))) lo ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) lo (lfsWtxs1 ts)))
          (_ , LF.sendLF (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) ≡ just (decLFs-src (suc (suc (suc zero))) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) = refl
lfs-fire-wtxs1 (suc (suc (suc zero))) hi ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) hi (lfsWtxs1 ts)))
          (_ , LF.sendLF (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) ≡ just (decLFs-src (suc (suc (suc zero))) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts)) = refl
lfs-fire-wvot1 : (l : Link) (d : Dir) (vs : _)
  → decLFs-src l d (lfsWvot1 vs)
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.sendLF l d) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)))) ]─►
    decLFs-src l d (lfsSil LF.stIdle)
lfs-fire-wvot1 (zero) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) lo (lfsWvot1 vs)))
          (_ , LF.sendLF (zero) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) ≡ just (decLFs-src (zero) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) = refl
lfs-fire-wvot1 (zero) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) hi (lfsWvot1 vs)))
          (_ , LF.sendLF (zero) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) ≡ just (decLFs-src (zero) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) = refl
lfs-fire-wvot1 (suc zero) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) lo (lfsWvot1 vs)))
          (_ , LF.sendLF (suc zero) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) ≡ just (decLFs-src (suc zero) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) = refl
lfs-fire-wvot1 (suc zero) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) hi (lfsWvot1 vs)))
          (_ , LF.sendLF (suc zero) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) ≡ just (decLFs-src (suc zero) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) = refl
lfs-fire-wvot1 (suc (suc zero)) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) lo (lfsWvot1 vs)))
          (_ , LF.sendLF (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) ≡ just (decLFs-src (suc (suc zero)) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) = refl
lfs-fire-wvot1 (suc (suc zero)) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) hi (lfsWvot1 vs)))
          (_ , LF.sendLF (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) ≡ just (decLFs-src (suc (suc zero)) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) = refl
lfs-fire-wvot1 (suc (suc (suc zero))) lo vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) lo (lfsWvot1 vs)))
          (_ , LF.sendLF (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) ≡ just (decLFs-src (suc (suc (suc zero))) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) = refl
lfs-fire-wvot1 (suc (suc (suc zero))) hi vs = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) hi (lfsWvot1 vs)))
          (_ , LF.sendLF (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) ≡ just (decLFs-src (suc (suc (suc zero))) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs)) = refl
lfs-fire-wnext1 : (l : Link) (d : Dir) (b : _) (ts : _)
  → decLFs-src l d (lfsWnext1 (b , ts))
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.sendLF l d) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)))) ]─►
    decLFs-src l d (lfsSil LF.stBlockRange)
lfs-fire-wnext1 (zero) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) lo (lfsWnext1 (b , ts))))
          (_ , LF.sendLF (zero) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ just (decLFs-src (zero) lo (lfsSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) = refl
lfs-fire-wnext1 (zero) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) hi (lfsWnext1 (b , ts))))
          (_ , LF.sendLF (zero) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ just (decLFs-src (zero) hi (lfsSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) = refl
lfs-fire-wnext1 (suc zero) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) lo (lfsWnext1 (b , ts))))
          (_ , LF.sendLF (suc zero) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc zero) lo (lfsSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) = refl
lfs-fire-wnext1 (suc zero) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) hi (lfsWnext1 (b , ts))))
          (_ , LF.sendLF (suc zero) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc zero) hi (lfsSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) = refl
lfs-fire-wnext1 (suc (suc zero)) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) lo (lfsWnext1 (b , ts))))
          (_ , LF.sendLF (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc (suc zero)) lo (lfsSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) = refl
lfs-fire-wnext1 (suc (suc zero)) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) hi (lfsWnext1 (b , ts))))
          (_ , LF.sendLF (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc (suc zero)) hi (lfsSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) = refl
lfs-fire-wnext1 (suc (suc (suc zero))) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) lo (lfsWnext1 (b , ts))))
          (_ , LF.sendLF (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc (suc (suc zero))) lo (lfsSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) = refl
lfs-fire-wnext1 (suc (suc (suc zero))) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) hi (lfsWnext1 (b , ts))))
          (_ , LF.sendLF (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc (suc (suc zero))) hi (lfsSil LF.stBlockRange))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)) = refl
lfs-fire-wlast1 : (l : Link) (d : Dir) (b : _) (ts : _)
  → decLFs-src l d (lfsWlast1 (b , ts))
      LFL.─[ LFL.ev (LFL.evl (LFL.evLabel _ (LF.sendLF l d) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)))) ]─►
    decLFs-src l d (lfsSil LF.stIdle)
lfs-fire-wlast1 (zero) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) lo (lfsWlast1 (b , ts))))
          (_ , LF.sendLF (zero) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ just (decLFs-src (zero) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) = refl
lfs-fire-wlast1 (zero) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (zero) hi (lfsWlast1 (b , ts))))
          (_ , LF.sendLF (zero) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ just (decLFs-src (zero) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) = refl
lfs-fire-wlast1 (suc zero) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) lo (lfsWlast1 (b , ts))))
          (_ , LF.sendLF (suc zero) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc zero) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) = refl
lfs-fire-wlast1 (suc zero) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc zero) hi (lfsWlast1 (b , ts))))
          (_ , LF.sendLF (suc zero) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc zero) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) = refl
lfs-fire-wlast1 (suc (suc zero)) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) lo (lfsWlast1 (b , ts))))
          (_ , LF.sendLF (suc (suc zero)) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc (suc zero)) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) = refl
lfs-fire-wlast1 (suc (suc zero)) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc zero)) hi (lfsWlast1 (b , ts))))
          (_ , LF.sendLF (suc (suc zero)) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc (suc zero)) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) = refl
lfs-fire-wlast1 (suc (suc (suc zero))) lo b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) lo (lfsWlast1 (b , ts))))
          (_ , LF.sendLF (suc (suc (suc zero))) lo) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc (suc (suc zero))) lo (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) = refl
lfs-fire-wlast1 (suc (suc (suc zero))) hi b ts = LFL.sVis refl o
  where
    o : vis-ofF (PTree.force (decLFs-src (suc (suc (suc zero))) hi (lfsWlast1 (b , ts))))
          (_ , LF.sendLF (suc (suc (suc zero))) hi) (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) ≡ just (decLFs-src (suc (suc (suc zero))) hi (lfsSil LF.stIdle))
    o rewrite ≟-yes-refl {A = Payload} (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)) = refl

------------------------------------------------------------------------
-- LF-CLIENT backward production leaf.
------------------------------------------------------------------------
Tlfc : Link → Dir → NS.Table NS.LFcPos
Tlfc l d = record { isFin = NS.lfCfin ; nxt = NS.lfCnxt l d }
mkMlfc : (l : Link) (d : Dir) (pos′ : LFcPos) {q′ : NS.LFcPos} {M : NetProc}
  → M ≡ tableSpec (Tlfc l d) q′ → q′ ≡ coarsenLFc pos′ → M ≡ absLFc l d pos′
mkMlfc l d pos′ Meq qeq = trans Meq (cong (tableSpec (Tlfc l d)) qeq)

lfc-hstep : (l : Link) (d : Dir) (st : LF.LFState)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {M : NetProc}
  → absLFc l d (lfcHead st) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M
  → Σ[ pos′ ∈ LFcPos ] (decLFc l d (lfcHead st) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► decLFc l d pos′)
      × (M ≡ absLFc l d pos′)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' sendLFBlockRequest} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcWblk1 a , RFLF.renameMap-ev-fwd (lfc-fire-blkreq l d a) , mkMlfc l d (lfcWblk1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' sendLFBlockTxsRequest} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcWtxs1 a , RFLF.renameMap-ev-fwd (lfc-fire-txsreq l d a) , mkMlfc l d (lfcWtxs1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' sendLFVotesRequest} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcWvot1 a , RFLF.renameMap-ev-fwd (lfc-fire-votreq l d a) , mkMlfc l d (lfcWvot1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' sendLFBlockRangeRequest} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcWrng1 a , RFLF.renameMap-ev-fwd (lfc-fire-rngreq l d a) , mkMlfc l d (lfcWrng1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' sendLFDone} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcDone1 , RFLF.renameMap-ev-fwd (lfc-fire-cdone l d) , mkMlfc l d (lfcDone1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' sendLFBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' sendLFBlockTxs} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' sendLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' sendLFNextBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' sendLFLastBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' recvLFBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' recvLFBlockTxs} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stIdle {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlock b)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcRblk1 b , RFLF.renameMap-ev-fwd (lfc-fire-rblk l d b t0 md ln) , mkMlfc l d (lfcRblk1 b) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch MsgLFDone} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlock {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxs ts)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcRbtx1 ts , RFLF.renameMap-ev-fwd (lfc-fire-rbtx l d ts t0 md ln) , mkMlfc l d (lfcRbtx1 ts) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch MsgLFDone} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockTxs {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVoteDelivery vs)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcRvot1 vs , RFLF.renameMap-ev-fwd (lfc-fire-rvot l d vs t0 md ln) , mkMlfc l d (lfcRvot1 vs) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch MsgLFDone} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stVotes {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFNextBlockAndTxsInRange b ts)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcRnext1 b ts , RFLF.renameMap-ev-fwd (lfc-fire-rnext l d b ts t0 md ln) , mkMlfc l d (lfcRnext1 b ts) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFLastBlockAndTxsInRange b ts)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfcRlast1 b ts , RFLF.renameMap-ev-fwd (lfc-fire-rlast l d b ts t0 md ln) , mkMlfc l d (lfcRlast1 b ts) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxsRequest _ _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVotesRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockRangeRequest _)} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch MsgLFDone} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stBlockRange {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfc-hstep l d LF.stDone step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcHead LF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

decLFc-ev-prod-abs : (l : Link) (d : Dir) (pos : LFcPos)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {M : NetProc}
  → absLFc l d pos ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M
  → Σ[ pos′ ∈ LFcPos ] (decLFc l d pos ═[ ev (evl (evLabel X (ιLF e₁) a)) ]═► decLFc l d pos′)
      × (M ≡ absLFc l d pos′)
decLFc-ev-prod-abs l d (lfcHead st) step with lfc-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
decLFc-ev-prod-abs l d (lfcSil st) step with lfc-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decLFc-sil-step l d st) τ*-refl) f τ*-refl , m
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' recvLFBlock} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ decBlock ⦄ a b
...     | yes refl = lfcSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-rblk1 l d b)) τ*-refl , mkMlfc l d (lfcSil LF.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' recvLFBlock} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' recvLFBlock} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' sendLFBlockRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' sendLFBlockTxsRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' sendLFVotesRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' sendLFBlockRangeRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' sendLFDone} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' sendLFBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' sendLFBlockTxs} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' sendLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' sendLFNextBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' sendLFLastBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' recvLFBlockTxs} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRblk1 b) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' recvLFBlockTxs} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ DecEqI.DecEq-List ⦄ a ts
...     | yes refl = lfcSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-rbtx1 l d ts)) τ*-refl , mkMlfc l d (lfcSil LF.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' recvLFBlockTxs} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' recvLFBlockTxs} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' sendLFBlockRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' sendLFBlockTxsRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' sendLFVotesRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' sendLFBlockRangeRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' sendLFDone} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' sendLFBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' sendLFBlockTxs} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' sendLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' sendLFNextBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' sendLFLastBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' recvLFBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRbtx1 ts) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRbtx1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ DecEqI.DecEq-List ⦄ a vs
...     | yes refl = lfcSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-rvot1 l d vs)) τ*-refl , mkMlfc l d (lfcSil LF.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' sendLFBlockRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' sendLFBlockTxsRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' sendLFVotesRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' sendLFBlockRangeRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' sendLFDone} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' sendLFBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' sendLFBlockTxs} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' sendLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' sendLFNextBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' sendLFLastBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' recvLFBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' recvLFBlockTxs} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRvot1 vs) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' recvLFRangeBlock} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ NS.DecEq-Block×ListTx ⦄ a (b , ts)
...     | yes refl = lfcSil LF.stBlockRange , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-rnext1 l d b ts)) τ*-refl , mkMlfc l d (lfcSil LF.stBlockRange) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' sendLFBlockRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' sendLFBlockTxsRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' sendLFVotesRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' sendLFBlockRangeRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' sendLFDone} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' sendLFBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' sendLFBlockTxs} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' sendLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' sendLFNextBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' sendLFLastBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' recvLFBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' recvLFBlockTxs} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRnext1 b ts) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRnext1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' recvLFRangeBlock} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with _≟_ ⦃ NS.DecEq-Block×ListTx ⦄ a (b , ts)
...     | yes refl = lfcSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-rlast1 l d b ts)) τ*-refl , mkMlfc l d (lfcSil LF.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' sendLFBlockRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' sendLFBlockTxsRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' sendLFVotesRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' sendLFBlockRangeRequest} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' sendLFDone} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' sendLFBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' sendLFBlockTxs} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' sendLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' sendLFNextBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' sendLFLastBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' recvLFBlock} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' recvLFBlockTxs} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcRlast1 b ts) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcRlast1 b ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWblk1 pt) {e₁ = LF.sendLF l' d'} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWblk1 pt)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRequest pt))
...     | yes refl = lfcSil LF.stBlock , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-wblk1 l d pt)) τ*-refl , mkMlfc l d (lfcSil LF.stBlock) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWblk1 pt) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWblk1 pt) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWblk1 pt) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWblk1 pt)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWblk1 pt) {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWblk1 pt)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWblk1 pt) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWblk1 pt)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWtxs1 (pt , bm)) {e₁ = LF.sendLF l' d'} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWtxs1 (pt , bm))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockTxsRequest pt bm))
...     | yes refl = lfcSil LF.stBlockTxs , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-wtxs1 l d pt bm)) τ*-refl , mkMlfc l d (lfcSil LF.stBlockTxs) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWtxs1 (pt , bm)) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWtxs1 (pt , bm)) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWtxs1 (pt , bm)) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWtxs1 (pt , bm))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWtxs1 (pt , bm)) {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWtxs1 (pt , bm))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWtxs1 (pt , bm)) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWtxs1 (pt , bm))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWvot1 vs) {e₁ = LF.sendLF l' d'} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWvot1 vs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFVotesRequest vs))
...     | yes refl = lfcSil LF.stVotes , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-wvot1 l d vs)) τ*-refl , mkMlfc l d (lfcSil LF.stVotes) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWvot1 vs) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWvot1 vs) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWvot1 vs) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWvot1 vs) {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWvot1 vs) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWrng1 r) {e₁ = LF.sendLF l' d'} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWrng1 r)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch (MsgLFBlockRangeRequest r))
...     | yes refl = lfcSil LF.stBlockRange , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-wrng1 l d r)) τ*-refl , mkMlfc l d (lfcSil LF.stBlockRange) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWrng1 r) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWrng1 r) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWrng1 r) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWrng1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWrng1 r) {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWrng1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d (lfcWrng1 r) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc (lfcWrng1 r)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d lfcDone1 {e₁ = LF.sendLF l' d'} {a} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc lfcDone1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromInitiator , length₀ , leiosFetch MsgLFDone)
...     | yes refl = lfcSil LF.stDone , wev τ*-refl (RFLF.renameMap-ev-fwd (lfc-fire-wdone1 l d)) τ*-refl , mkMlfc l d (lfcSil LF.stDone) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d lfcDone1 {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d lfcDone1 {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d lfcDone1 {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc lfcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d lfcDone1 {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc lfcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFc-ev-prod-abs l d lfcDone1 {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfc l d) (coarsenLFc lfcDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

------------------------------------------------------------------------
-- LF-SERVER backward production leaf.
------------------------------------------------------------------------
Tlfs : Link → Dir → NS.Table NS.LFsPos
Tlfs l d = record { isFin = NS.lfSfin ; nxt = NS.lfSnxt l d }
mkMlfs : (l : Link) (d : Dir) (pos′ : LFsPos) {q′ : NS.LFsPos} {M : NetProc}
  → M ≡ tableSpec (Tlfs l d) q′ → q′ ≡ coarsenLFs pos′ → M ≡ absLFs l d pos′
mkMlfs l d pos′ Meq qeq = trans Meq (cong (tableSpec (Tlfs l d)) qeq)

lfs-hstep : (l : Link) (d : Dir) (st : LF.LFState)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {M : NetProc}
  → absLFs l d (lfsHead st) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M
  → Σ[ pos′ ∈ LFsPos ] (decLFs l d (lfsHead st) ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► decLFs l d pos′)
      × (M ≡ absLFs l d pos′)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRequest pt)} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsSil LF.stBlock , RFLF.renameMap-ev-fwd (lfs-fire-ireq-blk l d pt t0 md ln) , mkMlfs l d (lfsSil LF.stBlock) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockTxsRequest pt bm)} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsSil LF.stBlockTxs , RFLF.renameMap-ev-fwd (lfs-fire-ireq-txs l d pt bm t0 md ln) , mkMlfs l d (lfsSil LF.stBlockTxs) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFVotesRequest vs)} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsSil LF.stVotes , RFLF.renameMap-ev-fwd (lfs-fire-ireq-vot l d vs t0 md ln) , mkMlfs l d (lfsSil LF.stVotes) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFBlockRangeRequest r)} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsSil LF.stBlockRange , RFLF.renameMap-ev-fwd (lfs-fire-ireq-rng l d r t0 md ln) , mkMlfs l d (lfsSil LF.stBlockRange) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = t0 , md , ln , leiosFetch (MsgLFDone)} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsDone1 , RFLF.renameMap-ev-fwd (lfs-fire-idone l d t0 md ln) , mkMlfs l d (lfsDone1) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlock _)} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFBlockTxs _)} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFVoteDelivery _)} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFNextBlockAndTxsInRange _ _)} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosFetch (MsgLFLastBlockAndTxsInRange _ _)} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , chainSync x} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , blockFetch x} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , txSubmission x} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , keepAlive x} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.receiveLF l' d'} {a = _ , _ , _ , leiosNotify x} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stIdle {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stIdle)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' sendLFBlock} {a} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsWblk1 a , RFLF.renameMap-ev-fwd (lfs-fire-sblk l d a) , mkMlfs l d (lfsWblk1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' sendLFBlockRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' sendLFBlockTxsRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' sendLFVotesRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' sendLFBlockRangeRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' sendLFDone} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' sendLFBlockTxs} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' sendLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' sendLFNextBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' sendLFLastBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' recvLFBlock} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' recvLFBlockTxs} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlock {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlock)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' sendLFBlockTxs} {a} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsWtxs1 a , RFLF.renameMap-ev-fwd (lfs-fire-stxs l d a) , mkMlfs l d (lfsWtxs1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' sendLFBlockRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' sendLFBlockTxsRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' sendLFVotesRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' sendLFBlockRangeRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' sendLFDone} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' sendLFBlock} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' sendLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' sendLFNextBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' sendLFLastBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' recvLFBlock} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' recvLFBlockTxs} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockTxs {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockTxs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' sendLFVoteDelivery} {a} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsWvot1 a , RFLF.renameMap-ev-fwd (lfs-fire-svot l d a) , mkMlfs l d (lfsWvot1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' sendLFBlockRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' sendLFBlockTxsRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' sendLFVotesRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' sendLFBlockRangeRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' sendLFDone} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' sendLFBlock} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' sendLFBlockTxs} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' sendLFNextBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' sendLFLastBlockAndTxsInRange} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' recvLFBlock} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' recvLFBlockTxs} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stVotes {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stVotes)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' sendLFNextBlockAndTxsInRange} {a} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsWnext1 a , RFLF.renameMap-ev-fwd (lfs-fire-snext l d a) , mkMlfs l d (lfsWnext1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' sendLFLastBlockAndTxsInRange} {a} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsWlast1 a , RFLF.renameMap-ev-fwd (lfs-fire-slast l d a) , mkMlfs l d (lfsWlast1 a) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' sendLFBlockRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' sendLFBlockTxsRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' sendLFVotesRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' sendLFBlockRangeRequest} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' sendLFDone} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' sendLFBlock} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' sendLFBlockTxs} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' sendLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' recvLFBlock} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' recvLFBlockTxs} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' recvLFVoteDelivery} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.apiLFev l' d' recvLFRangeBlock} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stBlockRange {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stBlockRange)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
lfs-hstep l d LF.stDone step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsHead LF.stDone)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)

decLFs-ev-prod-abs : (l : Link) (d : Dir) (pos : LFsPos)
    {X : Set 0ℓ} {e₁ : LF.LFEv X} {a : X} {M : NetProc}
  → absLFs l d pos ─[ ev (evl (evLabel X (ιLF e₁) a)) ]─► M
  → Σ[ pos′ ∈ LFsPos ] (decLFs l d pos ═[ ev (evl (evLabel X (ιLF e₁) a)) ]═► decLFs l d pos′)
      × (M ≡ absLFs l d pos′)
decLFs-ev-prod-abs l d (lfsHead st) step with lfs-hstep l d st step
... | pos′ , f , m = pos′ , wev τ*-refl f τ*-refl , m
decLFs-ev-prod-abs l d (lfsSil st) step with lfs-hstep l d st step
... | pos′ , f , m = pos′ , wev (τ*-step (decLFs-sil-step l d st) τ*-refl) f τ*-refl , m
decLFs-ev-prod-abs l d lfsDone1 {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs lfsDone1) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl = lfsSil LF.stDone , wev τ*-refl (RFLF.renameMap-ev-fwd (lfs-fire-sddone l d)) τ*-refl , mkMlfs l d (lfsSil LF.stDone) Meq (just-injective (sym ceq))
...   | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
...   | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d lfsDone1 {e₁ = LF.sendLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs lfsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d lfsDone1 {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs lfsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d lfsDone1 {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs lfsDone1) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWblk1 b) {e₁ = LF.sendLF l' d'} {a} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWblk1 b)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlock b))
...     | yes refl = lfsSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfs-fire-wblk1 l d b)) τ*-refl , mkMlfs l d (lfsSil LF.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWblk1 b) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWblk1 b) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWblk1 b) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWblk1 b) {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWblk1 b) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWblk1 b)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWtxs1 ts) {e₁ = LF.sendLF l' d'} {a} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWtxs1 ts)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFBlockTxs ts))
...     | yes refl = lfsSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfs-fire-wtxs1 l d ts)) τ*-refl , mkMlfs l d (lfsSil LF.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWtxs1 ts) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWtxs1 ts) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWtxs1 ts) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWtxs1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWtxs1 ts) {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWtxs1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWtxs1 ts) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWtxs1 ts)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWvot1 vs) {e₁ = LF.sendLF l' d'} {a} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWvot1 vs)) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFVoteDelivery vs))
...     | yes refl = lfsSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfs-fire-wvot1 l d vs)) τ*-refl , mkMlfs l d (lfsSil LF.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWvot1 vs) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWvot1 vs) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWvot1 vs) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWvot1 vs) {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWvot1 vs) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWvot1 vs)) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWnext1 (b , ts)) {e₁ = LF.sendLF l' d'} {a} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWnext1 (b , ts))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFNextBlockAndTxsInRange b ts))
...     | yes refl = lfsSil LF.stBlockRange , wev τ*-refl (RFLF.renameMap-ev-fwd (lfs-fire-wnext1 l d b ts)) τ*-refl , mkMlfs l d (lfsSil LF.stBlockRange) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWnext1 (b , ts)) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWnext1 (b , ts)) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWnext1 (b , ts)) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWnext1 (b , ts))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWnext1 (b , ts)) {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWnext1 (b , ts))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWnext1 (b , ts)) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWnext1 (b , ts))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWlast1 (b , ts)) {e₁ = LF.sendLF l' d'} {a} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWlast1 (b , ts))) step
... | q′ , ceq , Meq with l' ≟ l | d' ≟ d
...   | yes refl | yes refl with a ≟ (time₀ , FromResponder , length₀ , leiosFetch (MsgLFLastBlockAndTxsInRange b ts))
...     | yes refl = lfsSil LF.stIdle , wev τ*-refl (RFLF.renameMap-ev-fwd (lfs-fire-wlast1 l d b ts)) τ*-refl , mkMlfs l d (lfsSil LF.stIdle) Meq (just-injective (sym ceq))
...     | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWlast1 (b , ts)) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | yes refl | no _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWlast1 (b , ts)) {e₁ = LF.sendLF l' d'} step | q′ , ceq , Meq | no _ | _ = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWlast1 (b , ts)) {e₁ = LF.receiveLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWlast1 (b , ts))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWlast1 (b , ts)) {e₁ = LF.apiLFev l' d' m} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWlast1 (b , ts))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
decLFs-ev-prod-abs l d (lfsWlast1 (b , ts)) {e₁ = LF.doneLF l' d'} step
  with tableSpec-ev-inv (Tlfs l d) (coarsenLFs (lfsWlast1 (b , ts))) step
... | q′ , ceq , Meq = ⊥-elim (nothing-absurd ceq)
-- LF-SECTION-END
